//! Native proof service boundary. Public artifacts stay retained, private values have no Debug.
//! This API proves frozen native call intents. It does not fund, sign, or submit transactions.
use crate::{
    Config, Db, Plan,
    artifacts::{ContractBundleSet, Role, VerifiedBundle},
    assembly::{BookedComIndices, CheckedNativeCall, NativeIntent},
    client::{ChainIdentity, NetworkPolicy, Snapshot},
    unshielded_caller::{SnapshotUnshieldedSpendScope, check_snapshot_spends},
    zkir::IrSource,
};
use base_crypto::cost_model::CostDuration;
use coin_structure::coin::{Commitment, PublicAddress};
use futures::{Future, FutureExt, pin_mut, select_biased};
use ledger::structure::{
    ContractAction, ContractCall, Intent, LedgerParameters, LedgerState, ProofKind, ProofMarker,
    ProofPreimageVersioned, ProofVersioned, Signature, UtxoSpend,
};
use midnight_proofs::{plonk::ConstraintSystem, poly::kzg::params::ParamsKZG, utils::SerdeFormat};
use midnight_zk_stdlib::{MidnightPK, Relation, ZkStdLib, ZkStdLibArch};
use onchain_runtime::context::BlockContext;
use onchain_runtime::state::{
    ContractMaintenanceAuthority, ContractMaintenanceVerifyingKey, ContractOperation,
    ContractState, EntryPointBuf,
};
use rand::{CryptoRng, Rng};
use serde_json::Value as Json;
use serialize::{Deserializable, Serializable, Tagged, tagged_deserialize, tagged_serialize};
use sha2::{Digest, Sha256};
use std::{cell::RefCell, collections::BTreeMap, fmt, io, rc::Rc, sync::Arc};
use storage::storage::Map;
use transient_crypto::{
    commitment::{Pedersen, PedersenRandomness},
    curve::Fr,
    proofs::{
        KeyLocation, ParamsProver, ParamsProverProvider, ParamsVerifier, Proof, ProofPreimage,
        ProverKey, ProvingKeyMaterial, ProvingProvider, Resolver, VerifierKey, Zkir,
    },
};

pub type ProvedNativeIntent = Intent<Signature, ProofMarker, PedersenRandomness, Db>;
pub type PublicProvedNativeIntent = Intent<Signature, ProofMarker, Pedersen, Db>;
mod composition;
pub use composition::{
    CompositionDraft, CompositionMaterial, IndependentComposition, PreparedComposition,
};

const MAX_RESPONSE: usize = 1_048_576;
const MAX_PARAMETERS: usize = 134_217_728;
const MAX_PRIVATE_CONFIG: usize = 1_048_576;
const MAX_NATIVE_STATE: usize = 1_048_576;

struct CallPreview<P: ProofKind<Db>> {
    call: ContractCall<P, Db>,
    statement: Vec<Fr>,
}

fn preview_transcript_activity(
    old: &onchain_runtime::transcript::Transcript<Db>,
    activity: &[Option<usize>],
    cursor: &mut usize,
    cost_model: &onchain_runtime::cost_model::CostModel,
) -> Result<onchain_runtime::transcript::Transcript<Db>> {
    let mut program = Vec::new();
    for op in old.program.iter_deref() {
        while let Some(Some(skip)) = activity.get(*cursor) {
            let skip = u32::try_from(*skip).map_err(|_| Error::UnsupportedActivity)?;
            program.push(onchain_runtime::ops::Op::Noop { n: skip });
            *cursor = (*cursor).checked_add(1).ok_or(Error::UnsupportedActivity)?;
        }
        if !matches!(activity.get(*cursor), Some(None)) {
            return Err(Error::UnsupportedActivity);
        }
        program.push((*op).clone());
        *cursor = (*cursor).checked_add(1).ok_or(Error::UnsupportedActivity)?;
    }
    while let Some(Some(skip)) = activity.get(*cursor) {
        let skip = u32::try_from(*skip).map_err(|_| Error::UnsupportedActivity)?;
        program.push(onchain_runtime::ops::Op::Noop { n: skip });
        *cursor = (*cursor).checked_add(1).ok_or(Error::UnsupportedActivity)?;
    }

    let mut merged = Vec::with_capacity(program.len());
    let mut pending_noop = 0u32;
    let mut added_gas = 0u64;
    for op in program {
        match op {
            onchain_runtime::ops::Op::Noop { n } => {
                pending_noop = pending_noop
                    .checked_add(n)
                    .ok_or(Error::UnsupportedActivity)?;
            }
            op => {
                if pending_noop != 0 {
                    added_gas = added_gas
                        .checked_add(noop_gas(cost_model, pending_noop)?)
                        .ok_or(Error::UnsupportedActivity)?;
                    merged.push(onchain_runtime::ops::Op::Noop { n: pending_noop });
                    pending_noop = 0;
                }
                merged.push(op);
            }
        }
    }
    if pending_noop != 0 {
        added_gas = added_gas
            .checked_add(noop_gas(cost_model, pending_noop)?)
            .ok_or(Error::UnsupportedActivity)?;
        merged.push(onchain_runtime::ops::Op::Noop { n: pending_noop });
    }
    let original_gas = old.gas.compute_time.into_picoseconds();
    let compute_time = original_gas
        .checked_add(added_gas)
        .ok_or(Error::UnsupportedActivity)?;
    let mut transcript = old.clone();
    transcript.program = merged.into();
    transcript.gas.compute_time = CostDuration::from_picoseconds(compute_time);
    Ok(transcript)
}

fn noop_gas(cost_model: &onchain_runtime::cost_model::CostModel, count: u32) -> Result<u64> {
    let linear = cost_model
        .noop_coeff_arg
        .into_picoseconds()
        .checked_mul(u64::from(count))
        .ok_or(Error::UnsupportedActivity)?;
    cost_model
        .noop_constant
        .into_picoseconds()
        .checked_add(linear)
        .ok_or(Error::UnsupportedActivity)
}

fn preview_call_activity<P: ProofKind<Db>>(
    call: &ContractCall<P, Db>,
    activity: &[Option<usize>],
    binding_commitment: Pedersen,
    cost_model: &onchain_runtime::cost_model::CostModel,
) -> Result<CallPreview<P>> {
    let op_count = call
        .guaranteed_transcript
        .iter()
        .chain(call.fallible_transcript.iter())
        .try_fold(0usize, |count, transcript| {
            count.checked_add(transcript.program.len())
        })
        .ok_or(Error::UnsupportedActivity)?;
    if activity.iter().filter(|entry| entry.is_none()).count() != op_count {
        return Err(Error::UnsupportedActivity);
    }
    let mut call = call.clone();
    let mut cursor = 0usize;
    if let Some(old) = call.guaranteed_transcript.as_ref() {
        call.guaranteed_transcript = Some(storage::arena::Sp::new(preview_transcript_activity(
            old,
            activity,
            &mut cursor,
            cost_model,
        )?));
    }
    if let Some(old) = call.fallible_transcript.as_ref() {
        call.fallible_transcript = Some(storage::arena::Sp::new(preview_transcript_activity(
            old,
            activity,
            &mut cursor,
            cost_model,
        )?));
    }
    if cursor != activity.len() {
        return Err(Error::UnsupportedActivity);
    }
    let statement = call
        .public_inputs(binding_commitment)
        .map_err(|_| Error::InvalidIntent)?;
    Ok(CallPreview { call, statement })
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct StateOnly {
    state: BTreeMap<String, Json>,
}
impl Drop for StateOnly {
    fn drop(&mut self) {
        for value in self.state.values_mut() {
            crate::control::wipe_json(value);
        }
    }
}

struct SecretInputs(BTreeMap<String, Json>);
impl Drop for SecretInputs {
    fn drop(&mut self) {
        for value in self.0.values_mut() {
            crate::control::wipe_json(value);
        }
    }
}

struct SecretConfig(crate::Config);
impl Drop for SecretConfig {
    fn drop(&mut self) {
        for value in self.0.inputs.values_mut() {
            crate::control::wipe_json(value);
        }
    }
}

/// A one-use target made before source witness execution. The exact deployment nonce and
/// initial state stay with this value so the later call cannot select a different address.
pub struct WitnessTarget {
    manifest: String,
    contract: String,
    entrypoint: String,
    circuit_file: String,
    k: u8,
    proof_parameters_sha256: String,
    ttl: u64,
    deployment: crate::assembly::PreparedDeployment,
}

/// Authenticated complete operation map and its one retained deployment identity.
/// Per-operation parameters and call TTLs are selected separately.
pub struct WitnessContractTarget {
    inner: Arc<WitnessContractInner>,
}

struct WitnessContractInner {
    bundles: ContractBundleSet,
    deployment: crate::assembly::PreparedOperationMapDeployment,
    deployment_identity: String,
    state_schema_sha256: String,
    ready_state: ContractState<Db>,
}

/// An operation-specific target. It binds its own circuit degree and trusted SRS before
/// source callbacks begin, while sharing the original deployment address and operation map.
#[derive(Clone)]
pub struct ContractOperationTarget {
    inner: Arc<WitnessContractInner>,
    operation: String,
    manifest: String,
    k: u8,
    proof_parameters_sha256: String,
    ttl: u64,
}

/// Opaque current state admitted by the native client after its receipt and private commit.
/// The token is moved into one source invocation and cannot be cloned or reconstructed publicly.
pub struct CurrentStateContext {
    chain_identity: Option<ChainIdentity>,
    contract_set_identity: String,
    deployment_identity: String,
    state_schema_sha256: String,
    address: String,
    identity: String,
    state_bytes: Vec<u8>,
    state: ContractState<Db>,
}

/// One side of the private two-call relay path. The state token moves only after the
/// complete, snapshot-checked composition has been prepared.
pub(crate) struct CurrentStateCompositionCall<'target, 'state> {
    pub(crate) target: &'target ContractOperationTarget,
    pub(crate) current: &'state mut Option<CurrentStateContext>,
    pub(crate) parameters: &'target TrustedParameters,
    pub(crate) inputs: BTreeMap<String, Json>,
}

/// Private binding carried from prepared source call through client receipt validation.
#[derive(Clone)]
pub(crate) struct ContractStateBinding {
    contract_set_identity: String,
    deployment_identity: String,
    state_schema_sha256: String,
    address: String,
    operation: String,
    context_identity: String,
    current_state_sha256: Option<String>,
    current_state: Option<Vec<u8>>,
    expected_state: Vec<u8>,
    deployment: bool,
}

impl WitnessContractTarget {
    /// Authenticate every retained operation verifier and freeze one complete-map deployment.
    pub fn from_state_config(
        bundles: ContractBundleSet,
        state_config: &[u8],
        deployment_ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        Self::from_state_config_inner(bundles, state_config, deployment_ttl, rng, None)
    }

    /// Bootstrap a complete authenticated contract through a smaller initial verifier map.
    /// Calls remain unavailable until every verifier is installed and the authority is locked.
    pub fn from_staged_state_config(
        bundles: ContractBundleSet,
        state_config: &[u8],
        initial_operations: &[String],
        bootstrap_key: base_crypto::schnorr::VerifyingKey,
        deployment_ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        Self::from_state_config_inner(
            bundles,
            state_config,
            deployment_ttl,
            rng,
            Some((initial_operations, bootstrap_key)),
        )
    }

    fn from_state_config_inner(
        bundles: ContractBundleSet,
        state_config: &[u8],
        deployment_ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
        staging: Option<(&[String], base_crypto::schnorr::VerifyingKey)>,
    ) -> Result<Self> {
        if state_config.len() > MAX_PRIVATE_CONFIG {
            return Err(Error::Limit);
        }
        let state: StateOnly =
            serde_json::from_slice(state_config).map_err(|_| Error::InvalidPrivateInput)?;
        let (first_name, first_bundle) = bundles.iter().next().ok_or(Error::InvalidArtifacts)?;
        let plan_bytes = first_bundle
            .file(Role::Plan)
            .map_err(|_| Error::InvalidArtifacts)?;
        let plan: Plan = serde_json::from_slice(plan_bytes).map_err(|_| Error::InvalidArtifacts)?;
        let plan_json: Json =
            serde_json::from_slice(plan_bytes).map_err(|_| Error::InvalidArtifacts)?;
        let contract = plan_json["contractName"]
            .as_str()
            .filter(|name| *name == bundles.contract_name())
            .ok_or(Error::BindingMismatch)?;
        if plan.entrypoint != first_name {
            return Err(Error::BindingMismatch);
        }
        let schema_bytes =
            serde_json::to_vec(&plan_json["state"]).map_err(|_| Error::InvalidArtifacts)?;
        let state_schema_sha256 = hex::encode(Sha256::digest(&schema_bytes));

        let expected_operations = bundles
            .iter()
            .map(|(name, _)| name.to_owned())
            .collect::<Vec<_>>();
        let mut operations = Vec::with_capacity(expected_operations.len());
        for (name, bundle) in bundles.iter() {
            let material = Material::retained(bundle)?;
            let selected_plan: Json = serde_json::from_slice(
                bundle
                    .file(Role::Plan)
                    .map_err(|_| Error::InvalidArtifacts)?,
            )
            .map_err(|_| Error::InvalidArtifacts)?;
            if material.entrypoint != name
                || selected_plan["contractName"] != contract
                || selected_plan["entrypoint"] != name
                || serde_json::to_vec(&selected_plan["state"])
                    .map_err(|_| Error::InvalidArtifacts)?
                    != schema_bytes
            {
                return Err(Error::BindingMismatch);
            }
            operations.push((
                name.to_owned(),
                ContractOperation::new(Some(material.verifier), None),
            ));
        }
        let mut deployment = crate::assembly::prepare_operation_map_deployment_target(
            &plan,
            contract,
            &state.state,
            &expected_operations,
            operations,
            deployment_ttl,
            rng,
        )
        .map_err(|_| Error::InvalidPrivateInput)?;
        let ready_state = deployment.ready_state().map_err(|_| Error::InvalidIntent)?;
        if let Some((names, key)) = staging {
            let installed: std::collections::BTreeSet<_> = names.iter().cloned().collect();
            if installed.len() != names.len() {
                return Err(Error::BindingMismatch);
            }
            deployment = deployment
                .with_installation_subset(
                    &installed,
                    ContractMaintenanceAuthority {
                        committee: vec![ContractMaintenanceVerifyingKey::Schnorr(key)],
                        threshold: 1,
                        counter: 0,
                    },
                    deployment_ttl,
                    rng,
                )
                .map_err(|_| Error::InvalidIntent)?;
        }
        let deployment_identity = deployment_identity(deployment.intent())?;
        Ok(Self {
            inner: Arc::new(WitnessContractInner {
                bundles,
                deployment,
                deployment_identity,
                state_schema_sha256,
                ready_state,
            }),
        })
    }

    pub fn contract_address(&self) -> &str {
        self.inner.deployment.address()
    }

    pub fn identity(&self) -> &str {
        self.inner.bundles.identity()
    }

    /// Authenticate the original deployment from a trusted durable attempt.
    /// Receipt and private-CAS recovery remain necessary before state admission.
    pub fn restore_deployment(
        self,
        attempt: &crate::client::SubmissionAttempt,
        ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        if attempt.transaction().event() != crate::client::ContractEvent::Deploy
            || attempt.transaction().policy().profile != crate::profile::NAME
        {
            return Err(Error::BindingMismatch);
        }
        let transaction: crate::funding::SealedTransaction = decode(attempt.transaction().bytes())?;
        let ledger::structure::Transaction::Standard(transaction) = transaction else {
            return Err(Error::BindingMismatch);
        };
        let intent = transaction
            .intents
            .get(&crate::funding::CONTRACT_SEGMENT)
            .ok_or(Error::BindingMismatch)?;
        if intent.actions.len() != 1 {
            return Err(Error::BindingMismatch);
        }
        let Some(ContractAction::Deploy(deployment)) = intent.actions.iter_deref().next() else {
            return Err(Error::BindingMismatch);
        };
        let mut inner = Arc::try_unwrap(self.inner).map_err(|_| Error::BindingMismatch)?;
        inner.deployment = inner
            .deployment
            .with_retained_deployment((**deployment).clone(), ttl, rng)
            .map_err(|_| Error::BindingMismatch)?;
        if inner.deployment.address() != attempt.transaction().contract_address()
            || encode(
                &inner
                    .deployment
                    .ready_state()
                    .map_err(|_| Error::BindingMismatch)?,
            )? != attempt.transaction().expected_state()
        {
            return Err(Error::BindingMismatch);
        }
        inner.deployment_identity = deployment_identity(inner.deployment.intent())?;
        Ok(Self {
            inner: Arc::new(inner),
        })
    }

    pub(crate) fn recovery_binding(
        &self,
        attempt: &crate::client::SubmissionAttempt,
    ) -> Result<ContractStateBinding> {
        use crate::client::ContractEvent;
        let transaction = attempt.transaction();
        if transaction.contract_address() != self.contract_address()
            || transaction.policy().profile != crate::profile::NAME
        {
            return Err(Error::BindingMismatch);
        }
        let journal: Json = serde_json::from_slice(attempt.record().journal_bytes())
            .map_err(|_| Error::BindingMismatch)?;
        let operation = journal["entrypoint"]
            .as_str()
            .ok_or(Error::BindingMismatch)?;
        let state: ContractState<Db> = decode(transaction.expected_state())?;
        if encode(&state)? != transaction.expected_state() {
            return Err(Error::BindingMismatch);
        }
        match transaction.event() {
            ContractEvent::Deploy => {
                let expected = self
                    .inner
                    .deployment
                    .ready_state()
                    .map_err(|_| Error::BindingMismatch)?;
                if state != expected || self.inner.bundles.operation(operation).is_none() {
                    return Err(Error::BindingMismatch);
                }
            }
            ContractEvent::Maintain => {
                if operation != "__noctium_maintenance"
                    || !supported_maintenance_authority(&state.maintenance_authority)
                {
                    return Err(Error::BindingMismatch);
                }
                for pair in state.operations.iter() {
                    let (name, value) = &*pair;
                    if self.inner.ready_state.operations.get(&**name).as_deref() != Some(&**value) {
                        return Err(Error::BindingMismatch);
                    }
                }
            }
            ContractEvent::Call => {
                if self.inner.bundles.operation(operation).is_none()
                    || state.operations != self.inner.ready_state.operations
                    || state.maintenance_authority.committee
                        != self.inner.ready_state.maintenance_authority.committee
                    || state.maintenance_authority.threshold
                        != self.inner.ready_state.maintenance_authority.threshold
                {
                    return Err(Error::BindingMismatch);
                }
                let plan: Plan = serde_json::from_slice(
                    self.deployment_bundle()?
                        .file(Role::Plan)
                        .map_err(|_| Error::InvalidArtifacts)?,
                )
                .map_err(|_| Error::InvalidArtifacts)?;
                crate::constructor::check_sealed_state(
                    &plan,
                    &self.inner.ready_state.data,
                    &state.data,
                )
                .map_err(|_| Error::BindingMismatch)?;
            }
        }
        let checkpoint = attempt
            .record()
            .immutable_digest()
            .map_err(|_| Error::BindingMismatch)?;
        // Recovery admits a verified post-state, not an unexecuted source pre-state.
        let previous = (transaction.event() != ContractEvent::Deploy)
            .then(|| transaction.expected_state().to_vec());
        Ok(ContractStateBinding {
            contract_set_identity: self.identity().to_owned(),
            deployment_identity: self.inner.deployment_identity.clone(),
            state_schema_sha256: self.inner.state_schema_sha256.clone(),
            address: self.contract_address().to_owned(),
            operation: operation.to_owned(),
            context_identity: checkpoint,
            current_state_sha256: previous
                .as_ref()
                .map(|bytes| hex::encode(Sha256::digest(bytes))),
            current_state: previous,
            expected_state: transaction.expected_state().to_vec(),
            deployment: transaction.event() == ContractEvent::Deploy,
        })
    }

    /// Select one operation with its own trusted parameters and fresh native call TTL.
    pub fn operation(
        &self,
        operation: &str,
        parameters: &TrustedParameters,
        ttl: u64,
    ) -> Result<ContractOperationTarget> {
        if ttl == 0 {
            return Err(Error::InvalidIntent);
        }
        let bundle = self
            .inner
            .bundles
            .operation(operation)
            .ok_or(Error::BindingMismatch)?;
        let material = Material::retained(bundle)?;
        if material.entrypoint != operation || material.circuit.k() != parameters.k() {
            return Err(Error::InvalidParameters);
        }
        let plan: Json = serde_json::from_slice(
            bundle
                .file(Role::Plan)
                .map_err(|_| Error::InvalidArtifacts)?,
        )
        .map_err(|_| Error::InvalidArtifacts)?;
        if plan["contractName"] != self.inner.bundles.contract_name()
            || plan["entrypoint"] != operation
        {
            return Err(Error::BindingMismatch);
        }
        Ok(ContractOperationTarget {
            inner: self.inner.clone(),
            operation: operation.to_owned(),
            manifest: bundle
                .authenticated_manifest_sha256()
                .ok_or(Error::UnauthenticatedBundle)?
                .to_owned(),
            k: material.circuit.k(),
            proof_parameters_sha256: parameters.sha256().to_owned(),
            ttl,
        })
    }

    pub(crate) fn deployment_intent(&self) -> &NativeIntent {
        self.inner.deployment.intent()
    }

    pub(crate) fn deployment_bundle(&self) -> Result<&VerifiedBundle> {
        self.inner
            .bundles
            .iter()
            .next()
            .map(|(_, bundle)| bundle)
            .ok_or(Error::InvalidArtifacts)
    }

    pub(crate) fn deployment_binding(&self, operation: &str) -> Result<ContractStateBinding> {
        let bundle = self
            .inner
            .bundles
            .operation(operation)
            .ok_or(Error::BindingMismatch)?;
        let deployment = self
            .inner
            .deployment
            .intent()
            .actions
            .iter_deref()
            .next()
            .ok_or(Error::InvalidIntent)?;
        let ContractAction::Deploy(deployment) = deployment else {
            return Err(Error::InvalidIntent);
        };
        let expected_state = encode(&deployment.initial_state)?;
        Ok(ContractStateBinding {
            contract_set_identity: self.identity().to_owned(),
            deployment_identity: self.inner.deployment_identity.clone(),
            state_schema_sha256: self.inner.state_schema_sha256.clone(),
            address: self.contract_address().to_owned(),
            operation: operation.to_owned(),
            context_identity: digest_parts(&[
                self.identity().as_bytes(),
                self.inner.deployment_identity.as_bytes(),
                operation.as_bytes(),
                bundle
                    .authenticated_manifest_sha256()
                    .ok_or(Error::UnauthenticatedBundle)?
                    .as_bytes(),
            ]),
            current_state_sha256: None,
            current_state: None,
            expected_state,
            deployment: true,
        })
    }

    pub(crate) fn prepare_installation(
        &self,
        current: &CurrentStateContext,
        names: &[String],
        signer: &base_crypto::schnorr::SigningKey,
        lock: bool,
        ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<(NativeIntent, ContractStateBinding)> {
        use ledger::structure::{
            ContractOperationVersionedVerifierKey, MaintenanceUpdate, SingleUpdate,
        };
        if ttl == 0
            || current.contract_set_identity != self.identity()
            || current.deployment_identity != self.inner.deployment_identity
            || current.state_schema_sha256 != self.inner.state_schema_sha256
            || current.address != self.contract_address()
            || current.state.data != self.inner.ready_state.data
            || current.state.balance != self.inner.ready_state.balance
            || (names.is_empty() && !lock)
            || names.len() > self.inner.bundles.iter().count()
        {
            return Err(Error::BindingMismatch);
        }
        let authority = &current.state.maintenance_authority;
        if authority.threshold != 1
            || authority.committee
                != vec![ContractMaintenanceVerifyingKey::Schnorr(
                    signer.verifying_key(),
                )]
            || authority.counter == u32::MAX
        {
            return Err(Error::BindingMismatch);
        }
        for pair in current.state.operations.iter() {
            let (entry, operation) = &*pair;
            if self.inner.ready_state.operations.get(&**entry).as_deref() != Some(&**operation) {
                return Err(Error::BindingMismatch);
            }
        }
        let mut expected = current.state.clone();
        expected.maintenance_authority.counter += 1;
        let mut updates = Vec::new();
        let mut unique = std::collections::BTreeSet::new();
        for name in names {
            if !unique.insert(name) {
                return Err(Error::BindingMismatch);
            }
            let entry = EntryPointBuf(name.as_bytes().to_vec());
            if expected.operations.get(&entry).is_some() {
                return Err(Error::BindingMismatch);
            }
            let operation = self
                .inner
                .ready_state
                .operations
                .get(&entry)
                .ok_or(Error::BindingMismatch)?;
            let verifier = operation.v3.clone().ok_or(Error::BindingMismatch)?;
            updates.push(SingleUpdate::VerifierKeyInsert(
                entry.clone(),
                ContractOperationVersionedVerifierKey::V4(verifier),
            ));
            expected.operations = expected.operations.insert(entry, (*operation).clone());
        }
        if lock {
            if expected.operations != self.inner.ready_state.operations {
                return Err(Error::BindingMismatch);
            }
            let counter = expected.maintenance_authority.counter;
            expected.maintenance_authority = self.inner.ready_state.maintenance_authority.clone();
            expected.maintenance_authority.counter = counter;
            updates.push(SingleUpdate::ReplaceAuthority(
                expected.maintenance_authority.clone(),
            ));
        }
        let address = coin_structure::contract::ContractAddress(base_crypto::hash::HashOutput(
            hex::decode(self.contract_address())
                .map_err(|_| Error::BindingMismatch)?
                .try_into()
                .map_err(|_| Error::BindingMismatch)?,
        ));
        let mut update = MaintenanceUpdate::<Db> {
            address,
            updates: updates.into(),
            counter: authority.counter,
            signatures: vec![].into(),
        };
        let signature = Signature::Schnorr(signer.sign(rng, &update.data_to_sign()));
        update.signatures = vec![ledger::structure::SignaturesValue(0, signature)].into();
        let intent = NativeIntent::empty(rng, base_crypto::time::Timestamp::from_secs(ttl))
            .add_maintenance_update(update);
        Ok((
            intent,
            ContractStateBinding {
                contract_set_identity: self.identity().to_owned(),
                deployment_identity: self.inner.deployment_identity.clone(),
                state_schema_sha256: self.inner.state_schema_sha256.clone(),
                address: self.contract_address().to_owned(),
                operation: "__noctium_maintenance".into(),
                context_identity: current.identity.clone(),
                current_state_sha256: Some(hex::encode(Sha256::digest(&current.state_bytes))),
                current_state: Some(current.state_bytes.clone()),
                expected_state: encode(&expected)?,
                deployment: false,
            },
        ))
    }

    pub(crate) fn prepare_authority_rotation(
        &self,
        current: &CurrentStateContext,
        signer: &base_crypto::schnorr::SigningKey,
        next_key: base_crypto::schnorr::VerifyingKey,
        ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<(NativeIntent, ContractStateBinding)> {
        use ledger::structure::{MaintenanceUpdate, SingleUpdate};

        if ttl == 0
            || !self.maintenance_context_matches(current)
            || current.state.maintenance_authority.threshold != 1
            || current.state.maintenance_authority.committee
                != vec![ContractMaintenanceVerifyingKey::Schnorr(
                    signer.verifying_key(),
                )]
            || current.state.maintenance_authority.counter == u32::MAX
            || next_key == signer.verifying_key()
            || encode(&current.state)? != current.state_bytes
        {
            return Err(Error::BindingMismatch);
        }

        let next_counter = current.state.maintenance_authority.counter + 1;
        let next_authority = ContractMaintenanceAuthority {
            committee: vec![ContractMaintenanceVerifyingKey::Schnorr(next_key)],
            threshold: 1,
            counter: next_counter,
        };
        let mut expected = current.state.clone();
        expected.maintenance_authority = next_authority.clone();
        let address = coin_structure::contract::ContractAddress(base_crypto::hash::HashOutput(
            hex::decode(self.contract_address())
                .map_err(|_| Error::BindingMismatch)?
                .try_into()
                .map_err(|_| Error::BindingMismatch)?,
        ));
        let mut update = MaintenanceUpdate::<Db> {
            address,
            updates: vec![SingleUpdate::ReplaceAuthority(next_authority)].into(),
            counter: current.state.maintenance_authority.counter,
            signatures: vec![].into(),
        };
        let signature = Signature::Schnorr(signer.sign(rng, &update.data_to_sign()));
        update.signatures = vec![ledger::structure::SignaturesValue(0, signature)].into();
        let intent = NativeIntent::empty(rng, base_crypto::time::Timestamp::from_secs(ttl))
            .add_maintenance_update(update);
        Ok((
            intent,
            ContractStateBinding {
                contract_set_identity: self.identity().to_owned(),
                deployment_identity: self.inner.deployment_identity.clone(),
                state_schema_sha256: self.inner.state_schema_sha256.clone(),
                address: self.contract_address().to_owned(),
                operation: "__noctium_maintenance".into(),
                context_identity: current.identity.clone(),
                current_state_sha256: Some(hex::encode(Sha256::digest(&current.state_bytes))),
                current_state: Some(current.state_bytes.clone()),
                expected_state: encode(&expected)?,
                deployment: false,
            },
        ))
    }

    fn maintenance_context_matches(&self, current: &CurrentStateContext) -> bool {
        current.contract_set_identity == self.identity()
            && current.deployment_identity == self.inner.deployment_identity
            && current.state_schema_sha256 == self.inner.state_schema_sha256
            && current.address == self.contract_address()
            && current.state.operations == self.inner.ready_state.operations
            && supported_maintenance_authority(&current.state.maintenance_authority)
    }
}

impl ContractOperationTarget {
    pub fn operation(&self) -> &str {
        &self.operation
    }

    pub fn contract_address(&self) -> &str {
        self.inner.deployment.address()
    }

    /// Prepare a contract CALL without a witness-control sidecar from scalar inputs and one admitted current-state
    /// token. The selected operation target pins its own SRS identity and call TTL. Public
    /// target and state checks run before the token moves, and any preparation error preserves
    /// the token for a corrected attempt. Contracts without a witness-control sidecar use this
    /// path directly.
    pub fn prepare_call(
        &self,
        current_state: &mut Option<CurrentStateContext>,
        parameters: &TrustedParameters,
        inputs: BTreeMap<String, Json>,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<PreparedProof> {
        self.prepare_call_with_context(current_state, parameters, inputs, None, None, rng)
    }

    /// Prepare a call using the explicit prospective block context supplied by the host.
    /// Ledger execution rechecks any clock predicate in the resulting transcript.
    pub fn prepare_call_in_block(
        &self,
        current_state: &mut Option<CurrentStateContext>,
        parameters: &TrustedParameters,
        inputs: BTreeMap<String, Json>,
        block: &BlockContext,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<PreparedProof> {
        self.prepare_call_with_context(current_state, parameters, inputs, Some(block), None, rng)
    }

    /// Derive a top-level user caller from the selected unshielded inputs in the snapshot.
    /// The proof attaches an exact balanced return offer for later approval and signing.
    pub fn prepare_call_with_unshielded_caller(
        &self,
        current_state: &mut Option<CurrentStateContext>,
        parameters: &TrustedParameters,
        inputs: BTreeMap<String, Json>,
        snapshot: &Snapshot,
        policy: &NetworkPolicy,
        spends: &[UtxoSpend],
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<PreparedProof> {
        let mut inputs = SecretInputs(inputs);
        snapshot.validate(policy).map_err(|_| Error::BindingMismatch)?;
        let scope = check_snapshot_spends(snapshot, spends).map_err(|_| Error::InvalidIntent)?;
        self.prepare_call_with_context(
            current_state,
            parameters,
            std::mem::take(&mut inputs.0),
            Some(&snapshot.block),
            Some(&scope),
            rng,
        )
    }

    fn prepare_call_with_context(
        &self,
        current_state: &mut Option<CurrentStateContext>,
        parameters: &TrustedParameters,
        inputs: BTreeMap<String, Json>,
        block: Option<&BlockContext>,
        unshielded_scope: Option<&SnapshotUnshieldedSpendScope<'_>>,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<PreparedProof> {
        let mut inputs = SecretInputs(inputs);
        if parameters.k() != self.k || parameters.sha256() != self.proof_parameters_sha256 {
            return Err(Error::InvalidParameters);
        }
        let state = current_state.as_ref().ok_or(Error::BindingMismatch)?;
        if !self.context_matches(state) {
            return Err(Error::BindingMismatch);
        }
        let prepared = PreparedProof::from_contract_witness_inputs_with_context(
            self,
            state,
            std::mem::take(&mut inputs.0),
            Map::new(),
            block,
            unshielded_scope,
            rng,
        )?;
        current_state.take().ok_or(Error::BindingMismatch)?;
        Ok(prepared)
    }

    pub(crate) fn belongs_to(&self, contract: &WitnessContractTarget) -> bool {
        Arc::ptr_eq(&self.inner, &contract.inner)
    }

    pub(crate) fn bundle(&self) -> Result<&VerifiedBundle> {
        self.inner
            .bundles
            .operation(&self.operation)
            .ok_or(Error::BindingMismatch)
    }

    pub(crate) fn authenticated_control_target(
        &self,
        context_id: u64,
    ) -> Result<crate::control::AuthenticatedNativeTarget> {
        let bundle = self.bundle()?;
        if bundle.authenticated_manifest_sha256() != Some(self.manifest.as_str()) {
            return Err(Error::BindingMismatch);
        }
        let target = authenticated_control_target(
            context_id,
            bundle,
            &self.inner.bundles.contract_name(),
            &self.operation,
            bundle
                .manifest()
                .entries
                .iter()
                .find(|entry| entry.role == Role::Circuit)
                .map(|entry| entry.name.as_str())
                .ok_or(Error::InvalidArtifacts)?,
            self.contract_address(),
        )?;
        Ok(target)
    }

    pub(crate) fn preparation_cursor(
        &self,
        state: &CurrentStateContext,
        inputs: &BTreeMap<String, Json>,
    ) -> Result<crate::PreparationCursor> {
        if !self.context_matches(state) {
            return Err(Error::BindingMismatch);
        }
        preparation_cursor(
            self.bundle()?,
            &state.state,
            self.contract_address(),
            inputs,
        )
    }

    pub(crate) fn context_matches(&self, state: &CurrentStateContext) -> bool {
        // Bootstrap advances the replay counter; readiness depends on the locked authority policy.
        state.contract_set_identity == self.inner.bundles.identity()
            && state.deployment_identity == self.inner.deployment_identity
            && state.state_schema_sha256 == self.inner.state_schema_sha256
            && state.address == self.contract_address()
            && state.state.operations == self.inner.ready_state.operations
            && state.state.maintenance_authority.committee
                == self.inner.ready_state.maintenance_authority.committee
            && state.state.maintenance_authority.threshold
                == self.inner.ready_state.maintenance_authority.threshold
    }

    pub(crate) fn parameters_sha256(&self) -> &str {
        &self.proof_parameters_sha256
    }

    pub(crate) fn ttl(&self) -> u64 {
        self.ttl
    }

    pub(crate) fn k(&self) -> u8 {
        self.k
    }

    pub(crate) fn contract_set_identity(&self) -> &str {
        self.inner.bundles.identity()
    }

    pub(crate) fn deployment_identity(&self) -> &str {
        &self.inner.deployment_identity
    }

    pub(crate) fn state_schema_sha256(&self) -> &str {
        &self.inner.state_schema_sha256
    }

    fn selected_material(&self) -> Result<Material> {
        let material = Material::retained(self.bundle()?)?;
        if material.entrypoint != self.operation || material.circuit.k() != self.k {
            return Err(Error::BindingMismatch);
        }
        Ok(material)
    }
}

fn supported_maintenance_authority(authority: &ContractMaintenanceAuthority) -> bool {
    authority.threshold == 1
        && (authority.committee.is_empty()
            || matches!(
                authority.committee.as_slice(),
                [ContractMaintenanceVerifyingKey::Schnorr(_)]
            ))
}

impl ContractStateBinding {
    /// Native client calls this only after BoundTransaction receipt validation, exact state
    /// comparison, finality, and the required private journal commit.
    pub(crate) fn admit_committed_state(
        &self,
        state_bytes: &[u8],
        expected_state: &[u8],
        checkpoint_identity: &str,
        deployment: bool,
    ) -> Result<CurrentStateContext> {
        let current_state_sha256 = self
            .current_state
            .as_deref()
            .map(|current| hex::encode(Sha256::digest(current)));
        if state_bytes.len() > MAX_NATIVE_STATE
            || state_bytes != expected_state
            || state_bytes != self.expected_state
            || deployment != self.deployment
            || checkpoint_identity.len() != 64
            || (!self.deployment
                && current_state_sha256.as_deref() != self.current_state_sha256.as_deref())
            || !checkpoint_identity
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err(Error::BindingMismatch);
        }
        let state: ContractState<Db> = decode(state_bytes)?;
        if encode(&state)? != state_bytes {
            return Err(Error::BindingMismatch);
        }
        let state_sha256 = hex::encode(Sha256::digest(state_bytes));
        let identity = digest_parts(&[
            self.contract_set_identity.as_bytes(),
            self.deployment_identity.as_bytes(),
            self.address.as_bytes(),
            self.state_schema_sha256.as_bytes(),
            state_sha256.as_bytes(),
            checkpoint_identity.as_bytes(),
        ]);
        Ok(CurrentStateContext {
            chain_identity: None,
            contract_set_identity: self.contract_set_identity.clone(),
            deployment_identity: self.deployment_identity.clone(),
            state_schema_sha256: self.state_schema_sha256.clone(),
            address: self.address.clone(),
            identity,
            state_bytes: state_bytes.to_vec(),
            state,
        })
    }

    pub(crate) fn admit_committed_state_on_chain(
        &self,
        state_bytes: &[u8],
        expected_state: &[u8],
        checkpoint_identity: &str,
        deployment: bool,
        chain_identity: &ChainIdentity,
    ) -> Result<CurrentStateContext> {
        let mut context = self.admit_committed_state(
            state_bytes,
            expected_state,
            checkpoint_identity,
            deployment,
        )?;
        context.chain_identity = Some(chain_identity.clone());
        Ok(context)
    }

    pub(crate) fn current_state_bytes(&self) -> Option<&[u8]> {
        self.current_state.as_deref()
    }

    #[cfg(feature = "localnet")]
    pub(crate) fn expected_state(&self) -> &[u8] {
        &self.expected_state
    }

    pub(crate) fn context_identity(&self) -> &str {
        &self.context_identity
    }

    pub(crate) fn matches_event(&self, deployment: bool) -> bool {
        self.deployment == deployment
    }

    pub(crate) fn matches_target(&self, address: &str, operation: &str) -> bool {
        self.address == address && self.operation == operation
    }

    pub(crate) fn matches_operation_target(&self, target: &ContractOperationTarget) -> bool {
        if self.deployment
            || self.contract_set_identity != target.contract_set_identity()
            || self.deployment_identity != target.deployment_identity()
            || self.state_schema_sha256 != target.state_schema_sha256()
            || self.address != target.contract_address()
            || self.operation != target.operation
        {
            return false;
        }
        let Some(current_state) = self.current_state.as_deref() else {
            return false;
        };
        self.current_state_sha256.as_deref()
            == Some(hex::encode(Sha256::digest(current_state)).as_str())
            && self.context_identity.len() == 64
            && self
                .context_identity
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    }
}

fn digest_parts(parts: &[&[u8]]) -> String {
    let mut hash = Sha256::new();
    for part in parts {
        hash.update((part.len() as u64).to_le_bytes());
        hash.update(part);
    }
    hex::encode(hash.finalize())
}

fn deployment_identity(intent: &NativeIntent) -> Result<String> {
    let Some(ContractAction::Deploy(deployment)) = intent.actions.iter_deref().next() else {
        return Err(Error::InvalidIntent);
    };
    Ok(hex::encode(Sha256::digest(encode(&**deployment)?)))
}

fn authenticated_control_target(
    context_id: u64,
    bundle: &VerifiedBundle,
    contract: &str,
    entrypoint: &str,
    circuit_file: &str,
    address: &str,
) -> Result<crate::control::AuthenticatedNativeTarget> {
    let control_plan_bytes = bundle
        .file(Role::WitnessControl)
        .map_err(|_| Error::InvalidArtifacts)?
        .to_vec();
    let control_plan: Json =
        serde_json::from_slice(&control_plan_bytes).map_err(|_| Error::InvalidArtifacts)?;
    let binding_bytes = bundle
        .file(Role::WitnessBinding)
        .map_err(|_| Error::InvalidArtifacts)?
        .to_vec();
    let relation: Json = serde_json::from_slice(
        bundle
            .file(Role::Circuit)
            .map_err(|_| Error::InvalidArtifacts)?,
    )
    .map_err(|_| Error::InvalidArtifacts)?;
    let selected_plan: Json = serde_json::from_slice(
        bundle
            .file(Role::Plan)
            .map_err(|_| Error::InvalidArtifacts)?,
    )
    .map_err(|_| Error::InvalidArtifacts)?;
    if selected_plan["contractName"] != contract
        || selected_plan["entrypoint"] != entrypoint
        || selected_plan["nativeCircuitFile"] != circuit_file
    {
        return Err(Error::BindingMismatch);
    }
    crate::control::validate_witness_artifacts(
        &control_plan,
        &binding_bytes,
        &relation,
        &selected_plan,
        contract,
        entrypoint,
        circuit_file,
        crate::profile::NAME,
    )
    .map_err(|_| Error::BindingMismatch)?;
    Ok(crate::control::AuthenticatedNativeTarget {
        context_id,
        contract_address: address.to_owned(),
        entrypoint: entrypoint.to_owned(),
        control_plan,
        control_plan_bytes,
        binding_bytes,
        relation,
    })
}

impl WitnessTarget {
    /// Prepare the exact deployment target from authenticated public artifacts and private
    /// initial state. This runs before provider calls and returns only a public target identity.
    pub fn from_state_config(
        bundle: &VerifiedBundle,
        state_config: &[u8],
        parameters: &TrustedParameters,
        ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        if state_config.len() > MAX_PRIVATE_CONFIG {
            return Err(Error::Limit);
        }
        let manifest = bundle
            .authenticated_manifest_sha256()
            .ok_or(Error::UnauthenticatedBundle)?
            .to_owned();
        let material = Material::retained(bundle)?;
        if material.circuit.k() != parameters.k() {
            return Err(Error::InvalidParameters);
        }
        let state: StateOnly =
            serde_json::from_slice(state_config).map_err(|_| Error::InvalidPrivateInput)?;
        let plan_bytes = bundle
            .file(Role::Plan)
            .map_err(|_| Error::InvalidArtifacts)?;
        let plan: Plan = serde_json::from_slice(plan_bytes).map_err(|_| Error::InvalidArtifacts)?;
        let plan_json: Json =
            serde_json::from_slice(plan_bytes).map_err(|_| Error::InvalidArtifacts)?;
        let contract = plan_json["contractName"]
            .as_str()
            .filter(|name| !name.is_empty())
            .ok_or(Error::InvalidArtifacts)?
            .to_owned();
        let circuit_file = bundle
            .manifest()
            .entries
            .iter()
            .find(|entry| entry.role == Role::Circuit)
            .map(|entry| entry.name.clone())
            .ok_or(Error::InvalidArtifacts)?;
        let deployment = crate::assembly::prepare_deployment_target(
            &plan,
            &state.state,
            material.verifier,
            ttl,
            rng,
        )
        .map_err(|_| Error::InvalidPrivateInput)?;
        let target = Self {
            manifest,
            contract,
            entrypoint: plan.entrypoint,
            circuit_file,
            k: material.circuit.k(),
            proof_parameters_sha256: parameters.sha256().to_owned(),
            ttl,
            deployment,
        };
        target.authenticated_control_target(0, bundle)?;
        Ok(target)
    }

    pub(crate) fn context_matches(&self, manifest: &str, profile: &str, ttl: u64) -> bool {
        self.manifest == manifest && profile == crate::profile::NAME && self.ttl == ttl
    }

    pub(crate) fn manifest_sha256(&self) -> &str {
        &self.manifest
    }

    pub fn contract_address(&self) -> &str {
        &self.deployment.address
    }

    pub fn entrypoint(&self) -> &str {
        &self.entrypoint
    }

    pub(crate) fn preparation_cursor(
        &self,
        bundle: &VerifiedBundle,
        inputs: &BTreeMap<String, Json>,
    ) -> Result<crate::PreparationCursor> {
        if bundle.authenticated_manifest_sha256() != Some(self.manifest.as_str()) {
            return Err(Error::BindingMismatch);
        }
        let Some(ContractAction::Deploy(deployment)) =
            self.deployment.intent.actions.iter_deref().next()
        else {
            return Err(Error::InvalidIntent);
        };
        preparation_cursor(
            bundle,
            &deployment.initial_state,
            self.contract_address(),
            inputs,
        )
    }

    pub(crate) fn k(&self) -> u8 {
        self.k
    }

    pub(crate) fn proof_parameters_sha256(&self) -> &str {
        &self.proof_parameters_sha256
    }

    pub(crate) fn authenticated_control_target(
        &self,
        context_id: u64,
        bundle: &VerifiedBundle,
    ) -> Result<crate::control::AuthenticatedNativeTarget> {
        if bundle.authenticated_manifest_sha256() != Some(self.manifest.as_str()) {
            return Err(Error::BindingMismatch);
        }
        authenticated_control_target(
            context_id,
            bundle,
            &self.contract,
            &self.entrypoint,
            &self.circuit_file,
            self.contract_address(),
        )
    }
}

fn preparation_cursor(
    bundle: &VerifiedBundle,
    state: &ContractState<Db>,
    address: &str,
    inputs: &BTreeMap<String, Json>,
) -> Result<crate::PreparationCursor> {
    let plan: Plan = serde_json::from_slice(
        bundle
            .file(Role::Plan)
            .map_err(|_| Error::InvalidArtifacts)?,
    )
    .map_err(|_| Error::InvalidArtifacts)?;
    let parameters: LedgerParameters = decode(
        bundle
            .file(Role::LedgerParameters)
            .map_err(|_| Error::InvalidArtifacts)?,
    )?;
    let address = coin_structure::contract::ContractAddress(base_crypto::hash::HashOutput(
        hex::decode(address)
            .map_err(|_| Error::BindingMismatch)?
            .try_into()
            .map_err(|_| Error::BindingMismatch)?,
    ));
    let mut context = onchain_runtime::context::QueryContext::new(state.data.clone(), address);
    context.call_context.balance = state.balance.clone();
    crate::PreparationCursor::from_context(&plan, inputs, context, &parameters, false)
        .map_err(|_| Error::InvalidPrivateInput)
}

/// Fixed diagnostics deliberately discard upstream value-bearing causes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    UnauthenticatedBundle,
    InvalidArtifacts,
    Limit,
    InvalidPrivateInput,
    InvalidIntent,
    UnsupportedActivity,
    InvalidParameters,
    Service,
    InvalidResponse,
    InvalidProof,
    BindingMismatch,
    Cancelled,
    Deadline,
    Attachment,
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "noctium_proof_{self:?}")
    }
}
impl std::error::Error for Error {}
type Result<T> = std::result::Result<T, Error>;
fn decode<T: Deserializable + Tagged>(data: &[u8]) -> Result<T> {
    let mut reader = data;
    let value = tagged_deserialize(&mut reader).map_err(|_| Error::InvalidArtifacts)?;
    if !reader.is_empty() {
        return Err(Error::InvalidArtifacts);
    }
    Ok(value)
}
fn encode<T: Serializable + Tagged>(value: &T) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    tagged_serialize(value, &mut bytes).map_err(|_| Error::Attachment)?;
    Ok(bytes)
}

fn take<'a>(reader: &mut &'a [u8], len: usize) -> Result<&'a [u8]> {
    let (value, rest) = reader
        .split_at_checked(len)
        .ok_or(Error::InvalidArtifacts)?;
    *reader = rest;
    Ok(value)
}
fn key_payload<T: Tagged>(bytes: &[u8]) -> Result<&[u8]> {
    let prefix = format!("midnight:{}:", T::tag());
    let mut reader = bytes
        .strip_prefix(prefix.as_bytes())
        .ok_or(Error::InvalidArtifacts)?;
    let len = <u32 as Deserializable>::deserialize(&mut reader, 0)
        .map_err(|_| Error::InvalidArtifacts)? as usize;
    if len != reader.len() || len > MAX_PARAMETERS {
        return Err(Error::InvalidArtifacts);
    }
    Ok(reader)
}
fn key_columns(circuit: &IrSource, k: u8) -> Result<(usize, usize)> {
    if !(1..=20).contains(&k) {
        return Err(Error::InvalidArtifacts);
    }
    let mut cs = ConstraintSystem::default();
    ZkStdLib::configure(&mut cs, (circuit.used_chips(), k - 1));
    Ok((
        cs.num_fixed_columns() + cs.num_selectors(),
        cs.permutation().get_columns().len(),
    ))
}
fn check_vk_body(
    reader: &mut &[u8],
    k: u8,
    point_bytes: usize,
    columns: (usize, usize),
) -> Result<()> {
    if take(reader, 2)? != [3, k] {
        return Err(Error::InvalidArtifacts);
    }
    let count = u32::from_le_bytes(take(reader, 4)?.try_into().unwrap()) as usize;
    if count != columns.0 {
        return Err(Error::InvalidArtifacts);
    }
    take(reader, (count + columns.1) * point_bytes)?;
    Ok(())
}
fn checked_prover(
    bytes: &[u8],
    circuit: &IrSource,
    k: u8,
    columns: (usize, usize),
) -> Result<ProverKey<IrSource>> {
    let raw = key_payload::<ProverKey<IrSource>>(bytes)?;
    let mut prefix = vec![k];
    circuit
        .write_relation(&mut prefix)
        .map_err(|_| Error::InvalidArtifacts)?;
    // Reject arbitrary embedded relations before the native parser configures their chips.
    let mut reader = raw
        .strip_prefix(prefix.as_slice())
        .ok_or(Error::InvalidArtifacts)?;
    check_vk_body(&mut reader, k, 96, columns)?;
    for expected in [columns.0, columns.1] {
        let count = u32::from_be_bytes(take(&mut reader, 4)?.try_into().unwrap()) as usize;
        if count != expected {
            return Err(Error::InvalidArtifacts);
        }
        for _ in 0..count {
            let len = u32::from_be_bytes(take(&mut reader, 4)?.try_into().unwrap()) as usize;
            if len != 1usize << k {
                return Err(Error::InvalidArtifacts);
            }
            // The pinned Fq raw reader omits its modulus check, even in RawBytes mode.
            // Montgomery limbs still require the same [0, modulus) numeric bound.
            if take(&mut reader, len * 32)?
                .chunks_exact(32)
                .any(|scalar| Fr::from_le_bytes(scalar).is_none())
            {
                return Err(Error::InvalidArtifacts);
            }
        }
    }
    if !reader.is_empty() {
        return Err(Error::InvalidArtifacts);
    }
    let mut reader = raw;
    let key = MidnightPK::<IrSource>::read(&mut reader, SerdeFormat::RawBytes)
        .map_err(|_| Error::InvalidArtifacts)?;
    if !reader.is_empty() {
        return Err(Error::InvalidArtifacts);
    }
    Ok(ProverKey::from_raw(key))
}
fn checked_verifier(
    bytes: &[u8],
    circuit: &IrSource,
    k: u8,
    columns: (usize, usize),
) -> Result<VerifierKey> {
    let mut reader = key_payload::<VerifierKey>(bytes)?;
    let architecture = ZkStdLibArch::read(&mut reader).map_err(|_| Error::InvalidArtifacts)?;
    if architecture != circuit.used_chips() || take(&mut reader, 1)? != [k] {
        return Err(Error::InvalidArtifacts);
    }
    let inputs = u32::from_le_bytes(take(&mut reader, 4)?.try_into().unwrap());
    if inputs == 0 || inputs > (1u32 << k) {
        return Err(Error::InvalidArtifacts);
    }
    check_vk_body(&mut reader, k, 48, columns)?;
    if !reader.is_empty() {
        return Err(Error::InvalidArtifacts);
    }
    let verifier: VerifierKey = decode(bytes)?;
    verifier.init().map_err(|_| Error::InvalidArtifacts)?;
    Ok(verifier)
}

/// The host supplies trusted SRS identity independently of untrusted provider responses.
/// A matching digest authenticates bytes, not their ceremony or provenance.
pub struct TrustedParameters {
    k: u8,
    sha256: String,
    prover: ParamsProver,
    verifier: ParamsVerifier,
}
impl TrustedParameters {
    pub fn from_bytes(bytes: &[u8], k: u8, trusted_sha256: &str) -> Result<Self> {
        if bytes.is_empty() || bytes.len() > MAX_PARAMETERS {
            return Err(Error::Limit);
        }
        if !(1..=20).contains(&k)
            || trusted_sha256.len() != 64
            || !trusted_sha256
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            || hex::encode(Sha256::digest(bytes)) != trusted_sha256
        {
            return Err(Error::InvalidParameters);
        }
        // The pinned native raw format has two 2^k G1 arrays (96 bytes each),
        // two G2 points (192 bytes each), and a little-endian u32 degree.
        // Check before the upstream parser shifts or allocates from its header.
        let expected_len = 4 + (1usize << k) * 2 * 96 + 2 * 192;
        if bytes.len() != expected_len || bytes[..4] != u32::from(k).to_le_bytes() {
            return Err(Error::InvalidParameters);
        }
        let mut reader = bytes;
        let native = ParamsKZG::read_custom(&mut reader, SerdeFormat::RawBytes)
            .map_err(|_| Error::InvalidParameters)?;
        if !reader.is_empty() {
            return Err(Error::InvalidParameters);
        }
        let prover = ParamsProver(Arc::new(native));
        // ParamsVerifier exposes only the unchecked reader. All points and the
        // complete encoding have already passed the checked native parser above.
        let verifier = ParamsVerifier::read(bytes).map_err(|_| Error::InvalidParameters)?;
        Ok(Self {
            k,
            sha256: trusted_sha256.to_owned(),
            prover,
            verifier,
        })
    }
    pub fn k(&self) -> u8 {
        self.k
    }
    pub fn sha256(&self) -> &str {
        &self.sha256
    }
}
impl ParamsProverProvider for TrustedParameters {
    async fn get_params(&self, k: u8) -> io::Result<ParamsProver> {
        if k != self.k {
            return Err(io::Error::other("noctium_parameter_degree_mismatch"));
        }
        Ok(self.prover.clone())
    }
}

pub(crate) async fn regenerate_prover_key(
    bundle: &VerifiedBundle,
    deployed: &ContractState<Db>,
    parameters: &TrustedParameters,
) -> Result<Vec<u8>> {
    let get = |role| bundle.file(role).map_err(|_| Error::InvalidArtifacts);
    let plan: Plan =
        serde_json::from_slice(get(Role::Plan)?).map_err(|_| Error::InvalidArtifacts)?;
    let verifier_bytes = get(Role::VerifierKey)?;
    let operation = EntryPointBuf(plan.entrypoint.into_bytes());
    let installed = deployed
        .operations
        .get(&operation)
        .ok_or(Error::BindingMismatch)?;
    let installed = installed.latest().ok_or(Error::BindingMismatch)?;
    if encode(installed)? != verifier_bytes {
        return Err(Error::BindingMismatch);
    }

    let circuit = IrSource::load(get(Role::Circuit)?).map_err(|_| Error::InvalidArtifacts)?;
    if circuit.k() != parameters.k() {
        return Err(Error::InvalidParameters);
    }
    // Derive the verifier from the authenticated circuit and trusted SRS before
    // accepting its prover key. Installed key bytes never configure key generation.
    let (prover, verifier) = circuit
        .keygen(parameters)
        .await
        .map_err(|_| Error::InvalidParameters)?;
    if encode(&verifier)? != verifier_bytes {
        return Err(Error::BindingMismatch);
    }
    encode(&prover)
}

struct Material {
    native: ProvingKeyMaterial,
    prover: ProverKey<IrSource>,
    circuit: IrSource,
    verifier: VerifierKey,
    parameters: LedgerParameters,
    entrypoint: String,
}
impl Material {
    fn retained(bundle: &VerifiedBundle) -> Result<Self> {
        if bundle.authenticated_manifest_sha256().is_none() {
            return Err(Error::UnauthenticatedBundle);
        }
        let get = |role| bundle.file(role).map_err(|_| Error::InvalidArtifacts);
        let plan: Plan =
            serde_json::from_slice(get(Role::Plan)?).map_err(|_| Error::InvalidArtifacts)?;
        if !crate::profile::validate_plan(plan.target.as_deref(), plan.target_profile.as_ref()) {
            return Err(Error::InvalidArtifacts);
        }
        let native = ProvingKeyMaterial {
            prover_key: get(Role::ProverKey)?.to_vec(),
            verifier_key: get(Role::VerifierKey)?.to_vec(),
            ir_source: get(Role::Circuit)?.to_vec(),
        };
        let circuit = IrSource::load(&native.ir_source[..]).map_err(|_| Error::InvalidArtifacts)?;
        if !circuit.do_communications_commitment {
            return Err(Error::InvalidArtifacts);
        }
        let k = circuit.k();
        let columns = key_columns(&circuit, k)?;
        let prover = checked_prover(&native.prover_key, &circuit, k, columns)?;
        let verifier = checked_verifier(&native.verifier_key, &circuit, k, columns)?;
        let parameters = decode(get(Role::LedgerParameters)?)?;
        Ok(Self {
            native,
            prover,
            circuit,
            verifier,
            parameters,
            entrypoint: plan.entrypoint,
        })
    }
}

/// Frozen intent and exact native statement. No private preimage accessor or Debug implementation.
pub struct PreparedProof {
    intent: NativeIntent,
    deployment: Option<NativeIntent>,
    material: Material,
    statement: Vec<Fr>,
    activity: Vec<Option<usize>>,
    required_parameters_sha256: Option<String>,
    contract_binding: Option<ContractStateBinding>,
}
impl PreparedProof {
    /// Construct the source-selected call in memory using host-owned cryptographic entropy.
    /// Authentication and public material validation precede private input parsing.
    pub fn from_config(
        bundle: &VerifiedBundle,
        private_config: &[u8],
        ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        Self::from_config_with_context(bundle, private_config, ttl, None, rng)
    }

    /// Prepare using an explicit prospective block context from the host.
    /// Ledger execution rechecks any clock predicate in the resulting transcript.
    pub fn from_config_in_block(
        bundle: &VerifiedBundle,
        private_config: &[u8],
        ttl: u64,
        block: &BlockContext,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        Self::from_config_with_context(bundle, private_config, ttl, Some(block), rng)
    }

    fn from_config_with_context(
        bundle: &VerifiedBundle,
        private_config: &[u8],
        ttl: u64,
        block: Option<&BlockContext>,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        let material = Material::retained(bundle)?;
        if private_config.len() > 1_048_576 {
            return Err(Error::Limit);
        }
        let config =
            crate::parse_private_config(private_config).map_err(|_| Error::InvalidPrivateInput)?;
        let plan: Plan = serde_json::from_slice(
            bundle
                .file(Role::Plan)
                .map_err(|_| Error::InvalidArtifacts)?,
        )
        .map_err(|_| Error::InvalidArtifacts)?;
        let (deploy, intent) = crate::assembly::prepare_call(
            &plan,
            &config,
            &material.parameters,
            material.verifier.clone(),
            &material.circuit,
            ttl,
            block,
            rng,
        )
        .map_err(|_| Error::InvalidPrivateInput)?;
        let mut prepared = Self::freeze(material, intent)?;
        prepared.deployment = Some(deploy);
        Ok(prepared)
    }

    /// Prepare a proof from the exact native source input map and retained deployment target.
    /// Callers must obtain `inputs` from a completed authenticated Control invocation.
    pub fn from_witness_inputs(
        bundle: &VerifiedBundle,
        target: &WitnessTarget,
        inputs: BTreeMap<String, Json>,
        ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        let mut inputs = SecretInputs(inputs);
        if !target.context_matches(
            bundle.authenticated_manifest_sha256().unwrap_or_default(),
            crate::profile::NAME,
            ttl,
        ) {
            return Err(Error::BindingMismatch);
        }
        target.authenticated_control_target(0, bundle)?;
        let material = Material::retained(bundle)?;
        if material.circuit.k() != target.k {
            return Err(Error::InvalidParameters);
        }
        let plan: Plan = serde_json::from_slice(
            bundle
                .file(Role::Plan)
                .map_err(|_| Error::InvalidArtifacts)?,
        )
        .map_err(|_| Error::InvalidArtifacts)?;
        let config = SecretConfig(crate::Config {
            inputs: std::mem::take(&mut inputs.0),
            state: BTreeMap::new(),
            negative_cases: Vec::new(),
        });
        let call = crate::assembly::prepare_call_for_target(
            &plan,
            &config.0,
            &material.parameters,
            material.verifier.clone(),
            &material.circuit,
            ttl,
            &target.deployment,
            rng,
        );
        let call = call.map_err(|_| Error::InvalidPrivateInput)?;
        let mut prepared = Self::freeze(material, call)?;
        prepared.deployment = Some(target.deployment.intent.clone());
        prepared.required_parameters_sha256 = Some(target.proof_parameters_sha256.clone());
        let (address, entrypoint) = prepared.call_target()?;
        if address != target.contract_address() || entrypoint != target.entrypoint() {
            return Err(Error::BindingMismatch);
        }
        Ok(prepared)
    }

    pub(crate) fn from_contract_witness_inputs(
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Json>,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        Self::from_contract_witness_inputs_with_block(target, current, inputs, None, rng)
    }

    pub(crate) fn from_contract_witness_inputs_with_block(
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Json>,
        block: Option<&BlockContext>,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        Self::from_contract_witness_inputs_with_context(
            target,
            current,
            inputs,
            Map::new(),
            block,
            None,
            rng,
        )
    }

    pub(crate) fn from_contract_witness_inputs_with_com_indices(
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Json>,
        com_indices: Map<Commitment, u64, Db>,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        Self::from_contract_witness_inputs_with_context(
            target,
            current,
            inputs,
            com_indices,
            None,
            None,
            rng,
        )
    }

    fn from_contract_witness_inputs_with_context(
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Json>,
        com_indices: Map<Commitment, u64, Db>,
        block: Option<&BlockContext>,
        unshielded_scope: Option<&SnapshotUnshieldedSpendScope<'_>>,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        let mut inputs = SecretInputs(inputs);
        if !target.context_matches(current) {
            return Err(Error::BindingMismatch);
        }
        let material = target.selected_material()?;
        if let Some(scope) = unshielded_scope {
            let snapshot = &scope.snapshot().state;
            ensure_current_state_matches_snapshot(target, current, snapshot)?;
            if *snapshot.parameters != material.parameters {
                return Err(Error::InvalidParameters);
            }
        }
        let bundle = target.bundle()?;
        if bundle.authenticated_manifest_sha256() != Some(target.manifest.as_str()) {
            return Err(Error::BindingMismatch);
        }
        let plan: Plan = serde_json::from_slice(
            bundle
                .file(Role::Plan)
                .map_err(|_| Error::InvalidArtifacts)?,
        )
        .map_err(|_| Error::InvalidArtifacts)?;
        let config = SecretConfig(crate::Config {
            inputs: std::mem::take(&mut inputs.0),
            state: BTreeMap::new(),
            negative_cases: Vec::new(),
        });
        let (call, predicted) = crate::assembly::prepare_call_for_ready_state(
            &plan,
            &target.inner.bundles.contract_name(),
            &target.operation,
            &config.0,
            &material.parameters,
            ContractOperation::new(Some(material.verifier.clone()), None),
            &material.circuit,
            target.ttl,
            &target.inner.deployment,
            &target.inner.ready_state,
            &current.state,
            &com_indices,
            block,
            unshielded_scope.map(|scope| PublicAddress::User(scope.address())),
            rng,
        )
        .map_err(|_| Error::InvalidPrivateInput)?;
        let expected_state = encode(&predicted)?;
        let mut prepared = Self::freeze_with_unshielded_scope(material, call, unshielded_scope)?;
        prepared.required_parameters_sha256 = Some(target.proof_parameters_sha256.clone());
        let (address, entrypoint) = prepared.call_target()?;
        if address != target.contract_address() || entrypoint != target.operation {
            return Err(Error::BindingMismatch);
        }
        prepared.contract_binding = Some(ContractStateBinding {
            contract_set_identity: target.contract_set_identity().to_owned(),
            deployment_identity: target.deployment_identity().to_owned(),
            state_schema_sha256: target.state_schema_sha256().to_owned(),
            address,
            operation: entrypoint,
            context_identity: current.identity.clone(),
            current_state_sha256: Some(hex::encode(Sha256::digest(&current.state_bytes))),
            current_state: Some(current.state_bytes.clone()),
            expected_state,
            deployment: false,
        });
        Ok(prepared)
    }

    /// Re-freeze a host-balanced intent. This first slice accepts one call and no offers/dust.
    /// Native intent inputs contain private witnesses and need private storage.
    pub fn from_intent(bundle: &VerifiedBundle, intent: NativeIntent) -> Result<Self> {
        Self::freeze(Material::retained(bundle)?, intent)
    }
    fn freeze(material: Material, intent: NativeIntent) -> Result<Self> {
        Self::freeze_with_unshielded_scope(material, intent, None)
    }

    fn freeze_with_unshielded_scope(
        material: Material,
        mut intent: NativeIntent,
        scope: Option<&SnapshotUnshieldedSpendScope<'_>>,
    ) -> Result<Self> {
        if intent.actions.len() != 1
            || intent.dust_actions.is_some()
            || intent.guaranteed_unshielded_offer.is_some()
            || intent.fallible_unshielded_offer.is_some()
        {
            return Err(Error::InvalidIntent);
        }
        intent.guaranteed_unshielded_offer = scope
            .map(SnapshotUnshieldedSpendScope::guaranteed_offer)
            .map(storage::arena::Sp::new);
        let Some(ContractAction::Call(call)) = intent.actions.iter_deref().next() else {
            return Err(Error::InvalidIntent);
        };
        if call.entry_point.0 != material.entrypoint.as_bytes() {
            return Err(Error::InvalidIntent);
        }
        let ProofPreimageVersioned::V2(preimage) = &call.proof else {
            return Err(Error::InvalidIntent);
        };
        if preimage.key_location.0.as_ref() != material.entrypoint {
            return Err(Error::InvalidIntent);
        }
        let activity = preimage
            .check(&material.circuit)
            .map_err(|_| Error::InvalidIntent)?;
        let preview = preview_call_activity(
            call,
            &activity,
            intent.binding_commitment.into(),
            &material.parameters.cost_model.runtime_cost_model,
        )?;
        let statement = preview.statement;
        if statement.get(1) != Some(&call.communication_commitment)
            || preimage
                .communications_commitment
                .map(|(commitment, _)| commitment)
                != Some(call.communication_commitment)
        {
            return Err(Error::BindingMismatch);
        }
        let result = Self {
            intent,
            deployment: None,
            material,
            statement,
            activity,
            required_parameters_sha256: None,
            contract_binding: None,
        };
        result.validate_statement_preimage()?;
        Ok(result)
    }
    fn preimage(&self) -> Result<&ProofPreimage> {
        let Some(ContractAction::Call(call)) = self.intent.actions.iter_deref().next() else {
            return Err(Error::InvalidIntent);
        };
        let ProofPreimageVersioned::V2(preimage) = &call.proof else {
            return Err(Error::InvalidIntent);
        };
        Ok(preimage)
    }
    fn validate_statement_preimage(&self) -> Result<()> {
        let mut preimage = self.preimage()?.clone();
        preimage.binding_input = self.statement[0];
        // The selected IR checks exact input/output packing and communication binding.
        let activity = preimage
            .check(&self.material.circuit)
            .map_err(|_| Error::BindingMismatch)?;
        if activity != self.activity {
            return Err(Error::UnsupportedActivity);
        }
        let Some(ContractAction::Call(call)) = self.intent.actions.iter_deref().next() else {
            return Err(Error::InvalidIntent);
        };
        let preview = preview_call_activity(
            call,
            &activity,
            self.intent.binding_commitment.into(),
            &self.material.parameters.cost_model.runtime_cost_model,
        )?;
        if preview.statement != self.statement {
            return Err(Error::BindingMismatch);
        }
        Ok(())
    }
    pub fn deployment_intent(&self) -> Option<&NativeIntent> {
        self.deployment.as_ref()
    }
    pub(crate) fn call_target(&self) -> Result<(String, String)> {
        let Some(ContractAction::Call(call)) = self.intent.actions.iter_deref().next() else {
            return Err(Error::InvalidIntent);
        };
        let entrypoint =
            String::from_utf8(call.entry_point.0.clone()).map_err(|_| Error::InvalidIntent)?;
        Ok((hex::encode(call.address.0.0), entrypoint))
    }
    pub fn k(&self) -> u8 {
        self.material.circuit.k()
    }
    pub fn profile(&self) -> &'static str {
        crate::profile::NAME
    }
    fn validate_parameters(&self, params: &TrustedParameters) -> Result<()> {
        if params.k != self.k()
            || self
                .required_parameters_sha256
                .as_deref()
                .is_some_and(|digest| digest != params.sha256())
        {
            return Err(Error::InvalidParameters);
        }
        Ok(())
    }
    /// Explicit private serialization for durable retries. Re-proving requires fresh entropy.
    pub fn private_intent_bytes(&self) -> Result<Vec<u8>> {
        encode(&self.intent)
    }
    /// Retain an explicit private service request without retaining a future or callback.
    /// The preimage uses the same frozen binding checked by the native intent prover.
    pub fn private_request_payload(
        &self,
        params: &TrustedParameters,
        max_response_bytes: usize,
    ) -> Result<zeroize::Zeroizing<Vec<u8>>> {
        if max_response_bytes == 0 || max_response_bytes > MAX_RESPONSE {
            return Err(Error::Limit);
        }
        self.validate_parameters(params)?;
        self.validate_statement_preimage()?;
        let mut preimage = self.preimage()?.clone();
        preimage.binding_input = self.statement[0];
        ProofRequest {
            preimage: &preimage,
            material: &self.material.native,
            prover: &self.material.prover,
            parameters: params,
            max_response_bytes,
            expected_statement: &self.statement,
            expected_activity: &self.activity,
        }
        .private_wire_payload()
    }
    /// Resume a pulled service request through the same verifier and native attachment path.
    pub async fn attach_response(
        &self,
        params: &TrustedParameters,
        response: &[u8],
        max_response_bytes: usize,
    ) -> Result<ProvedIntent> {
        struct Supplied<'a>(&'a [u8]);
        impl ProofService for Supplied<'_> {
            async fn prove(
                &self,
                _: ProofRequest<'_>,
            ) -> std::result::Result<Vec<u8>, ServiceError> {
                Ok(self.0.to_vec())
            }
        }
        if response.is_empty() || response.len() > max_response_bytes {
            return Err(Error::Limit);
        }
        self.prove(
            &Supplied(response),
            params,
            max_response_bytes,
            futures::future::pending(),
        )
        .await
    }
    /// Explicit local service adapter for a host worker with fresh host-owned entropy.
    /// Returns the service V2 encoding, separate from the verified attached ledger V3 result.
    pub async fn local_response(
        &self,
        params: &TrustedParameters,
        max_response_bytes: usize,
        rng: impl Rng + CryptoRng,
    ) -> Result<Vec<u8>> {
        let proved = self
            .prove(
                &LocalProver::new(rng),
                params,
                max_response_bytes,
                futures::future::pending(),
            )
            .await?;
        let Some(ContractAction::Call(call)) = proved.native().actions.iter_deref().next() else {
            return Err(Error::Attachment);
        };
        let ProofVersioned::V3(proof) = &call.proof else {
            return Err(Error::Attachment);
        };
        encode(&ProofVersioned::V2(proof.clone()))
    }
    /// Verify a versioned service response against this frozen call, retained key and trusted SRS.
    /// This does not attach, sign or submit anything.
    pub fn verify_response(
        &self,
        params: &TrustedParameters,
        response: &[u8],
        max_response_bytes: usize,
    ) -> Result<()> {
        self.verified_response(params, response, max_response_bytes)
            .map(|_| ())
    }
    fn verified_response(
        &self,
        params: &TrustedParameters,
        response: &[u8],
        max_response_bytes: usize,
    ) -> Result<Proof> {
        self.validate_parameters(params)?;
        verify_service_response(
            &self.material.verifier,
            params,
            &self.statement,
            response,
            max_response_bytes,
        )
    }
    /// Race proof construction against a host timer/cancellation future. Dropping this future
    /// drops the provider future. CPU-only native proving requires a host worker for hard stop.
    pub async fn prove<S: ProofService>(
        &self,
        service: &S,
        params: &TrustedParameters,
        max_response_bytes: usize,
        stop: impl Future<Output = Abort>,
    ) -> Result<ProvedIntent> {
        if max_response_bytes == 0 || max_response_bytes > MAX_RESPONSE {
            return Err(Error::Limit);
        }
        self.validate_parameters(params)?;
        let preimage = self.preimage()?;
        let calls = [SelectedProof {
            key: &preimage.key_location,
            material: &self.material,
            statement: &self.statement,
            activity: &self.activity,
            parameters: params,
        }];
        let intent = prove_intent(&self.intent, &calls, service, max_response_bytes, stop).await?;
        if intent.guaranteed_unshielded_offer != self.intent.guaranteed_unshielded_offer
            || intent.fallible_unshielded_offer != self.intent.fallible_unshielded_offer
        {
            return Err(Error::BindingMismatch);
        }
        let Some(ContractAction::Call(call)) = intent.actions.iter_deref().next() else {
            return Err(Error::Attachment);
        };
        if call
            .public_inputs(intent.binding_commitment.into())
            .map_err(|_| Error::Attachment)?
            != self.statement
        {
            return Err(Error::BindingMismatch);
        }
        let ProofVersioned::V3(proof) = &call.proof else {
            return Err(Error::Attachment);
        };
        self.material
            .verifier
            .verify(&params.verifier, proof, self.statement.iter().copied())
            .map_err(|_| Error::InvalidProof)?;
        ProvedIntent::checked_encoding(intent, self.contract_binding.clone())
    }
}

/// Prepare the native relay and destination calls in fixed ledger order. Both calls
/// evaluate against the same snapshot and booked index map. The destination's
/// communication randomness is the opening committed by the relay source call.
pub(crate) fn prepare_relay_destination_composition<'target, 'state>(
    relay: CurrentStateCompositionCall<'target, 'state>,
    destination: CurrentStateCompositionCall<'target, 'state>,
    snapshot: &LedgerState<Db>,
    booked_indices: &BookedComIndices,
    destination_communication_commitment_rand: Fr,
    rng: &mut (impl Rng + CryptoRng),
) -> Result<(PreparedComposition<'target>, [ContractStateBinding; 2])> {
    let CurrentStateCompositionCall {
        target: relay_target,
        current: relay_current_slot,
        parameters: relay_parameters,
        inputs: relay_input_values,
    } = relay;
    let CurrentStateCompositionCall {
        target: destination_target,
        current: destination_current_slot,
        parameters: destination_parameters,
        inputs: destination_input_values,
    } = destination;
    let relay_config = SecretConfig(Config {
        inputs: relay_input_values,
        state: BTreeMap::new(),
        negative_cases: Vec::new(),
    });
    let destination_config = SecretConfig(Config {
        inputs: destination_input_values,
        state: BTreeMap::new(),
        negative_cases: Vec::new(),
    });

    if destination_communication_commitment_rand == Fr::from(0u64)
        || relay_target.ttl == 0
        || relay_target.ttl != destination_target.ttl
        || relay_target.contract_address() == destination_target.contract_address()
    {
        return Err(Error::BindingMismatch);
    }
    let relay_current = relay_current_slot
        .as_ref()
        .ok_or(Error::BindingMismatch)?;
    let destination_current = destination_current_slot
        .as_ref()
        .ok_or(Error::BindingMismatch)?;
    ensure_current_state_matches_snapshot(relay_target, relay_current, snapshot)?;
    ensure_current_state_matches_snapshot(destination_target, destination_current, snapshot)?;

    let relay_material = relay_target.selected_material()?;
    let destination_material = destination_target.selected_material()?;
    ensure_target_parameters(relay_target, relay_parameters, &relay_material)?;
    ensure_target_parameters(
        destination_target,
        destination_parameters,
        &destination_material,
    )?;
    let relay_plan = target_plan(relay_target)?;
    let destination_plan = target_plan(destination_target)?;
    let ttl = relay_target.ttl;
    let relay_name = relay_target.inner.bundles.contract_name();
    let destination_name = destination_target.inner.bundles.contract_name();
    let relay_call = crate::assembly::prepare_checked_call_for_ready_state(
        &relay_plan,
        relay_name,
        &relay_target.operation,
        &relay_config.0,
        &snapshot.parameters,
        ContractOperation::new(Some(relay_material.verifier.clone()), None),
        &relay_material.circuit,
        ttl,
        &relay_target.inner.deployment,
        &relay_target.inner.ready_state,
        &relay_current.state,
        booked_indices,
        None,
        None,
        rng,
    )
    .map_err(|_| Error::InvalidPrivateInput)?;
    let relay_address = parse_contract_address(relay_target.contract_address())?;
    let destination_call = crate::assembly::prepare_checked_call_for_ready_state(
        &destination_plan,
        destination_name,
        &destination_target.operation,
        &destination_config.0,
        &snapshot.parameters,
        ContractOperation::new(Some(destination_material.verifier.clone()), None),
        &destination_material.circuit,
        ttl,
        &destination_target.inner.deployment,
        &destination_target.inner.ready_state,
        &destination_current.state,
        booked_indices,
        Some(PublicAddress::Contract(relay_address)),
        Some(destination_communication_commitment_rand),
        rng,
    )
    .map_err(|_| Error::InvalidPrivateInput)?;

    let checked_calls = [
        CheckedNativeCall {
            execution: &relay_call.execution,
            circuit: &relay_material.circuit,
            initial_context: relay_call.initial_context.clone(),
            entry_point: relay_call.entry_point.clone(),
            communication_commitment_rand: relay_call.communication_commitment_rand,
        },
        CheckedNativeCall {
            execution: &destination_call.execution,
            circuit: &destination_material.circuit,
            initial_context: destination_call.initial_context.clone(),
            entry_point: destination_call.entry_point.clone(),
            communication_commitment_rand: destination_call.communication_commitment_rand,
        },
    ];
    let intent = crate::assembly::assemble_checked_calls(
        &checked_calls,
        &snapshot.parameters,
        ttl,
        rng,
    )
    .map_err(|_| Error::InvalidIntent)?;
    let selections = [
        CompositionMaterial {
            bundle: relay_target.bundle()?,
            parameters: relay_parameters,
        },
        CompositionMaterial {
            bundle: destination_target.bundle()?,
            parameters: destination_parameters,
        },
    ];
    let prepared = PreparedComposition::from_intent(intent, snapshot, &selections)?;
    let bindings = [
        current_state_binding(relay_target, relay_current, &relay_call.predicted)?,
        current_state_binding(
            destination_target,
            destination_current,
            &destination_call.predicted,
        )?,
    ];

    // These tokens are single-use. Keep both intact for every earlier error path.
    let _relay_token = relay_current_slot.take().ok_or(Error::BindingMismatch)?;
    let _destination_token = destination_current_slot.take().ok_or(Error::BindingMismatch)?;
    Ok((prepared, bindings))
}

pub(crate) fn ensure_current_state_matches_snapshot(
    target: &ContractOperationTarget,
    current: &CurrentStateContext,
    snapshot: &LedgerState<Db>,
) -> Result<()> {
    if !target.context_matches(current) || current.state_bytes.len() > MAX_NATIVE_STATE {
        return Err(Error::BindingMismatch);
    }
    let address = parse_contract_address(target.contract_address())?;
    let deployed = snapshot
        .contract
        .get(&address)
        .ok_or(Error::BindingMismatch)?;
    if encode(deployed)? != current.state_bytes
        || encode(&current.state)? != current.state_bytes
    {
        return Err(Error::BindingMismatch);
    }
    Ok(())
}

pub(crate) fn ensure_current_state_matches_verified_snapshot(
    target: &ContractOperationTarget,
    current: &CurrentStateContext,
    snapshot: &Snapshot,
) -> Result<()> {
    if current.chain_identity.as_ref() != Some(&snapshot.chain) {
        return Err(Error::BindingMismatch);
    }
    ensure_current_state_matches_snapshot(target, current, &snapshot.state)
}

fn ensure_target_parameters(
    target: &ContractOperationTarget,
    parameters: &TrustedParameters,
    material: &Material,
) -> Result<()> {
    if parameters.k() != target.k
        || parameters.sha256() != target.proof_parameters_sha256.as_str()
        || material.circuit.k() != target.k
    {
        return Err(Error::InvalidParameters);
    }
    Ok(())
}

fn target_plan(target: &ContractOperationTarget) -> Result<Plan> {
    serde_json::from_slice(
        target
            .bundle()?
            .file(Role::Plan)
            .map_err(|_| Error::InvalidArtifacts)?,
    )
    .map_err(|_| Error::InvalidArtifacts)
}

fn parse_contract_address(address: &str) -> Result<coin_structure::contract::ContractAddress> {
    let bytes: [u8; 32] = hex::decode(address)
        .map_err(|_| Error::BindingMismatch)?
        .try_into()
        .map_err(|_| Error::BindingMismatch)?;
    Ok(coin_structure::contract::ContractAddress(
        base_crypto::hash::HashOutput(bytes),
    ))
}

fn current_state_binding(
    target: &ContractOperationTarget,
    current: &CurrentStateContext,
    predicted: &ContractState<Db>,
) -> Result<ContractStateBinding> {
    Ok(ContractStateBinding {
        contract_set_identity: target.contract_set_identity().to_owned(),
        deployment_identity: target.deployment_identity().to_owned(),
        state_schema_sha256: target.state_schema_sha256().to_owned(),
        address: target.contract_address().to_owned(),
        operation: target.operation.clone(),
        context_identity: current.identity.clone(),
        current_state_sha256: Some(hex::encode(Sha256::digest(&current.state_bytes))),
        current_state: Some(current.state_bytes.clone()),
        expected_state: encode(predicted)?,
        deployment: false,
    })
}

/// Native attached result only becomes available after local cryptographic verification.
/// The binding is frozen. Subsequent changes to bound call/intent fields require re-proving.
pub struct ProvedIntent {
    intent: ProvedNativeIntent,
    bytes: Vec<u8>,
    contract_binding: Option<ContractStateBinding>,
}
impl ProvedIntent {
    fn checked_encoding(
        intent: ProvedNativeIntent,
        contract_binding: Option<ContractStateBinding>,
    ) -> Result<Self> {
        let bytes = encode(&intent)?;
        let decoded: ProvedNativeIntent = decode(&bytes).map_err(|_| Error::Attachment)?;
        if encode(&decoded)? != bytes {
            return Err(Error::Attachment);
        }
        Ok(Self {
            intent: decoded,
            bytes,
            contract_binding,
        })
    }

    pub fn native(&self) -> &ProvedNativeIntent {
        &self.intent
    }
    pub fn serialized(&self) -> &[u8] {
        &self.bytes
    }
    pub(crate) fn contract_binding(&self) -> Option<&ContractStateBinding> {
        self.contract_binding.as_ref()
    }
    /// Public proof result. The private unsealed binding randomness is replaced by its commitment.
    /// This projection supplies neither funding nor the sealed transaction binding proof.
    pub fn public_serialized(&self) -> Result<Vec<u8>> {
        let intent: PublicProvedNativeIntent = Intent {
            guaranteed_unshielded_offer: self.intent.guaranteed_unshielded_offer.clone(),
            fallible_unshielded_offer: self.intent.fallible_unshielded_offer.clone(),
            actions: self.intent.actions.clone(),
            dust_actions: self.intent.dust_actions.clone(),
            ttl: self.intent.ttl,
            binding_commitment: self.intent.binding_commitment.into(),
        };
        let bytes = encode(&intent)?;
        let decoded: PublicProvedNativeIntent = decode(&bytes)?;
        if encode(&decoded)? != bytes {
            return Err(Error::Attachment);
        }
        Ok(bytes)
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Abort {
    Cancelled,
    Deadline,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ServiceError;
impl fmt::Display for ServiceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("noctium_proof_service_failure")
    }
}
impl std::error::Error for ServiceError {}

/// Explicit private-data disclosure to a host-authorized proof service.
/// No ambient network/filesystem behavior lives in this trait or in the core.
#[allow(async_fn_in_trait)]
pub trait ProofService {
    async fn prove(&self, request: ProofRequest<'_>) -> std::result::Result<Vec<u8>, ServiceError>;
}
/// Private request, intentionally lacks Debug. A remote adapter must obtain host authority
/// before transmitting this witness-bearing material and enforce limits while reading bytes.
pub struct ProofRequest<'a> {
    preimage: &'a ProofPreimage,
    material: &'a ProvingKeyMaterial,
    prover: &'a ProverKey<IrSource>,
    pub parameters: &'a TrustedParameters,
    pub max_response_bytes: usize,
    expected_statement: &'a [Fr],
    expected_activity: &'a [Option<usize>],
}
impl ProofRequest<'_> {
    /// Official /prove wire payload: (versioned preimage, retained keys+IR, no binding override).
    /// Binding is already replaced by the upstream native intent prover's exact value.
    pub fn private_wire_payload(&self) -> Result<zeroize::Zeroizing<Vec<u8>>> {
        encode(&(
            ProofPreimageVersioned::V2(std::sync::Arc::new(self.preimage.clone())),
            Some(self.material.clone()),
            Option::<Fr>::None,
        ))
        .map(zeroize::Zeroizing::new)
    }
    /// Run the selected pinned native prover with host-supplied entropy and parameters.
    pub async fn prove_locally(
        self,
        rng: impl Rng + CryptoRng,
    ) -> std::result::Result<Vec<u8>, ServiceError> {
        let ir = IrSource::load(&self.material.ir_source[..]).map_err(|_| ServiceError)?;
        let (proof, statement, activity) = ir
            .prove(rng, self.parameters, self.prover.clone(), self.preimage)
            .await
            .map_err(|_| ServiceError)?;
        if statement != self.expected_statement || activity != self.expected_activity {
            return Err(ServiceError);
        }
        let response = encode(&ProofVersioned::V2(proof)).map_err(|_| ServiceError)?;
        if response.len() > self.max_response_bytes {
            return Err(ServiceError);
        }
        Ok(response)
    }
}
/// One-use local prover. The host supplies fresh entropy for every attempt.
pub struct LocalProver<R>(RefCell<Option<R>>);
impl<R: Rng + CryptoRng> LocalProver<R> {
    pub fn new(rng: R) -> Self {
        Self(RefCell::new(Some(rng)))
    }
}
impl<R: Rng + CryptoRng> ProofService for LocalProver<R> {
    async fn prove(&self, request: ProofRequest<'_>) -> std::result::Result<Vec<u8>, ServiceError> {
        let rng = self.0.borrow_mut().take().ok_or(ServiceError)?;
        request.prove_locally(rng).await
    }
}
fn verify_service_response(
    verifier: &VerifierKey,
    params: &TrustedParameters,
    statement: &[Fr],
    response: &[u8],
    max_response_bytes: usize,
) -> Result<Proof> {
    if max_response_bytes == 0
        || max_response_bytes > MAX_RESPONSE
        || response.is_empty()
        || response.len() > max_response_bytes
    {
        return Err(Error::Limit);
    }
    // The pinned /prove transport version is independent of ledger V3 attachment.
    let ProofVersioned::V2(proof) = decode(response).map_err(|_| Error::InvalidResponse)? else {
        return Err(Error::InvalidResponse);
    };
    verifier
        .verify(&params.verifier, &proof, statement.iter().copied())
        .map_err(|_| Error::InvalidProof)?;
    Ok(proof)
}

struct SelectedProof<'a> {
    key: &'a KeyLocation,
    material: &'a Material,
    statement: &'a [Fr],
    activity: &'a [Option<usize>],
    parameters: &'a TrustedParameters,
}

async fn prove_intent<S: ProofService>(
    intent: &NativeIntent,
    calls: &[SelectedProof<'_>],
    service: &S,
    max_response_bytes: usize,
    stop: impl Future<Output = Abort>,
) -> Result<ProvedNativeIntent> {
    if max_response_bytes == 0 || max_response_bytes > MAX_RESPONSE {
        return Err(Error::Limit);
    }
    let parameters = &calls
        .first()
        .ok_or(Error::InvalidIntent)?
        .material
        .parameters;
    let outcome = Rc::new(RefCell::new(None));
    let provider = CheckedProvider {
        calls,
        service,
        max_response_bytes,
        outcome: outcome.clone(),
    };
    let work = intent
        .prove(0, provider, &parameters.cost_model.runtime_cost_model)
        .fuse();
    let stop = stop.fuse();
    pin_mut!(work, stop);
    let result = select_biased! {
        reason = stop => return Err(match reason { Abort::Cancelled => Error::Cancelled, Abort::Deadline => Error::Deadline }),
        result = work => result,
    };
    result
        .map(|(_, intent)| intent)
        .map_err(|_| outcome.borrow().unwrap_or(Error::Attachment))
}

struct CheckedProvider<'a, S> {
    calls: &'a [SelectedProof<'a>],
    service: &'a S,
    max_response_bytes: usize,
    outcome: Rc<RefCell<Option<Error>>>,
}
impl<S> Clone for CheckedProvider<'_, S> {
    fn clone(&self) -> Self {
        Self {
            calls: self.calls,
            service: self.service,
            max_response_bytes: self.max_response_bytes,
            outcome: self.outcome.clone(),
        }
    }
}
impl<S> Resolver for CheckedProvider<'_, S> {
    async fn resolve_key(&self, key: KeyLocation) -> io::Result<Option<ProvingKeyMaterial>> {
        Ok(self
            .calls
            .iter()
            .find(|call| *call.key == key)
            .map(|call| call.material.native.clone()))
    }
}
impl<S: ProofService> ProvingProvider for CheckedProvider<'_, S> {
    async fn check(&self, preimage: &ProofPreimage) -> anyhow::Result<Vec<Option<usize>>> {
        let result = self.selected(preimage).and_then(|selected| {
            preimage
                .check(&selected.material.circuit)
                .ok()
                .filter(|activity| *activity == selected.activity)
                .ok_or(Error::InvalidIntent)
        });
        if let Err(error) = &result {
            *self.outcome.borrow_mut() = Some(*error);
        }
        result.map_err(Into::into)
    }
    async fn prove(self, preimage: &ProofPreimage, overwrite: Option<Fr>) -> anyhow::Result<Proof> {
        let result = self.checked_prove(preimage, overwrite).await;
        if let Err(error) = &result {
            *self.outcome.borrow_mut() = Some(*error);
        }
        result.map_err(Into::into)
    }
    fn split(&mut self) -> Self {
        self.clone()
    }
    fn resolver(&self) -> &impl Resolver {
        self
    }
}
impl<S: ProofService> CheckedProvider<'_, S> {
    fn selected(&self, preimage: &ProofPreimage) -> Result<&SelectedProof<'_>> {
        let commitment = preimage
            .communications_commitment
            .ok_or(Error::BindingMismatch)?
            .0;
        self.calls
            .iter()
            .find(|call| {
                *call.key == preimage.key_location && call.statement.get(1) == Some(&commitment)
            })
            .ok_or(Error::BindingMismatch)
    }

    async fn checked_prove(
        &self,
        preimage: &ProofPreimage,
        overwrite: Option<Fr>,
    ) -> Result<Proof> {
        let selected = self.selected(preimage)?;
        if overwrite != selected.statement.first().copied() {
            return Err(Error::BindingMismatch);
        }
        let mut preimage = preimage.clone();
        preimage.binding_input = overwrite.ok_or(Error::BindingMismatch)?;
        let response = self
            .service
            .prove(ProofRequest {
                preimage: &preimage,
                material: &selected.material.native,
                prover: &selected.material.prover,
                parameters: selected.parameters,
                max_response_bytes: self.max_response_bytes,
                expected_statement: selected.statement,
                expected_activity: selected.activity,
            })
            .await
            .map_err(|_| Error::Service)?;
        verify_service_response(
            &selected.material.verifier,
            selected.parameters,
            selected.statement,
            &response,
            self.max_response_bytes,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures::{executor::block_on, future::pending};
    use rand::rngs::OsRng;

    #[test]
    #[cfg(feature = "zkir-321")]
    #[ignore = "requires the externally pinned confidential-token bundle index"]
    fn staged_installation_and_authority_rotation_bind_current_state() {
        let index = std::fs::read(std::env::var("NOCTIUM_STAGED_BUNDLE_INDEX").unwrap()).unwrap();
        assert_eq!(
            crate::artifacts::digest(&index),
            std::env::var("NOCTIUM_STAGED_BUNDLE_INDEX_SHA256").unwrap()
        );
        let locations: Json = serde_json::from_slice(&index).unwrap();
        let locations = locations.as_array().unwrap();
        let names: Vec<_> = locations
            .iter()
            .map(|entry| entry["name"].as_str().unwrap().to_owned())
            .collect();
        let bundles = ContractBundleSet::new(
            locations
                .iter()
                .map(|entry| {
                    crate::artifacts::verify(
                        std::path::Path::new(entry["directory"].as_str().unwrap()),
                        Some(entry["manifestSha256"].as_str().unwrap()),
                    )
                    .unwrap()
                })
                .collect(),
        )
        .unwrap();
        let owner = base_crypto::schnorr::SigningKey::sample(&mut OsRng);
        let foreign = base_crypto::schnorr::SigningKey::sample(&mut OsRng);
        let target = WitnessContractTarget::from_staged_state_config(
            bundles,
            br#"{"state":{"name_":"Noctium Token","symbol_":"NOC","decimals_":"6"}}"#,
            &names[..8],
            owner.verifying_key(),
            2_000_000_000,
            &mut OsRng,
        )
        .unwrap();
        let initial = target.inner.deployment.ready_state().unwrap();
        assert_eq!(initial.maintenance_authority.counter, 0);
        let bytes = encode(&initial).unwrap();
        let current = target
            .deployment_binding("registerWithKey")
            .unwrap()
            .admit_committed_state(&bytes, &bytes, &"a".repeat(64), true)
            .unwrap();
        assert_eq!(initial.operations.size(), 8);
        assert!(
            target
                .prepare_installation(
                    &current,
                    &names[8..],
                    &foreign,
                    true,
                    2_000_000_000,
                    &mut OsRng
                )
                .is_err()
        );
        assert!(
            target
                .prepare_installation(
                    &current,
                    &names[..1],
                    &owner,
                    false,
                    2_000_000_000,
                    &mut OsRng
                )
                .is_err()
        );
        assert!(
            target
                .prepare_installation(
                    &current,
                    &names[8..9],
                    &owner,
                    true,
                    2_000_000_000,
                    &mut OsRng
                )
                .is_err()
        );
        let (intent, binding) = target
            .prepare_installation(
                &current,
                &names[8..],
                &owner,
                true,
                2_000_000_000,
                &mut OsRng,
            )
            .unwrap();
        let expected: ContractState<Db> = decode(&binding.expected_state).unwrap();
        let mut ready = target.inner.ready_state.clone();
        ready.maintenance_authority.counter = 1;
        assert!(expected == ready);
        assert_eq!(expected.operations.size(), 16);
        assert!(expected.maintenance_authority.committee.is_empty());
        let Some(ContractAction::Maintain(update)) = intent.actions.iter_deref().next() else {
            panic!("expected native maintenance")
        };
        assert_eq!(update.counter, 0);
        let signature = update.signatures.iter_deref().next().unwrap();
        let Signature::Schnorr(signature) = &signature.1 else {
            panic!("expected Schnorr signature")
        };
        assert!(
            owner
                .verifying_key()
                .verify(&update.data_to_sign(), signature)
        );
        let proved = crate::native_client::prove_maintenance(
            &intent,
            &ledger::structure::INITIAL_PARAMETERS,
        )
        .unwrap();
        assert_eq!(proved.actions.len(), 1);
        let admitted = binding
            .admit_committed_state(
                &binding.expected_state,
                &binding.expected_state,
                &"b".repeat(64),
                false,
            )
            .unwrap();
        assert!(admitted.state.operations == target.inner.ready_state.operations);
        assert!(admitted.state.maintenance_authority == ready.maintenance_authority);

        let next_owner = base_crypto::schnorr::SigningKey::sample(&mut OsRng);
        let (install_intent, install_binding) = target
            .prepare_installation(
                &current,
                &names[8..],
                &owner,
                false,
                2_000_000_000,
                &mut OsRng,
            )
            .unwrap();
        let installed_state: ContractState<Db> = decode(&install_binding.expected_state).unwrap();
        assert_eq!(
            installed_state.operations,
            target.inner.ready_state.operations
        );
        assert_eq!(installed_state.maintenance_authority.counter, 1);
        assert_eq!(
            installed_state.maintenance_authority.committee,
            vec![ContractMaintenanceVerifyingKey::Schnorr(
                owner.verifying_key()
            )]
        );
        assert!(matches!(
            install_intent.actions.iter_deref().next(),
            Some(ContractAction::Maintain(_))
        ));
        let call_target = ContractOperationTarget {
            inner: target.inner.clone(),
            operation: names[0].clone(),
            manifest: String::new(),
            k: 1,
            proof_parameters_sha256: String::new(),
            ttl: 1,
        };
        let installed = install_binding
            .admit_committed_state(
                &install_binding.expected_state,
                &install_binding.expected_state,
                &"c".repeat(64),
                false,
            )
            .unwrap();
        assert!(
            !call_target.context_matches(&installed),
            "calls must stay blocked until the maintenance authority is locked"
        );

        assert!(
            target
                .prepare_authority_rotation(
                    &installed,
                    &foreign,
                    next_owner.verifying_key(),
                    2_000_000_000,
                    &mut OsRng,
                )
                .is_err()
        );
        let (rotation, binding) = target
            .prepare_authority_rotation(
                &installed,
                &owner,
                next_owner.verifying_key(),
                2_000_000_000,
                &mut OsRng,
            )
            .unwrap();
        let expected: ContractState<Db> = decode(&binding.expected_state).unwrap();
        assert_eq!(expected.operations, installed.state.operations);
        assert_eq!(expected.data, installed.state.data);
        assert_eq!(expected.balance, installed.state.balance);
        assert_eq!(expected.maintenance_authority.counter, 2);
        assert_eq!(
            expected.maintenance_authority.committee,
            vec![ContractMaintenanceVerifyingKey::Schnorr(
                next_owner.verifying_key()
            )]
        );
        let Some(ContractAction::Maintain(update)) = rotation.actions.iter_deref().next() else {
            panic!("expected signed authority rotation")
        };
        assert_eq!(update.counter, 1);
        assert_eq!(update.updates.len(), 1);
        let Some(ledger::structure::SingleUpdate::ReplaceAuthority(authority)) =
            update.updates.iter_deref().next()
        else {
            panic!("rotation must replace only the maintenance authority")
        };
        assert_eq!(authority, &expected.maintenance_authority);
        let signature = update.signatures.iter_deref().next().unwrap();
        let Signature::Schnorr(signature) = &signature.1 else {
            panic!("expected a Schnorr maintenance signature")
        };
        assert!(
            owner
                .verifying_key()
                .verify(&update.data_to_sign(), signature)
        );
        assert!(
            crate::native_client::prove_maintenance(
                &rotation,
                &ledger::structure::INITIAL_PARAMETERS
            )
            .is_ok()
        );

        let rotated = binding
            .admit_committed_state(
                &binding.expected_state,
                &binding.expected_state,
                &"d".repeat(64),
                false,
            )
            .unwrap();
        assert!(target.maintenance_context_matches(&rotated));
        assert!(!call_target.context_matches(&rotated));
        assert!(
            target
                .prepare_authority_rotation(
                    &rotated,
                    &owner,
                    foreign.verifying_key(),
                    2_000_000_000,
                    &mut OsRng,
                )
                .is_err()
        );

        let unbound = CurrentStateContext {
            chain_identity: None,
            contract_set_identity: "different contract set".into(),
            deployment_identity: rotated.deployment_identity.clone(),
            state_schema_sha256: rotated.state_schema_sha256.clone(),
            address: rotated.address.clone(),
            identity: rotated.identity.clone(),
            state_bytes: rotated.state_bytes.clone(),
            state: rotated.state.clone(),
        };
        assert!(
            target
                .prepare_authority_rotation(
                    &unbound,
                    &next_owner,
                    foreign.verifying_key(),
                    2_000_000_000,
                    &mut OsRng,
                )
                .is_err()
        );

        let (next_rotation, _) = target
            .prepare_authority_rotation(
                &rotated,
                &next_owner,
                foreign.verifying_key(),
                2_000_000_000,
                &mut OsRng,
            )
            .unwrap();
        let Some(ContractAction::Maintain(update)) = next_rotation.actions.iter_deref().next()
        else {
            panic!("new authority must be able to rotate the next key")
        };
        assert_eq!(update.counter, 2);

        let mut altered = expected;
        altered.maintenance_authority.counter += 1;
        let altered_bytes = encode(&altered).unwrap();
        assert!(
            binding
                .admit_committed_state(&altered_bytes, &altered_bytes, &"e".repeat(64), false)
                .is_err()
        );

        let (lock, lock_binding) = target
            .prepare_installation(&rotated, &[], &next_owner, true, 2_000_000_000, &mut OsRng)
            .unwrap();
        assert!(matches!(
            lock.actions.iter_deref().next(),
            Some(ContractAction::Maintain(_))
        ));
        let locked_state: ContractState<Db> = decode(&lock_binding.expected_state).unwrap();
        assert_eq!(locked_state.operations, target.inner.ready_state.operations);
        assert_eq!(locked_state.operations.size(), 16);
        assert_eq!(locked_state.maintenance_authority.counter, 3);
        assert!(locked_state.maintenance_authority.committee.is_empty());
        assert_eq!(locked_state.maintenance_authority.threshold, 1);
        let locked = lock_binding
            .admit_committed_state(
                &lock_binding.expected_state,
                &lock_binding.expected_state,
                &"f".repeat(64),
                false,
            )
            .unwrap();
        assert!(call_target.context_matches(&locked));
    }

    #[cfg(feature = "zkir-321")]
    fn issue67_supply_fixture(name: &str) -> String {
        std::env::var(format!("NOCTIUM_ISSUE67_SUPPLY_{name}"))
            .unwrap_or_else(|_| panic!("missing NOCTIUM_ISSUE67_SUPPLY_{name}"))
    }

    #[cfg(feature = "zkir-321")]
    fn issue67_supply_total(state_bytes: &[u8]) -> String {
        use onchain_runtime::state::StateValue;
        use transient_crypto::fab::AlignedValueExt;

        let state: ContractState<Db> = decode(state_bytes).unwrap();
        let StateValue::Array(array) = state.data.get_ref() else {
            panic!("expected contract state array")
        };
        let StateValue::Cell(value) = &*array.get(0).unwrap() else {
            panic!("expected totalSupply cell")
        };
        let mut fields = Vec::new();
        value.value_only_field_repr(&mut fields);
        assert_eq!(fields.len(), 1);
        crate::field_decimal(fields[0])
    }

    #[cfg(feature = "zkir-321")]
    fn issue67_supply_bundles() -> ContractBundleSet {
        let add = crate::artifacts::verify(
            std::path::Path::new(&issue67_supply_fixture("ADD_BUNDLE")),
            Some("96398175fb2a762a38b079e00a4cb405e2ce3b9517c64ad8546b25c1ed173903"),
        )
        .unwrap();
        let sub = crate::artifacts::verify(
            std::path::Path::new(&issue67_supply_fixture("SUB_BUNDLE")),
            Some("15b820d15e0ad5ad0f231c04fdabd11b9dbfe7b92a944324b10e791862c4c6a8"),
        )
        .unwrap();
        ContractBundleSet::new(vec![add, sub]).unwrap()
    }

    #[cfg(feature = "zkir-321")]
    fn issue67_supply_parameters(name: &str, k: u8, digest: &str) -> TrustedParameters {
        let bytes = std::fs::read(issue67_supply_fixture(name)).unwrap();
        TrustedParameters::from_bytes(&bytes, k, digest).unwrap()
    }

    #[cfg(feature = "zkir-321")]
    fn issue67_client_descriptor() -> Vec<u8> {
        serde_json::to_vec(&serde_json::json!({
            "abiVersion": 1,
            "policy": {
                "networkId": "noctium-test",
                "genesis": "8".repeat(64),
                "specVersion": 1,
                "transactionVersion": 4,
                "profile": crate::profile::NAME,
                "maxDust": "1"
            },
            "capabilities": {
                "chain": "chain",
                "funding": "wallet",
                "signing": "signer",
                "journal": "store"
            }
        }))
        .unwrap()
    }

    #[cfg(feature = "zkir-321")]
    fn issue67_client_setup() -> Vec<u8> {
        serde_json::to_vec(&serde_json::json!({
            "hostContext": {
                "protocolVersion": 1,
                "namespace": "noctium-test",
                "baseRevision": "r0",
                "attemptId": "c".repeat(64),
                "capabilities": [{
                    "id": "commit",
                    "namespace": "noctium-test",
                    "keyPrefix": "cache/",
                    "operations": [crate::host::CAS]
                }],
                "operations": [],
                "providers": [],
                "commitCapability": "commit"
            },
            "stages": []
        }))
        .unwrap()
    }

    #[cfg(feature = "zkir-321")]
    fn issue43_fixture(name: &str) -> String {
        std::env::var(format!("NOCTIUM_ISSUE43_{name}"))
            .unwrap_or_else(|_| panic!("missing NOCTIUM_ISSUE43_{name}"))
    }

    fn issue43_empty_activity_fixture(name: &str) -> String {
        std::env::var(format!("NOCTIUM_ISSUE43_EMPTY_{name}"))
            .unwrap_or_else(|_| panic!("missing NOCTIUM_ISSUE43_EMPTY_{name}"))
    }

    #[test]
    fn contract_state_binding_rejects_wrong_operation_and_successor() {
        let state = ContractState::<Db>::default();
        let expected = encode(&state).unwrap();
        let binding = ContractStateBinding {
            contract_set_identity: "11".repeat(32),
            deployment_identity: "22".repeat(32),
            state_schema_sha256: "33".repeat(32),
            address: "44".repeat(32),
            operation: "apply".into(),
            context_identity: "55".repeat(32),
            current_state_sha256: Some(hex::encode(Sha256::digest(&expected))),
            current_state: Some(expected.clone()),
            expected_state: expected.clone(),
            deployment: false,
        };
        assert!(binding.matches_target("44".repeat(32).as_str(), "apply"));
        assert!(!binding.matches_target("44".repeat(32).as_str(), "claim"));
        let token = binding
            .admit_committed_state(&expected, &expected, &"aa".repeat(32), false)
            .unwrap();
        assert_eq!(token.state_bytes, expected);
        let mut wrong_successor = expected.clone();
        wrong_successor.push(0);
        assert!(
            binding
                .admit_committed_state(&wrong_successor, &wrong_successor, &"aa".repeat(32), false,)
                .is_err()
        );
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires the pinned PublicSupply operation bundles and trusted k8/k9 SRS fixtures"]
    fn public_supply_scalar_handoff_binds_operation_and_current_state() {
        let bundles = issue67_supply_bundles();
        let state_config = br#"{"state":{"totalSupply":"0"}}"#;
        let ttl = 2_000_000_000;
        let contract =
            WitnessContractTarget::from_state_config(bundles, state_config, ttl, &mut OsRng)
                .unwrap();
        let params9 = issue67_supply_parameters(
            "PARAMETERS_K9",
            9,
            "b9009f1098bcefffec3c461ab3a5e3a17f7e5599f0f08c70fcdc55a89227bcbd",
        );
        let params8 = issue67_supply_parameters(
            "PARAMETERS_K8",
            8,
            "909b707551eaaea79828e883cde6fc46ab15986c3b1d791bed462c9e2805c933",
        );
        let add = contract.operation("addSupply", &params9, ttl).unwrap();
        let sub = contract.operation("subSupply", &params8, ttl).unwrap();
        assert_eq!(add.contract_address(), sub.contract_address());
        assert_eq!(add.k(), 9);
        assert_eq!(sub.k(), 8);

        // This test-only admission stands in for the later native client receipt/checkpoint
        // owner. It does not claim finalized-ledger evidence.
        let deployment_binding = contract.deployment_binding("addSupply").unwrap();
        let initial_bytes = deployment_binding.expected_state.clone();
        let mut current = Some(
            deployment_binding
                .admit_committed_state(&initial_bytes, &initial_bytes, &"a".repeat(64), true)
                .unwrap(),
        );
        assert_eq!(issue67_supply_total(&initial_bytes), "0");

        let amount5 = BTreeMap::from([("amount".to_owned(), serde_json::json!("5"))]);
        assert!(matches!(
            add.prepare_call(&mut current, &params8, amount5.clone(), &mut OsRng),
            Err(Error::InvalidParameters)
        ));
        assert!(current.is_some(), "bad SRS must preserve the state token");
        let prepared_add = add
            .prepare_call(&mut current, &params9, amount5, &mut OsRng)
            .unwrap();
        assert!(
            current.is_none(),
            "successful preparation consumes the token"
        );
        let add_binding = prepared_add.contract_binding.as_ref().unwrap();
        assert!(add_binding.matches_operation_target(&add));
        let state5_bytes = add_binding.expected_state.clone();
        assert_eq!(issue67_supply_total(&state5_bytes), "5");

        // One local proof exercises the public typed client handoff. A wrong selected operation
        // is rejected first and leaves the proved value available for the correct operation.
        let proved = block_on(prepared_add.prove(
            &LocalProver::new(OsRng),
            &params9,
            MAX_RESPONSE,
            pending(),
        ))
        .unwrap();
        let mut proved = Some(proved);
        let descriptor = issue67_client_descriptor();
        let setup = issue67_client_setup();
        assert!(matches!(
            contract.start_call_client(&sub, &mut proved, &descriptor, &setup),
            Err(crate::witness_execution::Error::Proof(
                Error::BindingMismatch
            ))
        ));
        assert!(
            proved.is_some(),
            "wrong operation must preserve the proved value"
        );
        let client = contract
            .start_call_client(&add, &mut proved, &descriptor, &setup)
            .unwrap();
        assert_eq!(client.status()["status"], "ready");
        assert!(
            proved.is_none(),
            "successful startup consumes the proved value"
        );

        let mut current5 = Some(
            add_binding
                .admit_committed_state(&state5_bytes, &state5_bytes, &"b".repeat(64), false)
                .unwrap(),
        );
        let amount2 = BTreeMap::from([("amount".to_owned(), serde_json::json!("2"))]);
        assert!(matches!(
            sub.prepare_call(&mut current5, &params9, amount2.clone(), &mut OsRng),
            Err(Error::InvalidParameters)
        ));
        assert!(
            current5.is_some(),
            "bad per-operation SRS must preserve state"
        );

        // A fresh deployment over the same immutable bundle set has a different retained
        // address/deployment identity, so its test token cannot satisfy this selected CALL.
        let other = WitnessContractTarget::from_state_config(
            issue67_supply_bundles(),
            state_config,
            ttl,
            &mut OsRng,
        )
        .unwrap();
        let other_binding = other.deployment_binding("subSupply").unwrap();
        let other_initial = other_binding.expected_state.clone();
        let mut wrong_state = Some(
            other_binding
                .admit_committed_state(&other_initial, &other_initial, &"d".repeat(64), true)
                .unwrap(),
        );
        assert!(matches!(
            sub.prepare_call(&mut wrong_state, &params8, amount2.clone(), &mut OsRng),
            Err(Error::BindingMismatch)
        ));
        assert!(
            wrong_state.is_some(),
            "foreign deployment token must remain owned"
        );

        let prepared_sub = sub
            .prepare_call(&mut current5, &params8, amount2, &mut OsRng)
            .unwrap();
        assert!(current5.is_none());
        let sub_binding = prepared_sub.contract_binding.as_ref().unwrap();
        assert!(sub_binding.matches_operation_target(&sub));
        assert_eq!(sub_binding.address, add_binding.address);
        assert_eq!(
            sub_binding.deployment_identity,
            add_binding.deployment_identity
        );
        assert_eq!(issue67_supply_total(&sub_binding.expected_state), "3");
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires authenticated conditional-write bundle, private config and trusted SRS"]
    fn inactive_guarded_write_matches_native_noop_preview_and_binds_skipped_fields() {
        let bundle_dir = issue43_fixture("BUNDLE");
        let manifest_digest = issue43_fixture("MANIFEST_SHA256");
        let bundle =
            crate::artifacts::verify(std::path::Path::new(&bundle_dir), Some(&manifest_digest))
                .unwrap();
        let config_bytes = std::fs::read(issue43_fixture("PRIVATE_CONFIG")).unwrap();
        let parameters_bytes = std::fs::read(issue43_fixture("PROOF_PARAMETERS")).unwrap();
        let parameters_digest = issue43_fixture("PROOF_PARAMETERS_SHA256");
        let ttl = 2_000_000_000;
        let mut prepared =
            PreparedProof::from_config(&bundle, &config_bytes, ttl, &mut OsRng).unwrap();
        let parameters =
            TrustedParameters::from_bytes(&parameters_bytes, prepared.k(), &parameters_digest)
                .unwrap();
        assert_eq!(
            prepared.activity,
            [
                None,
                None,
                Some(5),
                Some(5),
                Some(1),
                Some(4),
                Some(5),
                Some(5),
                Some(1),
            ]
        );
        let ContractAction::Call(source_call) =
            prepared.intent.actions.iter_deref().next().unwrap()
        else {
            unreachable!()
        };
        let preview = preview_call_activity(
            source_call,
            &prepared.activity,
            prepared.intent.binding_commitment.into(),
            &prepared.material.parameters.cost_model.runtime_cost_model,
        )
        .unwrap();
        assert_eq!(preview.statement, prepared.statement);

        let cost_model = &prepared.material.parameters.cost_model.runtime_cost_model;
        let noop_charge = |count: u32| {
            u128::from(cost_model.noop_constant.into_picoseconds())
                + u128::from(cost_model.noop_coeff_arg.into_picoseconds()) * u128::from(count)
        };
        for (source, previewed) in [
            (
                source_call.guaranteed_transcript.as_deref(),
                preview.call.guaranteed_transcript.as_deref(),
            ),
            (
                source_call.fallible_transcript.as_deref(),
                preview.call.fallible_transcript.as_deref(),
            ),
        ] {
            match (source, previewed) {
                (Some(source), Some(previewed)) => {
                    let added_noop_gas: u128 = previewed
                        .program
                        .iter_deref()
                        .filter_map(|op| match op {
                            onchain_runtime::ops::Op::Noop { n } => Some(noop_charge(*n)),
                            _ => None,
                        })
                        .sum();
                    assert_eq!(
                        u128::from(previewed.gas.compute_time.into_picoseconds()),
                        u128::from(source.gas.compute_time.into_picoseconds()) + added_noop_gas,
                        "each present partition charges its own inserted Noops"
                    );
                }
                (None, None) => {}
                _ => panic!("preview changed transcript partition presence"),
            }
        }

        let mut bad_active_count = prepared.activity.clone();
        bad_active_count.push(None);
        assert!(preview_call_activity(
            source_call,
            &bad_active_count,
            prepared.intent.binding_commitment.into(),
            cost_model,
        )
        .is_err());

        let proved = block_on(prepared.prove(
            &LocalProver::new(OsRng),
            &parameters,
            MAX_RESPONSE,
            pending(),
        ))
        .unwrap();
        let ContractAction::Call(actual) = proved.native().actions.iter_deref().next().unwrap()
        else {
            unreachable!()
        };
        assert_eq!(
            actual.guaranteed_transcript,
            preview.call.guaranteed_transcript
        );
        assert_eq!(actual.fallible_transcript, preview.call.fallible_transcript);
        assert_eq!(
            actual
                .public_inputs(proved.native().binding_commitment.into())
                .unwrap(),
            prepared.statement
        );
        let noop_fields = actual
            .guaranteed_transcript
            .iter()
            .chain(actual.fallible_transcript.iter())
            .flat_map(|transcript| transcript.program.iter_deref())
            .filter_map(|op| match op {
                onchain_runtime::ops::Op::Noop { n } => Some(*n),
                _ => None,
            })
            .try_fold(0u32, u32::checked_add)
            .unwrap();
        assert_eq!(noop_fields, 26);

        let ContractAction::Call(call) = proved.native().actions.iter_deref().next().unwrap()
        else {
            unreachable!()
        };
        let ProofVersioned::V3(proof) = &call.proof else {
            unreachable!()
        };
        let response = encode(&ProofVersioned::V2(proof.clone())).unwrap();
        assert_eq!(
            prepared.verify_response(&parameters, &response, MAX_RESPONSE),
            Ok(())
        );
        let skipped_field = prepared
            .statement
            .iter()
            .enumerate()
            .skip(2)
            .find_map(|(index, field)| (*field == Fr::from(0u64)).then_some(index))
            .expect("skipped Noop fields are public zero elements");
        prepared.statement[skipped_field] = Fr::from(1u64);
        assert_eq!(
            prepared.verify_response(&parameters, &response, MAX_RESPONSE),
            Err(Error::InvalidProof)
        );

        let bundle_dir = issue43_empty_activity_fixture("BUNDLE");
        let manifest_digest = issue43_empty_activity_fixture("MANIFEST_SHA256");
        let bundle =
            crate::artifacts::verify(std::path::Path::new(&bundle_dir), Some(&manifest_digest))
                .unwrap();
        let config_bytes = std::fs::read(issue43_empty_activity_fixture("PRIVATE_CONFIG")).unwrap();
        let parameters_bytes =
            std::fs::read(issue43_empty_activity_fixture("PROOF_PARAMETERS")).unwrap();
        let parameters_digest = issue43_empty_activity_fixture("PROOF_PARAMETERS_SHA256");
        let empty_prepared =
            PreparedProof::from_config(&bundle, &config_bytes, ttl, &mut OsRng).unwrap();
        assert!(empty_prepared.activity.iter().all(Option::is_some));
        assert_eq!(empty_prepared.activity.iter().flatten().sum::<usize>(), 26);
        let ContractAction::Call(empty_source_call) =
            empty_prepared.intent.actions.iter_deref().next().unwrap()
        else {
            unreachable!()
        };
        let empty_source_transcript = empty_source_call
            .guaranteed_transcript
            .as_ref()
            .expect("all-inactive source retains an empty transcript container");
        assert_eq!(empty_source_transcript.program.len(), 0);
        assert!(empty_source_call.fallible_transcript.is_none());
        let empty_cost = &empty_prepared.material.parameters.cost_model.runtime_cost_model;
        let empty_preview = preview_call_activity(
            empty_source_call,
            &empty_prepared.activity,
            empty_prepared.intent.binding_commitment.into(),
            empty_cost,
        )
        .unwrap();
        assert_eq!(empty_preview.statement, empty_prepared.statement);
        assert!(empty_preview.call.fallible_transcript.is_none());
        let empty_preview_transcript = empty_preview
            .call
            .guaranteed_transcript
            .as_ref()
            .expect("preview keeps the empty guaranteed partition");
        assert_eq!(
            empty_preview_transcript
                .program
                .iter_deref()
                .filter_map(|op| match op {
                    onchain_runtime::ops::Op::Noop { n } => Some(*n),
                    _ => None,
                })
                .collect::<Vec<_>>(),
            [26]
        );
        assert_eq!(
            u128::from(empty_preview_transcript.gas.compute_time.into_picoseconds()),
            u128::from(empty_source_transcript.gas.compute_time.into_picoseconds())
                + u128::from(empty_cost.noop_constant.into_picoseconds())
                + 26 * u128::from(empty_cost.noop_coeff_arg.into_picoseconds()),
            "the empty partition charges its trailing Noop"
        );
        let empty_parameters = TrustedParameters::from_bytes(
            &parameters_bytes,
            empty_prepared.k(),
            &parameters_digest,
        )
        .unwrap();
        let empty_proved = block_on(empty_prepared.prove(
            &LocalProver::new(OsRng),
            &empty_parameters,
            MAX_RESPONSE,
            pending(),
        ))
        .unwrap();
        let ContractAction::Call(empty_actual) =
            empty_proved.native().actions.iter_deref().next().unwrap()
        else {
            unreachable!()
        };
        assert_eq!(
            empty_actual.guaranteed_transcript,
            empty_preview.call.guaranteed_transcript
        );
        assert_eq!(
            empty_actual.fallible_transcript,
            empty_preview.call.fallible_transcript
        );
        assert_eq!(
            empty_actual
                .public_inputs(empty_proved.native().binding_commitment.into())
                .unwrap(),
            empty_prepared.statement
        );
        let empty_noop_fields = empty_actual
            .guaranteed_transcript
            .iter()
            .chain(empty_actual.fallible_transcript.iter())
            .flat_map(|transcript| transcript.program.iter_deref())
            .filter_map(|op| match op {
                onchain_runtime::ops::Op::Noop { n } => Some(*n),
                _ => None,
            })
            .try_fold(0u32, u32::checked_add)
            .unwrap();
        assert_eq!(empty_noop_fields, 26);
        assert_eq!(
            empty_actual
                .guaranteed_transcript
                .as_ref()
                .unwrap()
                .program
                .iter_deref()
                .filter(|op| !matches!(op, onchain_runtime::ops::Op::Noop { .. }))
                .count(),
            0
        );
    }

    #[test]
    #[ignore = "requires authenticated real source bundle, private inputs, SRS and another retained VK"]
    fn real_crypto_rejects_each_statement_field_and_wrong_key() {
        let root = std::env::var("NOCTIUM_TEST_BUNDLE").unwrap();
        let digest = std::env::var("NOCTIUM_TEST_MANIFEST_SHA256").unwrap();
        let config = std::fs::read(std::env::var("NOCTIUM_TEST_PRIVATE_CONFIG").unwrap()).unwrap();
        let parameters =
            std::fs::read(std::env::var("NOCTIUM_TEST_PROOF_PARAMETERS").unwrap()).unwrap();
        let parameter_digest = std::env::var("NOCTIUM_TEST_PROOF_PARAMETERS_SHA256").unwrap();
        let bundle = crate::artifacts::verify(root.as_ref(), Some(&digest)).unwrap();
        let mut prepared =
            PreparedProof::from_config(&bundle, &config, 2_000_000_000, &mut OsRng).unwrap();
        let params =
            TrustedParameters::from_bytes(&parameters, prepared.k(), &parameter_digest).unwrap();
        let proved =
            block_on(prepared.prove(&LocalProver::new(OsRng), &params, MAX_RESPONSE, pending()))
                .unwrap();
        let ContractAction::Call(call) = proved.native().actions.iter_deref().next().unwrap()
        else {
            unreachable!()
        };
        let ProofVersioned::V3(proof) = &call.proof else {
            unreachable!()
        };
        let response = encode(&ProofVersioned::V2(proof.clone())).unwrap();
        prepared
            .verify_response(&params, &response, MAX_RESPONSE)
            .unwrap();
        // Binding, communication commitment and every public statement field receive independent tests.
        for index in 0..prepared.statement.len() {
            let old = prepared.statement[index];
            prepared.statement[index] = old + Fr::from(1u64);
            assert_eq!(
                prepared.verify_response(&params, &response, MAX_RESPONSE),
                Err(Error::InvalidProof),
                "statement index {index}"
            );
            prepared.statement[index] = old;
        }
        let other = std::fs::read(std::env::var("NOCTIUM_TEST_OTHER_VERIFIER").unwrap()).unwrap();
        let other: VerifierKey = decode(&other).unwrap();
        other.init().unwrap();
        prepared.material.verifier = other;
        assert_eq!(
            prepared.verify_response(&params, &response, MAX_RESPONSE),
            Err(Error::InvalidProof)
        );
    }
}
