//! Owned Rust API for executing source witnesses and preparing their native client call.
//!
//! A `WitnessExecution` owns one authenticated source invocation and its frozen deployment
//! target. `prepare_proof` keeps that invocation available until every proof-side check passes,
//! then moves its private Runtime into `WitnessProof`. The Runtime never leaves an opaque
//! proof/client owner as a detached value.

use crate::{
    artifacts::{Role, VerifiedBundle},
    client,
    control::{self, TypedResponse},
    funding::{SealedTransaction, UnsealedTransaction},
    host,
    native_client::{self, Command, Contract, Descriptor, Driver, ServiceReply},
    proof::{
        self, ContractOperationTarget, CurrentStateContext, PreparedProof, ProofService,
        ProvedIntent, ProvedNativeIntent, TrustedParameters, WitnessContractTarget,
    },
};
use futures::Future;
use rand::{CryptoRng, Rng};
use serde_json::Value as Json;
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    ops::Deref,
    sync::atomic::{AtomicU64, Ordering},
};
use zeroize::Zeroizing;

static NEXT_RUST_TARGET_CONTEXT: AtomicU64 = AtomicU64::new(1);

fn next_context_id() -> Result<u64> {
    NEXT_RUST_TARGET_CONTEXT
        .try_update(Ordering::Relaxed, Ordering::Relaxed, |value| {
            value.checked_add(1).filter(|next| *next != 0)
        })
        .map_err(|_| Error::ResourceLimit)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    State,
    ResourceLimit,
    InvalidArtifacts,
    InvalidSource,
    InvalidClientDescriptor,
    Proof(proof::Error),
    Client(client::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::State => f.write_str("noctium_witness_execution_state"),
            Self::ResourceLimit => f.write_str("noctium_witness_execution_limit"),
            Self::InvalidArtifacts => f.write_str("noctium_witness_execution_artifacts"),
            Self::InvalidSource => f.write_str("noctium_witness_execution_source"),
            Self::InvalidClientDescriptor => {
                f.write_str("noctium_witness_execution_client_descriptor")
            }
            Self::Proof(error) => error.fmt(f),
            Self::Client(error) => error.fmt(f),
        }
    }
}
impl std::error::Error for Error {}
pub type Result<T> = std::result::Result<T, Error>;

/// Exact public witness control expected by a generated Rust entrypoint module.
pub struct GeneratedBinding {
    control: &'static [u8],
}

impl GeneratedBinding {
    pub const fn new(control: &'static [u8]) -> Self {
        Self { control }
    }

    pub fn check_bundle(&self, bundle: &VerifiedBundle) -> Result<()> {
        if bundle.authenticated_manifest_sha256().is_none()
            || bundle.file(Role::WitnessControl).ok() != Some(self.control)
        {
            return Err(Error::InvalidArtifacts);
        }
        // The bundle verifier already checked the binding embedded in this exact control file.
        Ok(())
    }

    pub fn check_operation(&self, target: &ContractOperationTarget) -> Result<()> {
        self.check_bundle(target.bundle().map_err(Error::Proof)?)
    }

    /// Build a correlated reply for a declared provider. The session still validates the reply.
    pub fn reply(
        request: &Json,
        attempt_id: &str,
        provider: (&str, &str, &str, &str),
        value: Json,
    ) -> Result<TypedResponse> {
        let (name, operation, capability, schema) = provider;
        let response = TypedResponse {
            protocol_version: 2,
            request_id: request["requestId"].as_str().unwrap_or_default().into(),
            attempt_id: attempt_id.into(),
            outcome: "value".into(),
            operation: operation.into(),
            capability: capability.into(),
            schema: schema.into(),
            value: Some(value),
            error: None,
        };
        if request["name"] != name
            || request["operation"] != operation
            || request["capability"] != capability
            || request["schema"] != schema
            || response.request_id.is_empty()
        {
            return Err(Error::InvalidSource);
        }
        Ok(response)
    }
}

/// JSON returned by source execution. Treat the contents as private, even when the status is
/// public, because completion includes the source result.
pub struct PrivateJson {
    value: Json,
    _reservations: Vec<control::AggregateReservation>,
}
impl PrivateJson {
    fn from_accounted(value: control::AccountedJson) -> Self {
        let (value, reservations) = value.into_parts();
        Self {
            value,
            _reservations: reservations,
        }
    }
    pub fn as_json(&self) -> &Json {
        &self.value
    }
}
impl Deref for PrivateJson {
    type Target = Json;
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}
impl Drop for PrivateJson {
    fn drop(&mut self) {
        control::wipe_json(&mut self.value);
    }
}

struct SecretInputs(BTreeMap<String, Json>);
impl Drop for SecretInputs {
    fn drop(&mut self) {
        for value in self.0.values_mut() {
            control::wipe_json(value);
        }
    }
}

// The native cursor owns the only ledger execution prefix. Source callbacks never supply state reads.
struct LedgerPreparation {
    cursor: crate::PreparationCursor,
    supplied: BTreeSet<String>,
    operation_end: usize,
}
impl LedgerPreparation {
    fn new(cursor: crate::PreparationCursor, inputs: &BTreeMap<String, Json>) -> Self {
        Self {
            cursor,
            supplied: inputs.keys().cloned().collect(),
            operation_end: 0,
        }
    }
    fn resume(&mut self, session: &mut control::Session) -> anyhow::Result<()> {
        let call = session
            .pending_ledger_call()?
            .ok_or_else(|| anyhow::anyhow!("missing internal ledger callback"))?;
        let mut inputs = session.partial_native_inputs()?;
        let mut additions = SecretInputs(std::mem::take(&mut inputs.values));
        additions.0.retain(|name, _| !self.supplied.contains(name));
        if !additions.0.is_empty() {
            self.cursor.supply_inputs(&additions.0)?;
        }
        self.supplied.extend(additions.0.keys().cloned());
        anyhow::ensure!(
            call.operation_end > self.operation_end,
            "ledger callback operation order mismatch"
        );
        let mut observed = None;
        while self.operation_end < call.operation_end {
            match self.cursor.step()? {
                crate::PreparationStep::Operation { index, read } => {
                    anyhow::ensure!(
                        index == self.operation_end,
                        "native preparation operation order mismatch"
                    );
                    self.operation_end = index + 1;
                    if self.operation_end == call.operation_end {
                        observed = read;
                    }
                }
                crate::PreparationStep::PendingInputs(_) => {
                    anyhow::bail!("ledger callback depends on an unavailable witness")
                }
                crate::PreparationStep::Complete => {
                    anyhow::bail!("ledger callback exceeds native preparation")
                }
            }
        }
        let value = match &call.read {
            Some(name) => {
                let read =
                    observed.ok_or_else(|| anyhow::anyhow!("ledger callback read is absent"))?;
                anyhow::ensure!(
                    read.active && read.name == *name,
                    "ledger callback read mismatch"
                );
                read.values
                    .get(name)
                    .ok_or_else(|| anyhow::anyhow!("ledger callback value is absent"))?
                    .public_json()
            }
            None => serde_json::json!({"kind":"unit"}),
        };
        session.resume_ledger(value)?;
        Ok(())
    }
}

/// A running host-neutral source witness invocation bound to one authenticated bundle target.
pub struct WitnessExecution {
    target: Option<proof::WitnessTarget>,
    contract_target: Option<ContractOperationTarget>,
    current_state: Option<CurrentStateContext>,
    session: Option<control::Session>,
    ledger: Option<LedgerPreparation>,
    context_id: u64,
    ttl: u64,
    proof_parameters_sha256: String,
    contract_address: String,
    entrypoint: String,
}

impl WitnessExecution {
    /// Authenticate the typed source artifacts, freeze the deployment address, and begin source
    /// execution. `source_inputs` contains the original public and private Lean arguments.
    pub fn begin(
        bundle: &VerifiedBundle,
        state_config: &[u8],
        source_inputs: BTreeMap<String, Json>,
        host_context: host::Context,
        parameters: &TrustedParameters,
        ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        let mut source_inputs = SecretInputs(source_inputs);
        let target =
            proof::WitnessTarget::from_state_config(bundle, state_config, parameters, ttl, rng)
                .map_err(Error::Proof)?;
        Self::from_target(
            bundle,
            target,
            std::mem::take(&mut source_inputs.0),
            host_context,
            parameters,
            ttl,
        )
    }

    /// Begin source execution with a target prepared earlier from the same authenticated bundle.
    /// This lets hosts choose the private-state namespace from the frozen contract address.
    pub fn from_target(
        bundle: &VerifiedBundle,
        target: proof::WitnessTarget,
        source_inputs: BTreeMap<String, Json>,
        host_context: host::Context,
        parameters: &TrustedParameters,
        ttl: u64,
    ) -> Result<Self> {
        let mut source_inputs = SecretInputs(source_inputs);
        let manifest = bundle.authenticated_manifest_sha256().unwrap_or_default();
        if !target.context_matches(manifest, crate::profile::NAME, ttl)
            || target.proof_parameters_sha256() != parameters.sha256()
        {
            return Err(Error::Proof(proof::Error::BindingMismatch));
        }
        let context_id = next_context_id()?;
        let authenticated = target
            .authenticated_control_target(context_id, bundle)
            .map_err(Error::Proof)?;
        let plan_bytes = bundle
            .file(Role::WitnessControl)
            .map_err(|_| Error::InvalidArtifacts)?;
        let mut session = control::Session::from_authenticated_native_target(
            plan_bytes,
            std::mem::take(&mut source_inputs.0),
            host_context,
            authenticated,
        )
        .map_err(|_| Error::InvalidSource)?;
        let ledger = if session.has_ledger_calls() {
            let inputs = session
                .partial_native_inputs()
                .map_err(|_| Error::InvalidSource)?;
            let cursor = target
                .preparation_cursor(bundle, &inputs.values)
                .map_err(Error::Proof)?;
            Some(LedgerPreparation::new(cursor, &inputs.values))
        } else {
            None
        };
        Ok(Self {
            contract_address: target.contract_address().to_owned(),
            entrypoint: target.entrypoint().to_owned(),
            target: Some(target),
            contract_target: None,
            current_state: None,
            session: Some(session),
            ledger,
            context_id,
            ttl,
            proof_parameters_sha256: parameters.sha256().to_owned(),
        })
    }

    /// Begin a complete-contract operation after the native client admits its exact current
    /// state. The caller retains the token if any public or source-construction check fails.
    /// Public target, SRS, operation, address, and state checks run before callbacks.
    pub fn begin_contract_operation(
        target: &ContractOperationTarget,
        current_state: &mut Option<CurrentStateContext>,
        source_inputs: BTreeMap<String, Json>,
        host_context: host::Context,
        parameters: &TrustedParameters,
    ) -> Result<Self> {
        let mut source_inputs = SecretInputs(source_inputs);
        let current_state_ref = current_state.as_ref().ok_or(Error::State)?;
        if parameters.sha256() != target.parameters_sha256()
            || parameters.k() != target.k()
            || !target.context_matches(current_state_ref)
        {
            return Err(Error::Proof(proof::Error::BindingMismatch));
        }
        let context_id = next_context_id()?;
        let authenticated = target
            .authenticated_control_target(context_id)
            .map_err(Error::Proof)?;
        let bundle = target.bundle().map_err(Error::Proof)?;
        let plan_bytes = bundle
            .file(Role::WitnessControl)
            .map_err(|_| Error::InvalidArtifacts)?;
        let mut session = control::Session::from_authenticated_native_target(
            plan_bytes,
            std::mem::take(&mut source_inputs.0),
            host_context,
            authenticated,
        )
        .map_err(|_| Error::InvalidSource)?;
        let ledger = if session.has_ledger_calls() {
            let inputs = session
                .partial_native_inputs()
                .map_err(|_| Error::InvalidSource)?;
            let cursor = target
                .preparation_cursor(current_state_ref, &inputs.values)
                .map_err(Error::Proof)?;
            Some(LedgerPreparation::new(cursor, &inputs.values))
        } else {
            None
        };
        let current_state = current_state.take().ok_or(Error::State)?;
        let ttl = target.ttl();
        let contract_address = target.contract_address().to_owned();
        let entrypoint = target.operation().to_owned();
        Ok(Self {
            target: None,
            contract_target: Some(target.clone()),
            current_state: Some(current_state),
            session: Some(session),
            ledger,
            context_id,
            ttl,
            proof_parameters_sha256: parameters.sha256().to_owned(),
            contract_address,
            entrypoint,
        })
    }

    pub fn contract_address(&self) -> &str {
        &self.contract_address
    }

    pub fn entrypoint(&self) -> &str {
        &self.entrypoint
    }

    pub fn advance(&mut self) -> Result<PrivateJson> {
        let session = self.session.as_mut().ok_or(Error::State)?;
        loop {
            let result = session
                .advance_accounted()
                .map(PrivateJson::from_accounted)
                .map_err(|_| Error::InvalidSource)?;
            if session
                .pending_ledger_call()
                .map_err(|_| Error::InvalidSource)?
                .is_none()
            {
                return Ok(result);
            }
            let resumed = self
                .ledger
                .as_mut()
                .ok_or(Error::InvalidSource)?
                .resume(session);
            if resumed.is_err() {
                let _ = session.cancel();
                self.ledger = None;
                return Err(Error::InvalidSource);
            }
        }
    }

    pub fn private_request(&mut self) -> Result<PrivateJson> {
        self.session
            .as_mut()
            .ok_or(Error::State)?
            .private_request_accounted()
            .map(PrivateJson::from_accounted)
            .map_err(|_| Error::InvalidSource)
    }

    pub fn resume_typed(&mut self, response: TypedResponse) -> Result<Json> {
        self.session
            .as_mut()
            .ok_or(Error::State)?
            .resume_typed(response)
            .map_err(|_| Error::InvalidSource)
    }

    pub fn cancel(&mut self) -> Result<Json> {
        if self.contract_target.is_some() {
            return Err(Error::State);
        }
        self.cancel_session()
    }

    /// Cancel an unprepared complete-contract invocation and return its exact validated state
    /// token for a corrected retry. The source Session clears staged writes before the token
    /// leaves this owner. Once preparation consumes the token, this method returns State.
    pub fn cancel_contract_operation(&mut self) -> Result<(Json, CurrentStateContext)> {
        if self.contract_target.is_none() || self.current_state.is_none() {
            return Err(Error::State);
        }
        let result = self.cancel_session()?;
        self.contract_target = None;
        let current_state = self.current_state.take().ok_or(Error::State)?;
        Ok((result, current_state))
    }

    fn cancel_session(&mut self) -> Result<Json> {
        let result = self
            .session
            .as_mut()
            .ok_or(Error::State)?
            .cancel()
            .map_err(|_| Error::InvalidSource)?;
        self.session = None;
        self.ledger = None;
        self.target = None;
        Ok(result)
    }

    /// Prepare from the completed invocation, then consume its Runtime only after all exact
    /// bundle, relation, target and input-map checks pass. A failed preparation leaves this
    /// completed invocation available for a corrected retry without provider re-execution.
    pub fn prepare_proof(
        &mut self,
        bundle: &VerifiedBundle,
        ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<WitnessProof> {
        let target = self.target.as_ref().ok_or(Error::State)?;
        let session = self.session.as_mut().ok_or(Error::State)?;
        if ttl != self.ttl {
            return Err(Error::Proof(proof::Error::BindingMismatch));
        }
        if target.proof_parameters_sha256() != self.proof_parameters_sha256 {
            return Err(Error::Proof(proof::Error::BindingMismatch));
        }
        let authenticated = target
            .authenticated_control_target(self.context_id, bundle)
            .map_err(Error::Proof)?;
        let mut inputs = session
            .peek_completed_invocation(
                self.context_id,
                &authenticated.contract_address,
                &authenticated.entrypoint,
                &authenticated.control_plan,
                &authenticated.binding_bytes,
                &authenticated.relation,
            )
            .map_err(|_| Error::InvalidSource)?;
        let expected_inputs = inputs
            .try_clone_accounted()
            .map_err(|_| Error::ResourceLimit)?;
        let prepared = PreparedProof::from_witness_inputs(
            bundle,
            target,
            std::mem::take(&mut inputs.values),
            ttl,
            rng,
        )
        .map_err(Error::Proof)?;
        let ledger_parameters: ledger::structure::LedgerParameters = serialize::tagged_deserialize(
            bundle
                .file(Role::LedgerParameters)
                .map_err(|_| Error::InvalidArtifacts)?,
        )
        .map_err(|_| Error::InvalidArtifacts)?;
        let deployment = prepared
            .deployment_intent()
            .map(|intent| native_client::prove_deployment(intent, &ledger_parameters))
            .transpose()
            .map_err(|_| Error::InvalidArtifacts)?;
        let completed = session
            .take_completed_invocation(
                self.context_id,
                &authenticated.control_plan,
                &authenticated.binding_bytes,
                &authenticated.relation,
                &expected_inputs,
                &authenticated.contract_address,
                &authenticated.entrypoint,
            )
            .map_err(|_| Error::InvalidSource)?;
        let runtime = completed.runtime;
        self.session = None;
        self.ledger = None;
        self.target = None;
        Ok(WitnessProof {
            prepared: Some(prepared),
            deployment,
            runtime: Some(runtime),
            proof_parameters_sha256: self.proof_parameters_sha256.clone(),
            contract_address: self.contract_address.clone(),
            entrypoint: self.entrypoint.clone(),
        })
    }

    /// Freeze an authenticated contract-set CALL from this exact completed source invocation.
    pub fn prepare_contract_proof(
        &mut self,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<WitnessProof> {
        self.prepare_contract_proof_with_block(None, rng)
    }

    pub(crate) fn prepare_contract_proof_with_snapshot(
        &mut self,
        snapshot: &client::Snapshot,
        policy: &client::NetworkPolicy,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<WitnessProof> {
        snapshot
            .validate(policy)
            .map_err(|_| Error::Proof(proof::Error::BindingMismatch))?;
        let target = self.contract_target.as_ref().ok_or(Error::State)?;
        let current_state = self.current_state.as_ref().ok_or(Error::State)?;
        proof::ensure_current_state_matches_verified_snapshot(target, current_state, snapshot)
            .map_err(Error::Proof)?;
        self.prepare_contract_proof_with_block(Some(&snapshot.block), rng)
    }

    fn prepare_contract_proof_with_block(
        &mut self,
        block: Option<&onchain_runtime::context::BlockContext>,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<WitnessProof> {
        let target = self.contract_target.as_ref().ok_or(Error::State)?;
        let current_state = self.current_state.as_ref().ok_or(Error::State)?;
        let session = self.session.as_mut().ok_or(Error::State)?;
        if target.ttl() != self.ttl
            || target.parameters_sha256() != self.proof_parameters_sha256
            || !target.context_matches(current_state)
        {
            return Err(Error::Proof(proof::Error::BindingMismatch));
        }
        let authenticated = target
            .authenticated_control_target(self.context_id)
            .map_err(Error::Proof)?;
        let mut inputs = session
            .peek_completed_invocation(
                self.context_id,
                &authenticated.contract_address,
                &authenticated.entrypoint,
                &authenticated.control_plan,
                &authenticated.binding_bytes,
                &authenticated.relation,
            )
            .map_err(|_| Error::InvalidSource)?;
        let expected_inputs = inputs
            .try_clone_accounted()
            .map_err(|_| Error::ResourceLimit)?;
        let prepared = PreparedProof::from_contract_witness_inputs_with_block(
            target,
            current_state,
            std::mem::take(&mut inputs.values),
            block,
            rng,
        )
        .map_err(Error::Proof)?;
        let completed = session
            .take_completed_invocation(
                self.context_id,
                &authenticated.control_plan,
                &authenticated.binding_bytes,
                &authenticated.relation,
                &expected_inputs,
                &authenticated.contract_address,
                &authenticated.entrypoint,
            )
            .map_err(|_| Error::InvalidSource)?;
        let runtime = completed.runtime;
        self.session = None;
        self.contract_target = None;
        self.current_state = None;
        self.ledger = None;
        Ok(WitnessProof {
            prepared: Some(prepared),
            deployment: None,
            runtime: Some(runtime),
            proof_parameters_sha256: self.proof_parameters_sha256.clone(),
            contract_address: self.contract_address.clone(),
            entrypoint: self.entrypoint.clone(),
        })
    }
}

impl WitnessContractTarget {
    /// Restore the retained deployment identity from its SDK60 journal after a host restart.
    pub async fn restore_deployment_from_journal(
        self,
        store: &impl client::JournalStore,
        deployment_attempt_id: &str,
        ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        let attempt = client::SubmissionAttempt::recover(store, deployment_attempt_id)
            .await
            .map_err(Error::Client)?;
        self.restore_deployment(&attempt, ttl, rng)
            .map_err(Error::Proof)
    }

    /// Rebind a trusted durable attempt to authenticated artifacts, then reobserve finality and CAS.
    pub async fn recover_client(
        &self,
        store: &impl client::JournalStore,
        attempt_id: &str,
        descriptor_json: &[u8],
        context_json: &[u8],
    ) -> Result<WitnessClient> {
        let recovery_context =
            native_client::recovery_host_context(context_json).map_err(Error::Client)?;
        if recovery_context.attempt_id != attempt_id {
            return Err(Error::Client(client::Error::Identity));
        }
        let attempt = client::SubmissionAttempt::recover(store, attempt_id)
            .await
            .map_err(Error::Client)?;
        let binding = self.recovery_binding(&attempt).map_err(Error::Proof)?;
        let descriptor: Descriptor =
            serde_json::from_slice(descriptor_json).map_err(|_| Error::InvalidClientDescriptor)?;
        let driver = Driver::recover_with_state_binding(descriptor, context_json, binding)
            .map_err(Error::Client)?;
        Ok(WitnessClient { driver })
    }

    /// Prove and start the one retained operation-map deployment. The setup Runtime belongs to
    /// this deployment client, while each later source CALL gets its own Runtime and journal.
    pub fn start_deployment_client(
        &self,
        operation: &str,
        descriptor_json: &[u8],
        setup_json: &[u8],
    ) -> Result<WitnessClient> {
        let binding = self.deployment_binding(operation).map_err(Error::Proof)?;
        let bundle = self.deployment_bundle().map_err(Error::Proof)?;
        let parameter_bytes = bundle
            .file(Role::LedgerParameters)
            .map_err(|_| Error::InvalidArtifacts)?;
        let mut reader = parameter_bytes;
        let parameters: ledger::structure::LedgerParameters =
            serialize::tagged_deserialize(&mut reader).map_err(|_| Error::InvalidArtifacts)?;
        if !reader.is_empty() {
            return Err(Error::InvalidArtifacts);
        }
        let intent = native_client::prove_deployment(self.deployment_intent(), &parameters)
            .map_err(Error::Client)?;
        let descriptor: Descriptor =
            serde_json::from_slice(descriptor_json).map_err(|_| Error::InvalidClientDescriptor)?;
        let driver = Driver::start_with_state_binding(
            descriptor,
            setup_json,
            Contract::Deployment {
                intent,
                entrypoint: operation.to_owned(),
            },
            binding,
        )
        .map_err(Error::Client)?;
        Ok(WitnessClient { driver })
    }

    /// Append authenticated verifiers during bootstrap and optionally lock the authority.
    /// The caller retains the current token if construction or client startup fails.
    pub fn start_installation_client(
        &self,
        current_state: &mut Option<CurrentStateContext>,
        operations: &[String],
        signer: &base_crypto::schnorr::SigningKey,
        lock: bool,
        ttl: u64,
        descriptor_json: &[u8],
        setup_json: &[u8],
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<WitnessClient> {
        let current = current_state.as_ref().ok_or(Error::State)?;
        let (intent, binding) = self
            .prepare_installation(current, operations, signer, lock, ttl, rng)
            .map_err(Error::Proof)?;
        self.start_maintenance_client(current_state, intent, binding, descriptor_json, setup_json)
    }

    /// Replace the active single-key maintenance authority after all authenticated verifiers
    /// have been installed. The current token stays with the caller on any startup failure.
    pub fn start_authority_rotation_client(
        &self,
        current_state: &mut Option<CurrentStateContext>,
        current_signer: &base_crypto::schnorr::SigningKey,
        next_key: base_crypto::schnorr::VerifyingKey,
        ttl: u64,
        descriptor_json: &[u8],
        setup_json: &[u8],
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<WitnessClient> {
        let current = current_state.as_ref().ok_or(Error::State)?;
        let (intent, binding) = self
            .prepare_authority_rotation(current, current_signer, next_key, ttl, rng)
            .map_err(Error::Proof)?;
        self.start_maintenance_client(current_state, intent, binding, descriptor_json, setup_json)
    }

    fn start_maintenance_client(
        &self,
        current_state: &mut Option<CurrentStateContext>,
        intent: crate::assembly::NativeIntent,
        binding: proof::ContractStateBinding,
        descriptor_json: &[u8],
        setup_json: &[u8],
    ) -> Result<WitnessClient> {
        let bundle = self.deployment_bundle().map_err(Error::Proof)?;
        let bytes = bundle
            .file(Role::LedgerParameters)
            .map_err(|_| Error::InvalidArtifacts)?;
        let mut reader = bytes;
        let parameters: ledger::structure::LedgerParameters =
            serialize::tagged_deserialize(&mut reader).map_err(|_| Error::InvalidArtifacts)?;
        if !reader.is_empty() {
            return Err(Error::InvalidArtifacts);
        }
        let intent =
            native_client::prove_maintenance(&intent, &parameters).map_err(Error::Client)?;
        let descriptor: Descriptor =
            serde_json::from_slice(descriptor_json).map_err(|_| Error::InvalidClientDescriptor)?;
        let driver = Driver::start_with_state_binding(
            descriptor,
            setup_json,
            Contract::Maintenance {
                intent,
                entrypoint: "__noctium_maintenance".into(),
            },
            binding,
        )
        .map_err(Error::Client)?;
        current_state.take().ok_or(Error::State)?;
        Ok(WitnessClient { driver })
    }

    /// Start a CALL client without a witness-control sidecar from a bound proof and explicit host setup.
    /// This handoff accepts no witness Runtime or synthetic control plan. It checks the retained
    /// contract deployment, selected operation, and exact prepared-state binding before the host
    /// setup Runtime is created. The proved value moves only after client startup succeeds.
    pub fn start_call_client(
        &self,
        operation: &ContractOperationTarget,
        proved: &mut Option<ProvedIntent>,
        descriptor_json: &[u8],
        setup_json: &[u8],
    ) -> Result<WitnessClient> {
        if !operation.belongs_to(self) {
            return Err(Error::Proof(proof::Error::BindingMismatch));
        }
        let proved_ref = proved.as_ref().ok_or(Error::State)?;
        let binding = proved_ref
            .contract_binding()
            .filter(|binding| binding.matches_operation_target(operation))
            .cloned()
            .ok_or(Error::Proof(proof::Error::BindingMismatch))?;
        let descriptor: Descriptor =
            serde_json::from_slice(descriptor_json).map_err(|_| Error::InvalidClientDescriptor)?;
        let driver = Driver::start_with_state_binding(
            descriptor,
            setup_json,
            Contract::Proved(proved_ref.native().clone()),
            binding,
        )
        .map_err(Error::Client)?;
        proved.take();
        Ok(WitnessClient { driver })
    }
}

/// A prepared native proof that still owns the exact source Runtime and target.
pub struct WitnessProof {
    prepared: Option<PreparedProof>,
    deployment: Option<ProvedNativeIntent>,
    runtime: Option<host::Runtime>,
    proof_parameters_sha256: String,
    contract_address: String,
    entrypoint: String,
}

impl WitnessProof {
    /// Prove against the frozen source call. Provider or verification errors retain the proof
    /// and Runtime inside this value, so the caller can retry the proof service safely. An
    /// explicit Abort or dropping a polled proof future discards the source Runtime and makes
    /// this value terminal. Dropping a future before its first poll leaves this value untouched.
    pub async fn prove<S: ProofService>(
        &mut self,
        service: &S,
        parameters: &TrustedParameters,
        max_response_bytes: usize,
        stop: impl Future<Output = proof::Abort>,
    ) -> Result<WitnessProvedCall> {
        if self.prepared.is_none() || self.runtime.is_none() {
            return Err(Error::State);
        }
        if parameters.sha256() != self.proof_parameters_sha256 {
            return Err(Error::Proof(proof::Error::InvalidParameters));
        }
        let mut attempt = ProofAttempt {
            owner: self,
            completed: false,
        };
        let result = {
            let prepared = attempt.owner.prepared.as_ref().ok_or(Error::State)?;
            prepared
                .prove(service, parameters, max_response_bytes, stop)
                .await
        };
        match result {
            Ok(proved) => {
                attempt.completed = true;
                attempt.owner.prepared = None;
                Ok(WitnessProvedCall {
                    proved,
                    deployment: attempt.owner.deployment.take(),
                    runtime: attempt.owner.runtime.take(),
                    contract_address: attempt.owner.contract_address.clone(),
                    entrypoint: attempt.owner.entrypoint.clone(),
                    deployment_client_started: false,
                })
            }
            Err(error @ (proof::Error::Cancelled | proof::Error::Deadline)) => {
                attempt.owner.discard();
                attempt.completed = true;
                Err(Error::Proof(error))
            }
            Err(error) => {
                attempt.completed = true;
                Err(Error::Proof(error))
            }
        }
    }

    fn discard(&mut self) {
        self.prepared = None;
        self.deployment = None;
        self.runtime = None;
    }
}

struct ProofAttempt<'a> {
    owner: &'a mut WitnessProof,
    completed: bool,
}
impl Drop for ProofAttempt<'_> {
    fn drop(&mut self) {
        if !self.completed {
            self.owner.discard();
        }
    }
}

/// A proved CALL that keeps the source Runtime private until the native call client consumes it.
pub struct WitnessProvedCall {
    proved: ProvedIntent,
    deployment: Option<ProvedNativeIntent>,
    runtime: Option<host::Runtime>,
    contract_address: String,
    entrypoint: String,
    deployment_client_started: bool,
}

impl WitnessProvedCall {
    /// Public proof projection. The unsealed binding randomness and source Runtime stay here.
    pub fn public_serialized(&self) -> Result<Vec<u8>> {
        self.proved.public_serialized().map_err(Error::Proof)
    }

    pub fn contract_address(&self) -> &str {
        &self.contract_address
    }

    pub fn entrypoint(&self) -> &str {
        &self.entrypoint
    }

    /// Start the separate deployment client. Its Setup context does not consume the source
    /// Runtime, which remains attached to this proved CALL for later execution.
    pub fn start_deployment_client(
        &mut self,
        descriptor_json: &[u8],
        setup_json: &[u8],
    ) -> Result<WitnessClient> {
        if self.deployment_client_started {
            return Err(Error::State);
        }
        let descriptor: Descriptor =
            serde_json::from_slice(descriptor_json).map_err(|_| Error::InvalidClientDescriptor)?;
        let intent = self.deployment.as_ref().ok_or(Error::State)?.clone();
        let driver = Driver::start(
            descriptor,
            setup_json,
            Contract::Deployment {
                intent,
                entrypoint: self.entrypoint.clone(),
            },
        )
        .map_err(Error::Client)?;
        self.deployment_client_started = true;
        Ok(WitnessClient { driver })
    }

    /// Transfer the source Runtime into the client for the proved CALL. Descriptor and target
    /// checks happen before Runtime consumption. A rejected start leaves this object retryable.
    pub fn start_call_client(&mut self, descriptor_json: &[u8]) -> Result<WitnessClient> {
        let descriptor: Descriptor =
            serde_json::from_slice(descriptor_json).map_err(|_| Error::InvalidClientDescriptor)?;
        let contract = Contract::Proved(self.proved.native().clone());
        let driver = if let Some(binding) = self.proved.contract_binding().cloned() {
            Driver::start_with_runtime_and_binding(descriptor, &mut self.runtime, contract, binding)
        } else {
            Driver::start_with_runtime(descriptor, &mut self.runtime, contract)
        }
        .map_err(Error::Client)?;
        self.runtime = None;
        Ok(WitnessClient { driver })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WitnessClientCommand {
    Prepare,
    Submit,
    Observe,
    Commit,
    Cancel,
    Deadline,
    Reload,
}

/// A host reply for an existing native client request.
pub enum WitnessClientReply {
    Snapshot(client::Snapshot),
    Funded(UnsealedTransaction),
    Signed(SealedTransaction),
    Submitted(client::Submission),
    Observed(client::Observation),
    Loaded(client::StoredRecord),
    Persisted(client::StoreAcknowledgement),
    Cas(client::CasReceipt),
    Failure,
}

/// One pending native host request. Private payload bytes zeroize on drop.
pub struct WitnessClientRequest {
    pub id: u64,
    pub metadata: Json,
    private_payload: Option<Zeroizing<Vec<u8>>>,
    transaction: Option<client::BoundTransaction>,
}
impl WitnessClientRequest {
    pub fn private_payload(&self) -> Option<&[u8]> {
        self.private_payload.as_deref().map(Vec::as_slice)
    }

    /// Exact immutable transaction binding for submit and observe adapters.
    pub fn transaction(&self) -> Option<&client::BoundTransaction> {
        self.transaction.as_ref()
    }
}

/// Thin Rust facade over the existing native client driver. It adds no transaction state machine.
pub struct WitnessClient {
    driver: Driver,
}
impl WitnessClient {
    pub(crate) fn into_driver(self) -> Driver {
        self.driver
    }

    /// Restore a client from the exact private context in its trusted journal domain.
    pub fn recover(descriptor_json: &[u8], context: &[u8]) -> Result<Self> {
        let descriptor: Descriptor =
            serde_json::from_slice(descriptor_json).map_err(|_| Error::InvalidClientDescriptor)?;
        let driver = Driver::recover(descriptor, context).map_err(Error::Client)?;
        Ok(Self { driver })
    }

    pub fn recovery_context(&self) -> Result<&[u8]> {
        self.driver.recovery_context().ok_or(Error::State)
    }

    /// Return request metadata without materializing its private arguments.
    pub fn request_metadata(&self) -> Result<Option<Json>> {
        let Some(request) = self.driver.request() else {
            return Ok(None);
        };
        let mut metadata = request.metadata();
        if let native_client::RequestData::Persist {
            record,
            expected_revision,
        } = &request.data
        {
            metadata["expectedRevision"] =
                serde_json::json!(expected_revision.map(|revision| revision.to_string()));
            metadata["immutableDigest"] =
                Json::String(record.immutable_digest().map_err(Error::Client)?);
        }
        Ok(Some(metadata))
    }

    pub fn status(&self) -> Json {
        self.driver.status()
    }

    pub fn request(&self) -> Result<Option<WitnessClientRequest>> {
        let Some(request) = self.driver.request() else {
            return Ok(None);
        };
        let metadata = request.metadata();
        let private_payload = if metadata["hasPrivateArguments"] == true {
            Some(request.private_bytes().map_err(Error::Client)?)
        } else {
            None
        };
        let transaction = match &request.data {
            native_client::RequestData::Submit(transaction)
            | native_client::RequestData::Observe(transaction) => Some(transaction.clone()),
            _ => None,
        };
        Ok(Some(WitnessClientRequest {
            id: request.id,
            metadata,
            private_payload,
            transaction,
        }))
    }

    pub fn command(&mut self, command: WitnessClientCommand) -> Result<Json> {
        let command = match command {
            WitnessClientCommand::Prepare => Command::Prepare,
            WitnessClientCommand::Submit => Command::Submit,
            WitnessClientCommand::Observe => Command::Observe,
            WitnessClientCommand::Commit => Command::Commit,
            WitnessClientCommand::Cancel => Command::Cancel,
            WitnessClientCommand::Deadline => Command::Deadline,
            WitnessClientCommand::Reload => Command::Reload,
        };
        self.driver.command(command).map_err(Error::Client)?;
        self.driver.poll().map_err(Error::Client)?;
        Ok(self.driver.status())
    }

    pub fn poll(&mut self) -> Result<Json> {
        self.driver.poll().map_err(Error::Client)?;
        Ok(self.driver.status())
    }

    pub fn complete(&mut self, id: u64, reply: WitnessClientReply) -> Result<Json> {
        let reply = match reply {
            WitnessClientReply::Snapshot(value) => ServiceReply::Snapshot(value),
            WitnessClientReply::Funded(value) => ServiceReply::Funded(value),
            WitnessClientReply::Signed(value) => ServiceReply::Signed(value),
            WitnessClientReply::Submitted(value) => ServiceReply::Submitted(value),
            WitnessClientReply::Observed(value) => ServiceReply::Observed(value),
            WitnessClientReply::Loaded(value) => ServiceReply::Loaded(value),
            WitnessClientReply::Persisted(value) => ServiceReply::Persisted(value),
            WitnessClientReply::Cas(value) => ServiceReply::Cas(value),
            WitnessClientReply::Failure => ServiceReply::Failure,
        };
        self.driver.complete(id, reply).map_err(Error::Client)?;
        self.driver.poll().map_err(Error::Client)?;
        Ok(self.driver.status())
    }

    pub fn detachable(&self) -> bool {
        self.driver.detachable()
    }

    /// Return the retained signed transaction for a native host transport.
    pub fn transaction(&self) -> Result<Vec<u8>> {
        self.driver.transaction().map_err(Error::Client)
    }

    /// Return the exact contract state from the verified finalized receipt.
    pub fn receipt_state(&self) -> Result<Vec<u8>> {
        self.driver.receipt_state().map_err(Error::Client)
    }

    /// Return the next opaque state token after this client verifies finality and commits its
    /// private journal. Recovery-loaded clients lack this in-memory contract binding.
    pub fn current_state_context(&mut self) -> Result<CurrentStateContext> {
        self.driver.current_state_context().map_err(Error::Client)
    }
}

#[cfg(all(test, feature = "zkir-321"))]
mod tests {
    use super::*;
    use crate::{
        artifacts::{self, ContractBundleSet},
        control::TypedResponse,
        host::{Capability, Context, Limits, Operation, Provider},
    };
    use rand::rngs::OsRng;
    use serde_json::json;
    use std::collections::{BTreeMap, BTreeSet};

    const TTL: u64 = 2_000_000_000;

    fn fixture_env(name: &str) -> String {
        std::env::var(format!("NOCTIUM_WITNESS_PUBLIC_{name}"))
            .unwrap_or_else(|_| panic!("missing NOCTIUM_WITNESS_PUBLIC_{name}"))
    }

    fn block_time_fixture_env(name: &str) -> String {
        std::env::var(format!("NOCTIUM_BLOCK_TIME_WITNESS_{name}"))
            .unwrap_or_else(|_| panic!("missing NOCTIUM_BLOCK_TIME_WITNESS_{name}"))
    }

    fn test_context(plan: &Json, attempt_id: &str) -> host::Context {
        let mut operations = BTreeMap::<String, Operation>::new();
        let mut providers = Vec::new();
        let mut capability_map = BTreeMap::<String, (String, BTreeSet<String>)>::new();
        for signature in plan["witnesses"].as_array().unwrap() {
            let name = signature["name"].as_str().unwrap().to_owned();
            let operation = signature["operation"].as_str().unwrap().to_owned();
            let capability = signature["capability"].as_str().unwrap().to_owned();
            let private_key = signature["privateKey"].as_str().map(str::to_owned);
            let parameters = signature["parameters"].as_array().unwrap();
            let mut argument_schema = parameters
                .iter()
                .map(|parameter| {
                    (
                        parameter["name"].as_str().unwrap().to_owned(),
                        parameter["type"].as_str().unwrap().to_owned(),
                    )
                })
                .collect::<BTreeMap<_, _>>();
            if operation == host::READ {
                argument_schema.insert("key".into(), "Key".into());
            }
            operations.insert(
                operation.clone(),
                Operation {
                    operation: operation.clone(),
                    argument_schema,
                    result_schema: signature["resultType"].as_str().unwrap().to_owned(),
                },
            );
            let prefix = private_key
                .as_deref()
                .map(|key| {
                    key.rsplit_once('/')
                        .map(|(root, _)| format!("{root}/"))
                        .unwrap_or_else(|| key.to_owned())
                })
                .unwrap_or_else(|| "lookup/".into());
            let entry = capability_map
                .entry(capability.clone())
                .or_insert_with(|| (prefix.clone(), BTreeSet::new()));
            assert_eq!(entry.0, prefix);
            entry.1.insert(operation.clone());
            if private_key.is_some() {
                entry.1.insert(host::STAGE.into());
            }
            providers.push(Provider {
                input: name,
                operation,
                capability,
                arguments: private_key
                    .map(|key| BTreeMap::from([("key".into(), json!(key))]))
                    .unwrap_or_default(),
            });
        }
        let private = capability_map
            .entry("private".into())
            .or_insert_with(|| ("cache/".into(), BTreeSet::new()));
        private.1.insert(host::STAGE.into());
        let mut capabilities = capability_map
            .into_iter()
            .map(|(id, (key_prefix, operations))| Capability {
                id,
                namespace: "noctium".into(),
                key_prefix,
                operations: operations.into_iter().collect(),
            })
            .collect::<Vec<_>>();
        capabilities.push(Capability {
            id: "commit".into(),
            namespace: "noctium".into(),
            key_prefix: "cache/".into(),
            operations: vec![host::CAS.into()],
        });
        Context {
            protocol_version: 1,
            namespace: "noctium".into(),
            base_revision: "preview-r0".into(),
            attempt_id: attempt_id.into(),
            capabilities,
            operations: operations.into_values().collect(),
            providers,
            commit_capability: "commit".into(),
            limits: Limits::default(),
        }
    }

    fn source_inputs(expected: &str) -> BTreeMap<String, Json> {
        BTreeMap::from([
            ("expected".into(), json!(expected)),
            ("seed".into(), json!("7")),
        ])
    }

    fn complete_source(execution: &mut WitnessExecution, attempt_id: &str) -> bool {
        for _ in 0..64 {
            let status = execution.advance().unwrap();
            match status["status"].as_str().unwrap() {
                "completed" => return true,
                "failed" => return false,
                "need_host" => {
                    let request = &status["request"];
                    let value = match request["name"].as_str().unwrap() {
                        "cache" => json!("1"),
                        "lookup" => json!("14"),
                        other => panic!("unexpected provider {other}"),
                    };
                    let response: TypedResponse = serde_json::from_value(json!({
                        "protocolVersion": 2,
                        "requestId": request["requestId"],
                        "attemptId": attempt_id,
                        "outcome": "value",
                        "operation": request["operation"],
                        "capability": request["capability"],
                        "schema": request["schema"],
                        "value": value,
                    }))
                    .unwrap();
                    execution.resume_typed(response).unwrap();
                }
                other => panic!("unexpected source status {other}"),
            }
        }
        panic!("source witness exceeded the request bound")
    }

    fn deployment_state_context(
        target: &WitnessContractTarget,
        operation: &str,
        chain: Option<&client::ChainIdentity>,
    ) -> CurrentStateContext {
        use ledger::structure::ContractAction;

        let binding = target.deployment_binding(operation).unwrap();
        let ContractAction::Deploy(deployment) = target
            .deployment_intent()
            .actions
            .iter_deref()
            .next()
            .unwrap()
        else {
            unreachable!()
        };
        let mut state_bytes = Vec::new();
        serialize::tagged_serialize(&deployment.initial_state, &mut state_bytes).unwrap();
        let checkpoint = "f".repeat(64);
        match chain {
            Some(chain) => binding.admit_committed_state_on_chain(
                &state_bytes,
                &state_bytes,
                &checkpoint,
                true,
                chain,
            ),
            None => binding.admit_committed_state(&state_bytes, &state_bytes, &checkpoint, true),
        }
        .unwrap()
    }

    fn deployment_snapshot(
        target: &WitnessContractTarget,
        policy: &client::NetworkPolicy,
    ) -> client::Snapshot {
        use coin_structure::contract::ContractAddress;
        use ledger::structure::{ContractAction, LedgerState};
        use onchain_runtime::context::BlockContext;

        let ContractAction::Deploy(deployment) = target
            .deployment_intent()
            .actions
            .iter_deref()
            .next()
            .unwrap()
        else {
            unreachable!()
        };
        let address = ContractAddress(base_crypto::hash::HashOutput(
            hex::decode(target.contract_address())
                .unwrap()
                .try_into()
                .unwrap(),
        ));
        let mut state = LedgerState::<crate::Db>::new(policy.network_id.clone());
        state.contract = state
            .contract
            .insert(address, deployment.initial_state.clone());
        client::Snapshot {
            chain: client::ChainIdentity {
                network_id: policy.network_id.clone(),
                genesis: policy.genesis.clone(),
                spec_version: policy.spec_version,
                transaction_version: policy.transaction_version,
                profile: policy.profile.clone(),
            },
            finalized_hash: "f".repeat(64),
            height: 1,
            state,
            block: BlockContext::default(),
        }
    }

    #[test]
    #[ignore = "requires the retained BlockTime bundle and pinned public K7 parameters"]
    fn block_time_missing_snapshot_and_wrong_chain_keep_completed_source() {
        let bundle = artifacts::verify(
            std::path::Path::new(&block_time_fixture_env("BUNDLE")),
            Some(&block_time_fixture_env("MANIFEST_SHA256")),
        )
        .unwrap();
        let parameters_bytes = std::fs::read(block_time_fixture_env("PARAMETERS")).unwrap();
        let parameters_digest = block_time_fixture_env("PARAMETERS_SHA256");
        let parameters =
            TrustedParameters::from_bytes(&parameters_bytes, 7, &parameters_digest).unwrap();
        let control_plan: Json =
            serde_json::from_slice(bundle.file(Role::WitnessControl).unwrap()).unwrap();
        let entrypoint = serde_json::from_slice::<Json>(bundle.file(Role::Plan).unwrap()).unwrap()
            ["entrypoint"]
            .as_str()
            .unwrap()
            .to_owned();
        let bundles = ContractBundleSet::new(vec![bundle]).unwrap();
        let contract = WitnessContractTarget::from_state_config(
            bundles,
            br#"{"state":{"total":"0"}}"#,
            TTL,
            &mut OsRng,
        )
        .unwrap();
        let operation = contract.operation(&entrypoint, &parameters, TTL).unwrap();
        let policy = client::NetworkPolicy {
            network_id: "noctium-test".into(),
            genesis: "a".repeat(64),
            spec_version: 2001100,
            transaction_version: 4,
            profile: crate::profile::NAME.into(),
            max_dust: 10u128.pow(22),
        };
        let snapshot = deployment_snapshot(&contract, &policy);
        let mut checkpoint = Some(deployment_state_context(
            &contract,
            &entrypoint,
            Some(&snapshot.chain),
        ));
        let attempt = "d".repeat(64);
        let mut execution = WitnessExecution::begin_contract_operation(
            &operation,
            &mut checkpoint,
            BTreeMap::from([
                ("expected".into(), json!("14")),
                ("seed".into(), json!("7")),
                ("cutoff".into(), json!("2000000000")),
                ("enabled".into(), json!(true)),
            ]),
            test_context(&control_plan, &attempt),
            &parameters,
        )
        .unwrap();
        assert!(complete_source(&mut execution, &attempt));

        assert!(matches!(
            execution.prepare_contract_proof(&mut OsRng),
            Err(Error::Proof(proof::Error::InvalidPrivateInput))
        ));
        assert!(execution.session.is_some());
        assert!(execution.current_state.is_some());

        let mut wrong_policy = policy.clone();
        wrong_policy.genesis = "b".repeat(64);
        assert!(matches!(
            execution.prepare_contract_proof_with_snapshot(&snapshot, &wrong_policy, &mut OsRng),
            Err(Error::Proof(proof::Error::BindingMismatch))
        ));
        assert!(execution.session.is_some());
        assert!(execution.current_state.is_some());

        let mut other_chain_policy = policy.clone();
        other_chain_policy.genesis = "b".repeat(64);
        let other_chain_snapshot = deployment_snapshot(&contract, &other_chain_policy);
        other_chain_snapshot.validate(&other_chain_policy).unwrap();
        assert!(matches!(
            execution.prepare_contract_proof_with_snapshot(
                &other_chain_snapshot,
                &other_chain_policy,
                &mut OsRng
            ),
            Err(Error::Proof(proof::Error::BindingMismatch))
        ));
        assert!(execution.session.is_some());
        assert!(execution.current_state.is_some());

        let mut wrong_state = client::Snapshot {
            chain: snapshot.chain.clone(),
            finalized_hash: snapshot.finalized_hash.clone(),
            height: snapshot.height,
            state: snapshot.state.clone(),
            block: snapshot.block.clone(),
        };
        let address = coin_structure::contract::ContractAddress(base_crypto::hash::HashOutput(
            hex::decode(operation.contract_address())
                .unwrap()
                .try_into()
                .unwrap(),
        ));
        wrong_state.state.contract = wrong_state
            .state
            .contract
            .insert(address, Default::default());
        assert!(matches!(
            execution.prepare_contract_proof_with_snapshot(&wrong_state, &policy, &mut OsRng),
            Err(Error::Proof(proof::Error::BindingMismatch))
        ));
        assert!(execution.session.is_some());
        assert!(execution.current_state.is_some());

        let proof = execution
            .prepare_contract_proof_with_snapshot(&snapshot, &policy, &mut OsRng)
            .unwrap();
        assert!(execution.session.is_none());
        assert!(execution.current_state.is_none());
        drop(proof);
    }

    #[test]
    #[ignore = "requires authenticated witness bundle and pinned public SRS fixtures"]
    fn cancelled_contract_source_returns_checkpoint_for_corrected_retry() {
        let bundle = artifacts::verify(
            std::path::Path::new(&fixture_env("BUNDLE")),
            Some(&fixture_env("MANIFEST_SHA256")),
        )
        .unwrap();
        let parameters_bytes = std::fs::read(fixture_env("PARAMETERS")).unwrap();
        let parameters_digest = fixture_env("PARAMETERS_SHA256");
        let parameters =
            TrustedParameters::from_bytes(&parameters_bytes, 7, &parameters_digest).unwrap();
        let control_plan: Json =
            serde_json::from_slice(bundle.file(Role::WitnessControl).unwrap()).unwrap();
        let entrypoint = serde_json::from_slice::<Json>(bundle.file(Role::Plan).unwrap()).unwrap()
            ["entrypoint"]
            .as_str()
            .unwrap()
            .to_owned();
        let bundles = ContractBundleSet::new(vec![bundle]).unwrap();
        let contract = WitnessContractTarget::from_state_config(
            bundles,
            br#"{"state":{"total":"0"}}"#,
            TTL,
            &mut OsRng,
        )
        .unwrap();
        let operation = contract.operation(&entrypoint, &parameters, TTL).unwrap();
        let checkpoint = deployment_state_context(&contract, &entrypoint, None);

        let mut available = Some(checkpoint);
        let mut rejected_inputs = source_inputs("15");
        rejected_inputs.insert("unexpected".into(), Json::Null);
        assert!(matches!(
            WitnessExecution::begin_contract_operation(
                &operation,
                &mut available,
                rejected_inputs,
                test_context(&control_plan, &"a".repeat(64)),
                &parameters,
            ),
            Err(Error::InvalidSource)
        ));
        assert!(available.is_some(), "constructor rejection keeps the token");

        let failed_attempt = "b".repeat(64);
        let mut failed = WitnessExecution::begin_contract_operation(
            &operation,
            &mut available,
            source_inputs("15"),
            test_context(&control_plan, &failed_attempt),
            &parameters,
        )
        .unwrap();
        assert!(
            available.is_none(),
            "successful construction consumes the token"
        );
        assert!(!complete_source(&mut failed, &failed_attempt));
        let (cancelled, checkpoint) = failed.cancel_contract_operation().unwrap();
        assert_eq!(cancelled["status"], "cancelled");
        assert!(
            failed.session.is_none(),
            "cancellation drops the source Runtime"
        );
        assert!(failed.current_state.is_none());
        assert!(matches!(failed.advance(), Err(Error::State)));

        let retry_attempt = "c".repeat(64);
        let mut retry_state = Some(checkpoint);
        let mut retry = WitnessExecution::begin_contract_operation(
            &operation,
            &mut retry_state,
            source_inputs("14"),
            test_context(&control_plan, &retry_attempt),
            &parameters,
        )
        .unwrap();
        assert!(retry_state.is_none());
        assert!(complete_source(&mut retry, &retry_attempt));
        let proof = retry.prepare_contract_proof(&mut OsRng).unwrap();
        assert!(retry.current_state.is_none());
        assert!(matches!(
            retry.cancel_contract_operation(),
            Err(Error::State)
        ));
        drop(proof);
    }
}

#[cfg(all(test, feature = "zkir-321"))]
mod ledger_tests;

#[cfg(all(test, feature = "zkir-321"))]
mod typed_ledger_tests;

#[cfg(all(test, feature = "zkir-321"))]
mod range_ledger_tests;

#[cfg(all(test, feature = "zkir-321"))]
mod iteration_ledger_tests;

#[cfg(all(test, feature = "zkir-321"))]
mod wallet_key_tests;
