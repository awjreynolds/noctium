//! Native assembly of private, unbalanced deploy/call intents. No proving or network.
use crate::artifacts::{Role, VerifiedBundle};
#[cfg(test)]
use crate::create_state;
use crate::zkir::IrSource;
use crate::{
    Config, Db, Execution, LEDGER_REVISION, Plan, ZKIR_REVISION, field_value,
    prepare_with_context_and_block_time,
};
use anyhow::{Context, Result, anyhow, ensure};
use base_crypto::time::Timestamp;
use coin_structure::coin::{Commitment, PublicAddress};
use ledger::{
    construct::{ContractCallPrototype, PreTranscript, partition_transcripts},
    structure::{
        ContractAction, ContractCall, ContractDeploy, Intent, LedgerParameters,
        ProofPreimageMarker, ProofPreimageVersioned, Signature, StandardTransaction,
    },
};
use onchain_runtime::{
    context::{BlockContext, QueryContext},
    result_mode::ResultModeVerify,
    state::{ContractMaintenanceAuthority, ContractOperation, ContractState, EntryPointBuf},
    transcript::Transcript,
};
use rand::{CryptoRng, Rng, rngs::OsRng};
use serde_json::{Value as Json, json};
use serialize::{Deserializable, Serializable, Tagged, tagged_deserialize, tagged_serialize};
use sha2::{Digest, Sha256};
use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
    fs,
    io::Write,
    ops::Deref,
    path::{Path, PathBuf},
};
use storage::storage::Map;
use transient_crypto::{
    commitment::PedersenRandomness,
    curve::Fr,
    proofs::{KeyLocation, ProofPreimage, ProverKey, VerifierKey, Zkir},
};

pub type NativeIntent = Intent<Signature, ProofPreimageMarker, PedersenRandomness, Db>;
pub(crate) type BookedComIndices = Map<Commitment, u64, Db>;

/// One prepared source call and the initial ledger context used to replay it.
pub struct CheckedNativeCall<'a> {
    pub execution: &'a Execution,
    pub circuit: &'a IrSource,
    pub initial_context: QueryContext<Db>,
    pub entry_point: EntryPointBuf,
    pub communication_commitment_rand: Fr,
}

/// Public program, context and commitments for one independently prepared call.
#[derive(Clone)]
pub struct CompositionOffer {
    pub(crate) pre_transcript: PreTranscript<Db>,
    pub(crate) entry_point: EntryPointBuf,
    pub(crate) activity: Vec<Option<usize>>,
}

impl CompositionOffer {
    pub fn commitment(&self) -> Fr {
        self.pre_transcript.comm_comm.expect("checked public offer")
    }
}

impl CheckedNativeCall<'_> {
    /// Project only fields that the ledger will use to partition and replay this call.
    pub fn composition_offer(&self, parameters: &LedgerParameters) -> Result<CompositionOffer> {
        let context = &self.initial_context;
        let execution = self.execution;
        ensure!(
            context.effects == Default::default(),
            "native intent requires a fresh effects context for each call"
        );
        ensure!(
            self.communication_commitment_rand != Fr::from(0u64),
            "native call commitment randomness must be nonzero"
        );
        let name = std::str::from_utf8(&self.entry_point)?;
        ensure!(
            execution.preimage.key_location.0 == name,
            "native entrypoint differs from the checked relation"
        );
        let replay = context
            .query(
                &execution.program,
                None,
                &parameters.cost_model.runtime_cost_model,
            )
            .map_err(|_| anyhow!("native execution does not replay from the supplied context"))?;
        ensure!(
            replay.context.address == execution.after.address
                && replay.context.state == execution.after.state
                && replay.context.effects == execution.after.effects,
            "native execution differs from the supplied initial context"
        );
        crate::validate_call_input_header_json(
            &execution.call_input_header,
            &serde_json::to_value(self.circuit)?,
        )?;
        let commitment = onchain_runtime::communication_commitment(
            execution.call_input()?,
            execution.call_output()?,
            self.communication_commitment_rand,
        );
        let offer = CompositionOffer {
            pre_transcript: PreTranscript {
                context: context.clone(),
                program: execution.program.clone(),
                comm_comm: Some(commitment),
            },
            entry_point: self.entry_point.clone(),
            activity: execution.activity_schedule.clone(),
        };
        let active = self
            .composition_preimage(&offer)
            .check(self.circuit)
            .map_err(|_| anyhow!("native call preimage failed the official circuit checker"))?;
        ensure!(
            active == offer.activity
                && active.iter().filter(|skip| skip.is_none()).count() == execution.program.len(),
            "native call activity metadata differs from its checked relation"
        );
        Ok(offer)
    }

    pub(crate) fn composition_preimage(&self, offer: &CompositionOffer) -> ProofPreimage {
        let mut expected = self.execution.preimage.clone();
        expected.key_location = KeyLocation(Cow::Owned(format!(
            "{}:{}",
            hex::encode(self.initial_context.address.0.0),
            String::from_utf8_lossy(&self.entry_point),
        )));
        expected.communications_commitment =
            Some((offer.commitment(), self.communication_commitment_rand));
        expected
    }
}

pub(crate) fn partition_composition(
    offers: &[CompositionOffer],
    parameters: &LedgerParameters,
) -> Result<Vec<ContractCall<(), Db>>> {
    ensure!(!offers.is_empty(), "expected at least one native call");
    let mut commitments = BTreeMap::new();
    let pre_transcripts: Vec<_> = offers
        .iter()
        .map(|offer| offer.pre_transcript.clone())
        .collect();
    for (i, offer) in offers.iter().enumerate() {
        ensure!(
            commitments.insert(offer.commitment(), i).is_none(),
            "native intent requires unique communication commitments"
        );
    }
    let partitions = partition_transcripts(&pre_transcripts, parameters)
        .map_err(|_| anyhow!("official native call forest partition failed"))?;
    ensure!(
        partitions.len() == offers.len(),
        "invalid native partition count"
    );

    let mut claimed = BTreeMap::new();
    let mut actions = Vec::with_capacity(offers.len());
    for (i, (offer, (mut guaranteed, fallible))) in offers.iter().zip(partitions).enumerate() {
        let context = &offer.pre_transcript.context;
        if let Some(coin_structure::coin::PublicAddress::Contract(parent)) =
            context.call_context.caller
        {
            ensure!(
                claimed.get(&i) == Some(&parent),
                "supplied caller context does not match the contract call forest"
            );
        }
        if guaranteed.is_none() && fallible.is_none() {
            guaranteed = Some(empty_transcript(
                context,
                &parameters.cost_model.runtime_cost_model,
            )?);
        }
        for claim in guaranteed
            .iter()
            .chain(fallible.iter())
            .flat_map(|transcript| transcript.effects.claimed_contract_calls.iter())
        {
            let (_, address, entry_hash, commitment) = (*claim).deref().into_inner();
            let callee = commitments
                .get(&commitment)
                .copied()
                .filter(|&callee| {
                    callee > i
                        && offers[callee].pre_transcript.context.address == address
                        && offers[callee].entry_point.ep_hash() == entry_hash
                })
                .context("contract claim has no matching later call in this intent")?;
            ensure!(
                claimed.insert(callee, context.address).is_none(),
                "contract call has multiple claims"
            );
        }
        actions.push(ContractCall {
            address: context.address,
            entry_point: offer.entry_point.clone(),
            guaranteed_transcript: guaranteed.map(storage::arena::Sp::new),
            fallible_transcript: fallible.map(storage::arena::Sp::new),
            communication_commitment: offer.commitment(),
            proof: (),
        });
    }
    Ok(actions)
}

/// Build one private, unbalanced intent from prepared calls in ledger execution
/// order. The host supplies the call contexts. The ledger verifies their actual
/// state, operation keys and effects when the proved transaction is submitted.
pub fn assemble_checked_calls(
    calls: &[CheckedNativeCall<'_>],
    parameters: &LedgerParameters,
    ttl: u64,
    rng: &mut (impl Rng + CryptoRng),
) -> Result<NativeIntent> {
    ensure!(ttl > 0, "TTL must be explicit Unix seconds");
    let offers = calls
        .iter()
        .map(|call| call.composition_offer(parameters))
        .collect::<Result<Vec<_>>>()?;
    let public = partition_composition(&offers, parameters)?;
    let mut intent = NativeIntent::empty(rng, Timestamp::from_secs(ttl));
    for ((call, offer), action) in calls.iter().zip(&offers).zip(&public) {
        let expected = call.composition_preimage(offer);
        intent = intent.add_call::<ProofPreimage>(ContractCallPrototype {
            address: action.address,
            entry_point: action.entry_point.clone(),
            op: ContractOperation::new(None, None),
            guaranteed_public_transcript: action.guaranteed_transcript.as_deref().cloned(),
            fallible_public_transcript: action.fallible_transcript.as_deref().cloned(),
            private_transcript_outputs: expected
                .private_transcript
                .iter()
                .copied()
                .map(field_value)
                .collect(),
            input: call.execution.call_input()?,
            output: call.execution.call_output()?,
            communication_commitment_rand: call.communication_commitment_rand,
            key_location: expected.key_location.clone(),
        });
        let ContractAction::Call(native) = &*intent
            .actions
            .get(intent.actions.len() - 1)
            .context("ledger constructor omitted the checked call")?
        else {
            return Err(anyhow!("ledger constructor returned an unexpected action"));
        };
        let ProofPreimageVersioned::V2(preimage) = &native.proof else {
            return Err(anyhow!("unsupported preimage version"));
        };
        ensure!(
            native.address == action.address
                && native.entry_point == action.entry_point
                && native.communication_commitment == action.communication_commitment
                && **preimage == expected,
            "ledger constructor changed the checked call or its preimage"
        );
    }
    StandardTransaction::new(
        "",
        [(1, intent.clone())].into_iter().collect(),
        None,
        Default::default(),
    )
    .sequencing_check()
    .map_err(|_| anyhow!("official native call sequencing rejected"))?;
    Ok(intent)
}

fn empty_transcript(
    context: &QueryContext<Db>,
    cost: &onchain_runtime::cost_model::CostModel,
) -> Result<Transcript<Db>> {
    let query = context
        .query::<ResultModeVerify>(&[], None, cost)
        .map_err(|_| anyhow!("empty native transcript query rejected"))?;
    Ok(Transcript {
        gas: query.gas_cost,
        effects: query.context.effects,
        program: Vec::<onchain_runtime::ops::Op<ResultModeVerify, Db>>::new().into(),
        version: Some(storage::arena::Sp::new(Transcript::<Db>::VERSION)),
    })
}

/// Explicit input bytes. Keys must come from a trusted, pinned key-generation step.
/// The assembler checks native encodings and k, not cryptographic key/IR correspondence.
pub struct Inputs<'a> {
    pub plan: &'a [u8],
    pub circuit: &'a [u8],
    pub prover_key: &'a [u8],
    pub verifier_key: &'a [u8],
    pub ledger_parameters: &'a [u8],
    pub config: &'a [u8],
    pub ttl_unix: u64,
}
fn bytes<T: Serializable + Tagged>(value: &T) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    tagged_serialize(value, &mut bytes)?;
    Ok(bytes)
}
fn decode<T: Serializable + Deserializable + Tagged>(value: &[u8]) -> Result<T> {
    let mut reader = value;
    let decoded = tagged_deserialize(&mut reader)?;
    ensure!(reader.is_empty(), "trailing serialized bytes");
    Ok(decoded)
}
fn roundtrip<T: Serializable + Deserializable + Tagged>(value: &T) -> Result<(T, Vec<u8>)> {
    let encoded = bytes(value)?;
    let decoded = decode(&encoded)?;
    ensure!(
        bytes(&decoded)? == encoded,
        "native serialization roundtrip changed bytes"
    );
    Ok((decoded, encoded))
}
fn digest(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}
fn real_preimage(intent: &NativeIntent) -> Result<&ProofPreimage> {
    ensure!(
        intent.actions.len() == 1,
        "expected exactly one contract call"
    );
    let Some(ContractAction::Call(call)) = intent.actions.iter_deref().next() else {
        return Err(anyhow!("expected contract call"));
    };
    match &call.proof {
        ProofPreimageVersioned::V2(preimage) => Ok(preimage),
        _ => Err(anyhow!("unsupported preimage version")),
    }
}

fn nonzero_random(rng: &mut (impl Rng + CryptoRng)) -> Result<Fr> {
    // Bound both zero rejection and noncanonical field rejection from a broken host RNG.
    for _ in 0..128 {
        let mut bytes = zeroize::Zeroizing::new([0u8; 32]);
        rng.fill_bytes(&mut *bytes);
        if let Some(value) = Fr::from_le_bytes(&*bytes) {
            if value != Fr::from(0u64) {
                return Ok(value);
            }
        }
    }
    Err(anyhow!("host entropy rejected"))
}
struct Built {
    initial: ContractState<Db>,
    predicted: ContractState<Db>,
    execution: Execution,
    initial_context: QueryContext<Db>,
    entry_point: EntryPointBuf,
    communication_commitment_rand: Fr,
    deploy: NativeIntent,
    call: NativeIntent,
    address: String,
    operations: usize,
    guaranteed: usize,
    fallible: usize,
}

/// Checked execution data retained only while assembling a relay/destination pair.
pub(crate) struct CheckedCurrentStateCall {
    pub(crate) execution: Execution,
    pub(crate) initial_context: QueryContext<Db>,
    pub(crate) entry_point: EntryPointBuf,
    pub(crate) communication_commitment_rand: Fr,
    pub(crate) predicted: ContractState<Db>,
}

pub(crate) struct PreparedDeployment {
    pub(crate) intent: NativeIntent,
    pub(crate) address: String,
    pub(crate) entrypoint: String,
}

pub(crate) struct PreparedOperationMapDeployment {
    intent: NativeIntent,
    address: String,
    contract: String,
}
impl PreparedOperationMapDeployment {
    pub(crate) fn intent(&self) -> &NativeIntent {
        &self.intent
    }

    pub(crate) fn address(&self) -> &str {
        &self.address
    }

    pub(crate) fn ready_state(&self) -> Result<ContractState<Db>> {
        let Some(ContractAction::Deploy(deployment)) = self.intent.actions.iter_deref().next()
        else {
            return Err(anyhow!("native target deployment missing"));
        };
        Ok(deployment.initial_state.clone())
    }

    pub(crate) fn with_installation_subset(
        &self,
        installed: &BTreeSet<String>,
        authority: ContractMaintenanceAuthority,
        ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        ensure!(ttl > 0, "TTL must be explicit Unix seconds");
        ensure!(
            self.intent.actions.len() == 1,
            "native target deployment missing"
        );
        let Some(ContractAction::Deploy(deployment)) = self.intent.actions.iter_deref().next()
        else {
            return Err(anyhow!("native target deployment missing"));
        };
        ensure!(
            hex::encode(deployment.address().0.0) == self.address,
            "native target address mismatch"
        );

        let mut initial = deployment.initial_state.clone();
        let known: BTreeSet<String> = initial
            .operations
            .iter()
            .map(|pair| {
                let (name, _) = &*pair;
                String::from_utf8((**name).0.clone()).context("invalid operation name in target")
            })
            .collect::<Result<_>>()?;
        ensure!(
            !installed.is_empty(),
            "installation subset must be nonempty"
        );
        ensure!(
            installed.is_subset(&known),
            "installation subset contains an unknown operation"
        );
        ensure!(
            installed.len() < known.len(),
            "installation subset must be a strict subset"
        );

        for name in known.difference(installed) {
            initial.operations = initial
                .operations
                .remove(&EntryPointBuf(name.as_bytes().to_vec()));
        }
        initial.maintenance_authority = authority;

        let deployment = ContractDeploy::new(rng, initial);
        let address = hex::encode(deployment.address().0.0);
        let intent = NativeIntent::empty(rng, Timestamp::from_secs(ttl)).add_deploy(deployment);
        Ok(Self {
            intent,
            address,
            contract: self.contract.clone(),
        })
    }

    pub(crate) fn with_retained_deployment(
        &self,
        deployment: ContractDeploy<Db>,
        ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        ensure!(ttl > 0, "TTL must be explicit Unix seconds");
        ensure!(
            deployment.initial_state == self.ready_state()?,
            "retained deployment differs from authenticated initialization"
        );
        let address = hex::encode(deployment.address().0.0);
        let intent = NativeIntent::empty(rng, Timestamp::from_secs(ttl)).add_deploy(deployment);
        Ok(Self {
            intent,
            address,
            contract: self.contract.clone(),
        })
    }
}

fn valid_operation_name(name: &str) -> bool {
    !name.is_empty()
        && name.len() <= 128
        && name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
        && !name.as_bytes()[0].is_ascii_digit()
}

fn checked_operation_names(
    expected: &[String],
    operations: Vec<(String, ContractOperation)>,
) -> Result<BTreeMap<String, ContractOperation>> {
    ensure!(
        !expected.is_empty()
            && expected.len() <= crate::artifacts::MAX_ENTRIES
            && operations.len() <= crate::artifacts::MAX_ENTRIES,
        "invalid operation count"
    );
    let mut expected_names = BTreeSet::new();
    for name in expected {
        ensure!(valid_operation_name(name), "invalid entrypoint");
        ensure!(
            expected_names.insert(name.as_str()),
            "duplicate operation name"
        );
    }
    let mut operation_map = BTreeMap::new();
    for (name, operation) in operations {
        ensure!(valid_operation_name(&name), "invalid entrypoint");
        ensure!(
            operation_map.insert(name, operation).is_none(),
            "duplicate operation name"
        );
    }
    let actual_names: BTreeSet<_> = operation_map.keys().map(String::as_str).collect();
    ensure!(
        actual_names == expected_names,
        "operation map does not match the complete operation list"
    );
    Ok(operation_map)
}

/// Retain one deployment with all validated operation bindings for the source contract.
pub(crate) fn prepare_operation_map_deployment_target(
    plan: &Plan,
    contract: &str,
    state: &BTreeMap<String, Json>,
    expected_operations: &[String],
    operations: Vec<(String, ContractOperation)>,
    ttl: u64,
    rng: &mut (impl Rng + CryptoRng),
) -> Result<PreparedOperationMapDeployment> {
    ensure!(ttl > 0, "TTL must be explicit Unix seconds");
    ensure!(
        !contract.is_empty() && contract.len() <= 4096,
        "invalid contract name"
    );
    ensure!(valid_operation_name(&plan.entrypoint), "invalid entrypoint");
    let operations = checked_operation_names(expected_operations, operations)?;
    ensure!(
        operations.contains_key(&plan.entrypoint),
        "selected operation missing from contract"
    );

    let mut initial = ContractState::<Db>::default();
    initial.data = crate::constructor::deployment_state(plan, state)?;
    for (name, operation) in operations {
        initial.operations = initial
            .operations
            .insert(EntryPointBuf(name.into_bytes()), operation);
    }
    let deployment = ContractDeploy::new(rng, initial);
    let address = hex::encode(deployment.address().0.0);
    let intent = NativeIntent::empty(rng, Timestamp::from_secs(ttl)).add_deploy(deployment);
    Ok(PreparedOperationMapDeployment {
        intent,
        address,
        contract: contract.to_owned(),
    })
}

fn contract_initial_state(
    plan: &Plan,
    state: &BTreeMap<String, Json>,
    operation: &ContractOperation,
) -> Result<(ContractState<Db>, EntryPointBuf)> {
    ensure!(
        !plan.entrypoint.is_empty()
            && plan.entrypoint.len() <= 128
            && plan
                .entrypoint
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'_')
            && !plan.entrypoint.as_bytes()[0].is_ascii_digit(),
        "invalid entrypoint"
    );
    let entry = EntryPointBuf(plan.entrypoint.as_bytes().to_vec());
    let mut initial = ContractState::<Db>::default();
    initial.data = crate::constructor::deployment_state(plan, state)?;
    initial.operations = initial.operations.insert(entry.clone(), operation.clone());
    Ok((initial, entry))
}

pub(crate) fn prepare_deployment_target(
    plan: &Plan,
    state: &BTreeMap<String, Json>,
    verifier: VerifierKey,
    ttl: u64,
    rng: &mut (impl Rng + CryptoRng),
) -> Result<PreparedDeployment> {
    ensure!(ttl > 0, "TTL must be explicit Unix seconds");
    let operation = ContractOperation::new(Some(verifier), None);
    let (initial, _) = contract_initial_state(plan, state, &operation)?;
    let deployment = ContractDeploy::new(rng, initial);
    let address = hex::encode(deployment.address().0.0);
    let intent = NativeIntent::empty(rng, Timestamp::from_secs(ttl)).add_deploy(deployment);
    Ok(PreparedDeployment {
        intent,
        address,
        entrypoint: plan.entrypoint.clone(),
    })
}

fn build(
    plan: &Plan,
    config: &Config,
    parameters: &LedgerParameters,
    operation: ContractOperation,
    circuit: &IrSource,
    ttl: u64,
) -> Result<Built> {
    build_with_rng(
        plan, config, parameters, operation, circuit, ttl, None, &mut OsRng,
    )
}
fn build_with_rng(
    plan: &Plan,
    config: &Config,
    parameters: &LedgerParameters,
    operation: ContractOperation,
    circuit: &IrSource,
    ttl: u64,
    block: Option<&BlockContext>,
    mut rng: &mut (impl Rng + CryptoRng),
) -> Result<Built> {
    ensure!(ttl > 0, "TTL must be explicit Unix seconds");
    let (initial, entry) = contract_initial_state(plan, &config.state, &operation)?;
    let deployment = ContractDeploy::new(&mut rng, initial.clone());
    let com_indices = Map::new();
    build_for_deployment(
        plan,
        config,
        parameters,
        operation,
        circuit,
        ttl,
        initial,
        entry,
        deployment,
        None,
        block,
        &com_indices,
        None,
        None,
        &mut rng,
    )
}

fn build_for_deployment(
    plan: &Plan,
    config: &Config,
    parameters: &LedgerParameters,
    operation: ContractOperation,
    circuit: &IrSource,
    ttl: u64,
    initial: ContractState<Db>,
    entry: EntryPointBuf,
    deployment: ContractDeploy<Db>,
    retained_intent: Option<&NativeIntent>,
    block: Option<&BlockContext>,
    com_indices: &BookedComIndices,
    caller: Option<PublicAddress>,
    communication_commitment_rand: Option<Fr>,
    rng: &mut (impl Rng + CryptoRng),
) -> Result<Built> {
    ensure!(ttl > 0, "TTL must be explicit Unix seconds");
    let address = deployment.address();
    let mut context = QueryContext::new(initial.data.clone(), address);
    context.call_context.balance = initial.balance.clone();
    context.call_context.caller = caller;
    context.call_context.com_indices = com_indices.clone();
    // prepare's zero-randomness preimage is diagnostic only. Reuse only its
    // evaluated program and private fields, then repartition for this commitment.
    if let Some(block) = block {
        context.call_context.tblock = block.tblock;
        context.call_context.tblock_err = block.tblock_err;
        context.call_context.parent_block_hash = block.parent_block_hash;
        context.call_context.last_block_time = block.last_block_time;
    }
    let initial_context = context.clone();
    let evaluated = prepare_with_context_and_block_time(
        plan,
        &config.inputs,
        context.clone(),
        parameters,
        block.is_some(),
    )?;
    let call_input = evaluated.call_input()?;
    let call_output = evaluated.call_output()?;
    let randomness = match communication_commitment_rand {
        Some(randomness) if randomness != Fr::from(0u64) => randomness,
        Some(_) => return Err(anyhow!("native call commitment randomness must be nonzero")),
        None => nonzero_random(rng)?,
    };
    let commitment = onchain_runtime::communication_commitment(
        call_input.clone(),
        call_output.clone(),
        randomness,
    );
    let mut partitions = partition_transcripts(
        &[PreTranscript {
            context: context.clone(),
            program: evaluated.program.clone(),
            comm_comm: Some(commitment),
        }],
        parameters,
    )
    .map_err(|_| anyhow!("native transaction partition failed"))?;
    ensure!(partitions.len() == 1, "expected one call partition");
    let (mut guaranteed, fallible) = partitions.pop().unwrap();
    let mut after = context;
    let cost = &parameters.cost_model.runtime_cost_model;
    if evaluated.program.is_empty() {
        ensure!(
            guaranteed.is_none() && fallible.is_none(),
            "empty source program unexpectedly produced a native transcript"
        );
        // Ledger sequencing requires a transcript, including pure and all-inactive calls.
        guaranteed = Some(empty_transcript(&after, cost)?);
    }
    for transcript in guaranteed.iter().chain(fallible.iter()) {
        after = after
            .run_transcript(transcript, cost)
            .map_err(|_| anyhow!("native transaction transcript rejected"))?
            .context;
        ensure!(
            after.effects == transcript.effects,
            "native transaction transcript effects mismatch"
        );
        // The ledger credits inputs before debiting outputs for each transcript.
        let balance = &mut after.call_context.balance;
        for (token, amount) in transcript.effects.unshielded_inputs.clone() {
            let current = balance.get(&token).map(|value| *value).unwrap_or(0);
            *balance = balance.insert(
                token,
                current
                    .checked_add(amount)
                    .context("contract balance overflow")?,
            );
        }
        for (token, amount) in transcript.effects.unshielded_outputs.clone() {
            let current = balance.get(&token).map(|value| *value).unwrap_or(0);
            *balance = balance.insert(
                token,
                current
                    .checked_sub(amount)
                    .context("insufficient contract balance")?,
            );
        }
        after.effects = Default::default();
    }
    let guaranteed_count = guaranteed.as_ref().map_or(0, |t| t.program.len());
    let fallible_count = fallible.as_ref().map_or(0, |t| t.program.len());
    let prototype = ContractCallPrototype {
        address,
        entry_point: entry.clone(),
        op: operation,
        guaranteed_public_transcript: guaranteed,
        fallible_public_transcript: fallible,
        private_transcript_outputs: evaluated
            .preimage
            .private_transcript
            .iter()
            .copied()
            .map(field_value)
            .collect(),
        input: call_input,
        output: call_output,
        communication_commitment_rand: randomness,
        key_location: KeyLocation(Cow::Owned(plan.entrypoint.clone())),
    };
    let ttl = Timestamp::from_secs(ttl);
    let deploy = match retained_intent {
        Some(intent) => intent.clone(),
        None => NativeIntent::empty(rng, ttl).add_deploy(deployment),
    };
    let call = NativeIntent::empty(rng, ttl).add_call::<ProofPreimage>(prototype);
    let checked = real_preimage(&call)?
        .check(circuit)
        .map_err(|_| anyhow!("constructor preimage rejected by official checker"))?;
    ensure!(
        checked.iter().filter(|activity| activity.is_none()).count() == evaluated.program.len(),
        "constructor activity metadata mismatch"
    );
    ensure!(
        real_preimage(&call)?.communications_commitment == Some((commitment, randomness)),
        "constructor communication commitment mismatch"
    );
    let mut predicted = initial.clone();
    predicted.data = after.state;
    predicted.balance = after.call_context.balance;
    let operation_count = evaluated.program.len();
    Ok(Built {
        initial,
        predicted,
        execution: evaluated,
        initial_context,
        entry_point: entry,
        communication_commitment_rand: randomness,
        deploy,
        call,
        address: hex::encode(address.0.0),
        operations: operation_count,
        guaranteed: guaranteed_count,
        fallible: fallible_count,
    })
}

pub(crate) fn prepare_call_for_target(
    plan: &Plan,
    config: &Config,
    parameters: &LedgerParameters,
    verifier: VerifierKey,
    circuit: &IrSource,
    ttl: u64,
    target: &PreparedDeployment,
    rng: &mut (impl Rng + CryptoRng),
) -> Result<NativeIntent> {
    ensure!(
        target.entrypoint == plan.entrypoint,
        "native target entrypoint mismatch"
    );
    let Some(ContractAction::Deploy(deployment)) = target.intent.actions.iter_deref().next() else {
        return Err(anyhow!("native target deployment missing"));
    };
    ensure!(
        hex::encode(deployment.address().0.0) == target.address,
        "native target address mismatch"
    );
    let operation = ContractOperation::new(Some(verifier), None);
    let initial = deployment.initial_state.clone();
    let entry = EntryPointBuf(plan.entrypoint.as_bytes().to_vec());
    let built = build_for_deployment(
        plan,
        config,
        parameters,
        operation,
        circuit,
        ttl,
        initial,
        entry,
        (**deployment).clone(),
        Some(&target.intent),
        None,
        &Map::new(),
        None,
        None,
        rng,
    )?;
    Ok(built.call)
}

/// Prepare a call against current public state while retaining the original deployment address.
#[cfg(test)]
pub(crate) fn prepare_call_for_current_state(
    plan: &Plan,
    contract: &str,
    selected_operation: &str,
    config: &Config,
    parameters: &LedgerParameters,
    operation: ContractOperation,
    circuit: &IrSource,
    ttl: u64,
    target: &PreparedOperationMapDeployment,
    current: &ContractState<Db>,
    rng: &mut (impl Rng + CryptoRng),
) -> Result<(NativeIntent, ContractState<Db>)> {
    let ready = target.ready_state()?;
    prepare_call_for_ready_state(
        plan,
        contract,
        selected_operation,
        config,
        parameters,
        operation,
        circuit,
        ttl,
        target,
        &ready,
        current,
        &Map::new(),
        None,
        None,
        rng,
    )
}

/// Prepare a call against the authenticated ready state while retaining the
/// original partial deployment address and nonce.
pub(crate) fn prepare_call_for_ready_state(
    plan: &Plan,
    contract: &str,
    selected_operation: &str,
    config: &Config,
    parameters: &LedgerParameters,
    operation: ContractOperation,
    circuit: &IrSource,
    ttl: u64,
    target: &PreparedOperationMapDeployment,
    ready: &ContractState<Db>,
    current: &ContractState<Db>,
    com_indices: &BookedComIndices,
    block: Option<&BlockContext>,
    caller: Option<PublicAddress>,
    rng: &mut (impl Rng + CryptoRng),
) -> Result<(NativeIntent, ContractState<Db>)> {
    let built = build_ready_state_call(
        plan,
        contract,
        selected_operation,
        config,
        parameters,
        operation,
        circuit,
        ttl,
        target,
        ready,
        current,
        com_indices,
        block,
        caller,
        None,
        rng,
    )?;
    Ok((built.call, built.predicted))
}

pub(crate) fn prepare_checked_call_for_ready_state(
    plan: &Plan,
    contract: &str,
    selected_operation: &str,
    config: &Config,
    parameters: &LedgerParameters,
    operation: ContractOperation,
    circuit: &IrSource,
    ttl: u64,
    target: &PreparedOperationMapDeployment,
    ready: &ContractState<Db>,
    current: &ContractState<Db>,
    com_indices: &BookedComIndices,
    caller: Option<PublicAddress>,
    communication_commitment_rand: Option<Fr>,
    rng: &mut (impl Rng + CryptoRng),
) -> Result<CheckedCurrentStateCall> {
    let built = build_ready_state_call(
        plan,
        contract,
        selected_operation,
        config,
        parameters,
        operation,
        circuit,
        ttl,
        target,
        ready,
        current,
        com_indices,
        None,
        caller,
        communication_commitment_rand,
        rng,
    )?;
    Ok(CheckedCurrentStateCall {
        execution: built.execution,
        initial_context: built.initial_context,
        entry_point: built.entry_point,
        communication_commitment_rand: built.communication_commitment_rand,
        predicted: built.predicted,
    })
}

fn build_ready_state_call(
    plan: &Plan,
    contract: &str,
    selected_operation: &str,
    config: &Config,
    parameters: &LedgerParameters,
    operation: ContractOperation,
    circuit: &IrSource,
    ttl: u64,
    target: &PreparedOperationMapDeployment,
    ready: &ContractState<Db>,
    current: &ContractState<Db>,
    com_indices: &BookedComIndices,
    block: Option<&BlockContext>,
    caller: Option<PublicAddress>,
    communication_commitment_rand: Option<Fr>,
    rng: &mut (impl Rng + CryptoRng),
) -> Result<Built> {
    ensure!(
        target.contract == contract,
        "native target contract mismatch"
    );
    ensure!(
        selected_operation == plan.entrypoint && valid_operation_name(selected_operation),
        "selected operation does not match plan"
    );
    ensure!(
        target.intent().actions.len() == 1,
        "native target deployment missing"
    );
    let Some(ContractAction::Deploy(deployment)) = target.intent().actions.iter_deref().next()
    else {
        return Err(anyhow!("native target deployment missing"));
    };
    ensure!(
        hex::encode(deployment.address().0.0) == target.address(),
        "native target address mismatch"
    );
    ensure!(
        current.operations == ready.operations
            && current.maintenance_authority.committee == ready.maintenance_authority.committee
            && current.maintenance_authority.threshold == ready.maintenance_authority.threshold,
        "current contract operation revision or authority differs from ready state"
    );
    let entry = EntryPointBuf(selected_operation.as_bytes().to_vec());
    ensure!(
        ready.operations.get(&entry).as_deref() == Some(&operation)
            && current.operations.get(&entry).as_deref() == Some(&operation),
        "selected operation verifier differs from ready state"
    );

    let built = build_for_deployment(
        plan,
        config,
        parameters,
        operation,
        circuit,
        ttl,
        current.clone(),
        entry,
        (**deployment).clone(),
        Some(target.intent()),
        block,
        com_indices,
        caller,
        communication_commitment_rand,
        rng,
    )?;
    ensure!(
        built.address == target.address(),
        "native target address mismatch"
    );
    Ok(built)
}

/// In-memory constructor used by the native proof API after authenticating public material.
pub(crate) fn prepare_call(
    plan: &Plan,
    config: &Config,
    parameters: &LedgerParameters,
    verifier: VerifierKey,
    circuit: &IrSource,
    ttl: u64,
    block: Option<&BlockContext>,
    rng: &mut (impl Rng + CryptoRng),
) -> Result<(NativeIntent, NativeIntent)> {
    let built = build_with_rng(
        plan,
        config,
        parameters,
        ContractOperation::new(Some(verifier), None),
        circuit,
        ttl,
        block,
        rng,
    )?;
    Ok((built.deploy, built.call))
}

struct OutputDirectory {
    path: PathBuf,
    keep: bool,
}
impl OutputDirectory {
    fn new(path: &Path) -> Result<Self> {
        let mut options = fs::DirBuilder::new();
        #[cfg(unix)]
        {
            use std::os::unix::fs::DirBuilderExt;
            options.mode(0o700);
        }
        options
            .create(path)
            .context("output directory must be new")?;
        Ok(Self {
            path: path.to_owned(),
            keep: false,
        })
    }
    fn directory(&self, name: &str) -> Result<()> {
        let mut options = fs::DirBuilder::new();
        #[cfg(unix)]
        {
            use std::os::unix::fs::DirBuilderExt;
            options.mode(0o700);
        }
        options.create(self.path.join(name))?;
        Ok(())
    }
    fn write(&self, name: &str, value: &[u8]) -> Result<()> {
        let mut options = fs::OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt;
            options.mode(0o600);
        }
        let mut file = options.open(self.path.join(name))?;
        file.write_all(value)?;
        file.sync_all()?;
        Ok(())
    }
}
impl Drop for OutputDirectory {
    fn drop(&mut self) {
        if !self.keep {
            let _ = fs::remove_dir_all(&self.path);
        }
    }
}

/// Validate and assemble before creating the private output directory. Never overwrites.
/// Output intents contain witness material and require private storage.
pub fn assemble(inputs: Inputs<'_>, output: &Path) -> Result<Json> {
    ensure!(
        inputs.plan.len() <= 1_048_576
            && inputs.config.len() <= 1_048_576
            && inputs.circuit.len() <= 4_194_304
            && inputs.ledger_parameters.len() <= 1_048_576
            && inputs.prover_key.len() <= 134_217_728
            && inputs.verifier_key.len() <= 1_048_576,
        "assembly input limit exceeded"
    );
    ensure!(!output.exists(), "output directory already exists");
    let plan: Plan = serde_json::from_slice(inputs.plan).context("invalid source plan")?;
    ensure!(
        crate::profile::validate_plan(plan.target.as_deref(), plan.target_profile.as_ref()),
        "plan target differs from linked native profile"
    );
    let config = crate::parse_private_config(inputs.config)?;
    let parameters: LedgerParameters =
        decode(inputs.ledger_parameters).context("invalid ledger parameters")?;
    let circuit = IrSource::load(inputs.circuit).context("invalid native circuit")?;
    ensure!(
        circuit.do_communications_commitment,
        "circuit must bind communication commitment"
    );
    let prover: ProverKey<IrSource> =
        decode(inputs.prover_key).context("invalid native prover key")?;
    let raw = prover
        .init()
        .map_err(|_| anyhow!("native prover key initialization failed"))?;
    ensure!(
        raw.k() == circuit.k(),
        "prover key and circuit size mismatch"
    );
    let verifier: VerifierKey =
        decode(inputs.verifier_key).context("invalid native verifier key")?;
    verifier
        .init()
        .map_err(|_| anyhow!("native verifier key initialization failed"))?;
    let operation = ContractOperation::new(Some(verifier), None);
    let operation_bytes = bytes(&operation)?;
    let built = build(
        &plan,
        &config,
        &parameters,
        operation,
        &circuit,
        inputs.ttl_unix,
    )?;
    let (deploy, deploy_bytes) = roundtrip(&built.deploy)?;
    let (call, call_bytes) = roundtrip(&built.call)?;
    let (initial, initial_bytes) = roundtrip(&built.initial)?;
    let (_, predicted_bytes) = roundtrip(&built.predicted)?;
    ensure!(
        real_preimage(&call)?
            .check(&circuit)
            .map_err(|_| anyhow!("serialized constructor preimage rejected"))?
            .len()
            == built.operations,
        "serialized activity metadata mismatch"
    );
    ensure!(
        deploy.ttl.to_secs() == inputs.ttl_unix && call.ttl.to_secs() == inputs.ttl_unix,
        "serialized TTL mismatch"
    );
    let Some(ContractAction::Deploy(deployment)) = deploy.actions.iter_deref().next() else {
        return Err(anyhow!("serialized deployment missing"));
    };
    ensure!(
        bytes(&deployment.initial_state)? == bytes(&initial)?
            && hex::encode(deployment.address().0.0) == built.address,
        "serialized deployment state mismatch"
    );
    let summary = json!({"qualification":"native Rust constructor preimage checked; no proof or ledger acceptance","runtime":"native Rust","nodeInvoked":false,"address":built.address,"entrypoint":plan.entrypoint,"k":circuit.k(),"operationBytes":operation_bytes.len(),"operations":built.operations,"guaranteedOps":built.guaranteed,"fallibleOps":built.fallible,"ttlUnix":inputs.ttl_unix,"sourcePlanSha256":digest(inputs.plan),"nativeCircuitSha256":digest(inputs.circuit),"ledgerParametersSha256":digest(inputs.ledger_parameters),"initialStateSha256":digest(&initial_bytes),"predictedStateSha256":digest(&predicted_bytes),"ledgerRevision":LEDGER_REVISION,"zkirRevision":ZKIR_REVISION,"zkirRelease":crate::profile::RELEASE,"runtimeProfile":crate::profile::ABI,"officialConstructorPreimageChecked":true,"nativeSerializationRoundtrip":true,"freshCryptographicRandomness":true,"keyPairAssociationVerified":false,"cryptographicProofGenerated":false,"transactionSubmitted":false});
    let mut directory = OutputDirectory::new(output)?;
    directory.directory("keys")?;
    directory.directory("zkir")?;
    for (name, value) in [
        (
            format!("keys/{}.prover", plan.entrypoint),
            inputs.prover_key.to_vec(),
        ),
        (
            format!("keys/{}.verifier", plan.entrypoint),
            inputs.verifier_key.to_vec(),
        ),
        (
            format!("zkir/{}.zkir", plan.entrypoint),
            inputs.circuit.to_vec(),
        ),
        (format!("zkir/{}.bzkir", plan.entrypoint), bytes(&circuit)?),
        ("initial-state.bin".into(), initial_bytes),
        ("predicted-state.bin".into(), predicted_bytes),
        ("deploy-intent.bin".into(), deploy_bytes),
        ("call-intent.bin".into(), call_bytes),
        (
            "constructor-preimage.bin".into(),
            bytes(real_preimage(&call)?)?,
        ),
        ("source-plan.json".into(), inputs.plan.to_vec()),
        ("runtime-config.json".into(), inputs.config.to_vec()),
        ("ledger.params".into(), inputs.ledger_parameters.to_vec()),
        (
            "native-contract.json".into(),
            serde_json::to_vec_pretty(&summary)?,
        ),
    ] {
        directory.write(&name, &value)?;
    }
    directory.keep = true;
    Ok(summary)
}

/// Assemble exclusively from retained, verified public payloads and separate private inputs.
/// Callers authenticate the bundle with an external trusted manifest digest at verification.
pub fn assemble_verified(
    bundle: &VerifiedBundle,
    private_config: &[u8],
    ttl_unix: u64,
    output: &Path,
) -> Result<Json> {
    assemble(
        Inputs {
            plan: bundle.file(Role::Plan)?,
            circuit: bundle.file(Role::Circuit)?,
            prover_key: bundle.file(Role::ProverKey)?,
            verifier_key: bundle.file(Role::VerifierKey)?,
            ledger_parameters: bundle.file(Role::LedgerParameters)?,
            config: private_config,
            ttl_unix,
        },
        output,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    struct ConstantRng(u8, usize);
    impl rand::RngCore for ConstantRng {
        fn next_u32(&mut self) -> u32 {
            u32::from_le_bytes([self.0; 4])
        }
        fn next_u64(&mut self) -> u64 {
            u64::from_le_bytes([self.0; 8])
        }
        fn fill_bytes(&mut self, bytes: &mut [u8]) {
            self.1 += 1;
            assert!(self.1 <= 128, "entropy sampling did not stop");
            bytes.fill(self.0);
        }
        fn try_fill_bytes(&mut self, bytes: &mut [u8]) -> std::result::Result<(), rand::Error> {
            self.fill_bytes(bytes);
            Ok(())
        }
    }
    impl CryptoRng for ConstantRng {}

    #[test]
    fn constructor_bounds_zero_and_noncanonical_host_entropy() {
        let (plan, config, circuit) = sample();
        for byte in [0, 255] {
            let mut rng = ConstantRng(byte, 0);
            let error = build_with_rng(
                &plan,
                &config,
                &ledger::structure::INITIAL_PARAMETERS,
                ContractOperation::new(None, None),
                &circuit,
                2_000_000_000,
                None,
                &mut rng,
            )
            .err()
            .unwrap();
            assert_eq!(error.to_string(), "host entropy rejected");
            assert_eq!(rng.1, 128);
        }
        let mut rng = ConstantRng(1, 0);
        assert_eq!(
            nonzero_random(&mut rng).unwrap(),
            Fr::from_le_bytes(&[1; 32]).unwrap()
        );
        assert_eq!(rng.1, 1);
    }
    fn selected_fixture_json() -> Json {
        let mut value: Json =
            serde_json::from_str(include_str!("../tests/fixtures/unsigned/plan.json")).unwrap();
        if cfg!(feature = "zkir-321") {
            value["target"] = json!(crate::profile::NAME);
            value["targetProfile"] = crate::profile::target_json();
        }
        value
    }
    fn selected_fixture_plan() -> Plan {
        serde_json::from_value(selected_fixture_json()).unwrap()
    }
    fn sample() -> (Plan, Config, IrSource) {
        (selected_fixture_plan(),
         serde_json::from_value(json!({"inputs":{"left":"255","right":"255","expected":"510"},"state":{"total":"0"}})).unwrap(),
         IrSource::load(include_bytes!("../tests/fixtures/unsigned/circuit.zkir").as_slice()).unwrap())
    }
    fn operation_entries(names: &[&str]) -> Vec<(String, ContractOperation)> {
        names
            .iter()
            .map(|name| (name.to_string(), ContractOperation::new(None, None)))
            .collect()
    }
    #[test]
    fn constructor_uses_fresh_randomness_and_roundtrips_real_preimage() {
        let (plan, config, circuit) = sample();
        let parameters = &ledger::structure::INITIAL_PARAMETERS;
        // A key-free operation tests constructor/checker semantics only. CLI integration
        // separately validates real tagged prover and verifier keys before building.
        let first = build(
            &plan,
            &config,
            parameters,
            ContractOperation::new(None, None),
            &circuit,
            2_000_000_000,
        )
        .unwrap();
        let second = build(
            &plan,
            &config,
            parameters,
            ContractOperation::new(None, None),
            &circuit,
            2_000_000_000,
        )
        .unwrap();
        assert_ne!(first.address, second.address);
        let first_proof = real_preimage(&first.call).unwrap();
        let second_proof = real_preimage(&second.call).unwrap();
        assert_ne!(
            first_proof.communications_commitment,
            second_proof.communications_commitment
        );
        assert_ne!(
            first_proof.communications_commitment.unwrap().1,
            Fr::from(0u64)
        );
        let (decoded, _) = roundtrip(&first.call).unwrap();
        assert_eq!(
            real_preimage(&decoded)
                .unwrap()
                .check(&circuit)
                .unwrap()
                .len(),
            8
        );
        let (decoded, _) = roundtrip(&first.deploy).unwrap();
        assert_eq!(decoded.ttl.to_secs(), 2_000_000_000);
    }
    #[cfg(feature = "zkir-321")]
    #[test]
    fn pure_call_retains_the_transcript_required_by_ledger_sequencing() {
        let plan: Plan = serde_json::from_slice(include_bytes!(
            "../tests/fixtures/curve-witness/321/CurveWitness.claim.impact.json"
        ))
        .unwrap();
        let circuit = IrSource::load(
            include_bytes!("../tests/fixtures/curve-witness/321/CurveWitness.claim.zkir")
                .as_slice(),
        )
        .unwrap();
        let config: Config = serde_json::from_value(json!({
            "state": {},
            "inputs": {
                "scalar": {"kind": "jubjubScalar", "value": "0"},
                "expectedScalar": {"kind": "jubjubScalar", "value": "0"},
                "$helper5": {"kind": "jubjubScalar", "value": "0"},
                "point": {"kind": "jubjubPoint", "x": "0", "y": "1"},
                "expectedPoint": {"kind": "jubjubPoint", "x": "0", "y": "1"},
                "$helper8": {"kind": "jubjubPoint", "x": "0", "y": "1"}
            }
        }))
        .unwrap();
        let built = build(
            &plan,
            &config,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractOperation::new(None, None),
            &circuit,
            2_000_000_000,
        )
        .unwrap();
        let Some(ContractAction::Call(call)) = built.call.actions.iter_deref().next() else {
            panic!("expected a call");
        };
        assert!(
            call.guaranteed_transcript
                .as_ref()
                .unwrap()
                .program
                .is_empty()
        );
        assert!(call.fallible_transcript.is_none());
        assert!(
            real_preimage(&built.call)
                .unwrap()
                .check(&circuit)
                .unwrap()
                .is_empty()
        );
    }
    #[test]
    fn wrong_inputs_reject_the_real_constructor_preimage() {
        let (plan, mut config, circuit) = sample();
        config.inputs.insert("expected".into(), json!("509"));
        assert!(
            build(
                &plan,
                &config,
                &ledger::structure::INITIAL_PARAMETERS,
                ContractOperation::new(None, None),
                &circuit,
                2_000_000_000
            )
            .is_err()
        );
    }
    #[test]
    fn private_output_rollback_and_no_overwrite() {
        let path =
            std::env::temp_dir().join(format!("noctium-assembly-test-{}", OsRng.r#gen::<u64>()));
        {
            let directory = OutputDirectory::new(&path).unwrap();
            directory.write("private.bin", b"synthetic").unwrap();
            assert!(OutputDirectory::new(&path).is_err());
            assert!(directory.write("private.bin", b"replacement").is_err());
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                assert_eq!(
                    fs::metadata(&path).unwrap().permissions().mode() & 0o777,
                    0o700
                );
                assert_eq!(
                    fs::metadata(path.join("private.bin"))
                        .unwrap()
                        .permissions()
                        .mode()
                        & 0o777,
                    0o600
                );
            }
        }
        assert!(!path.exists());
    }
    #[test]
    fn invalid_assembly_leaves_destination_absent() {
        let path =
            std::env::temp_dir().join(format!("noctium-assembly-invalid-{}", OsRng.r#gen::<u64>()));
        assert!(
            assemble(
                Inputs {
                    plan: b"{}",
                    circuit: b"{}",
                    prover_key: b"",
                    verifier_key: b"",
                    ledger_parameters: b"",
                    config: b"{}",
                    ttl_unix: 2_000_000_000
                },
                &path
            )
            .is_err()
        );
        assert!(!path.exists());
    }
    #[test]
    fn malformed_private_config_discards_value_bearing_parser_cause() {
        let path =
            std::env::temp_dir().join(format!("noctium-assembly-privacy-{}", OsRng.r#gen::<u64>()));
        let selected_plan = serde_json::to_vec(&selected_fixture_json()).unwrap();
        let error = assemble(
            Inputs {
                plan: &selected_plan,
                circuit: b"{}",
                prover_key: b"",
                verifier_key: b"",
                ledger_parameters: b"",
                config: br#"{"inputs":"SENTINEL_SECRET_PRIVATE_CONFIG","state":{}}"#,
                ttl_unix: 2_000_000_000,
            },
            &path,
        )
        .unwrap_err();
        for rendered in [
            format!("{error}"),
            format!("{error:#}"),
            format!("{error:?}"),
        ] {
            assert!(rendered.contains("invalid private configuration"));
            assert!(!rendered.contains("SENTINEL_SECRET_PRIVATE_CONFIG"));
        }
        assert_eq!(error.chain().count(), 1);
        assert!(!path.exists());
    }

    #[test]
    fn operation_map_deployment_requires_complete_unique_bounded_valid_names() {
        let (plan, config, _) = sample();
        let names = vec!["apply".to_owned(), "alias".to_owned()];
        let mut rng = ConstantRng(1, 0);
        let target = prepare_operation_map_deployment_target(
            &plan,
            "BoundedScalars",
            &config.state,
            &names,
            operation_entries(&["apply", "alias"]),
            2_000_000_000,
            &mut rng,
        )
        .unwrap();
        let Some(ContractAction::Deploy(deployment)) = target.intent.actions.iter_deref().next()
        else {
            panic!("operation map target should retain one deployment");
        };
        assert_eq!(deployment.initial_state.operations.iter().count(), 2);
        assert!(
            deployment
                .initial_state
                .operations
                .get(&EntryPointBuf(b"apply".to_vec()))
                .is_some()
        );

        for (names, entries) in [
            (
                vec!["apply".to_owned(), "apply".to_owned()],
                operation_entries(&["apply", "apply"]),
            ),
            (
                vec!["apply".to_owned(), "alias".to_owned()],
                operation_entries(&["apply", "apply"]),
            ),
            (
                vec!["apply".to_owned(), "alias".to_owned()],
                operation_entries(&["apply"]),
            ),
            (
                vec!["apply".to_owned(), "bad-name".to_owned()],
                operation_entries(&["apply", "bad-name"]),
            ),
            (vec!["alias".to_owned()], operation_entries(&["alias"])),
        ] {
            assert!(
                prepare_operation_map_deployment_target(
                    &plan,
                    "BoundedScalars",
                    &config.state,
                    &names,
                    entries,
                    2_000_000_000,
                    &mut rng,
                )
                .is_err()
            );
        }

        let too_many: Vec<_> = (0..=crate::artifacts::MAX_ENTRIES)
            .map(|index| format!("op{index}"))
            .collect();
        assert!(
            prepare_operation_map_deployment_target(
                &plan,
                "BoundedScalars",
                &config.state,
                &too_many,
                too_many
                    .iter()
                    .map(|name| (name.clone(), ContractOperation::new(None, None)))
                    .collect(),
                2_000_000_000,
                &mut rng,
            )
            .is_err()
        );
    }

    #[test]
    fn current_state_call_keeps_original_deployment_and_uses_current_data() {
        let (mut plan, mut config, circuit) = sample();
        plan.state.push(crate::StateDecl {
            name: "unused".into(),
            kind: json!({"cell":"UIntRange<511>"}),
            sealed: false,
            cell_alignment: None,
        });
        config.state.insert("unused".into(), json!("0"));
        let names = vec!["apply".to_owned(), "alias".to_owned()];
        let entries = operation_entries(&["apply", "alias"]);
        let mut rng = ConstantRng(1, 0);
        let target = prepare_operation_map_deployment_target(
            &plan,
            "BoundedScalars",
            &config.state,
            &names,
            entries,
            2_000_000_000,
            &mut rng,
        )
        .unwrap();
        let retained_bytes = bytes(&target.intent).unwrap();
        let Some(ContractAction::Deploy(deployment)) = target.intent.actions.iter_deref().next()
        else {
            panic!("operation map target should retain one deployment");
        };
        let initial_state = deployment.initial_state.clone();
        let original_address = target.address.clone();
        let operation = ContractOperation::new(None, None);

        let mut changed_state = config.state.clone();
        changed_state.insert("unused".into(), json!("7"));
        let mut current = initial_state.clone();
        current.data = create_state(&plan, &changed_state).unwrap();
        let mut call_rng = ConstantRng(1, 0);
        let (call, predicted) = prepare_call_for_current_state(
            &plan,
            "BoundedScalars",
            "apply",
            &config,
            &ledger::structure::INITIAL_PARAMETERS,
            operation,
            &circuit,
            2_000_000_000,
            &target,
            &current,
            &mut call_rng,
        )
        .unwrap();
        let Some(ContractAction::Call(call_action)) = call.actions.iter_deref().next() else {
            panic!("current state intent should contain one call");
        };
        assert_eq!(hex::encode(call_action.address.0.0), original_address);
        assert_eq!(predicted.operations, current.operations);
        assert_ne!(
            bytes(&predicted.data).unwrap(),
            bytes(&initial_state.data).unwrap()
        );
        assert_eq!(
            crate::read_state_cell(
                &QueryContext::new(predicted.data.clone(), deployment.address()),
                1,
                &[],
                "UIntRange<511>",
                "field"
            )
            .unwrap(),
            crate::input_value("UIntRange<511>", &json!("7")).unwrap()
        );
        assert_eq!(bytes(&target.intent).unwrap(), retained_bytes);
        assert_eq!(target.address, original_address);
    }

    #[test]
    fn current_state_call_rejects_wrong_selection_and_changed_operation_revision() {
        use rand::{Rng, rngs::OsRng};

        let (plan, config, circuit) = sample();
        let mut key_rng = OsRng;
        // Synthetic uninitialized keys test binding equality only, never proof verification.
        let verifier: VerifierKey = key_rng.r#gen();
        let names = vec!["apply".to_owned(), "alias".to_owned()];
        let entries = vec![
            (
                "apply".to_owned(),
                ContractOperation::new(Some(verifier.clone()), None),
            ),
            ("alias".to_owned(), ContractOperation::new(None, None)),
        ];
        let mut rng = ConstantRng(1, 0);
        let target = prepare_operation_map_deployment_target(
            &plan,
            "BoundedScalars",
            &config.state,
            &names,
            entries,
            2_000_000_000,
            &mut rng,
        )
        .unwrap();
        let Some(ContractAction::Deploy(deployment)) = target.intent.actions.iter_deref().next()
        else {
            panic!("operation map target should retain one deployment");
        };
        let current = deployment.initial_state.clone();

        assert!(
            prepare_call_for_current_state(
                &plan,
                "BoundedScalars",
                "alias",
                &config,
                &ledger::structure::INITIAL_PARAMETERS,
                ContractOperation::new(Some(verifier.clone()), None),
                &circuit,
                2_000_000_000,
                &target,
                &current,
                &mut rng,
            )
            .is_err()
        );
        assert!(
            prepare_call_for_current_state(
                &plan,
                "BoundedScalars",
                "apply",
                &config,
                &ledger::structure::INITIAL_PARAMETERS,
                ContractOperation::new(None, None),
                &circuit,
                2_000_000_000,
                &target,
                &current,
                &mut rng,
            )
            .is_err()
        );

        let mut changed = current.clone();
        changed.operations = changed.operations.insert(
            EntryPointBuf(b"apply".to_vec()),
            ContractOperation::new(None, None),
        );
        assert!(
            prepare_call_for_current_state(
                &plan,
                "BoundedScalars",
                "apply",
                &config,
                &ledger::structure::INITIAL_PARAMETERS,
                ContractOperation::new(Some(verifier), None),
                &circuit,
                2_000_000_000,
                &target,
                &changed,
                &mut rng,
            )
            .is_err()
        );
    }

    #[test]
    fn legacy_single_entrypoint_target_keeps_its_retained_address() {
        use rand::{Rng, rngs::OsRng};

        let (plan, config, circuit) = sample();
        let verifier: VerifierKey = OsRng.r#gen();
        let mut rng = ConstantRng(1, 0);
        let target = prepare_deployment_target(
            &plan,
            &config.state,
            verifier.clone(),
            2_000_000_000,
            &mut rng,
        )
        .unwrap();
        let retained = bytes(&target.intent).unwrap();
        let call = prepare_call_for_target(
            &plan,
            &config,
            &ledger::structure::INITIAL_PARAMETERS,
            verifier,
            &circuit,
            2_000_000_000,
            &target,
            &mut rng,
        )
        .unwrap();
        let Some(ContractAction::Call(call)) = call.actions.iter_deref().next() else {
            panic!("legacy target helper should return a call");
        };
        assert_eq!(hex::encode(call.address.0.0), target.address);
        assert_eq!(bytes(&target.intent).unwrap(), retained);
    }
}
