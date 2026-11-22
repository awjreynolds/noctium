//! Owned native client tasks. Transport, wallet, approval and durable stores are explicit services.
use crate::{
    assembly::NativeIntent,
    client::{
        self, BoundTransaction, CasReceipt, ChainAdapter, FinalizedReceipt, FundingAdapter,
        HostFailure, JournalStore, NetworkPolicy, Observation, ObservedReceipt, RecoveryRecord,
        SigningAdapter, Snapshot, StoreAcknowledgement, StoredRecord, Submission,
        SubmissionAttempt,
    },
    funding::{SealedTransaction, UnsealedTransaction},
    host,
    lifecycle::Phase,
    proof::{ContractStateBinding, CurrentStateContext, ProvedNativeIntent},
};
use futures::{Future, FutureExt, channel::oneshot, task::noop_waker};
use serde::Deserialize;
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    pin::Pin,
    sync::{
        Arc, Mutex,
        atomic::{AtomicU64, Ordering},
    },
    task::{Context, Poll},
};
use zeroize::Zeroizing;
const MAX_REQUESTS: usize = 1024;
fn require(condition: bool, error: client::Error) -> Result<(), client::Error> {
    if condition { Ok(()) } else { Err(error) }
}
static NEXT_REQUEST: AtomicU64 = AtomicU64::new(1);
#[derive(Clone, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct Capabilities {
    pub chain: String,
    pub funding: String,
    pub signing: String,
    pub journal: String,
}
impl Capabilities {
    pub fn validate(&self) -> bool {
        [&self.chain, &self.funding, &self.signing, &self.journal]
            .iter()
            .all(|s| {
                !s.is_empty()
                    && s.len() <= 128
                    && s.bytes()
                        .all(|b| b.is_ascii_alphanumeric() || b"._-".contains(&b))
            })
    }
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct Descriptor {
    pub abi_version: u32,
    #[serde(deserialize_with = "policy")]
    pub policy: NetworkPolicy,
    pub capabilities: Capabilities,
}
pub(crate) fn policy<'de, D: serde::Deserializer<'de>>(d: D) -> Result<NetworkPolicy, D::Error> {
    #[derive(Deserialize)]
    #[serde(rename_all = "camelCase", deny_unknown_fields)]
    struct Wire {
        network_id: String,
        genesis: String,
        spec_version: u32,
        transaction_version: u32,
        profile: String,
        max_dust: String,
    }
    let w = Wire::deserialize(d)?;
    let amount = w
        .max_dust
        .parse::<u128>()
        .ok()
        .filter(|v| v.to_string() == w.max_dust && *v > 0)
        .ok_or_else(|| serde::de::Error::custom("invalid_native_budget"))?;
    Ok(NetworkPolicy {
        network_id: w.network_id,
        genesis: w.genesis,
        spec_version: w.spec_version,
        transaction_version: w.transaction_version,
        profile: w.profile,
        max_dust: amount,
    })
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct Setup {
    pub host_context: host::Context,
    pub stages: Vec<host::Stage>,
}
pub(crate) enum Contract {
    Proved(ProvedNativeIntent),
    Deployment {
        intent: ProvedNativeIntent,
        entrypoint: String,
    },
    /// Proof-free maintenance action. `entrypoint` names its local host journal target.
    Maintenance {
        intent: ProvedNativeIntent,
        entrypoint: String,
    },
}
fn snapshot_copy(s: &Snapshot) -> Snapshot {
    Snapshot {
        chain: s.chain.clone(),
        finalized_hash: s.finalized_hash.clone(),
        height: s.height,
        state: s.state.clone(),
        block: s.block.clone(),
    }
}
fn record_copy(r: &RecoveryRecord) -> Result<RecoveryRecord, HostFailure> {
    serde_json::from_slice(&r.private_bytes().map_err(|_| HostFailure)?).map_err(|_| HostFailure)
}
pub(crate) fn recovery_host_context(context: &[u8]) -> Result<host::Context, client::Error> {
    let value: Json = serde_json::from_slice(context).map_err(|_| client::Error::Identity)?;
    if value.get("recoveryVersion").is_some() {
        serde_json::from_value(value["context"].clone()).map_err(|_| client::Error::Identity)
    } else {
        serde_json::from_value(value).map_err(|_| client::Error::Identity)
    }
}
pub(crate) enum RequestData {
    Snapshot,
    Fund {
        contract: ProvedNativeIntent,
        snapshot: Snapshot,
    },
    Sign {
        transaction: UnsealedTransaction,
        snapshot: Snapshot,
    },
    Submit(BoundTransaction),
    Observe(BoundTransaction),
    Load(String),
    Persist {
        record: RecoveryRecord,
        expected_revision: Option<u64>,
    },
    Cas(RecoveryRecord),
}
pub(crate) enum ServiceReply {
    Snapshot(Snapshot),
    Funded(UnsealedTransaction),
    Signed(SealedTransaction),
    Submitted(Submission),
    Observed(Observation),
    Loaded(StoredRecord),
    Persisted(StoreAcknowledgement),
    Cas(CasReceipt),
    Failure,
}
pub(crate) struct Request {
    pub id: u64,
    pub operation: &'static str,
    pub capability: String,
    pub schema: &'static str,
    pub policy: NetworkPolicy,
    pub data: RequestData,
}
impl Request {
    pub fn metadata(&self) -> Json {
        json!({"abiVersion":1,"status":"need_host","requestId":self.id.to_string(),"operation":self.operation,"capability":self.capability,"schema":self.schema,"profile":crate::profile::NAME,"hasPrivateArguments":matches!(self.data,RequestData::Fund{..}|RequestData::Sign{..}|RequestData::Load(_)|RequestData::Persist{..}|RequestData::Cas(_))})
    }
    pub fn accepts(&self, reply: &ServiceReply) -> bool {
        matches!(
            (&self.data, reply),
            (_, ServiceReply::Failure)
                | (RequestData::Snapshot, ServiceReply::Snapshot(_))
                | (RequestData::Fund { .. }, ServiceReply::Funded(_))
                | (RequestData::Sign { .. }, ServiceReply::Signed(_))
                | (RequestData::Submit(_), ServiceReply::Submitted(_))
                | (RequestData::Observe(_), ServiceReply::Observed(_))
                | (RequestData::Load(_), ServiceReply::Loaded(_))
                | (RequestData::Persist { .. }, ServiceReply::Persisted(_))
                | (RequestData::Cas(_), ServiceReply::Cas(_))
        )
    }
    pub fn private_bytes(&self) -> Result<Zeroizing<Vec<u8>>, client::Error> {
        match &self.data {
            RequestData::Persist { record, .. } | RequestData::Cas(record) => {
                record.private_bytes()
            }
            RequestData::Fund { contract, .. } => encode(contract).map(Zeroizing::new),
            RequestData::Sign { transaction, .. } => encode(transaction).map(Zeroizing::new),
            RequestData::Load(attempt) => Ok(Zeroizing::new(attempt.as_bytes().to_vec())),
            _ => Err(client::Error::State),
        }
    }
}
fn encode<T: serialize::Serializable + serialize::Tagged>(v: &T) -> Result<Vec<u8>, client::Error> {
    let mut b = Vec::new();
    serialize::tagged_serialize(v, &mut b).map_err(|_| client::Error::InvalidTransaction)?;
    Ok(b)
}
struct Pending {
    request: Arc<Request>,
    sender: oneshot::Sender<ServiceReply>,
}
struct Mailbox {
    pending: Option<Pending>,
    count: usize,
}
#[derive(Clone)]
struct Adapter {
    mailbox: Arc<Mutex<Mailbox>>,
    capabilities: Capabilities,
    policy: NetworkPolicy,
}
impl Adapter {
    async fn exchange(&self, data: RequestData) -> Result<ServiceReply, HostFailure> {
        let (operation, capability, schema) = match &data {
            RequestData::Snapshot => (
                "chain.snapshot.v1",
                &self.capabilities.chain,
                "native.snapshot.v1",
            ),
            RequestData::Fund { .. } => (
                "funding.native.v1",
                &self.capabilities.funding,
                "native.unsealed-transaction.v1",
            ),
            RequestData::Sign { .. } => (
                "approval.sign.v1",
                &self.capabilities.signing,
                "native.sealed-transaction.v1",
            ),
            RequestData::Submit(_) => (
                "chain.submit.v1",
                &self.capabilities.chain,
                "native.submission.v1",
            ),
            RequestData::Observe(_) => (
                "chain.observe.v1",
                &self.capabilities.chain,
                "native.finalized-receipt.v1",
            ),
            RequestData::Load(_) => (
                "journal.load.v1",
                &self.capabilities.journal,
                "native.trusted-record.v1",
            ),
            RequestData::Persist { .. } => (
                "journal.persist.v1",
                &self.capabilities.journal,
                "native.durable-ack.v1",
            ),
            RequestData::Cas(_) => (
                "private_state.compare_exchange.v1",
                &self.capabilities.journal,
                "native.cas-receipt.v1",
            ),
        };
        let (sender, receiver) = oneshot::channel();
        {
            let mut m = self.mailbox.lock().map_err(|_| HostFailure)?;
            if m.pending.is_some() || m.count >= MAX_REQUESTS {
                return Err(HostFailure);
            }
            let id = NEXT_REQUEST
                .try_update(Ordering::Relaxed, Ordering::Relaxed, |v| v.checked_add(1))
                .map_err(|_| HostFailure)?;
            m.count += 1;
            m.pending = Some(Pending {
                request: Arc::new(Request {
                    id,
                    operation,
                    capability: capability.clone(),
                    schema,
                    policy: self.policy.clone(),
                    data,
                }),
                sender,
            });
        }
        receiver.await.map_err(|_| HostFailure)
    }
}
impl ChainAdapter for Adapter {
    async fn snapshot(&self) -> Result<Snapshot, HostFailure> {
        match self.exchange(RequestData::Snapshot).await? {
            ServiceReply::Snapshot(s) => Ok(s),
            _ => Err(HostFailure),
        }
    }
    async fn submit(&self, t: &BoundTransaction) -> Result<Submission, HostFailure> {
        match self.exchange(RequestData::Submit(t.clone())).await? {
            ServiceReply::Submitted(s) => Ok(s),
            _ => Err(HostFailure),
        }
    }
    async fn observe(&self, t: &BoundTransaction) -> Result<Observation, HostFailure> {
        match self.exchange(RequestData::Observe(t.clone())).await? {
            ServiceReply::Observed(s) => Ok(s),
            _ => Err(HostFailure),
        }
    }
}
impl FundingAdapter for Adapter {
    async fn fund(
        &self,
        c: &ProvedNativeIntent,
        s: &Snapshot,
        p: &NetworkPolicy,
    ) -> Result<UnsealedTransaction, HostFailure> {
        if *p != self.policy {
            return Err(HostFailure);
        }
        match self
            .exchange(RequestData::Fund {
                contract: c.clone(),
                snapshot: snapshot_copy(s),
            })
            .await?
        {
            ServiceReply::Funded(t) => Ok(t),
            _ => Err(HostFailure),
        }
    }
}
impl SigningAdapter for Adapter {
    async fn approve_and_sign(
        &self,
        t: &UnsealedTransaction,
        s: &Snapshot,
        p: &NetworkPolicy,
    ) -> Result<SealedTransaction, HostFailure> {
        if *p != self.policy {
            return Err(HostFailure);
        }
        match self
            .exchange(RequestData::Sign {
                transaction: t.clone(),
                snapshot: snapshot_copy(s),
            })
            .await?
        {
            ServiceReply::Signed(t) => Ok(t),
            _ => Err(HostFailure),
        }
    }
}
impl JournalStore for Adapter {
    async fn load(&self, id: &str) -> Result<StoredRecord, HostFailure> {
        match self.exchange(RequestData::Load(id.into())).await? {
            ServiceReply::Loaded(r) => Ok(r),
            _ => Err(HostFailure),
        }
    }
    async fn persist(
        &self,
        r: &RecoveryRecord,
        expected_revision: Option<u64>,
    ) -> Result<StoreAcknowledgement, HostFailure> {
        match self
            .exchange(RequestData::Persist {
                record: record_copy(r)?,
                expected_revision,
            })
            .await?
        {
            ServiceReply::Persisted(a) => Ok(a),
            _ => Err(HostFailure),
        }
    }
    async fn compare_exchange(&self, r: &RecoveryRecord) -> Result<CasReceipt, HostFailure> {
        match self.exchange(RequestData::Cas(record_copy(r)?)).await? {
            ServiceReply::Cas(c) => Ok(c),
            _ => Err(HostFailure),
        }
    }
}
fn address(c: &Contract) -> Result<(String, String), client::Error> {
    use ledger::structure::ContractAction;
    let (a, entry) = match c {
        Contract::Proved(i) => match i.actions.iter_deref().next() {
            Some(ContractAction::Call(c)) => (
                c.address,
                String::from_utf8(c.entry_point.0.clone()).map_err(|_| client::Error::Identity)?,
            ),
            Some(ContractAction::Deploy(d)) => (d.address(), "claim".into()),
            _ => return Err(client::Error::Identity),
        },
        Contract::Deployment { intent, entrypoint } => match intent.actions.iter_deref().next() {
            Some(ContractAction::Deploy(d)) => (d.address(), entrypoint.clone()),
            _ => return Err(client::Error::Identity),
        },
        Contract::Maintenance { intent, entrypoint } => match intent.actions.iter_deref().next() {
            Some(ContractAction::Maintain(update)) => (update.address, entrypoint.clone()),
            _ => return Err(client::Error::Identity),
        },
    };
    Ok((hex::encode(a.0.0), entry))
}
struct State {
    policy: NetworkPolicy,
    contract: Option<Contract>,
    runtime: Option<host::Runtime>,
    attempt: Option<SubmissionAttempt>,
    context: Zeroizing<Vec<u8>>,
    receipt: Option<FinalizedReceipt>,
    state_binding: Option<ContractStateBinding>,
    context_issued: bool,
    durable: bool,
    cancelled: bool,
}
fn restored_runtime(
    context: &[u8],
    attempt: &SubmissionAttempt,
) -> Result<host::Runtime, client::Error> {
    let context_json: Json =
        serde_json::from_slice(context).map_err(|_| client::Error::Identity)?;
    let recovery = context_json.get("recoveryVersion").is_some();
    let ctx = recovery_host_context(context)?;
    let journal: Json = serde_json::from_slice(attempt.record().journal_bytes())
        .map_err(|_| client::Error::Identity)?;
    if journal["attemptId"] != ctx.attempt_id
        || journal["baseRevision"] != ctx.base_revision
        || journal["namespace"] != ctx.namespace
    {
        return Err(client::Error::Identity);
    }
    let target: String = journal["contractAddress"]
        .as_str()
        .ok_or(client::Error::Identity)?
        .into();
    let entry: String = journal["entrypoint"]
        .as_str()
        .ok_or(client::Error::Identity)?
        .into();
    let capabilities: Vec<_> = ctx
        .capabilities
        .iter()
        .map(|c| {
            (
                c.id.clone(),
                c.key_prefix.clone(),
                c.operations.contains(&host::STAGE.into()),
            )
        })
        .collect();
    let mut runtime = if recovery {
        host::Runtime::from_recovery_context(context_json).map_err(|_| client::Error::Identity)?
    } else {
        host::Runtime::new(ctx, &BTreeMap::new(), target.clone(), entry.clone())
            .map_err(|_| client::Error::Identity)?
    };
    if !runtime.has_target(&target, &entry) {
        return Err(client::Error::Identity);
    }
    let typed_registry = runtime.typed_registry().cloned();
    for (key, write) in journal["writes"]
        .as_object()
        .ok_or(client::Error::Identity)?
    {
        let cap = capabilities
            .iter()
            .find(|(_, prefix, stage)| *stage && key.starts_with(prefix))
            .ok_or(client::Error::Identity)?;
        let stage = host::Stage {
            abi_version: if typed_registry.is_some() { 2 } else { 1 },
            operation: host::STAGE.into(),
            capability: cap.0.clone(),
            key: key.clone(),
            ty: write["type"]
                .as_str()
                .ok_or(client::Error::Identity)?
                .into(),
            value: write["value"].clone(),
        };
        if let Some(registry) = &typed_registry {
            runtime
                .stage_typed(stage, registry)
                .map_err(|_| client::Error::Identity)?;
        } else {
            runtime.stage(stage).map_err(|_| client::Error::Identity)?;
        }
    }
    runtime
        .execution_finished(true)
        .map_err(|_| client::Error::State)?;
    attempt.restore_runtime(&mut runtime)?;
    Ok(runtime)
}
#[derive(Clone, Copy, Eq, PartialEq)]
pub(crate) enum Command {
    Prepare,
    Submit,
    Observe,
    Commit,
    Cancel,
    Deadline,
    Reload,
}
impl Command {
    pub fn parse(s: &str) -> Option<Self> {
        Some(match s {
            "prepare" => Self::Prepare,
            "submit" => Self::Submit,
            "observe" => Self::Observe,
            "commit" => Self::Commit,
            "cancel" => Self::Cancel,
            "deadline" => Self::Deadline,
            "reload" => Self::Reload,
            _ => return None,
        })
    }
}
// A deployment contains no call/dust preimage. Ask the native prover to preserve that fact.
#[derive(Clone)]
struct NoProof;
impl transient_crypto::proofs::Resolver for NoProof {
    async fn resolve_key(
        &self,
        _: transient_crypto::proofs::KeyLocation,
    ) -> std::io::Result<Option<transient_crypto::proofs::ProvingKeyMaterial>> {
        Ok(None)
    }
}
impl transient_crypto::proofs::ProvingProvider for NoProof {
    async fn check(
        &self,
        _: &transient_crypto::proofs::ProofPreimage,
    ) -> anyhow::Result<Vec<Option<usize>>> {
        Err(anyhow::anyhow!("deployment_has_no_proof"))
    }
    async fn prove(
        self,
        _: &transient_crypto::proofs::ProofPreimage,
        _: Option<transient_crypto::curve::Fr>,
    ) -> anyhow::Result<transient_crypto::proofs::Proof> {
        Err(anyhow::anyhow!("deployment_has_no_proof"))
    }
    fn split(&mut self) -> Self {
        self.clone()
    }
    fn resolver(&self) -> &impl transient_crypto::proofs::Resolver {
        self
    }
}
pub(crate) fn prove_deployment(
    intent: &NativeIntent,
    parameters: &ledger::structure::LedgerParameters,
) -> Result<ProvedNativeIntent, client::Error> {
    prove_proofless_action(intent, parameters, ProoflessAction::Deployment)
}

pub(crate) fn prove_maintenance(
    intent: &NativeIntent,
    parameters: &ledger::structure::LedgerParameters,
) -> Result<ProvedNativeIntent, client::Error> {
    prove_proofless_action(intent, parameters, ProoflessAction::Maintenance)
}

#[derive(Clone, Copy)]
enum ProoflessAction {
    Deployment,
    Maintenance,
}

fn prove_proofless_action(
    intent: &NativeIntent,
    parameters: &ledger::structure::LedgerParameters,
    expected: ProoflessAction,
) -> Result<ProvedNativeIntent, client::Error> {
    use ledger::structure::ContractAction;
    let action_matches = match (expected, intent.actions.iter_deref().next()) {
        (ProoflessAction::Deployment, Some(ContractAction::Deploy(_)))
        | (ProoflessAction::Maintenance, Some(ContractAction::Maintain(_))) => true,
        _ => false,
    };
    if intent.actions.len() != 1
        || !action_matches
        || intent.dust_actions.is_some()
        || intent.guaranteed_unshielded_offer.is_some()
        || intent.fallible_unshielded_offer.is_some()
    {
        return Err(client::Error::InvalidTransaction);
    }
    // This deployment has no proof work or external awaits, including inside an async host.
    intent
        .prove(
            crate::funding::CONTRACT_SEGMENT,
            NoProof,
            &parameters.cost_model.runtime_cost_model,
        )
        .now_or_never()
        .ok_or(client::Error::InvalidTransaction)?
        .map(|(_, i)| i)
        .map_err(|_| client::Error::InvalidTransaction)
}
async fn step(
    mut state: State,
    command: Command,
    adapter: Adapter,
) -> (State, Result<Json, client::Error>) {
    let result = async {
        match command {
            Command::Prepare => {
                let contract = match &state.contract {
                    Some(Contract::Proved(i))
                    | Some(Contract::Deployment { intent: i, .. })
                    | Some(Contract::Maintenance { intent: i, .. }) => i,
                    _ => return Err(client::Error::State),
                };
                let bound = BoundTransaction::prepare(
                    contract,
                    state.policy.clone(),
                    &adapter,
                    &adapter,
                    &adapter,
                )
                .await?;
                let ctx = recovery_host_context(&state.context)?;
                state.attempt = Some(SubmissionAttempt::new(
                    bound,
                    &ctx.attempt_id,
                    state.runtime.as_mut().ok_or(client::Error::State)?,
                )?);
            }
            Command::Reload => {
                let ctx = recovery_host_context(&state.context)?;
                let attempt = SubmissionAttempt::recover(&adapter, &ctx.attempt_id).await?;
                if attempt.transaction().policy() != &state.policy {
                    return Err(client::Error::Network);
                }
                state.runtime = Some(restored_runtime(&state.context, &attempt)?);
                state.receipt = None;
                state.attempt = Some(attempt);
                state.contract = None;
                state.durable = true;
            }
            command => {
                let attempt = state.attempt.as_mut().ok_or(client::Error::State)?;
                let runtime = state.runtime.as_mut().ok_or(client::Error::State)?;
                match command {
                    Command::Submit => {
                        attempt.submit_once(runtime, &adapter, &adapter).await?;
                        state.durable = true;
                    }
                    Command::Observe => {
                        let terminal =
                            matches!(attempt.phase()?, Phase::Committed | Phase::Conflicted);
                        if let Some(receipt) =
                            attempt.observe_once(runtime, &adapter, &adapter).await?
                        {
                            if let ObservedReceipt::Full(receipt) = receipt {
                                state.receipt = Some(receipt);
                            }
                            if !terminal {
                                state.durable = true
                            }
                        }
                    }
                    Command::Commit => {
                        attempt.commit_private(runtime, &adapter, 1).await?;
                        state.durable = true;
                    }
                    Command::Cancel => {
                        attempt.cancel(runtime, &adapter).await?;
                        state.durable = true;
                        state.cancelled = true;
                    }
                    Command::Deadline => {
                        let phase = attempt.phase()?;
                        if phase == Phase::Cancelled {
                            attempt.cancel(runtime, &adapter).await?;
                            state.durable = true;
                            return Err(client::Error::Deadline);
                        }
                        let result = attempt.deadline(runtime, &adapter).await;
                        if result == Err(client::Error::Deadline)
                            && matches!(
                                phase,
                                Phase::Prepared | Phase::Submitted | Phase::Uncertain
                            )
                        {
                            state.durable = true;
                        }
                        result?;
                    }
                    _ => return Err(client::Error::State),
                }
            }
        }
        Ok(json!({"status":"step_done"}))
    }
    .await;
    if result.is_err() && !(command == Command::Deadline && result == Err(client::Error::Deadline))
    {
        state.durable = false;
    }
    (state, result)
}
type Task = Pin<Box<dyn Future<Output = (State, Result<Json, client::Error>)> + Send + 'static>>;
pub(crate) struct Driver {
    state: Option<State>,
    task: Option<Task>,
    recovery_binding: Option<ContractStateBinding>,
    adapter: Adapter,
    mode: Option<Command>,
    last: Json,
    cancel_prepare: bool,
}
impl Driver {
    fn validate_descriptor(descriptor: &Descriptor) -> Result<(), client::Error> {
        descriptor.policy.validate()?;
        if descriptor.abi_version != 1 || !descriptor.capabilities.validate() {
            return Err(client::Error::Policy);
        }
        Ok(())
    }

    pub fn start(
        descriptor: Descriptor,
        setup_bytes: &[u8],
        contract: Contract,
    ) -> Result<Self, client::Error> {
        Self::validate_descriptor(&descriptor)?;
        let setup: Setup =
            serde_json::from_slice(setup_bytes).map_err(|_| client::Error::Identity)?;
        let raw: Json = serde_json::from_slice(setup_bytes).map_err(|_| client::Error::Identity)?;
        let context = Zeroizing::new(
            serde_json::to_vec(&raw["hostContext"]).map_err(|_| client::Error::Identity)?,
        );
        let (target, entry) = address(&contract)?;
        let mut runtime = host::Runtime::new(setup.host_context, &BTreeMap::new(), target, entry)
            .map_err(|_| client::Error::Identity)?;
        for stage in setup.stages {
            runtime.stage(stage).map_err(|_| client::Error::Identity)?;
        }
        runtime
            .execution_finished(true)
            .map_err(|_| client::Error::State)?;
        let policy = descriptor.policy.clone();
        Ok(Self::new(
            descriptor,
            State {
                policy,
                contract: Some(contract),
                runtime: Some(runtime),
                attempt: None,
                context,
                receipt: None,
                state_binding: None,
                context_issued: false,
                durable: false,
                cancelled: false,
            },
        ))
    }

    pub(crate) fn start_with_state_binding(
        descriptor: Descriptor,
        setup_bytes: &[u8],
        contract: Contract,
        binding: ContractStateBinding,
    ) -> Result<Self, client::Error> {
        Self::validate_state_binding(&contract, &binding)?;
        let mut driver = Self::start(descriptor, setup_bytes, contract)?;
        driver
            .state
            .as_mut()
            .ok_or(client::Error::State)?
            .state_binding = Some(binding);
        Ok(driver)
    }

    pub(crate) fn start_with_runtime(
        descriptor: Descriptor,
        runtime: &mut Option<host::Runtime>,
        contract: Contract,
    ) -> Result<Self, client::Error> {
        Self::validate_descriptor(&descriptor)?;
        let (target, entrypoint) = address(&contract)?;
        let source_runtime = runtime.as_ref().ok_or(client::Error::State)?;
        if !source_runtime.has_target(&target, &entrypoint) {
            return Err(client::Error::Identity);
        }
        let context_value = source_runtime
            .recovery_context()
            .map_err(|_| client::Error::Identity)?;
        let context = Zeroizing::new(
            serde_json::to_vec(&context_value).map_err(|_| client::Error::Identity)?,
        );
        let runtime = runtime.take().ok_or(client::Error::State)?;
        let policy = descriptor.policy.clone();
        Ok(Self::new(
            descriptor,
            State {
                policy,
                contract: Some(contract),
                runtime: Some(runtime),
                attempt: None,
                context,
                receipt: None,
                state_binding: None,
                context_issued: false,
                durable: false,
                cancelled: false,
            },
        ))
    }

    pub(crate) fn start_with_runtime_and_binding(
        descriptor: Descriptor,
        runtime: &mut Option<host::Runtime>,
        contract: Contract,
        binding: ContractStateBinding,
    ) -> Result<Self, client::Error> {
        Self::validate_state_binding(&contract, &binding)?;
        let mut driver = Self::start_with_runtime(descriptor, runtime, contract)?;
        driver
            .state
            .as_mut()
            .ok_or(client::Error::State)?
            .state_binding = Some(binding);
        Ok(driver)
    }

    fn validate_state_binding(
        contract: &Contract,
        binding: &ContractStateBinding,
    ) -> Result<(), client::Error> {
        use ledger::structure::ContractAction;

        let (address, operation) = address(contract)?;
        let deployment = matches!(contract, Contract::Deployment { .. });
        let explicit_action = match contract {
            Contract::Proved(intent) => {
                matches!(
                    intent.actions.iter_deref().next(),
                    Some(ContractAction::Call(_))
                )
            }
            Contract::Deployment { intent, .. } => {
                matches!(
                    intent.actions.iter_deref().next(),
                    Some(ContractAction::Deploy(_))
                )
            }
            Contract::Maintenance { intent, .. } => matches!(
                intent.actions.iter_deref().next(),
                Some(ContractAction::Maintain(_))
            ),
        };
        require(
            explicit_action
                && binding.matches_target(&address, &operation)
                && binding.matches_event(deployment)
                && if deployment {
                    binding.current_state_bytes().is_none()
                } else {
                    binding.current_state_bytes().is_some()
                },
            client::Error::Identity,
        )
    }
    fn new(descriptor: Descriptor, mut state: State) -> Self {
        state.policy = descriptor.policy.clone();
        Self {
            state: Some(state),
            task: None,
            recovery_binding: None,
            adapter: Adapter {
                mailbox: Arc::new(Mutex::new(Mailbox {
                    pending: None,
                    count: 0,
                })),
                capabilities: descriptor.capabilities,
                policy: descriptor.policy,
            },
            mode: None,
            last: json!({"status":"ready"}),
            cancel_prepare: false,
        }
    }
    pub fn recover(descriptor: Descriptor, context: &[u8]) -> Result<Self, client::Error> {
        descriptor.policy.validate()?;
        if descriptor.abi_version != 1 || !descriptor.capabilities.validate() {
            return Err(client::Error::Policy);
        }
        recovery_host_context(context)?;
        let policy = descriptor.policy.clone();
        let mut driver = Self::new(
            descriptor,
            State {
                policy,
                contract: None,
                runtime: None,
                attempt: None,
                context: Zeroizing::new(context.to_vec()),
                receipt: None,
                state_binding: None,
                context_issued: false,
                durable: false,
                cancelled: false,
            },
        );
        driver.command(Command::Reload)?;
        Ok(driver)
    }

    /// Recover the journaled attempt first, then restore its privately validated source binding.
    /// Current-state admission still waits for the recovered attempt's receipt and journal CAS.
    pub(crate) fn recover_with_state_binding(
        descriptor: Descriptor,
        context: &[u8],
        binding: ContractStateBinding,
    ) -> Result<Self, client::Error> {
        let mut driver = Self::recover(descriptor, context)?;
        require(
            driver.mode == Some(Command::Reload)
                && driver.task.is_some()
                && driver.recovery_binding.is_none(),
            client::Error::State,
        )?;
        driver.recovery_binding = Some(binding);
        Ok(driver)
    }

    pub fn command(&mut self, command: Command) -> Result<(), client::Error> {
        if self.task.is_some() {
            if command == Command::Cancel && self.mode == Some(Command::Prepare) {
                self.cancel_prepare = true;
                if let Some(q) = self.request() {
                    self.complete(q.id, ServiceReply::Failure)?;
                }
                return Ok(());
            }
            return Err(client::Error::State);
        }
        let s = self.state.as_mut().ok_or(client::Error::State)?;
        if s.cancelled {
            return Err(client::Error::State);
        }
        if command == Command::Cancel
            && s.attempt
                .as_ref()
                .is_some_and(|a| !matches!(a.phase(), Ok(Phase::Prepared | Phase::Cancelled)))
        {
            return Err(client::Error::CancellationAfterBroadcast);
        }
        if command == Command::Prepare && s.contract.is_none() {
            return Err(client::Error::State);
        }
        if command == Command::Cancel && s.attempt.is_none() {
            s.runtime
                .as_mut()
                .ok_or(client::Error::State)?
                .cancel()
                .map_err(|_| client::Error::State)?;
            s.cancelled = true;
            self.last = json!({"status":"cancelled"});
            return Ok(());
        }
        if command == Command::Prepare && s.attempt.is_some() {
            return Err(client::Error::State);
        }
        if command != Command::Prepare && command != Command::Reload && s.attempt.is_none() {
            return Err(client::Error::State);
        }
        if let Some(attempt) = &s.attempt {
            let phase = attempt.phase()?;
            let allowed = match command {
                Command::Prepare => false,
                Command::Submit => {
                    matches!(phase, Phase::Prepared | Phase::Submitted | Phase::Uncertain)
                }
                Command::Observe => matches!(
                    phase,
                    Phase::Submitted
                        | Phase::Uncertain
                        | Phase::AwaitingCas
                        | Phase::PartiallyAccepted
                        | Phase::Committed
                        | Phase::Conflicted
                ),
                Command::Commit => matches!(
                    phase,
                    Phase::AwaitingCas | Phase::Committed | Phase::Conflicted
                ),
                Command::Cancel => matches!(phase, Phase::Prepared | Phase::Cancelled),
                Command::Deadline => matches!(
                    phase,
                    Phase::Prepared | Phase::Submitted | Phase::Uncertain | Phase::Cancelled
                ),
                Command::Reload => true,
            };
            if !allowed {
                return Err(client::Error::State);
            }
        }
        let state = self.state.take().ok_or(client::Error::State)?;
        self.mode = Some(command);
        self.task = Some(Box::pin(step(state, command, self.adapter.clone())));
        Ok(())
    }
    pub fn poll(&mut self) -> Result<(), client::Error> {
        for _ in 0..3 {
            if self.cancel_prepare {
                if let Some(q) = self.request() {
                    self.complete(q.id, ServiceReply::Failure)?;
                }
            }
            let Some(task) = self.task.as_mut() else {
                break;
            };
            let waker = noop_waker();
            let mut context = Context::from_waker(&waker);
            match task.as_mut().poll(&mut context) {
                Poll::Ready((mut state, result)) => {
                    if self.mode == Some(Command::Reload) {
                        if let Some(binding) = self.recovery_binding.take() {
                            state.state_binding = Some(binding);
                        }
                    }
                    if self.cancel_prepare {
                        self.cancel_prepare = false;
                        // The last signing reply can win the race with cancellation.
                        // A newly bound attempt must complete SDK cancellation durably.
                        if state.attempt.is_some() {
                            self.mode = Some(Command::Cancel);
                            self.task =
                                Some(Box::pin(step(state, Command::Cancel, self.adapter.clone())));
                            continue;
                        }
                        if let Some(runtime) = state.runtime.as_mut() {
                            if runtime.cancel().is_err() {
                                self.last =
                                    json!({"status":"step_error","error":"noctium_client_State"});
                                self.state = Some(state);
                                self.task = None;
                                self.mode = None;
                                break;
                            }
                        }
                        state.cancelled = true;
                        self.last = json!({"status":"cancelled","phase":"Cancelled"});
                    } else {
                        self.last = match result {
                            Ok(value) => value,
                            Err(error) => json!({"status":"step_error","error":error.to_string()}),
                        };
                    }
                    self.state = Some(state);
                    self.task = None;
                    self.mode = None;
                    break;
                }
                Poll::Pending => {
                    if !self.cancel_prepare {
                        break;
                    }
                }
            }
        }
        Ok(())
    }
    pub fn request(&self) -> Option<Arc<Request>> {
        self.adapter
            .mailbox
            .lock()
            .ok()?
            .pending
            .as_ref()
            .map(|p| p.request.clone())
    }
    pub fn complete(&self, id: u64, reply: ServiceReply) -> Result<(), client::Error> {
        let mut m = self
            .adapter
            .mailbox
            .lock()
            .map_err(|_| client::Error::State)?;
        let p = m.pending.as_ref().ok_or(client::Error::State)?;
        if p.request.id != id || !p.request.accepts(&reply) {
            return Err(client::Error::Identity);
        }
        let p = m.pending.take().ok_or(client::Error::State)?;
        p.sender.send(reply).map_err(|_| client::Error::State)
    }
    pub fn status(&self) -> Json {
        if let Some(request) = self.request() {
            return request.metadata();
        }
        let mut status = self.last.clone();
        status["abiVersion"] = json!(1);
        status["profile"] = json!(crate::profile::NAME);
        status["busy"] = json!(self.task.is_some());
        if let Some(state) = &self.state {
            if let Some(attempt) = &state.attempt {
                let t = attempt.transaction();
                status["phase"] = json!(format!("{:?}", attempt.phase().unwrap_or(Phase::Failed)));
                status["attemptId"] = json!(attempt.record().identity().attempt_id);
                status["transactionId"] = json!(t.transaction_id());
                status["contractAddress"] = json!(t.contract_address());
                status["event"] = json!(format!("{:?}", t.event()));
                status["durableAcknowledged"] = json!(state.durable);
                if let Some(cas) = attempt.record().cas_receipt() {
                    status["privateCommitted"] = json!(cas.committed);
                    status["privateRevision"] = json!(cas.revision);
                    status["privateAcknowledged"] =
                        json!(state.runtime.as_ref().is_some_and(|runtime| {
                            runtime.matches_cas(cas.committed, &cas.revision)
                        }));
                }
            } else if let Some(contract) = &state.contract {
                if let Ok((a, e)) = address(contract) {
                    status["contractAddress"] = json!(a);
                    status["entrypoint"] = json!(e)
                }
            }
            if state.cancelled {
                status["phase"] = json!("Cancelled")
            }
            let partial = state
                .attempt
                .as_ref()
                .and_then(|attempt| attempt.record().partial_receipt());
            if let Some(receipt) = state
                .receipt
                .as_ref()
                .or(partial.map(|value| &value.receipt))
            {
                status["receipt"] = json!({"blockHash":receipt.block_hash,"height":receipt.height.to_string(),"finalizedHash":receipt.finalized_hash,"finalizedHeight":receipt.finalized_height.to_string(),"extrinsicHash":receipt.extrinsic_hash,"extrinsicIndex":receipt.extrinsic_index,"transactionId":receipt.transaction_id,"intentId":receipt.intent_id,"contractAddress":receipt.contract_address,"event":format!("{:?}",receipt.event),"contractStateBytes":receipt.contract_state.len(),"contractStateSha256":crate::artifacts::digest(&receipt.contract_state)})
            }
            if let Some(partial) = partial {
                status["receipt"]["outcome"] = json!("partialSuccess");
                status["receipt"]["segments"] = json!(partial.segments);
                status["receipt"]["entrypointHex"] = json!(hex::encode(&partial.entrypoint));
            }
        }
        status
    }
    pub fn detachable(&self) -> bool {
        if self.task.is_some() {
            return false;
        }
        self.state
            .as_ref()
            .is_none_or(|s| s.attempt.is_none() || s.durable)
    }
    pub fn recovery_context(&self) -> Option<&[u8]> {
        self.state.as_ref().map(|state| state.context.as_slice())
    }
    pub fn transaction(&self) -> Result<Vec<u8>, client::Error> {
        Ok(self
            .state
            .as_ref()
            .and_then(|s| s.attempt.as_ref())
            .ok_or(client::Error::State)?
            .transaction()
            .bytes()
            .to_vec())
    }
    pub fn receipt_state(&self) -> Result<Vec<u8>, client::Error> {
        let state = self.state.as_ref().ok_or(client::Error::State)?;
        let receipt = state
            .receipt
            .as_ref()
            .or_else(|| {
                let partial = state.attempt.as_ref()?.record().partial_receipt()?;
                Some(&partial.receipt)
            })
            .ok_or(client::Error::State)?;
        Ok(receipt.contract_state.clone())
    }

    pub fn current_state_context(&mut self) -> Result<CurrentStateContext, client::Error> {
        let state = self.state.as_mut().ok_or(client::Error::State)?;
        require(!state.context_issued, client::Error::State)?;
        let binding = state.state_binding.as_ref().ok_or(client::Error::State)?;
        let attempt = state.attempt.as_ref().ok_or(client::Error::State)?;
        let receipt = state.receipt.as_ref().ok_or(client::Error::Receipt)?;
        let transaction = attempt.transaction();
        transaction.check_receipt(receipt)?;
        require(
            state.durable && attempt.phase()? == Phase::Committed,
            client::Error::State,
        )?;
        let cas = attempt.record().cas_receipt().ok_or(client::Error::State)?;
        require(
            cas.committed && &cas.identity == attempt.record().identity(),
            client::Error::Receipt,
        )?;
        if let Some(runtime) = &state.runtime {
            require(
                runtime.matches_cas(cas.committed, &cas.revision),
                client::Error::Receipt,
            )?;
        } else {
            return Err(client::Error::State);
        }
        let deployment = match transaction.event() {
            client::ContractEvent::Deploy => true,
            client::ContractEvent::Call | client::ContractEvent::Maintain => false,
        };
        let journal_identity = attempt.record().identity();
        let checkpoint =
            serde_json::to_vec(&(receipt, journal_identity, cas, binding.context_identity()))
                .map_err(|_| client::Error::Identity)?;
        let context = binding
            .admit_committed_state_on_chain(
                &receipt.contract_state,
                transaction.expected_state(),
                &crate::artifacts::digest(&checkpoint),
                deployment,
                &receipt.chain,
            )
            .map_err(|_| client::Error::Receipt)?;
        state.context_issued = true;
        Ok(context)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use base_crypto::{hash::HashOutput, time::Timestamp};
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use storage::arena::Sp;

    #[test]
    fn deployment_conversion_is_ready_inside_an_executor() {
        use ledger::structure::{ContractAction, ContractDeploy, Intent};
        let mut rng = StdRng::from_seed([23; 32]);
        let deployment = ContractDeploy {
            initial_state: onchain_runtime::state::ContractState::<crate::Db>::default(),
            nonce: HashOutput([4; 32]),
        };
        let address = deployment.address();
        let intent: NativeIntent = Intent {
            actions: vec![ContractAction::Deploy(Sp::new(deployment))].into(),
            guaranteed_unshielded_offer: None,
            fallible_unshielded_offer: None,
            dust_actions: None,
            binding_commitment: rng.r#gen(),
            ttl: Timestamp::from_secs(2_000_000_000),
        };
        let converted = futures::executor::block_on(async {
            prove_deployment(&intent, &ledger::structure::INITIAL_PARAMETERS)
        })
        .unwrap();
        let Some(ContractAction::Deploy(actual)) = converted.actions.iter_deref().next() else {
            panic!("expected native deployment")
        };
        assert_eq!(actual.address(), address);
        assert_eq!(converted.ttl, intent.ttl);
        assert_eq!(converted.binding_commitment, intent.binding_commitment);
    }

    fn witness_test_contract() -> (Contract, String) {
        use ledger::structure::{ContractAction, ContractDeploy, Intent};
        let mut rng = StdRng::from_seed([19; 32]);
        let deployment = ContractDeploy {
            initial_state: onchain_runtime::state::ContractState::<crate::Db>::default(),
            nonce: HashOutput([3; 32]),
        };
        let address = hex::encode(deployment.address().0.0);
        let intent: ProvedNativeIntent = Intent {
            actions: vec![ContractAction::Deploy(Sp::new(deployment))].into(),
            guaranteed_unshielded_offer: None,
            fallible_unshielded_offer: None,
            dust_actions: None,
            binding_commitment: rng.r#gen(),
            ttl: Timestamp::from_secs(2_000_000_000),
        };
        (
            Contract::Deployment {
                intent,
                entrypoint: "claim".into(),
            },
            address,
        )
    }

    fn witness_test_runtime(target: &str) -> host::Runtime {
        let context: host::Context = serde_json::from_slice(include_bytes!(
            "../tests/fixtures/private-state/context.json"
        ))
        .unwrap();
        let private_inputs = BTreeMap::from([("left".into(), "UIntRange<256>".into())]);
        let mut runtime =
            host::Runtime::new(context, &private_inputs, target.into(), "claim".into()).unwrap();
        runtime
            .stage(host::Stage {
                abi_version: 1,
                operation: host::STAGE.into(),
                capability: "store".into(),
                key: "claims/receipt".into(),
                ty: "UIntRange<256>".into(),
                value: json!("5"),
            })
            .unwrap();
        runtime.execution_finished(true).unwrap();
        runtime
    }

    fn witness_test_descriptor() -> Descriptor {
        Descriptor {
            abi_version: 1,
            policy: NetworkPolicy {
                network_id: "undeployed".into(),
                genesis: "8".repeat(64),
                spec_version: 1,
                transaction_version: 4,
                profile: crate::profile::NAME.into(),
                max_dust: 1,
            },
            capabilities: Capabilities {
                chain: "chain".into(),
                funding: "wallet".into(),
                signing: "signer".into(),
                journal: "store".into(),
            },
        }
    }

    #[test]
    fn witness_driver_rejects_target_mismatch_without_consuming_source_runtime() {
        let (contract, address) = witness_test_contract();
        let mut source = Some(witness_test_runtime(&"b".repeat(64)));
        assert!(
            Driver::start_with_runtime(witness_test_descriptor(), &mut source, contract,).is_err()
        );
        assert!(source.is_some());

        let (contract, _) = witness_test_contract();
        let mut source = Some(witness_test_runtime(&address));
        let mut invalid_descriptor = witness_test_descriptor();
        invalid_descriptor.abi_version = 2;
        assert!(Driver::start_with_runtime(invalid_descriptor, &mut source, contract).is_err());
        assert!(source.is_some());

        let (contract, _) = witness_test_contract();
        let mut driver =
            Driver::start_with_runtime(witness_test_descriptor(), &mut source, contract).unwrap();
        assert!(source.is_none());
        let recovery: Json =
            serde_json::from_slice(&driver.state.as_ref().unwrap().context).unwrap();
        assert_eq!(recovery["recoveryVersion"], 1);
        assert_eq!(recovery["target"], address);
        assert_eq!(recovery["entrypoint"], "claim");
        let attempt_id = recovery["context"]["attemptId"]
            .as_str()
            .unwrap()
            .to_owned();
        let runtime = driver.state.as_mut().unwrap().runtime.as_mut().unwrap();
        runtime
            .notify(host::Notice {
                abi_version: 1,
                event: "bind".into(),
                attempt_id: attempt_id.clone(),
                transaction_id: "c".repeat(64),
            })
            .unwrap();
        let journal = runtime.private_journal().unwrap();
        assert_eq!(journal["transactionId"], "c".repeat(64));
        assert_eq!(journal["contractAddress"], address);
        assert_eq!(journal["writes"]["claims/receipt"]["value"], "5");
        assert!(
            runtime
                .notify(host::Notice {
                    abi_version: 1,
                    event: "bind".into(),
                    attempt_id: attempt_id.clone(),
                    transaction_id: "d".repeat(64),
                })
                .is_err()
        );
        assert_eq!(runtime.private_journal().unwrap(), journal);

        for event in ["persisted", "submitted", "accepted"] {
            let request_cas = runtime
                .notify(host::Notice {
                    abi_version: 1,
                    event: event.into(),
                    attempt_id: attempt_id.clone(),
                    transaction_id: "c".repeat(64),
                })
                .unwrap();
            assert_eq!(request_cas, event == "accepted");
        }
        runtime.begin_cas(17).unwrap();
        let cas_request = runtime.private_arguments().unwrap();
        assert_eq!(cas_request["journal"]["transactionId"], "c".repeat(64));
        assert_eq!(
            cas_request["journal"]["writes"]["claims/receipt"]["value"],
            "5"
        );
        runtime
            .finish_cas(
                17,
                Some(host::CAS),
                Some("store"),
                Some(host::CAS_SCHEMA),
                json!({
                    "attemptId": attempt_id,
                    "transactionId": "c".repeat(64),
                    "journalDigest": journal["journalDigest"],
                    "outcome": "committed",
                    "baseRevision": journal["baseRevision"],
                    "revision": "r1"
                }),
            )
            .unwrap();
        assert!(runtime.private_journal().is_err());
    }

    #[test]
    fn typed_recovery_envelope_keeps_the_original_host_attempt_identity() {
        let context: Json = serde_json::from_slice(include_bytes!(
            "../tests/fixtures/private-state/context.json"
        ))
        .unwrap();
        let envelope = json!({
            "recoveryVersion": 1,
            "context": context,
            "typed": true,
            "typedInputs": ["lookup"],
            "typedSchemas": [],
            "target": "a".repeat(64),
            "entrypoint": "claim"
        });
        let bytes = serde_json::to_vec(&envelope).unwrap();
        let restored = recovery_host_context(&bytes).unwrap();
        assert_eq!(restored.attempt_id, "a".repeat(64));
        assert_eq!(restored.namespace, "wallet_A");
        assert_eq!(restored.base_revision, "r0");
    }

    #[test]
    fn recover_accepts_typed_witness_context_envelope() {
        let context: Json = serde_json::from_slice(include_bytes!(
            "../tests/fixtures/private-state/context.json"
        ))
        .unwrap();
        let envelope = json!({
            "recoveryVersion": 1,
            "context": context,
            "typed": true,
            "typedInputs": ["lookup"],
            "typedSchemas": [],
            "target": "a".repeat(64),
            "entrypoint": "claim"
        });
        let bytes = serde_json::to_vec(&envelope).unwrap();
        let driver = Driver::recover(witness_test_descriptor(), &bytes).unwrap();
        assert!(driver.task.is_some());
    }

    #[test]
    fn new_wire_identities_and_budgets_are_lossless_decimal_strings() {
        let policy = NetworkPolicy {
            network_id: "undeployed".into(),
            genesis: "8".repeat(64),
            spec_version: 1,
            transaction_version: 4,
            profile: crate::profile::NAME.into(),
            max_dust: 1,
        };
        let request = Request {
            id: 9_007_199_254_740_993,
            operation: "chain.snapshot.v1",
            capability: "chain".into(),
            schema: "native.snapshot.v1",
            policy,
            data: RequestData::Snapshot,
        };
        assert_eq!(request.metadata()["requestId"], "9007199254740993");
        let wire = json!({"abiVersion":1,"policy":{"networkId":"undeployed","genesis":"8".repeat(64),"specVersion":1,"transactionVersion":4,"profile":crate::profile::NAME,"maxDust":"340282366920938463463374607431768211455"},"capabilities":{"chain":"chain","funding":"wallet","signing":"signer","journal":"store"}});
        let descriptor: Descriptor = serde_json::from_value(wire.clone()).unwrap();
        assert_eq!(descriptor.policy.max_dust, u128::MAX);
        for value in [
            json!(1),
            json!("01"),
            json!("-1"),
            json!("340282366920938463463374607431768211456"),
        ] {
            let mut bad = wire.clone();
            bad["policy"]["maxDust"] = value;
            assert!(serde_json::from_value::<Descriptor>(bad).is_err());
        }
    }
    #[test]
    fn cancellation_racing_completed_preparation_retries_undurable_terminal_record() {
        let (attempt, runtime) = crate::client::tests::prepared_driver_fixture();
        let policy = attempt.transaction().policy().clone();
        let descriptor = Descriptor {
            abi_version: 1,
            policy: policy.clone(),
            capabilities: Capabilities {
                chain: "chain".into(),
                funding: "wallet".into(),
                signing: "signer".into(),
                journal: "store".into(),
            },
        };
        let state = State {
            policy,
            contract: None,
            runtime: Some(runtime),
            attempt: Some(attempt),
            context: Zeroizing::new(Vec::new()),
            receipt: None,
            state_binding: None,
            context_issued: false,
            durable: false,
            cancelled: false,
        };
        let mut driver = Driver::new(descriptor, state);
        let state = driver.state.take().unwrap();
        driver.task = Some(Box::pin(futures::future::ready((
            state,
            Ok(json!({"status":"step_done"})),
        ))));
        driver.mode = Some(Command::Prepare);
        driver.command(Command::Cancel).unwrap();
        driver.poll().unwrap();
        let request = driver.request().unwrap();
        assert!(matches!(request.data, RequestData::Persist { .. }));
        assert!(!driver.detachable());
        driver.complete(request.id, ServiceReply::Failure).unwrap();
        driver.poll().unwrap();
        assert_eq!(driver.status()["phase"], "Cancelled");
        assert_eq!(driver.status()["durableAcknowledged"], false);
        assert!(!driver.detachable());
        assert!(driver.command(Command::Submit).is_err());
        driver.command(Command::Cancel).unwrap();
        driver.poll().unwrap();
        let request = driver.request().unwrap();
        let RequestData::Persist { record, .. } = &request.data else {
            panic!("cancellation must only persist")
        };
        let ack = StoreAcknowledgement {
            identity: record.identity().clone(),
            record_sha256: crate::artifacts::digest(&record.private_bytes().unwrap()),
            revision: 1,
        };
        driver
            .complete(request.id, ServiceReply::Persisted(ack))
            .unwrap();
        driver.poll().unwrap();
        assert_eq!(driver.status()["phase"], "Cancelled");
        assert_eq!(driver.status()["durableAcknowledged"], true);
        assert!(driver.detachable());
        assert!(driver.request().is_none());
    }
}
