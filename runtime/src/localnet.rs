//! Opt-in host adapter. Every endpoint, network policy, deadline and wallet seed is explicit.
#[path = "localnet_store.rs"]
pub mod journal;
mod shielded_receive;
mod shielded_relay;
mod shielded_merge;
mod shielded_transfer;
use crate::{
    Db,
    client::{
        BoundTransaction, ChainIdentity, FinalizedReceipt, NetworkPolicy, Observation,
        PartialReceipt, Snapshot,
    },
};
use base_crypto::{
    cost_model::{FixedPoint, SyntheticCost},
    hash::HashOutput,
    time::Timestamp,
};
use coin_structure::contract::ContractAddress;
use frame_metadata::{RuntimeMetadata, RuntimeMetadataPrefixed, v16::RuntimeMetadataV16};
use ledger::{
    dust::{DustLocalState, DustSecretKey},
    semantics::{TransactionContext, TransactionResult},
    structure::{LedgerState, SystemTransaction},
    verify::WellFormedStrictness,
};
#[cfg(test)]
use ledger::events::EventDetails;
use onchain_runtime::context::BlockContext;
use parity_scale_codec::{Compact, Decode, Encode};
use reqwest::blocking::Client;
use scale_info::{PortableRegistry, TypeDef, TypeDefPrimitive};
use scale_value::{Composite, Value as ScaleValue, ValueDef};
use serde_json::{Value as Json, json};
use serialize::{Deserializable, Serializable, Tagged, tagged_deserialize};
use std::{cell::RefCell, collections::BTreeMap, io::Read, time::Duration};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    Policy,
    Transport,
    Limit,
    Response,
    Network,
    Metadata,
    State,
    Replay,
    Proof,
    Storage,
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "noctium_localnet_{self:?}")
    }
}
impl std::error::Error for Error {}

#[derive(Debug)]
pub enum WitnessPreparationError {
    Node(Error),
    Witness(crate::witness_execution::Error),
}
impl std::fmt::Display for WitnessPreparationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Node(error) => error.fmt(f),
            Self::Witness(error) => error.fmt(f),
        }
    }
}
impl std::error::Error for WitnessPreparationError {}
type Result<T> = std::result::Result<T, Error>;
fn check(value: bool, error: Error) -> Result<()> {
    if value { Ok(()) } else { Err(error) }
}
fn hex_bytes(value: &Json) -> Result<Vec<u8>> {
    hex::decode(
        value
            .as_str()
            .ok_or(Error::Response)?
            .strip_prefix("0x")
            .unwrap_or(value.as_str().ok_or(Error::Response)?),
    )
    .map_err(|_| Error::Response)
}
fn hash_text(value: &Json) -> Result<String> {
    let bytes = hex_bytes(value)?;
    check(bytes.len() == 32, Error::Response)?;
    Ok(hex::encode(bytes))
}

pub const DEVELOPMENT_GENESIS: &str =
    "823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d";

pub struct Rpc {
    client: Client,
    endpoint: reqwest::Url,
    max_response: usize,
}
/// Read-only host-selected cache. The native provider checks its pinned official hashes.
/// Synchronous mode rejects missing files and never fetches from the supplied source URL.
pub struct ProofCache {
    provider: base_crypto::data_provider::MidnightDataProvider,
}
impl ProofCache {
    pub fn new(directory: std::path::PathBuf, parameter_source: reqwest::Url) -> Result<Self> {
        check(
            matches!(parameter_source.scheme(), "http" | "https"),
            Error::Policy,
        )?;
        Ok(Self {
            provider: base_crypto::data_provider::MidnightDataProvider {
                fetch_mode: base_crypto::data_provider::FetchMode::Synchronous,
                base_url: parameter_source,
                output_mode: base_crypto::data_provider::OutputMode::Log,
                expected_data: ledger::dust::DUST_EXPECTED_FILES.to_vec(),
                dir: directory,
            },
        })
    }
    async fn read(&self, path: &str, limit: usize) -> Result<Vec<u8>> {
        let file = self
            .provider
            .get_file(path, "native cache material missing")
            .await
            .map_err(|_| Error::Proof)?;
        let mut bytes = Vec::new();
        file.take(limit as u64 + 1)
            .read_to_end(&mut bytes)
            .map_err(|_| Error::Proof)?;
        check(bytes.len() <= limit, Error::Limit)?;
        Ok(bytes)
    }
    pub async fn dust(&self) -> Result<crate::funding::DustMaterial> {
        let mut values = Vec::new();
        for suffix in ["spend.prover", "spend.verifier", "spend.bzkir"] {
            let (path, _, _) = ledger::dust::DUST_EXPECTED_FILES
                .iter()
                .find(|(path, _, _)| path.ends_with(suffix))
                .ok_or(Error::Proof)?;
            values.push(self.read(path, 16 * 1024 * 1024).await?);
        }
        crate::funding::DustMaterial::from_bytes(&values[0], &values[1], &values[2])
            .map_err(|_| Error::Proof)
    }
    pub async fn parameters(&self, k: u8) -> Result<crate::proof::TrustedParameters> {
        check((1..=20).contains(&k), Error::Proof)?;
        let bytes = self
            .read(
                &base_crypto::data_provider::MidnightDataProvider::name_k(k),
                128 * 1024 * 1024,
            )
            .await?;
        use sha2::Digest;
        let digest = hex::encode(sha2::Sha256::digest(&bytes));
        crate::proof::TrustedParameters::from_bytes(&bytes, k, &digest).map_err(|_| Error::Proof)
    }
}
impl Rpc {
    pub fn new(endpoint: &str, timeout: Duration, max_response: usize) -> Result<Self> {
        let endpoint = reqwest::Url::parse(endpoint).map_err(|_| Error::Policy)?;
        check(
            matches!(endpoint.scheme(), "http" | "https")
                && endpoint.username().is_empty()
                && endpoint.password().is_none()
                && timeout >= Duration::from_millis(1)
                && timeout <= Duration::from_secs(120)
                && (1024..=64 * 1024 * 1024).contains(&max_response),
            Error::Policy,
        )?;
        let client = Client::builder()
            .no_proxy()
            .redirect(reqwest::redirect::Policy::none())
            .timeout(timeout)
            .build()
            .map_err(|_| Error::Transport)?;
        Ok(Self {
            client,
            endpoint,
            max_response,
        })
    }
    fn send(&self, body: &Json) -> Result<Json> {
        let response = self
            .client
            .post(self.endpoint.clone())
            .json(body)
            .send()
            .map_err(|_| Error::Transport)?
            .error_for_status()
            .map_err(|_| Error::Transport)?;
        if response
            .content_length()
            .is_some_and(|len| len > self.max_response as u64)
        {
            return Err(Error::Limit);
        }
        let mut bytes = Vec::new();
        response
            .take(self.max_response as u64 + 1)
            .read_to_end(&mut bytes)
            .map_err(|_| Error::Transport)?;
        check(bytes.len() <= self.max_response, Error::Limit)?;
        serde_json::from_slice(&bytes).map_err(|_| Error::Response)
    }
    pub fn call(&self, method: &str, params: Json) -> Result<Json> {
        let response =
            self.send(&json!({"jsonrpc":"2.0","id":1,"method":method,"params":params}))?;
        check(
            response["jsonrpc"] == "2.0" && response["id"] == 1 && response.get("error").is_none(),
            Error::Response,
        )?;
        response.get("result").cloned().ok_or(Error::Response)
    }
    fn batch(&self, calls: &[(String, Json)]) -> Result<Vec<Json>> {
        check(!calls.is_empty() && calls.len() <= 128, Error::Limit)?;
        let request = calls.iter().enumerate().map(|(id, (method, params))| json!({"jsonrpc":"2.0","id":id,"method":method,"params":params})).collect::<Vec<_>>();
        let response = self.send(&Json::Array(request))?;
        let rows = response.as_array().ok_or(Error::Response)?;
        check(rows.len() == calls.len(), Error::Response)?;
        let mut out = vec![None; calls.len()];
        for row in rows {
            let id = row["id"].as_u64().ok_or(Error::Response)? as usize;
            check(
                id < out.len()
                    && out[id].is_none()
                    && row["jsonrpc"] == "2.0"
                    && row.get("error").is_none(),
                Error::Response,
            )?;
            out[id] = Some(row.get("result").cloned().ok_or(Error::Response)?);
        }
        out.into_iter()
            .map(|row| row.ok_or(Error::Response))
            .collect()
    }
    pub fn chain_identity(&self, at: &str, profile: &str) -> Result<ChainIdentity> {
        let genesis = hash_text(&self.call("chain_getBlockHash", json!([0]))?)?;
        let runtime = self.call("state_getRuntimeVersion", json!([format!("0x{at}")]))?;
        check(runtime["specName"] == "midnight", Error::Network)?;
        let network = hex_bytes(&self.call(
            "state_call",
            json!(["MidnightRuntimeApi_get_network_id", "0x", format!("0x{at}")]),
        )?)?;
        let mut reader = network.as_slice();
        let network_id = String::decode(&mut reader).map_err(|_| Error::Response)?;
        check(reader.is_empty(), Error::Response)?;
        Ok(ChainIdentity {
            network_id,
            genesis,
            spec_version: runtime["specVersion"]
                .as_u64()
                .and_then(|n| u32::try_from(n).ok())
                .ok_or(Error::Response)?,
            transaction_version: runtime["transactionVersion"]
                .as_u64()
                .and_then(|n| u32::try_from(n).ok())
                .ok_or(Error::Response)?,
            profile: profile.into(),
        })
    }
    pub fn metadata(&self, at: &str) -> Result<Metadata> {
        let negotiated = hex_bytes(&self.call(
            "state_call",
            json!([
                "Metadata_metadata_at_version",
                "0x10000000",
                format!("0x{at}")
            ]),
        )?)?;
        let mut outer = negotiated.as_slice();
        check(
            u8::decode(&mut outer).map_err(|_| Error::Metadata)? == 1,
            Error::Metadata,
        )?;
        let length = Compact::<u32>::decode(&mut outer)
            .map_err(|_| Error::Metadata)?
            .0 as usize;
        check(
            length == outer.len() && length <= 2 * 1024 * 1024,
            Error::Metadata,
        )?;
        let RuntimeMetadataPrefixed(magic, metadata) =
            RuntimeMetadataPrefixed::decode(&mut outer).map_err(|_| Error::Metadata)?;
        check(
            magic == frame_metadata::META_RESERVED && outer.is_empty(),
            Error::Metadata,
        )?;
        let RuntimeMetadata::V16(metadata) = metadata else {
            return Err(Error::Metadata);
        };
        Metadata::new(metadata)
    }
}

pub struct Metadata {
    native: RuntimeMetadataV16,
    pub pallet: u8,
    pub call: u8,
    events_type: u32,
    fingerprint: Vec<u8>,
}
impl Metadata {
    fn variants(
        registry: &PortableRegistry,
        id: u32,
    ) -> Result<&scale_info::TypeDefVariant<scale_info::form::PortableForm>> {
        let ty = registry.resolve(id).ok_or(Error::Metadata)?;
        if let TypeDef::Variant(variants) = &ty.type_def {
            Ok(variants)
        } else {
            Err(Error::Metadata)
        }
    }
    fn bytes_type(registry: &PortableRegistry, id: u32, depth: usize) -> bool {
        if depth > 8 {
            return false;
        }
        let Some(ty) = registry.resolve(id) else {
            return false;
        };
        match &ty.type_def {
            TypeDef::Sequence(sequence) => registry
                .resolve(sequence.type_param.id)
                .is_some_and(|ty| ty.type_def == TypeDef::Primitive(TypeDefPrimitive::U8)),
            TypeDef::Composite(composite) if composite.fields.len() == 1 => {
                Self::bytes_type(registry, composite.fields[0].ty.id, depth + 1)
            }
            _ => false,
        }
    }
    pub fn new(native: RuntimeMetadataV16) -> Result<Self> {
        check(native.extrinsic.versions.contains(&4), Error::Metadata)?;
        let pallet = native
            .pallets
            .iter()
            .find(|p| p.name == "Midnight")
            .ok_or(Error::Metadata)?;
        let calls = Self::variants(
            &native.types,
            pallet.calls.as_ref().ok_or(Error::Metadata)?.ty.id,
        )?;
        let call = calls
            .variants
            .iter()
            .find(|c| c.name == "send_mn_transaction")
            .ok_or(Error::Metadata)?;
        check(
            call.fields.len() == 1
                && call.fields[0].name.as_deref() == Some("midnight_tx")
                && Self::bytes_type(&native.types, call.fields[0].ty.id, 0),
            Error::Metadata,
        )?;
        let system = native
            .pallets
            .iter()
            .find(|p| p.name == "System")
            .ok_or(Error::Metadata)?;
        let events = system
            .storage
            .as_ref()
            .ok_or(Error::Metadata)?
            .entries
            .iter()
            .find(|e| e.name == "Events")
            .ok_or(Error::Metadata)?;
        let frame_metadata::v14::StorageEntryType::Plain(events_type) = &events.ty else {
            return Err(Error::Metadata);
        };
        use sha2::Digest;
        let fingerprint = sha2::Sha256::digest(native.encode()).to_vec();
        let result = Self {
            fingerprint,
            pallet: pallet.index,
            call: call.index,
            events_type: events_type.id,
            native,
        };
        result.validate_events()?;
        Ok(result)
    }
    fn validate_events(&self) -> Result<()> {
        let pallet = self
            .native
            .pallets
            .iter()
            .find(|p| p.name == "Midnight")
            .ok_or(Error::Metadata)?;
        let events = Self::variants(
            &self.native.types,
            pallet.event.as_ref().ok_or(Error::Metadata)?.ty.id,
        )?;
        for name in [
            "ContractCall",
            "ContractDeploy",
            "TxApplied",
            "TxPartialSuccess",
        ] {
            check(
                events.variants.iter().any(|v| v.name == name),
                Error::Metadata,
            )?;
        }
        Ok(())
    }
    pub fn extrinsic(&self, native_transaction: &[u8]) -> Result<Vec<u8>> {
        check(
            !native_transaction.is_empty() && native_transaction.len() <= 4 * 1024 * 1024,
            Error::Limit,
        )?;
        let mut payload = vec![4, self.pallet, self.call];
        Compact(u32::try_from(native_transaction.len()).map_err(|_| Error::Limit)?)
            .encode_to(&mut payload);
        payload.extend_from_slice(native_transaction);
        let mut out = Compact(u32::try_from(payload.len()).map_err(|_| Error::Limit)?).encode();
        out.extend(payload);
        Ok(out)
    }
    pub fn events(&self, encoded: &[u8]) -> Result<scale_value::Value<u32>> {
        check(encoded.len() <= 4 * 1024 * 1024, Error::Limit)?;
        let mut reader = encoded;
        let events =
            scale_value::scale::decode_as_type(&mut reader, self.events_type, &self.native.types)
                .map_err(|_| Error::Metadata)?;
        check(reader.is_empty(), Error::Metadata)?;
        Ok(events)
    }
    fn call_value(&self, extrinsic: &[u8]) -> Result<Option<ScaleValue<u32>>> {
        let mut reader = extrinsic;
        let len = Compact::<u32>::decode(&mut reader)
            .map_err(|_| Error::Metadata)?
            .0 as usize;
        check(len == reader.len(), Error::Metadata)?;
        let version = u8::decode(&mut reader).map_err(|_| Error::Metadata)?;
        if version & 128 != 0 {
            return Ok(None);
        }
        check(
            (version == 4 || version == 5) && self.native.extrinsic.versions.contains(&version),
            Error::Metadata,
        )?;
        let value = scale_value::scale::decode_as_type(
            &mut reader,
            self.native.extrinsic.call_ty.id,
            &self.native.types,
        )
        .map_err(|_| Error::Metadata)?;
        check(reader.is_empty(), Error::Metadata)?;
        Ok(Some(value))
    }
}

fn field<'a>(value: &'a ScaleValue<u32>, name: &str) -> Option<&'a ScaleValue<u32>> {
    let fields = match &value.value {
        ValueDef::Composite(c) => c,
        ValueDef::Variant(v) => &v.values,
        _ => return None,
    };
    if let Composite::Named(values) = fields {
        if let Some((_, value)) = values.iter().find(|(key, _)| key == name) {
            return Some(value);
        }
    }
    if fields.len() == 1 {
        field(fields.values().next()?, name)
    } else {
        None
    }
}
fn variant(value: &ScaleValue<u32>) -> Result<(&str, &Composite<u32>)> {
    match &value.value {
        ValueDef::Variant(v) => Ok((&v.name, &v.values)),
        ValueDef::Composite(c) if c.len() == 1 => {
            variant(c.values().next().ok_or(Error::Metadata)?)
        }
        _ => Err(Error::Metadata),
    }
}
fn scale_bytes(value: &ScaleValue<u32>) -> Result<Vec<u8>> {
    let ValueDef::Composite(composite) = &value.value else {
        return Err(Error::Metadata);
    };
    if composite.len() == 1
        && matches!(
            composite.values().next().map(|v| &v.value),
            Some(ValueDef::Composite(_))
        )
    {
        return scale_bytes(composite.values().next().ok_or(Error::Metadata)?);
    }
    composite
        .values()
        .map(|v| {
            v.as_u128()
                .and_then(|n| u8::try_from(n).ok())
                .ok_or(Error::Metadata)
        })
        .collect()
}
fn phase(value: &ScaleValue<u32>) -> Result<u32> {
    let (name, values) = variant(value)?;
    match name {
        "ApplyExtrinsic" => values
            .values()
            .next()
            .and_then(ScaleValue::as_u128)
            .and_then(|n| u32::try_from(n).ok())
            .ok_or(Error::Metadata),
        "Initialization" => Ok(0),
        "Finalization" => Ok(u32::MAX),
        _ => Err(Error::Metadata),
    }
}
fn native_decode<T: Deserializable + Tagged>(bytes: &[u8]) -> Result<T> {
    tagged_deserialize(bytes).map_err(|_| Error::State)
}
fn native_bytes<T: Serializable>(value: &T) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    Serializable::serialize(value, &mut bytes).map_err(|_| Error::State)?;
    Ok(bytes)
}

enum ReplayTransaction {
    Native(Vec<u8>),
    System(Vec<u8>),
}
#[derive(Clone)]
struct ReplayCache {
    state: LedgerState<Db>,
    dust: DustLocalState<Db>,
    height: u64,
    hash: String,
    block: BlockContext,
}
struct PartialReplay<'a> {
    transaction: &'a [u8],
    address: ContractAddress,
    partial: bool,
    result: Option<(BTreeMap<u16, bool>, Vec<u8>)>,
    #[cfg(test)]
    logs: Option<Vec<FinalizedContractLog>>,
}
#[cfg(test)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct FinalizedContractLog {
    address: ContractAddress,
    entry_point: onchain_runtime::state::EntryPointBuf,
    item: onchain_runtime::ops::VersionedLogItem<Db>,
}
/// Development-node trust is explicit: finalized RPC history is replayed locally and
/// the resulting native ledger root must match the finalized runtime API root.
pub struct Node {
    rpc: Rpc,
    policy: NetworkPolicy,
    metadata: Metadata,
    runtime_code: String,
    cache: RefCell<Option<ReplayCache>>,
    dust_secret: RefCell<Option<DustSecretKey>>,
    max_replay_blocks: u64,
}
pub struct FinalizedContractState {
    pub chain: ChainIdentity,
    pub block_hash: String,
    pub height: u64,
    pub bytes: Vec<u8>,
}

impl Node {
    pub fn connect(
        endpoint: &str,
        policy: NetworkPolicy,
        timeout: Duration,
        max_response: usize,
        max_replay_blocks: u64,
    ) -> Result<Self> {
        policy.validate().map_err(|_| Error::Policy)?;
        check((1..=100_000).contains(&max_replay_blocks), Error::Policy)?;
        let rpc = Rpc::new(endpoint, timeout, max_response)?;
        check(
            matches!(
                rpc.endpoint.host_str(),
                Some("127.0.0.1" | "localhost" | "[::1]" | "::1")
            ),
            Error::Policy,
        )?;
        let at = hash_text(&rpc.call("chain_getFinalizedHead", json!([]))?)?;
        policy
            .check(&rpc.chain_identity(&at, &policy.profile)?)
            .map_err(|_| Error::Network)?;
        let metadata = rpc.metadata(&at)?;
        let runtime_code = hash_text(&rpc.call(
            "state_getStorageHash",
            json!(["0x3a636f6465", format!("0x{at}")]),
        )?)?;
        Ok(Self {
            rpc,
            policy,
            metadata,
            runtime_code,
            cache: RefCell::new(None),
            dust_secret: RefCell::new(None),
            max_replay_blocks,
        })
    }
    fn check_runtime(&self, at: &str) -> Result<()> {
        let code = hash_text(&self.rpc.call(
            "state_getStorageHash",
            json!(["0x3a636f6465", format!("0x{at}")]),
        )?)?;
        check(code == self.runtime_code, Error::Metadata)?;
        check(
            self.rpc.metadata(at)?.fingerprint == self.metadata.fingerprint,
            Error::Metadata,
        )
    }
    /// Public runtime identity, distinct from the selected contract compiler profile.
    pub fn runtime_fingerprint(&self) -> (String, String) {
        (
            self.runtime_code.clone(),
            hex::encode(&self.metadata.fingerprint),
        )
    }
    /// Public auditing reuses receipt verification without creating a submitting attempt.
    pub fn observe_public_reference(
        &self,
        reference: &crate::client::PublicTransactionReference,
    ) -> Result<Option<crate::client::FinalizedReceipt>> {
        self.finalized_receipt(&reference.bound_view())
    }
    /// Submit the exact bytes already sealed by the development host's approval service.
    pub async fn submit_development_reference(
        &self,
        reference: &crate::client::PublicTransactionReference,
        approved: &crate::funding::SealedTransaction,
    ) -> std::result::Result<crate::client::Submission, crate::client::HostFailure> {
        use crate::client::HostFailure;

        if self.policy.genesis != DEVELOPMENT_GENESIS {
            return Err(HostFailure);
        }
        let bound = reference.development_submission_view()?;
        let mut sealed = Vec::new();
        serialize::tagged_serialize(approved, &mut sealed).map_err(|_| HostFailure)?;
        if bound.policy() != &self.policy || bound.bytes() != sealed.as_slice() {
            return Err(HostFailure);
        }
        crate::client::ChainAdapter::submit(self, &bound).await
    }
    pub fn finalized_contract_state(&self, address: &str) -> Result<FinalizedContractState> {
        check(
            address.len() == 64 && hex::decode(address).is_ok_and(|v| v.len() == 32),
            Error::Policy,
        )?;
        let hash = hash_text(&self.rpc.call("chain_getFinalizedHead", json!([]))?)?;
        let chain = self.rpc.chain_identity(&hash, &self.policy.profile)?;
        self.policy.check(&chain).map_err(|_| Error::Network)?;
        self.check_runtime(&hash)?;
        let header = self
            .rpc
            .call("chain_getHeader", json!([format!("0x{hash}")]))?;
        let height = u64::from_str_radix(
            header["number"]
                .as_str()
                .ok_or(Error::Response)?
                .trim_start_matches("0x"),
            16,
        )
        .map_err(|_| Error::Response)?;
        let bytes = hex_bytes(&self.rpc.call(
            "midnight_contractState",
            json!([address, format!("0x{hash}")]),
        )?)?;
        check(bytes.len() <= 1024 * 1024, Error::Limit)?;
        let state: onchain_runtime::state::ContractState<Db> = native_decode(&bytes)?;
        let mut canonical = Vec::new();
        serialize::tagged_serialize(&state, &mut canonical).map_err(|_| Error::State)?;
        check(bytes == canonical, Error::State)?;
        Ok(FinalizedContractState {
            chain,
            block_hash: hash,
            height,
            bytes,
        })
    }
    /// Read exact native parameters at a block linked to the captured finalized head.
    pub fn finalized_ledger_parameters_at(&self, block_hash: &str, height: u64) -> Result<Vec<u8>> {
        check(
            block_hash.len() == 64 && hex::decode(block_hash).is_ok_and(|v| v.len() == 32),
            Error::Policy,
        )?;
        let tip = hash_text(&self.rpc.call("chain_getFinalizedHead", json!([]))?)?;
        let chain = self.rpc.chain_identity(&tip, &self.policy.profile)?;
        self.policy.check(&chain).map_err(|_| Error::Network)?;
        self.check_runtime(&tip)?;
        let header = self
            .rpc
            .call("chain_getHeader", json!([format!("0x{tip}")]))?;
        let tip_height = u64::from_str_radix(
            header["number"]
                .as_str()
                .ok_or(Error::Response)?
                .trim_start_matches("0x"),
            16,
        )
        .map_err(|_| Error::Response)?;
        check(
            height <= tip_height && tip_height - height <= self.max_replay_blocks,
            Error::Limit,
        )?;
        let mut previous = None;
        for numbers in (height..=tip_height).collect::<Vec<_>>().chunks(40) {
            let hashes = self
                .rpc
                .batch(
                    &numbers
                        .iter()
                        .map(|n| ("chain_getBlockHash".into(), json!([n])))
                        .collect::<Vec<_>>(),
                )?
                .iter()
                .map(hash_text)
                .collect::<Result<Vec<_>>>()?;
            let rows = self.rpc.batch(
                &hashes
                    .iter()
                    .flat_map(|h| {
                        [
                            ("chain_getHeader".into(), json!([format!("0x{h}")])),
                            (
                                "state_getStorageHash".into(),
                                json!(["0x3a636f6465", format!("0x{h}")]),
                            ),
                        ]
                    })
                    .collect::<Vec<_>>(),
            )?;
            for (index, rows) in rows.chunks_exact(2).enumerate() {
                if previous.is_none() {
                    check(hashes[index] == block_hash, Error::Replay)?;
                }
                check(hash_text(&rows[1])? == self.runtime_code, Error::Metadata)?;
                let number = u64::from_str_radix(
                    rows[0]["number"]
                        .as_str()
                        .ok_or(Error::Response)?
                        .trim_start_matches("0x"),
                    16,
                )
                .map_err(|_| Error::Response)?;
                check(number == numbers[index], Error::Replay)?;
                validate_parent(previous.as_deref(), &hash_text(&rows[0]["parentHash"])?)?;
                previous = Some(hashes[index].clone());
            }
        }
        validate_finalized_tip(previous.as_deref(), &tip)?;
        self.check_runtime(block_hash)?;
        let bytes = hex_bytes(&self.rpc.call(
            "state_call",
            json!([
                "MidnightRuntimeApi_get_ledger_parameters",
                "0x",
                format!("0x{block_hash}")
            ]),
        )?)?;
        let mut reader = bytes.as_slice();
        check(
            u8::decode(&mut reader).map_err(|_| Error::State)? == 0,
            Error::State,
        )?;
        let value = Vec::<u8>::decode(&mut reader).map_err(|_| Error::State)?;
        check(
            reader.is_empty() && value.len() <= 1024 * 1024,
            Error::State,
        )?;
        let native: ledger::structure::LedgerParameters = native_decode(&value)?;
        let mut canonical = Vec::new();
        serialize::tagged_serialize(&native, &mut canonical).map_err(|_| Error::State)?;
        check(canonical == value, Error::State)?;
        Ok(value)
    }
    /// Attach only before the first sync. The seed never leaves this host adapter.
    pub fn attach_dust_seed(&self, root_seed: &[u8]) -> Result<()> {
        check(
            self.cache.borrow().is_none()
                && self.dust_secret.borrow().is_none()
                && matches!(root_seed.len(), 16 | 32),
            Error::Policy,
        )?;
        let path = "m/44'/2400'/0'/2/0".parse().map_err(|_| Error::Policy)?;
        let private = bip32::XPrv::derive_from_path(root_seed, &path).map_err(|_| Error::Policy)?;
        let derived = zeroize::Zeroizing::new(<[u8; 32]>::from(private.private_key().to_bytes()));
        *self.dust_secret.borrow_mut() = Some(DustSecretKey::derive_secret_key(&derived));
        Ok(())
    }
    fn transactions(
        &self,
        extrinsics: &[Json],
        events: Option<&ScaleValue<u32>>,
        genesis: bool,
    ) -> Result<(Timestamp, Vec<ReplayTransaction>)> {
        let mut timestamp = None;
        let mut transactions = Vec::new();
        for (index, encoded) in extrinsics.iter().enumerate() {
            let Some(call) = self.metadata.call_value(&hex_bytes(encoded)?)? else {
                continue;
            };
            let (pallet, values) = variant(&call)?;
            let nested = values.values().next().ok_or(Error::Metadata)?;
            let (name, _) = variant(nested)?;
            match (pallet, name) {
                ("Timestamp", "set") => {
                    check(timestamp.is_none(), Error::Replay)?;
                    timestamp = Some(
                        field(nested, "now")
                            .and_then(ScaleValue::as_u128)
                            .and_then(|n| u64::try_from(n).ok())
                            .ok_or(Error::Metadata)?
                            / 1000,
                    );
                }
                ("Midnight", "send_mn_transaction") => transactions.push((
                    index as u32,
                    ReplayTransaction::Native(scale_bytes(
                        field(nested, "midnight_tx").ok_or(Error::Metadata)?,
                    )?),
                )),
                ("MidnightSystem", "send_mn_system_transaction") if genesis => transactions.push((
                    index as u32,
                    ReplayTransaction::System(scale_bytes(
                        field(nested, "midnight_system_tx").ok_or(Error::Metadata)?,
                    )?),
                )),
                _ => {}
            }
        }
        if let Some(events) = events {
            let ValueDef::Composite(rows) = &events.value else {
                return Err(Error::Metadata);
            };
            for record in rows.values() {
                let event = field(record, "event").ok_or(Error::Metadata)?;
                let (pallet, values) = variant(event)?;
                let nested = values.values().next().ok_or(Error::Metadata)?;
                let (name, _) = variant(nested)?;
                if pallet == "MidnightSystem" && name == "SystemTransactionApplied" {
                    let order = phase(field(record, "phase").ok_or(Error::Metadata)?)?;
                    let tx = scale_bytes(
                        field(nested, "serialized_system_transaction").ok_or(Error::Metadata)?,
                    )?;
                    transactions.push((order, ReplayTransaction::System(tx)));
                }
            }
        }
        transactions.sort_by_key(|(index, _)| *index);
        Ok((
            Timestamp::from_secs(timestamp.unwrap_or(0)),
            transactions.into_iter().map(|(_, tx)| tx).collect(),
        ))
    }
    fn apply_block(
        &self,
        cache: &mut ReplayCache,
        block: BlockContext,
        transactions: Vec<ReplayTransaction>,
        mut partial: Option<&mut PartialReplay<'_>>,
    ) -> Result<()> {
        let mut cost = SyntheticCost::ZERO;
        for transaction in transactions {
            let (next, events, spent) = match transaction {
                ReplayTransaction::System(bytes) => {
                    let tx: SystemTransaction = native_decode(&bytes)?;
                    let spent = tx.cost(&cache.state.parameters);
                    let (state, events) = cache
                        .state
                        .apply_system_tx(&tx, block.tblock)
                        .map_err(|_| Error::Replay)?;
                    (state, events, spent)
                }
                ReplayTransaction::Native(bytes) => {
                    let tx: crate::funding::SealedTransaction = native_decode(&bytes)?;
                    let context = TransactionContext {
                        ref_state: cache.state.clone(),
                        block_context: block.clone(),
                        whitelist: None,
                    };
                    let mut strictness = WellFormedStrictness::default();
                    // Finalized historical proofs were checked by the trusted node. The final
                    // native state-root comparison authenticates this bounded replay result.
                    strictness.verify_native_proofs = false;
                    strictness.verify_contract_proofs = false;
                    strictness.verify_signatures = false;
                    strictness.enforce_balancing = false;
                    let Ok(verified) =
                        tx.erase_proofs()
                            .well_formed(&cache.state, strictness, block.tblock)
                    else {
                        continue;
                    };
                    let spent = tx
                        .cost(&cache.state.parameters, false)
                        .map_err(|_| Error::Replay)?;
                    let (state, outcome) = cache.state.apply(&verified, &context);
                    if let Some(replay) = partial.as_deref_mut()
                        && bytes == replay.transaction
                    {
                        if replay.partial {
                            let TransactionResult::PartialSuccess(segments, _) = &outcome else {
                                return Err(Error::Replay);
                            };
                            check(replay.result.is_none(), Error::Replay)?;
                            let contract = state.contract.get(&replay.address).ok_or(Error::State)?;
                            let mut bytes = Vec::new();
                            serialize::tagged_serialize(&*contract, &mut bytes)
                                .map_err(|_| Error::State)?;
                            replay.result = Some((
                                segments.iter().map(|(&number, value)| (number, value.is_ok())).collect(),
                                bytes,
                            ));
                        }
                        #[cfg(test)]
                        if !replay.partial {
                            let TransactionResult::Success(events) = &outcome else {
                                return Err(Error::Replay);
                            };
                            check(replay.logs.is_none(), Error::Replay)?;
                            replay.logs = Some(events.iter().filter_map(|event| {
                                match &event.content {
                                    EventDetails::ContractLog { address, entry_point, logged_item } => {
                                        Some(FinalizedContractLog {
                                            address: *address,
                                            entry_point: entry_point.clone(),
                                            item: logged_item.clone(),
                                        })
                                    }
                                    _ => None,
                                }
                            }).collect());
                        }
                    }
                    let events = match outcome {
                        TransactionResult::Success(events)
                        | TransactionResult::PartialSuccess(_, events) => events,
                        TransactionResult::Failure(_) => Vec::new(),
                    };
                    (state, events, spent)
                }
            };
            cost = cost + spent;
            cache.state = next;
            if let Some(secret) = self.dust_secret.borrow().as_ref() {
                cache.dust = cache
                    .dust
                    .replay_events(secret, events.iter())
                    .map_err(|_| Error::Replay)?;
            }
        }
        let normalized = cost
            .normalize(cache.state.parameters.limits.block_limits)
            .ok_or(Error::Replay)?;
        let fullness = FixedPoint::max(
            FixedPoint::max(normalized.read_time, normalized.compute_time),
            FixedPoint::max(
                normalized.block_usage,
                FixedPoint::max(normalized.bytes_written, normalized.bytes_churned),
            ),
        );
        cache.state = cache
            .state
            .post_block_update(block.tblock, normalized, fullness)
            .map_err(|_| Error::Replay)?;
        cache.dust = cache.dust.process_ttls(block.tblock);
        cache.block = block;
        Ok(())
    }
    pub fn sync(&self) -> Result<Snapshot> {
        let final_hash = hash_text(&self.rpc.call("chain_getFinalizedHead", json!([]))?)?;
        self.replay_to(&final_hash, &mut self.cache.borrow_mut(), None)
    }

    /// Prepare a completed typed witness against this node's verified finalized snapshot.
    /// The caller cannot supply a clock value or a replacement block context.
    pub fn prepare_contract_witness_proof(
        &self,
        execution: &mut crate::witness_execution::WitnessExecution,
        rng: &mut (impl rand::Rng + rand::CryptoRng),
    ) -> std::result::Result<crate::witness_execution::WitnessProof, WitnessPreparationError> {
        let snapshot = self.sync().map_err(WitnessPreparationError::Node)?;
        execution
            .prepare_contract_proof_with_snapshot(&snapshot, &self.policy, rng)
            .map_err(WitnessPreparationError::Witness)
    }

    fn replay_to(
        &self,
        final_hash: &str,
        cache: &mut Option<ReplayCache>,
        mut partial: Option<&mut PartialReplay<'_>>,
    ) -> Result<Snapshot> {
        let identity = self.rpc.chain_identity(final_hash, &self.policy.profile)?;
        self.policy.check(&identity).map_err(|_| Error::Network)?;
        self.check_runtime(final_hash)?;
        let header = self
            .rpc
            .call("chain_getHeader", json!([format!("0x{final_hash}")]))?;
        let height = u64::from_str_radix(
            header["number"]
                .as_str()
                .ok_or(Error::Response)?
                .trim_start_matches("0x"),
            16,
        )
        .map_err(|_| Error::Response)?;
        check(height <= self.max_replay_blocks, Error::Limit)?;
        let mut replay = if let Some(cached) = cache.as_ref() {
            cached.clone()
        } else {
            self.check_runtime(&self.policy.genesis)?;
            let properties = self.rpc.call("system_properties", json!([]))?;
            let initial: LedgerState<Db> =
                native_decode(&hex_bytes(&properties["genesis_state"])?)?;
            check(initial.network_id == self.policy.network_id, Error::Network)?;
            let genesis = properties["genesis_extrinsics"]
                .as_array()
                .ok_or(Error::Response)?;
            let (time, transactions) = self.transactions(genesis, None, true)?;
            let mut replay = ReplayCache {
                dust: DustLocalState::new(initial.parameters.dust),
                state: LedgerState::new(self.policy.network_id.clone()),
                height: 0,
                hash: self.policy.genesis.clone(),
                block: BlockContext::default(),
            };
            self.apply_block(
                &mut replay,
                BlockContext {
                    tblock: time,
                    ..Default::default()
                },
                transactions,
                None,
            )?;
            replay.state = initial;
            replay
        };
        check(height >= replay.height, Error::Replay)?;
        for heights in ((replay.height + 1)..=height)
            .collect::<Vec<_>>()
            .chunks(40)
        {
            let requests: Vec<_> = heights
                .iter()
                .map(|number| ("chain_getBlockHash".into(), json!([number])))
                .collect();
            let hashes = self
                .rpc
                .batch(&requests)?
                .iter()
                .map(hash_text)
                .collect::<Result<Vec<_>>>()?;
            let requests: Vec<_> = hashes.iter().flat_map(|hash| [("chain_getBlock".into(), json!([format!("0x{hash}")])), ("state_getStorage".into(), json!(["0x26aa394eea5630e07c48ae0c9558cef780d41e5e16056765bc8461851072c9d7",format!("0x{hash}")])), ("state_getStorageHash".into(),json!(["0x3a636f6465",format!("0x{hash}")]))]).collect();
            let rows = self.rpc.batch(&requests)?;
            for (index, hash) in hashes.iter().enumerate() {
                check(
                    hash_text(&rows[index * 3 + 2])? == self.runtime_code,
                    Error::Metadata,
                )?;
                let block = &rows[index * 3]["block"];
                check(
                    u64::from_str_radix(
                        block["header"]["number"]
                            .as_str()
                            .ok_or(Error::Response)?
                            .trim_start_matches("0x"),
                        16,
                    )
                    .map_err(|_| Error::Response)?
                        == heights[index],
                    Error::Replay,
                )?;
                check(
                    hash_text(&block["header"]["parentHash"])? == replay.hash,
                    Error::Replay,
                )?;
                let events = self.metadata.events(&hex_bytes(&rows[index * 3 + 1])?)?;
                let (time, transactions) = self.transactions(
                    block["extrinsics"].as_array().ok_or(Error::Response)?,
                    Some(&events),
                    false,
                )?;
                let context = BlockContext {
                    tblock: time,
                    tblock_err: 30,
                    parent_block_hash: HashOutput(
                        hex::decode(&replay.hash)
                            .map_err(|_| Error::Response)?
                            .try_into()
                            .map_err(|_| Error::Response)?,
                    ),
                    last_block_time: replay.block.tblock,
                };
                let capture = if heights[index] == height {
                    partial.as_deref_mut()
                } else {
                    None
                };
                self.apply_block(&mut replay, context, transactions, capture)?;
                replay.height = heights[index];
                replay.hash = hash.clone();
            }
        }
        check(replay.hash == final_hash, Error::Replay)?;
        let raw_root = hex_bytes(&self.rpc.call(
            "state_call",
            json!([
                "MidnightRuntimeApi_get_ledger_state_root",
                "0x",
                format!("0x{final_hash}")
            ]),
        )?)?;
        let mut reader = raw_root.as_slice();
        check(
            u8::decode(&mut reader).map_err(|_| Error::State)? == 0,
            Error::State,
        )?;
        let root = Vec::<u8>::decode(&mut reader).map_err(|_| Error::State)?;
        check(reader.is_empty(), Error::State)?;
        let stored = storage::storage::default_storage::<Db>()
            .arena
            .alloc(replay.state.clone());
        check(native_bytes(&stored.as_typed_key())? == root, Error::Replay)?;
        let snapshot = Snapshot {
            chain: identity,
            finalized_hash: final_hash.into(),
            height,
            state: replay.state.clone(),
            block: replay.block.clone(),
        };
        *cache = Some(replay);
        Ok(snapshot)
    }
    /// Observe a bound transaction at one canonical finalized block.
    pub fn finalized_receipt(
        &self,
        transaction: &BoundTransaction,
    ) -> Result<Option<FinalizedReceipt>> {
        match self.finalized_observation(transaction)? {
            Observation::Pending => Ok(None),
            Observation::Finalized(receipt) => Ok(Some(receipt)),
            Observation::Rejected | Observation::Partial(_) => Err(Error::Replay),
        }
    }
    fn finalized_observation(&self, transaction: &BoundTransaction) -> Result<Observation> {
        let final_hash = hash_text(&self.rpc.call("chain_getFinalizedHead", json!([]))?)?;
        transaction
            .policy()
            .check(&self.rpc.chain_identity(&final_hash, &self.policy.profile)?)
            .map_err(|_| Error::Network)?;
        let header = self
            .rpc
            .call("chain_getHeader", json!([format!("0x{final_hash}")]))?;
        let height = u64::from_str_radix(
            header["number"]
                .as_str()
                .ok_or(Error::Response)?
                .trim_start_matches("0x"),
            16,
        )
        .map_err(|_| Error::Response)?;
        check(
            height.saturating_sub(transaction.after_height()) <= self.max_replay_blocks,
            Error::Limit,
        )?;
        self.check_runtime(&final_hash)?;
        let expected = self.metadata.extrinsic(transaction.bytes())?;
        let mut previous = None;
        let mut found = None;
        for numbers in ((transaction.after_height() + 1)..=height)
            .collect::<Vec<_>>()
            .chunks(64)
        {
            let queries: Vec<_> = numbers
                .iter()
                .map(|n| ("chain_getBlockHash".into(), json!([n])))
                .collect();
            let hashes = self
                .rpc
                .batch(&queries)?
                .iter()
                .map(hash_text)
                .collect::<Result<Vec<_>>>()?;
            let blocks = self.rpc.batch(
                &hashes
                    .iter()
                    .flat_map(|h| {
                        [
                            ("chain_getBlock".into(), json!([format!("0x{h}")])),
                            (
                                "state_getStorageHash".into(),
                                json!(["0x3a636f6465", format!("0x{h}")]),
                            ),
                        ]
                    })
                    .collect::<Vec<_>>(),
            )?;
            for (offset, rows) in blocks.chunks_exact(2).enumerate() {
                check(hash_text(&rows[1])? == self.runtime_code, Error::Metadata)?;
                let block = &rows[0];
                let header_number = u64::from_str_radix(
                    block["block"]["header"]["number"]
                        .as_str()
                        .ok_or(Error::Response)?
                        .trim_start_matches("0x"),
                    16,
                )
                .map_err(|_| Error::Response)?;
                check(header_number == numbers[offset], Error::Replay)?;
                let parent = hash_text(&block["block"]["header"]["parentHash"])?;
                validate_parent(previous.as_deref(), &parent)?;
                previous = Some(hashes[offset].clone());
                let extrinsics = block["block"]["extrinsics"]
                    .as_array()
                    .ok_or(Error::Response)?;
                let matching = extrinsics
                    .iter()
                    .enumerate()
                    .filter_map(|(index, encoded)| {
                        hex_bytes(encoded)
                            .is_ok_and(|bytes| bytes == expected)
                            .then_some(index)
                    })
                    .collect::<Vec<_>>();
                if matching.is_empty() {
                    continue;
                }
                check(matching.len() == 1, Error::Replay)?;
                let index = matching[0];
                let encoded = self.rpc.call(
                    "state_getStorage",
                    json!([
                        "0x26aa394eea5630e07c48ae0c9558cef780d41e5e16056765bc8461851072c9d7",
                        format!("0x{}", hashes[offset])
                    ]),
                )?;
                let decoded = self.metadata.events(&hex_bytes(&encoded)?)?;
                let ValueDef::Composite(rows) = &decoded.value else {
                    return Err(Error::Metadata);
                };
                let mut partial = None;
                let mut contract = transaction.contract_event_counts();
                for row in rows.values() {
                    let (phase_name, phase_fields) =
                        variant(field(row, "phase").ok_or(Error::Metadata)?)?;
                    if phase_name != "ApplyExtrinsic"
                        || phase_fields.values().next().and_then(ScaleValue::as_u128)
                            != Some(index as u128)
                    {
                        continue;
                    }
                    let (pallet, nested) = variant(field(row, "event").ok_or(Error::Metadata)?)?;
                    if pallet != "Midnight" {
                        continue;
                    }
                    let event = nested.values().next().ok_or(Error::Metadata)?;
                    let (name, _) = variant(event)?;
                    if name == "TxRejected" {
                        return Err(Error::Replay);
                    }
                    if !matches!(
                        name,
                        "TxApplied" | "TxPartialSuccess" | "ContractCall" | "ContractDeploy"
                    ) {
                        continue;
                    }
                    let tx_hash = scale_bytes(field(event, "tx_hash").ok_or(Error::Metadata)?)?;
                    check(
                        hex::encode(tx_hash) == transaction.transaction_id(),
                        Error::Response,
                    )?;
                    if matches!(name, "TxApplied" | "TxPartialSuccess") {
                        check(
                            partial.replace(name == "TxPartialSuccess").is_none(),
                            Error::Replay,
                        )?;
                    } else {
                        let address: coin_structure::contract::ContractAddress = native_decode(
                            &scale_bytes(field(event, "contract_address").ok_or(Error::Metadata)?)?,
                        )?;
                        let expected_event = match transaction.event() {
                            crate::client::ContractEvent::Deploy => "ContractDeploy",
                            crate::client::ContractEvent::Call => "ContractCall",
                            crate::client::ContractEvent::Maintain => {
                                return Err(Error::Replay);
                            }
                        };
                        check(name == expected_event, Error::Response)?;
                        let count = contract
                            .get_mut(&hex::encode(address.0.0))
                            .filter(|count| **count > 0)
                            .ok_or(Error::Response)?;
                        *count -= 1;
                    }
                }
                let partial = partial.ok_or(Error::Replay)?;
                if !partial {
                    check(contract.values().all(|&count| count == 0), Error::Replay)?;
                }
                let read_state = |address: &str| {
                    let bytes = hex_bytes(&self.rpc.call(
                        "midnight_contractState",
                        json!([address, format!("0x{}", hashes[offset])]),
                    )?)?;
                    let state: onchain_runtime::state::ContractState<Db> = native_decode(&bytes)?;
                    let mut canonical = Vec::new();
                    serialize::tagged_serialize(&state, &mut canonical)
                        .map_err(|_| Error::State)?;
                    check(canonical == bytes, Error::State)?;
                    Ok::<_, Error>(bytes)
                };
                let canonical = read_state(transaction.contract_address())?;
                let secondary_states = transaction
                    .secondary_states()
                    .keys()
                    .map(|address| Ok((address.clone(), read_state(address)?)))
                    .collect::<Result<BTreeMap<_, _>>>()?;
                use blake2::Digest;
                let extrinsic_hash = hex::encode(
                    blake2::Blake2b::<blake2::digest::consts::U32>::digest(&expected),
                );
                let receipt = FinalizedReceipt {
                    chain: self
                        .rpc
                        .chain_identity(&hashes[offset], &self.policy.profile)?,
                    block_hash: hashes[offset].clone(),
                    height: numbers[offset],
                    finalized_hash: final_hash.clone(),
                    finalized_height: height,
                    extrinsic_hash,
                    extrinsic_index: index as u32,
                    transaction_id: transaction.transaction_id().into(),
                    intent_id: transaction.intent_id().into(),
                    contract_address: transaction.contract_address().into(),
                    event: transaction.event(),
                    contract_state: canonical,
                    secondary_states,
                };
                check(found.is_none(), Error::Replay)?;
                found = Some(if partial {
                    let entrypoint = transaction.checkpoint_entrypoint().ok_or(Error::Replay)?;
                    let address = ContractAddress(HashOutput(
                        hex::decode(transaction.contract_address())
                            .map_err(|_| Error::Response)?
                            .try_into()
                            .map_err(|_| Error::Response)?,
                    ));
                    let mut replay = PartialReplay {
                        transaction: transaction.bytes(),
                        address,
                        partial: true,
                        result: None,
                        #[cfg(test)]
                        logs: None,
                    };
                    // The outcome event carries the transaction hash only. Replay the exact
                    // signed bytes in the canonical block to recover the segment results.
                    let mut cache = self
                        .cache
                        .borrow()
                        .as_ref()
                        .filter(|cache| cache.height < receipt.height)
                        .cloned();
                    self.replay_to(&receipt.block_hash, &mut cache, Some(&mut replay))?;
                    let (segments, state) = replay.result.ok_or(Error::Replay)?;
                    check(state == receipt.contract_state, Error::Replay)?;
                    let partial = PartialReceipt {
                        receipt,
                        segments,
                        entrypoint: entrypoint.to_vec(),
                    };
                    transaction
                        .check_partial_receipt(&partial)
                        .map_err(|_| Error::Response)?;
                    Observation::Partial(partial)
                } else {
                    transaction
                        .check_receipt(&receipt)
                        .map_err(|_| Error::Response)?;
                    Observation::Finalized(receipt)
                });
            }
        }
        validate_finalized_tip(previous.as_deref(), &final_hash)?;
        Ok(found.unwrap_or(Observation::Pending))
    }
}

fn validate_parent(previous: Option<&str>, parent: &str) -> Result<()> {
    check(previous.is_none_or(|hash| hash == parent), Error::Replay)
}
fn validate_finalized_tip(last: Option<&str>, finalized: &str) -> Result<()> {
    check(last.is_none_or(|hash| hash == finalized), Error::Replay)
}
fn cache_matches(cache: &ReplayCache, snapshot: &Snapshot) -> bool {
    cache.hash == snapshot.finalized_hash
        && cache.height == snapshot.height
        && cache.state == snapshot.state
        && cache.block.tblock == snapshot.block.tblock
        && cache.block.tblock_err == snapshot.block.tblock_err
        && cache.block.parent_block_hash == snapshot.block.parent_block_hash
        && cache.block.last_block_time == snapshot.block.last_block_time
}

// Pool refusal after an unknown broadcast does not establish absence of ledger effects.
fn pool_submission(code: Option<i64>, finalized: bool) -> crate::client::Submission {
    if code == Some(1013) || finalized {
        crate::client::Submission::Broadcast
    } else {
        crate::client::Submission::Uncertain
    }
}

impl crate::client::ChainAdapter for Node {
    async fn snapshot(&self) -> std::result::Result<Snapshot, crate::client::HostFailure> {
        self.sync().map_err(|_| crate::client::HostFailure)
    }
    async fn submit(
        &self,
        transaction: &crate::client::BoundTransaction,
    ) -> std::result::Result<crate::client::Submission, crate::client::HostFailure> {
        use crate::client::{HostFailure, Submission};
        let at = hash_text(
            &self
                .rpc
                .call("chain_getFinalizedHead", json!([]))
                .map_err(|_| HostFailure)?,
        )
        .map_err(|_| HostFailure)?;
        self.policy
            .check(
                &self
                    .rpc
                    .chain_identity(&at, &self.policy.profile)
                    .map_err(|_| HostFailure)?,
            )
            .map_err(|_| HostFailure)?;
        self.check_runtime(&at).map_err(|_| HostFailure)?;
        let metadata = self.rpc.metadata(&at).map_err(|_| HostFailure)?;
        let extrinsic = metadata
            .extrinsic(transaction.bytes())
            .map_err(|_| HostFailure)?;
        let response = match self.rpc.send(&json!({"jsonrpc":"2.0","id":1,"method":"author_submitExtrinsic","params":[format!("0x{}",hex::encode(&extrinsic))]})) { Ok(response) => response, Err(_) => return Ok(Submission::Uncertain) };
        if response["id"] != 1 || response["jsonrpc"] != "2.0" {
            return Ok(Submission::Uncertain);
        }
        if let Some(error) = response.get("error") {
            let code = error["code"].as_i64();
            let finalized = matches!(code, Some(1010..=1016))
                && matches!(
                    self.finalized_observation(transaction),
                    Ok(Observation::Finalized(_) | Observation::Partial(_))
                );
            return Ok(pool_submission(code, finalized));
        }
        use blake2::Digest;
        let expected = hex::encode(blake2::Blake2b::<blake2::digest::consts::U32>::digest(
            &extrinsic,
        ));
        if hash_text(&response["result"]).ok().as_deref() == Some(expected.as_str()) {
            Ok(Submission::Broadcast)
        } else {
            Ok(Submission::Uncertain)
        }
    }
    async fn observe(
        &self,
        transaction: &crate::client::BoundTransaction,
    ) -> std::result::Result<crate::client::Observation, crate::client::HostFailure> {
        self.finalized_observation(transaction)
            .map_err(|_| crate::client::HostFailure)
    }
}

pub struct DevelopmentFunding<'a> {
    node: &'a Node,
    material: &'a crate::funding::DustMaterial,
    parameters: &'a crate::proof::TrustedParameters,
    policy: crate::funding::FeePolicy,
    rng: RefCell<Option<rand::rngs::StdRng>>,
    shielded_receive: Option<shielded_receive::BookedOffer>,
    shielded_relay: Option<shielded_relay::BookedRelay>,
    shielded_immediate_change: Option<shielded_transfer::BookedImmediateChange>,
    wallet_shielded_receive: Option<shielded_receive::BookedWalletOffer>,
    wallet_shielded_mint: Option<shielded_receive::BookedWalletMint>,
    shielded_transfer: Option<shielded_transfer::BookedTransfer>,
    shielded_split: Option<shielded_transfer::BookedTransfer>,
    shielded_merge: Option<shielded_merge::BookedMerge>,
}
impl<'a> DevelopmentFunding<'a> {
    fn has_shielded_offer(&self) -> bool {
        self.shielded_receive.is_some()
            || self.shielded_relay.is_some()
            || self.shielded_immediate_change.is_some()
            || self.wallet_shielded_receive.is_some()
            || self.wallet_shielded_mint.is_some()
            || self.shielded_transfer.is_some()
            || self.shielded_split.is_some()
            || self.shielded_merge.is_some()
    }

    pub fn new(
        node: &'a Node,
        material: &'a crate::funding::DustMaterial,
        parameters: &'a crate::proof::TrustedParameters,
        policy: crate::funding::FeePolicy,
        rng: rand::rngs::StdRng,
    ) -> Self {
        Self {
            node,
            material,
            parameters,
            policy,
            rng: RefCell::new(Some(rng)),
            shielded_receive: None,
            shielded_relay: None,
            shielded_immediate_change: None,
            wallet_shielded_receive: None,
            wallet_shielded_mint: None,
            shielded_transfer: None,
            shielded_split: None,
            shielded_merge: None,
        }
    }
}
impl crate::client::FundingAdapter for DevelopmentFunding<'_> {
    async fn fund(
        &self,
        contract: &crate::proof::ProvedNativeIntent,
        snapshot: &Snapshot,
        policy: &NetworkPolicy,
    ) -> std::result::Result<crate::funding::UnsealedTransaction, crate::client::HostFailure> {
        use crate::client::HostFailure;
        policy.check(&snapshot.chain).map_err(|_| HostFailure)?;
        if *policy != self.node.policy {
            return Err(HostFailure);
        }
        let settle_mint = contract.guaranteed_unshielded_offer.is_some();
        if settle_mint {
            if self.has_shielded_offer() {
                return Err(HostFailure);
            }
            crate::unshielded_mint::validate_user_output_offer(contract)
                .map_err(|_| HostFailure)?;
        }
        let state = {
            let cache = self.node.cache.borrow();
            let cache = cache.as_ref().ok_or(HostFailure)?;
            if !cache_matches(cache, snapshot) {
                return Err(HostFailure);
            }
            cache.dust.clone()
        };
        let secret = self
            .node
            .dust_secret
            .borrow()
            .as_ref()
            .ok_or(HostFailure)?
            .clone();
        let rng = self.rng.borrow_mut().take().ok_or(HostFailure)?;
        let wallet = crate::funding::DustFunding::new(secret, state);
        let funded = if let Some(merge) = &self.shielded_merge {
            merge.check_booking(snapshot)?;
            wallet
                .fund_shielded_merge(
                    contract,
                    merge.offer.clone(),
                    merge.randomness,
                    merge.staged_mint(),
                    &policy.network_id,
                    &snapshot.state.parameters,
                    self.material,
                    self.parameters,
                    snapshot.block.tblock,
                    self.policy,
                    rng,
                )
                .await
        } else if let Some(relay) = &self.shielded_relay {
            relay.check_booking(snapshot)?;
            wallet
                .fund_shielded_relay(
                    contract,
                    relay.offer.clone(),
                    relay.randomness,
                    &relay.mint,
                    relay.domain,
                    &policy.network_id,
                    &snapshot.state.parameters,
                    self.material,
                    self.parameters,
                    snapshot.block.tblock,
                    self.policy,
                    rng,
                )
                .await
        } else if let Some(immediate_change) = &self.shielded_immediate_change {
            immediate_change.check_booking(snapshot)?;
            wallet
                .fund_shielded_immediate_change(
                    contract,
                    immediate_change.offer.clone(),
                    immediate_change.randomness,
                    &immediate_change.mint,
                    immediate_change.domain,
                    immediate_change.recipient,
                    &policy.network_id,
                    &snapshot.state.parameters,
                    self.material,
                    self.parameters,
                    snapshot.block.tblock,
                    self.policy,
                    rng,
                )
                .await
        } else if let Some(receive) = &self.wallet_shielded_receive {
            receive.check_booking(snapshot)?;
            wallet
                .fund_wallet_shielded_receive(
                    contract,
                    receive.offer.clone(),
                    receive.randomness,
                    &policy.network_id,
                    &snapshot.state.parameters,
                    self.material,
                    self.parameters,
                    snapshot.block.tblock,
                    self.policy,
                    rng,
                )
                .await
        } else if let Some(mint) = &self.wallet_shielded_mint {
            mint.check_booking(snapshot)?;
            wallet
                .fund_shielded_wallet_mint(
                    contract,
                    mint.offer.clone(),
                    mint.randomness,
                    mint.domain,
                    &mint.coin,
                    mint.recipient,
                    &policy.network_id,
                    &snapshot.state.parameters,
                    self.material,
                    self.parameters,
                    snapshot.block.tblock,
                    self.policy,
                    rng,
                )
                .await
        } else if let Some(receive) = &self.shielded_receive {
            receive.check_booking(snapshot)?;
            wallet
                .fund_shielded_receive(
                    contract,
                    receive.offer.clone(),
                    receive.randomness,
                    &policy.network_id,
                    &snapshot.state.parameters,
                    self.material,
                    self.parameters,
                    snapshot.block.tblock,
                    self.policy,
                    rng,
                )
                .await
        } else if let Some(split) = &self.shielded_split {
            split.check_booking(snapshot)?;
            wallet
                .fund_shielded_split(
                    contract,
                    split.offer.clone(),
                    split.randomness,
                    &policy.network_id,
                    &snapshot.state.parameters,
                    self.material,
                    self.parameters,
                    snapshot.block.tblock,
                    self.policy,
                    rng,
                )
                .await
        } else if let Some(transfer) = &self.shielded_transfer {
            transfer.check_booking(snapshot)?;
            wallet
                .fund_shielded_transfer(
                    contract,
                    transfer.offer.clone(),
                    transfer.randomness,
                    &policy.network_id,
                    &snapshot.state.parameters,
                    self.material,
                    self.parameters,
                    snapshot.block.tblock,
                    self.policy,
                    rng,
                )
                .await
        } else if settle_mint {
            wallet
                .fund_unshielded_mint(
                    contract,
                    &policy.network_id,
                    &snapshot.state.parameters,
                    self.material,
                    self.parameters,
                    snapshot.block.tblock,
                    self.policy,
                    rng,
                )
                .await
        } else {
            wallet
                .fund(
                    contract,
                    &policy.network_id,
                    &snapshot.state.parameters,
                    self.material,
                    self.parameters,
                    snapshot.block.tblock,
                    self.policy,
                    rng,
                )
                .await
        }
        .map_err(|_| HostFailure)?;
        Ok(funded.native().clone())
    }

    async fn fund_unshielded_caller(
        &self,
        contract: &crate::proof::ProvedNativeIntent,
        snapshot: &Snapshot,
        policy: &NetworkPolicy,
    ) -> std::result::Result<crate::funding::UnsealedTransaction, crate::client::HostFailure> {
        use crate::client::HostFailure;

        if self.has_shielded_offer() {
            return Err(HostFailure);
        }
        policy.check(&snapshot.chain).map_err(|_| HostFailure)?;
        if *policy != self.node.policy {
            return Err(HostFailure);
        }
        crate::unshielded_caller::validate_guaranteed_caller_offer(snapshot, contract)
            .map_err(|_| HostFailure)?;
        let state = {
            let cache = self.node.cache.borrow();
            let cache = cache.as_ref().ok_or(HostFailure)?;
            if !cache_matches(cache, snapshot) {
                return Err(HostFailure);
            }
            cache.dust.clone()
        };
        let secret = self
            .node
            .dust_secret
            .borrow()
            .as_ref()
            .ok_or(HostFailure)?
            .clone();
        let rng = self.rng.borrow_mut().take().ok_or(HostFailure)?;
        let wallet = crate::funding::DustFunding::new(secret, state);
        let funded = wallet
            .fund_unshielded_caller(
                contract,
                snapshot,
                &policy.network_id,
                &snapshot.state.parameters,
                self.material,
                self.parameters,
                snapshot.block.tblock,
                self.policy,
                rng,
            )
            .await
            .map_err(|_| HostFailure)?;
        Ok(funded.native().clone())
    }
}
/// The caller supplies an explicit approval function and a fresh entropy owner.
pub struct ExplicitSeal<F> {
    approve: F,
    rng: RefCell<Option<rand::rngs::StdRng>>,
    unshielded_caller_key: Option<ledger::structure::SigningKey>,
}
impl<F> ExplicitSeal<F> {
    pub fn new(approve: F, rng: rand::rngs::StdRng) -> Self {
        Self {
            approve,
            rng: RefCell::new(Some(rng)),
            unshielded_caller_key: None,
        }
    }

    /// Opt in to signing the snapshot-checked contract caller offer after approval.
    pub fn with_unshielded_caller_key(
        mut self,
        key: ledger::structure::SigningKey,
    ) -> Self {
        self.unshielded_caller_key = Some(key);
        self
    }
}

fn sign_guaranteed_caller_offer(
    transaction: &mut crate::funding::UnsealedTransaction,
    snapshot: &Snapshot,
    key: &ledger::structure::SigningKey,
    rng: &mut rand::rngs::StdRng,
) -> std::result::Result<(), crate::client::HostFailure> {
    use crate::funding::CONTRACT_SEGMENT;
    use ledger::structure::Transaction;

    let Transaction::Standard(standard) = transaction else {
        return Err(crate::client::HostFailure);
    };
    let mut contract = (*standard
        .intents
        .get(&CONTRACT_SEGMENT)
        .ok_or(crate::client::HostFailure)?)
    .clone();
    crate::unshielded_caller::validate_guaranteed_caller_offer(snapshot, &contract)
        .map_err(|_| crate::client::HostFailure)?;
    let signature_count = contract
        .guaranteed_unshielded_offer
        .as_deref()
        .ok_or(crate::client::HostFailure)?
        .inputs
        .len();
    let signing_keys = vec![key.clone(); signature_count];
    contract = contract
        .sign(rng, CONTRACT_SEGMENT, &signing_keys, &[], &[])
        .map_err(|_| crate::client::HostFailure)?;
    standard.intents = standard.intents.insert(CONTRACT_SEGMENT, contract);
    Ok(())
}

impl<F: Fn(&crate::funding::UnsealedTransaction, &NetworkPolicy) -> bool>
    crate::client::SigningAdapter for ExplicitSeal<F>
{
    async fn approve_and_sign(
        &self,
        transaction: &crate::funding::UnsealedTransaction,
        snapshot: &Snapshot,
        policy: &NetworkPolicy,
    ) -> std::result::Result<crate::funding::SealedTransaction, crate::client::HostFailure> {
        policy
            .check(&snapshot.chain)
            .map_err(|_| crate::client::HostFailure)?;
        if !(self.approve)(transaction, policy) {
            return Err(crate::client::HostFailure);
        }
        let mut rng = self
            .rng
            .borrow_mut()
            .take()
            .ok_or(crate::client::HostFailure)?;
        let mut transaction = transaction.clone();
        if let Some(key) = &self.unshielded_caller_key {
            sign_guaranteed_caller_offer(&mut transaction, snapshot, key, &mut rng)?;
        }
        Ok(transaction.seal(rng))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::Digest;

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires the pinned NativeBlockTime checkTime bundle and funded development node"]
    fn native_block_time_strict_edges_finalize_without_state_changes() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, Role},
            proof::{LocalProver, PreparedProof},
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use base_crypto::hash::HashOutput;
        use coin_structure::contract::ContractAddress;
        use futures::{executor::block_on, future::pending};
        use onchain_runtime::{context::QueryContext, state::EntryPointBuf};
        use rand::{SeedableRng, rngs::StdRng};
        use serde_json::json;
        use std::{collections::BTreeMap, env, path::Path};

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let directory = setting("NOCTIUM_BLOCK_TIME_BUNDLES")?;
            let pins: BTreeMap<String, String> =
                serde_json::from_str(&setting("NOCTIUM_BLOCK_TIME_MANIFESTS")?)?;
            ensure!(
                pins.len() == 1 && pins.contains_key("checkTime"),
                "expected the single checkTime bundle pin"
            );
            let bundle = artifacts::verify(
                &Path::new(&directory).join("checkTime"),
                Some(&pins["checkTime"]),
            )?;
            let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
            ensure!(plan.entrypoint == "checkTime", "expected checkTime plan");
            let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
            let cache = ProofCache::new(
                setting("NOCTIUM_BLOCK_TIME_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(&setting("NOCTIUM_BLOCK_TIME_NODE")?, &cache)
                .await?;

            let inclusion_timestamp = |block_hash: &str| -> anyhow::Result<u64> {
                let block = funded
                    .node
                    .rpc
                    .call("chain_getBlock", json!([format!("0x{block_hash}")]))?;
                let extrinsics = block["block"]["extrinsics"]
                    .as_array()
                    .context("finalized inclusion block has no extrinsics")?;
                let (timestamp, _) = funded.node.transactions(extrinsics, None, false)?;
                Ok(timestamp.to_secs())
            };

            let mut records = Vec::new();
            for (name, enabled, cutoff) in [
                ("inactive", false, 0u64),
                ("minimum", true, 0u64),
                ("maximum", true, u64::MAX),
            ] {
                let snapshot = funded.node.sync()?;
                let source_time = snapshot.block.tblock.to_secs();
                ensure!(source_time > 0, "expected a positive finalized block time");
                let ttl = source_time
                    .checked_add(1800)
                    .context("proof TTL overflows UInt64")?;
                let inputs = BTreeMap::from([
                    ("cutoff".into(), json!(cutoff.to_string())),
                    ("enabled".into(), json!(enabled)),
                ]);
                let private_config = serde_json::to_vec(&json!({
                    "inputs": inputs,
                    "state": {},
                }))?;
                let prepared = PreparedProof::from_config_in_block(
                    &bundle,
                    &private_config,
                    ttl,
                    &snapshot.block,
                    &mut StdRng::from_entropy(),
                )?;
                let (address, operation) = prepared.call_target()?;
                ensure!(operation == "checkTime", "proof targets another operation");

                let native_address = ContractAddress(HashOutput(
                    hex::decode(&address)?
                        .try_into()
                        .map_err(|_| anyhow::anyhow!("invalid contract address"))?,
                ));
                let mut source_context = QueryContext::new(
                    crate::create_state(&plan, &BTreeMap::new())?,
                    native_address,
                );
                source_context.call_context.tblock = snapshot.block.tblock;
                source_context.call_context.tblock_err = snapshot.block.tblock_err;
                source_context.call_context.parent_block_hash = snapshot.block.parent_block_hash;
                source_context.call_context.last_block_time = snapshot.block.last_block_time;
                let oracle = crate::prepare_with_context(
                    &plan,
                    &inputs,
                    source_context,
                    &snapshot.state.parameters,
                )?;
                ensure!(
                    crate::check(&oracle, &circuit)? == oracle.activity_schedule,
                    "source oracle activity differs from the native circuit"
                );
                let outputs = oracle.returns_json();
                let before = outputs["beforeDeadline"]
                    .as_bool()
                    .context("source oracle omitted beforeDeadline")?;
                let after = outputs["afterDeadline"]
                    .as_bool()
                    .context("source oracle omitted afterDeadline")?;
                let expected = if enabled {
                    (source_time < cutoff, cutoff < source_time)
                } else {
                    (false, false)
                };
                ensure!((before, after) == expected, "source oracle edge result differs");

                let call_parameters = cache.parameters(prepared.k()).await?;
                let proved_call = prepared
                    .prove(
                        &LocalProver::new(StdRng::from_entropy()),
                        &call_parameters,
                        1_048_576,
                        pending(),
                    )
                    .await?;
                let (_, deployment) = prepared
                    .deployment_intent()
                    .context("missing deployment intent")?
                    .prove(
                        crate::funding::CONTRACT_SEGMENT,
                        builtin_zkir::LocalProvingProvider {
                            rng: StdRng::from_entropy(),
                            resolver: &funded.dust,
                            params: &funded.dust_parameters,
                        },
                        &snapshot.state.parameters.cost_model.runtime_cost_model,
                    )
                    .await
                    .map_err(|error| anyhow::anyhow!("deployment proof: {error:?}"))?;
                let (_, deployment_receipt) = funded.finalize(&deployment).await?;
                let (_, call_receipt) = funded.finalize(proved_call.native()).await?;
                ensure!(
                    call_receipt.contract_address == address,
                    "finalized checkTime call targets another contract"
                );
                ensure!(
                    deployment_receipt.contract_state == call_receipt.contract_state,
                    "checkTime changed native contract state"
                );
                let deployed_state: onchain_runtime::state::ContractState<Db> =
                    native_decode(&deployment_receipt.contract_state)?;
                ensure!(deployed_state.operations.size() == 1, "expected one native operation");
                ensure!(
                    deployed_state
                        .operations
                        .get(&EntryPointBuf(b"checkTime".to_vec()))
                        .is_some(),
                    "deployed native state omitted checkTime"
                );
                let deployment_time = inclusion_timestamp(&deployment_receipt.block_hash)?;
                let call_time = inclusion_timestamp(&call_receipt.block_hash)?;
                ensure!(
                    deployment_time > 0 && call_time > 0,
                    "finalized deployment or checkTime inclusion has no block timestamp"
                );
                let inclusion_result = if enabled {
                    (call_time < cutoff, cutoff < call_time)
                } else {
                    (false, false)
                };
                ensure!(
                    (before, after) == inclusion_result,
                    "source oracle result did not stay on the same side through finalization"
                );

                records.push(json!({
                    "case": name,
                    "enabled": enabled,
                    "cutoff": cutoff.to_string(),
                    "sourceOracle": {
                        "finalizedContextTimestamp": source_time.to_string(),
                        "beforeDeadline": before,
                        "afterDeadline": after,
                    },
                    "deployment": {
                        "height": deployment_receipt.height,
                        "blockHash": deployment_receipt.block_hash,
                        "finalizedHeight": deployment_receipt.finalized_height,
                        "finalizedHash": deployment_receipt.finalized_hash,
                        "timestamp": deployment_time.to_string(),
                        "transactionId": deployment_receipt.transaction_id,
                    },
                    "call": {
                        "height": call_receipt.height,
                        "blockHash": call_receipt.block_hash,
                        "finalizedHeight": call_receipt.finalized_height,
                        "finalizedHash": call_receipt.finalized_hash,
                        "timestamp": call_time.to_string(),
                        "transactionId": call_receipt.transaction_id,
                    },
                    "oneOperationCheckTimeBundle": true,
                    "nativeStateUnchanged": true,
                }));
            }

            let final_snapshot = funded.node.sync()?;
            println!(
                "{}",
                json!({
                    "operation": "checkTime",
                    "bundleManifestSha256": pins,
                    "records": records,
                    "finalizedTip": {
                        "height": final_snapshot.height,
                        "blockHash": final_snapshot.finalized_hash,
                        "timestamp": final_snapshot.block.tblock.to_secs().to_string(),
                    },
                    "scope": {
                        "equalityAtRealChainTimeTested": false,
                        "witnessCurrentStateBindingTested": false,
                    },
                })
            );
            Ok(())
        })
    }

    #[test]
    fn pool_refusal_before_finality_keeps_submission_uncertain() {
        use crate::client::Submission;
        for code in [
            None,
            Some(-1),
            Some(1010),
            Some(1011),
            Some(1012),
            Some(1014),
            Some(1015),
            Some(1016),
        ] {
            assert_eq!(pool_submission(code, false), Submission::Uncertain);
            assert_eq!(pool_submission(code, true), Submission::Broadcast);
        }
        assert_eq!(pool_submission(Some(1013), false), Submission::Broadcast);
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires the authenticated RootFixedByteRecordSet bundle and the funded development node"]
    fn root_fixed_byte_record_set_finalizes_on_funded_ledger() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use base_crypto::{
            fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom},
            hash::HashOutput,
        };
        use coin_structure::contract::ContractAddress;
        use onchain_runtime::state::{ContractState, StateValue};
        use rand::{SeedableRng, rngs::StdRng};
        use sha2::{Digest, Sha256};
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::proofs::Zkir;

        futures::executor::block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let path = setting("NOCTIUM_ROOT_RECORD_SET_BUNDLE")?;
            let manifest = setting("NOCTIUM_ROOT_RECORD_SET_MANIFEST")?;
            let bundle = artifacts::verify(Path::new(&path), Some(&manifest))?;
            let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
            let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
            let cache = ProofCache::new(
                setting("NOCTIUM_ROOT_RECORD_SET_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded =
                FundedLedgerTest::connect(&setting("NOCTIUM_ROOT_RECORD_SET_NODE")?, &cache)
                    .await
                    .context("connect funded development node and admit DUST material")?;
            let parameters = cache
                .parameters(circuit.k())
                .await
                .with_context(|| format!("load root Set k{} parameters", circuit.k()))?;
            let snapshot = funded
                .node
                .sync()
                .context("replay finalized localnet ledger")?;
            let ttl = snapshot.block.tblock.to_secs() + 1800;
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![bundle])?,
                br#"{"state":{"members":[]}}"#,
                ttl,
                &mut StdRng::from_entropy(),
            )?;
            let address = ContractAddress(HashOutput(
                hex::decode(target.contract_address())?
                    .try_into()
                    .map_err(|_| anyhow::anyhow!("invalid fixture address"))?,
            ));
            let update = target.operation("update", &parameters, ttl)?;
            let (state, deployment) = funded.deploy(&target, "update").await?;
            let initial: ContractState<Db> = native_decode(&deployment.contract_state)?;
            let mut last = [3u8; 33];
            last[32] = 4;
            let mut inputs = BTreeMap::from([
                ("tag".into(), json!({"kind":"bytes", "values":[7]})),
                (
                    "firstId".into(),
                    json!({"kind":"bytes", "values":vec![3u8; 33]}),
                ),
                (
                    "lateId".into(),
                    json!({"kind":"bytes", "values":last.as_slice()}),
                ),
            ]);
            let execution = crate::prepare(
                &plan,
                &inputs,
                &initial.data,
                &snapshot.state.parameters,
                address,
            )?;
            crate::check(&execution, &circuit)?;
            let returns = execution.returns_json();
            ensure!(
                returns
                    == BTreeMap::from([
                        ("first".into(), json!(true)),
                        ("late".into(), json!(true)),
                        ("firstAfter".into(), json!(false)),
                        ("lateAfter".into(), json!(true)),
                        ("count".into(), json!("1")),
                    ]),
                "root Set returned a different membership lifecycle"
            );
            let late = inputs.insert(
                "lateId".into(),
                json!({"kind":"bytes", "values":&last[..32]}),
            );
            ensure!(
                crate::prepare(
                    &plan,
                    &inputs,
                    &initial.data,
                    &snapshot.state.parameters,
                    address
                )
                .is_err(),
                "wrong-width key unexpectedly passed native admission"
            );
            inputs.insert("lateId".into(), late.context("missing retained key input")?);
            let call = funded
                .call(&update, &mut Some(state), &parameters, inputs)
                .await?;
            let observed: ContractState<Db> = native_decode(&call.contract_state)?;
            ensure!(
                observed.data == execution.after.state,
                "finalized state differs from preparation"
            );
            let StateValue::Array(slots) = observed.data.get_ref() else {
                anyhow::bail!("expected root state slots");
            };
            let Some(StateValue::Map(members)) = slots.get(0) else {
                anyhow::bail!("expected root Set");
            };
            let key = AlignedValue::new(
                FabValue(vec![
                    ValueAtom::from([7u8].as_slice()),
                    ValueAtom::from(last.as_slice()),
                ]),
                Alignment::concat(&[
                    Alignment::singleton(AlignmentAtom::Bytes { length: 1 }),
                    Alignment::singleton(AlignmentAtom::Bytes { length: 33 }),
                ]),
            )
            .context("invalid expected key alignment")?;
            ensure!(
                members.size() == 1
                    && matches!(members.get(&key), Some(value) if matches!(&*value, StateValue::Null)),
                "finalized Set has a different member"
            );
            let receipt = |value: &FinalizedReceipt| {
                json!({
                    "height": value.height, "blockHash": value.block_hash,
                    "finalizedHeight": value.finalized_height, "finalizedHash": value.finalized_hash,
                    "transactionId": value.transaction_id, "extrinsicHash": value.extrinsic_hash,
                    "extrinsicIndex": value.extrinsic_index,
                })
            };
            println!(
                "{}",
                json!({
                    "manifestSha256": manifest,
                    "k": circuit.k(),
                    "contractAddress": target.contract_address(),
                    "deploy": receipt(&deployment),
                    "call": receipt(&call),
                    "returns": returns,
                    "stateSha256": hex::encode(Sha256::digest(&call.contract_state)),
                    "stateBytes": call.contract_state.len(),
                    "exactLateByteMember": true,
                    "wrongWidthRejectedBeforeSubmission": true,
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires the authenticated NominalFieldRecordSet bundle and the funded development node"]
    fn nominal_field_record_set_finalizes_mutations_on_funded_ledger() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use base_crypto::hash::HashOutput;
        use coin_structure::contract::ContractAddress;
        use onchain_runtime::state::{ContractState, StateValue};
        use rand::{SeedableRng, rngs::StdRng};
        use sha2::{Digest, Sha256};
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::{curve::Fr, proofs::Zkir};

        futures::executor::block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let path = setting("NOCTIUM_NOMINAL_RECORD_SET_BUNDLE")?;
            let manifest = setting("NOCTIUM_NOMINAL_RECORD_SET_MANIFEST")?;
            let bundle = artifacts::verify(Path::new(&path), Some(&manifest))?;
            let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
            ensure!(
                plan.entrypoint == "update",
                "unexpected nominal RecordSet entrypoint"
            );
            let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
            let cache = ProofCache::new(
                setting("NOCTIUM_NOMINAL_RECORD_SET_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(
                &setting("NOCTIUM_NOMINAL_RECORD_SET_NODE")?,
                &cache,
            )
            .await
            .context("connect funded development node and admit DUST material")?;
            let parameters = cache
                .parameters(circuit.k())
                .await
                .with_context(|| format!("load nominal RecordSet k{} parameters", circuit.k()))?;
            let snapshot = funded
                .node
                .sync()
                .context("replay finalized localnet ledger")?;
            let ttl = snapshot.block.tblock.to_secs() + 1800;
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![bundle])?,
                br#"{"state":{"members":[]}}"#,
                ttl,
                &mut StdRng::from_entropy(),
            )?;
            let update = target.operation("update", &parameters, ttl)?;
            let (state, deployment) = funded.deploy(&target, "update").await?;
            let mut current = Some(state);
            let initial: ContractState<Db> = native_decode(&deployment.contract_state)?;
            let address = ContractAddress(HashOutput(
                hex::decode(target.contract_address())?
                    .try_into()
                    .map_err(|_| anyhow::anyhow!("invalid fixture address"))?,
            ));
            let inputs = |adding, removing| {
                BTreeMap::from([
                    ("amount".into(), json!("17")),
                    ("adding".into(), json!(adding)),
                    ("removing".into(), json!(removing)),
                ])
            };
            let expected_returns = |before, after_insert, after_remove| {
                BTreeMap::from([
                    ("before".into(), json!(before)),
                    ("afterInsert".into(), json!(after_insert)),
                    ("afterRemove".into(), json!(after_remove)),
                ])
            };
            let key = crate::field_value(Fr::from(17u64));

            let insert_inputs = inputs(true, false);
            let insert_snapshot = funded.node.sync()?;
            let inserted = crate::prepare(
                &plan,
                &insert_inputs,
                &initial.data,
                &insert_snapshot.state.parameters,
                address,
            )?;
            crate::check(&inserted, &circuit)?;
            let insert_returns = inserted.returns_json();
            ensure!(
                insert_returns == expected_returns(false, true, true),
                "nominal RecordSet insertion returned unexpected membership values"
            );
            let insert = funded
                .call(
                    &update,
                    &mut current,
                    &parameters,
                    insert_inputs,
                )
                .await?;
            let inserted_state: ContractState<Db> = native_decode(&insert.contract_state)?;
            ensure!(
                inserted_state.data == inserted.after.state,
                "finalized inserted state differs from native preparation"
            );
            let StateValue::Array(insert_slots) = inserted_state.data.get_ref() else {
                anyhow::bail!("expected inserted root state slots");
            };
            let Some(StateValue::Map(inserted_members)) = insert_slots.get(0) else {
                anyhow::bail!("expected inserted root RecordSet");
            };
            ensure!(
                inserted_members.size() == 1
                    && matches!(inserted_members.get(&key), Some(value) if matches!(&*value, StateValue::Null)),
                "finalized RecordSet does not contain the exact aligned Field key"
            );

            let remove_inputs = inputs(false, true);
            let remove_snapshot = funded.node.sync()?;
            let removed = crate::prepare(
                &plan,
                &remove_inputs,
                &inserted_state.data,
                &remove_snapshot.state.parameters,
                address,
            )?;
            crate::check(&removed, &circuit)?;
            let remove_returns = removed.returns_json();
            ensure!(
                remove_returns == expected_returns(true, true, false),
                "nominal RecordSet removal returned unexpected membership values"
            );
            let remove = funded
                .call(
                    &update,
                    &mut current,
                    &parameters,
                    remove_inputs,
                )
                .await?;
            let removed_state: ContractState<Db> = native_decode(&remove.contract_state)?;
            ensure!(
                removed_state.data == removed.after.state,
                "finalized removed state differs from native preparation"
            );
            ensure!(
                remove.contract_state == deployment.contract_state,
                "removing the only member did not restore the exact initial state bytes"
            );
            let StateValue::Array(remove_slots) = removed_state.data.get_ref() else {
                anyhow::bail!("expected removed root state slots");
            };
            let Some(StateValue::Map(removed_members)) = remove_slots.get(0) else {
                anyhow::bail!("expected removed root RecordSet");
            };
            ensure!(
                removed_members.size() == 0 && removed_members.get(&key).is_none(),
                "finalized RecordSet retained the removed aligned Field key"
            );

            let receipt = |stage: &str, value: &FinalizedReceipt| {
                json!({
                    "stage": stage,
                    "height": value.height,
                    "finalizedHeight": value.finalized_height,
                    "finalizedHash": value.finalized_hash,
                    "stateBytes": value.contract_state.len(),
                    "stateSha256": hex::encode(Sha256::digest(&value.contract_state)),
                })
            };
            println!(
                "{}",
                json!({
                    "manifestSha256": manifest,
                    "profile": crate::profile::NAME,
                    "k": circuit.k(),
                    "receipts": [
                        receipt("deploy", &deployment),
                        receipt("insert", &insert),
                        receipt("remove", &remove),
                    ],
                    "insertReturns": insert_returns,
                    "removeReturns": remove_returns,
                    "exactAlignedFieldMemberAfterInsert": true,
                    "exactAlignedFieldMemberAbsentAfterRemove": true,
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires the authenticated RootFixedByteRecordValuedMap bundle and the funded development node"]
    fn root_fixed_byte_record_valued_map_finalizes_on_funded_ledger() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use base_crypto::{
            fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom},
            hash::HashOutput,
        };
        use coin_structure::contract::ContractAddress;
        use onchain_runtime::state::{ContractState, StateValue};
        use rand::{SeedableRng, rngs::StdRng};
        use sha2::{Digest, Sha256};
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::{curve::Fr, proofs::Zkir};

        futures::executor::block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let path = setting("NOCTIUM_ROOT_RECORD_MAP_BUNDLE")?;
            let manifest = setting("NOCTIUM_ROOT_RECORD_MAP_MANIFEST")?;
            let bundle = artifacts::verify(Path::new(&path), Some(&manifest))?;
            let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
            let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
            let cache = ProofCache::new(
                setting("NOCTIUM_ROOT_RECORD_MAP_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(
                &setting("NOCTIUM_ROOT_RECORD_MAP_NODE")?,
                &cache,
            )
            .await
            .context("connect funded development node and admit DUST material")?;
            let parameters = cache
                .parameters(circuit.k())
                .await
                .with_context(|| format!("load root Map k{} parameters", circuit.k()))?;
            let snapshot = funded
                .node
                .sync()
                .context("replay finalized localnet ledger")?;
            let ttl = snapshot.block.tblock.to_secs() + 1800;
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![bundle])?,
                br#"{"state":{"receipts":[]}}"#,
                ttl,
                &mut StdRng::from_entropy(),
            )?;
            let address = ContractAddress(HashOutput(
                hex::decode(target.contract_address())?
                    .try_into()
                    .map_err(|_| anyhow::anyhow!("invalid fixture address"))?,
            ));
            let update = target.operation("update", &parameters, ttl)?;
            let (state, deployment) = funded.deploy(&target, "update").await?;
            let initial: ContractState<Db> = native_decode(&deployment.contract_state)?;
            let mut last = [3u8; 33];
            last[32] = 4;
            let mut inputs = BTreeMap::from([
                ("tag".into(), json!({"kind":"bytes", "values":[7]})),
                (
                    "firstId".into(),
                    json!({"kind":"bytes", "values":vec![3u8; 33]}),
                ),
                (
                    "lateId".into(),
                    json!({"kind":"bytes", "values":last.as_slice()}),
                ),
                ("firstAccepted".into(), json!(true)),
                ("firstCode".into(), json!("101")),
                ("lateAccepted".into(), json!(false)),
                ("lateCode".into(), json!("303")),
            ]);
            let execution = crate::prepare(
                &plan,
                &inputs,
                &initial.data,
                &snapshot.state.parameters,
                address,
            )?;
            crate::check(&execution, &circuit)?;
            let returns = execution.returns_json();
            ensure!(
                returns
                    == BTreeMap::from([
                        ("first".into(), json!(true)),
                        ("late".into(), json!(true)),
                        ("firstAcceptedResult".into(), json!(true)),
                        ("firstCodeResult".into(), json!("101")),
                        ("lateAcceptedResult".into(), json!(false)),
                        ("lateCodeResult".into(), json!("303")),
                        ("firstRemaining".into(), json!(false)),
                        ("lateRemaining".into(), json!(true)),
                        ("retainedAccepted".into(), json!(false)),
                        ("retainedCode".into(), json!("303")),
                    ]),
                "root record-valued Map returned a different lifecycle"
            );
            let late = inputs.insert(
                "lateId".into(),
                json!({"kind":"bytes", "values":&last[..32]}),
            );
            ensure!(
                crate::prepare(
                    &plan,
                    &inputs,
                    &initial.data,
                    &snapshot.state.parameters,
                    address
                )
                .is_err(),
                "wrong-width key unexpectedly passed native admission"
            );
            inputs.insert("lateId".into(), late.context("missing retained key input")?);
            let call = funded
                .call(&update, &mut Some(state), &parameters, inputs)
                .await?;
            let observed: ContractState<Db> = native_decode(&call.contract_state)?;
            ensure!(
                observed.data == execution.after.state,
                "finalized state differs from preparation"
            );
            let StateValue::Array(slots) = observed.data.get_ref() else {
                anyhow::bail!("expected root state slots");
            };
            let Some(StateValue::Map(receipts)) = slots.get(0) else {
                anyhow::bail!("expected root record-valued Map");
            };
            let key = AlignedValue::new(
                FabValue(vec![
                    ValueAtom::from([7u8].as_slice()),
                    ValueAtom::from(last.as_slice()),
                ]),
                Alignment::concat(&[
                    Alignment::singleton(AlignmentAtom::Bytes { length: 1 }),
                    Alignment::singleton(AlignmentAtom::Bytes { length: 33 }),
                ]),
            )
            .context("invalid expected key alignment")?;
            let value = AlignedValue::concat(&[
                crate::field_value(Fr::from(0u64)),
                crate::field_value(Fr::from(303u64)),
            ]);
            ensure!(
                receipts.size() == 1
                    && receipts.get(&key).is_some_and(|entry| match &*entry {
                        StateValue::Cell(cell) => **cell == value,
                        _ => false,
                    }),
                "finalized Map lost the exact late-byte key or record value"
            );
            let receipt = |value: &FinalizedReceipt| {
                json!({
                    "height": value.height, "blockHash": value.block_hash,
                    "finalizedHeight": value.finalized_height, "finalizedHash": value.finalized_hash,
                    "transactionId": value.transaction_id, "extrinsicHash": value.extrinsic_hash,
                    "extrinsicIndex": value.extrinsic_index,
                })
            };
            println!(
                "{}",
                json!({
                    "manifestSha256": manifest,
                    "k": circuit.k(),
                    "contractAddress": target.contract_address(),
                    "deploy": receipt(&deployment),
                    "call": receipt(&call),
                    "returns": returns,
                    "stateSha256": hex::encode(Sha256::digest(&call.contract_state)),
                    "stateBytes": call.contract_state.len(),
                    "exactLateByteKeyAndRecordValue": true,
                    "wrongWidthRejectedBeforeSubmission": true,
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires authenticated NativeSet bundles and the funded development node"]
    fn native_sets_finalize_on_funded_ledger() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use base_crypto::{fab::AlignedValue, hash::HashOutput};
        use coin_structure::contract::ContractAddress;
        use futures::executor::block_on;
        use onchain_runtime::state::{ContractState, StateValue};
        use rand::{SeedableRng, rngs::StdRng};
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::{curve::Fr, proofs::Zkir};

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let directory = setting("NOCTIUM_NATIVE_SET_BUNDLES")?;
            let pins: BTreeMap<String, String> =
                serde_json::from_str(&setting("NOCTIUM_NATIVE_SET_MANIFESTS")?)?;
            let entries = ["inspect", "update"];
            let mut bundles = Vec::new();
            let mut plans = BTreeMap::new();
            let mut circuits = BTreeMap::new();
            let mut degrees = BTreeMap::new();
            for entry in entries {
                let pin = pins.get(entry).context("missing operation manifest pin")?;
                let bundle = artifacts::verify(&Path::new(&directory).join(entry), Some(pin))?;
                let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
                let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
                degrees.insert(entry, circuit.k());
                plans.insert(entry, plan);
                circuits.insert(entry, circuit);
                bundles.push(bundle);
            }
            let cache = ProofCache::new(
                setting("NOCTIUM_NATIVE_SET_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(&setting("NOCTIUM_NATIVE_SET_NODE")?, &cache)
                .await?;
            let mut parameters = BTreeMap::new();
            for (entry, degree) in &degrees {
                parameters.insert(*entry, cache.parameters(*degree).await?);
            }
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(bundles)?,
                br#"{"state":{"registered":[],"groups":[]}}"#,
                ttl,
                &mut rng,
            )?;
            let update = target.operation("update", &parameters["update"], ttl)?;
            let inspect = target.operation("inspect", &parameters["inspect"], ttl)?;
            let (deployed, deployment) = funded.deploy(&target, "update").await?;
            let mut current = Some(deployed);
            let address = ContractAddress(HashOutput(
                hex::decode(target.contract_address())?
                    .try_into()
                    .map_err(|_| anyhow::anyhow!("invalid fixture address"))?,
            ));
            let update_inputs = |adding, removing, clearing| {
                BTreeMap::from([
                    ("bucket".into(), json!("7")),
                    ("tag".into(), json!({"kind":"bytes", "values":vec![7u8; 32]})),
                    ("adding".into(), json!(adding)),
                    ("removing".into(), json!(removing)),
                    ("clearing".into(), json!(clearing)),
                ])
            };
            let inspect_inputs = |bucket: u64, enabled: bool| {
                BTreeMap::from([
                    ("bucket".into(), json!(bucket.to_string())),
                    ("enabled".into(), json!(enabled)),
                ])
            };
            let update_returns = |present, group_present, total: u64, group_size: u64| {
                BTreeMap::from([
                    ("containsTag".into(), json!(present)),
                    ("groupContainsTag".into(), json!(group_present)),
                    ("totalTags".into(), json!(total.to_string())),
                    ("groupTags".into(), json!(group_size.to_string())),
                    ("isEmpty".into(), json!(total == 0)),
                ])
            };
            let check_state = |receipt: &FinalizedReceipt,
                               expected_root: &[[u8; 32]],
                               expected_groups: &[(u64, Vec<[u8; 32]>)]|
             -> anyhow::Result<ContractState<Db>> {
                let state: ContractState<Db> = native_decode(&receipt.contract_state)?;
                let StateValue::Array(slots) = state.data.get_ref() else {
                    anyhow::bail!("expected native state slots");
                };
                let Some(StateValue::Map(root)) = slots.get(0) else {
                    anyhow::bail!("expected root Set in slot 0");
                };
                ensure!(root.size() == expected_root.len(), "root Set differs");
                for member in expected_root {
                    ensure!(
                        matches!(root.get(&AlignedValue::from(*member)), Some(value) if matches!(&*value, StateValue::Null)),
                        "root Set member differs"
                    );
                }
                let Some(StateValue::Map(groups)) = slots.get(1) else {
                    anyhow::bail!("expected nested Set map in slot 1");
                };
                ensure!(groups.size() == expected_groups.len(), "nested Set keys differ");
                for (bucket, members) in expected_groups {
                    let key = crate::field_value(Fr::from(*bucket));
                    let Some(group) = groups.get(&key) else {
                        anyhow::bail!("nested Set bucket is missing");
                    };
                    let StateValue::Map(group) = &*group else {
                        anyhow::bail!("expected nested Set");
                    };
                    ensure!(group.size() == members.len(), "nested Set differs");
                    for member in members {
                        ensure!(
                            matches!(group.get(&AlignedValue::from(*member)), Some(value) if matches!(&*value, StateValue::Null)),
                            "nested Set member differs"
                        );
                    }
                }
                Ok(state)
            };
            let simulate = |entry: &str,
                            state_bytes: &[u8],
                            inputs: &BTreeMap<String, Json>,
                            expected_returns: BTreeMap<String, Json>|
             -> anyhow::Result<crate::Execution> {
                let state: ContractState<Db> = native_decode(state_bytes)?;
                let execution = crate::prepare(
                    &plans[entry],
                    inputs,
                    &state.data,
                    &funded.node.sync()?.state.parameters,
                    address,
                )?;
                crate::check(&execution, &circuits[entry])?;
                ensure!(
                    execution.returns_json() == expected_returns,
                    "{entry} return values differ from Compact oracle semantics"
                );
                Ok(execution)
            };

            check_state(&deployment, &[], &[])?;
            ensure!(
                matches!(
                    inspect.prepare_call(
                        &mut current,
                        &parameters["inspect"],
                        inspect_inputs(9, true),
                        &mut rng
                    ),
                    Err(crate::proof::Error::InvalidPrivateInput)
                ) && current.is_some(),
                "active inspect of an absent bucket must reject preparation and retain the state token"
            );

            let tag = [7u8; 32];
            let updates = [
                (
                    update_inputs(true, false, false),
                    update_returns(true, true, 1, 1),
                    vec![tag],
                    vec![(7, vec![tag])],
                ),
                (
                    update_inputs(true, false, false),
                    update_returns(true, true, 1, 1),
                    vec![tag],
                    vec![(7, vec![tag])],
                ),
                (
                    update_inputs(false, true, false),
                    update_returns(false, false, 0, 0),
                    vec![],
                    vec![(7, vec![])],
                ),
                (
                    update_inputs(true, false, true),
                    update_returns(false, false, 0, 0),
                    vec![],
                    vec![(7, vec![])],
                ),
            ];
            let mut receipts = Vec::new();
            let mut before = deployment.contract_state.clone();
            for (index, (inputs, expected, root, groups)) in updates.into_iter().enumerate() {
                let execution = simulate("update", &before, &inputs, expected.clone())?;
                let receipt = funded
                    .call(&update, &mut current, &parameters["update"], inputs)
                    .await?;
                let observed = check_state(&receipt, &root, &groups)?;
                ensure!(
                    execution.after.state == observed.data,
                    "finalized Set state differs from checked native preparation"
                );
                if index == 1 {
                    ensure!(
                        receipt.contract_state == before,
                        "duplicate Set insertion changed finalized state"
                    );
                }
                before = receipt.contract_state.clone();
                receipts.push((expected, receipt));
            }

            let inspection_inputs = inspect_inputs(7, true);
            let inspection = simulate(
                "inspect",
                &before,
                &inspection_inputs,
                BTreeMap::from([
                    ("registeredEmpty".into(), json!(true)),
                    ("groupsEmpty".into(), json!(false)),
                    ("selectedEmpty".into(), json!(true)),
                ]),
            )?;
            let read = funded
                .call(
                    &inspect,
                    &mut current,
                    &parameters["inspect"],
                    inspection_inputs,
                )
                .await?;
            let observed = check_state(&read, &[], &[(7, vec![])])?;
            ensure!(
                inspection.after.state == observed.data && read.contract_state == before,
                "inspection changed or misread finalized Set state"
            );
            println!(
                "{}",
                json!({
                    "contractAddress": target.contract_address(),
                    "deployment": [deployment.height, deployment.transaction_id],
                    "calls": receipts.iter().map(|(returns, receipt)| json!({
                        "height": receipt.height,
                        "transactionId": receipt.transaction_id,
                        "checkedSourceReturns": returns,
                    })).chain(std::iter::once(json!({
                        "height": read.height,
                        "transactionId": read.transaction_id,
                        "checkedSourceReturns": inspection.returns_json(),
                    }))).collect::<Vec<_>>(),
                    "environment": ["NOCTIUM_NATIVE_SET_NODE", "NOCTIUM_NATIVE_SET_BUNDLES",
                        "NOCTIUM_NATIVE_SET_MANIFESTS", "NOCTIUM_NATIVE_SET_PARAMETER_CACHE"],
                    "scope": "root and nested Bytes32 Set insertion, duplicate, membership, size, emptiness, removal, reset, and absent active path rejection",
                    "absentActiveBucketRejectedBeforeSubmission": true,
                    "duplicateInsertionUnchanged": true,
                    "rootAndNestedSetsMatchedExactAfterState": true,
                    "compactOracle": "tests/compact/NativeSet.compact",
                    "compactComparison": "expected return values and state semantics; no Compact-generated bundle executed",
                    "bundleManifestSha256": pins,
                    "k": degrees,
                })
            );
            Ok(())
        })
    }

    #[test]
    fn ancestry_and_funding_snapshot_mismatches_fail_closed() {
        assert!(validate_parent(Some("a"), "b").is_err());
        validate_parent(Some("a"), "a").unwrap();
        assert!(validate_finalized_tip(Some("branch"), "finalized").is_err());
        validate_finalized_tip(Some("finalized"), "finalized").unwrap();
        let state = LedgerState::<Db>::new("undeployed");
        let snapshot = Snapshot {
            chain: ChainIdentity {
                network_id: "undeployed".into(),
                genesis: "1".repeat(64),
                spec_version: 2001100,
                transaction_version: 4,
                profile: crate::profile::NAME.into(),
            },
            finalized_hash: "2".repeat(64),
            height: 10,
            state: state.clone(),
            block: BlockContext::default(),
        };
        let mut cache = ReplayCache {
            dust: DustLocalState::new(state.parameters.dust),
            state,
            height: 10,
            hash: "2".repeat(64),
            block: BlockContext::default(),
        };
        assert!(cache_matches(&cache, &snapshot));
        cache.hash = "3".repeat(64);
        assert!(!cache_matches(&cache, &snapshot));
        cache.hash = snapshot.finalized_hash.clone();
        cache.height += 1;
        assert!(!cache_matches(&cache, &snapshot));
        cache.height = snapshot.height;
        cache.block.tblock_err += 1;
        assert!(!cache_matches(&cache, &snapshot));
        cache.block = snapshot.block.clone();
        cache.state.network_id = "wrong".into();
        assert!(!cache_matches(&cache, &snapshot));
    }
    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires authenticated NativeCellReset bundles and the funded development node"]
    fn cell_resets_finalize_canonical_defaults_on_ledger() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use futures::executor::block_on;
        use onchain_runtime::state::ContractState;
        use rand::{SeedableRng, rngs::StdRng};
        use sha2::Digest;
        use std::{env, path::Path};
        use transient_crypto::proofs::Zkir;

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let directory = setting("NOCTIUM_CELL_RESET_BUNDLES")?;
            let pins: BTreeMap<String, String> =
                serde_json::from_str(&setting("NOCTIUM_CELL_RESET_MANIFESTS")?)?;
            let bundle = |entry: &str| {
                let pin = pins.get(entry).context("missing operation manifest pin")?;
                Ok::<_, anyhow::Error>(
                    artifacts::verify(&Path::new(&directory).join(entry), Some(pin))?,
                )
            };
            let seed_bundle = bundle("seed")?;
            let clear_bundle = bundle("clear")?;
            let seed_k = IrSource::load(seed_bundle.file(Role::Circuit)?)?.k();
            let clear_k = IrSource::load(clear_bundle.file(Role::Circuit)?)?.k();
            let clear_plan: crate::Plan = serde_json::from_slice(clear_bundle.file(Role::Plan)?)?;
            let values = |amount: &str, nonce: &str, active: bool, memo: [u8; 4]| {
                BTreeMap::from([
                    ("amount".into(), json!(amount)),
                    ("nonce".into(), json!(nonce)),
                    ("active".into(), json!(active)),
                    ("memo".into(), json!({"kind":"bytes","values":memo})),
                ])
            };
            let expected_seeded = crate::create_state(&clear_plan, &values("42", "17", true, *b"seed"))?;
            let expected_cleared = crate::create_state(&clear_plan, &values("0", "0", false, [0; 4]))?;
            let cache = ProofCache::new(
                setting("NOCTIUM_CELL_RESET_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(&setting("NOCTIUM_CELL_RESET_NODE")?, &cache)
                .await?;
            let seed_parameters = cache.parameters(seed_k).await?;
            let clear_parameters = cache.parameters(clear_k).await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![seed_bundle, clear_bundle])?,
                br#"{"state":{"amount":"0","nonce":"0","active":false,"memo":{"kind":"bytes","values":[0,0,0,0]}}}"#,
                ttl,
                &mut rng,
            )?;
            let (deployed, deployment) = funded.deploy(&target, "clear").await?;
            let mut current = Some(deployed);
            let seed = target.operation("seed", &seed_parameters, ttl)?;
            let clear = target.operation("clear", &clear_parameters, ttl)?;
            let seeded = funded
                .call(&seed, &mut current, &seed_parameters, BTreeMap::new())
                .await?;
            let seeded_state: ContractState<Db> = native_decode(&seeded.contract_state)?;
            ensure!(
                seeded_state.data.get_ref() == expected_seeded.get_ref(),
                "finalized seed does not match the fixture's typed cells"
            );
            let inactive = funded
                .call(
                    &clear,
                    &mut current,
                    &clear_parameters,
                    BTreeMap::from([("enabled".into(), json!(false))]),
                )
                .await?;
            ensure!(
                inactive.contract_state == seeded.contract_state,
                "inactive clear changed finalized state"
            );
            let cleared = funded
                .call(
                    &clear,
                    &mut current,
                    &clear_parameters,
                    BTreeMap::from([("enabled".into(), json!(true))]),
                )
                .await?;

            let cleared_state: ContractState<Db> = native_decode(&cleared.contract_state)?;
            ensure!(
                cleared_state.data.get_ref() == expected_cleared.get_ref(),
                "finalized clear does not match the fixture's typed defaults"
            );

            println!(
                "{}",
                json!({
                    "contractAddress": target.contract_address(),
                    "deploymentHeight": deployment.height,
                    "receipts": [
                        json!({"stage":"deployment","height":deployment.height,"transactionId":deployment.transaction_id}),
                        json!({"stage":"seed","height":seeded.height,"transactionId":seeded.transaction_id}),
                        json!({"stage":"inactiveClear","height":inactive.height,"transactionId":inactive.transaction_id}),
                        json!({"stage":"activeClear","height":cleared.height,"transactionId":cleared.transaction_id}),
                    ],
                    "inactiveClearPreservedExactState": true,
                    "seedCellsMatchedFixture": true,
                    "resetCellsMatchedCanonicalFabDefaults": true,
                    "finalState": {
                        "contractStateSha256": hex::encode(sha2::Sha256::digest(&cleared.contract_state)),
                        "finalizedHash": cleared.finalized_hash,
                        "amount": "0",
                        "nonce": "0",
                        "active": false,
                        "memo": [0, 0, 0, 0],
                    },
                    "bundleManifestSha256": pins,
                    "k": {"seed":seed_k,"clear":clear_k},
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires authenticated QualifiedCoinCellReset bundles and the funded development node"]
    fn qualified_coin_cell_reset_finalizes_exact_zero_coin_and_preserves_marker() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use futures::executor::block_on;
        use onchain_runtime::state::ContractState;
        use rand::{SeedableRng, rngs::StdRng};
        use sha2::Digest;
        use std::{env, path::Path};
        use transient_crypto::proofs::Zkir;

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let directory = setting("NOCTIUM_QUALIFIED_COIN_RESET_BUNDLES")?;
            let pins: BTreeMap<String, String> =
                serde_json::from_str(&setting("NOCTIUM_QUALIFIED_COIN_RESET_MANIFESTS")?)?;
            let bundle = |entry: &str| {
                let pin = pins.get(entry).with_context(|| format!("missing {entry} manifest pin"))?;
                Ok::<_, anyhow::Error>(
                    artifacts::verify(&Path::new(&directory).join(entry), Some(pin))?,
                )
            };
            let clear_bundle = bundle("clear")?;
            let guarded_clear_bundle = bundle("guardedClear")?;
            let clear_k = IrSource::load(clear_bundle.file(Role::Circuit)?)?.k();
            let guarded_clear_k = IrSource::load(guarded_clear_bundle.file(Role::Circuit)?)?.k();
            let guarded_clear_plan: crate::Plan =
                serde_json::from_slice(guarded_clear_bundle.file(Role::Plan)?)?;
            let bytes = |byte: u8| json!({"kind":"bytes","values":vec![byte; 32]});
            let values = |nonce: u8, color: u8, value: &str, index: &str| {
                BTreeMap::from([
                    ("marker".into(), json!("37")),
                    (
                        "coinSlot".into(),
                        json!({"nonce":bytes(nonce),"color":bytes(color),"value":value,"mtIndex":index}),
                    ),
                ])
            };
            let initial_values = values(2, 1, "5", "42");
            let expected_initial = crate::create_state(&guarded_clear_plan, &initial_values)?;
            let expected_cleared = crate::create_state(
                &guarded_clear_plan,
                &values(0, 0, "0", "0"),
            )?;
            let state_config = serde_json::to_vec(&json!({"state":initial_values}))?;
            let cache = ProofCache::new(
                setting("NOCTIUM_QUALIFIED_COIN_RESET_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(
                &setting("NOCTIUM_QUALIFIED_COIN_RESET_NODE")?,
                &cache,
            )
            .await?;
            let guarded_clear_parameters = cache.parameters(guarded_clear_k).await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![clear_bundle, guarded_clear_bundle])?,
                &state_config,
                ttl,
                &mut rng,
            )?;
            let guarded_clear = target.operation("guardedClear", &guarded_clear_parameters, ttl)?;
            let (deployed, deployment) = funded.deploy(&target, "guardedClear").await?;
            let deployed_state: ContractState<Db> = native_decode(&deployment.contract_state)?;
            ensure!(
                deployed_state.data.get_ref() == expected_initial.get_ref(),
                "deployment did not preserve the marker and qualifying Coin constructor state"
            );
            let mut current = Some(deployed);
            let cleared = funded
                .call(
                    &guarded_clear,
                    &mut current,
                    &guarded_clear_parameters,
                    BTreeMap::from([("enabled".into(), json!(true))]),
                )
                .await?;
            let cleared_state: ContractState<Db> = native_decode(&cleared.contract_state)?;
            ensure!(
                cleared_state.data.get_ref() == expected_cleared.get_ref(),
                "active guardedClear did not finalize a typed zero Coin and preserve the adjacent marker"
            );
            println!(
                "{}",
                json!({
                    "contractAddress": target.contract_address(),
                    "receipts": [
                        json!({"stage":"deployment","height":deployment.height,"transactionId":deployment.transaction_id,"finalizedHash":deployment.finalized_hash}),
                        json!({"stage":"activeGuardedClear","height":cleared.height,"transactionId":cleared.transaction_id,"finalizedHash":cleared.finalized_hash}),
                    ],
                    "constructorCoin": {"nonceByte":2,"colorByte":1,"value":"5","mtIndex":"42"},
                    "finalState": {
                        "contractStateSha256": hex::encode(sha2::Sha256::digest(&cleared.contract_state)),
                        "finalizedHash": cleared.finalized_hash,
                        "marker": "37",
                        "coinSlot": {"nonce":vec![0u8; 32],"color":vec![0u8; 32],"value":"0","mtIndex":"0"},
                    },
                    "bundleManifestSha256": pins,
                    "k": {"clear":clear_k,"guardedClear":guarded_clear_k},
                    "environment": ["NOCTIUM_QUALIFIED_COIN_RESET_NODE","NOCTIUM_QUALIFIED_COIN_RESET_BUNDLES",
                        "NOCTIUM_QUALIFIED_COIN_RESET_MANIFESTS","NOCTIUM_QUALIFIED_COIN_RESET_PARAMETER_CACHE"],
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires authenticated SealedMapConstructor bundles and the funded development node"]
    fn sealed_map_constructor_finalizes_exact_seeded_map_and_read_only_get() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use futures::executor::block_on;
        use onchain_runtime::state::{ContractState, StateValue};
        use rand::{SeedableRng, rngs::StdRng};
        use sha2::Digest;
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::{curve::Fr, proofs::Zkir};

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let directory = setting("NOCTIUM_SEALED_MAP_FUNDED_BUNDLES")?;
            let pins: BTreeMap<String, String> =
                serde_json::from_str(&setting("NOCTIUM_SEALED_MAP_FUNDED_MANIFESTS")?)?;
            let bundle = |entry: &str| {
                let pin = pins
                    .get(entry)
                    .with_context(|| format!("missing {entry} manifest pin"))?;
                Ok::<_, anyhow::Error>(artifacts::verify(
                    &Path::new(&directory).join(entry),
                    Some(pin),
                )?)
            };
            let get_bundle = bundle("get")?;
            let touch_bundle = bundle("touch")?;
            let get_k = IrSource::load(get_bundle.file(Role::Circuit)?)?.k();
            let touch_k = IrSource::load(touch_bundle.file(Role::Circuit)?)?.k();
            let get_plan: crate::Plan = serde_json::from_slice(get_bundle.file(Role::Plan)?)?;
            let constructor_arguments = BTreeMap::from([
                ("key".into(), json!("5")),
                ("value".into(), json!("42")),
            ]);
            let expected_state = crate::construct_state(&get_plan, &constructor_arguments)?;
            let StateValue::Array(expected_slots) = expected_state.get_ref() else {
                anyhow::bail!("native constructor did not produce state slots")
            };
            let Some(StateValue::Map(expected_entries)) = expected_slots.get(0) else {
                anyhow::bail!("native constructor did not seed the sealed Map")
            };
            ensure!(
                expected_entries.size() == 1,
                "native constructor Map does not have exactly one entry"
            );
            let expected_key = crate::field_value(Fr::from(5u64));
            let expected_entry = expected_entries.get(&expected_key);
            let Some(StateValue::Cell(expected_value)) = expected_entry.as_deref() else {
                anyhow::bail!("native constructor omitted the seeded Map value")
            };
            ensure!(
                **expected_value == crate::field_value(Fr::from(42u64)),
                "native constructor seeded the wrong Map value"
            );
            ensure!(
                matches!(expected_slots.get(1), Some(StateValue::Map(map)) if map.size() == 0),
                "native constructor did not leave the neighboring sealed Map empty"
            );
            let state_config = br#"{"state":{"key":"5","value":"42"}}"#;
            let cache = ProofCache::new(
                setting("NOCTIUM_SEALED_MAP_FUNDED_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(
                &setting("NOCTIUM_SEALED_MAP_FUNDED_NODE")?,
                &cache,
            )
            .await?;
            let get_parameters = cache.parameters(get_k).await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![get_bundle, touch_bundle])?,
                state_config,
                ttl,
                &mut rng,
            )?;
            let get = target.operation("get", &get_parameters, ttl)?;
            let (deployed, deployment) = funded.deploy(&target, "get").await?;
            let deployed_state: ContractState<Db> = native_decode(&deployment.contract_state)?;
            ensure!(
                deployed_state.data.get_ref() == expected_state.get_ref(),
                "deployment state does not match the exact native constructor state"
            );

            let mut current = Some(deployed);
            let read = funded
                .call(
                    &get,
                    &mut current,
                    &get_parameters,
                    BTreeMap::from([("key".into(), json!("5"))]),
                )
                .await?;
            let final_state: ContractState<Db> = native_decode(&read.contract_state)?;
            ensure!(
                final_state.data.get_ref() == expected_state.get_ref(),
                "funded get changed the finalized constructor state"
            );

            let receipt = |stage: &str, item: &crate::client::FinalizedReceipt| {
                json!({
                    "stage": stage,
                    "chain": &item.chain,
                    "height": item.height,
                    "blockHash": item.block_hash,
                    "finalizedHeight": item.finalized_height,
                    "finalizedHash": item.finalized_hash,
                    "extrinsicHash": item.extrinsic_hash,
                    "extrinsicIndex": item.extrinsic_index,
                    "transactionId": item.transaction_id,
                    "intentId": item.intent_id,
                    "contractAddress": item.contract_address,
                    "contractStateSha256": hex::encode(sha2::Sha256::digest(&item.contract_state)),
                })
            };
            println!(
                "{}",
                json!({
                    "contractAddress": target.contract_address(),
                    "constructorArguments": {"key":"5","value":"42"},
                    "deploymentMatchedExactConstructState": true,
                    "getFinalizedStateMatchedExactConstructState": true,
                    "neighboringEmptySealedMapPreserved": true,
                    "receipts": [receipt("deployment", &deployment), receipt("get", &read)],
                    "bundleManifestSha256": pins,
                    "k": {"get":get_k,"touch":touch_k},
                    "environment": [
                        "NOCTIUM_SEALED_MAP_FUNDED_BUNDLES",
                        "NOCTIUM_SEALED_MAP_FUNDED_MANIFESTS",
                        "NOCTIUM_SEALED_MAP_FUNDED_PARAMETER_CACHE",
                        "NOCTIUM_SEALED_MAP_FUNDED_NODE",
                    ],
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires an authenticated RecordConstructor bundle and funded development node"]
    fn funded_record_constructor_deploys_and_reads_initialized_state() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use onchain_runtime::state::ContractState;
        use rand::{SeedableRng, rngs::StdRng};
        use sha2::Digest;
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::proofs::Zkir;

        futures::executor::block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let manifest = setting("NOCTIUM_RECORD_CONSTRUCTOR_FUNDED_MANIFEST_SHA256")?;
            let bundle = artifacts::verify(
                Path::new(&setting("NOCTIUM_RECORD_CONSTRUCTOR_FUNDED_BUNDLE")?),
                Some(&manifest),
            )?;
            let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
            ensure!(
                plan.entrypoint == "inspect",
                "unexpected record constructor entrypoint"
            );
            let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
            let degree = circuit.k();
            let cache = ProofCache::new(
                setting("NOCTIUM_RECORD_CONSTRUCTOR_FUNDED_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(
                &setting("NOCTIUM_RECORD_CONSTRUCTOR_FUNDED_NODE")?,
                &cache,
            )
            .await?;
            let parameters = cache.parameters(degree).await?;
            let owner = json!({"kind": "bytes", "values": ([1u8; 32])});
            let arguments = BTreeMap::from([
                ("owner".into(), owner.clone()),
                ("amount".into(), json!("19")),
                ("count".into(), json!("7")),
                ("active".into(), json!(true)),
            ]);
            let expected_state = crate::construct_state(&plan, &arguments)?;
            let state_config = serde_json::to_vec(&json!({"state": arguments}))?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![bundle])?,
                &state_config,
                ttl,
                &mut StdRng::from_entropy(),
            )?;
            let (deployed, deployment) = funded.deploy(&target, "inspect").await?;
            let state: ContractState<Db> = native_decode(&deployment.contract_state)?;
            ensure!(
                state.data.get_ref() == expected_state.get_ref(),
                "finalized deployment differs from the checked constructor"
            );
            let address = ContractAddress(HashOutput(
                hex::decode(target.contract_address())?
                    .try_into()
                    .map_err(|_| anyhow::anyhow!("invalid contract address"))?,
            ));
            let inputs = BTreeMap::from([("owner".into(), owner)]);
            let snapshot = funded.node.sync()?;
            let execution = crate::prepare(
                &plan,
                &inputs,
                &state.data,
                &snapshot.state.parameters,
                address,
            )?;
            ensure!(
                crate::check(&execution, &circuit)? == execution.activity_schedule,
                "constructor read does not match the native circuit"
            );
            let returns = execution.returns_json();
            ensure!(
                returns
                    == BTreeMap::from([
                        ("cellAmount".into(), json!("19")),
                        ("cellCount".into(), json!("7")),
                        ("cellActive".into(), json!(true)),
                        ("mapAmount".into(), json!("19")),
                        ("mapCount".into(), json!("7")),
                        ("mapActive".into(), json!(true)),
                    ]),
                "record constructor read returned unexpected fields"
            );
            let operation = target.operation("inspect", &parameters, ttl)?;
            let call = funded
                .call(&operation, &mut Some(deployed), &parameters, inputs)
                .await?;
            ensure!(
                call.contract_state == deployment.contract_state,
                "read changed the finalized record state"
            );
            let receipt = |item: &FinalizedReceipt| {
                json!({
                    "height": item.height,
                    "blockHash": item.block_hash,
                    "finalizedHash": item.finalized_hash,
                    "transactionId": item.transaction_id,
                    "stateSha256": hex::encode(sha2::Sha256::digest(&item.contract_state)),
                })
            };
            println!(
                "{}",
                json!({
                    "profile": crate::profile::NAME,
                    "genesis": funded.node.policy.genesis,
                    "contractAddress": target.contract_address(),
                    "bundleManifestSha256": manifest,
                    "degree": degree,
                    "deployment": receipt(&deployment),
                    "inspect": receipt(&call),
                    "checkedReturns": returns,
                    "stateUnchanged": true,
                })
            );
            Ok(())
        })
    }

    fn prepared_runtime(attempt: &str, address: &str) -> crate::host::Runtime {
        let context = serde_json::from_value(json!({"protocolVersion":1,"namespace":"qualification","baseRevision":"r0","attemptId":attempt,"capabilities":[{"id":"store","namespace":"qualification","keyPrefix":"claims/","operations":[crate::host::STAGE,crate::host::CAS]}],"operations":[],"providers":[],"commitCapability":"store"})).unwrap();
        let mut runtime = crate::host::Runtime::new(
            context,
            &std::collections::BTreeMap::new(),
            address.into(),
            "claim".into(),
        )
        .unwrap();
        runtime
            .stage(crate::host::Stage {
                abi_version: 1,
                operation: crate::host::STAGE.into(),
                capability: "store".into(),
                key: "claims/used".into(),
                ty: "Bool".into(),
                value: json!(true),
            })
            .unwrap();
        runtime.execution_finished(true).unwrap();
        runtime
    }
    struct LostAcknowledgement<'a>(&'a Node);
    impl crate::client::ChainAdapter for LostAcknowledgement<'_> {
        async fn snapshot(&self) -> std::result::Result<Snapshot, crate::client::HostFailure> {
            self.0.snapshot().await
        }
        async fn submit(
            &self,
            transaction: &crate::client::BoundTransaction,
        ) -> std::result::Result<crate::client::Submission, crate::client::HostFailure> {
            assert_eq!(
                self.0.submit(transaction).await?,
                crate::client::Submission::Broadcast
            );
            Ok(crate::client::Submission::Uncertain)
        }
        async fn observe(
            &self,
            transaction: &crate::client::BoundTransaction,
        ) -> std::result::Result<crate::client::Observation, crate::client::HostFailure> {
            self.0.observe(transaction).await
        }
    }
    #[test]
    #[ignore = "deploys and claims on the explicitly authorized isolated local development chain"]
    fn real_rust_only_funded_deploy_and_claim() {
        use crate::{
            artifacts,
            client::{
                BoundTransaction, ChainAdapter, ContractEvent, Error as ClientError, Submission,
                SubmissionAttempt,
            },
            proof::{LocalProver, PreparedProof},
        };
        use futures::{executor::block_on, future::pending};
        use rand::{SeedableRng, rngs::OsRng};
        block_on(async {
            let policy = NetworkPolicy {
                network_id: "undeployed".into(),
                genesis: "823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d".into(),
                spec_version: 2001100,
                transaction_version: 4,
                profile: crate::profile::NAME.into(),
                max_dust: 10u128.pow(22),
            };
            let mut node = Node::connect(
                "http://127.0.0.1:19944",
                policy.clone(),
                Duration::from_secs(30),
                64 * 1024 * 1024,
                10_000,
            )
            .unwrap();
            let mut seed = [0u8; 32];
            seed[31] = 1;
            node.attach_dust_seed(&seed).unwrap();
            let snapshot = node.sync().unwrap();
            node.metadata.fingerprint[0] ^= 1;
            assert_eq!(node.sync().err(), Some(Error::Metadata));
            node.metadata.fingerprint[0] ^= 1;
            let code = node.runtime_code.clone();
            node.runtime_code = "0".repeat(64);
            assert_eq!(node.sync().err(), Some(Error::Metadata));
            node.runtime_code = code;
            let cache = ProofCache::new(
                "/private/tmp/noctium-proof-params".into(),
                reqwest::Url::parse("https://srs.midnight.network/").unwrap(),
            )
            .unwrap();
            let material = cache.dust().await.unwrap();
            let dust_srs = cache.parameters(material.k()).await.unwrap();
            let bundle = artifacts::verify(
                std::path::Path::new(&std::env::var("NOCTIUM_TEST_BUNDLE").unwrap()),
                Some(&std::env::var("NOCTIUM_TEST_MANIFEST_SHA256").unwrap()),
            )
            .unwrap();
            let config = zeroize::Zeroizing::new(
                std::fs::read(std::env::var("NOCTIUM_TEST_PRIVATE_CONFIG").unwrap()).unwrap(),
            );
            let prepared = PreparedProof::from_config(
                &bundle,
                &config,
                snapshot.block.tblock.to_secs() + 1800,
                &mut OsRng,
            )
            .unwrap();
            let private = crate::parse_private_config(&config).unwrap();
            assert_eq!(private.negative_cases.len(), 5);
            let mut negative_claims = Vec::new();
            for case in &private.negative_cases {
                let mut modified: Json = serde_json::from_slice(&config).unwrap();
                modified["inputs"] = serde_json::to_value(&case.inputs).unwrap();
                let encoded = zeroize::Zeroizing::new(serde_json::to_vec(&modified).unwrap());
                assert!(
                    PreparedProof::from_config(
                        &bundle,
                        &encoded,
                        snapshot.block.tblock.to_secs() + 1800,
                        &mut OsRng
                    )
                    .is_err()
                );
                negative_claims.push(case.name.clone());
            }
            let mut wrong_genesis = policy.clone();
            wrong_genesis.genesis = "0".repeat(64);
            assert_eq!(
                Node::connect(
                    "http://127.0.0.1:19944",
                    wrong_genesis,
                    Duration::from_secs(30),
                    64 * 1024 * 1024,
                    10_000
                )
                .err(),
                Some(Error::Network)
            );
            let mut wrong_profile = policy.clone();
            wrong_profile.profile = "unsupported-profile".into();
            assert_eq!(
                Node::connect(
                    "http://127.0.0.1:19944",
                    wrong_profile,
                    Duration::from_secs(30),
                    64 * 1024 * 1024,
                    10_000
                )
                .err(),
                Some(Error::Policy)
            );
            let call_srs = cache.parameters(prepared.k()).await.unwrap();
            let call = prepared
                .prove(
                    &LocalProver::new(rand::rngs::StdRng::from_entropy()),
                    &call_srs,
                    1_048_576,
                    pending(),
                )
                .await
                .unwrap();
            let provider = builtin_zkir::LocalProvingProvider {
                rng: rand::rngs::StdRng::from_entropy(),
                resolver: &material,
                params: &dust_srs,
            };
            let (_, deploy) = prepared
                .deployment_intent()
                .unwrap()
                .prove(
                    crate::funding::CONTRACT_SEGMENT,
                    provider,
                    &snapshot.state.parameters.cost_model.runtime_cost_model,
                )
                .await
                .unwrap();
            let journal_dir = std::path::PathBuf::from(format!(
                "/private/tmp/noctium-native-journal-{}-{}",
                std::process::id(),
                snapshot.height
            ));
            let mut evidence = Vec::new();
            let mut accepted = Vec::new();
            for (kind, intent) in [
                (ContractEvent::Deploy, &deploy),
                (ContractEvent::Call, call.native()),
            ] {
                let funding = DevelopmentFunding::new(
                    &node,
                    &material,
                    &dust_srs,
                    crate::funding::FeePolicy {
                        max_dust: policy.max_dust,
                        margin_blocks: 3,
                        max_spends: 8,
                    },
                    rand::rngs::StdRng::from_entropy(),
                );
                let mut mismatched = node.sync().unwrap();
                mismatched.height += 1;
                assert!(
                    crate::client::FundingAdapter::fund(&funding, intent, &mismatched, &policy)
                        .await
                        .is_err()
                );
                assert!(funding.rng.borrow().is_some());
                let signing = ExplicitSeal::new(
                    |_: &crate::funding::UnsealedTransaction, p: &NetworkPolicy| {
                        p.genesis
                            == "823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d"
                            && p.max_dust <= 10u128.pow(22)
                    },
                    rand::rngs::StdRng::from_entropy(),
                );
                let bound =
                    BoundTransaction::prepare(intent, policy.clone(), &node, &funding, &signing)
                        .await
                        .unwrap();
                assert_eq!(bound.event(), kind);
                if kind == ContractEvent::Call {
                    use ledger::structure::{ContractAction, ProofVersioned, Transaction};
                    use storage::arena::Sp;
                    let current = node.sync().unwrap();
                    for mutation in ["proof", "publicCommitment", "network"] {
                        let mut invalid: crate::funding::SealedTransaction =
                            native_decode(bound.bytes()).unwrap();
                        let Transaction::Standard(stx) = &mut invalid else {
                            panic!("standard transaction")
                        };
                        if mutation == "network" {
                            stx.network_id = "wrong-network".into();
                        } else {
                            let mut intent =
                                (*stx.intents.get(&crate::funding::CONTRACT_SEGMENT).unwrap())
                                    .clone();
                            let mut actions: Vec<_> =
                                intent.actions.iter_deref().cloned().collect();
                            let ContractAction::Call(call) = &mut actions[0] else {
                                panic!("claim call")
                            };
                            let mut changed = (**call).clone();
                            if mutation == "proof" {
                                let ProofVersioned::V3(proof) = &mut changed.proof else {
                                    panic!("v3 proof")
                                };
                                proof.0[0] ^= 1;
                            } else {
                                changed.communication_commitment.0 +=
                                    transient_crypto::curve::Fr::from(1u64).0;
                            }
                            *call = Sp::new(changed);
                            intent.actions = actions.into();
                            stx.intents =
                                stx.intents.insert(crate::funding::CONTRACT_SEGMENT, intent);
                        }
                        assert!(
                            invalid
                                .well_formed(
                                    &current.state,
                                    WellFormedStrictness::default(),
                                    current.block.tblock
                                )
                                .is_err(),
                            "{mutation}"
                        );
                        let mut bytes = Vec::new();
                        serialize::tagged_serialize(&invalid, &mut bytes).unwrap();
                        let extrinsic = node.metadata.extrinsic(&bytes).unwrap();
                        let response = node.rpc.send(&json!({"jsonrpc":"2.0","id":1,"method":"author_submitExtrinsic","params":[format!("0x{}",hex::encode(extrinsic))]})).unwrap();
                        assert!(
                            response.get("error").is_some(),
                            "invalid {mutation} refused before pool acceptance"
                        );
                    }
                }
                let attempt_id = hex::encode(sha2::Sha256::digest(format!(
                    "{}:{}",
                    bound.transaction_id(),
                    snapshot.height
                )));
                let address = bound.contract_address().to_owned();
                let expected_bytes = bound.bytes().to_vec();
                let store =
                    journal::DirectoryJournal::new(&journal_dir, Duration::from_secs(2)).unwrap();
                let mut runtime = prepared_runtime(&attempt_id, &address);
                let mut attempt = SubmissionAttempt::new(bound, &attempt_id, &mut runtime).unwrap();
                assert_eq!(
                    attempt
                        .submit_once(&mut runtime, &LostAcknowledgement(&node), &store)
                        .await
                        .unwrap(),
                    Submission::Uncertain
                );
                assert_eq!(
                    attempt.cancel(&mut runtime, &store).await,
                    Err(ClientError::CancellationAfterBroadcast)
                );
                assert_eq!(
                    attempt.deadline(&mut runtime, &store).await,
                    Err(ClientError::Deadline)
                );
                drop((attempt, runtime, store));
                let store =
                    journal::DirectoryJournal::new(&journal_dir, Duration::from_secs(2)).unwrap();
                let mut attempt = SubmissionAttempt::recover(&store, &attempt_id)
                    .await
                    .unwrap();
                assert_eq!(attempt.transaction().bytes(), expected_bytes);
                let mut runtime = prepared_runtime(&attempt_id, &address);
                attempt.restore_runtime(&mut runtime).unwrap();
                // Retransmit only the durable sealed transaction after an unknown outcome.
                assert_eq!(
                    attempt
                        .submit_once(&mut runtime, &node, &store)
                        .await
                        .unwrap(),
                    Submission::Broadcast
                );
                let deadline = std::time::Instant::now() + Duration::from_secs(90);
                loop {
                    if let Some(receipt) = attempt
                        .observe_once(&mut runtime, &node, &store)
                        .await
                        .unwrap()
                    {
                        let crate::client::ObservedReceipt::Full(receipt) = receipt else {
                            panic!("expected a fully applied transaction");
                        };
                        let transaction = attempt.transaction();
                        for mutation in [
                            "genesis",
                            "profile",
                            "transaction",
                            "intent",
                            "address",
                            "state",
                            "finality",
                        ] {
                            let mut wrong = receipt.clone();
                            match mutation {
                                "genesis" => wrong.chain.genesis = "0".repeat(64),
                                "profile" => wrong.chain.profile = "wrong-profile".into(),
                                "transaction" => wrong.transaction_id = "0".repeat(64),
                                "intent" => wrong.intent_id = "0".repeat(64),
                                "address" => wrong.contract_address = "0".repeat(64),
                                "state" => wrong.contract_state.push(0),
                                "finality" => wrong.finalized_height = wrong.height - 1,
                                _ => unreachable!(),
                            }
                            assert!(transaction.check_receipt(&wrong).is_err(), "{mutation}");
                        }
                        let state_digest =
                            hex::encode(sha2::Sha256::digest(&receipt.contract_state));
                        evidence.push(json!({"event":format!("{kind:?}"),"height":receipt.height,"blockHash":receipt.block_hash,"transactionId":transaction.transaction_id(),"intentId":transaction.intent_id(),"contractAddress":transaction.contract_address(),"contractStateBytes":receipt.contract_state.len(),"contractStateSha256":state_digest,"extrinsicHash":receipt.extrinsic_hash,"extrinsicIndex":receipt.extrinsic_index}));
                        eprintln!(
                            "native Rust {:?} finalized at height {}, transaction {}, contract {}, exact state SHA256 {}",
                            kind,
                            receipt.height,
                            transaction.transaction_id(),
                            transaction.contract_address(),
                            state_digest
                        );
                        break;
                    }
                    assert!(std::time::Instant::now() < deadline);
                    std::thread::sleep(Duration::from_millis(500));
                }
                accepted.push((attempt, runtime));
            }
            let store =
                journal::DirectoryJournal::new(&journal_dir, Duration::from_secs(2)).unwrap();
            let (mut deployment, mut runtime) = accepted.remove(0);
            let deployment_id = deployment.record().identity().attempt_id.clone();
            let receipt = deployment
                .commit_private(&mut runtime, &store, 7)
                .await
                .unwrap();
            assert!(receipt.committed);
            assert_eq!(store.revision("qualification").unwrap(), "r1");
            assert_eq!(
                store
                    .private_value("qualification", "claims/used")
                    .unwrap()
                    .unwrap()["value"],
                true
            );
            assert!(
                deployment
                    .commit_private(&mut runtime, &store, 7)
                    .await
                    .unwrap()
                    .committed
            );
            let (mut claim, mut runtime) = accepted.remove(0);
            let claim_receipt = claim.commit_private(&mut runtime, &store, 8).await.unwrap();
            assert!(!claim_receipt.committed);
            assert_eq!(claim_receipt.revision, "r1");
            assert_eq!(store.revision("qualification").unwrap(), "r1");
            drop(deployment);
            let mut recovered = SubmissionAttempt::recover(&store, &deployment_id)
                .await
                .unwrap();
            let mut runtime =
                prepared_runtime(&deployment_id, recovered.transaction().contract_address());
            recovered.restore_runtime(&mut runtime).unwrap();
            assert_eq!(
                recovered
                    .commit_private(&mut runtime, &store, 9)
                    .await
                    .err(),
                Some(ClientError::Receipt)
            );
            recovered
                .observe_once(&mut runtime, &node, &store)
                .await
                .unwrap()
                .unwrap();
            assert!(
                recovered
                    .commit_private(&mut runtime, &store, 9)
                    .await
                    .unwrap()
                    .committed
            );
            assert_eq!(store.revision("qualification").unwrap(), "r1");
            // The exact accepted transaction stays an idempotent client retry. A raw
            // duplicate submission is refused by the native pool and never rebuilt.
            assert_eq!(
                node.submit(&claim.transaction()).await.unwrap(),
                Submission::Broadcast
            );
            let replay = node.rpc.send(&json!({"jsonrpc":"2.0","id":1,"method":"author_submitExtrinsic","params":[format!("0x{}",hex::encode(node.metadata.extrinsic(claim.transaction().bytes()).unwrap()))]})).unwrap();
            assert!(replay.get("error").is_some());
            let state: onchain_runtime::state::ContractState<Db> =
                native_decode(claim.transaction().expected_state()).unwrap();
            let plan: crate::Plan =
                serde_json::from_slice(bundle.file(artifacts::Role::Plan).unwrap()).unwrap();
            let address = coin_structure::contract::ContractAddress(HashOutput(
                hex::decode(claim.transaction().contract_address())
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ));
            assert!(
                crate::prepare(
                    &plan,
                    &private.inputs,
                    &state.data,
                    &node.sync().unwrap().state.parameters,
                    address
                )
                .is_err()
            );
            if let Ok(path) = std::env::var("NOCTIUM_TEST_EVIDENCE") {
                let final_snapshot = node.sync().unwrap();
                let mut final_state = Vec::new();
                serialize::tagged_serialize(&final_snapshot.state, &mut final_state).unwrap();
                let value = json!({"runtimeCodeHash":node.runtime_code,"metadataVersion":16,"metadataSha256":hex::encode(&node.metadata.fingerprint),"contractParametersSha256":call_srs.sha256(),"dustParametersSha256":dust_srs.sha256(),"finalReplayHeight":final_snapshot.height,"finalReplayBlockHash":final_snapshot.finalized_hash,"nativeLedgerStateTaggedSha256":hex::encode(sha2::Sha256::digest(&final_state)),"nativeStoredLedgerRootMatchedRuntime":true,"schemaVersion":1,"scope":"native deploy and claim, lost acknowledgement, durable restart, byte-identical retry, postbroadcast cancellation/deadline, exact finalized state, committed private CAS and accepted-chain private CAS conflict","profile":crate::profile::NAME,"manifestSha256":std::env::var("NOCTIUM_TEST_MANIFEST_SHA256").unwrap(),"genesis":policy.genesis,"specVersion":policy.spec_version,"transactionVersion":policy.transaction_version,"journalDirectory":journal_dir,"negativeClaims":negative_claims,"invalidNativeProofRefused":true,"alteredPublicCommitmentRefused":true,"wrongNetworkRefused":true,"wrongGenesisRefused":true,"wrongProfileRefused":true,"rawReplayRefused":true,"claimedStateReplayRefused":true,"wrongReceiptFieldsRefused":true,"metadataMismatchRefused":true,"runtimeCodeMismatchRefused":true,"fundingCacheMismatchRefusedBeforeEntropyUse":true,"records":evidence});
                std::fs::write(path, serde_json::to_vec_pretty(&value).unwrap()).unwrap();
            }
        });
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires authenticated NativeMapReset bundles and the funded development node"]
    fn native_map_reset_finalizes_an_exact_empty_state() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use futures::executor::block_on;
        use onchain_runtime::state::{ContractState, StateValue};
        use rand::{SeedableRng, rngs::StdRng};
        use std::{env, path::Path};
        use storage::storage::HashMap;
        use transient_crypto::{curve::Fr, proofs::Zkir};

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let directory = setting("NOCTIUM_MAP_RESET_BUNDLES")?;
            let pins: BTreeMap<String, String> =
                serde_json::from_str(&setting("NOCTIUM_MAP_RESET_MANIFESTS")?)?;
            let bundle = |operation: &str| {
                let pin = pins
                    .get(operation)
                    .with_context(|| format!("missing {operation} manifest pin"))?;
                Ok::<_, anyhow::Error>(artifacts::verify(
                    &Path::new(&directory).join(operation),
                    Some(pin),
                )?)
            };
            let seed_bundle = bundle("seed")?;
            let clear_bundle = bundle("clearMap")?;
            let seed_degree = IrSource::load(seed_bundle.file(Role::Circuit)?)?.k();
            let clear_degree = IrSource::load(clear_bundle.file(Role::Circuit)?)?.k();
            let cache = ProofCache::new(
                setting("NOCTIUM_MAP_RESET_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(&setting("NOCTIUM_MAP_RESET_NODE")?, &cache)
                .await?;
            let seed_parameters = cache.parameters(seed_degree).await?;
            let clear_parameters = cache.parameters(clear_degree).await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![seed_bundle, clear_bundle])?,
                br#"{"state":{"values":[]}}"#,
                ttl,
                &mut rng,
            )?;
            let seed = target.operation("seed", &seed_parameters, ttl)?;
            let clear_map = target.operation("clearMap", &clear_parameters, ttl)?;
            let (deployed, deployment) = funded.deploy(&target, "seed").await?;
            let mut current = Some(deployed);
            let seed_inputs = |key: u64, amount: u64| {
                BTreeMap::from([
                    ("key".into(), json!(key.to_string())),
                    ("amount".into(), json!(amount.to_string())),
                ])
            };
            let first = funded
                .call(&seed, &mut current, &seed_parameters, seed_inputs(1, 19))
                .await?;
            let seeded = funded
                .call(&seed, &mut current, &seed_parameters, seed_inputs(2, 23))
                .await?;
            let seeded_state: ContractState<Db> = native_decode(&seeded.contract_state)?;
            let StateValue::Array(slots) = seeded_state.data.get_ref() else {
                anyhow::bail!("expected native state slots")
            };
            let Some(StateValue::Map(values)) = slots.get(0) else {
                anyhow::bail!("expected seeded Map")
            };
            ensure!(values.size() == 2, "expected two seeded Map entries");
            for (key, expected) in [(1u64, 19u64), (2, 23)] {
                let entry = values.get(&crate::field_value(Fr::from(key)));
                let Some(StateValue::Cell(value)) = entry.as_deref() else {
                    anyhow::bail!("expected seeded Map cell for key {key}")
                };
                ensure!(
                    **value == crate::field_value(Fr::from(expected)),
                    "seeded Map value differs for key {key}"
                );
            }

            let cleared = funded
                .call(
                    &clear_map,
                    &mut current,
                    &clear_parameters,
                    BTreeMap::from([("key".into(), json!("1"))]),
                )
                .await?;
            let final_state: ContractState<Db> = native_decode(&cleared.contract_state)?;
            let expected_empty: StateValue<Db> =
                StateValue::Array(vec![StateValue::Map(HashMap::new())].into());
            ensure!(
                *final_state.data.get_ref() == expected_empty,
                "clearMap did not finalize the exact empty Map state"
            );
            println!(
                "{}",
                json!({
                    "contractAddress": target.contract_address(),
                    "deploymentHeight": deployment.height,
                    "seedHeights": [first.height, seeded.height],
                    "clearMapHeight": cleared.height,
                    "transactionIds": [first.transaction_id, seeded.transaction_id, cleared.transaction_id],
                    "seededEntries": 2,
                    "finalEntries": 0,
                    "exactEmptyStateAccepted": true,
                    "bundleManifestSha256": pins,
                    "k": {"seed": seed_degree, "clearMap": clear_degree},
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires the authenticated RecordMapCollections update bundle and funded development node"]
    fn record_map_collections_finalize_distinct_keys_noop_and_reset() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use futures::executor::block_on;
        use onchain_runtime::state::{ChargedState, ContractState, StateValue};
        use rand::{SeedableRng, rngs::StdRng};
        use serde_json::json;
        use sha2::Digest;
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::proofs::Zkir;

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let endpoint = setting("NOCTIUM_RECORD_MAP_COLLECTIONS_NODE")?;
            ensure!(
                endpoint == "http://127.0.0.1:19944",
                "RecordMapCollections requires the authorized loopback node on port 19944"
            );
            let manifest = setting("NOCTIUM_RECORD_MAP_COLLECTIONS_MANIFEST")?;
            let bundle = artifacts::verify(
                Path::new(&setting("NOCTIUM_RECORD_MAP_COLLECTIONS_BUNDLE")?),
                Some(&manifest),
            )?;
            let bundle_digest = bundle
                .authenticated_manifest_sha256()
                .context("verified bundle omitted its authenticated manifest pin")?
                .to_owned();
            let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
            ensure!(plan.entrypoint == "update", "expected RecordMapCollections.update");
            let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
            let degree = circuit.k();
            let cache = ProofCache::new(
                setting("NOCTIUM_RECORD_MAP_COLLECTIONS_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let parameters = cache.parameters(degree).await?;
            let funded = FundedLedgerTest::connect(&endpoint, &cache).await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![bundle])?,
                br#"{"state":{"scalars":[],"records":[]}}"#,
                ttl,
                &mut rng,
            )?;
            let update = target.operation("update", &parameters, ttl)?;
            let empty_config = BTreeMap::from([
                ("scalars".to_owned(), json!([])),
                ("records".to_owned(), json!([])),
            ]);
            let mut model_state = crate::create_state(&plan, &empty_config)?;
            let (deployed, deployment) = funded.deploy(&target, "update").await?;
            let deployed_state: ContractState<Db> = native_decode(&deployment.contract_state)?;
            ensure!(
                deployment.contract_address == target.contract_address(),
                "deployment receipt belongs to another contract address"
            );
            ensure!(
                deployed_state.data.get_ref() == model_state.get_ref(),
                "deployed RecordMapCollections state differs from the exact empty constructor state"
            );
            let mut current = Some(deployed);
            let address = ContractAddress(HashOutput(
                hex::decode(target.contract_address())?
                    .try_into()
                    .map_err(|_| anyhow::anyhow!("invalid target contract address"))?,
            ));

            let call_inputs = |active, amount: u16, adding, clear| {
                BTreeMap::from([
                    ("active".into(), json!(active)),
                    ("amount".into(), json!(amount.to_string())),
                    ("adding".into(), json!(adding)),
                    ("clear".into(), json!(clear)),
                ])
            };
            let simulate = |before: &ChargedState<Db>,
                            inputs: &BTreeMap<String, Json>,
                            expected_size: u64| {
                let snapshot = funded.node.sync()?;
                let execution = crate::prepare(
                    &plan,
                    inputs,
                    before,
                    &snapshot.state.parameters,
                    address,
                )?;
                ensure!(
                    crate::check(&execution, &circuit)? == execution.activity_schedule,
                    "native RecordMapCollections relation did not check"
                );
                let expected_returns = BTreeMap::from([
                    ("scalarSize".into(), json!(expected_size.to_string())),
                    ("scalarEmpty".into(), json!(expected_size == 0)),
                    ("recordSize".into(), json!(expected_size.to_string())),
                    ("recordEmpty".into(), json!(expected_size == 0)),
                ]);
                ensure!(
                    execution.returns_json() == expected_returns,
                    "native RecordMapCollections return values differ from the expected size and emptiness"
                );
                Ok::<_, anyhow::Error>(execution)
            };
            let verify_receipt = |bound: &BoundTransaction,
                                  receipt: &FinalizedReceipt,
                                  execution: &crate::Execution|
             -> anyhow::Result<()> {
                bound.check_receipt(receipt)?;
                ensure!(
                    receipt.chain.genesis == DEVELOPMENT_GENESIS,
                    "finalized receipt belongs to another genesis"
                );
                ensure!(
                    receipt.contract_address == target.contract_address(),
                    "finalized receipt belongs to another contract address"
                );
                ensure!(
                    receipt.contract_state == bound.expected_state(),
                    "finalized receipt bytes differ from the bound expected state"
                );
                let decoded: ContractState<Db> = native_decode(&receipt.contract_state)?;
                ensure!(
                    decoded.data.get_ref() == execution.after.state.get_ref(),
                    "decoded finalized RecordMap data differs from checked native execution"
                );
                Ok(())
            };
            let receipt_record = |receipt: &FinalizedReceipt| {
                json!({
                    "height": receipt.height,
                    "finalizedHeight": receipt.finalized_height,
                    "blockHash": receipt.block_hash,
                    "finalizedHash": receipt.finalized_hash,
                    "extrinsicHash": receipt.extrinsic_hash,
                    "transactionId": receipt.transaction_id,
                    "intentId": receipt.intent_id,
                    "stateBytes": receipt.contract_state.len(),
                    "stateSha256": hex::encode(sha2::Sha256::digest(&receipt.contract_state)),
                })
            };

            let mut receipts = Vec::new();
            let mut previous_receipt_state = deployment.contract_state.clone();
            let mut reset_finalized = false;
            for (active, adding, clear, size) in [
                (true, true, false, 1u64),
                (false, true, false, 2),
                (false, false, false, 2),
                (true, false, true, 0),
            ] {
                let inputs = call_inputs(active, 513, adding, clear);
                let execution = simulate(&model_state, &inputs, size)?;
                let (bound, receipt) = funded
                    .call_with_bound(&update, &mut current, &parameters, inputs)
                    .await?;
                verify_receipt(&bound, &receipt, &execution)?;
                if !adding && !clear {
                    ensure!(
                        receipt.contract_state == previous_receipt_state,
                        "inactive update changed finalized state bytes"
                    );
                }
                if clear {
                    let reset_state: ContractState<Db> =
                        native_decode(&receipt.contract_state)?;
                    let StateValue::Array(slots) = reset_state.data.get_ref() else {
                        anyhow::bail!("expected finalized native state slots")
                    };
                    ensure!(
                        slots.len() == 2
                            && matches!(slots.get(0), Some(StateValue::Map(map)) if map.size() == 0)
                            && matches!(slots.get(1), Some(StateValue::Map(map)) if map.size() == 0),
                        "reset did not finalize two empty root Maps"
                    );
                    reset_finalized = true;
                }
                let checked_returns = execution.returns_json();
                model_state = execution.after.state;
                previous_receipt_state = receipt.contract_state.clone();
                let mut record = receipt_record(&receipt);
                record["checkedReturns"] = json!(checked_returns);
                receipts.push(record);
            }
            ensure!(reset_finalized, "reset receipt was not checked");

            println!(
                "{}",
                json!({
                    "profile": crate::profile::NAME,
                    "genesis": funded.node.policy.genesis,
                    "contractAddress": target.contract_address(),
                    "bundleManifestSha256": bundle_digest,
                    "degree": degree,
                    "deployment": receipt_record(&deployment),
                    "calls": receipts,
                    "distinctKeysDifferByActiveBool": true,
                    "inactiveUpdatePreservedExactFinalizedBytes": true,
                    "resetFinalizedBothMapsEmpty": true,
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "submits funded NestedRecordMap calls to the authorized isolated localnet"]
    fn nested_record_map_finalizes_and_preserves_outer_and_inner_siblings() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use futures::executor::block_on;
        use onchain_runtime::state::{ContractState, StateValue};
        use rand::{SeedableRng, rngs::StdRng};
        use sha2::Digest;
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::proofs::Zkir;

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let endpoint = setting("NOCTIUM_NESTED_RECORD_MAP_NODE")?;
            ensure!(
                endpoint == "http://127.0.0.1:19944",
                "NestedRecordMap requires the authorized loopback node on port 19944"
            );
            let directory = setting("NOCTIUM_NESTED_RECORD_MAP_BUNDLES")?;
            let pins: BTreeMap<String, String> =
                serde_json::from_str(&setting("NOCTIUM_NESTED_RECORD_MAP_MANIFESTS")?)?;
            let entries = ["initializeOwner", "upsert", "lookup", "removeMemo"];
            let mut bundles = Vec::with_capacity(entries.len());
            let mut degrees = BTreeMap::new();
            let mut plans = BTreeMap::new();
            let mut circuits = BTreeMap::new();
            for entry in entries {
                let pin = pins
                    .get(entry)
                    .with_context(|| format!("missing {entry} manifest pin"))?;
                let bundle = artifacts::verify(&Path::new(&directory).join(entry), Some(pin))?;
                let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
                ensure!(plan.entrypoint == entry, "unexpected NestedRecordMap entrypoint");
                let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
                degrees.insert(entry.to_owned(), circuit.k());
                plans.insert(entry.to_owned(), plan);
                circuits.insert(entry.to_owned(), circuit);
                bundles.push(bundle);
            }

            let cache = ProofCache::new(
                setting("NOCTIUM_NESTED_RECORD_MAP_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(&endpoint, &cache).await?;
            let mut parameters = BTreeMap::new();
            for entry in entries {
                parameters.insert(entry, cache.parameters(degrees[entry]).await?);
            }
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(bundles)?,
                br#"{"state":{"memos":[]}}"#,
                ttl,
                &mut StdRng::from_entropy(),
            )?;
            let mut operations = BTreeMap::new();
            for entry in entries {
                operations.insert(entry, target.operation(entry, &parameters[entry], ttl)?);
            }
            let state_config = BTreeMap::from([("memos".to_owned(), json!([]))]);
            let mut model_state = crate::create_state(&plans["initializeOwner"], &state_config)?;
            let (deployed_state, deployment) =
                funded.deploy(&target, "initializeOwner").await?;
            let mut current = Some(deployed_state);
            let deployed: ContractState<Db> = native_decode(&deployment.contract_state)?;
            ensure!(
                deployment.contract_address == target.contract_address()
                    && deployed.data.get_ref() == model_state.get_ref(),
                "deployed NestedRecordMap state differs from its empty constructor"
            );
            let address = ContractAddress(HashOutput(
                hex::decode(target.contract_address())?
                    .try_into()
                    .map_err(|_| anyhow::anyhow!("invalid target contract address"))?,
            ));
            let bytes = |byte: u8| json!({"kind":"bytes", "values":vec![byte; 32]});
            let key_inputs = |owner: u8, active: bool, amount: u16| {
                BTreeMap::from([
                    ("owner".into(), bytes(owner)),
                    ("active".into(), json!(active)),
                    ("amount".into(), json!(amount.to_string())),
                ])
            };
            let init_inputs = |owner| BTreeMap::from([("owner".into(), bytes(owner))]);
            let mut steps: Vec<(&str, BTreeMap<String, Json>, BTreeMap<String, Json>)> = Vec::new();
            for owner in [1, 2] {
                steps.push(("initializeOwner", init_inputs(owner), BTreeMap::new()));
            }
            for (owner, active, value) in [(1, true, 11u16), (1, false, 22), (2, true, 99)] {
                let mut inputs = key_inputs(owner, active, 513);
                inputs.insert("value".into(), json!(value.to_string()));
                steps.push((
                    "upsert",
                    inputs,
                    BTreeMap::from([
                        ("presentBefore".into(), json!(false)),
                        ("presentAfter".into(), json!(true)),
                        ("storedValue".into(), json!(value.to_string())),
                    ]),
                ));
            }
            let mut lookup_inputs = key_inputs(1, true, 513);
            lookup_inputs.insert("shouldRead".into(), json!(true));
            steps.push((
                "lookup",
                lookup_inputs,
                BTreeMap::from([
                    ("present".into(), json!(true)),
                    ("storedValue".into(), json!("11")),
                ]),
            ));
            let mut removal_inputs = key_inputs(1, false, 513);
            removal_inputs.insert("removeIt".into(), json!(true));
            steps.push((
                "removeMemo",
                removal_inputs,
                BTreeMap::from([
                    ("presentBefore".into(), json!(true)),
                    ("presentAfter".into(), json!(false)),
                ]),
            ));

            let receipt_record = |receipt: &FinalizedReceipt| {
                json!({
                    "height": receipt.height,
                    "finalizedHeight": receipt.finalized_height,
                    "finalizedHash": receipt.finalized_hash,
                    "transactionId": receipt.transaction_id,
                    "stateBytes": receipt.contract_state.len(),
                    "stateSha256": hex::encode(sha2::Sha256::digest(&receipt.contract_state)),
                })
            };
            let mut calls = Vec::with_capacity(steps.len());
            for (entry, inputs, expected_returns) in steps {
                let snapshot = funded.node.sync()?;
                let execution = crate::prepare(
                    &plans[entry],
                    &inputs,
                    &model_state,
                    &snapshot.state.parameters,
                    address,
                )?;
                ensure!(
                    crate::check(&execution, &circuits[entry])? == execution.activity_schedule,
                    "native NestedRecordMap {entry} relation did not check"
                );
                ensure!(
                    execution.returns_json() == expected_returns,
                    "native NestedRecordMap {entry} returns differ from expectations"
                );
                let (bound, receipt) = funded
                    .call_with_bound(
                        &operations[entry],
                        &mut current,
                        &parameters[entry],
                        inputs,
                    )
                    .await?;
                bound.check_receipt(&receipt)?;
                ensure!(
                    receipt.chain.genesis == DEVELOPMENT_GENESIS
                        && receipt.contract_address == target.contract_address()
                        && receipt.contract_state == bound.expected_state(),
                    "finalized NestedRecordMap receipt has the wrong chain, contract, or state bytes"
                );
                let decoded: ContractState<Db> = native_decode(&receipt.contract_state)?;
                ensure!(
                    decoded.data.get_ref() == execution.after.state.get_ref(),
                    "decoded finalized NestedRecordMap state differs from checked native execution"
                );
                let mut record = receipt_record(&receipt);
                record["entrypoint"] = json!(entry);
                record["checkedReturns"] = json!(execution.returns_json());
                calls.push(record);
                model_state = execution.after.state;
            }

            let StateValue::Array(slots) = model_state.get_ref() else {
                anyhow::bail!("expected final NestedRecordMap state slots")
            };
            ensure!(
                slots.len() == 1
                    && matches!(slots.get(0), Some(StateValue::Map(owners)) if owners.size() == 2),
                "final state must retain exactly two initialized owners"
            );
            println!(
                "{}",
                json!({
                    "contractAddress": target.contract_address(),
                    "genesis": funded.node.policy.genesis,
                    "bundleManifestSha256": pins,
                    "k": degrees,
                    "deployment": receipt_record(&deployment),
                    "calls": calls,
                    "finalOwners": 2,
                    "nativeStateMatchedEveryFinalizedReceipt": true,
                    "ownerOneSiblingRemovalPreservedOwnerTwo": true,
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires the pinned development ledger and authenticated NativeUserCaller artifacts"]
    fn signed_unshielded_spend_authenticates_the_finalized_user_caller() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            funding::{CONTRACT_SEGMENT, one_intent},
            proof::{LocalProver, WitnessContractTarget},
            unshielded_caller::{Error as CallerError, validate_guaranteed_caller_offer},
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use coin_structure::coin::{NIGHT, UserAddress};
        use ledger::structure::{SigningKey, Utxo, UtxoSpend};
        use onchain_runtime::state::ContractState;
        use rand::{SeedableRng, rngs::StdRng};
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::proofs::Zkir;

        futures::executor::block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let bundle_root = setting("NOCTIUM_USER_CALLER_BUNDLE")?;
            let pin = setting("NOCTIUM_USER_CALLER_MANIFEST")?;
            let bundle = artifacts::verify(Path::new(&bundle_root), Some(&pin))?;
            let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
            let k = IrSource::load(bundle.file(Role::Circuit)?)?.k();
            let cache = ProofCache::new(
                setting("NOCTIUM_USER_CALLER_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(&setting("NOCTIUM_USER_CALLER_NODE")?, &cache)
                .await?;
            let parameters = cache.parameters(k).await?;

            let mut seed = zeroize::Zeroizing::new([0u8; 32]);
            seed[31] = 1;
            let derivation = "m/44'/2400'/0'/0/0".parse()?;
            let private = bip32::XPrv::derive_from_path(&*seed, &derivation)?;
            let key_bytes = zeroize::Zeroizing::new(<[u8; 32]>::from(private.private_key().to_bytes()));
            let key = SigningKey::Schnorr(
                base_crypto::schnorr::SigningKey::from_bytes(&*key_bytes)
                    .map_err(|error| anyhow::anyhow!("development Schnorr key: {error}"))?,
            );
            let owner = key.verifying_key();
            let address = UserAddress::from(owner.clone());
            let initial = funded.node.sync()?;
            let generation = &initial.state.dust.generation;
            let utxo = initial.state.utxo.utxos.iter().map(|entry| entry.0.clone())
                .filter(|utxo| utxo.owner == address && utxo.type_ == NIGHT && utxo.value > 0)
                .min_by_key(|utxo| (
                    generation.night_indices.contains_key(&utxo.initial_nonce()),
                    utxo.value,
                ))
                .context("development wallet has no spendable NIGHT outpoint")?;
            let prior_dust_generation = generation.night_indices.contains_key(&utxo.initial_nonce());
            let spend = UtxoSpend {
                value: utxo.value,
                type_: utxo.type_.clone(),
                intent_hash: utxo.intent_hash,
                output_no: utxo.output_no,
                owner,
            };
            let ttl = initial.block.tblock.to_secs() + 1800;
            let state_config = serde_json::to_vec(&json!({
                "state": {"observedUser": {"kind":"bytes", "values": vec![0u8; 32]}},
            }))?;
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![bundle])?, &state_config, ttl, &mut rng,
            )?;
            let operation = target.operation("observe", &parameters, ttl)?;
            let (state, deployment) = funded.deploy(&target, "observe").await?;
            let snapshot = funded.node.sync()?;
            let mut current = Some(state);
            let prepared = operation.prepare_call_with_unshielded_caller(
                &mut current, &parameters, BTreeMap::new(), &snapshot, &funded.node.policy,
                std::slice::from_ref(&spend), &mut rng,
            )?;
            ensure!(current.is_none(), "prepared caller did not consume its state token");
            let proved = prepared.prove(
                &LocalProver::new(StdRng::from_entropy()), &parameters, 1_048_576,
                futures::future::pending(),
            ).await?;

            let mut unsigned = one_intent(
                &snapshot.chain.network_id, CONTRACT_SEGMENT, proved.native().clone(),
            );
            let wrong_key = SigningKey::Schnorr(base_crypto::schnorr::SigningKey::sample(&mut rng));
            ensure!(
                sign_guaranteed_caller_offer(&mut unsigned, &snapshot, &wrong_key, &mut rng).is_err(),
                "caller offer accepted the wrong signing key"
            );
            let mut altered = proved.native().clone();
            let mut altered_offer = altered.guaranteed_unshielded_offer.as_deref()
                .context("proved caller is missing its exact offer")?.clone();
            let mut outputs: Vec<ledger::structure::UtxoOutput> = (&altered_offer.outputs).into();
            outputs[0].value += 1;
            altered_offer.outputs = outputs.into();
            altered.guaranteed_unshielded_offer = Some(storage::arena::Sp::new(altered_offer));
            ensure!(
                matches!(validate_guaranteed_caller_offer(&snapshot, &altered), Err(CallerError::InvalidOffer)),
                "changed principal return passed caller offer validation"
            );
            let return_intent = proved.native().erase_proofs().erase_signatures().intent_hash(0);
            let (_, receipt) = funded.finalize_with_funding(proved.native(), TestFunding::Caller(key)).await?;
            let finalized: ContractState<Db> = native_decode(&receipt.contract_state)?;
            let user_hex = hex::encode(address.0.0);
            let expected = crate::create_state(&plan, &BTreeMap::from([(
                "observedUser".into(), json!({"kind":"bytes", "values": address.0.0}),
            )]))?;
            ensure!(finalized.data.get_ref() == expected.get_ref(), "ledger supplied a different caller");
            let after = funded.node.sync()?;

            ensure!(
                matches!(validate_guaranteed_caller_offer(&after, proved.native()), Err(CallerError::SpendNotInSnapshot)),
                "spent caller input remained admissible after finalization"
            );
            ensure!(!after.state.utxo.utxos.contains_key(&Utxo::from(spend.clone())), "selected outpoint remained live");
            ensure!(after.state.utxo.utxos.iter().any(|entry| {
                let utxo = &entry.0;
                utxo.owner == address && utxo.type_ == spend.type_ && utxo.value == spend.value
                    && utxo.output_no == 0 && utxo.intent_hash == return_intent
            }), "same-owner return outpoint or amount differs");
            println!("{}", json!({
                "bundleManifestSha256": pin,
                "observedUser": user_hex,
                "contractAddress": receipt.contract_address,
                "deploymentHeight": deployment.height,
                "finalizedHeight": receipt.height,
                "finalizedHash": receipt.finalized_hash,
                "transactionId": receipt.transaction_id,
                "spentNight": spend.value.to_string(),
                "priorDustGeneration": prior_dust_generation,
                "sameOwnerPrincipalReturned": true,
                "ordinaryFundingRejectedCallerOffer": true,
                "wrongSigningKeyRejected": true,
                "alteredReturnOfferRejected": true,
                "spentOutpointRejected": true,
                "k": k,
            }));
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    enum TestFunding {
        Ordinary,
        Caller(ledger::structure::SigningKey),
        Mint,
    }

    #[cfg(feature = "zkir-321")]
    struct FundedLedgerTest {
        node: Node,
        dust: crate::funding::DustMaterial,
        dust_parameters: crate::proof::TrustedParameters,
    }

    #[cfg(feature = "zkir-321")]
    impl FundedLedgerTest {
        async fn connect(endpoint: &str, cache: &ProofCache) -> anyhow::Result<Self> {
            let policy = NetworkPolicy {
                network_id: "undeployed".into(),
                genesis: DEVELOPMENT_GENESIS.into(),
                spec_version: 2_001_100,
                transaction_version: 4,
                profile: crate::profile::NAME.into(),
                max_dust: 10u128.pow(22),
            };
            let node = Node::connect(
                endpoint,
                policy.clone(),
                Duration::from_secs(15),
                64 * 1024 * 1024,
                100_000,
            )?;
            let mut local_seed = [0; 32];
            local_seed[31] = 1;
            node.attach_dust_seed(&local_seed)?;
            let dust = cache.dust().await?;
            let dust_parameters = cache.parameters(dust.k()).await?;
            Ok(Self {
                node,
                dust,
                dust_parameters,
            })
        }

        async fn finalize(
            &self,
            intent: &crate::proof::ProvedNativeIntent,
        ) -> anyhow::Result<(BoundTransaction, FinalizedReceipt)> {
            self.finalize_with_funding(intent, TestFunding::Ordinary).await
        }

        async fn finalize_with_funding(
            &self,
            intent: &crate::proof::ProvedNativeIntent,
            mode: TestFunding,
        ) -> anyhow::Result<(BoundTransaction, FinalizedReceipt)> {
            use crate::client::{ChainAdapter, Submission};
            use crate::funding::{FeePolicy, UnsealedTransaction};
            use anyhow::ensure;
            use rand::{SeedableRng, rngs::StdRng};
            use std::time::Instant;

            let policy = &self.node.policy;
            let funding = DevelopmentFunding::new(
                &self.node,
                &self.dust,
                &self.dust_parameters,
                FeePolicy {
                    max_dust: policy.max_dust,
                    margin_blocks: 3,
                    max_spends: 8,
                },
                StdRng::from_entropy(),
            );
            let approve = |_: &UnsealedTransaction, candidate: &NetworkPolicy| candidate == policy;
            let signer = ExplicitSeal::new(approve, StdRng::from_entropy());
            let bound = match mode {
                TestFunding::Caller(key) => {
                    ensure!(
                        matches!(
                            BoundTransaction::prepare(intent, policy.clone(), &self.node, &funding, &signer).await,
                            Err(crate::client::Error::InvalidTransaction)
                        ),
                        "ordinary funding accepted the caller offer"
                    );
                    let signer = signer.with_unshielded_caller_key(key);
                    BoundTransaction::prepare_unshielded_caller(
                        intent, policy.clone(), &self.node, &funding, &signer,
                    ).await?
                }
                TestFunding::Mint => BoundTransaction::prepare_unshielded_mint(
                    intent, policy.clone(), &self.node, &funding, &signer,
                ).await?,
                TestFunding::Ordinary => BoundTransaction::prepare(
                    intent, policy.clone(), &self.node, &funding, &signer,
                ).await?,
            };
            ensure!(
                self.node
                    .submit(&bound)
                    .await
                    .map_err(|_| anyhow::anyhow!("submit failed"))?
                    != Submission::Rejected,
                "localnet rejected intent"
            );
            let deadline = Instant::now() + Duration::from_secs(90);
            loop {
                if let Some(receipt) = self.node.finalized_receipt(&bound)? {
                    bound.check_receipt(&receipt)?;
                    return Ok((bound, receipt));
                }
                ensure!(Instant::now() < deadline, "receipt did not finalize");
                std::thread::sleep(Duration::from_millis(500));
            }
        }

        async fn deploy(
            &self,
            target: &crate::proof::WitnessContractTarget,
            operation: &str,
        ) -> anyhow::Result<(crate::proof::CurrentStateContext, FinalizedReceipt)> {
            use crate::funding::CONTRACT_SEGMENT;
            use rand::{SeedableRng, rngs::StdRng};

            let (_, deployment) = target
                .deployment_intent()
                .prove(
                    CONTRACT_SEGMENT,
                    builtin_zkir::LocalProvingProvider {
                        rng: StdRng::from_entropy(),
                        resolver: &self.dust,
                        params: &self.dust_parameters,
                    },
                    &self
                        .node
                        .sync()?
                        .state
                        .parameters
                        .cost_model
                        .runtime_cost_model,
                )
                .await
                .map_err(|error| anyhow::anyhow!("deployment proof: {error:?}"))?;
            let (bound, receipt) = self.finalize(&deployment).await?;
            let state = target
                .deployment_binding(operation)?
                .admit_committed_state(
                    &receipt.contract_state,
                    bound.expected_state(),
                    &receipt.finalized_hash,
                    true,
                )?;
            Ok((state, receipt))
        }

        async fn call(
            &self,
            operation: &crate::proof::ContractOperationTarget,
            current: &mut Option<crate::proof::CurrentStateContext>,
            parameters: &crate::proof::TrustedParameters,
            inputs: BTreeMap<String, Json>,
        ) -> anyhow::Result<FinalizedReceipt> {
            Ok(self.call_with_bound(operation, current, parameters, inputs).await?.1)
        }

        async fn call_with_bound(
            &self,
            operation: &crate::proof::ContractOperationTarget,
            current: &mut Option<crate::proof::CurrentStateContext>,
            parameters: &crate::proof::TrustedParameters,
            inputs: BTreeMap<String, Json>,
        ) -> anyhow::Result<(BoundTransaction, FinalizedReceipt)> {
            use crate::proof::LocalProver;
            use anyhow::Context;
            use rand::{SeedableRng, rngs::StdRng};

            let proved = operation
                .prepare_call(current, parameters, inputs, &mut StdRng::from_entropy())?
                .prove(
                    &LocalProver::new(StdRng::from_entropy()),
                    parameters,
                    1_048_576,
                    futures::future::pending(),
                )
                .await?;
            let (bound, receipt) = self.finalize(proved.native()).await?;
            *current = Some(
                proved
                    .contract_binding()
                    .context("missing checked contract binding")?
                    .admit_committed_state(
                        &receipt.contract_state,
                        bound.expected_state(),
                        &receipt.finalized_hash,
                        false,
                    )?,
            );
            Ok((bound, receipt))
        }
    }

    fn finalized_contract_logs(
        node: &Node,
        bound: &BoundTransaction,
        receipt: &FinalizedReceipt,
    ) -> anyhow::Result<Vec<FinalizedContractLog>> {
        use anyhow::{Context, ensure};

        bound.check_receipt(receipt)?;
        let mut cache = node.cache.borrow().clone();
        ensure!(
            cache.as_ref().is_some_and(|cache| cache.height < receipt.height),
            "no pre-inclusion replay state is available"
        );
        let address = ContractAddress(HashOutput(
            hex::decode(bound.contract_address())?
                .try_into()
                .map_err(|_| anyhow::anyhow!("invalid bound contract address"))?,
        ));
        let mut replay = PartialReplay {
            transaction: bound.bytes(),
            address,
            partial: false,
            result: None,
            logs: None,
        };
        let snapshot = node.replay_to(&receipt.block_hash, &mut cache, Some(&mut replay))?;
        ensure!(
            snapshot.height == receipt.height && snapshot.finalized_hash == receipt.block_hash,
            "captured block differs from finalized receipt"
        );
        let contract = snapshot
            .state
            .contract
            .get(&address)
            .context("replayed contract state is missing")?;
        let mut state = Vec::new();
        serialize::tagged_serialize(&*contract, &mut state)
            .map_err(|_| anyhow::anyhow!("cannot encode replayed contract state"))?;
        ensure!(
            state == receipt.contract_state,
            "replayed contract state differs from the checked receipt"
        );
        replay.logs.context("exact finalized transaction emitted no replay capture")
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "spends the published development wallet on the pinned isolated localnet"]
    fn standard_event_helper_finalizes_logs() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use base_crypto::fab::{Alignment, AlignmentAtom};
        use futures::executor::block_on;
        use onchain_runtime::{ops::LogEventType, state::StateValue};
        use rand::{SeedableRng, rngs::StdRng};
        use serde_json::json;
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::proofs::Zkir;

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let directory = setting("NOCTIUM_STANDARD_EVENTS_BUNDLES")?;
            let pins: BTreeMap<String, String> =
                serde_json::from_str(&setting("NOCTIUM_STANDARD_EVENTS_MANIFESTS")?)?;
            let mut bundles = Vec::new();
            let mut helper_k = None;
            for entry in ["logSpend", "logCatalog", "logHelperSpend"] {
                let pin = pins.get(entry).with_context(|| format!("missing {entry} manifest pin"))?;
                let bundle = artifacts::verify(&Path::new(&directory).join(entry), Some(pin))?;
                let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
                ensure!(plan.entrypoint == entry, "bundle directory does not match operation");
                if entry == "logHelperSpend" {
                    helper_k = Some(IrSource::load(bundle.file(Role::Circuit)?)?.k());
                }
                bundles.push(bundle);
            }
            let cache = ProofCache::new(
                setting("NOCTIUM_STANDARD_EVENTS_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let parameters = cache
                .parameters(helper_k.context("missing helper event circuit")?)
                .await?;
            let funded = FundedLedgerTest::connect(
                &setting("NOCTIUM_STANDARD_EVENTS_NODE")?,
                &cache,
            )
            .await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(bundles)?,
                br#"{"state":{}}"#,
                ttl,
                &mut rng,
            )?;
            let operation = target.operation("logHelperSpend", &parameters, ttl)?;
            let (deployed, deployment) = funded.deploy(&target, "logHelperSpend").await?;
            let mut current = Some(deployed);
            let nullifier: Vec<u8> = (1..=32).collect();
            let call = |active| {
                BTreeMap::from([
                    ("active".into(), json!(active)),
                    ("nullifier".into(), json!({"kind":"bytes","values":nullifier})),
                ])
            };
            let (active_bound, active_receipt) = funded
                .call_with_bound(&operation, &mut current, &parameters, call(true))
                .await?;
            let active_logs = finalized_contract_logs(&funded.node, &active_bound, &active_receipt)?;
            let (inactive_bound, inactive_receipt) = funded
                .call_with_bound(&operation, &mut current, &parameters, call(false))
                .await?;
            let inactive_logs = finalized_contract_logs(&funded.node, &inactive_bound, &inactive_receipt)?;

            fn payload(log: &FinalizedContractLog) -> anyhow::Result<&[u8]> {
                let StateValue::Cell(data) = &log.item.data else {
                    anyhow::bail!("event payload is not a byte cell")
                };
                let [atom] = data.value.0.as_slice() else {
                    anyhow::bail!("expected one event byte payload")
                };
                ensure!(
                    data.alignment == Alignment::singleton(AlignmentAtom::Bytes { length: atom.0.len() as u32 }),
                    "event payload alignment differs from its bytes"
                );
                Ok(&atom.0)
            }
            let expected_address = hex::encode(hex::decode(active_bound.contract_address())?);
            let assert_logs = |logs: &[FinalizedContractLog], kinds: &[LogEventType]| -> anyhow::Result<()> {
                ensure!(logs.len() == kinds.len(), "unexpected finalized event count");
                for (log, kind) in logs.iter().zip(kinds) {
                    ensure!(hex::encode(log.address.0.0) == expected_address, "event belongs to another contract");
                    ensure!(log.entry_point == onchain_runtime::state::EntryPointBuf(b"logHelperSpend".to_vec()), "event belongs to another entrypoint");
                    ensure!(log.item.version == 1, "unexpected event schema version");
                    ensure!(log.item.event_type == *kind, "finalized event tag differs");
                }
                Ok(())
            };
            assert_logs(&active_logs, &[LogEventType::Paused, LogEventType::ShieldedSpend, LogEventType::Unpaused])?;
            assert_logs(&inactive_logs, &[LogEventType::Paused, LogEventType::Unpaused])?;
            ensure!(payload(&active_logs[0])?.is_empty(), "Paused payload is not empty");
            ensure!(payload(&active_logs[1])? == nullifier.as_slice(), "helper payload differs");
            ensure!(payload(&active_logs[2])?.is_empty(), "Unpaused payload is not empty");
            ensure!(
                payload(&inactive_logs[0])?.is_empty() && payload(&inactive_logs[1])?.is_empty(),
                "inactive branch emitted an unexpected helper payload"
            );

            let receipt_logs = |logs: &[FinalizedContractLog]| -> anyhow::Result<Vec<_>> {
                logs.iter().map(|log| {
                    let bytes = payload(log)?;
                    Ok(json!({
                        "version": log.item.version,
                        "tag": log.item.event_type as u8,
                        "payloadLength": bytes.len(),
                        "payloadSha256": hex::encode(sha2::Sha256::digest(bytes)),
                    }))
                }).collect()
            };
            println!("{}", json!({
                "profile": crate::profile::NAME,
                "contractAddress": active_receipt.contract_address,
                "deployment": {"height": deployment.height, "transactionId": deployment.transaction_id},
                "active": {"height": active_receipt.height, "blockHash": active_receipt.block_hash, "transactionId": active_receipt.transaction_id, "events": receipt_logs(&active_logs)?},
                "inactive": {"height": inactive_receipt.height, "blockHash": inactive_receipt.block_hash, "transactionId": inactive_receipt.transaction_id, "events": receipt_logs(&inactive_logs)?},
                "exactFinalizedEventBytesChecked": true,
            }));
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "spends the published development wallet on the pinned isolated localnet"]
    fn standard_event_catalog_finalizes_all_logs() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use base_crypto::fab::{Alignment, AlignmentAtom};
        use futures::executor::block_on;
        use onchain_runtime::state::StateValue;
        use rand::{SeedableRng, rngs::StdRng};
        use serde_json::json;
        use sha2::{Digest, Sha256};
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::proofs::Zkir;

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let directory = setting("NOCTIUM_STANDARD_EVENTS_BUNDLES")?;
            let pins: BTreeMap<String, String> =
                serde_json::from_str(&setting("NOCTIUM_STANDARD_EVENTS_MANIFESTS")?)?;
            let mut bundles = Vec::new();
            let mut catalog_k = None;
            let mut catalog_compiler = None;
            let mut catalog_artifacts = None;
            for entry in ["logSpend", "logCatalog", "logHelperSpend"] {
                let pin = pins.get(entry).with_context(|| format!("missing {entry} manifest pin"))?;
                let bundle = artifacts::verify(&Path::new(&directory).join(entry), Some(pin))?;
                let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
                ensure!(plan.entrypoint == entry, "bundle directory does not match operation");
                if entry == "logCatalog" {
                    let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
                    catalog_k = Some(circuit.k());
                    catalog_compiler = Some(bundle.manifest().compiler.clone());
                    catalog_artifacts = Some(bundle.manifest().entries.clone());
                }
                bundles.push(bundle);
            }
            let catalog_k = catalog_k.context("missing logCatalog circuit")?;
            let catalog_compiler = catalog_compiler.context("missing logCatalog compiler identity")?;
            let catalog_artifacts = catalog_artifacts.context("missing logCatalog artifacts")?;
            let manifest_pin = pins.get("logCatalog").context("missing logCatalog manifest pin")?;
            let cache = ProofCache::new(
                setting("NOCTIUM_STANDARD_EVENTS_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let parameters = cache.parameters(catalog_k).await?;
            let funded = FundedLedgerTest::connect(
                &setting("NOCTIUM_STANDARD_EVENTS_NODE")?,
                &cache,
            )
            .await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(bundles)?,
                br#"{"state":{}}"#,
                ttl,
                &mut rng,
            )?;
            let operation = target.operation("logCatalog", &parameters, ttl)?;
            let (deployed, deployment) = funded.deploy(&target, "logCatalog").await?;
            let mut current = Some(deployed);
            let bytes = |length: usize, start: usize| {
                let values: Vec<_> = (0..length)
                    .map(|index| ((start + index) % 256) as u8)
                    .collect();
                json!({"kind":"bytes","values":values})
            };
            let inputs = BTreeMap::from([
                ("commitment".into(), bytes(32, 1)),
                ("domain".into(), bytes(32, 225)),
                ("ciphertext".into(), bytes(512, 1)),
                ("memo".into(), bytes(256, 2)),
                ("value".into(), json!(((1u128 << 127) + 0x10203).to_string())),
            ]);
            let (bound, call_receipt) = funded
                .call_with_bound(&operation, &mut current, &parameters, inputs)
                .await?;
            ensure!(
                deployment.contract_state == call_receipt.contract_state,
                "catalog call changed contract state"
            );
            let logs = finalized_contract_logs(&funded.node, &bound, &call_receipt)?;
            let reference_bytes = include_bytes!("../../tests/standard-event-catalog-compact.json");
            let compact_source = include_bytes!("../../tests/compact/StandardEventCatalog.compact");
            let compact_runner = include_bytes!("../../tests/compact/standard-event-catalog.mjs");
            let reference: serde_json::Value = serde_json::from_slice(reference_bytes)?;
            let expected = reference["events"].as_array().context("missing Compact event list")?;
            ensure!(expected.len() == 11 && logs.len() == expected.len(), "catalog log count differs");
            let contract_address = bound.contract_address().to_owned();
            let entrypoint = onchain_runtime::state::EntryPointBuf(b"logCatalog".to_vec());
            let mut observed = Vec::with_capacity(logs.len());
            for (log, expected) in logs.iter().zip(expected) {
                ensure!(
                    hex::encode(log.address.0.0) == contract_address,
                    "event belongs to another contract"
                );
                ensure!(log.entry_point == entrypoint, "event belongs to another entrypoint");
                let version = expected["version"].as_u64().context("missing event version")? as u32;
                let tag = expected["tag"].as_u64().context("missing event tag")? as u8;
                let payload_length = expected["payloadLength"]
                    .as_u64()
                    .context("missing payload length")? as u32;
                let digest = expected["payloadSha256"]
                    .as_str()
                    .context("missing Compact payload digest")?;
                ensure!(log.item.version == version, "finalized event version differs from Compact");
                ensure!(log.item.event_type as u8 == tag, "finalized event tag differs from Compact");
                let StateValue::Cell(data) = &log.item.data else {
                    anyhow::bail!("finalized event payload is not a byte cell")
                };
                ensure!(
                    data.alignment == Alignment::singleton(AlignmentAtom::Bytes { length: payload_length }),
                    "finalized event payload width differs from Compact"
                );
                let [atom] = data.value.0.as_slice() else {
                    anyhow::bail!("expected one finalized event byte atom")
                };
                ensure!(atom.0.len() <= payload_length as usize, "event payload exceeds declared width");
                let mut payload = atom.0.clone();
                payload.resize(payload_length as usize, 0);
                let payload_sha256 = hex::encode(Sha256::digest(&payload));
                ensure!(payload_sha256 == digest, "finalized event payload digest differs from Compact");
                observed.push(json!({
                    "version": version,
                    "tag": tag,
                    "payloadLength": payload_length,
                    "payloadSha256": payload_sha256,
                }));
            }
            let entry_hash = |role: Role, name: Option<&str>| -> anyhow::Result<String> {
                catalog_artifacts
                    .iter()
                    .find(|entry| entry.role == role && name.is_none_or(|name| entry.name == name))
                    .map(|entry| entry.sha256.clone())
                    .context("missing bundle manifest entry")
            };
            let receipt_fields = |value: &FinalizedReceipt| json!({
                "blockHash": value.block_hash,
                "height": value.height,
                "finalizedHash": value.finalized_hash,
                "finalizedHeight": value.finalized_height,
                "extrinsicHash": value.extrinsic_hash,
                "extrinsicIndex": value.extrinsic_index,
                "transactionId": value.transaction_id,
            });
            println!("{}", json!({
                "schemaVersion": 1,
                "profile": crate::profile::NAME,
                "network": call_receipt.chain,
                "compiler": catalog_compiler,
                "sourceSha256": entry_hash(Role::Source, Some("examples/StandardEvents.lean"))?,
                "compactReference": {
                    "compiler": reference["compiler"],
                    "runtime": reference["runtime"],
                    "sourceSha256": hex::encode(Sha256::digest(compact_source)),
                    "runnerSha256": hex::encode(Sha256::digest(compact_runner)),
                    "payloadReferenceSha256": hex::encode(Sha256::digest(reference_bytes)),
                },
                "artifacts": {
                    "bundleManifestSha256": manifest_pin,
                    "circuitSha256": entry_hash(Role::Circuit, None)?,
                    "impactPlanSha256": entry_hash(Role::Plan, None)?,
                    "profileSha256": entry_hash(Role::Profile, None)?,
                    "ledgerParametersSha256": entry_hash(Role::LedgerParameters, None)?,
                    "proverKeySha256": entry_hash(Role::ProverKey, None)?,
                    "verifierKeySha256": entry_hash(Role::VerifierKey, None)?,
                    "toolchainSha256": entry_hash(Role::Toolchain, None)?,
                    "k": catalog_k,
                },
                "contractAddress": contract_address,
                "deployment": receipt_fields(&deployment),
                "call": receipt_fields(&call_receipt),
                "logs": observed,
                "stateUnchanged": true,
                "allElevenFinalizedLogsMatchPinnedCompact": true,
                "scope": "One fresh deployment and one logCatalog call. The call uses hasCiphertext=true, hasContractAddress=false, hasAmount=true, and the user/contract branches shown by the input fixture. Alternate option and address branch combinations remain unqualified.",
            }));
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "spends the published development wallet on the pinned isolated localnet"]
    fn standard_event_flag_branches_finalize_on_localnet() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use base_crypto::fab::{Alignment, AlignmentAtom};
        use futures::executor::block_on;
        use onchain_runtime::state::StateValue;
        use rand::{SeedableRng, rngs::StdRng};
        use serde_json::{Value as Json, json};
        use sha2::{Digest, Sha256};
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::proofs::Zkir;

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let directory = setting("NOCTIUM_EVENT_FLAG_BUNDLE")?;
            let pin = setting("NOCTIUM_EVENT_FLAG_MANIFEST")?;
            let bundle = artifacts::verify(Path::new(&directory), Some(&pin))?;
            let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
            let entrypoint = "emitFlagBranches";
            ensure!(plan.entrypoint == entrypoint, "wrong standard event plan");
            let k = IrSource::load(bundle.file(Role::Circuit)?)?.k();
            let compiler = bundle.manifest().compiler.clone();
            let artifacts = bundle.manifest().entries.clone();
            let reference: Json = serde_json::from_slice(include_bytes!(
                "../../tests/standard-event-flag-branches-compact.json"
            ))?;
            let fixed_inputs: BTreeMap<String, Json> =
                serde_json::from_value(reference["nativeInputs"].clone())?;
            let cases = reference["cases"]
                .as_array()
                .context("missing Compact flag cases")?;
            let cache = ProofCache::new(
                setting("NOCTIUM_EVENT_FLAG_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let parameters = cache.parameters(k).await?;
            let funded =
                FundedLedgerTest::connect(&setting("NOCTIUM_EVENT_FLAG_NODE")?, &cache).await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![bundle])?,
                br#"{"state":{}}"#,
                ttl,
                &mut rng,
            )?;
            let operation = target.operation(entrypoint, &parameters, ttl)?;
            let (deployed, deployment) = funded.deploy(&target, entrypoint).await?;
            let mut current = Some(deployed);
            let receipt_fields = |receipt: &FinalizedReceipt| {
                json!({
                    "height": receipt.height, "blockHash": receipt.block_hash,
                    "finalizedHeight": receipt.finalized_height, "finalizedHash": receipt.finalized_hash,
                    "extrinsicIndex": receipt.extrinsic_index, "extrinsicHash": receipt.extrinsic_hash,
                    "transactionId": receipt.transaction_id,
                })
            };
            let mut observed = Vec::new();
            for (present, route) in [(false, false), (false, true), (true, false), (true, true)] {
                let expected = cases
                    .iter()
                    .find(|case| case["present"] == json!(present) && case["route"] == json!(route))
                    .context("missing selected Compact flag case")?;
                let expected_logs = expected["events"]
                    .as_array()
                    .context("missing Compact events")?;
                let mut inputs = fixed_inputs.clone();
                inputs.insert("present".into(), json!(present));
                inputs.insert("route".into(), json!(route));
                let (bound, receipt) = funded
                    .call_with_bound(&operation, &mut current, &parameters, inputs)
                    .await?;
                ensure!(
                    receipt.contract_state == deployment.contract_state,
                    "event call changed contract state"
                );
                let logs = finalized_contract_logs(&funded.node, &bound, &receipt)?;
                ensure!(
                    logs.len() == 6 && logs.len() == expected_logs.len(),
                    "wrong finalized event count"
                );
                let address = bound.contract_address().to_owned();
                let expected_entrypoint =
                    onchain_runtime::state::EntryPointBuf(entrypoint.as_bytes().to_vec());
                for (order, (log, expected)) in logs.iter().zip(expected_logs).enumerate() {
                    ensure!(hex::encode(log.address.0.0) == address, "wrong log address");
                    ensure!(
                        log.entry_point == expected_entrypoint,
                        "wrong log entrypoint"
                    );
                    ensure!(
                        expected["order"] == json!(order),
                        "wrong Compact event order"
                    );
                    ensure!(
                        expected["version"] == json!(log.item.version),
                        "wrong log version"
                    );
                    ensure!(
                        expected["tag"] == json!(log.item.event_type as u8),
                        "wrong log tag"
                    );
                    let width = u32::try_from(
                        expected["payloadLength"]
                            .as_u64()
                            .context("missing byte width")?,
                    )?;
                    let StateValue::Cell(data) = &log.item.data else {
                        anyhow::bail!("expected a byte cell event");
                    };
                    ensure!(
                        data.alignment
                            == Alignment::singleton(AlignmentAtom::Bytes { length: width }),
                        "wrong event alignment"
                    );
                    let [atom] = data.value.0.as_slice() else {
                        anyhow::bail!("expected one byte atom");
                    };
                    let mut padded = atom.0.clone();
                    ensure!(
                        padded.len() <= width as usize,
                        "event bytes exceed the alignment"
                    );
                    padded.resize(width as usize, 0);
                    ensure!(
                        expected["payloadSha256"] == json!(hex::encode(Sha256::digest(&padded))),
                        "wrong event digest"
                    );
                }
                observed.push(json!({
                    "present": present, "route": route, "contractAddress": address,
                    "confirmation": receipt_fields(&receipt), "events": expected_logs,
                }));
            }
            println!(
                "{}",
                json!({
                    "schemaVersion": 1, "profile": crate::profile::NAME,
                    "network": deployment.chain, "entrypoint": entrypoint, "k": k,
                    "compiler": compiler, "artifactEntries": artifacts, "bundleManifestSha256": pin,
                    "deployment": receipt_fields(&deployment), "calls": observed, "stateUnchanged": true,
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires the pinned NativeUnshieldedMintRecipient bundle and funded development node"]
    fn funded_recipient_mint_distinguishes_contract_and_user_with_same_address_bytes()
    -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            client::ContractEvent,
            proof::{LocalProver, WitnessContractTarget},
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use coin_structure::{
            coin::{PublicAddress, TokenType, UserAddress},
            contract::ContractAddress,
        };
        use futures::executor::block_on;
        use ledger::structure::{ContractAction, GUARANTEED_SEGMENT, Transaction, Utxo, UtxoOutput};
        use onchain_runtime::{context::ClaimedUnshieldedSpendsKey, state::ContractState};
        use rand::{SeedableRng, rngs::StdRng};
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::proofs::Zkir;

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let manifest = setting("NOCTIUM_FUNDED_RECIPIENT_MINT_MANIFEST_SHA256")?;
            let bundle = artifacts::verify(
                Path::new(&setting("NOCTIUM_FUNDED_RECIPIENT_MINT_BUNDLE")?),
                Some(&manifest),
            )?;
            let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
            let cache = ProofCache::new(
                setting("NOCTIUM_FUNDED_RECIPIENT_MINT_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let parameters = cache.parameters(circuit.k()).await?;
            let funded =
                FundedLedgerTest::connect(&setting("NOCTIUM_FUNDED_RECIPIENT_MINT_NODE")?, &cache)
                    .await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![bundle])?,
                br#"{"state":{}}"#,
                ttl,
                &mut rng,
            )?;
            let operation = target.operation("mint", &parameters, ttl)?;
            let (deployed, deployment) = funded
                .deploy(&target, "mint")
                .await
                .context("finalize recipient-mint deployment")?;
            ensure!(
                deployment.event == ContractEvent::Deploy,
                "recipient-mint deployment receipt has the wrong event"
            );
            eprintln!(
                "recipient-mint deployment {} finalized at {}",
                target.contract_address(),
                deployment.finalized_hash,
            );
            let mut current = Some(deployed);

            let address_bytes: [u8; 32] = hex::decode(target.contract_address())?
                .try_into()
                .map_err(|_| anyhow::anyhow!("target address is not 32 bytes"))?;
            let own = ContractAddress(HashOutput(address_bytes));
            let domain = HashOutput(std::array::from_fn(|index| (index + 1) as u8));
            let amount = 7u64;
            let token_color = own.custom_unshielded_token_type(domain);
            let expected_color = token_color.0;
            let token = TokenType::Unshielded(token_color);
            let inputs = |is_contract: bool| {
                BTreeMap::from([
                    ("domain".into(), json!({"kind":"bytes", "values":domain.0})),
                    ("amount".into(), json!(amount.to_string())),
                    ("isContract".into(), json!(is_contract)),
                    (
                        "recipient".into(),
                        json!({"kind":"bytes", "values":address_bytes}),
                    ),
                    ("enabled".into(), json!(true)),
                ])
            };

            let mut receipts = Vec::new();
            for (is_contract, recipient) in [
                (true, PublicAddress::Contract(own)),
                (false, PublicAddress::User(UserAddress(own.0))),
            ] {
                let recipient_tag = if is_contract { "contract" } else { "user" };
                let prepared = operation.prepare_call(
                    &mut current,
                    &parameters,
                    inputs(is_contract),
                    &mut rng,
                )?;
                let proved = prepared
                    .prove(
                        &LocalProver::new(StdRng::from_entropy()),
                        &parameters,
                        1_048_576,
                        futures::future::pending(),
                    )
                    .await?;
                let Some(ContractAction::Call(call)) = proved.native().actions.get(0) else {
                    anyhow::bail!("recipient-mint proof omitted its contract call");
                };
                let transcript = call
                    .guaranteed_transcript
                    .as_ref()
                    .context("recipient-mint call omitted its guaranteed transcript")?;
                let effects = &transcript.effects;
                ensure!(
                    effects.unshielded_mints.get(&domain).map(|value| *value) == Some(amount),
                    "mint transcript has the wrong domain amount"
                );
                ensure!(
                    effects.unshielded_mints.size() == 1,
                    "mint transcript contains unexpected domains"
                );
                let self_credit = is_contract;
                ensure!(
                    effects.unshielded_inputs.get(&token).map(|value| *value)
                        == self_credit.then_some(amount as u128),
                    "same-byte recipient tag produced the wrong contract credit"
                );
                ensure!(
                    effects.unshielded_inputs.size() == usize::from(self_credit),
                    "mint transcript contains unexpected contract credits"
                );
                ensure!(
                    effects.unshielded_outputs.size() == 0,
                    "mint operation unexpectedly produced user-side UTXOs"
                );
                ensure!(
                    effects
                        .claimed_unshielded_spends
                        .get(&ClaimedUnshieldedSpendsKey(token.clone(), recipient))
                        .map(|value| *value)
                        == Some(amount as u128),
                    "claim transcript has the wrong principal tag or amount"
                );
                ensure!(
                    effects.claimed_unshielded_spends.size() == 1,
                    "mint transcript contains unexpected recipient claims"
                );

                let binding = proved
                    .contract_binding()
                    .context("missing checked contract binding")?;
                let funding = if is_contract { TestFunding::Ordinary } else { TestFunding::Mint };
                let (bound, receipt) = funded
                    .finalize_with_funding(proved.native(), funding)
                    .await
                    .with_context(|| format!("finalize {recipient_tag}-tagged mint"))?;
                ensure!(
                    receipt.event == ContractEvent::Call
                        && receipt.contract_address == target.contract_address(),
                    "recipient-mint call receipt has the wrong target or event"
                );
                current = Some(binding.admit_committed_state(
                    &receipt.contract_state,
                    bound.expected_state(),
                    &receipt.finalized_hash,
                    false,
                )?);
                let state: ContractState<Db> = native_decode(&receipt.contract_state)?;
                ensure!(
                    state.balance.get(&token).map(|value| *value) == Some(amount as u128),
                    "finalized contract balance differs from the self-credit expectation"
                );
                let Transaction::Standard(signed) = native_decode::<crate::funding::SealedTransaction>(bound.bytes())? else {
                    anyhow::bail!("mint receipt must identify a standard transaction");
                };
                let intent = signed.intents.get(&crate::funding::CONTRACT_SEGMENT)
                    .context("mint transaction omitted contract segment")?;
                if is_contract {
                    ensure!(intent.guaranteed_unshielded_offer.is_none(), "self-credit produced a user offer");
                } else {
                    let offer = intent.guaranteed_unshielded_offer.as_deref()
                        .context("signed mint transaction omitted the user offer")?;
                    let expected = UtxoOutput {
                        value: u128::from(amount),
                        owner: UserAddress(own.0),
                        type_: token_color,
                    };
                    ensure!(offer.inputs.is_empty() && offer.signatures.is_empty()
                        && offer.outputs.len() == 1 && offer.outputs.get(0) == Some(&expected),
                        "signed user offer does not match the proved mint");
                    let utxo = Utxo {
                        value: u128::from(amount),
                        owner: UserAddress(own.0),
                        type_: token_color,
                        // The ledger hashes guaranteed outputs in logical segment zero.
                        intent_hash: intent
                            .erase_proofs()
                            .erase_signatures()
                            .intent_hash(GUARANTEED_SEGMENT),
                        output_no: 0,
                    };
                    ensure!(funded.node.sync()?.state.utxo.utxos.contains_key(&utxo),
                        "exact user output is missing from the finalized ledger");
                }
                eprintln!("{recipient_tag}-tagged mint finalized at {}", receipt.finalized_hash);
                receipts.push(receipt);
            }

            ensure!(
                receipts.len() == 2,
                "expected two finalized recipient-mint calls"
            );
            ensure!(
                receipts[0].transaction_id != receipts[1].transaction_id,
                "same-byte recipient cases did not produce distinct transactions"
            );
            let first: ContractState<Db> = native_decode(&receipts[0].contract_state)?;
            let second: ContractState<Db> = native_decode(&receipts[1].contract_state)?;
            ensure!(
                second.balance.get(&token).map(|value| *value)
                    == first.balance.get(&token).map(|value| *value),
                "user-tagged same-byte mint changed the contract balance"
            );
            println!(
                "{}",
                json!({
                    "bundleManifestSha256": manifest,
                    "deploymentHeight": deployment.height,
                    "deploymentFinalizedHash": deployment.finalized_hash,
                    "contractAddress": target.contract_address(),
                    "domain": hex::encode(domain.0),
                    "expectedColor": hex::encode(expected_color.0),
                    "amount": amount.to_string(),
                    "selfCall": {
                        "height": receipts[0].height,
                        "finalizedHash": receipts[0].finalized_hash,
                        "transactionId": receipts[0].transaction_id,
                        "contractBalance": amount.to_string(),
                        "recipientTag": "contract"
                    },
                    "sameBytesUserCall": {
                        "height": receipts[1].height,
                        "finalizedHash": receipts[1].finalized_hash,
                        "transactionId": receipts[1].transaction_id,
                        "contractBalance": second.balance.get(&token).map(|value| value.to_string()),
                        "recipientTag": "user",
                        "finalizedUserOutput": {"index":0,"value":amount.to_string()}
                    }
                })
            );
            Ok(())
        })
    }
    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires the pinned NativeContractAddress bundle and funded development node"]
    fn kernel_self_uses_target_address_and_skips_state_when_inactive() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use futures::executor::block_on;
        use onchain_runtime::state::ContractState;
        use rand::{SeedableRng, rngs::StdRng};
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::proofs::Zkir;

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let directory = setting("NOCTIUM_KERNEL_SELF_BUNDLE")?;
            let manifest = setting("NOCTIUM_KERNEL_SELF_MANIFEST_SHA256")?;
            let bundle = artifacts::verify(Path::new(&directory), Some(&manifest))?;
            let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
            let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
            let cache = ProofCache::new(
                setting("NOCTIUM_KERNEL_SELF_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(&setting("NOCTIUM_KERNEL_SELF_NODE")?, &cache)
                .await?;
            let parameters = cache.parameters(circuit.k()).await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let state_config = serde_json::to_vec(
                &json!({"state":{"lastAddress":{"kind":"bytes","values":vec![0u8;32]}}}),
            )?;
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![bundle])?,
                &state_config,
                ttl,
                &mut rng,
            )?;
            let identify = target.operation("identify", &parameters, ttl)?;
            let (deployed, deployment) = funded.deploy(&target, "identify").await?;
            let mut current = Some(deployed);
            let inputs = |enabled| BTreeMap::from([("enabled".into(), json!(enabled))]);
            let active = funded
                .call(&identify, &mut current, &parameters, inputs(true))
                .await?;

            let address = hex::decode(target.contract_address())?;
            ensure!(address.len() == 32, "target contract address is not 32 bytes");
            let expected = crate::create_state(
                &plan,
                &BTreeMap::from([(
                    "lastAddress".into(),
                    json!({"kind":"bytes","values":address}),
                )]),
            )?;
            let active_state: ContractState<Db> = native_decode(&active.contract_state)?;
            ensure!(
                *active_state.data.get_ref() == *expected.get_ref(),
                "active identify call did not finalize lastAddress as its target address"
            );

            let inactive = funded
                .call(&identify, &mut current, &parameters, inputs(false))
                .await?;
            ensure!(
                inactive.contract_state == active.contract_state,
                "inactive identify call changed the exact finalized contract state"
            );
            println!(
                "{}",
                json!({
                    "contractAddress": target.contract_address(),
                    "deploymentHeight": deployment.height,
                    "activeHeight": active.height,
                    "inactiveHeight": inactive.height,
                    "transactionIds": [deployment.transaction_id, active.transaction_id, inactive.transaction_id],
                    "activeStateBindsTargetAddress": true,
                    "inactiveStateUnchanged": true,
                    "bundleManifestSha256": manifest,
                    "k": circuit.k(),
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires authenticated NativeMapDefault bundles and the funded development node"]
    fn native_map_default_inserts_and_preserves_siblings() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use futures::executor::block_on;
        use onchain_runtime::state::{ContractState, StateValue};
        use rand::{SeedableRng, rngs::StdRng};
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::{curve::Fr, proofs::Zkir};

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let directory = setting("NOCTIUM_MAP_DEFAULT_BUNDLES")?;
            let pins: BTreeMap<String, String> =
                serde_json::from_str(&setting("NOCTIUM_MAP_DEFAULT_MANIFESTS")?)?;
            let entries = [
                "seed",
                "defaultValue",
                "clear",
                "defaults",
                "missingParent",
                "defaultHistoric",
                "appendHistoric",
                "checkHistoricZero",
                "resetHistoric",
            ];
            let mut bundles = Vec::with_capacity(entries.len());
            let mut degrees = BTreeMap::<String, u8>::new();
            let mut plans = BTreeMap::<String, crate::Plan>::new();
            for entry in entries {
                let pin = pins
                    .get(entry)
                    .with_context(|| format!("missing {entry} manifest pin"))?;
                let bundle = artifacts::verify(&Path::new(&directory).join(entry), Some(pin))?;
                if matches!(entry, "seed" | "defaultValue") {
                    degrees.insert(
                        entry.to_owned(),
                        IrSource::load(bundle.file(Role::Circuit)?)?.k(),
                    );
                    plans.insert(
                        entry.to_owned(),
                        serde_json::from_slice(bundle.file(Role::Plan)?)?,
                    );
                }
                bundles.push(bundle);
            }
            let seed_degree = degrees["seed"];
            let default_degree = degrees["defaultValue"];
            let cache = ProofCache::new(
                setting("NOCTIUM_MAP_DEFAULT_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(&setting("NOCTIUM_MAP_DEFAULT_NODE")?, &cache)
                .await?;
            let seed_parameters = cache.parameters(seed_degree).await?;
            let default_parameters = cache.parameters(default_degree).await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let empty_state_config = br#"{
                "state": {
                    "values": [],
                    "nestedValues": [],
                    "nestedMaps": [],
                    "sets": [],
                    "lists": [],
                    "counters": [],
                    "ordinary": [],
                    "historic": [],
                    "records": []
                }
            }"#;
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(bundles)?,
                empty_state_config,
                ttl,
                &mut rng,
            )?;
            let seed = target.operation("seed", &seed_parameters, ttl)?;
            let default = target.operation("defaultValue", &default_parameters, ttl)?;
            let (deployed, deployment) = funded.deploy(&target, "seed").await?;
            let mut current = Some(deployed);
            let inputs = |plan: &crate::Plan, key: u64, amount: u64| {
                plan.circuit
                    .inputs
                    .iter()
                    .map(|input| {
                        let value = match input.name.as_str() {
                            "owner" => json!({"kind":"bytes","values":vec![7u8;32]}),
                            "key" => json!(key.to_string()),
                            "amount" => json!(amount.to_string()),
                            "enabled" => json!(true),
                            other => panic!("unexpected NativeMapDefault input {other}"),
                        };
                        (input.name.clone(), value)
                    })
                    .collect::<BTreeMap<_, _>>()
            };
            let assert_values = |receipt: &FinalizedReceipt, expected: &[(u64, u64)]| {
                let state: ContractState<Db> = native_decode(&receipt.contract_state)?;
                let StateValue::Array(slots) = state.data.get_ref() else {
                    anyhow::bail!("expected native state slots")
                };
                let Some(StateValue::Map(values)) = slots.get(0) else {
                    anyhow::bail!("expected root values Map in slot zero")
                };
                ensure!(
                    values.size() == expected.len(),
                    "Map entry count differs from expected finalized state"
                );
                for &(key, amount) in expected {
                    let entry = values.get(&crate::field_value(Fr::from(key)));
                    let Some(StateValue::Cell(value)) = entry.as_deref() else {
                        anyhow::bail!("expected Map cell at key {key}")
                    };
                    ensure!(
                        **value == crate::field_value(Fr::from(amount)),
                        "finalized Map value differs at key {key}"
                    );
                }
                Ok::<_, anyhow::Error>(())
            };

            let seeded_one = funded
                .call(
                    &seed,
                    &mut current,
                    &seed_parameters,
                    inputs(&plans["seed"], 1, 19),
                )
                .await?;
            let seeded = funded
                .call(
                    &seed,
                    &mut current,
                    &seed_parameters,
                    inputs(&plans["seed"], 2, 23),
                )
                .await?;
            assert_values(&seeded, &[(1, 19), (2, 23)])?;
            let inserted_default = funded
                .call(
                    &default,
                    &mut current,
                    &default_parameters,
                    inputs(&plans["defaultValue"], 3, 99),
                )
                .await?;
            assert_values(&inserted_default, &[(1, 19), (2, 23), (3, 0)])?;
            let replaced = funded
                .call(
                    &default,
                    &mut current,
                    &default_parameters,
                    inputs(&plans["defaultValue"], 1, 99),
                )
                .await?;
            assert_values(&replaced, &[(1, 0), (2, 23), (3, 0)])?;

            println!(
                "{}",
                json!({
                    "contractAddress": target.contract_address(),
                    "deploymentHeight": deployment.height,
                    "seedHeights": [seeded_one.height, seeded.height],
                    "missingDefaultHeight": inserted_default.height,
                    "replacementHeight": replaced.height,
                    "transactionIds": [seeded_one.transaction_id, seeded.transaction_id, inserted_default.transaction_id, replaced.transaction_id],
                    "finalValues": [[1, 0], [2, 23], [3, 0]],
                    "missingKeyInsertedAsZero": true,
                    "nonzeroKeyReplacedWithZero": true,
                    "siblingValuesPreserved": true,
                    "bundleManifestSha256": pins,
                    "k": {"seed": seed_degree, "defaultValue": default_degree},
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires authenticated CounterCompare bundles and the funded development node"]
    fn counter_comparison_finalizes_on_ledger() -> anyhow::Result<()> {
        use crate::zkir::IrSource;
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
        };
        use anyhow::{Context, ensure};
        use base_crypto::fab::AlignedValue;
        use futures::executor::block_on;
        use onchain_runtime::state::{ContractState, StateValue};
        use rand::{SeedableRng, rngs::StdRng};
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::proofs::Zkir;

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let directory = setting("NOCTIUM_COUNTER_COMPARE_BUNDLES")?;
            let manifest_pins: BTreeMap<String, String> =
                serde_json::from_str(&setting("NOCTIUM_COUNTER_COMPARE_MANIFESTS")?)?;
            let entries = ["inspect", "seedNested", "inspectNested"];
            let mut bundles = Vec::new();
            let mut degrees = BTreeMap::new();
            for entry in entries {
                let digest = manifest_pins
                    .get(entry)
                    .context("missing operation manifest pin")?;
                let bundle = artifacts::verify(&Path::new(&directory).join(entry), Some(digest))?;
                degrees.insert(entry, IrSource::load(bundle.file(Role::Circuit)?)?.k());
                bundles.push(bundle);
            }
            let cache = ProofCache::new(
                setting("NOCTIUM_COUNTER_COMPARE_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded =
                FundedLedgerTest::connect(&setting("NOCTIUM_COUNTER_COMPARE_NODE")?, &cache)
                    .await?;
            let mut parameters = BTreeMap::new();
            for (entry, degree) in &degrees {
                parameters.insert(*entry, cache.parameters(*degree).await?);
            }
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(bundles)?,
                br#"{"state":{"total":"0","epochs":[]}}"#,
                ttl,
                &mut rng,
            )?;
            let (deployed, deploy_receipt) = funded.deploy(&target, "inspect").await?;
            let mut current = Some(deployed);
            let inputs = BTreeMap::from([
                ("owner".into(), json!({"kind":"bytes","values":vec![1; 32]})),
                (
                    "spender".into(),
                    json!({"kind":"bytes","values":vec![2; 32]}),
                ),
                ("threshold".into(), json!("301")),
                ("enabled".into(), json!(true)),
            ]);
            let nested = target.operation("inspectNested", &parameters["inspectNested"], ttl)?;
            ensure!(
                nested
                    .prepare_call(
                        &mut current,
                        &parameters["inspectNested"],
                        inputs.clone(),
                        &mut rng
                    )
                    .is_err()
                    && current.is_some(),
                "a comparison on an unseeded path must reject and retain the state token"
            );

            let mut receipts = Vec::new();
            for entry in entries {
                let params = &parameters[entry];
                let operation = target.operation(entry, params, ttl)?;
                receipts.push(
                    funded
                        .call(&operation, &mut current, params, inputs.clone())
                        .await?,
                );
            }
            let [standalone, seed, nested] = receipts.as_slice() else {
                anyhow::bail!("expected three finalized operations");
            };
            ensure!(
                seed.contract_state == nested.contract_state,
                "ordered read changed finalized state"
            );
            let state: ContractState<Db> = native_decode(&nested.contract_state)?;
            let StateValue::Array(slots) = state.data.get_ref() else {
                anyhow::bail!("expected native state slots");
            };
            let Some(StateValue::Cell(counter)) = slots.get(0) else {
                anyhow::bail!("expected standalone counter");
            };
            ensure!(
                **counter == AlignedValue::from(300u64),
                "finalized counter did not reach 300"
            );
            let Some(StateValue::Map(owners)) = slots.get(1) else {
                anyhow::bail!("expected nested Counter map");
            };
            let owner = owners.get(&AlignedValue::from([1u8; 32]));
            let Some(StateValue::Map(spenders)) = owner.as_deref() else {
                anyhow::bail!("expected seeded owner map");
            };
            let spender = spenders.get(&AlignedValue::from([2u8; 32]));
            let Some(StateValue::Cell(nested_counter)) = spender.as_deref() else {
                anyhow::bail!("expected seeded nested Counter");
            };
            ensure!(
                **nested_counter == AlignedValue::from(300u64),
                "nested Counter differs from 300"
            );
            println!(
                "{}",
                json!({
                    "contractAddress": target.contract_address(),
                    "deploymentHeight": deploy_receipt.height,
                    "callHeights": [standalone.height, seed.height, nested.height],
                    "transactionIds": [standalone.transaction_id, seed.transaction_id, nested.transaction_id],
                    "threshold": 301,
                    "finalizedCounter": 300,
                    "finalizedNestedCounter": 300,
                    "unseededActiveRejectedBeforeSubmission": true,
                    "nestedReadStateUnchanged": true,
                    "exactPredictedStateAccepted": true,
                    "bundleManifestSha256": manifest_pins,
                    "k": degrees,
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires the authenticated checkTime bundle and funded development node"]
    fn block_time_uses_an_authenticated_current_state_and_explicit_context() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::{Error, LocalProver, WitnessContractTarget},
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use futures::{executor::block_on, future::pending};
        use rand::{SeedableRng, rngs::StdRng};
        use std::{env, path::Path};
        use transient_crypto::proofs::Zkir;

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let bundle_path = setting("NOCTIUM_BLOCK_TIME_CURRENT_BUNDLE")?;
            let pin = setting("NOCTIUM_BLOCK_TIME_CURRENT_MANIFEST_SHA256")?;
            let bundle = artifacts::verify(Path::new(&bundle_path), Some(&pin))?;
            let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
            let cache = ProofCache::new(
                setting("NOCTIUM_BLOCK_TIME_CURRENT_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(
                &setting("NOCTIUM_BLOCK_TIME_CURRENT_NODE")?,
                &cache,
            ).await?;
            let parameters = cache.parameters(circuit.k()).await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![bundle])?,
                br#"{"state":{}}"#,
                ttl,
                &mut rng,
            )?;
            let operation = target.operation("checkTime", &parameters, ttl)?;
            let (deployed, deployment) = funded.deploy(&target, "checkTime").await?;
            let mut current = Some(deployed);
            let inputs = || BTreeMap::from([
                ("enabled".into(), json!(true)),
                ("cutoff".into(), json!(u64::MAX.to_string())),
            ]);
            ensure!(
                matches!(
                    operation.prepare_call(&mut current, &parameters, inputs(), &mut rng),
                    Err(Error::InvalidPrivateInput)
                ) && current.is_some(),
                "missing active block context must reject without taking the current-state token"
            );

            let block = funded.node.sync()?.block;
            let prepared = operation.prepare_call_in_block(
                &mut current, &parameters, inputs(), &block, &mut rng,
            )?;
            ensure!(current.is_none(), "successful preparation must consume the token");
            let proved = prepared
                .prove(&LocalProver::new(StdRng::from_entropy()), &parameters, 1_048_576, pending())
                .await?;
            let (bound, receipt) = funded.finalize(proved.native()).await?;
            proved.contract_binding().context("missing current-state binding")?
                .admit_committed_state(
                    &receipt.contract_state, bound.expected_state(), &receipt.finalized_hash, false,
                )?;
            ensure!(receipt.contract_state == deployment.contract_state, "block-time read changed state");
            println!("{}", json!({
                "bundleManifestSha256": pin,
                "contractAddress": target.contract_address(),
                "deploymentHeight": deployment.height,
                "callHeight": receipt.height,
                "callTransactionId": receipt.transaction_id,
                "sourceBlockTimeUnixSeconds": block.tblock.to_secs().to_string(),
                "missingContextRetainedToken": true,
                "contextBoundCallPreservedState": true,
            }));
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires authenticated CounterAmounts bundles and the funded development node"]
    fn counter_amounts_finalize_dynamic_updates_on_ledger() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use base_crypto::fab::AlignedValue;
        use futures::executor::block_on;
        use onchain_runtime::state::{ContractState, StateValue};
        use rand::{SeedableRng, rngs::StdRng};
        use std::{env, path::Path};
        use transient_crypto::proofs::Zkir;

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let directory = setting("NOCTIUM_COUNTER_AMOUNTS_BUNDLES")?;
            let pins: BTreeMap<String, String> =
                serde_json::from_str(&setting("NOCTIUM_COUNTER_AMOUNTS_MANIFESTS")?)?;
            let entries = ["apply", "reduce", "guarded"];
            let mut bundles = Vec::with_capacity(entries.len());
            let mut degrees = BTreeMap::new();
            for entry in entries {
                let pin = pins
                    .get(entry)
                    .with_context(|| format!("missing {entry} manifest pin"))?;
                let bundle = artifacts::verify(&Path::new(&directory).join(entry), Some(pin))?;
                degrees.insert(entry, IrSource::load(bundle.file(Role::Circuit)?)?.k());
                bundles.push(bundle);
            }

            let cache = ProofCache::new(
                setting("NOCTIUM_COUNTER_AMOUNTS_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded =
                FundedLedgerTest::connect(&setting("NOCTIUM_COUNTER_AMOUNTS_NODE")?, &cache)
                    .await?;
            let mut parameters = BTreeMap::new();
            for (entry, degree) in &degrees {
                parameters.insert(*entry, cache.parameters(*degree).await?);
            }

            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(bundles)?,
                br#"{"state":{"total":"10","epochs":[]}}"#,
                ttl,
                &mut rng,
            )?;
            let apply = target.operation("apply", &parameters["apply"], ttl)?;
            let reduce = target.operation("reduce", &parameters["reduce"], ttl)?;
            let (deployed, deployment) = funded.deploy(&target, "apply").await?;
            let mut current = Some(deployed);

            let inputs = |amount: u16| {
                BTreeMap::from([
                    ("owner".into(), json!({"kind":"bytes","values":vec![4; 32]})),
                    (
                        "spender".into(),
                        json!({"kind":"bytes","values":vec![7; 32]}),
                    ),
                    ("amount".into(), json!(amount.to_string())),
                    ("enabled".into(), json!(true)),
                ])
            };
            ensure!(
                matches!(
                    reduce.prepare_call(&mut current, &parameters["reduce"], inputs(1), &mut rng),
                    Err(crate::proof::Error::InvalidPrivateInput)
                ) && current.is_some(),
                "reducing an uninitialized nested Counter path must reject before submission and retain its state token"
            );

            let zero = funded
                .call(&apply, &mut current, &parameters["apply"], inputs(0))
                .await?;
            let increased = funded
                .call(&apply, &mut current, &parameters["apply"], inputs(3))
                .await?;
            let reduced = funded
                .call(&reduce, &mut current, &parameters["reduce"], inputs(2))
                .await?;

            let assert_finalized = |receipt: &FinalizedReceipt, total: u64, epoch: Option<u64>| {
                let state: ContractState<Db> = native_decode(&receipt.contract_state)?;
                let StateValue::Array(slots) = state.data.get_ref() else {
                    anyhow::bail!("expected native CounterAmounts state slots")
                };
                let Some(StateValue::Cell(counter)) = slots.get(0) else {
                    anyhow::bail!("expected standalone Counter")
                };
                ensure!(
                    **counter == AlignedValue::from(total),
                    "finalized standalone Counter differs from {total}"
                );
                let Some(StateValue::Map(owners)) = slots.get(1) else {
                    anyhow::bail!("expected nested Counter map")
                };
                let owner = owners.get(&AlignedValue::from([4u8; 32]));
                match (owner.as_deref(), epoch) {
                    (None, None) => {}
                    (Some(StateValue::Map(spenders)), Some(expected)) => {
                        let spender = spenders.get(&AlignedValue::from([7u8; 32]));
                        let Some(StateValue::Cell(counter)) = spender.as_deref() else {
                            anyhow::bail!("expected nested spender Counter")
                        };
                        ensure!(
                            **counter == AlignedValue::from(expected),
                            "finalized nested Counter differs from {expected}"
                        );
                    }
                    _ => anyhow::bail!("nested Counter presence differs from expectation"),
                }
                Ok::<_, anyhow::Error>(())
            };
            assert_finalized(&deployment, 10, None)?;
            assert_finalized(&zero, 10, Some(0))?;
            assert_finalized(&increased, 13, Some(3))?;
            assert_finalized(&reduced, 11, Some(1))?;

            println!(
                "{}",
                json!({
                    "contractAddress": target.contract_address(),
                    "deploymentHeight": deployment.height,
                    "callHeights": [zero.height, increased.height, reduced.height],
                    "bundleManifestSha256": pins,
                    "k": degrees,
                    "operations": ["apply(amount=0)", "apply(amount=3)", "reduce(amount=2)"],
                    "uninitializedReduceRejectedBeforeSubmission": true,
                    "finalizedStates": [
                        {"total":10,"nested":null},
                        {"total":10,"nested":0},
                        {"total":13,"nested":3},
                        {"total":11,"nested":1}
                    ]
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires authenticated NativeMapRemove bundles and the funded development node"]
    fn nested_map_remove_finalizes_and_preserves_siblings() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use base_crypto::fab::AlignedValue;
        use futures::executor::block_on;
        use onchain_runtime::state::{ContractState, StateValue};
        use rand::{SeedableRng, rngs::StdRng};
        use std::{env, path::Path};
        use storage::{arena::Sp, storage::HashMap};
        use transient_crypto::{curve::Fr, proofs::Zkir};

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let directory = setting("NOCTIUM_MAP_REMOVE_BUNDLES")?;
            let pins: BTreeMap<String, String> =
                serde_json::from_str(&setting("NOCTIUM_MAP_REMOVE_MANIFESTS")?)?;
            let bundle = |operation: &str| {
                let pin = pins
                    .get(operation)
                    .context("missing operation manifest pin")?;
                Ok::<_, anyhow::Error>(artifacts::verify(
                    &Path::new(&directory).join(operation),
                    Some(pin),
                )?)
            };
            let seed_bundle = bundle("seed")?;
            let remove_bundle = bundle("remove")?;
            let subtree_bundle = bundle("removeOwner")?;
            let seed_degree = IrSource::load(seed_bundle.file(Role::Circuit)?)?.k();
            let remove_degree = IrSource::load(remove_bundle.file(Role::Circuit)?)?.k();
            let subtree_degree = IrSource::load(subtree_bundle.file(Role::Circuit)?)?.k();
            let cache = ProofCache::new(
                setting("NOCTIUM_MAP_REMOVE_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded =
                FundedLedgerTest::connect(&setting("NOCTIUM_MAP_REMOVE_NODE")?, &cache).await?;
            let seed_parameters = cache.parameters(seed_degree).await?;
            let remove_parameters = cache.parameters(remove_degree).await?;
            let subtree_parameters = cache.parameters(subtree_degree).await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![seed_bundle, remove_bundle, subtree_bundle])?,
                br#"{"state":{"escrow":[]}}"#,
                ttl,
                &mut rng,
            )?;
            let seed = target.operation("seed", &seed_parameters, ttl)?;
            let remove = target.operation("remove", &remove_parameters, ttl)?;
            let remove_owner = target.operation("removeOwner", &subtree_parameters, ttl)?;
            let (deployed, deployment) = funded.deploy(&target, "seed").await?;
            let mut current = Some(deployed);

            let bytes = |byte: u8| json!({"kind":"bytes","values":vec![byte;32]});
            let remove_inputs = |owner| {
                BTreeMap::from([
                    ("owner".into(), bytes(owner)),
                    ("spender".into(), bytes(1)),
                    ("enabled".into(), json!(true)),
                ])
            };
            let seed_inputs = BTreeMap::from([
                ("ownerA".into(), bytes(0)),
                ("ownerB".into(), bytes(3)),
                ("target".into(), bytes(1)),
                ("sibling".into(), bytes(2)),
            ]);
            let seeded = funded
                .call(&seed, &mut current, &seed_parameters, seed_inputs)
                .await?;
            ensure!(
                matches!(
                    remove.prepare_call(
                        &mut current,
                        &remove_parameters,
                        remove_inputs(9),
                        &mut rng
                    ),
                    Err(crate::proof::Error::InvalidPrivateInput)
                ) && current.is_some(),
                "a missing parent must fail preparation and retain the state token"
            );
            let removed = funded
                .call(&remove, &mut current, &remove_parameters, remove_inputs(0))
                .await?;
            let repeated = funded
                .call(&remove, &mut current, &remove_parameters, remove_inputs(0))
                .await?;
            ensure!(
                removed.contract_state == repeated.contract_state,
                "repeat removal changed state"
            );

            let subtree_inputs = |owner, enabled| {
                BTreeMap::from([
                    ("owner".into(), bytes(owner)),
                    ("enabled".into(), json!(enabled)),
                ])
            };
            let subtree = funded
                .call(
                    &remove_owner,
                    &mut current,
                    &subtree_parameters,
                    subtree_inputs(0, true),
                )
                .await?;
            let repeated_subtree = funded
                .call(
                    &remove_owner,
                    &mut current,
                    &subtree_parameters,
                    subtree_inputs(0, true),
                )
                .await?;
            let inactive_subtree = funded
                .call(
                    &remove_owner,
                    &mut current,
                    &subtree_parameters,
                    subtree_inputs(3, false),
                )
                .await?;
            ensure!(
                subtree.contract_state == repeated_subtree.contract_state
                    && subtree.contract_state == inactive_subtree.contract_state,
                "repeat or inactive subtree removal changed state"
            );

            let expected = |keep_owner, keep_target| {
                let record = |x: u64| {
                    StateValue::Cell(Sp::new(AlignedValue::concat(&[
                        crate::field_value(Fr::from(x)),
                        crate::field_value(Fr::from(x + 1)),
                    ])))
                };
                let mut owner_a = HashMap::new().insert([2u8; 32].into(), record(20));
                if keep_target {
                    owner_a = owner_a.insert([1u8; 32].into(), record(10));
                }
                let owner_b = HashMap::new().insert([1u8; 32].into(), record(30));
                let mut owners = HashMap::new().insert([3u8; 32].into(), StateValue::Map(owner_b));
                if keep_owner {
                    owners = owners.insert([0u8; 32].into(), StateValue::Map(owner_a));
                }
                StateValue::Array(vec![StateValue::Map(owners)].into())
            };
            let seed_state: ContractState<Db> = native_decode(&seeded.contract_state)?;
            let final_state: ContractState<Db> = native_decode(&removed.contract_state)?;
            ensure!(
                *seed_state.data.get_ref() == expected(true, true),
                "seeded records differ"
            );
            ensure!(
                *final_state.data.get_ref() == expected(true, false),
                "removed record or survivors differ"
            );
            let subtree_state: ContractState<Db> = native_decode(&subtree.contract_state)?;
            ensure!(
                *subtree_state.data.get_ref() == expected(false, false),
                "removed subtree or surviving owner differs"
            );
            println!(
                "{}",
                json!({
                    "contractAddress": target.contract_address(),
                    "deploymentHeight": deployment.height,
                    "seedHeight": seeded.height,
                    "removeHeight": removed.height,
                    "repeatHeight": repeated.height,
                    "removeOwnerHeight": subtree.height,
                    "repeatOwnerHeight": repeated_subtree.height,
                    "inactiveOwnerHeight": inactive_subtree.height,
                    "transactionIds": [seeded.transaction_id, removed.transaction_id, repeated.transaction_id,
                        subtree.transaction_id, repeated_subtree.transaction_id, inactive_subtree.transaction_id],
                    "missingParentRejectedBeforeSubmission": true,
                    "siblingRecordsPreserved": true,
                    "repeatStateUnchanged": true,
                    "subtreeRemovedAndOtherOwnerPreserved": true,
                    "repeatAndInactiveSubtreeStateUnchanged": true,
                    "exactPredictedStateAccepted": true,
                    "bundleManifestSha256": pins,
                    "k": {"seed":seed_degree,"remove":remove_degree,"removeOwner":subtree_degree},
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires authenticated NativeCounter bundles and the funded development node"]
    fn counter_reads_and_resets_finalize_on_ledger() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use base_crypto::fab::AlignedValue;
        use futures::executor::block_on;
        use onchain_runtime::state::{ContractState, StateValue};
        use rand::{SeedableRng, rngs::StdRng};
        use std::{env, path::Path};
        use transient_crypto::proofs::Zkir;

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let directory = setting("NOCTIUM_COUNTER_TRANSITIONS_BUNDLES")?;
            let pins: BTreeMap<String, String> =
                serde_json::from_str(&setting("NOCTIUM_COUNTER_TRANSITIONS_MANIFESTS")?)?;
            let entries = [
                "bump",
                "reduce",
                "resetCounters",
                "guarded",
                "readCounters",
                "readTotal",
            ];
            let mut bundles = Vec::new();
            let mut artifacts = BTreeMap::new();
            for entry in entries {
                let pin = pins.get(entry).context("missing operation manifest pin")?;
                let bundle = artifacts::verify(&Path::new(&directory).join(entry), Some(pin))?;
                let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
                artifacts.insert(entry, (plan, IrSource::load(bundle.file(Role::Circuit)?)?));
                bundles.push(bundle);
            }
            let cache = ProofCache::new(
                setting("NOCTIUM_COUNTER_TRANSITIONS_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded =
                FundedLedgerTest::connect(&setting("NOCTIUM_COUNTER_TRANSITIONS_NODE")?, &cache)
                    .await?;
            let mut parameters = BTreeMap::new();
            for (entry, (_, circuit)) in &artifacts {
                parameters.insert(*entry, cache.parameters(circuit.k()).await?);
            }
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(bundles)?,
                br#"{"state":{"total":"0","epochs":[]}}"#,
                ttl,
                &mut rng,
            )?;
            let (deployed, deployment) = funded.deploy(&target, "readTotal").await?;
            let mut current = Some(deployed);
            let inputs = |entry: &str, spender: u8| {
                artifacts[entry]
                    .0
                    .circuit
                    .inputs
                    .iter()
                    .map(|input| {
                        let value = match input.name.as_str() {
                            "owner" => json!({"kind":"bytes","values":vec![0u8;32]}),
                            "spender" => json!({"kind":"bytes","values":vec![spender;32]}),
                            "enabled" => json!(true),
                            other => panic!("unexpected Counter fixture input {other}"),
                        };
                        (input.name.clone(), value)
                    })
                    .collect::<BTreeMap<_, _>>()
            };
            let call =
                async |entry: &str,
                       spender,
                       state: &mut Option<crate::proof::CurrentStateContext>| {
                    let params = &parameters[entry];
                    let operation = target.operation(entry, params, ttl)?;
                    funded
                        .call(&operation, state, params, inputs(entry, spender))
                        .await
                };
            let rejects = |entry: &str,
                           spender,
                           state: &mut Option<crate::proof::CurrentStateContext>|
             -> anyhow::Result<()> {
                let params = &parameters[entry];
                let operation = target.operation(entry, params, ttl)?;
                let error = operation
                    .prepare_call(
                        state,
                        params,
                        inputs(entry, spender),
                        &mut StdRng::from_entropy(),
                    )
                    .err();
                ensure!(
                    error == Some(crate::proof::Error::InvalidPrivateInput) && state.is_some(),
                    "missing Counter path must reject preparation and retain the state token"
                );
                Ok(())
            };
            let values = |receipt: &FinalizedReceipt,
                          total,
                          expected_epochs: &[(u8, u64)]|
             -> anyhow::Result<()> {
                let state: ContractState<Db> = native_decode(&receipt.contract_state)?;
                let StateValue::Array(slots) = state.data.get_ref() else {
                    anyhow::bail!("expected native state slots");
                };
                let Some(StateValue::Cell(counter)) = slots.get(0) else {
                    anyhow::bail!("expected standalone Counter");
                };
                ensure!(
                    **counter == AlignedValue::from(total),
                    "standalone Counter differs"
                );
                let Some(StateValue::Map(owners)) = slots.get(1) else {
                    anyhow::bail!("expected owner map");
                };
                if expected_epochs.is_empty() {
                    ensure!(owners.size() == 0, "initial owner map differs");
                } else {
                    let owner = owners.get(&AlignedValue::from([0u8; 32]));
                    let Some(StateValue::Map(epochs)) = owner.as_deref() else {
                        anyhow::bail!("expected epoch map");
                    };
                    ensure!(
                        owners.size() == 1 && epochs.size() == expected_epochs.len(),
                        "unexpected Counter keys"
                    );
                    for &(key, amount) in expected_epochs {
                        let entry = epochs.get(&AlignedValue::from([key; 32]));
                        let Some(StateValue::Cell(counter)) = entry.as_deref() else {
                            anyhow::bail!("missing epoch Counter");
                        };
                        ensure!(
                            **counter == AlignedValue::from(amount),
                            "nested Counter differs"
                        );
                    }
                }
                Ok(())
            };

            rejects("resetCounters", 1, &mut current)?;
            let initial = call("readTotal", 1, &mut current).await?;
            ensure!(
                initial.contract_state == deployment.contract_state,
                "standalone read changed state"
            );
            values(&initial, 0u64, &[])?;
            let bumped = call("bump", 1, &mut current).await?;
            values(&bumped, 3u64, &[(1, 1)])?;
            let bumped_twice = call("bump", 1, &mut current).await?;
            values(&bumped_twice, 6u64, &[(1, 2)])?;
            let reduced = call("reduce", 1, &mut current).await?;
            values(&reduced, 4u64, &[(1, 1)])?;
            rejects("readCounters", 2, &mut current)?;
            let created = call("resetCounters", 2, &mut current).await?;
            values(&created, 0u64, &[(1, 1), (2, 0)])?;
            let reset = call("resetCounters", 1, &mut current).await?;
            values(&reset, 0u64, &[(1, 0), (2, 0)])?;
            let read = call("readCounters", 1, &mut current).await?;
            ensure!(
                read.contract_state == reset.contract_state,
                "nested read changed state"
            );

            let state: ContractState<Db> = native_decode(&read.contract_state)?;
            let address = ContractAddress(HashOutput(
                hex::decode(target.contract_address())?
                    .try_into()
                    .map_err(|_| anyhow::anyhow!("invalid fixture address"))?,
            ));
            let (plan, circuit) = &artifacts["readCounters"];
            let execution = crate::prepare(
                plan,
                &inputs("readCounters", 1),
                &state.data,
                &funded.node.sync()?.state.parameters,
                address,
            )?;
            crate::check(&execution, circuit)?;
            ensure!(
                execution.returns_json() == BTreeMap::from([
                    ("epochValue".into(), json!("0")),
                    ("totalValue".into(), json!("0")),
                ]),
                "committed read values differ from the finalized counters"
            );
            let receipts = [initial, bumped, bumped_twice, reduced, created, reset, read];
            println!(
                "{}",
                json!({
                    "contractAddress": target.contract_address(),
                    "deploymentHeight": deployment.height,
                    "calls": receipts.iter().map(|receipt| json!([receipt.height,receipt.transaction_id])).collect::<Vec<_>>(),
                    "exactPredictedStateAccepted": true,
                    "readsUnchanged": true,
                    "missingParentAndLeafRejectedBeforeSubmission": true,
                    "resetCreatedAbsentLeaf": true,
                    "resetPreservedSibling": true,
                    "committedReadValues": execution.returns_json(),
                    "bundleManifestSha256": pins,
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires authenticated NativeNestedMapReset bundles and the funded development node"]
    fn nested_map_reset_retains_initialized_empty_parent_and_sibling() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use futures::executor::block_on;
        use onchain_runtime::state::{ContractState, StateValue};
        use rand::{SeedableRng, rngs::StdRng};
        use std::{env, path::Path};
        use storage::{arena::Sp, storage::HashMap};
        use transient_crypto::{curve::Fr, proofs::Zkir};

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let directory = setting("NOCTIUM_NESTED_MAP_RESET_BUNDLES")?;
            let pins: BTreeMap<String, String> =
                serde_json::from_str(&setting("NOCTIUM_NESTED_MAP_RESET_MANIFESTS")?)?;
            let bundle = |operation: &str| {
                let pin = pins
                    .get(operation)
                    .with_context(|| format!("missing {operation} manifest pin"))?;
                Ok::<_, anyhow::Error>(artifacts::verify(
                    &Path::new(&directory).join(operation),
                    Some(pin),
                )?)
            };
            let seed_bundle = bundle("seedNested")?;
            let clear_bundle = bundle("clearInner")?;
            let seed_degree = IrSource::load(seed_bundle.file(Role::Circuit)?)?.k();
            let clear_degree = IrSource::load(clear_bundle.file(Role::Circuit)?)?.k();
            let cache = ProofCache::new(
                setting("NOCTIUM_NESTED_MAP_RESET_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(
                &setting("NOCTIUM_NESTED_MAP_RESET_NODE")?,
                &cache,
            )
            .await?;
            let seed_parameters = cache.parameters(seed_degree).await?;
            let clear_parameters = cache.parameters(clear_degree).await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![seed_bundle, clear_bundle])?,
                br#"{"state":{"nestedValues":[]}}"#,
                ttl,
                &mut rng,
            )?;
            let seed = target.operation("seedNested", &seed_parameters, ttl)?;
            let clear = target.operation("clearInner", &clear_parameters, ttl)?;
            let (deployed, deployment) = funded.deploy(&target, "seedNested").await?;
            let mut current = Some(deployed);
            let seed_inputs = BTreeMap::from([
                ("owner".into(), json!("10")),
                ("targetA".into(), json!("1")),
                ("amountA".into(), json!("19")),
                ("targetB".into(), json!("2")),
                ("amountB".into(), json!("23")),
                ("siblingOwner".into(), json!("20")),
                ("siblingKey".into(), json!("3")),
                ("siblingAmount".into(), json!("31")),
            ]);
            let clear_inputs = |owner: u64, active: bool| {
                BTreeMap::from([
                    ("owner".into(), json!(owner.to_string())),
                    ("active".into(), json!(active)),
                ])
            };
            let key = |value| crate::field_value(Fr::from(value));
            let cell = |value| StateValue::Cell(Sp::new(key(value)));
            let expected = |reset_owner: bool, initialize_missing: bool| {
                let mut owner = HashMap::new();
                if !reset_owner {
                    owner = owner
                        .insert(key(1u64), cell(19u64))
                        .insert(key(2u64), cell(23u64));
                }
                let sibling = HashMap::new().insert(key(3u64), cell(31u64));
                let mut parents = HashMap::new()
                    .insert(key(10u64), StateValue::Map(owner))
                    .insert(key(20u64), StateValue::Map(sibling));
                if initialize_missing {
                    parents = parents.insert(key(30u64), StateValue::Map(HashMap::new()));
                }
                parents
            };
            let assert_state = |receipt: &FinalizedReceipt,
                                reset_owner: bool,
                                initialize_missing: bool|
             -> anyhow::Result<()> {
                let state: ContractState<Db> = native_decode(&receipt.contract_state)?;
                let StateValue::Array(slots) = state.data.get_ref() else {
                    anyhow::bail!("expected native state slots")
                };
                let Some(StateValue::Map(outer)) = slots.get(0) else {
                    anyhow::bail!("expected outer Map in native slot zero")
                };
                ensure!(
                    *outer == expected(reset_owner, initialize_missing),
                    "nested Map state differs from exact expected parent and sibling entries"
                );
                Ok(())
            };

            let seeded = funded
                .call(&seed, &mut current, &seed_parameters, seed_inputs)
                .await?;
            assert_state(&seeded, false, false)?;
            let inactive = funded
                .call(
                    &clear,
                    &mut current,
                    &clear_parameters,
                    clear_inputs(30, false),
                )
                .await?;
            ensure!(
                inactive.contract_state == seeded.contract_state,
                "inactive reset of missing parent changed finalized state"
            );
            let initialized = funded
                .call(
                    &clear,
                    &mut current,
                    &clear_parameters,
                    clear_inputs(30, true),
                )
                .await?;
            assert_state(&initialized, false, true)?;
            let cleared = funded
                .call(
                    &clear,
                    &mut current,
                    &clear_parameters,
                    clear_inputs(10, true),
                )
                .await?;
            assert_state(&cleared, true, true)?;
            println!(
                "{}",
                json!({
                    "contractAddress": target.contract_address(),
                    "deploymentHeight": deployment.height,
                    "seedHeight": seeded.height,
                    "inactiveMissingParentHeight": inactive.height,
                    "activeMissingParentHeight": initialized.height,
                    "resetHeight": cleared.height,
                    "transactionIds": [seeded.transaction_id, inactive.transaction_id, initialized.transaction_id, cleared.transaction_id],
                    "finalValues": {"owner10": {}, "owner20": {"3": 31}, "owner30": {}},
                    "inactiveMissingParentWasNoOp": true,
                    "activeMissingParentInitializedEmptyMap": true,
                    "selectedInnerMapResetAndSiblingPreserved": true,
                    "bundleManifestSha256": pins,
                    "k": {"seedNested": seed_degree, "clearInner": clear_degree},
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires the authenticated SealedSetConstructor inspect bundle and a funded development node"]
    fn sealed_root_set_constructor_finalizes_exact_immutable_state() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use onchain_runtime::state::ContractState;
        use rand::{SeedableRng, rngs::StdRng};
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::proofs::Zkir;

        futures::executor::block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let directory = setting("NOCTIUM_SEALED_SET_FUNDED_BUNDLE")?;
            let manifest = setting("NOCTIUM_SEALED_SET_FUNDED_MANIFEST")?;
            let bundle = artifacts::verify(Path::new(&directory), Some(&manifest))?;
            let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
            ensure!(plan.entrypoint == "inspect", "expected sealed Set inspect bundle");
            let k = IrSource::load(bundle.file(Role::Circuit)?)?.k();
            let arguments = BTreeMap::from([("key".into(), json!("17"))]);
            let expected = crate::constructor::construct_state(&plan, &arguments)?;

            let cache = ProofCache::new(
                setting("NOCTIUM_SEALED_SET_FUNDED_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(
                &setting("NOCTIUM_SEALED_SET_FUNDED_NODE")?, &cache,
            ).await?;
            let parameters = cache.parameters(k).await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![bundle])?,
                &serde_json::to_vec(&json!({"state": arguments}))?,
                ttl,
                &mut StdRng::from_entropy(),
            )?;
            let inspect = target.operation("inspect", &parameters, ttl)?;
            let (state, deployment) = funded.deploy(&target, "inspect").await?;
            let deployed: ContractState<Db> = native_decode(&deployment.contract_state)?;
            ensure!(
                deployed.data.get_ref() == expected.get_ref(),
                "deployed sealed Sets differ from native construction"
            );

            let mut current = Some(state);
            let receipt = funded.call(
                &inspect, &mut current, &parameters,
                BTreeMap::from([("key".into(), json!("17"))]),
            ).await?;
            ensure!(
                receipt.contract_state == deployment.contract_state,
                "sealed Set inspect changed finalized state bytes"
            );
            println!("{}", json!({
                "contractAddress": target.contract_address(),
                "bundleManifestSha256": manifest,
                "k": k,
                "deploymentHeight": deployment.height,
                "deploymentTransactionId": deployment.transaction_id,
                "finalizedHeight": receipt.height,
                "finalizedHash": receipt.finalized_hash,
                "transactionId": receipt.transaction_id,
                "constructStateMatchedDeployment": true,
                "inspectPreservedExactStateBytes": true,
            }));
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires the authenticated SealedCounterListConstructor inspect bundle and funded development node"]
    fn sealed_counter_list_constructor_finalizes_exact_immutable_state() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use futures::executor::block_on;
        use onchain_runtime::state::ContractState;
        use rand::{SeedableRng, rngs::StdRng};
        use serde_json::json;
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::proofs::Zkir;

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let directory = setting("NOCTIUM_SEALED_ADTS_FUNDED_BUNDLE")?;
            let manifest = setting("NOCTIUM_SEALED_ADTS_FUNDED_MANIFEST")?;
            let bundle = artifacts::verify(Path::new(&directory), Some(&manifest))?;
            let bundle_digest = bundle
                .authenticated_manifest_sha256()
                .context("verified bundle did not retain its manifest pin")?
                .to_owned();
            let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
            ensure!(plan.entrypoint == "inspect", "expected inspect bundle");
            let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
            let degree = circuit.k();
            let constructor_arguments = BTreeMap::from([
                ("amount".into(), json!("5")),
                ("first".into(), json!("17")),
            ]);
            let expected_state =
                crate::constructor::construct_state(&plan, &constructor_arguments)?;

            let cache = ProofCache::new(
                setting("NOCTIUM_SEALED_ADTS_FUNDED_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(
                &setting("NOCTIUM_SEALED_ADTS_FUNDED_NODE")?,
                &cache,
            )
            .await?;
            let parameters = cache.parameters(degree).await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![bundle])?,
                br#"{"state":{"amount":"5","first":"17"}}"#,
                ttl,
                &mut rng,
            )?;
            let inspect = target.operation("inspect", &parameters, ttl)?;
            let (deployed, deployment) = funded.deploy(&target, "inspect").await?;
            let deployed_state: ContractState<Db> = native_decode(&deployment.contract_state)?;
            ensure!(
                deployed_state.data.get_ref() == expected_state.get_ref(),
                "deployed constructor state differs from native construct_state"
            );

            let mut current = Some(deployed);
            let inspected = funded
                .call(&inspect, &mut current, &parameters, BTreeMap::new())
                .await?;
            ensure!(
                inspected.contract_state == deployment.contract_state,
                "no-input inspect changed the exact finalized state bytes"
            );
            let inspected_state: ContractState<Db> = native_decode(&inspected.contract_state)?;
            ensure!(
                inspected_state.data.get_ref() == expected_state.get_ref(),
                "inspected state differs from native construct_state"
            );

            println!(
                "{}",
                json!({
                    "scope": "deploy SealedCounterListConstructor(amount=5, first=17), then one no-input inspect",
                    "contractAddress": target.contract_address(),
                    "bundleManifestSha256": bundle_digest,
                    "degree": degree,
                    "deploymentReceipt": {
                        "height": deployment.height,
                        "finalizedHeight": deployment.finalized_height,
                        "blockHash": deployment.block_hash,
                        "finalizedHash": deployment.finalized_hash,
                        "transactionId": deployment.transaction_id
                    },
                    "inspectReceipt": {
                        "height": inspected.height,
                        "finalizedHeight": inspected.finalized_height,
                        "blockHash": inspected.block_hash,
                        "finalizedHash": inspected.finalized_hash,
                        "transactionId": inspected.transaction_id
                    },
                    "constructStateMatchedDeployment": true,
                    "inspectPreservedExactStateBytes": true
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "submits funded GenericRecordCell updates to the authorized isolated localnet"]
    fn generic_record_cell_finalizes_guarded_record_updates() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use futures::executor::block_on;
        use onchain_runtime::state::ContractState;
        use rand::{SeedableRng, rngs::StdRng};
        use serde_json::json;
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::proofs::Zkir;

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let endpoint = setting("NOCTIUM_GENERIC_RECORD_CELL_FUNDED_NODE")?;
            ensure!(
                endpoint == "http://127.0.0.1:19944",
                "GenericRecordCell requires the authorized loopback node on port 19944"
            );

            let entries = [
                (
                    "inspect",
                    "NOCTIUM_GENERIC_RECORD_CELL_FUNDED_INSPECT_BUNDLE",
                    "NOCTIUM_GENERIC_RECORD_CELL_FUNDED_INSPECT_SHA256",
                ),
                (
                    "update",
                    "NOCTIUM_GENERIC_RECORD_CELL_FUNDED_UPDATE_BUNDLE",
                    "NOCTIUM_GENERIC_RECORD_CELL_FUNDED_UPDATE_SHA256",
                ),
            ];
            let mut bundles = Vec::with_capacity(entries.len());
            let mut plans = BTreeMap::new();
            let mut circuits = BTreeMap::new();
            let mut degrees = BTreeMap::new();
            let mut pins = BTreeMap::new();
            for (entry, directory_env, digest_env) in entries {
                let directory = setting(directory_env)?;
                let digest = setting(digest_env)?;
                let bundle = artifacts::verify(Path::new(&directory), Some(&digest))?;
                let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
                ensure!(
                    plan.entrypoint == entry,
                    "unexpected GenericRecordCell {entry} plan"
                );
                let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
                degrees.insert(entry.to_owned(), circuit.k());
                plans.insert(entry.to_owned(), plan);
                circuits.insert(entry.to_owned(), circuit);
                pins.insert(entry.to_owned(), digest);
                bundles.push(bundle);
            }

            let cache = ProofCache::new(
                setting("NOCTIUM_GENERIC_RECORD_CELL_FUNDED_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(&endpoint, &cache).await?;
            let mut parameters = BTreeMap::new();
            for entry in ["inspect", "update"] {
                parameters.insert(entry, cache.parameters(degrees[entry]).await?);
            }
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let constructor_inputs = BTreeMap::from([
                ("issued".to_owned(), json!("5")),
                ("spent".to_owned(), json!("42")),
                (
                    "initialTag".to_owned(),
                    json!({"kind":"bytes", "values":[1, 2, 3, 4]}),
                ),
            ]);
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(bundles)?,
                &serde_json::to_vec(&json!({"state": &constructor_inputs}))?,
                ttl,
                &mut StdRng::from_entropy(),
            )?;
            let inspect = target.operation("inspect", &parameters["inspect"], ttl)?;
            let update = target.operation("update", &parameters["update"], ttl)?;
            let address = ContractAddress(HashOutput(
                hex::decode(target.contract_address())?
                    .try_into()
                    .map_err(|_| anyhow::anyhow!("invalid GenericRecordCell address"))?,
            ));
            let mut model_state = crate::construct_state(&plans["inspect"], &constructor_inputs)?;
            let (state, deployment) = funded.deploy(&target, "inspect").await?;
            let mut current = Some(state);
            let deployed: ContractState<Db> = native_decode(&deployment.contract_state)?;
            ensure!(
                deployment.contract_address == target.contract_address()
                    && deployment.chain.genesis == DEVELOPMENT_GENESIS
                    && deployed.data.get_ref() == model_state.get_ref(),
                "deployed GenericRecordCell state differs from the native constructor"
            );
            let mut last_state_bytes = deployment.contract_state.clone();

            let record_result = |issued: &str, spent: &str, tag: [u8; 4]| {
                json!({
                    "kind":"struct",
                    "id":"GenericRecordCell.Ledger",
                    "fields":[
                        {"name":"issued", "value":{"kind":"native", "value":issued}},
                        {"name":"spent", "value":{"kind":"native", "value":spent}},
                        {"name":"tag", "value":{"kind":"bytes", "values":tag}},
                    ],
                })
            };
            let expected_returns = |value| BTreeMap::from([("result".to_owned(), value)]);
            let mut expected_issued = "5".to_owned();
            let mut expected_spent = "42".to_owned();
            let mut expected_tag = [1, 2, 3, 4];
            let update_inputs = |enabled: bool, issued: &str, spent: &str, tag: [u8; 4]| {
                let mut inputs = BTreeMap::from([
                    ("enabled".to_owned(), json!(enabled)),
                    ("next.issued".to_owned(), json!(issued)),
                    ("next.spent".to_owned(), json!(spent)),
                ]);
                for (index, byte) in tag.into_iter().enumerate() {
                    inputs.insert(format!("next.tag.{index}"), json!(byte.to_string()));
                }
                inputs
            };
            let receipt_record = |receipt: &FinalizedReceipt| {
                json!({
                    "height": receipt.height,
                    "finalizedHeight": receipt.finalized_height,
                    "blockHash": receipt.block_hash,
                    "finalizedHash": receipt.finalized_hash,
                    "transactionId": receipt.transaction_id,
                    "stateBytes": receipt.contract_state.len(),
                    "stateSha256": hex::encode(sha2::Sha256::digest(&receipt.contract_state)),
                })
            };
            let record_call = |entry: &str, receipt: &FinalizedReceipt, returns: Json| {
                json!({
                    "entrypoint": entry,
                    "checkedReturns": returns,
                    "receipt": receipt_record(receipt),
                })
            };

            let empty = BTreeMap::new();
            let mut calls = Vec::new();
            let snapshot = funded.node.sync()?;
            let initial_read = crate::prepare(
                &plans["inspect"],
                &empty,
                &model_state,
                &snapshot.state.parameters,
                address,
            )?;
            ensure!(
                crate::check(&initial_read, &circuits["inspect"])?
                    == initial_read.activity_schedule
                    && initial_read.returns_json()
                        == expected_returns(record_result("5", "42", [1, 2, 3, 4])),
                "initial GenericRecordCell read differs from the constructor"
            );
            let (bound, initial_read_receipt) = funded
                .call_with_bound(
                    &inspect,
                    &mut current,
                    &parameters["inspect"],
                    empty.clone(),
                )
                .await?;
            bound.check_receipt(&initial_read_receipt)?;
            ensure!(
                initial_read_receipt.contract_state == deployment.contract_state
                    && initial_read_receipt.contract_state == bound.expected_state(),
                "initial GenericRecordCell read changed exact state bytes"
            );
            let initial_read_state: ContractState<Db> =
                native_decode(&initial_read_receipt.contract_state)?;
            ensure!(
                initial_read_state.data.get_ref() == model_state.get_ref(),
                "initial GenericRecordCell read differs from the native constructor state"
            );
            calls.push(record_call(
                "inspect",
                &initial_read_receipt,
                json!(initial_read.returns_json()),
            ));

            for (enabled, issued, spent, tag, label) in [
                (false, "11", "13", [9, 8, 7, 6], "disabled update"),
                (true, "8", "99", [128, 0, 255, 42], "enabled update"),
            ] {
                let inputs = update_inputs(enabled, issued, spent, tag);
                let snapshot = funded.node.sync()?;
                let execution = crate::prepare(
                    &plans["update"],
                    &inputs,
                    &model_state,
                    &snapshot.state.parameters,
                    address,
                )?;
                let returns = if enabled {
                    record_result(issued, spent, tag)
                } else {
                    record_result(&expected_issued, &expected_spent, expected_tag)
                };
                ensure!(
                    crate::check(&execution, &circuits["update"])?
                        == execution.activity_schedule
                        && execution.returns_json() == expected_returns(returns.clone()),
                    "native GenericRecordCell {label} return or relation mismatch"
                );
                let (bound, receipt) = funded
                    .call_with_bound(
                        &update,
                        &mut current,
                        &parameters["update"],
                        inputs,
                    )
                    .await?;
                bound.check_receipt(&receipt)?;
                ensure!(
                    receipt.chain.genesis == DEVELOPMENT_GENESIS
                        && receipt.contract_address == target.contract_address()
                        && receipt.contract_state == bound.expected_state(),
                    "finalized GenericRecordCell {label} has the wrong chain, contract, or state"
                );
                let decoded: ContractState<Db> = native_decode(&receipt.contract_state)?;
                ensure!(
                    decoded.data.get_ref() == execution.after.state.get_ref(),
                    "finalized GenericRecordCell {label} differs from checked native state"
                );
                if enabled {
                    ensure!(
                        receipt.contract_state != last_state_bytes,
                        "enabled GenericRecordCell update did not change state"
                    );
                    expected_issued = issued.to_owned();
                    expected_spent = spent.to_owned();
                    expected_tag = tag;
                } else {
                    ensure!(
                        receipt.contract_state == last_state_bytes
                            && execution.after.state.get_ref() == model_state.get_ref(),
                        "disabled GenericRecordCell update changed exact state bytes"
                    );
                }
                model_state = execution.after.state;
                last_state_bytes = receipt.contract_state.clone();
                calls.push(record_call(
                    "update",
                    &receipt,
                    json!(expected_returns(returns)),
                ));
            }

            let invalid = update_inputs(true, "8", "99", [128, 0, 255, 42]);
            let mut invalid = invalid;
            invalid.insert("next.tag.0".into(), json!("256"));
            let snapshot = funded.node.sync()?;
            let invalid_execution = crate::prepare(
                &plans["update"],
                &invalid,
                &model_state,
                &snapshot.state.parameters,
                address,
            )
            .and_then(|execution| {
                crate::check(&execution, &circuits["update"]).map(|_| ())
            });
            ensure!(
                invalid_execution.is_err(),
                "out-of-range GenericRecordCell byte passed native preparation"
            );

            let snapshot = funded.node.sync()?;
            let final_read = crate::prepare(
                &plans["inspect"],
                &empty,
                &model_state,
                &snapshot.state.parameters,
                address,
            )?;
            ensure!(
                crate::check(&final_read, &circuits["inspect"])?
                    == final_read.activity_schedule
                    && final_read.returns_json()
                        == expected_returns(record_result(
                            &expected_issued,
                            &expected_spent,
                            expected_tag,
                        )),
                "final GenericRecordCell read differs from enabled update"
            );
            let (bound, final_read_receipt) = funded
                .call_with_bound(
                    &inspect,
                    &mut current,
                    &parameters["inspect"],
                    empty,
                )
                .await?;
            bound.check_receipt(&final_read_receipt)?;
            let final_state: ContractState<Db> = native_decode(&final_read_receipt.contract_state)?;
            ensure!(
                final_read_receipt.contract_state == bound.expected_state()
                    && final_read_receipt.contract_state == last_state_bytes
                    && final_state.data.get_ref() == model_state.get_ref(),
                "final GenericRecordCell inspect does not preserve enabled state"
            );
            calls.push(record_call(
                "inspect",
                &final_read_receipt,
                json!(final_read.returns_json()),
            ));

            println!(
                "{}",
                json!({
                    "contractAddress": target.contract_address(),
                    "genesis": funded.node.policy.genesis,
                    "ledgerVersion": "9.1.0.1",
                    "zkirRelease": "3.2.1",
                    "profile": crate::profile::NAME,
                    "bundleManifestSha256": pins,
                    "k": degrees,
                    "deployment": receipt_record(&deployment),
                    "calls": calls,
                    "constructorStateMatchedNativePlan": true,
                    "disabledUpdatePreservedExactStateBytes": true,
                    "enabledUpdateStoredExactRecord": true,
                    "finalizedStateMatchedNativeExecution": true,
                    "outOfRangeByteRejectedBeforeSubmission": true,
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "submits funded FlatRecordCellReset updates to the authorized isolated localnet"]
    fn flat_record_cell_reset_finalizes_guarded_record_defaults() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use futures::executor::block_on;
        use onchain_runtime::state::ContractState;
        use rand::{SeedableRng, rngs::StdRng};
        use serde_json::json;
        use sha2::Digest;
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::proofs::Zkir;

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let endpoint = setting("NOCTIUM_FLAT_RECORD_CELL_RESET_FUNDED_NODE")?;
            ensure!(
                endpoint == "http://127.0.0.1:19944",
                "FlatRecordCellReset requires the authorized loopback node on port 19944"
            );

            let entries = [
                (
                    "clear",
                    "NOCTIUM_FLAT_RECORD_CELL_RESET_FUNDED_CLEAR_BUNDLE",
                    "NOCTIUM_FLAT_RECORD_CELL_RESET_FUNDED_CLEAR_SHA256",
                ),
                (
                    "guardedClear",
                    "NOCTIUM_FLAT_RECORD_CELL_RESET_FUNDED_GUARDED_CLEAR_BUNDLE",
                    "NOCTIUM_FLAT_RECORD_CELL_RESET_FUNDED_GUARDED_CLEAR_SHA256",
                ),
            ];
            let mut bundles = Vec::with_capacity(entries.len());
            let mut plans = BTreeMap::new();
            let mut circuits = BTreeMap::new();
            let mut degrees = BTreeMap::new();
            let mut pins = BTreeMap::new();
            for (entry, directory_env, digest_env) in entries {
                let directory = setting(directory_env)?;
                let digest = setting(digest_env)?;
                let bundle = artifacts::verify(Path::new(&directory), Some(&digest))?;
                let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
                ensure!(
                    plan.entrypoint == entry,
                    "unexpected FlatRecordCellReset {entry} plan"
                );
                let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
                degrees.insert(entry.to_owned(), circuit.k());
                plans.insert(entry.to_owned(), plan);
                circuits.insert(entry.to_owned(), circuit);
                pins.insert(entry.to_owned(), digest);
                bundles.push(bundle);
            }

            let parameter_cache = setting("NOCTIUM_FLAT_RECORD_CELL_RESET_FUNDED_PARAMETER_CACHE")?;
            let cache = ProofCache::new(
                parameter_cache.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(&endpoint, &cache).await?;
            let parameters = cache.parameters(degrees["guardedClear"]).await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let ledger_value = |issued: &str, spent: &str| {
                json!({
                    "kind":"struct",
                    "id":"FlatRecordCellReset.Ledger",
                    "fields":[
                        {"name":"issued", "value":{"kind":"native", "value":issued}},
                        {"name":"spent", "value":{"kind":"native", "value":spent}},
                    ],
                })
            };
            let state_values = |issued: &str, spent: &str| {
                BTreeMap::from([
                    ("marker".to_owned(), json!("37")),
                    ("ledger".to_owned(), ledger_value(issued, spent)),
                ])
            };
            let initial_values = state_values("5", "42");
            let reset_values = state_values("0", "0");
            let model_plan = &plans["guardedClear"];
            let initial_model = crate::create_state(model_plan, &initial_values)?;
            let reset_model = crate::create_state(model_plan, &reset_values)?;
            let state_config = serde_json::to_vec(&json!({"state": &initial_values}))?;
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(bundles)?,
                &state_config,
                ttl,
                &mut StdRng::from_entropy(),
            )?;
            let guarded_clear = target.operation("guardedClear", &parameters, ttl)?;
            let address = ContractAddress(HashOutput(
                hex::decode(target.contract_address())?
                    .try_into()
                    .map_err(|_| anyhow::anyhow!("invalid FlatRecordCellReset address"))?,
            ));
            let (state, deployment) = funded.deploy(&target, "guardedClear").await?;
            let mut current = Some(state);
            let deployed: ContractState<Db> = native_decode(&deployment.contract_state)?;
            ensure!(
                deployment.contract_address == target.contract_address()
                    && deployment.chain.genesis == DEVELOPMENT_GENESIS
                    && deployed.data.get_ref() == initial_model.get_ref(),
                "deployed FlatRecordCellReset state differs from marker 37 and counters 5/42"
            );
            println!(
                "{}",
                json!({
                    "stage": "deployment",
                    "contractAddress": target.contract_address(),
                    "height": deployment.height,
                    "finalizedHeight": deployment.finalized_height,
                    "transactionId": deployment.transaction_id,
                    "stateBytes": deployment.contract_state.len(),
                    "stateSha256": hex::encode(sha2::Sha256::digest(&deployment.contract_state)),
                })
            );
            let mut last_state_bytes = deployment.contract_state.clone();
            let mut receipts = Vec::new();
            for enabled in [false, true] {
                let inputs = BTreeMap::from([("enabled".into(), json!(enabled))]);
                let snapshot = funded.node.sync()?;
                let execution = crate::prepare(
                    &plans["guardedClear"],
                    &inputs,
                    &initial_model,
                    &snapshot.state.parameters,
                    address,
                )?;
                let expected = if enabled { &reset_model } else { &initial_model };
                ensure!(
                    crate::check(&execution, &circuits["guardedClear"])?
                        == execution.activity_schedule
                        && execution.after.state.get_ref() == expected.get_ref(),
                    "prepared guarded FlatRecordCellReset state differs for enabled={enabled}"
                );
                let (bound, receipt) = funded
                    .call_with_bound(&guarded_clear, &mut current, &parameters, inputs)
                    .await?;
                bound.check_receipt(&receipt)?;
                let finalized: ContractState<Db> = native_decode(&receipt.contract_state)?;
                ensure!(
                    receipt.chain.genesis == DEVELOPMENT_GENESIS
                        && receipt.contract_address == target.contract_address()
                        && receipt.contract_state == bound.expected_state()
                        && finalized.data == execution.after.state
                        && finalized.data.get_ref() == expected.get_ref(),
                    "finalized guarded FlatRecordCellReset state differs for enabled={enabled}"
                );
                if enabled {
                    ensure!(
                        receipt.contract_state != last_state_bytes,
                        "enabled FlatRecordCellReset did not change the seeded state bytes"
                    );
                    ensure!(
                        finalized.data.get_ref() == reset_model.get_ref(),
                        "enabled FlatRecordCellReset did not store zero typed fields"
                    );
                } else {
                    ensure!(
                        receipt.contract_state == last_state_bytes,
                        "disabled FlatRecordCellReset changed exact state bytes"
                    );
                    ensure!(
                        finalized.data.get_ref() == initial_model.get_ref(),
                        "disabled FlatRecordCellReset changed marker or record counters"
                    );
                }
                println!(
                    "{}",
                    json!({
                        "stage": "guardedClear",
                        "enabled": enabled,
                        "height": receipt.height,
                        "finalizedHeight": receipt.finalized_height,
                        "transactionId": receipt.transaction_id,
                        "stateBytes": receipt.contract_state.len(),
                        "stateSha256": hex::encode(sha2::Sha256::digest(&receipt.contract_state)),
                    })
                );
                last_state_bytes = receipt.contract_state.clone();
                receipts.push(json!({
                    "enabled": enabled,
                    "height": receipt.height,
                    "finalizedHeight": receipt.finalized_height,
                    "transactionId": receipt.transaction_id,
                    "stateBytes": receipt.contract_state.len(),
                    "stateSha256": hex::encode(sha2::Sha256::digest(&receipt.contract_state)),
                }));
            }

            println!(
                "{}",
                json!({
                    "contractAddress": target.contract_address(),
                    "genesis": funded.node.policy.genesis,
                    "operationManifestSha256": pins,
                    "k": degrees,
                    "deploymentStateMatchedMarkerAndCounters": true,
                    "disabledGuardPreservedExactStateBytes": true,
                    "enabledGuardMatchedPreparedTypedZeroDefaults": true,
                    "deployment": {
                        "height": deployment.height,
                        "finalizedHeight": deployment.finalized_height,
                        "transactionId": deployment.transaction_id,
                        "stateBytes": deployment.contract_state.len(),
                        "stateSha256": hex::encode(sha2::Sha256::digest(&deployment.contract_state)),
                    },
                    "guardedReceipts": receipts,
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "submits mixed record Cell resets to the funded development node"]
    fn mixed_record_cell_resets_finalize_typed_defaults() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use futures::executor::block_on;
        use onchain_runtime::state::ContractState;
        use rand::{SeedableRng, rngs::StdRng};
        use serde_json::json;
        use sha2::{Digest, Sha256};
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::proofs::Zkir;

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let endpoint = setting("NOCTIUM_MIXED_RECORD_RESET_NODE")?;
            ensure!(
                endpoint == "http://127.0.0.1:19944",
                "mixed record reset requires the funded loopback node"
            );
            let directory = setting("NOCTIUM_MIXED_RECORD_RESET_BUNDLE")?;
            let pin = setting("NOCTIUM_MIXED_RECORD_RESET_SHA256")?;
            let bundle = artifacts::verify(Path::new(&directory), Some(&pin))?;
            let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
            ensure!(
                plan.entrypoint == "clearMemos",
                "unexpected mixed record reset plan"
            );
            let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
            let k = circuit.k();
            let cache = ProofCache::new(
                setting("NOCTIUM_MIXED_RECORD_RESET_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(&endpoint, &cache).await?;
            let parameters = cache.parameters(k).await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![bundle])?,
                br#"{"state":{}}"#,
                ttl,
                &mut StdRng::from_entropy(),
            )?;
            let operation = target.operation("clearMemos", &parameters, ttl)?;
            let address = ContractAddress(HashOutput(
                hex::decode(target.contract_address())?
                    .try_into()
                    .map_err(|_| anyhow::anyhow!("invalid mixed record reset address"))?,
            ));

            let state_values = |active: bool, amount: &str, fixed_amount: &str, bytes: &[u8]| {
                BTreeMap::from([
                    ("typedMemo".into(), json!({"active":active,"amount":amount})),
                    (
                        "fixedBytesMemo".into(),
                        json!({
                            "active":active,"amount":fixed_amount,
                            "payload":{"kind":"bytes","values":bytes},
                        }),
                    ),
                ])
            };
            let seed = state_values(true, "513", "1027", b"seed");
            let defaults = state_values(false, "0", "0", &[0; 4]);
            let mut expected_state = crate::create_state(&plan, &seed)?;
            let reset_state = crate::create_state(&plan, &defaults)?;
            let constructor = crate::construct_state(&plan, &BTreeMap::new())?;
            ensure!(
                constructor.get_ref() == expected_state.get_ref(),
                "mixed record constructor differs from the oracle"
            );
            let (committed, deployment) = funded.deploy(&target, "clearMemos").await?;
            let receipt_json = |entry: &FinalizedReceipt| {
                json!({
                    "height":entry.height,
                    "blockHash":entry.block_hash,
                    "finalizedHeight":entry.finalized_height,
                    "finalizedHash":entry.finalized_hash,
                    "transactionId":entry.transaction_id,
                    "stateBytes":entry.contract_state.len(),
                    "stateSha256":hex::encode(Sha256::digest(&entry.contract_state)),
                })
            };
            println!(
                "{}",
                json!({
                    "stage":"deployment","contractAddress":target.contract_address(),
                    "receipt":receipt_json(&deployment),
                })
            );
            let deployed: ContractState<Db> = native_decode(&deployment.contract_state)?;
            ensure!(
                deployment.chain.genesis == DEVELOPMENT_GENESIS
                    && deployment.contract_address == target.contract_address()
                    && deployed.data.get_ref() == expected_state.get_ref(),
                "finalized constructor state differs"
            );
            let mut current = Some(committed);
            let mut calls = Vec::new();
            for enabled in [false, true] {
                let inputs = BTreeMap::from([("enabled".into(), json!(enabled))]);
                let snapshot = funded.node.sync()?;
                let execution = crate::prepare(
                    &plan,
                    &inputs,
                    &expected_state,
                    &snapshot.state.parameters,
                    address,
                )?;
                let expected = if enabled { &defaults } else { &seed };
                let returns = BTreeMap::from([
                    (
                        "typedActiveAfterReset".into(),
                        expected["typedMemo"]["active"].clone(),
                    ),
                    (
                        "typedAmountAfterReset".into(),
                        expected["typedMemo"]["amount"].clone(),
                    ),
                    (
                        "fixedBytesActiveAfterReset".into(),
                        expected["fixedBytesMemo"]["active"].clone(),
                    ),
                    (
                        "fixedBytesPayloadAfterReset".into(),
                        expected["fixedBytesMemo"]["payload"].clone(),
                    ),
                    (
                        "fixedBytesAmountAfterReset".into(),
                        expected["fixedBytesMemo"]["amount"].clone(),
                    ),
                ]);
                let post_state = if enabled {
                    &reset_state
                } else {
                    &expected_state
                };
                ensure!(
                    crate::check(&execution, &circuit)? == execution.activity_schedule
                        && execution.returns_json() == returns
                        && execution.after.state.get_ref() == post_state.get_ref(),
                    "native state or typed returns differ for enabled={enabled}"
                );
                let (bound, receipt) = funded
                    .call_with_bound(&operation, &mut current, &parameters, inputs)
                    .await?;
                let call = json!({
                    "enabled":enabled,"receipt":receipt_json(&receipt),"typedReturns":returns,
                });
                println!("{}", json!({"stage":"clearMemos","call":call}));
                bound.check_receipt(&receipt)?;
                let finalized: ContractState<Db> = native_decode(&receipt.contract_state)?;
                ensure!(
                    receipt.chain.genesis == DEVELOPMENT_GENESIS
                        && receipt.contract_address == target.contract_address()
                        && finalized.data == execution.after.state
                        && (receipt.contract_state == deployment.contract_state) != enabled,
                    "finalized state differs for enabled={enabled}"
                );
                expected_state = execution.after.state;
                calls.push(call);
            }
            println!(
                "{}",
                json!({
                    "contractAddress":target.contract_address(),"genesis":DEVELOPMENT_GENESIS,
                    "bundleManifestSha256":pin,"k":k,"deployment":receipt_json(&deployment),
                    "guardedCalls":calls,
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires pinned ListIsEmptyParity bundles and the funded development node"]
    fn list_is_empty_finalizes_zero_width_and_nested_record_reads() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            proof::WitnessContractTarget,
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use futures::executor::block_on;
        use onchain_runtime::state::ContractState;
        use rand::{SeedableRng, rngs::StdRng};
        use serde_json::json;
        use sha2::Sha256;
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::proofs::Zkir;

        block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let endpoint = setting("NOCTIUM_LIST_EMPTY_NODE")?;
            ensure!(
                endpoint == "http://127.0.0.1:19944",
                "List.isEmpty qualification requires the funded loopback node"
            );
            let directory = setting("NOCTIUM_LIST_EMPTY_BUNDLES")?;
            let pins: BTreeMap<String, String> =
                serde_json::from_str(&setting("NOCTIUM_LIST_EMPTY_SHA256")?)?;
            ensure!(
                pins.len() == 2 && pins.contains_key("seed") && pins.contains_key("inspect"),
                "expected exactly the seed and inspect bundle pins"
            );
            let mut bundles = Vec::new();
            let mut plans = BTreeMap::new();
            let mut circuits = BTreeMap::new();
            for name in ["seed", "inspect"] {
                let bundle =
                    artifacts::verify(&Path::new(&directory).join(name), Some(&pins[name]))?;
                let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
                ensure!(plan.entrypoint == name, "unexpected List.isEmpty plan");
                circuits.insert(name, IrSource::load(bundle.file(Role::Circuit)?)?);
                plans.insert(name, plan);
                bundles.push(bundle);
            }
            let degrees = BTreeMap::from([
                ("seed", circuits["seed"].k()),
                ("inspect", circuits["inspect"].k()),
            ]);
            let cache = ProofCache::new(
                setting("NOCTIUM_LIST_EMPTY_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded = FundedLedgerTest::connect(&endpoint, &cache).await?;
            let seed_parameters = cache.parameters(degrees["seed"]).await?;
            let inspect_parameters = cache.parameters(degrees["inspect"]).await?;
            let snapshot = funded.node.sync()?;
            let ttl = snapshot.block.tblock.to_secs() + 1800;
            let state_values = BTreeMap::from([
                ("emptyBytes".into(), json!([])),
                ("oneEmptyByte".into(), json!([])),
                ("memos".into(), json!([])),
            ]);
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(bundles)?,
                &serde_json::to_vec(&json!({"state":&state_values}))?,
                ttl,
                &mut StdRng::from_entropy(),
            )?;
            let address = ContractAddress(HashOutput(
                hex::decode(target.contract_address())?
                    .try_into()
                    .map_err(|_| anyhow::anyhow!("invalid List.isEmpty address"))?,
            ));
            let seed_operation = target.operation("seed", &seed_parameters, ttl)?;
            let inspect_operation = target.operation("inspect", &inspect_parameters, ttl)?;
            let bytes = |byte: u8| json!({"kind":"bytes","values":vec![byte;32]});
            let seed_inputs = BTreeMap::from([
                ("owner".into(), bytes(1)),
                ("emptySpender".into(), bytes(2)),
                ("populatedSpender".into(), bytes(3)),
            ]);
            let inspect_inputs = |probe_missing| {
                let mut inputs = seed_inputs.clone();
                inputs.extend([
                    ("missingOwner".into(), bytes(4)),
                    ("missingSpender".into(), bytes(5)),
                    ("probeMissing".into(), json!(probe_missing)),
                ]);
                inputs
            };
            let initial = crate::create_state(&plans["seed"], &state_values)?;
            let seeded = crate::prepare(
                &plans["seed"],
                &seed_inputs,
                &initial,
                &snapshot.state.parameters,
                address,
            )?;
            crate::check(&seeded, &circuits["seed"])?;
            let inspected = crate::prepare(
                &plans["inspect"],
                &inspect_inputs(false),
                &seeded.after.state,
                &snapshot.state.parameters,
                address,
            )?;
            let expected_returns = BTreeMap::from([
                ("emptyBytesResult".into(), json!(true)),
                ("oneEmptyByteResult".into(), json!(false)),
                ("emptyRecordListResult".into(), json!(true)),
                ("populatedRecordListResult".into(), json!(false)),
                ("missingRecordListResult".into(), json!(false)),
            ]);
            ensure!(
                crate::check(&inspected, &circuits["inspect"])? == inspected.activity_schedule
                    && inspected.returns_json() == expected_returns
                    && inspected.after.state == seeded.after.state,
                "List.isEmpty preparation differs from the Compact oracle"
            );
            ensure!(
                crate::prepare(
                    &plans["inspect"],
                    &inspect_inputs(true),
                    &seeded.after.state,
                    &snapshot.state.parameters,
                    address,
                )
                .is_err(),
                "active absent List path must reject before submission"
            );

            let receipt_json = |receipt: &FinalizedReceipt| {
                json!({
                    "height":receipt.height, "blockHash":receipt.block_hash,
                    "finalizedHeight":receipt.finalized_height,
                    "finalizedHash":receipt.finalized_hash,
                    "transactionId":receipt.transaction_id,
                    "stateBytes":receipt.contract_state.len(),
                    "stateSha256":hex::encode(Sha256::digest(&receipt.contract_state)),
                })
            };
            let (deployed, deployment) = funded.deploy(&target, "seed").await?;
            println!(
                "{}",
                json!({"stage":"deployment","receipt":receipt_json(&deployment)})
            );
            let initial_state: ContractState<Db> = native_decode(&deployment.contract_state)?;
            ensure!(
                initial_state.data == initial,
                "List deployment did not start empty"
            );
            let mut current = Some(deployed);
            let (seed_binding, seed_receipt) = funded
                .call_with_bound(
                    &seed_operation,
                    &mut current,
                    &seed_parameters,
                    seed_inputs.clone(),
                )
                .await?;
            println!(
                "{}",
                json!({"stage":"seed","receipt":receipt_json(&seed_receipt)})
            );
            seed_binding.check_receipt(&seed_receipt)?;
            let seeded_state: ContractState<Db> = native_decode(&seed_receipt.contract_state)?;
            ensure!(
                seeded_state.data == seeded.after.state,
                "finalized List seed differs"
            );
            let (inspect_binding, inspect_receipt) = funded
                .call_with_bound(
                    &inspect_operation,
                    &mut current,
                    &inspect_parameters,
                    inspect_inputs(false),
                )
                .await?;
            println!(
                "{}",
                json!({"stage":"inspect","receipt":receipt_json(&inspect_receipt)})
            );
            inspect_binding.check_receipt(&inspect_receipt)?;
            ensure!(
                inspect_receipt.contract_state == seed_receipt.contract_state,
                "finalized List.isEmpty read changed seeded state bytes"
            );
            println!(
                "{}",
                json!({
                    "contractAddress":target.contract_address(),"genesis":DEVELOPMENT_GENESIS,
                    "bundleManifestSha256":pins,"k":degrees,
                    "deployment":receipt_json(&deployment),"seed":receipt_json(&seed_receipt),
                    "inspect":receipt_json(&inspect_receipt),"returns":expected_returns,
                    "activeAbsentPathRejectedBeforeSubmission":true,
                })
            );
            Ok(())
        })
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires authenticated OpaqueCells bundles and a funded development node"]
    fn opaque_root_cells_finalize_typed_store_and_reads() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            assembly::NativeIntent,
            proof::{LocalProver, WitnessContractTarget},
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value, ValueAtom};
        use ledger::structure::{ContractAction, ProofPreimageVersioned};
        use onchain_runtime::state::ContractState;
        use rand::{SeedableRng, rngs::StdRng};
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::{fab::AlignedValueExt, proofs::Zkir};

        futures::executor::block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let root = setting("NOCTIUM_OPAQUE_CELLS_FUNDED_BUNDLES")?;
            let directory = Path::new(&root);
            let pins: BTreeMap<String, String> =
                serde_json::from_str(&setting("NOCTIUM_OPAQUE_CELLS_FUNDED_MANIFESTS")?)?;
            let mut bundles = Vec::new();
            let mut plans = BTreeMap::new();
            let mut degrees = BTreeMap::new();
            for entry in ["store", "readText", "readBytes"] {
                let pin = pins.get(entry).context("missing entrypoint manifest pin")?;
                let bundle =
                    artifacts::verify(&directory.join(format!("{entry}-bundle")), Some(pin))?;
                let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
                ensure!(
                    plan.entrypoint == entry,
                    "unexpected opaque Cell bundle plan"
                );
                degrees.insert(entry, IrSource::load(bundle.file(Role::Circuit)?)?.k());
                plans.insert(entry, plan);
                bundles.push(bundle);
            }

            let cache = ProofCache::new(
                setting("NOCTIUM_OPAQUE_CELLS_FUNDED_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded =
                FundedLedgerTest::connect(&setting("NOCTIUM_OPAQUE_CELLS_FUNDED_NODE")?, &cache)
                    .await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let text = "é\0λ";
            let bytes = [0u8, 1, 255];
            let payloads = BTreeMap::from([
                ("text".into(), json!({"kind":"opaqueString", "value":text})),
                (
                    "bytes".into(),
                    json!({"kind":"opaqueBytes", "values":bytes}),
                ),
            ]);
            let defaults = BTreeMap::from([
                ("text".into(), json!({"kind":"opaqueString", "value":""})),
                ("bytes".into(), json!({"kind":"opaqueBytes", "values":[]})),
            ]);
            let mut rng = StdRng::from_entropy();
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(bundles)?,
                &serde_json::to_vec(&json!({"state": &defaults}))?,
                ttl,
                &mut rng,
            )?;
            let (state, deployment) = funded.deploy(&target, "store").await?;
            let deployed: ContractState<Db> = native_decode(&deployment.contract_state)?;
            ensure!(
                deployed.data.get_ref()
                    == crate::create_state(&plans["store"], &defaults)?.get_ref(),
                "deployed opaque Cells differ from canonical empty values"
            );

            let store_parameters = cache.parameters(degrees["store"]).await?;
            let store = target.operation("store", &store_parameters, ttl)?;
            let mut current = Some(state);
            let stored = funded
                .call(
                    &store,
                    &mut current,
                    &store_parameters,
                    BTreeMap::from([
                        ("nextText".into(), payloads["text"].clone()),
                        ("nextBytes".into(), payloads["bytes"].clone()),
                    ]),
                )
                .await?;
            let stored_state: ContractState<Db> = native_decode(&stored.contract_state)?;
            ensure!(
                stored_state.data.get_ref()
                    == crate::create_state(&plans["store"], &payloads)?.get_ref(),
                "finalized opaque Cells differ from exact stored values"
            );

            let mut read_receipts = BTreeMap::new();
            for (entry, name, slot, raw) in [
                ("readText", "textValue", "text", text.as_bytes()),
                ("readBytes", "bytesValue", "bytes", bytes.as_slice()),
            ] {
                let parameters = cache.parameters(degrees[entry]).await?;
                let operation = target.operation(entry, &parameters, ttl)?;
                let prepared =
                    operation.prepare_call(&mut current, &parameters, BTreeMap::new(), &mut rng)?;
                let native: NativeIntent = native_decode(&prepared.private_intent_bytes()?)?;
                let Some(ContractAction::Call(call)) = native.actions.get(0) else {
                    anyhow::bail!("missing opaque read call");
                };
                let ProofPreimageVersioned::V2(preimage) = &call.proof else {
                    anyhow::bail!("unexpected opaque read proof version");
                };
                let aligned = AlignedValue::new(
                    Value(vec![ValueAtom::from(raw)]),
                    Alignment::singleton(AlignmentAtom::Compress),
                )
                .context("expected canonical Compress atom")?;
                let mut projection = Vec::new();
                aligned.value_only_field_repr(&mut projection);
                ensure!(
                    projection.len() == 1 && preimage.public_transcript_outputs == projection,
                    "{entry} proof did not bind exactly the expected Compress field ({} output fields)",
                    preimage.public_transcript_outputs.len()
                );
                let live = funded.node.sync()?;
                let execution = crate::prepare(
                    &plans[entry],
                    &BTreeMap::new(),
                    &stored_state.data,
                    &live.state.parameters,
                    call.address,
                )?;
                ensure!(
                    execution.returns_json().get(name) == Some(&payloads[slot]),
                    "opaque read return differs from the typed payload"
                );
                let proved = prepared
                    .prove(
                        &LocalProver::new(StdRng::from_entropy()),
                        &parameters,
                        1_048_576,
                        futures::future::pending(),
                    )
                    .await?;
                let (bound, receipt) = funded.finalize(proved.native()).await?;
                ensure!(
                    receipt.contract_state == stored.contract_state,
                    "opaque read changed finalized state"
                );
                current = Some(
                    proved
                        .contract_binding()
                        .context("missing opaque read binding")?
                        .admit_committed_state(
                            &receipt.contract_state,
                            bound.expected_state(),
                            &receipt.finalized_hash,
                            false,
                        )?,
                );
                read_receipts.insert(
                    entry,
                    json!({
                        "height": receipt.height, "finalizedHash": receipt.finalized_hash,
                        "transactionId": receipt.transaction_id, "returned": payloads[slot],
                    }),
                );
            }
            println!(
                "{}",
                json!({
                    "contractAddress": target.contract_address(),
                    "deployment": {
                        "height": deployment.height, "finalizedHash": deployment.finalized_hash,
                        "transactionId": deployment.transaction_id,
                    },
                    "store": {
                        "height": stored.height, "finalizedHash": stored.finalized_hash,
                        "transactionId": stored.transaction_id,
                    },
                    "reads": read_receipts,
                    "readStateBytesUnchanged": true,
                    "bundleManifestSha256": pins,
                    "k": degrees,
                })
            );
            Ok(())
        })
    }


    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires authenticated OpaqueCellReset bundles and a funded development node"]
    fn guarded_opaque_cell_resets_finalize_on_development_ledger() -> anyhow::Result<()> {
        use crate::{
            artifacts::{self, ContractBundleSet, Role},
            assembly::NativeIntent,
            proof::{LocalProver, WitnessContractTarget},
            zkir::IrSource,
        };
        use anyhow::{Context, ensure};
        use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value, ValueAtom};
        use ledger::structure::{ContractAction, ProofPreimageVersioned};
        use onchain_runtime::state::ContractState;
        use rand::{SeedableRng, rngs::StdRng};
        use std::{collections::BTreeMap, env, path::Path};
        use transient_crypto::{curve::Fr, fab::AlignedValueExt, proofs::Zkir};

        futures::executor::block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let root = setting("NOCTIUM_OPAQUE_RESET_FUNDED_BUNDLES")?;
            let pins: BTreeMap<String, String> =
                serde_json::from_str(&setting("NOCTIUM_OPAQUE_RESET_FUNDED_MANIFESTS")?)?;
            let mut bundles = Vec::new();
            let mut degrees = BTreeMap::new();
            for entry in ["seed", "clear"] {
                let pin = pins
                    .get(entry)
                    .context("missing opaque reset manifest pin")?;
                let directory = Path::new(&root).join(format!("{entry}-bundle"));
                let bundle = artifacts::verify(&directory, Some(pin))?;
                let plan: crate::Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
                ensure!(
                    plan.entrypoint == entry,
                    "unexpected opaque reset bundle plan"
                );
                degrees.insert(entry, IrSource::load(bundle.file(Role::Circuit)?)?.k());
                bundles.push(bundle);
            }
            let seed_plan: crate::Plan = serde_json::from_slice(bundles[0].file(Role::Plan)?)?;
            let cache = ProofCache::new(
                setting("NOCTIUM_OPAQUE_RESET_FUNDED_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let funded =
                FundedLedgerTest::connect(&setting("NOCTIUM_OPAQUE_RESET_FUNDED_NODE")?, &cache)
                    .await?;
            let ttl = funded.node.sync()?.block.tblock.to_secs() + 1800;
            let mut rng = StdRng::from_entropy();
            let empty_values = BTreeMap::from([
                ("text".into(), json!({"kind":"opaqueString","value":""})),
                ("bytes".into(), json!({"kind":"opaqueBytes","values":[]})),
            ]);
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(bundles)?,
                &serde_json::to_vec(&json!({"state": &empty_values}))?,
                ttl,
                &mut rng,
            )?;
            let (state, deployment) = funded.deploy(&target, "seed").await?;
            let deployed: ContractState<Db> = native_decode(&deployment.contract_state)?;
            ensure!(
                deployed.data.get_ref()
                    == crate::create_state(&seed_plan, &empty_values)?.get_ref(),
                "deployment did not store canonical empty opaque Cells"
            );

            let text = "é\0λ";
            let bytes = [0u8, 1, 255];
            let text_value = json!({"kind":"opaqueString","value":text});
            let bytes_value = json!({"kind":"opaqueBytes","values":bytes});
            let seed_parameters = cache.parameters(degrees["seed"]).await?;
            let seed = target.operation("seed", &seed_parameters, ttl)?;
            let mut current = Some(state);
            let stored = funded
                .call(
                    &seed,
                    &mut current,
                    &seed_parameters,
                    BTreeMap::from([
                        ("nextText".into(), text_value.clone()),
                        ("nextBytes".into(), bytes_value.clone()),
                    ]),
                )
                .await?;
            let stored_state: ContractState<Db> = native_decode(&stored.contract_state)?;
            let expected_storage = crate::create_state(
                &seed_plan,
                &BTreeMap::from([("text".into(), text_value), ("bytes".into(), bytes_value)]),
            )?;
            ensure!(
                stored_state.data.get_ref() == expected_storage.get_ref(),
                "seed mismatch"
            );

            let receipt_details = |receipt: &FinalizedReceipt| {
                json!({
                    "height": receipt.height, "finalizedHash": receipt.finalized_hash,
                    "transactionId": receipt.transaction_id,
                })
            };
            let clear_parameters = cache.parameters(degrees["clear"]).await?;
            let clear = target.operation("clear", &clear_parameters, ttl)?;
            let mut resets = BTreeMap::new();
            for (name, enabled, expected, raw) in [
                (
                    "inactive",
                    false,
                    &stored,
                    [text.as_bytes(), bytes.as_slice()],
                ),
                (
                    "active",
                    true,
                    &deployment,
                    [b"".as_slice(), b"".as_slice()],
                ),
            ] {
                let prepared = clear.prepare_call(
                    &mut current,
                    &clear_parameters,
                    BTreeMap::from([("enabled".into(), json!(enabled))]),
                    &mut rng,
                )?;
                let native: NativeIntent = native_decode(&prepared.private_intent_bytes()?)?;
                let Some(ContractAction::Call(call)) = native.actions.get(0) else {
                    anyhow::bail!("missing opaque reset call");
                };
                let ProofPreimageVersioned::V2(preimage) = &call.proof else {
                    anyhow::bail!("unexpected opaque reset proof version");
                };
                let mut projection = vec![Fr::from(u64::from(enabled))];
                for value in raw {
                    AlignedValue::new(
                        Value(vec![ValueAtom::from(value)]),
                        Alignment::singleton(AlignmentAtom::Compress),
                    )
                    .context("expected canonical Compress atom")?
                    .value_only_field_repr(&mut projection);
                }
                ensure!(
                    preimage.public_transcript_outputs == projection,
                    "{name} reset proof did not bind both expected opaque returns"
                );
                let proved = prepared
                    .prove(
                        &LocalProver::new(StdRng::from_entropy()),
                        &clear_parameters,
                        1_048_576,
                        futures::future::pending(),
                    )
                    .await?;
                let (bound, receipt) = funded.finalize(proved.native()).await?;
                ensure!(
                    receipt.contract_state == expected.contract_state,
                    "{name} reset state changed unexpectedly"
                );
                current = Some(
                    proved
                        .contract_binding()
                        .context("missing opaque reset binding")?
                        .admit_committed_state(
                            &receipt.contract_state,
                            bound.expected_state(),
                            &receipt.finalized_hash,
                            false,
                        )?,
                );
                resets.insert(name, receipt_details(&receipt));
            }
            println!(
                "{}",
                json!({
                    "contractAddress": target.contract_address(),
                    "bundleManifestSha256": pins,
                    "k": degrees,
                    "deployment": receipt_details(&deployment),
                    "seed": receipt_details(&stored),
                    "resets": resets,
                    "inactivePreservedExactSeededState": true,
                    "activeRestoredExactEmptyState": true,
                    "bothReturnsBoundPerGuard": true,
                })
            );
            Ok(())
        })
    }
}
