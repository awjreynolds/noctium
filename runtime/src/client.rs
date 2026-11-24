//! Host-authorized native transaction submission and private-journal recovery.
//! Node finality reports and durable storage are explicit host trust boundaries.
use crate::{
    Db,
    funding::{CONTRACT_SEGMENT, SealedTransaction, UnsealedTransaction, admissible_actions},
    host,
    lifecycle::{Event, Lifecycle, Phase},
    proof::ProvedNativeIntent,
};
#[cfg(feature = "localnet")]
use base_crypto::hash::HashOutput;
#[cfg(feature = "localnet")]
use coin_structure::{
    coin::{Info, PublicKey},
    transfer::{Recipient, SenderEvidence},
};
use ledger::{
    semantics::{TransactionContext, TransactionResult},
    structure::{
        ContractAction, Intent, LedgerState, PedersenDowngradeable, ProofMarker, Signature,
        Transaction, UnshieldedOffer,
    },
    verify::WellFormedStrictness,
};
#[cfg(feature = "localnet")]
use onchain_runtime::context::Effects;
use onchain_runtime::{context::BlockContext, ops::Op};
use serde::{Deserialize, Serialize};
use serialize::{Serializable, Tagged, tagged_deserialize, tagged_serialize};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use transient_crypto::commitment::Pedersen;
use zeroize::{Zeroize, Zeroizing};

const MAX_TRANSACTION: usize = 4 * 1024 * 1024;
const MAX_STATE: usize = 1024 * 1024;
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    Policy,
    Network,
    Parameters,
    Funding,
    Approval,
    AlteredTransaction,
    InvalidTransaction,
    Identity,
    Receipt,
    StaleReceipt,
    Persistence,
    State,
    Rejected,
    Uncertain,
    Deadline,
    Cancelled,
    CancellationAfterBroadcast,
    StorageConflict,
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "noctium_client_{self:?}")
    }
}
impl std::error::Error for Error {}
type Result<T> = std::result::Result<T, Error>;
fn require(valid: bool, error: Error) -> Result<()> {
    if valid { Ok(()) } else { Err(error) }
}
fn hash(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}
fn canonical_hash(text: &str) -> bool {
    text.len() == 64
        && text
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}
fn encode<T: Serializable + Tagged>(value: &T) -> Result<Vec<u8>> {
    let mut out = Vec::new();
    tagged_serialize(value, &mut out).map_err(|_| Error::InvalidTransaction)?;
    Ok(out)
}
fn body<T: Serializable>(value: &T) -> Result<Vec<u8>> {
    let mut out = Vec::new();
    Serializable::serialize(value, &mut out).map_err(|_| Error::InvalidTransaction)?;
    Ok(out)
}
fn journal_valid(journal: &serde_json::Value, identity: &JournalIdentity) -> Result<()> {
    let mut value = journal.clone();
    let object = value.as_object_mut().ok_or(Error::Identity)?;
    require(
        object.len() == 9
            && object
                .remove("journalDigest")
                .and_then(|v| v.as_str().map(str::to_owned))
                .as_deref()
                == Some(identity.journal_digest.as_str()),
        Error::Identity,
    )?;
    let bytes = Zeroizing::new(serde_json::to_vec(&value).map_err(|_| Error::Identity)?);
    let mut digest = Sha256::new();
    digest.update(b"noctium.private-state-journal.v1\0");
    digest.update(&*bytes);
    require(
        hex::encode(digest.finalize()) == identity.journal_digest,
        Error::Identity,
    )
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct NetworkPolicy {
    pub network_id: String,
    pub genesis: String,
    pub spec_version: u32,
    pub transaction_version: u32,
    pub profile: String,
    pub max_dust: u128,
}
impl NetworkPolicy {
    pub fn validate(&self) -> Result<()> {
        require(
            !self.network_id.is_empty()
                && self.network_id.len() <= 128
                && canonical_hash(&self.genesis)
                && self.profile == crate::profile::NAME
                && self.max_dust > 0
                && self.spec_version > 0
                && self.transaction_version > 0,
            Error::Policy,
        )
    }
    pub fn check(&self, observed: &ChainIdentity) -> Result<()> {
        self.validate()?;
        require(
            observed.network_id == self.network_id
                && observed.genesis == self.genesis
                && observed.spec_version == self.spec_version
                && observed.transaction_version == self.transaction_version
                && observed.profile == self.profile,
            Error::Network,
        )
    }
}
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ChainIdentity {
    pub network_id: String,
    pub genesis: String,
    pub spec_version: u32,
    pub transaction_version: u32,
    pub profile: String,
}
pub struct Snapshot {
    pub chain: ChainIdentity,
    pub finalized_hash: String,
    pub height: u64,
    pub state: LedgerState<Db>,
    pub block: BlockContext,
}
impl Snapshot {
    pub fn validate(&self, policy: &NetworkPolicy) -> Result<()> {
        policy.check(&self.chain)?;
        require(
            canonical_hash(&self.finalized_hash) && self.state.network_id == policy.network_id,
            Error::Network,
        )
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum ContractEvent {
    Deploy,
    Call,
    /// A maintenance action. Ledger semantics report TxApplied without a contract event.
    Maintain,
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct FinalizedReceipt {
    pub chain: ChainIdentity,
    pub block_hash: String,
    pub height: u64,
    pub finalized_hash: String,
    pub finalized_height: u64,
    pub extrinsic_hash: String,
    pub extrinsic_index: u32,
    pub transaction_id: String,
    pub intent_id: String,
    pub contract_address: String,
    pub event: ContractEvent,
    pub contract_state: Vec<u8>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    /// Canonical states at the inclusion block, keyed by other called addresses.
    pub secondary_states: BTreeMap<String, Vec<u8>>,
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct PartialReceipt {
    pub receipt: FinalizedReceipt,
    pub segments: BTreeMap<u16, bool>,
    pub entrypoint: Vec<u8>,
}
pub enum ObservedReceipt {
    Full(FinalizedReceipt),
    Partial(PartialReceipt),
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Submission {
    Broadcast,
    Rejected,
    Uncertain,
}
pub enum Observation {
    Pending,
    Rejected,
    Finalized(FinalizedReceipt),
    Partial(PartialReceipt),
}
#[derive(Clone, Copy, Debug)]
pub struct HostFailure;
/// The adapter verifies canonical finalized ancestry, exact extrinsic payload and event shape.
/// Maintenance has no contract-specific event, so its finalized state supplies the second check.
/// For partial success, the adapter also verifies the segment outcomes against finalized execution.
/// Credentials, endpoints, transport limits and deadlines stay in the host adapter.
#[allow(async_fn_in_trait)]
pub trait ChainAdapter {
    async fn snapshot(&self) -> std::result::Result<Snapshot, HostFailure>;
    async fn submit(
        &self,
        transaction: &BoundTransaction,
    ) -> std::result::Result<Submission, HostFailure>;
    async fn observe(
        &self,
        transaction: &BoundTransaction,
    ) -> std::result::Result<Observation, HostFailure>;
}
#[allow(async_fn_in_trait)]
pub trait FundingAdapter {
    async fn fund(
        &self,
        contract: &ProvedNativeIntent,
        snapshot: &Snapshot,
        policy: &NetworkPolicy,
    ) -> std::result::Result<UnsealedTransaction, HostFailure>;

    /// Fund a pre-checked unshielded caller intent without changing its selected spends.
    async fn fund_unshielded_caller(
        &self,
        _contract: &ProvedNativeIntent,
        _snapshot: &Snapshot,
        _policy: &NetworkPolicy,
    ) -> std::result::Result<UnsealedTransaction, HostFailure> {
        Err(HostFailure)
    }
}
#[allow(async_fn_in_trait)]
pub trait SigningAdapter {
    async fn approve_and_sign(
        &self,
        transaction: &UnsealedTransaction,
        snapshot: &Snapshot,
        policy: &NetworkPolicy,
    ) -> std::result::Result<SealedTransaction, HostFailure>;
}

fn public_intent<B: storage::Storable<Db> + PedersenDowngradeable<Db>>(
    intent: &Intent<Signature, ProofMarker, B, Db>,
) -> Intent<Signature, ProofMarker, Pedersen, Db> {
    Intent {
        guaranteed_unshielded_offer: intent.guaranteed_unshielded_offer.clone(),
        fallible_unshielded_offer: intent.fallible_unshielded_offer.clone(),
        actions: intent.actions.clone(),
        dust_actions: intent.dust_actions.clone(),
        ttl: intent.ttl,
        binding_commitment: intent.binding_commitment.downgrade(),
    }
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct CheckpointPrefix {
    entrypoint: Vec<u8>,
    segments: BTreeMap<u16, bool>,
    state: Vec<u8>,
}

fn checkpoint_call(
    transaction: &SealedTransaction,
) -> Option<(String, Vec<u8>, BTreeMap<u16, bool>)> {
    let Transaction::Standard(signed) = transaction else {
        return None;
    };
    let contract = signed.intents.get(&CONTRACT_SEGMENT)?;
    if contract.actions.len() != 1 {
        return None;
    }
    let ContractAction::Call(call) = contract.actions.iter_deref().next()? else {
        return None;
    };
    if call.guaranteed_transcript.as_ref()?.program.is_empty()
        || !matches!(
            call.fallible_transcript
                .as_ref()?
                .program
                .iter_deref()
                .next(),
            Some(Op::Ckpt)
        )
    {
        return None;
    }
    let segments = signed
        .segments()
        .into_iter()
        .map(|segment| (segment, segment != CONTRACT_SEGMENT))
        .collect();
    Some((
        hex::encode(call.address.0.0),
        call.entry_point.0.clone(),
        segments,
    ))
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct BoundData {
    policy: NetworkPolicy,
    transaction: Vec<u8>,
    transaction_id: String,
    intent_id: String,
    contract_address: String,
    event: ContractEvent,
    expected_state: Vec<u8>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    checkpoint: Option<CheckpointPrefix>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    call_counts: BTreeMap<String, usize>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    secondary_states: BTreeMap<String, Vec<u8>>,
    after_height: u64,
}
/// Exact signed native bytes and expected execution state. No mutation or private key access.
#[derive(Clone)]
pub struct BoundTransaction {
    data: BoundData,
}

#[cfg(feature = "localnet")]
fn no_unshielded_effects(effects: &Effects<Db>) -> bool {
    effects.unshielded_mints.size() == 0
        && effects.unshielded_inputs.size() == 0
        && effects.unshielded_outputs.size() == 0
        && effects.claimed_unshielded_spends.size() == 0
}

/// Accept only the pinned two-call relay shape and its exact transient/output commitments.
#[cfg(feature = "localnet")]
pub(crate) fn shielded_relay_shape_valid(
    contract: &ProvedNativeIntent,
    offer: &zswap::Offer<transient_crypto::proofs::Proof, Db>,
    relay_mint: &Info,
    mint_domain: HashOutput,
) -> bool {
    const RELAY_AMOUNT: u128 = 5;
    const NONCE_EVOLUTION_DOMAIN: &[u8] = b"midnight:kernel:nonce_evolve";

    if contract.actions.len() != 2
        || offer.inputs.len() != 0
        || offer.outputs.len() != 1
        || offer.transient.len() != 1
        || offer.deltas.len() != 1
        || relay_mint.value != RELAY_AMOUNT
    {
        return false;
    }

    let mut actions = contract.actions.iter_deref();
    let Some(ContractAction::Call(relay)) = actions.next() else {
        return false;
    };
    let Some(ContractAction::Call(destination)) = actions.next() else {
        return false;
    };
    if actions.next().is_some() || relay.address == destination.address {
        return false;
    }

    let Some(relay_transcript) = relay.guaranteed_transcript.as_deref() else {
        return false;
    };
    let Some(destination_transcript) = destination.guaranteed_transcript.as_deref() else {
        return false;
    };
    if relay.fallible_transcript.is_some() || destination.fallible_transcript.is_some() {
        return false;
    }

    let Some(transient) = offer.transient.iter_deref().next() else {
        return false;
    };
    let Some(output) = offer.outputs.iter_deref().next() else {
        return false;
    };
    let Some(delta) = offer.deltas.iter_deref().next() else {
        return false;
    };

    let relay_type = relay.address.custom_shielded_token_type(mint_domain);
    if relay_mint.type_ != relay_type {
        return false;
    }
    let destination_coin = relay_mint.evolve_from(NONCE_EVOLUTION_DOMAIN, RELAY_AMOUNT, relay_type);
    let transient_commitment = relay_mint.commitment(&Recipient::Contract(relay.address));
    let transient_nullifier = relay_mint.nullifier(&SenderEvidence::Contract(relay.address));
    let output_commitment = destination_coin.commitment(&Recipient::Contract(destination.address));

    let relay_effects = &relay_transcript.effects;
    let destination_effects = &destination_transcript.effects;
    relay_effects.claimed_shielded_receives.size() == 1
        && relay_effects
            .claimed_shielded_receives
            .iter()
            .any(|commitment| **commitment == transient_commitment)
        && relay_effects.claimed_nullifiers.size() == 1
        && relay_effects
            .claimed_nullifiers
            .iter()
            .any(|nullifier| **nullifier == transient_nullifier)
        && relay_effects.claimed_shielded_spends.size() == 1
        && relay_effects
            .claimed_shielded_spends
            .iter()
            .any(|commitment| **commitment == output_commitment)
        && relay_effects.claimed_contract_calls.size() == 1
        && relay_effects.claimed_contract_calls.iter().any(|claim| {
            let (sequence, address, entry_point, commitment) = (**claim).into_inner();
            sequence == 0
                && address == destination.address
                && entry_point == destination.entry_point.ep_hash()
                && commitment == destination.communication_commitment
        })
        && relay_effects.shielded_mints.size() == 1
        && relay_effects
            .shielded_mints
            .get(&mint_domain)
            .is_some_and(|amount| *amount == RELAY_AMOUNT as u64)
        && no_unshielded_effects(relay_effects)
        && destination_effects.claimed_shielded_receives.size() == 1
        && destination_effects
            .claimed_shielded_receives
            .iter()
            .any(|commitment| **commitment == output_commitment)
        && destination_effects.claimed_nullifiers.size() == 0
        && destination_effects.claimed_shielded_spends.size() == 0
        && destination_effects.claimed_contract_calls.size() == 0
        && destination_effects.shielded_mints.size() == 0
        && no_unshielded_effects(destination_effects)
        && transient.coin_com == transient_commitment
        && transient.nullifier == transient_nullifier
        && transient.contract_address.as_deref() == Some(&relay.address)
        && transient.ciphertext.is_none()
        && output.coin_com == output_commitment
        && output.contract_address.as_deref() == Some(&destination.address)
        && output.ciphertext.is_none()
        && delta.token_type == relay_type
        && delta.value == -(RELAY_AMOUNT as i128)
}

/// Bind one same-call mint split to the exact transient and outputs booked by the host.
#[cfg(feature = "localnet")]
pub(crate) fn shielded_immediate_change_shape_valid(
    contract: &ProvedNativeIntent,
    offer: &zswap::Offer<transient_crypto::proofs::Proof, Db>,
    mint: &Info,
    mint_domain: HashOutput,
    recipient: PublicKey,
) -> bool {
    const MINT_AMOUNT: u128 = 5;
    const USER_AMOUNT: u128 = 2;
    const NONCE_EVOLUTION_DOMAIN: &[u8] = b"midnight:kernel:nonce_evolve";
    const CHANGE_NONCE_EVOLUTION_DOMAIN: &[u8] = b"midnight:kernel:nonce_evolve/2";

    let Some(ContractAction::Call(call)) = contract.actions.get(0) else {
        return false;
    };
    let Some(transcript) = call.guaranteed_transcript.as_deref() else {
        return false;
    };
    if contract.actions.len() != 1
        || call.fallible_transcript.is_some()
        || mint.value != MINT_AMOUNT
        || mint.type_ != call.address.custom_shielded_token_type(mint_domain)
        || !offer.inputs.is_empty()
        || offer.outputs.len() != 2
        || offer.transient.len() != 1
        || offer.deltas.len() != 1
    {
        return false;
    }

    let Some(transient) = offer.transient.iter_deref().next() else {
        return false;
    };
    let Some(delta) = offer.deltas.iter_deref().next() else {
        return false;
    };

    let change_amount = MINT_AMOUNT - USER_AMOUNT;
    let user_coin = mint.evolve_from(NONCE_EVOLUTION_DOMAIN, USER_AMOUNT, mint.type_);
    let change_coin =
        mint.evolve_from(CHANGE_NONCE_EVOLUTION_DOMAIN, change_amount, mint.type_);
    let transient_commitment = mint.commitment(&Recipient::Contract(call.address));
    let transient_nullifier = mint.nullifier(&SenderEvidence::Contract(call.address));
    let user_commitment = user_coin.commitment(&Recipient::User(recipient));
    let change_commitment = change_coin.commitment(&Recipient::Contract(call.address));
    if user_commitment == change_commitment {
        return false;
    }
    let Some(user_output) = offer.outputs.iter_deref().find(|output| {
        output.coin_com == user_commitment
            && output.contract_address.is_none()
            && output.ciphertext.is_some()
    }) else {
        return false;
    };
    let Some(change_output) = offer.outputs.iter_deref().find(|output| {
        output.coin_com == change_commitment
            && output.contract_address.as_deref() == Some(&call.address)
            && output.ciphertext.is_none()
    }) else {
        return false;
    };
    let effects = &transcript.effects;

    effects.claimed_contract_calls.size() == 0
        && no_unshielded_effects(effects)
        && effects.claimed_nullifiers.size() == 1
        && effects.claimed_nullifiers.member(&transient_nullifier)
        && effects.claimed_shielded_receives.size() == 2
        && effects.claimed_shielded_receives.member(&transient_commitment)
        && effects.claimed_shielded_receives.member(&change_commitment)
        && effects.claimed_shielded_spends.size() == 2
        && effects.claimed_shielded_spends.member(&user_commitment)
        && effects.claimed_shielded_spends.member(&change_commitment)
        && effects.shielded_mints.size() == 1
        && effects
            .shielded_mints
            .get(&mint_domain)
            .is_some_and(|amount| *amount == MINT_AMOUNT as u64)
        && transient.coin_com == transient_commitment
        && transient.nullifier == transient_nullifier
        && transient.contract_address.as_deref() == Some(&call.address)
        && transient.ciphertext.is_none()
        && user_output.coin_com == user_commitment
        && user_output.contract_address.is_none()
        && user_output.ciphertext.is_some()
        && change_output.coin_com == change_commitment
        && change_output.contract_address.as_deref() == Some(&call.address)
        && change_output.ciphertext.is_none()
        && delta.token_type == mint.type_
        && delta.value == -(MINT_AMOUNT as i128)
}

/// Bind the proved merge effects to the precise guaranteed offer that the host booked.
#[cfg(feature = "localnet")]
pub(crate) fn shielded_merge_shape_valid(
    contract: &ProvedNativeIntent,
    offer: &zswap::Offer<transient_crypto::proofs::Proof, Db>,
    staged_mint: Option<(&Info, HashOutput)>,
) -> bool {
    let Some(ContractAction::Call(call)) = contract.actions.get(0) else {
        return false;
    };
    let Some(transcript) = call.guaranteed_transcript.as_deref() else {
        return false;
    };
    contract.actions.len() == 1
        && call.fallible_transcript.is_none()
        && shielded_merge_claims_match(&transcript.effects, call.address, offer, staged_mint)
}

#[cfg(feature = "localnet")]
pub(crate) fn shielded_merge_claims_match<P: storage::Storable<Db>>(
    effects: &Effects<Db>,
    address: coin_structure::contract::ContractAddress,
    offer: &zswap::Offer<P, Db>,
    staged_mint: Option<(&Info, HashOutput)>,
) -> bool {
    let (Some(input), Some(output)) = (offer.inputs.get(0), offer.outputs.get(0)) else {
        return false;
    };
    if effects.claimed_contract_calls.size() != 0
        || !no_unshielded_effects(effects)
        || offer.outputs.len() != 1
        || input.contract_address.as_deref() != Some(&address)
        || output.contract_address.as_deref() != Some(&address)
        || output.ciphertext.is_some()
        || effects.claimed_nullifiers.size() != 2
        || !effects.claimed_nullifiers.member(&input.nullifier)
        || effects.claimed_shielded_spends.size() != 1
        || !effects.claimed_shielded_spends.member(&output.coin_com)
        || !effects.claimed_shielded_receives.member(&output.coin_com)
    {
        return false;
    }

    match staged_mint {
        Some((mint, domain)) => {
            let (Some(transient), Some(delta), Ok(amount)) = (
                offer.transient.get(0), offer.deltas.get(0), u64::try_from(mint.value),
            ) else {
                return false;
            };
            let token_type = address.custom_shielded_token_type(domain);
            offer.inputs.len() == 1
                && offer.transient.len() == 1
                && offer.deltas.len() == 1
                && amount > 0
                && mint.type_ == token_type
                && delta.token_type == token_type
                && delta.value == -i128::from(amount)
                && transient.contract_address.as_deref() == Some(&address)
                && transient.ciphertext.is_none()
                && transient.nullifier == mint.nullifier(&SenderEvidence::Contract(address))
                && transient.coin_com == mint.commitment(&Recipient::Contract(address))
                && transient.nullifier != input.nullifier
                && transient.coin_com != output.coin_com
                && effects.claimed_nullifiers.member(&transient.nullifier)
                && effects.claimed_shielded_receives.size() == 2
                && effects.claimed_shielded_receives.member(&transient.coin_com)
                && effects.shielded_mints.size() == 1
                && effects.shielded_mints.get(&domain).is_some_and(|value| *value == amount)
        }
        None => {
            let Some(second) = offer.inputs.get(1) else {
                return false;
            };
            offer.inputs.len() == 2
                && offer.transient.is_empty()
                && offer.deltas.is_empty()
                && second.contract_address.as_deref() == Some(&address)
                && second.nullifier != input.nullifier
                && effects.claimed_nullifiers.member(&second.nullifier)
                && effects.claimed_shielded_receives.size() == 1
                && effects.shielded_mints.size() == 0
        }
    }
}

enum ContractFunding {
    Offerless,
    #[cfg(feature = "localnet")]
    Shielded(Vec<u8>),
    UnshieldedCaller,
    UnshieldedMint,
}

impl BoundTransaction {
    pub async fn prepare(
        contract: &ProvedNativeIntent,
        policy: NetworkPolicy,
        chain: &impl ChainAdapter,
        funding: &impl FundingAdapter,
        signer: &impl SigningAdapter,
    ) -> Result<Self> {
        Self::prepare_inner(contract, policy, chain, funding, signer, ContractFunding::Offerless)
            .await
    }

    /// Fund and bind a single top-level call with a same-owner unshielded return offer.
    /// The caller inputs must still exist in the fresh funding snapshot.
    pub async fn prepare_unshielded_caller(
        contract: &ProvedNativeIntent,
        policy: NetworkPolicy,
        chain: &impl ChainAdapter,
        funding: &impl FundingAdapter,
        signer: &impl SigningAdapter,
    ) -> Result<Self> {
        Self::prepare_inner(contract, policy, chain, funding, signer, ContractFunding::UnshieldedCaller)
            .await
    }

    /// Fund a single guaranteed custom-token mint to the user named by its proved transcript.
    /// The transaction pays the exact derived output and takes no unshielded inputs.
    pub async fn prepare_unshielded_mint(
        contract: &ProvedNativeIntent,
        policy: NetworkPolicy,
        chain: &impl ChainAdapter,
        funding: &impl FundingAdapter,
        signer: &impl SigningAdapter,
    ) -> Result<Self> {
        require(contract.guaranteed_unshielded_offer.is_none(), Error::InvalidTransaction)?;
        let output = crate::unshielded_mint::derive_user_output(contract)
            .map_err(|_| Error::InvalidTransaction)?;
        let mut contract = contract.clone();
        contract.guaranteed_unshielded_offer = Some(storage::arena::Sp::new(UnshieldedOffer {
            inputs: Default::default(),
            outputs: vec![output].into(),
            signatures: Default::default(),
        }));
        Self::prepare_inner(&contract, policy, chain, funding, signer, ContractFunding::UnshieldedMint)
            .await
    }

    #[cfg(feature = "localnet")]
    pub(crate) async fn prepare_shielded_receive(
        contract: &ProvedNativeIntent,
        expected_offer: &zswap::Offer<transient_crypto::proofs::Proof, Db>,
        policy: NetworkPolicy,
        chain: &impl ChainAdapter,
        funding: &impl FundingAdapter,
        signer: &impl SigningAdapter,
    ) -> Result<Self> {
        require(
            expected_offer.outputs.len() == 1
                && expected_offer.inputs.is_empty()
                && expected_offer.transient.is_empty(),
            Error::Funding,
        )?;
        let expected_offer = body(&Some(storage::arena::Sp::new(expected_offer.clone())))?;
        Self::prepare_inner(
            contract,
            policy,
            chain,
            funding,
            signer,
            ContractFunding::Shielded(expected_offer),
        )
        .await
    }

    #[cfg(feature = "localnet")]
    pub(crate) async fn prepare_wallet_shielded_receive(
        contract: &ProvedNativeIntent,
        expected_offer: &zswap::Offer<transient_crypto::proofs::Proof, Db>,
        policy: NetworkPolicy,
        chain: &impl ChainAdapter,
        funding: &impl FundingAdapter,
        signer: &impl SigningAdapter,
    ) -> Result<Self> {
        let Some(ContractAction::Call(call)) = contract.actions.get(0) else {
            return Err(Error::Funding);
        };
        let Some(transcript) = call.guaranteed_transcript.as_deref() else {
            return Err(Error::Funding);
        };
        let Some(input) = expected_offer.inputs.get(0) else {
            return Err(Error::Funding);
        };
        let Some(output) = expected_offer.outputs.get(0) else {
            return Err(Error::Funding);
        };
        require(
            contract.actions.len() == 1
                && call.fallible_transcript.is_none()
                && transcript.effects.claimed_nullifiers.size() == 0
                && transcript.effects.claimed_shielded_spends.size() == 0
                && transcript.effects.claimed_shielded_receives.size() == 1
                && transcript
                    .effects
                    .claimed_shielded_receives
                    .iter()
                    .any(|commitment| **commitment == output.coin_com)
                && transcript.effects.shielded_mints.size() == 0
                && expected_offer.inputs.len() == 1
                && expected_offer.outputs.len() == 1
                && expected_offer.transient.is_empty()
                && input.contract_address.is_none()
                && output.contract_address.as_deref() == Some(&call.address),
            Error::Funding,
        )?;
        let expected_offer = body(&Some(storage::arena::Sp::new(expected_offer.clone())))?;
        Self::prepare_inner(
            contract,
            policy,
            chain,
            funding,
            signer,
            ContractFunding::Shielded(expected_offer),
        )
        .await
    }

    #[cfg(feature = "localnet")]
    pub(crate) async fn prepare_shielded_transfer(
        contract: &ProvedNativeIntent,
        expected_offer: &zswap::Offer<transient_crypto::proofs::Proof, Db>,
        policy: NetworkPolicy,
        chain: &impl ChainAdapter,
        funding: &impl FundingAdapter,
        signer: &impl SigningAdapter,
    ) -> Result<Self> {
        let Some(ContractAction::Call(call)) = contract.actions.get(0) else {
            return Err(Error::Funding);
        };
        let Some(transcript) = call.guaranteed_transcript.as_deref() else {
            return Err(Error::Funding);
        };
        let Some(input) = expected_offer.inputs.get(0) else {
            return Err(Error::Funding);
        };
        let Some(output) = expected_offer.outputs.get(0) else {
            return Err(Error::Funding);
        };
        require(
            contract.actions.len() == 1
                && call.fallible_transcript.is_none()
                && transcript.effects.claimed_nullifiers.size() == 1
                && transcript
                    .effects
                    .claimed_nullifiers
                    .iter()
                    .any(|nullifier| **nullifier == input.nullifier)
                && transcript.effects.claimed_shielded_spends.size() == 1
                && transcript
                    .effects
                    .claimed_shielded_spends
                    .iter()
                    .any(|commitment| **commitment == output.coin_com)
                && transcript.effects.claimed_shielded_receives.size() == 0
                && transcript.effects.shielded_mints.size() == 0
                && expected_offer.inputs.len() == 1
                && expected_offer.outputs.len() == 1
                && expected_offer.transient.is_empty()
                && input.contract_address.as_deref() == Some(&call.address)
                && output.contract_address.is_none()
                && output.ciphertext.is_some(),
            Error::Funding,
        )?;
        let expected_offer = body(&Some(storage::arena::Sp::new(expected_offer.clone())))?;
        Self::prepare_inner(
            contract,
            policy,
            chain,
            funding,
            signer,
            ContractFunding::Shielded(expected_offer),
        )
        .await
    }

    #[cfg(feature = "localnet")]
    pub(crate) async fn prepare_shielded_merge(
        contract: &ProvedNativeIntent,
        expected_offer: &zswap::Offer<transient_crypto::proofs::Proof, Db>,
        staged_mint: Option<(&Info, HashOutput)>,
        policy: NetworkPolicy,
        chain: &impl ChainAdapter,
        funding: &impl FundingAdapter,
        signer: &impl SigningAdapter,
    ) -> Result<Self> {
        require(
            shielded_merge_shape_valid(contract, expected_offer, staged_mint),
            Error::Funding,
        )?;
        let expected_offer = body(&Some(storage::arena::Sp::new(expected_offer.clone())))?;
        Self::prepare_inner(
            contract,
            policy,
            chain,
            funding,
            signer,
            ContractFunding::Shielded(expected_offer),
        )
        .await
    }

    #[cfg(feature = "localnet")]
    pub(crate) async fn prepare_shielded_relay(
        contract: &ProvedNativeIntent,
        expected_offer: &zswap::Offer<transient_crypto::proofs::Proof, Db>,
        relay_mint: &Info,
        mint_domain: HashOutput,
        policy: NetworkPolicy,
        chain: &impl ChainAdapter,
        funding: &impl FundingAdapter,
        signer: &impl SigningAdapter,
    ) -> Result<Self> {
        require(
            shielded_relay_shape_valid(contract, expected_offer, relay_mint, mint_domain),
            Error::Funding,
        )?;
        let expected_offer = body(&Some(storage::arena::Sp::new(expected_offer.clone())))?;
        Self::prepare_inner(
            contract,
            policy,
            chain,
            funding,
            signer,
            ContractFunding::Shielded(expected_offer),
        )
        .await
    }

    #[cfg(feature = "localnet")]
    pub(crate) async fn prepare_shielded_immediate_change(
        contract: &ProvedNativeIntent,
        expected_offer: &zswap::Offer<transient_crypto::proofs::Proof, Db>,
        mint: &Info,
        mint_domain: HashOutput,
        recipient: PublicKey,
        policy: NetworkPolicy,
        chain: &impl ChainAdapter,
        funding: &impl FundingAdapter,
        signer: &impl SigningAdapter,
    ) -> Result<Self> {
        require(
            shielded_immediate_change_shape_valid(
                contract,
                expected_offer,
                mint,
                mint_domain,
                recipient,
            ),
            Error::Funding,
        )?;
        let expected_offer = body(&Some(storage::arena::Sp::new(expected_offer.clone())))?;
        Self::prepare_inner(
            contract,
            policy,
            chain,
            funding,
            signer,
            ContractFunding::Shielded(expected_offer),
        )
        .await
    }

    #[cfg(feature = "localnet")]
    pub(crate) async fn prepare_shielded_split(
        contract: &ProvedNativeIntent,
        expected_offer: &zswap::Offer<transient_crypto::proofs::Proof, Db>,
        policy: NetworkPolicy,
        chain: &impl ChainAdapter,
        funding: &impl FundingAdapter,
        signer: &impl SigningAdapter,
    ) -> Result<Self> {
        let Some(ContractAction::Call(call)) = contract.actions.get(0) else {
            return Err(Error::Funding);
        };
        let Some(transcript) = call.guaranteed_transcript.as_deref() else {
            return Err(Error::Funding);
        };
        let Some(input) = expected_offer.inputs.get(0) else {
            return Err(Error::Funding);
        };
        let mut user_output = None;
        let mut change_output = None;
        for output in expected_offer.outputs.iter_deref() {
            match (
                output.contract_address.as_deref(),
                output.ciphertext.is_some(),
            ) {
                (None, true) if user_output.is_none() => user_output = Some(output),
                (Some(owner), false) if owner == &call.address && change_output.is_none() => {
                    change_output = Some(output)
                }
                _ => return Err(Error::Funding),
            }
        }
        let (Some(user_output), Some(change_output)) = (user_output, change_output) else {
            return Err(Error::Funding);
        };
        require(
            contract.actions.len() == 1
                && call.fallible_transcript.is_none()
                && transcript.effects.claimed_nullifiers.size() == 1
                && transcript
                    .effects
                    .claimed_nullifiers
                    .iter()
                    .any(|nullifier| **nullifier == input.nullifier)
                && transcript.effects.claimed_shielded_spends.size() == 2
                && transcript
                    .effects
                    .claimed_shielded_spends
                    .iter()
                    .any(|commitment| **commitment == user_output.coin_com)
                && transcript
                    .effects
                    .claimed_shielded_spends
                    .iter()
                    .any(|commitment| **commitment == change_output.coin_com)
                && transcript.effects.claimed_shielded_receives.size() == 1
                && transcript
                    .effects
                    .claimed_shielded_receives
                    .iter()
                    .any(|commitment| **commitment == change_output.coin_com)
                && transcript.effects.shielded_mints.size() == 0
                && user_output.coin_com != change_output.coin_com
                && expected_offer.inputs.len() == 1
                && expected_offer.outputs.len() == 2
                && expected_offer.transient.is_empty()
                && input.contract_address.as_deref() == Some(&call.address),
            Error::Funding,
        )?;
        let expected_offer = body(&Some(storage::arena::Sp::new(expected_offer.clone())))?;
        Self::prepare_inner(
            contract,
            policy,
            chain,
            funding,
            signer,
            ContractFunding::Shielded(expected_offer),
        )
        .await
    }

    async fn prepare_inner(
        contract: &ProvedNativeIntent,
        policy: NetworkPolicy,
        chain: &impl ChainAdapter,
        funding: &impl FundingAdapter,
        signer: &impl SigningAdapter,
        offer: ContractFunding,
    ) -> Result<Self> {
        policy.validate()?;
        let snapshot = chain.snapshot().await.map_err(|_| Error::Network)?;
        snapshot.validate(&policy)?;
        require(
            admissible_actions(contract)
                && contract.dust_actions.is_none()
                && contract.fallible_unshielded_offer.is_none(),
            Error::InvalidTransaction,
        )?;
        let (address, event) = match contract
            .actions
            .iter_deref()
            .next()
            .ok_or(Error::InvalidTransaction)?
        {
            ContractAction::Deploy(deploy) => (deploy.address(), ContractEvent::Deploy),
            ContractAction::Call(call) => (call.address, ContractEvent::Call),
            ContractAction::Maintain(update) => (update.address, ContractEvent::Maintain),
        };
        let funded = match &offer {
            ContractFunding::UnshieldedCaller => {
                crate::unshielded_caller::validate_guaranteed_caller_offer(&snapshot, contract)
                    .map_err(|_| Error::InvalidTransaction)?;
                funding.fund_unshielded_caller(contract, &snapshot, &policy).await
            }
            ContractFunding::UnshieldedMint => {
                crate::unshielded_mint::validate_user_output_offer(contract)
                    .map_err(|_| Error::InvalidTransaction)?;
                funding.fund(contract, &snapshot, &policy).await
            }
            _ => {
                require(contract.guaranteed_unshielded_offer.is_none(), Error::InvalidTransaction)?;
                funding.fund(contract, &snapshot, &policy).await
            }
        }
        .map_err(|_| Error::Funding)?;
        let Transaction::Standard(funded_stx) = &funded else {
            return Err(Error::Funding);
        };
        require(
            funded_stx.network_id == policy.network_id
                && funded_stx
                    .intents
                    .get(&CONTRACT_SEGMENT)
                    .map(|intent| encode(&*intent))
                    .transpose()?
                    == Some(encode(contract)?),
            Error::AlteredTransaction,
        )?;
        let guaranteed_offer_matches = match offer {
            #[cfg(feature = "localnet")]
            ContractFunding::Shielded(expected) => body(&funded_stx.guaranteed_coins)? == expected,
            _ => funded_stx.guaranteed_coins.is_none(),
        };
        require(
            guaranteed_offer_matches
                && funded_stx.fallible_coins.is_empty()
                && funded_stx.intents.iter().take(3).count() <= 2,
            Error::Funding,
        )?;
        for item in funded_stx.intents.iter() {
            if *item.0 != CONTRACT_SEGMENT {
                require(
                    *item.0 == crate::funding::FUNDING_SEGMENT
                        && item.1.actions.is_empty()
                        && item.1.guaranteed_unshielded_offer.is_none()
                        && item.1.fallible_unshielded_offer.is_none()
                        && item
                            .1
                            .dust_actions
                            .as_ref()
                            .is_some_and(|d| d.registrations.is_empty()),
                    Error::Funding,
                )?;
            }
        }
        let approved = signer
            .approve_and_sign(&funded, &snapshot, &policy)
            .await
            .map_err(|_| Error::Approval)?;
        let Transaction::Standard(signed) = &approved else {
            return Err(Error::AlteredTransaction);
        };
        require(
            signed.network_id == policy.network_id
                && signed.intents.iter().take(3).count()
                    == funded_stx.intents.iter().take(3).count(),
            Error::AlteredTransaction,
        )?;
        // Signing and binding seals must preserve every proof, action and public commitment.
        for item in funded_stx.intents.iter() {
            let signed_intent = signed
                .intents
                .get(&*item.0)
                .ok_or(Error::AlteredTransaction)?;
            require(
                encode(&public_intent(&*item.1).erase_signatures())?
                    == encode(&public_intent(&*signed_intent).erase_signatures())?,
                Error::AlteredTransaction,
            )?;
        }
        require(
            body(&funded_stx.guaranteed_coins)? == body(&signed.guaranteed_coins)?
                && body(&funded_stx.fallible_coins)? == body(&signed.fallible_coins)?,
            Error::AlteredTransaction,
        )?;
        let fees = approved
            .fees_with_margin(&snapshot.state.parameters, 0)
            .map_err(|_| Error::Parameters)?;
        let mut spent = 0u128;
        for item in signed.intents.iter() {
            if let Some(dust) = item.1.dust_actions.as_ref() {
                for spend in dust.spends.iter_deref() {
                    spent = spent.checked_add(spend.v_fee).ok_or(Error::Funding)?;
                }
            }
        }
        require(spent >= fees && spent <= policy.max_dust, Error::Funding)?;
        let verified = approved
            .well_formed(
                &snapshot.state,
                WellFormedStrictness::default(),
                snapshot.block.tblock,
            )
            .map_err(|_| Error::InvalidTransaction)?;
        let context = TransactionContext {
            ref_state: snapshot.state.clone(),
            block_context: snapshot.block.clone(),
            whitelist: None,
        };
        let guaranteed = snapshot
            .state
            .apply_guaranteed_only(verified, &context)
            .map_err(|_| Error::InvalidTransaction)?;
        let checkpoint = checkpoint_call(&approved)
            .map(|(_, entrypoint, segments)| {
                let state = encode(
                    &*guaranteed
                        .contract
                        .get(&address)
                        .ok_or(Error::InvalidTransaction)?,
                )?;
                require(state.len() <= MAX_STATE, Error::InvalidTransaction)?;
                Ok(CheckpointPrefix {
                    entrypoint,
                    segments,
                    state,
                })
            })
            .transpose()?;
        let (predicted, outcome) = guaranteed.apply_fallible(&context);
        require(
            matches!(outcome, TransactionResult::Success(_)),
            Error::InvalidTransaction,
        )?;
        let expected_state = encode(
            &*predicted
                .contract
                .get(&address)
                .ok_or(Error::InvalidTransaction)?,
        )?;
        let mut call_counts = BTreeMap::new();
        let mut secondary_states = BTreeMap::new();
        let mut state_bytes = expected_state.len();
        if contract.actions.len() > 1 {
            for call in contract.calls() {
                let encoded = hex::encode(call.address.0.0);
                let count = call_counts.entry(encoded.clone()).or_insert(0);
                *count += 1;
                if *count == 1 && call.address != address {
                    let state = predicted
                        .contract
                        .get(&call.address)
                        .ok_or(Error::InvalidTransaction)?;
                    let bytes = encode(&*state)?;
                    state_bytes = state_bytes
                        .checked_add(bytes.len())
                        .ok_or(Error::InvalidTransaction)?;
                    require(
                        bytes.len() <= MAX_STATE && state_bytes <= MAX_TRANSACTION,
                        Error::InvalidTransaction,
                    )?;
                    secondary_states.insert(encoded, bytes);
                }
            }
        }
        let transaction = encode(&approved)?;
        require(
            transaction.len() <= MAX_TRANSACTION && expected_state.len() <= MAX_STATE,
            Error::InvalidTransaction,
        )?;
        let intent_id = hex::encode(
            signed
                .intents
                .get(&CONTRACT_SEGMENT)
                .ok_or(Error::Identity)?
                .erase_proofs()
                .erase_signatures()
                .intent_hash(CONTRACT_SEGMENT)
                .0
                .0,
        );
        let transaction_id = hex::encode(approved.transaction_hash().0.0);
        Ok(Self {
            data: BoundData {
                policy,
                transaction,
                transaction_id,
                intent_id,
                contract_address: hex::encode(address.0.0),
                event,
                expected_state,
                checkpoint,
                call_counts,
                secondary_states,
                after_height: snapshot.height,
            },
        })
    }
    pub fn bytes(&self) -> &[u8] {
        &self.data.transaction
    }
    pub fn transaction_id(&self) -> &str {
        &self.data.transaction_id
    }
    pub fn intent_id(&self) -> &str {
        &self.data.intent_id
    }
    pub fn contract_address(&self) -> &str {
        &self.data.contract_address
    }
    pub fn event(&self) -> ContractEvent {
        self.data.event
    }
    pub fn after_height(&self) -> u64 {
        self.data.after_height
    }
    pub fn policy(&self) -> &NetworkPolicy {
        &self.data.policy
    }
    pub fn expected_state(&self) -> &[u8] {
        &self.data.expected_state
    }
    pub fn checkpoint_entrypoint(&self) -> Option<&[u8]> {
        self.data
            .checkpoint
            .as_ref()
            .map(|prefix| prefix.entrypoint.as_slice())
    }
    /// Predicted canonical states for the other called addresses.
    pub fn secondary_states(&self) -> &BTreeMap<String, Vec<u8>> {
        &self.data.secondary_states
    }
    /// Exact address multiplicities for the receipt's contract event kind.
    pub fn contract_event_counts(&self) -> BTreeMap<String, usize> {
        match self.event() {
            ContractEvent::Maintain => BTreeMap::new(),
            _ if self.data.call_counts.is_empty() => [(self.contract_address().into(), 1)].into(),
            _ => self.data.call_counts.clone(),
        }
    }
    pub fn check_receipt(&self, receipt: &FinalizedReceipt) -> Result<()> {
        self.check_receipt_identity(receipt)?;
        require(
            receipt.contract_state == self.data.expected_state
                && receipt.secondary_states == self.data.secondary_states,
            Error::Receipt,
        )
    }
    pub fn check_partial_receipt(&self, partial: &PartialReceipt) -> Result<()> {
        let prefix = self.data.checkpoint.as_ref().ok_or(Error::Receipt)?;
        self.check_receipt_identity(&partial.receipt)?;
        require(
            partial.segments == prefix.segments
                && partial.entrypoint == prefix.entrypoint
                && partial.receipt.contract_state == prefix.state
                && partial.receipt.secondary_states.is_empty(),
            Error::Receipt,
        )
    }
    fn check_receipt_identity(&self, receipt: &FinalizedReceipt) -> Result<()> {
        self.data.policy.check(&receipt.chain)?;
        require(
            receipt.height > self.data.after_height && receipt.height <= receipt.finalized_height,
            Error::StaleReceipt,
        )?;
        // A receipt observed at the finalized height names the finalized block itself.
        // When finality has advanced, inclusion and head hashes identify different blocks.
        require(
            (receipt.height == receipt.finalized_height)
                == (receipt.block_hash == receipt.finalized_hash),
            Error::Receipt,
        )?;
        require(
            canonical_hash(&receipt.block_hash)
                && canonical_hash(&receipt.finalized_hash)
                && canonical_hash(&receipt.extrinsic_hash)
                && receipt.transaction_id == self.data.transaction_id
                && receipt.intent_id == self.data.intent_id
                && receipt.contract_address == self.data.contract_address
                && receipt.event == self.data.event,
            Error::Receipt,
        )
    }
}

/// Read-only public correlation. This type never authorizes submission or private CAS.
pub struct PublicTransactionReference {
    data: BoundData,
}
fn decode_public_transaction(
    policy: &NetworkPolicy,
    transaction: &[u8],
    after_height: u64,
    state_lengths: &[usize],
) -> Result<SealedTransaction> {
    policy.validate()?;
    let state_bytes = state_lengths
        .iter()
        .try_fold(0usize, |total, length| total.checked_add(*length))
        .ok_or(Error::InvalidTransaction)?;
    require(
        !transaction.is_empty()
            && transaction.len() <= MAX_TRANSACTION
            && state_lengths.iter().all(|length| *length <= MAX_STATE)
            && state_bytes <= MAX_TRANSACTION
            && after_height < u64::MAX,
        Error::InvalidTransaction,
    )?;
    let native: SealedTransaction =
        tagged_deserialize(transaction).map_err(|_| Error::InvalidTransaction)?;
    require(encode(&native)? == transaction, Error::InvalidTransaction)?;
    let Transaction::Standard(stx) = &native else {
        return Err(Error::InvalidTransaction);
    };
    require(stx.network_id == policy.network_id, Error::Network)?;
    require(
        stx.guaranteed_coins.is_none()
            && stx.fallible_coins.is_empty()
            && stx.intents.iter().take(3).count() <= 2,
        Error::InvalidTransaction,
    )?;
    for item in stx.intents.iter() {
        let segment = &item.0;
        let intent = &item.1;
        require(
            intent.guaranteed_unshielded_offer.is_none()
                && intent.fallible_unshielded_offer.is_none(),
            Error::InvalidTransaction,
        )?;
        if **segment == CONTRACT_SEGMENT {
            require(intent.dust_actions.is_none(), Error::InvalidTransaction)?;
        } else {
            require(
                **segment == crate::funding::FUNDING_SEGMENT
                    && intent.actions.is_empty()
                    && intent
                        .dust_actions
                        .as_ref()
                        .is_some_and(|dust| dust.registrations.is_empty()),
                Error::InvalidTransaction,
            )?;
        }
    }
    Ok(native)
}
impl PublicTransactionReference {
    pub fn from_bytes(
        policy: NetworkPolicy,
        transaction: &[u8],
        after_height: u64,
        expected_state: &[u8],
    ) -> Result<Self> {
        let native =
            decode_public_transaction(&policy, transaction, after_height, &[expected_state.len()])?;
        let Transaction::Standard(stx) = &native else {
            return Err(Error::InvalidTransaction);
        };
        let intent = stx
            .intents
            .get(&CONTRACT_SEGMENT)
            .ok_or(Error::InvalidTransaction)?;
        require(intent.actions.len() == 1, Error::InvalidTransaction)?;
        let (address, event) = match intent
            .actions
            .iter_deref()
            .next()
            .ok_or(Error::InvalidTransaction)?
        {
            ContractAction::Deploy(deploy) => {
                require(
                    encode(&deploy.initial_state)? == expected_state,
                    Error::Receipt,
                )?;
                (deploy.address(), ContractEvent::Deploy)
            }
            ContractAction::Call(call) => (call.address, ContractEvent::Call),
            ContractAction::Maintain(update) => (update.address, ContractEvent::Maintain),
        };
        let intent_id = hex::encode(
            intent
                .erase_proofs()
                .erase_signatures()
                .intent_hash(CONTRACT_SEGMENT)
                .0
                .0,
        );
        Ok(Self {
            data: BoundData {
                policy,
                transaction: transaction.to_vec(),
                transaction_id: hex::encode(native.transaction_hash().0.0),
                intent_id,
                contract_address: hex::encode(address.0.0),
                event,
                expected_state: expected_state.to_vec(),
                checkpoint: None,
                call_counts: BTreeMap::new(),
                secondary_states: BTreeMap::new(),
                after_height,
            },
        })
    }
    /// Binds exactly two ordered calls to caller-authenticated `(address, entrypoint, state)` slots.
    /// This read-only reference checks the finalized receipt; it does not verify proofs or submit.
    pub fn from_composed_calls(
        policy: NetworkPolicy,
        transaction: &[u8],
        after_height: u64,
        expected_calls: [(&[u8], &[u8], &[u8]); 2],
    ) -> Result<Self> {
        let state_lengths = [expected_calls[0].2.len(), expected_calls[1].2.len()];
        let native = decode_public_transaction(&policy, transaction, after_height, &state_lengths)?;
        let Transaction::Standard(stx) = &native else {
            return Err(Error::InvalidTransaction);
        };
        let intent = stx
            .intents
            .get(&CONTRACT_SEGMENT)
            .ok_or(Error::InvalidTransaction)?;
        require(intent.actions.len() == 2, Error::InvalidTransaction)?;
        let mut actions = intent.actions.iter_deref();
        let Some(ContractAction::Call(first)) = actions.next() else {
            return Err(Error::InvalidTransaction);
        };
        let Some(ContractAction::Call(second)) = actions.next() else {
            return Err(Error::InvalidTransaction);
        };
        require(actions.next().is_none(), Error::InvalidTransaction)?;
        let [
            (first_address, first_entrypoint, first_state),
            (second_address, second_entrypoint, second_state),
        ] = expected_calls;
        require(
            first_address.len() == 32
                && second_address.len() == 32
                && first_address != second_address,
            Error::Identity,
        )?;
        require(
            first.address.0.0.as_slice() == first_address
                && first.entry_point.0.as_slice() == first_entrypoint
                && second.address.0.0.as_slice() == second_address
                && second.entry_point.0.as_slice() == second_entrypoint,
            Error::Identity,
        )?;

        let first_encoded = hex::encode(first.address.0.0);
        let second_encoded = hex::encode(second.address.0.0);
        let intent_id = hex::encode(
            intent
                .erase_proofs()
                .erase_signatures()
                .intent_hash(CONTRACT_SEGMENT)
                .0
                .0,
        );
        Ok(Self {
            data: BoundData {
                policy,
                transaction: transaction.to_vec(),
                transaction_id: hex::encode(native.transaction_hash().0.0),
                intent_id,
                contract_address: first_encoded.clone(),
                event: ContractEvent::Call,
                expected_state: first_state.to_vec(),
                checkpoint: None,
                call_counts: [(first_encoded, 1), (second_encoded.clone(), 1)].into(),
                secondary_states: [(second_encoded, second_state.to_vec())].into(),
                after_height,
            },
        })
    }
    pub fn transaction_id(&self) -> &str {
        &self.data.transaction_id
    }
    pub fn contract_address(&self) -> &str {
        &self.data.contract_address
    }
    pub fn event(&self) -> ContractEvent {
        self.data.event
    }
    pub fn check_receipt(&self, receipt: &FinalizedReceipt) -> Result<()> {
        self.bound_view().check_receipt(receipt)
    }
    pub(crate) fn bound_view(&self) -> BoundTransaction {
        BoundTransaction {
            data: self.data.clone(),
        }
    }
    #[cfg(feature = "localnet")]
    pub(crate) fn development_submission_view(
        &self,
    ) -> std::result::Result<BoundTransaction, HostFailure> {
        if !self.data.secondary_states.is_empty() {
            return Err(HostFailure);
        }
        Ok(self.bound_view())
    }
}

#[derive(Clone, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct JournalIdentity {
    pub attempt_id: String,
    pub transaction_id: String,
    pub base_revision: String,
    pub journal_digest: String,
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CasReceipt {
    pub identity: JournalIdentity,
    pub revision: String,
    pub committed: bool,
}
#[derive(Clone, Copy, Eq, PartialEq, Serialize, Deserialize)]
enum DurablePhase {
    Prepared,
    Persisted,
    Submitted,
    Uncertain,
    Accepted,
    PartiallyAccepted,
    Rejected,
    Committed,
    Conflicted,
    Cancelled,
}
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RecoveryRecord {
    version: u32,
    bound: BoundData,
    identity: JournalIdentity,
    journal: Vec<u8>,
    phase: DurablePhase,
    cas: Option<CasReceipt>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    partial_receipt: Option<PartialReceipt>,
}
impl Drop for RecoveryRecord {
    fn drop(&mut self) {
        self.journal.zeroize();
    }
}
impl RecoveryRecord {
    pub fn phase(&self) -> Phase {
        match self.phase {
            DurablePhase::Prepared | DurablePhase::Persisted => Phase::Prepared,
            DurablePhase::Submitted => Phase::Submitted,
            DurablePhase::Uncertain => Phase::Uncertain,
            DurablePhase::Accepted => Phase::AwaitingCas,
            DurablePhase::PartiallyAccepted => Phase::PartiallyAccepted,
            DurablePhase::Rejected => Phase::Rejected,
            DurablePhase::Committed => Phase::Committed,
            DurablePhase::Conflicted => Phase::Conflicted,
            DurablePhase::Cancelled => Phase::Cancelled,
        }
    }
    pub fn cas_receipt(&self) -> Option<&CasReceipt> {
        self.cas.as_ref()
    }
    pub fn partial_receipt(&self) -> Option<&PartialReceipt> {
        self.partial_receipt.as_ref()
    }
    pub fn identity(&self) -> &JournalIdentity {
        &self.identity
    }
    pub fn transaction_bytes(&self) -> &[u8] {
        &self.bound.transaction
    }
    pub fn journal_bytes(&self) -> &[u8] {
        &self.journal
    }
    pub fn immutable_digest(&self) -> Result<String> {
        let value = Zeroizing::new(
            serde_json::to_vec(&(&self.version, &self.bound, &self.identity, &self.journal))
                .map_err(|_| Error::Persistence)?,
        );
        Ok(hash(&value))
    }
    pub fn private_bytes(&self) -> Result<Zeroizing<Vec<u8>>> {
        let bytes = serde_json::to_vec(self)
            .map(Zeroizing::new)
            .map_err(|_| Error::Persistence)?;
        require(bytes.len() <= 32 * 1024 * 1024, Error::Persistence)?;
        Ok(bytes)
    }
}
#[allow(async_fn_in_trait)]
pub trait JournalStore {
    /// Read the current authoritative record and its storage revision atomically.
    /// Importing unauthenticated caller bytes must never implement this operation.
    async fn load(&self, attempt_id: &str) -> std::result::Result<StoredRecord, HostFailure>;
    /// Durably retain exact bytes before acknowledging. Existing attempt bodies are immutable.
    async fn persist(
        &self,
        record: &RecoveryRecord,
        expected_revision: Option<u64>,
    ) -> std::result::Result<StoreAcknowledgement, HostFailure>;
    /// Deduplicate by the complete identity. Acceptance never implies private CAS success.
    async fn compare_exchange(
        &self,
        record: &RecoveryRecord,
    ) -> std::result::Result<CasReceipt, HostFailure>;
}
pub struct StoredRecord {
    pub private_bytes: Zeroizing<Vec<u8>>,
    pub revision: u64,
}
pub struct StoreAcknowledgement {
    pub identity: JournalIdentity,
    pub record_sha256: String,
    pub revision: u64,
}
pub struct SubmissionAttempt {
    record: RecoveryRecord,
    store_revision: Option<u64>,
    observed: bool,
}
impl SubmissionAttempt {
    pub fn new(
        bound: BoundTransaction,
        attempt_id: &str,
        runtime: &mut host::Runtime,
    ) -> Result<Self> {
        require(bound.data.call_counts.is_empty(), Error::InvalidTransaction)?;
        runtime
            .notify(host::Notice {
                abi_version: 1,
                event: "bind".into(),
                attempt_id: attempt_id.into(),
                transaction_id: bound.transaction_id().into(),
            })
            .map_err(|_| Error::Identity)?;
        let journal = runtime.private_journal().map_err(|_| Error::State)?;
        require(
            journal["contractAddress"].as_str() == Some(bound.contract_address()),
            Error::Identity,
        )?;
        let identity: JournalIdentity = JournalIdentity {
            attempt_id: attempt_id.into(),
            transaction_id: bound.transaction_id().into(),
            base_revision: journal["baseRevision"]
                .as_str()
                .ok_or(Error::Identity)?
                .into(),
            journal_digest: journal["journalDigest"]
                .as_str()
                .ok_or(Error::Identity)?
                .into(),
        };
        journal_valid(&journal, &identity)?;
        let record = RecoveryRecord {
            version: 1,
            bound: bound.data,
            identity,
            journal: serde_json::to_vec(&journal).map_err(|_| Error::Persistence)?,
            phase: DurablePhase::Prepared,
            cas: None,
            partial_receipt: None,
        };
        let attempt = Self {
            record,
            store_revision: None,
            observed: false,
        };
        attempt.model()?;
        Ok(attempt)
    }
    pub async fn recover(store: &impl JournalStore, attempt_id: &str) -> Result<Self> {
        require(canonical_hash(attempt_id), Error::Identity)?;
        let loaded = store
            .load(attempt_id)
            .await
            .map_err(|_| Error::Persistence)?;
        require(loaded.revision > 0, Error::Persistence)?;
        let attempt = Self::decode_record(&loaded.private_bytes, loaded.revision)?;
        require(
            attempt.record.identity.attempt_id == attempt_id,
            Error::Identity,
        )?;
        Ok(attempt)
    }
    fn decode_record(bytes: &[u8], revision: u64) -> Result<Self> {
        require(bytes.len() <= 32 * 1024 * 1024, Error::Persistence)?;
        let record: RecoveryRecord =
            serde_json::from_slice(bytes).map_err(|_| Error::Persistence)?;
        record.bound.policy.validate()?;
        require(
            record.version == 1
                && record.bound.transaction.len() <= MAX_TRANSACTION
                && record.bound.expected_state.len() <= MAX_STATE
                && record.bound.call_counts.is_empty()
                && record.bound.secondary_states.is_empty()
                && record.journal.len() <= host::MAX_PRIVATE_BYTES,
            Error::Persistence,
        )?;
        let transaction: SealedTransaction =
            tagged_deserialize(record.bound.transaction.as_slice())
                .map_err(|_| Error::Persistence)?;
        require(
            encode(&transaction)? == record.bound.transaction
                && hex::encode(transaction.transaction_hash().0.0)
                    == record.identity.transaction_id
                && record.bound.transaction_id == record.identity.transaction_id,
            Error::Identity,
        )?;
        let journal: serde_json::Value =
            serde_json::from_slice(&record.journal).map_err(|_| Error::Identity)?;
        require(
            journal["attemptId"].as_str() == Some(&record.identity.attempt_id)
                && journal["transactionId"].as_str() == Some(&record.identity.transaction_id)
                && journal["baseRevision"].as_str() == Some(&record.identity.base_revision)
                && journal["journalDigest"].as_str() == Some(&record.identity.journal_digest)
                && journal["contractAddress"].as_str() == Some(&record.bound.contract_address),
            Error::Identity,
        )?;
        journal_valid(&journal, &record.identity)?;
        let Transaction::Standard(stx) = &transaction else {
            return Err(Error::Identity);
        };
        let contract = stx.intents.get(&CONTRACT_SEGMENT).ok_or(Error::Identity)?;
        require(
            contract.actions.len() == 1
                && stx.network_id == record.bound.policy.network_id
                && hex::encode(
                    contract
                        .erase_proofs()
                        .erase_signatures()
                        .intent_hash(CONTRACT_SEGMENT)
                        .0
                        .0,
                ) == record.bound.intent_id,
            Error::Identity,
        )?;
        if let Some(prefix) = &record.bound.checkpoint {
            let (address, entrypoint, segments) =
                checkpoint_call(&transaction).ok_or(Error::Identity)?;
            require(
                record.bound.event == ContractEvent::Call
                    && record.bound.contract_address == address
                    && prefix.entrypoint == entrypoint
                    && prefix.segments == segments
                    && prefix.state.len() <= MAX_STATE,
                Error::Identity,
            )?;
        }
        let attempt = Self {
            record,
            store_revision: Some(revision),
            observed: false,
        };
        attempt.model()?;
        match (attempt.record.phase, &attempt.record.partial_receipt) {
            (DurablePhase::PartiallyAccepted, Some(receipt)) => {
                require(attempt.record.cas.is_none(), Error::Persistence)?;
                attempt.transaction().check_partial_receipt(receipt)?;
            }
            (DurablePhase::PartiallyAccepted, None) | (_, Some(_)) => {
                return Err(Error::Persistence);
            }
            _ => {}
        }
        Ok(attempt)
    }
    pub fn record(&self) -> &RecoveryRecord {
        &self.record
    }
    pub fn transaction(&self) -> BoundTransaction {
        BoundTransaction {
            data: self.record.bound.clone(),
        }
    }
    pub fn phase(&self) -> Result<Phase> {
        Ok(self.model()?.phase())
    }
    fn model(&self) -> Result<Lifecycle> {
        let identity = &self.record.identity;
        let mut model = Lifecycle::new(identity.attempt_id.clone(), identity.base_revision.clone())
            .map_err(|_| Error::Identity)?;
        model
            .apply(Event::ExecutionSucceeded)
            .map_err(|_| Error::State)?;
        model
            .apply(Event::Bind {
                transaction_id: identity.transaction_id.clone(),
            })
            .map_err(|_| Error::Identity)?;
        let ids = || (identity.transaction_id.clone(), identity.attempt_id.clone());
        if self.record.phase != DurablePhase::Prepared
            && self.record.phase != DurablePhase::Cancelled
        {
            let (transaction_id, attempt_id) = ids();
            model
                .apply(Event::Persisted {
                    transaction_id,
                    attempt_id,
                })
                .map_err(|_| Error::State)?;
        }
        if matches!(
            self.record.phase,
            DurablePhase::Submitted
                | DurablePhase::Uncertain
                | DurablePhase::Accepted
                | DurablePhase::PartiallyAccepted
                | DurablePhase::Rejected
                | DurablePhase::Committed
                | DurablePhase::Conflicted
        ) {
            let (transaction_id, attempt_id) = ids();
            model
                .apply(Event::Submitted {
                    transaction_id,
                    attempt_id,
                })
                .map_err(|_| Error::State)?;
        }
        if self.record.phase == DurablePhase::Uncertain {
            let (transaction_id, attempt_id) = ids();
            model
                .apply(Event::Uncertain {
                    transaction_id,
                    attempt_id,
                })
                .map_err(|_| Error::State)?;
        }
        if matches!(
            self.record.phase,
            DurablePhase::Accepted | DurablePhase::Committed | DurablePhase::Conflicted
        ) {
            let (transaction_id, attempt_id) = ids();
            model
                .apply(Event::Accepted {
                    transaction_id,
                    attempt_id,
                })
                .map_err(|_| Error::State)?;
        }
        if self.record.phase == DurablePhase::Rejected {
            let (transaction_id, attempt_id) = ids();
            model
                .apply(Event::Rejected {
                    transaction_id,
                    attempt_id,
                })
                .map_err(|_| Error::State)?;
        }
        if self.record.phase == DurablePhase::PartiallyAccepted {
            let (transaction_id, attempt_id) = ids();
            model
                .apply(Event::PartiallyAccepted {
                    transaction_id,
                    attempt_id,
                })
                .map_err(|_| Error::State)?;
        }
        if self.record.phase == DurablePhase::Cancelled {
            model.apply(Event::Cancel).map_err(|_| Error::State)?;
        }
        if matches!(
            self.record.phase,
            DurablePhase::Committed | DurablePhase::Conflicted
        ) {
            let cas = self.record.cas.as_ref().ok_or(Error::State)?;
            require(cas.identity == *identity, Error::Identity)?;
            require(
                cas.committed == (self.record.phase == DurablePhase::Committed),
                Error::Identity,
            )?;
            let (transaction_id, attempt_id) = ids();
            let event = if cas.committed {
                Event::CasCommitted {
                    transaction_id,
                    attempt_id,
                    base_revision: identity.base_revision.clone(),
                    revision: cas.revision.clone(),
                }
            } else {
                Event::CasConflict {
                    transaction_id,
                    attempt_id,
                    base_revision: identity.base_revision.clone(),
                    revision: cas.revision.clone(),
                }
            };
            model.apply(event).map_err(|_| Error::State)?;
        }
        Ok(model)
    }
    fn notify(&self, runtime: &mut host::Runtime, event: &str) -> Result<bool> {
        runtime
            .notify(host::Notice {
                abi_version: 1,
                event: event.into(),
                attempt_id: self.record.identity.attempt_id.clone(),
                transaction_id: self.record.identity.transaction_id.clone(),
            })
            .map_err(|_| Error::State)
    }
    async fn persist(&mut self, store: &impl JournalStore) -> Result<()> {
        let digest = hash(&self.record.private_bytes()?);
        let previous = self.store_revision;
        let ack = store
            .persist(&self.record, previous)
            .await
            .map_err(|_| Error::Persistence)?;
        require(
            ack.identity == self.record.identity
                && ack.record_sha256 == digest
                && ack.revision > 0
                && previous.is_none_or(|old| {
                    ack.revision == old || old.checked_add(1) == Some(ack.revision)
                }),
            Error::Identity,
        )?;
        self.store_revision = Some(ack.revision);
        Ok(())
    }
    /// Before retry, restore a host runtime with the same prepared reads/writes and replay
    /// notifications. A changed journal is rejected even when attempt/transaction IDs match.
    pub fn restore_runtime(&self, runtime: &mut host::Runtime) -> Result<()> {
        self.notify(runtime, "bind")?;
        require(
            runtime.private_journal().map_err(|_| Error::State)?
                == serde_json::from_slice::<serde_json::Value>(&self.record.journal)
                    .map_err(|_| Error::Identity)?,
            Error::Identity,
        )?;
        if self.record.phase != DurablePhase::Prepared
            && self.record.phase != DurablePhase::Cancelled
        {
            self.notify(runtime, "persisted")?;
        }
        if matches!(
            self.record.phase,
            DurablePhase::Submitted
                | DurablePhase::Uncertain
                | DurablePhase::Accepted
                | DurablePhase::PartiallyAccepted
                | DurablePhase::Committed
                | DurablePhase::Conflicted
                | DurablePhase::Rejected
        ) {
            self.notify(runtime, "submitted")?;
        }
        if self.record.phase == DurablePhase::Uncertain {
            self.notify(runtime, "uncertain")?;
        }
        if matches!(
            self.record.phase,
            DurablePhase::Accepted | DurablePhase::Committed | DurablePhase::Conflicted
        ) {
            self.notify(runtime, "accepted")?;
        }
        if self.record.phase == DurablePhase::Rejected {
            self.notify(runtime, "rejected")?;
        }
        if self.record.phase == DurablePhase::PartiallyAccepted {
            self.notify(runtime, "partially_accepted")?;
        }
        if self.record.phase == DurablePhase::Cancelled {
            runtime.cancel().map_err(|_| Error::State)?;
        }
        Ok(())
    }
    pub async fn submit_once(
        &mut self,
        runtime: &mut host::Runtime,
        chain: &impl ChainAdapter,
        store: &impl JournalStore,
    ) -> Result<Submission> {
        self.check_runtime_identity(runtime)?;
        require(
            matches!(
                self.phase()?,
                Phase::Prepared | Phase::Submitted | Phase::Uncertain
            ),
            Error::State,
        )?;
        let snapshot = chain.snapshot().await.map_err(|_| Error::Network)?;
        snapshot.validate(&self.record.bound.policy)?;
        if self.record.phase == DurablePhase::Prepared {
            self.record.phase = DurablePhase::Persisted;
        }
        self.persist(store).await?;
        self.notify(runtime, "persisted")?;
        self.record.phase = DurablePhase::Submitted;
        // A crash after this durable write is an unknown broadcast outcome. Recovery only
        // retransmits these exact bytes, never reconstructs a new funded transaction.
        self.persist(store).await?;
        self.notify(runtime, "submitted")?;
        let outcome = chain
            .submit(&self.transaction())
            .await
            .unwrap_or(Submission::Uncertain);
        match outcome {
            Submission::Broadcast => {}
            Submission::Rejected => {
                self.record.phase = DurablePhase::Rejected;
                self.notify(runtime, "rejected")?;
            }
            Submission::Uncertain => {
                self.record.phase = DurablePhase::Uncertain;
                self.notify(runtime, "uncertain")?;
            }
        }
        self.persist(store).await?;
        Ok(outcome)
    }
    pub async fn observe_once(
        &mut self,
        runtime: &mut host::Runtime,
        chain: &impl ChainAdapter,
        store: &impl JournalStore,
    ) -> Result<Option<ObservedReceipt>> {
        self.check_runtime_identity(runtime)?;
        if let Some(receipt) = self.record.partial_receipt.clone() {
            // Retry the durable acknowledgement after an interrupted observation.
            self.persist(store).await?;
            self.notify(runtime, "partially_accepted")?;
            return Ok(Some(ObservedReceipt::Partial(receipt)));
        }
        let phase = self.phase()?;
        require(
            matches!(
                phase,
                Phase::Submitted
                    | Phase::Uncertain
                    | Phase::AwaitingCas
                    | Phase::Committed
                    | Phase::Conflicted
            ),
            Error::State,
        )?;
        match chain
            .observe(&self.transaction())
            .await
            .map_err(|_| Error::Uncertain)?
        {
            Observation::Pending => Ok(None),
            Observation::Rejected => {
                require(
                    matches!(phase, Phase::Submitted | Phase::Uncertain),
                    Error::Receipt,
                )?;
                self.record.phase = DurablePhase::Rejected;
                self.notify(runtime, "rejected")?;
                self.persist(store).await?;
                Err(Error::Rejected)
            }
            Observation::Finalized(receipt) => {
                self.transaction().check_receipt(&receipt)?;
                self.observed = true;
                if !matches!(phase, Phase::Committed | Phase::Conflicted) {
                    self.record.phase = DurablePhase::Accepted;
                    self.notify(runtime, "accepted")?;
                    self.persist(store).await?;
                }
                Ok(Some(ObservedReceipt::Full(receipt)))
            }
            Observation::Partial(receipt) => {
                require(
                    matches!(phase, Phase::Submitted | Phase::Uncertain),
                    Error::Receipt,
                )?;
                self.transaction().check_partial_receipt(&receipt)?;
                self.record.phase = DurablePhase::PartiallyAccepted;
                self.record.partial_receipt = Some(receipt.clone());
                self.persist(store).await?;
                self.notify(runtime, "partially_accepted")?;
                Ok(Some(ObservedReceipt::Partial(receipt)))
            }
        }
    }
    pub async fn commit_private(
        &mut self,
        runtime: &mut host::Runtime,
        store: &impl JournalStore,
        request_id: u64,
    ) -> Result<CasReceipt> {
        require(
            matches!(
                self.phase()?,
                Phase::AwaitingCas | Phase::Committed | Phase::Conflicted
            ),
            Error::State,
        )?;
        self.check_runtime_identity(runtime)?;
        require(self.observed, Error::Receipt)?;
        if matches!(self.phase()?, Phase::Committed | Phase::Conflicted) {
            let receipt = self.record.cas.as_ref().ok_or(Error::State)?.clone();
            self.persist(store).await?;
            if !runtime.matches_cas(receipt.committed, &receipt.revision) {
                self.preflight_runtime_cas(runtime, request_id)?;
                self.runtime_cas(runtime, &receipt, request_id)?;
            }
            return Ok(receipt);
        }
        self.preflight_runtime_cas(runtime, request_id)?;
        // Check the current durable revision before an external private-state mutation.
        self.persist(store).await?;
        let receipt = store
            .compare_exchange(&self.record)
            .await
            .map_err(|_| Error::Persistence)?;
        require(receipt.identity == self.record.identity, Error::Identity)?;
        let mut model = self.model()?;
        let id = &receipt.identity;
        let event = if receipt.committed {
            Event::CasCommitted {
                transaction_id: id.transaction_id.clone(),
                attempt_id: id.attempt_id.clone(),
                base_revision: id.base_revision.clone(),
                revision: receipt.revision.clone(),
            }
        } else {
            Event::CasConflict {
                transaction_id: id.transaction_id.clone(),
                attempt_id: id.attempt_id.clone(),
                base_revision: id.base_revision.clone(),
                revision: receipt.revision.clone(),
            }
        };
        model.apply(event).map_err(|_| Error::Identity)?;
        self.record.phase = if receipt.committed {
            DurablePhase::Committed
        } else {
            DurablePhase::Conflicted
        };
        self.record.cas = Some(receipt.clone());
        // The store's CAS atomically retains its idempotency receipt with private writes.
        // Retain that validated receipt durably before the fallible runtime acknowledgement.
        self.persist(store).await?;
        self.runtime_cas(runtime, &receipt, request_id)?;
        Ok(receipt)
    }
    fn check_runtime_identity(&self, runtime: &host::Runtime) -> Result<()> {
        let id = &self.record.identity;
        require(
            runtime.matches_journal(
                &id.attempt_id,
                &id.transaction_id,
                &id.base_revision,
                &self.record.bound.contract_address,
                &id.journal_digest,
            ),
            Error::Identity,
        )
    }
    fn preflight_runtime_cas(&self, runtime: &mut host::Runtime, request_id: u64) -> Result<()> {
        self.check_runtime_identity(runtime)?;
        require(
            runtime.public_status()["phase"] == "awaiting_cas",
            Error::State,
        )?;
        require(
            runtime.private_journal().map_err(|_| Error::State)?
                == serde_json::from_slice::<serde_json::Value>(&self.record.journal)
                    .map_err(|_| Error::Identity)?,
            Error::Identity,
        )?;
        runtime.begin_cas(request_id).map_err(|_| Error::State)?;
        let metadata = runtime.cas_metadata().ok_or(Error::State)?;
        require(
            metadata["id"].as_u64() == Some(request_id)
                && metadata["operation"] == host::CAS
                && metadata["schema"] == host::CAS_SCHEMA
                && metadata["capability"].as_str().is_some(),
            Error::Identity,
        )
    }
    fn runtime_cas(
        &self,
        runtime: &mut host::Runtime,
        receipt: &CasReceipt,
        request_id: u64,
    ) -> Result<()> {
        let id = &receipt.identity;
        runtime.begin_cas(request_id).map_err(|_| Error::State)?;
        let metadata = runtime.cas_metadata().ok_or(Error::State)?;
        require(metadata["id"].as_u64() == Some(request_id), Error::Identity)?;
        runtime.finish_cas(request_id, Some(host::CAS), metadata["capability"].as_str(), Some(host::CAS_SCHEMA), serde_json::json!({"attemptId":id.attempt_id,"transactionId":id.transaction_id,"baseRevision":id.base_revision,"journalDigest":id.journal_digest,"revision":receipt.revision,"outcome":if receipt.committed {"committed"} else {"conflict"}})).map_err(|_| Error::Identity)
    }
    pub async fn cancel(
        &mut self,
        runtime: &mut host::Runtime,
        store: &impl JournalStore,
    ) -> Result<()> {
        self.check_runtime_identity(runtime)?;
        self.model()?
            .apply(Event::Cancel)
            .map_err(|_| Error::CancellationAfterBroadcast)?;
        runtime.cancel().map_err(|_| Error::State)?;
        self.record.phase = DurablePhase::Cancelled;
        self.persist(store).await
    }
    pub async fn deadline(
        &mut self,
        runtime: &mut host::Runtime,
        store: &impl JournalStore,
    ) -> Result<()> {
        self.check_runtime_identity(runtime)?;
        match self.phase()? {
            Phase::Prepared => {
                self.cancel(runtime, store).await?;
            }
            Phase::Submitted | Phase::Uncertain => {
                self.record.phase = DurablePhase::Uncertain;
                self.notify(runtime, "uncertain")?;
                self.persist(store).await?;
            }
            _ => {}
        }
        Err(Error::Deadline)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use base_crypto::{hash::HashOutput, time::Timestamp};
    use futures::executor::block_on;
    use ledger::structure::ContractDeploy;
    use onchain_runtime::state::ContractState;
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use std::{
        cell::{Cell, RefCell},
        collections::BTreeMap,
    };
    use storage::arena::Sp;

    fn policy() -> NetworkPolicy {
        NetworkPolicy {
            network_id: "undeployed".into(),
            genesis: "1".repeat(64),
            spec_version: 2001100,
            transaction_version: 4,
            profile: crate::profile::NAME.into(),
            max_dust: 10u128.pow(18),
        }
    }
    fn chain_identity() -> ChainIdentity {
        let p = policy();
        ChainIdentity {
            network_id: p.network_id,
            genesis: p.genesis,
            spec_version: p.spec_version,
            transaction_version: p.transaction_version,
            profile: p.profile,
        }
    }
    // A real native deployment encoding supports lifecycle tests. Acceptance here is a
    // controlled host report, supplemented by the opt-in real-node integration test.
    fn bound() -> BoundTransaction {
        let mut rng = StdRng::from_seed([7; 32]);
        let deploy = ContractDeploy {
            initial_state: ContractState::<Db>::default(),
            nonce: HashOutput([3; 32]),
        };
        let address = hex::encode(deploy.address().0.0);
        let contract: ProvedNativeIntent = Intent {
            actions: vec![ContractAction::Deploy(Sp::new(deploy))].into(),
            guaranteed_unshielded_offer: None,
            fallible_unshielded_offer: None,
            dust_actions: None,
            binding_commitment: rng.r#gen(),
            ttl: Timestamp::from_secs(2_000_000_000),
        };
        let sealed = crate::funding::one_intent("undeployed", CONTRACT_SEGMENT, contract).seal(rng);
        let Transaction::Standard(stx) = &sealed else {
            unreachable!()
        };
        let intent_id = hex::encode(
            stx.intents
                .get(&CONTRACT_SEGMENT)
                .unwrap()
                .erase_proofs()
                .erase_signatures()
                .intent_hash(CONTRACT_SEGMENT)
                .0
                .0,
        );
        BoundTransaction {
            data: BoundData {
                policy: policy(),
                transaction_id: hex::encode(sealed.transaction_hash().0.0),
                transaction: encode(&sealed).unwrap(),
                intent_id,
                contract_address: address,
                event: ContractEvent::Deploy,
                expected_state: vec![1, 2, 3],
                checkpoint: None,
                call_counts: BTreeMap::new(),
                secondary_states: BTreeMap::new(),
                after_height: 20,
            },
        }
    }
    fn runtime(attempt: char, address: &str, value: &str) -> host::Runtime {
        let context = serde_json::from_value(serde_json::json!({"protocolVersion":1,"namespace":"test","baseRevision":"r0","attemptId":attempt.to_string().repeat(64),"capabilities":[{"id":"store","namespace":"test","keyPrefix":"claims/","operations":[host::STAGE,host::CAS]}],"operations":[],"providers":[],"commitCapability":"store"})).unwrap();
        let mut runtime =
            host::Runtime::new(context, &BTreeMap::new(), address.into(), "claim".into()).unwrap();
        runtime
            .stage(host::Stage {
                abi_version: 1,
                operation: host::STAGE.into(),
                capability: "store".into(),
                key: "claims/used".into(),
                ty: "Native".into(),
                value: serde_json::json!(value),
            })
            .unwrap();
        runtime.execution_finished(true).unwrap();
        runtime
    }
    pub(crate) fn prepared_driver_fixture() -> (SubmissionAttempt, host::Runtime) {
        let bound = bound();
        let mut runtime = runtime('a', bound.contract_address(), "11");
        let attempt = SubmissionAttempt::new(bound, &"a".repeat(64), &mut runtime).unwrap();
        (attempt, runtime)
    }
    struct FakeChain {
        identity: RefCell<ChainIdentity>,
        submission: Cell<Submission>,
        sent: RefCell<Vec<Vec<u8>>>,
        partial: RefCell<Option<PartialReceipt>>,
    }
    impl FakeChain {
        fn new() -> Self {
            Self {
                identity: RefCell::new(chain_identity()),
                submission: Cell::new(Submission::Uncertain),
                sent: RefCell::new(Vec::new()),
                partial: RefCell::new(None),
            }
        }
    }
    fn receipt(tx: &BoundTransaction) -> FinalizedReceipt {
        FinalizedReceipt {
            chain: chain_identity(),
            block_hash: "2".repeat(64),
            height: 21,
            finalized_hash: "3".repeat(64),
            finalized_height: 22,
            extrinsic_hash: "4".repeat(64),
            extrinsic_index: 2,
            transaction_id: tx.transaction_id().into(),
            intent_id: tx.intent_id().into(),
            contract_address: tx.contract_address().into(),
            event: tx.event(),
            contract_state: tx.expected_state().to_vec(),
            secondary_states: tx.secondary_states().clone(),
        }
    }
    impl ChainAdapter for FakeChain {
        async fn snapshot(&self) -> std::result::Result<Snapshot, HostFailure> {
            Ok(Snapshot {
                chain: self.identity.borrow().clone(),
                finalized_hash: "2".repeat(64),
                height: 20,
                state: LedgerState::new("undeployed"),
                block: BlockContext::default(),
            })
        }
        async fn submit(
            &self,
            tx: &BoundTransaction,
        ) -> std::result::Result<Submission, HostFailure> {
            self.sent.borrow_mut().push(tx.bytes().to_vec());
            Ok(self.submission.get())
        }
        async fn observe(
            &self,
            tx: &BoundTransaction,
        ) -> std::result::Result<Observation, HostFailure> {
            Ok(self
                .partial
                .borrow()
                .clone()
                .map(Observation::Partial)
                .unwrap_or_else(|| Observation::Finalized(receipt(tx))))
        }
    }
    #[derive(Default)]
    struct MemoryStore {
        bodies: RefCell<BTreeMap<String, String>>,
        saved: RefCell<BTreeMap<String, Vec<u8>>>,
        receipts: RefCell<BTreeMap<String, CasReceipt>>,
        revision: Cell<u64>,
        applies: Cell<usize>,
        versions: RefCell<BTreeMap<String, u64>>,
        hashes: RefCell<BTreeMap<String, String>>,
        cas_calls: Cell<usize>,
        fail_committed_persist: Cell<bool>,
    }
    impl JournalStore for MemoryStore {
        async fn load(&self, attempt_id: &str) -> std::result::Result<StoredRecord, HostFailure> {
            let saved = self.saved.borrow();
            let bytes = saved.get(attempt_id).ok_or(HostFailure)?;
            if self.hashes.borrow().get(attempt_id) != Some(&hash(bytes)) {
                return Err(HostFailure);
            }
            Ok(StoredRecord {
                private_bytes: Zeroizing::new(bytes.clone()),
                revision: *self.versions.borrow().get(attempt_id).ok_or(HostFailure)?,
            })
        }
        async fn persist(
            &self,
            record: &RecoveryRecord,
            expected_revision: Option<u64>,
        ) -> std::result::Result<StoreAcknowledgement, HostFailure> {
            if record.phase == DurablePhase::Committed && self.fail_committed_persist.replace(false)
            {
                return Err(HostFailure);
            }
            let digest = record.immutable_digest().map_err(|_| HostFailure)?;
            let bytes = record.private_bytes().map_err(|_| HostFailure)?;
            let record_sha256 = hash(&bytes);
            let previous = self
                .versions
                .borrow()
                .get(&record.identity.attempt_id)
                .copied();
            if previous != expected_revision {
                return Err(HostFailure);
            }
            let mut bodies = self.bodies.borrow_mut();
            if let Some(old) = bodies.get(&record.identity.attempt_id) {
                if old != &digest {
                    return Err(HostFailure);
                }
            }
            bodies.insert(record.identity.attempt_id.clone(), digest);
            let unchanged =
                self.hashes.borrow().get(&record.identity.attempt_id) == Some(&record_sha256);
            let revision = if unchanged {
                previous.ok_or(HostFailure)?
            } else {
                previous.unwrap_or(0).checked_add(1).ok_or(HostFailure)?
            };
            self.saved
                .borrow_mut()
                .insert(record.identity.attempt_id.clone(), bytes.to_vec());
            self.versions
                .borrow_mut()
                .insert(record.identity.attempt_id.clone(), revision);
            self.hashes
                .borrow_mut()
                .insert(record.identity.attempt_id.clone(), record_sha256.clone());
            Ok(StoreAcknowledgement {
                identity: record.identity.clone(),
                record_sha256,
                revision,
            })
        }
        async fn compare_exchange(
            &self,
            record: &RecoveryRecord,
        ) -> std::result::Result<CasReceipt, HostFailure> {
            self.cas_calls.set(self.cas_calls.get() + 1);
            if let Some(old) = self.receipts.borrow().get(&record.identity.attempt_id) {
                if old.identity != record.identity {
                    return Err(HostFailure);
                }
                return Ok(old.clone());
            }
            let committed = record.identity.base_revision == format!("r{}", self.revision.get());
            if committed {
                self.revision.set(self.revision.get() + 1);
                self.applies.set(self.applies.get() + 1);
            }
            let receipt = CasReceipt {
                identity: record.identity.clone(),
                revision: format!("r{}", self.revision.get()),
                committed,
            };
            self.receipts
                .borrow_mut()
                .insert(record.identity.attempt_id.clone(), receipt.clone());
            Ok(receipt)
        }
    }
    #[test]
    fn receipt_identity_network_finality_and_exact_state_are_required() {
        let tx = bound();
        let good = receipt(&tx);
        tx.check_receipt(&good).unwrap();
        let mut wrong = good.clone();
        wrong.chain.genesis = "f".repeat(64);
        assert_eq!(tx.check_receipt(&wrong), Err(Error::Network));
        let mut wrong = good.clone();
        wrong.chain.profile = "other-profile".into();
        assert_eq!(tx.check_receipt(&wrong), Err(Error::Network));
        for mutate in [
            |r: &mut FinalizedReceipt| r.transaction_id = "f".repeat(64),
            |r: &mut FinalizedReceipt| r.intent_id = "f".repeat(64),
            |r: &mut FinalizedReceipt| r.contract_address = "f".repeat(64),
            |r: &mut FinalizedReceipt| r.event = ContractEvent::Call,
            |r: &mut FinalizedReceipt| r.contract_state.push(0),
            |r: &mut FinalizedReceipt| r.extrinsic_hash.clear(),
        ] {
            let mut wrong = good.clone();
            mutate(&mut wrong);
            assert_eq!(tx.check_receipt(&wrong), Err(Error::Receipt));
        }
        let mut wrong = good.clone();
        wrong.height = 20;
        assert_eq!(tx.check_receipt(&wrong), Err(Error::StaleReceipt));
        let mut wrong = good;
        wrong.finalized_height = 20;
        assert_eq!(tx.check_receipt(&wrong), Err(Error::StaleReceipt));

        let mut multi = tx;
        multi.data.event = ContractEvent::Call;
        let callee = "e".repeat(64);
        multi.data.call_counts = [(multi.contract_address().into(), 1), (callee.clone(), 1)].into();
        multi
            .data
            .secondary_states
            .insert(callee.clone(), vec![4, 5]);
        let mut composed = receipt(&multi);
        multi.check_receipt(&composed).unwrap();
        composed.secondary_states.remove(&callee);
        assert_eq!(multi.check_receipt(&composed), Err(Error::Receipt));
    }

    #[test]
    fn receipt_inclusion_and_finalization_hashes_match_their_heights() {
        let tx = bound();
        let mut receipt = receipt(&tx);

        // Inclusion at the finalized height identifies the finalized block.
        receipt.finalized_height = receipt.height;
        receipt.finalized_hash.clone_from(&receipt.block_hash);
        tx.check_receipt(&receipt).unwrap();

        // A later finalized head has a distinct block identity. The archived
        // composition fixture exercises this historical-receipt shape too.
        receipt.finalized_height += 1;
        receipt.finalized_hash = "3".repeat(64);
        tx.check_receipt(&receipt).unwrap();

        // Reject both inconsistent combinations.
        receipt.finalized_hash.clone_from(&receipt.block_hash);
        assert_eq!(tx.check_receipt(&receipt), Err(Error::Receipt));
        receipt.finalized_height = receipt.height;
        receipt.finalized_hash = "3".repeat(64);
        assert_eq!(tx.check_receipt(&receipt), Err(Error::Receipt));
    }
    #[test]
    fn partial_checkpoint_restores_receipt_and_staged_writes_without_resubmission_or_cas() {
        use ledger::structure::{ContractCall, ProofVersioned};
        use onchain_runtime::{state::EntryPointBuf, transcript::Transcript};
        use transient_crypto::{curve::Fr, proofs::Proof};

        block_on(async {
            let mut rng = StdRng::from_seed([7; 32]);
            let transcript = |program: Vec<_>| {
                Sp::new(Transcript {
                    gas: Default::default(),
                    effects: Default::default(),
                    program: program.into(),
                    version: None,
                })
            };
            let call = ContractCall {
                address: Default::default(),
                entry_point: EntryPointBuf(b"claim".to_vec()),
                guaranteed_transcript: Some(transcript(vec![Op::Ckpt])),
                fallible_transcript: Some(transcript(vec![Op::Ckpt])),
                communication_commitment: Fr::from(0u64),
                proof: ProofVersioned::V3(Proof(Vec::new())),
            };
            let contract = Intent {
                actions: vec![ContractAction::Call(Sp::new(call))].into(),
                guaranteed_unshielded_offer: None,
                fallible_unshielded_offer: None,
                dust_actions: None,
                binding_commitment: rng.r#gen(),
                ttl: Timestamp::from_secs(2_000_000_000),
            };
            let sealed =
                crate::funding::one_intent("undeployed", CONTRACT_SEGMENT, contract).seal(rng);
            let mut tx = PublicTransactionReference::from_bytes(
                policy(),
                &encode(&sealed).unwrap(),
                20,
                &[1, 2, 3],
            )
            .unwrap()
            .bound_view();
            let (_, entrypoint, segments) = checkpoint_call(&sealed).unwrap();
            let mut partial = PartialReceipt {
                receipt: receipt(&tx),
                entrypoint,
                segments,
            };
            partial.receipt.contract_state = vec![1, 2];
            tx.data.checkpoint = Some(CheckpointPrefix {
                entrypoint: partial.entrypoint.clone(),
                segments: partial.segments.clone(),
                state: partial.receipt.contract_state.clone(),
            });
            assert_eq!(tx.check_receipt(&partial.receipt), Err(Error::Receipt));
            tx.check_partial_receipt(&partial).unwrap();
            for alter in [
                |p: &mut PartialReceipt| p.receipt.transaction_id = "f".repeat(64),
                |p: &mut PartialReceipt| p.receipt.contract_state.push(3),
                |p: &mut PartialReceipt| p.entrypoint.push(0),
                |p: &mut PartialReceipt| {
                    p.segments.insert(CONTRACT_SEGMENT, true);
                },
            ] {
                let mut wrong = partial.clone();
                alter(&mut wrong);
                assert_eq!(tx.check_partial_receipt(&wrong), Err(Error::Receipt));
            }
            let address = tx.contract_address().to_owned();
            let id = "a".repeat(64);
            let mut staged = runtime('a', &address, "42");
            let mut attempt = SubmissionAttempt::new(tx, &id, &mut staged).unwrap();
            let chain = FakeChain::new();
            let store = MemoryStore::default();
            attempt
                .submit_once(&mut staged, &chain, &store)
                .await
                .unwrap();
            chain.partial.replace(Some(partial));
            assert!(matches!(
                attempt
                    .observe_once(&mut staged, &chain, &store)
                    .await
                    .unwrap(),
                Some(ObservedReceipt::Partial(_))
            ));
            assert_eq!(staged.public_status()["phase"], "partially_accepted");
            drop(attempt);
            let mut recovered = SubmissionAttempt::recover(&store, &id).await.unwrap();
            let mut restored = runtime('a', &address, "42");
            recovered.restore_runtime(&mut restored).unwrap();
            assert_eq!(recovered.phase().unwrap(), Phase::PartiallyAccepted);
            assert_eq!(
                restored.private_journal().unwrap()["writes"]["claims/used"]["value"],
                "42"
            );
            chain.partial.replace(None);
            assert!(matches!(
                recovered
                    .observe_once(&mut restored, &chain, &store)
                    .await
                    .unwrap(),
                Some(ObservedReceipt::Partial(_))
            ));
            assert_eq!(
                recovered.submit_once(&mut restored, &chain, &store).await,
                Err(Error::State)
            );
            assert_eq!(
                recovered
                    .commit_private(&mut restored, &store, 1)
                    .await
                    .err(),
                Some(Error::State)
            );
            assert_eq!(chain.sent.borrow().len(), 1);
            assert_eq!(store.cas_calls.get(), 0);
        });
    }
    #[test]
    fn uncertain_restart_retries_exact_bytes_and_deduplicates_private_cas() {
        block_on(async {
            let tx = bound();
            let address = tx.contract_address().to_owned();
            let mut runtime = runtime('a', &address, "42");
            let mut attempt = SubmissionAttempt::new(tx, &"a".repeat(64), &mut runtime).unwrap();
            let chain = FakeChain::new();
            let store = MemoryStore::default();
            assert_eq!(
                attempt
                    .submit_once(&mut runtime, &chain, &store)
                    .await
                    .unwrap(),
                Submission::Uncertain
            );
            assert_eq!(attempt.phase().unwrap(), Phase::Uncertain);
            assert_eq!(
                attempt.cancel(&mut runtime, &store).await,
                Err(Error::CancellationAfterBroadcast)
            );
            assert_eq!(
                attempt.deadline(&mut runtime, &store).await,
                Err(Error::Deadline)
            );
            drop(attempt);
            drop(runtime);
            let mut recovered = SubmissionAttempt::recover(&store, &"a".repeat(64))
                .await
                .unwrap();
            let mut restored = self::runtime('a', &address, "42");
            recovered.restore_runtime(&mut restored).unwrap();
            chain.submission.set(Submission::Broadcast);
            recovered
                .submit_once(&mut restored, &chain, &store)
                .await
                .unwrap();
            assert_eq!(chain.sent.borrow().len(), 2);
            assert_eq!(chain.sent.borrow()[0], chain.sent.borrow()[1]);
            assert!(
                recovered
                    .observe_once(&mut restored, &chain, &store)
                    .await
                    .unwrap()
                    .is_some()
            );
            assert_eq!(store.applies.get(), 0);
            assert!(
                recovered
                    .commit_private(&mut restored, &store, 8)
                    .await
                    .unwrap()
                    .committed
            );
            assert!(
                recovered
                    .commit_private(&mut restored, &store, 8)
                    .await
                    .unwrap()
                    .committed
            );
            assert_eq!(store.applies.get(), 1);
            let mut recovered = SubmissionAttempt::recover(&store, &"a".repeat(64))
                .await
                .unwrap();
            let mut restored = self::runtime('a', &address, "42");
            recovered.restore_runtime(&mut restored).unwrap();
            assert_eq!(restored.public_status()["phase"], "awaiting_cas");
            recovered
                .observe_once(&mut restored, &chain, &store)
                .await
                .unwrap();
            recovered
                .commit_private(&mut restored, &store, 9)
                .await
                .unwrap();
            assert_eq!(restored.public_status()["phase"], "committed");
        });
    }
    #[test]
    fn chain_acceptance_and_private_storage_conflict_stay_distinct() {
        block_on(async {
            let store = MemoryStore::default();
            let chain = FakeChain::new();
            chain.submission.set(Submission::Broadcast);
            let first = bound();
            let address = first.contract_address().to_owned();
            let mut r1 = runtime('a', &address, "42");
            let mut a = SubmissionAttempt::new(first, &"a".repeat(64), &mut r1).unwrap();
            let mut r2 = runtime('b', &address, "43");
            let mut b = SubmissionAttempt::new(bound(), &"b".repeat(64), &mut r2).unwrap();
            for (attempt, runtime) in [(&mut a, &mut r1), (&mut b, &mut r2)] {
                attempt.submit_once(runtime, &chain, &store).await.unwrap();
                attempt.observe_once(runtime, &chain, &store).await.unwrap();
            }
            assert!(
                a.commit_private(&mut r1, &store, 1)
                    .await
                    .unwrap()
                    .committed
            );
            assert!(
                !b.commit_private(&mut r2, &store, 1)
                    .await
                    .unwrap()
                    .committed
            );
            assert_eq!(b.phase().unwrap(), Phase::Conflicted);
            assert_eq!(r2.public_status()["acceptedHostEvidence"], true);
            assert_eq!(store.applies.get(), 1);
        });
    }
    #[test]
    fn changed_journal_or_transaction_cannot_reuse_a_durable_attempt() {
        block_on(async {
            let tx = bound();
            let address = tx.contract_address().to_owned();
            let mut runtime = runtime('a', &address, "42");
            let mut attempt = SubmissionAttempt::new(tx, &"a".repeat(64), &mut runtime).unwrap();
            let chain = FakeChain::new();
            let store = MemoryStore::default();
            attempt
                .submit_once(&mut runtime, &chain, &store)
                .await
                .unwrap();
            let saved = attempt.record.private_bytes().unwrap();
            let mut value: serde_json::Value = serde_json::from_slice(&saved).unwrap();
            let mut journal: serde_json::Value =
                serde_json::from_slice(&attempt.record.journal).unwrap();
            journal["writes"]["claims/used"]["value"] = "43".into();
            value["journal"] = serde_json::to_value(serde_json::to_vec(&journal).unwrap()).unwrap();
            assert_eq!(
                SubmissionAttempt::decode_record(&serde_json::to_vec(&value).unwrap(), 1).err(),
                Some(Error::Identity)
            );
            let mut value: serde_json::Value = serde_json::from_slice(&saved).unwrap();
            value["bound"]["transaction"][10] = 255.into();
            assert!(
                SubmissionAttempt::decode_record(&serde_json::to_vec(&value).unwrap(), 1).is_err()
            );
            let mut other_runtime = self::runtime('a', &address, "43");
            let changed =
                SubmissionAttempt::new(bound(), &"a".repeat(64), &mut other_runtime).unwrap();
            assert!(store.persist(changed.record(), None).await.is_err());
            let mut restored = self::runtime('a', &address, "43");
            assert_eq!(attempt.restore_runtime(&mut restored), Err(Error::Identity));
        });
    }
    #[test]
    fn recovery_authenticates_complete_current_record_and_requires_new_finality() {
        block_on(async {
            let tx = bound();
            let address = tx.contract_address().to_owned();
            let mut runtime = runtime('a', &address, "42");
            let mut attempt = SubmissionAttempt::new(tx, &"a".repeat(64), &mut runtime).unwrap();
            let store = MemoryStore::default();
            let chain = FakeChain::new();
            attempt
                .submit_once(&mut runtime, &chain, &store)
                .await
                .unwrap();
            let saved = store.saved.borrow()[&"a".repeat(64)].clone();
            for field in ["phase", "expectedState", "afterHeight", "cas"] {
                let mut value: serde_json::Value = serde_json::from_slice(&saved).unwrap();
                match field {
                    "phase" => value["phase"] = "Accepted".into(),
                    "expectedState" => value["bound"]["expectedState"] = serde_json::json!([9]),
                    "afterHeight" => value["bound"]["afterHeight"] = 0.into(),
                    _ => {
                        value["phase"] = "Committed".into();
                        value["cas"] = serde_json::to_value(CasReceipt {
                            identity: attempt.record.identity.clone(),
                            revision: "r1".into(),
                            committed: true,
                        })
                        .unwrap();
                    }
                }
                store
                    .saved
                    .borrow_mut()
                    .insert("a".repeat(64), serde_json::to_vec(&value).unwrap());
                assert_eq!(
                    SubmissionAttempt::recover(&store, &"a".repeat(64))
                        .await
                        .err(),
                    Some(Error::Persistence)
                );
            }
            store
                .saved
                .borrow_mut()
                .insert("a".repeat(64), saved.clone());
            attempt
                .observe_once(&mut runtime, &chain, &store)
                .await
                .unwrap();
            let accepted = store.saved.borrow()[&"a".repeat(64)].clone();
            store.saved.borrow_mut().insert("a".repeat(64), saved);
            assert_eq!(
                SubmissionAttempt::recover(&store, &"a".repeat(64))
                    .await
                    .err(),
                Some(Error::Persistence)
            );
            store.saved.borrow_mut().insert("a".repeat(64), accepted);
            let mut recovered = SubmissionAttempt::recover(&store, &"a".repeat(64))
                .await
                .unwrap();
            let mut restored = self::runtime('a', &address, "42");
            recovered.restore_runtime(&mut restored).unwrap();
            assert_eq!(
                recovered
                    .commit_private(&mut restored, &store, 1)
                    .await
                    .err(),
                Some(Error::Receipt)
            );
            assert_eq!(store.cas_calls.get(), 0);
            recovered
                .observe_once(&mut restored, &chain, &store)
                .await
                .unwrap();
            recovered
                .commit_private(&mut restored, &store, 1)
                .await
                .unwrap();
            assert_eq!(store.applies.get(), 1);
        });
    }
    #[test]
    fn private_cas_preflights_runtime_journal_and_pending_request() {
        block_on(async {
            let tx = bound();
            let address = tx.contract_address().to_owned();
            let mut runtime = runtime('a', &address, "42");
            let mut attempt = SubmissionAttempt::new(tx, &"a".repeat(64), &mut runtime).unwrap();
            let store = MemoryStore::default();
            let chain = FakeChain::new();
            attempt
                .submit_once(&mut runtime, &chain, &store)
                .await
                .unwrap();
            attempt
                .observe_once(&mut runtime, &chain, &store)
                .await
                .unwrap();
            for (letter, value) in [('b', "42"), ('a', "43")] {
                let mut wrong = self::runtime(letter, &address, value);
                for event in ["bind", "persisted", "submitted", "accepted"] {
                    wrong
                        .notify(host::Notice {
                            abi_version: 1,
                            event: event.into(),
                            attempt_id: letter.to_string().repeat(64),
                            transaction_id: attempt.record.identity.transaction_id.clone(),
                        })
                        .unwrap();
                }
                assert_eq!(
                    attempt.commit_private(&mut wrong, &store, 1).await.err(),
                    Some(Error::Identity)
                );
            }
            let mut prepared = self::runtime('a', &address, "42");
            prepared
                .notify(host::Notice {
                    abi_version: 1,
                    event: "bind".into(),
                    attempt_id: "a".repeat(64),
                    transaction_id: attempt.record.identity.transaction_id.clone(),
                })
                .unwrap();
            assert_eq!(
                attempt.commit_private(&mut prepared, &store, 1).await.err(),
                Some(Error::State)
            );
            runtime.begin_cas(77).unwrap();
            assert_eq!(
                attempt.commit_private(&mut runtime, &store, 78).await.err(),
                Some(Error::Identity)
            );
            assert_eq!(store.cas_calls.get(), 0);
            assert_eq!(store.applies.get(), 0);
            attempt
                .commit_private(&mut runtime, &store, 77)
                .await
                .unwrap();
            assert_eq!(store.applies.get(), 1);
        });
    }
    #[test]
    fn stale_recovery_cannot_overwrite_terminal_record_or_rebroadcast() {
        block_on(async {
            let tx = bound();
            let address = tx.contract_address().to_owned();
            let mut runtime = runtime('a', &address, "42");
            let mut attempt = SubmissionAttempt::new(tx, &"a".repeat(64), &mut runtime).unwrap();
            let store = MemoryStore::default();
            let chain = FakeChain::new();
            attempt
                .submit_once(&mut runtime, &chain, &store)
                .await
                .unwrap();
            let mut a = SubmissionAttempt::recover(&store, &"a".repeat(64))
                .await
                .unwrap();
            let mut b = SubmissionAttempt::recover(&store, &"a".repeat(64))
                .await
                .unwrap();
            let mut ra = self::runtime('a', &address, "42");
            let mut rb = self::runtime('a', &address, "42");
            a.restore_runtime(&mut ra).unwrap();
            b.restore_runtime(&mut rb).unwrap();
            a.observe_once(&mut ra, &chain, &store).await.unwrap();
            a.commit_private(&mut ra, &store, 1).await.unwrap();
            let sent = chain.sent.borrow().len();
            assert_eq!(
                b.submit_once(&mut rb, &chain, &store).await.err(),
                Some(Error::Persistence)
            );
            assert_eq!(chain.sent.borrow().len(), sent);
            let latest = SubmissionAttempt::recover(&store, &"a".repeat(64))
                .await
                .unwrap();
            assert_eq!(latest.phase().unwrap(), Phase::Committed);
            assert_eq!(store.applies.get(), 1);
        });
    }
    #[test]
    fn restart_reconciles_private_cas_before_runtime_ack_without_second_apply() {
        block_on(async {
            let tx = bound();
            let address = tx.contract_address().to_owned();
            let mut runtime = runtime('a', &address, "42");
            let mut attempt = SubmissionAttempt::new(tx, &"a".repeat(64), &mut runtime).unwrap();
            let store = MemoryStore::default();
            let chain = FakeChain::new();
            attempt
                .submit_once(&mut runtime, &chain, &store)
                .await
                .unwrap();
            attempt
                .observe_once(&mut runtime, &chain, &store)
                .await
                .unwrap();
            store.fail_committed_persist.set(true);
            assert_eq!(
                attempt.commit_private(&mut runtime, &store, 1).await.err(),
                Some(Error::Persistence)
            );
            assert_eq!(runtime.public_status()["phase"], "awaiting_cas");
            assert_eq!(store.applies.get(), 1);
            let mut recovered = SubmissionAttempt::recover(&store, &"a".repeat(64))
                .await
                .unwrap();
            let mut restored = self::runtime('a', &address, "42");
            recovered.restore_runtime(&mut restored).unwrap();
            recovered
                .observe_once(&mut restored, &chain, &store)
                .await
                .unwrap();
            recovered
                .commit_private(&mut restored, &store, 1)
                .await
                .unwrap();
            assert_eq!(store.applies.get(), 1);
            assert_eq!(restored.public_status()["phase"], "committed");
        });
    }
    #[test]
    fn live_retry_persists_terminal_cas_receipt_before_runtime_ack() {
        block_on(async {
            let tx = bound();
            let address = tx.contract_address().to_owned();
            let mut runtime = runtime('a', &address, "42");
            let mut attempt = SubmissionAttempt::new(tx, &"a".repeat(64), &mut runtime).unwrap();
            let store = MemoryStore::default();
            let chain = FakeChain::new();
            attempt
                .submit_once(&mut runtime, &chain, &store)
                .await
                .unwrap();
            attempt
                .observe_once(&mut runtime, &chain, &store)
                .await
                .unwrap();
            store.fail_committed_persist.set(true);
            assert_eq!(
                attempt.commit_private(&mut runtime, &store, 1).await.err(),
                Some(Error::Persistence)
            );
            assert_eq!(runtime.public_status()["phase"], "awaiting_cas");
            assert_eq!(store.applies.get(), 1);
            attempt
                .commit_private(&mut runtime, &store, 1)
                .await
                .unwrap();
            let stored = SubmissionAttempt::recover(&store, &"a".repeat(64))
                .await
                .unwrap();
            assert_eq!(stored.phase().unwrap(), Phase::Committed);
            assert_eq!(runtime.public_status()["phase"], "committed");
            assert_eq!(store.applies.get(), 1);
            assert_eq!(store.cas_calls.get(), 1);
        });
    }
    #[cfg(feature = "localnet")]
    #[test]
    fn directory_journal_restart_stale_writer_conflict_and_private_permissions() {
        use crate::localnet::journal::DirectoryJournal;
        use std::time::Duration;
        let root = std::env::temp_dir().join(format!(
            "noctium-journal-test-{}-{}",
            std::process::id(),
            rand::random::<u64>()
        ));
        block_on(async {
            let store = DirectoryJournal::new(&root, Duration::from_millis(100)).unwrap();
            let other = DirectoryJournal::new(&root, Duration::from_millis(100)).unwrap();
            let chain = FakeChain::new();
            let tx = bound();
            let address = tx.contract_address().to_owned();
            let mut ra = runtime('a', &address, "42");
            let mut a = SubmissionAttempt::new(tx, &"a".repeat(64), &mut ra).unwrap();
            a.submit_once(&mut ra, &chain, &store).await.unwrap();
            let mut stale = SubmissionAttempt::recover(&other, &"a".repeat(64))
                .await
                .unwrap();
            let mut rs = runtime('a', &address, "42");
            stale.restore_runtime(&mut rs).unwrap();
            a.observe_once(&mut ra, &chain, &store).await.unwrap();
            let cas = a.commit_private(&mut ra, &store, 1).await.unwrap();
            assert!(cas.committed);
            assert_eq!(other.revision("test").unwrap(), "r1");
            assert_eq!(
                other.private_value("test", "claims/used").unwrap().unwrap()["value"],
                "42"
            );
            let sent = chain.sent.borrow().len();
            assert_eq!(
                stale.submit_once(&mut rs, &chain, &other).await.err(),
                Some(Error::Persistence)
            );
            assert_eq!(chain.sent.borrow().len(), sent);
            drop((store, other));
            let store = DirectoryJournal::new(&root, Duration::from_millis(100)).unwrap();
            let mut a = SubmissionAttempt::recover(&store, &"a".repeat(64))
                .await
                .unwrap();
            let mut ra = runtime('a', &address, "42");
            a.restore_runtime(&mut ra).unwrap();
            assert_eq!(
                a.commit_private(&mut ra, &store, 2).await.err(),
                Some(Error::Receipt)
            );
            a.observe_once(&mut ra, &chain, &store).await.unwrap();
            assert!(
                a.commit_private(&mut ra, &store, 2)
                    .await
                    .unwrap()
                    .committed
            );
            assert_eq!(store.revision("test").unwrap(), "r1");
            let mut rb = runtime('b', &address, "43");
            let mut b = SubmissionAttempt::new(bound(), &"b".repeat(64), &mut rb).unwrap();
            b.submit_once(&mut rb, &chain, &store).await.unwrap();
            b.observe_once(&mut rb, &chain, &store).await.unwrap();
            assert!(
                !b.commit_private(&mut rb, &store, 3)
                    .await
                    .unwrap()
                    .committed
            );
            assert_eq!(
                store.private_value("test", "claims/used").unwrap().unwrap()["value"],
                "42"
            );
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                assert_eq!(
                    std::fs::metadata(&root).unwrap().permissions().mode() & 0o777,
                    0o700
                );
                assert_eq!(
                    std::fs::metadata(root.join("state.json"))
                        .unwrap()
                        .permissions()
                        .mode()
                        & 0o777,
                    0o600
                );
            }
            // The host directory authenticates the current record. Corruption is rejected,
            // without treating a self-hash from imported caller bytes as authentication.
            let mut state: serde_json::Value =
                serde_json::from_slice(&std::fs::read(root.join("state.json")).unwrap()).unwrap();
            state["attempts"][&"a".repeat(64)]["bytes"][0] = serde_json::json!(0);
            std::fs::write(root.join("state.json"), serde_json::to_vec(&state).unwrap()).unwrap();
            assert_eq!(
                SubmissionAttempt::recover(&store, &"a".repeat(64))
                    .await
                    .err(),
                Some(Error::Persistence)
            );
        });
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn lost_acknowledgement_then_unfinalized_pool_refusal_retains_journal() {
        block_on(async {
            let tx = bound();
            let address = tx.contract_address().to_owned();
            let mut runtime = runtime('a', &address, "42");
            let mut attempt = SubmissionAttempt::new(tx, &"a".repeat(64), &mut runtime).unwrap();
            let store = MemoryStore::default();
            let chain = FakeChain::new();
            assert_eq!(
                attempt
                    .submit_once(&mut runtime, &chain, &store)
                    .await
                    .unwrap(),
                Submission::Uncertain
            );
            // The first transaction may already be included at an unfinalized best head.
            // A subsequent stale/banned/replaced pool response is still uncertain.
            assert_eq!(
                attempt
                    .submit_once(&mut runtime, &chain, &store)
                    .await
                    .unwrap(),
                Submission::Uncertain
            );
            assert_eq!(attempt.phase().unwrap(), Phase::Uncertain);
            assert_eq!(
                runtime.private_journal().unwrap()["writes"]["claims/used"]["value"],
                "42"
            );
            assert!(
                attempt
                    .commit_private(&mut runtime, &store, 1)
                    .await
                    .is_err()
            );
            assert_eq!(store.cas_calls.get(), 0);
            assert_eq!(store.applies.get(), 0);
            assert_eq!(
                attempt.cancel(&mut runtime, &store).await,
                Err(Error::CancellationAfterBroadcast)
            );
            attempt
                .observe_once(&mut runtime, &chain, &store)
                .await
                .unwrap()
                .unwrap();
            assert!(
                attempt
                    .commit_private(&mut runtime, &store, 1)
                    .await
                    .unwrap()
                    .committed
            );
            assert_eq!(store.applies.get(), 1);
        });
    }
    #[test]
    fn unrelated_runtime_never_loses_writes_or_broadcasts_on_cancel_or_deadline() {
        block_on(async {
            let tx = bound();
            let address = tx.contract_address().to_owned();
            let mut ra = runtime('a', &address, "42");
            let mut a = SubmissionAttempt::new(tx, &"a".repeat(64), &mut ra).unwrap();
            let mut rb = runtime('b', &address, "43");
            let _b = SubmissionAttempt::new(bound(), &"b".repeat(64), &mut rb).unwrap();
            let store = MemoryStore::default();
            let chain = FakeChain::new();
            assert_eq!(a.cancel(&mut rb, &store).await, Err(Error::Identity));
            assert_eq!(a.deadline(&mut rb, &store).await, Err(Error::Identity));
            assert_eq!(
                a.submit_once(&mut rb, &chain, &store).await.err(),
                Some(Error::Identity)
            );
            assert_eq!(
                a.observe_once(&mut rb, &chain, &store).await.err(),
                Some(Error::Identity)
            );
            assert_eq!(
                rb.private_journal().unwrap()["writes"]["claims/used"]["value"],
                "43"
            );
            assert_eq!(rb.public_status()["phase"], "prepared");
            assert!(store.saved.borrow().is_empty());
            assert!(chain.sent.borrow().is_empty());
            a.cancel(&mut ra, &store).await.unwrap();
            assert_eq!(ra.public_status()["phase"], "cancelled");
            assert_eq!(rb.public_status()["phase"], "prepared");
        });
    }
    #[test]
    fn public_reference_derives_native_identity_and_checks_deployment_state() {
        let bound = bound();
        let native: SealedTransaction = tagged_deserialize(bound.bytes()).unwrap();
        let Transaction::Standard(stx) = &native else {
            panic!("standard")
        };
        let intent = stx.intents.get(&CONTRACT_SEGMENT).unwrap();
        let Some(ContractAction::Deploy(deploy)) = intent.actions.iter_deref().next() else {
            panic!("deploy")
        };
        let state = encode(&deploy.initial_state).unwrap();
        let reference =
            PublicTransactionReference::from_bytes(policy(), bound.bytes(), 20, &state).unwrap();
        assert_eq!(reference.transaction_id(), bound.transaction_id());
        assert_eq!(reference.contract_address(), bound.contract_address());
        assert_eq!(reference.event(), ContractEvent::Deploy);
        let mut receipt = receipt(&bound);
        receipt.height = 21;
        receipt.finalized_height = 21;
        receipt.finalized_hash.clone_from(&receipt.block_hash);
        receipt.contract_state.clone_from(&state);
        reference.check_receipt(&receipt).unwrap();
        receipt.secondary_states.insert("f".repeat(64), vec![9]);
        assert_eq!(reference.check_receipt(&receipt), Err(Error::Receipt));
        #[cfg(feature = "localnet")]
        assert!(reference.development_submission_view().is_ok());
        assert!(
            PublicTransactionReference::from_bytes(policy(), bound.bytes(), 20, &[1, 2, 3])
                .is_err()
        );
        let mut trailing = bound.bytes().to_vec();
        trailing.push(0);
        assert!(PublicTransactionReference::from_bytes(policy(), &trailing, 20, &state).is_err());
        assert!(
            PublicTransactionReference::from_bytes(policy(), bound.bytes(), u64::MAX, &state)
                .is_err()
        );
        let mut wrong = policy();
        wrong.network_id = "other".into();
        assert!(PublicTransactionReference::from_bytes(wrong, bound.bytes(), 20, &state).is_err());
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    fn public_composed_reference_checks_two_ordered_calls_and_exact_receipt_state() {
        let transaction =
            include_bytes!("../tests/fixtures/public-composition-30432/transaction.bin");
        let caller_state =
            include_bytes!("../tests/fixtures/public-composition-30432/caller.state");
        let callee_state =
            include_bytes!("../tests/fixtures/public-composition-30432/callee.state");
        let caller =
            hex::decode("a0cc5e863a975944bf82548438bf527cdeb95c33eba83a7af1230f31e1025695")
                .unwrap();
        let callee =
            hex::decode("50896ca2fa4858b4d0119751331d464e7f44960980b78f24fd4c1575d9d6b41a")
                .unwrap();
        assert_eq!(
            hash(caller_state),
            "d3c2f809b7c6a6fd56ad7e9e1ff5d1979e0f94a9cc30f1d63d3087ef63e09cbf"
        );
        assert_eq!(
            hash(callee_state),
            "96c73b9b42978a0411a12a16846d5c1ae6fb5ac544472f0843c29e2e37493bc0"
        );
        let fixture_policy = || {
            let mut p = policy();
            p.genesis = "823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d".into();
            p
        };
        let expected = [
            (caller.as_slice(), &b"claim"[..], caller_state.as_slice()),
            (callee.as_slice(), &b"advance"[..], callee_state.as_slice()),
        ];
        let reference = PublicTransactionReference::from_composed_calls(
            fixture_policy(),
            transaction,
            30_431,
            expected,
        )
        .unwrap();
        assert_eq!(
            reference.transaction_id(),
            "44da763bbde860dd6057062ee1a7e6e86f9c751ceede1a651bee2de31e7b8583"
        );
        assert_eq!(
            reference.contract_address(),
            "a0cc5e863a975944bf82548438bf527cdeb95c33eba83a7af1230f31e1025695"
        );
        assert_eq!(
            reference.bound_view().contract_event_counts(),
            [(hex::encode(&caller), 1), (hex::encode(&callee), 1),].into()
        );

        let mut chain = chain_identity();
        chain.genesis = fixture_policy().genesis;
        let receipt = FinalizedReceipt {
            chain,
            block_hash: "e879cd9d45a6889fb7b983ecac8550b7893573b4f63ff999abb39f5eb37ce94b".into(),
            height: 30_432,
            finalized_hash: "9b6ef59f11322bf0794e09d837b47d60e40d6f182e85224d9b55b8021d295ae2"
                .into(),
            finalized_height: 54_286,
            extrinsic_hash: "cd6999fc7ec8fbd6a691f8a7ef3311441f278df1c0e20b019a6da89e3ff8bea8"
                .into(),
            extrinsic_index: 4,
            transaction_id: reference.transaction_id().into(),
            intent_id: "7335e29a2900ed4191e8d052d9ab0c88cfe970d759822c5e3ad6caec59c2c4d5".into(),
            contract_address: hex::encode(&caller),
            event: ContractEvent::Call,
            contract_state: caller_state.to_vec(),
            secondary_states: [(hex::encode(&callee), callee_state.to_vec())].into(),
        };
        reference.check_receipt(&receipt).unwrap();
        #[cfg(feature = "localnet")]
        assert!(reference.development_submission_view().is_err());

        let mut wrong_state = receipt.clone();
        wrong_state.contract_state[0] ^= 1;
        assert_eq!(reference.check_receipt(&wrong_state), Err(Error::Receipt));
        let mut crossed_state = receipt.clone();
        crossed_state
            .secondary_states
            .insert(hex::encode(&callee), caller_state.to_vec());
        assert_eq!(reference.check_receipt(&crossed_state), Err(Error::Receipt));
        let rejects = |bytes: &[u8], after_height, expected_calls| {
            PublicTransactionReference::from_composed_calls(
                fixture_policy(),
                bytes,
                after_height,
                expected_calls,
            )
            .is_err()
        };
        assert!(
            rejects(transaction, 30_431, [expected[1], expected[0]])
        );
        let wrong_address = [0; 32];
        assert!(rejects(
            transaction,
            30_431,
            [
                (wrong_address.as_slice(), expected[0].1, expected[0].2),
                expected[1],
            ]
        ));
        assert!(rejects(
            transaction,
            30_431,
            [(expected[0].0, &b"wrong"[..], expected[0].2), expected[1]]
        ));
        let mut wrong_action: SealedTransaction = tagged_deserialize(&transaction[..]).unwrap();
        let Transaction::Standard(stx) = &mut wrong_action else {
            panic!("standard transaction")
        };
        let mut intent = (*stx.intents.get(&CONTRACT_SEGMENT).unwrap()).clone();
        let mut actions: Vec<_> = intent.actions.iter_deref().cloned().collect();
        actions[0] = ContractAction::Deploy(Sp::new(ContractDeploy {
            initial_state: ContractState::<Db>::default(),
            nonce: HashOutput([9; 32]),
        }));
        intent.actions = actions.into();
        stx.intents = stx.intents.insert(CONTRACT_SEGMENT, intent);
        assert!(rejects(&encode(&wrong_action).unwrap(), 30_431, expected));
        assert!(rejects(
            transaction,
            30_431,
            [
                expected[0],
                (expected[0].0, expected[1].1, expected[1].2),
            ]
        ));
        assert!(rejects(
            transaction,
            30_431,
            [(&caller[..31], expected[0].1, expected[0].2), expected[1]]
        ));
        assert!(rejects(bound().bytes(), 20, expected));
        let oversized_state = vec![0; MAX_STATE + 1];
        assert!(rejects(
            transaction,
            30_431,
            [
                (expected[0].0, expected[0].1, &oversized_state),
                expected[1],
            ]
        ));
        assert!(
            PublicTransactionReference::from_bytes(
                fixture_policy(),
                transaction,
                30_431,
                caller_state,
            )
            .is_err()
        );
    }
}
