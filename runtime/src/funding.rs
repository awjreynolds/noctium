//! Bounded native DUST fee construction. The host owns wallet state, keys and approval.
#[cfg(feature = "localnet")]
use crate::client::{
    Snapshot, shielded_immediate_change_shape_valid, shielded_merge_shape_valid,
    shielded_relay_shape_valid,
};
use crate::{
    Db,
    proof::{ProvedNativeIntent, TrustedParameters},
};
#[cfg(feature = "localnet")]
use base_crypto::hash::HashOutput;
use base_crypto::{rng::SplittableRng, time::Timestamp};
use coin_structure::coin::TokenType;
#[cfg(feature = "localnet")]
use coin_structure::{
    coin::{Info, PublicKey},
    transfer::Recipient,
};
use ledger::{
    dust::{DUST_EXPECTED_FILES, DustActions, DustLocalState, DustOutput, DustSecretKey},
    structure::{
        ContractAction, Intent, LedgerParameters, ProofMarker, Signature, StandardTransaction,
        SignatureVerifyingKey, Transaction,
    },
};
use rand::rngs::StdRng;
use sha2::{Digest, Sha256};
use std::io;
use storage::arena::Sp;
#[cfg(feature = "localnet")]
use transient_crypto::proofs::Proof;
use transient_crypto::{
    commitment::{PedersenRandomness, PureGeneratorPedersen},
    proofs::{KeyLocation, ProvingKeyMaterial, Resolver, Zkir},
};
#[cfg(feature = "localnet")]
use zswap::Offer as ZswapOffer;

pub type UnsealedTransaction = Transaction<Signature, ProofMarker, PedersenRandomness, Db>;
pub type SealedTransaction = Transaction<Signature, ProofMarker, PureGeneratorPedersen, Db>;
pub const CONTRACT_SEGMENT: u16 = 1;
pub const FUNDING_SEGMENT: u16 = 2;

pub(crate) fn admissible_actions(intent: &ProvedNativeIntent) -> bool {
    let count = intent.actions.len();
    count == 1
        || (count > 1
            && intent
                .actions
                .iter_deref()
                .all(|action| matches!(action, ContractAction::Call(_))))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    Material,
    Parameters,
    Wallet,
    Budget,
    Limits,
    Balance,
    Proof,
    Intent,
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "noctium_funding_{self:?}")
    }
}
impl std::error::Error for Error {}
type Result<T> = std::result::Result<T, Error>;

/// Official system-precompile material, authenticated against hashes pinned by the ledger.
/// The legacy DUST circuit is separate from the selected 3.x Lean contract circuit.
pub struct DustMaterial {
    material: ProvingKeyMaterial,
    k: u8,
}
impl DustMaterial {
    pub fn from_bytes(prover: &[u8], verifier: &[u8], circuit: &[u8]) -> Result<Self> {
        for (suffix, bytes) in [
            ("spend.prover", prover),
            ("spend.verifier", verifier),
            ("spend.bzkir", circuit),
        ] {
            let (_, expected, _) = DUST_EXPECTED_FILES
                .iter()
                .find(|(path, _, _)| path.ends_with(suffix))
                .ok_or(Error::Material)?;
            if bytes.is_empty()
                || bytes.len() > 16 * 1024 * 1024
                || Sha256::digest(bytes).as_slice() != expected
            {
                return Err(Error::Material);
            }
        }
        let ir = builtin_zkir::IrSource::load_from_tagged(io::Cursor::new(circuit))
            .map_err(|_| Error::Material)?;
        let k = ir.k();
        if !(1..=20).contains(&k) {
            return Err(Error::Material);
        }
        Ok(Self {
            material: ProvingKeyMaterial {
                prover_key: prover.to_vec(),
                verifier_key: verifier.to_vec(),
                ir_source: circuit.to_vec(),
            },
            k,
        })
    }
    pub fn k(&self) -> u8 {
        self.k
    }
}
impl Resolver for DustMaterial {
    async fn resolve_key(&self, key: KeyLocation) -> io::Result<Option<ProvingKeyMaterial>> {
        if key.0.as_ref() == "midnight/dust/spend" {
            Ok(Some(self.material.clone()))
        } else {
            Ok(None)
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct FeePolicy {
    pub max_dust: u128,
    pub margin_blocks: usize,
    pub max_spends: usize,
}
impl FeePolicy {
    fn validate(self) -> Result<()> {
        if self.max_dust == 0 || self.margin_blocks > 8 || !(1..=64).contains(&self.max_spends) {
            return Err(Error::Limits);
        }
        Ok(())
    }
}

/// Private wallet state supplied by an authorized host. No Debug or ambient key derivation.
pub struct DustFunding {
    secret: DustSecretKey,
    state: DustLocalState<Db>,
}
impl DustFunding {
    pub fn new(secret: DustSecretKey, state: DustLocalState<Db>) -> Self {
        Self { secret, state }
    }
    pub fn balance(&self, time: Timestamp) -> u128 {
        self.state.wallet_balance(time)
    }

    /// Speculative selection leaves the retained wallet unchanged. Replay accepted chain events
    /// before preparing another attempt. Approval and sealing belong to the host signer.
    pub async fn fund(
        &self,
        contract: &ProvedNativeIntent,
        network_id: &str,
        parameters: &LedgerParameters,
        material: &DustMaterial,
        srs: &TrustedParameters,
        now: Timestamp,
        policy: FeePolicy,
        rng: StdRng,
    ) -> Result<FundedTransaction> {
        self.fund_base(
            contract,
            one_intent(network_id, CONTRACT_SEGMENT, contract.clone()),
            network_id,
            parameters,
            material,
            srs,
            now,
            policy,
            rng,
        )
        .await
    }

    #[cfg(feature = "localnet")]
    pub(crate) async fn fund_unshielded_caller(
        &self,
        contract: &ProvedNativeIntent,
        snapshot: &Snapshot,
        network_id: &str,
        parameters: &LedgerParameters,
        material: &DustMaterial,
        srs: &TrustedParameters,
        now: Timestamp,
        policy: FeePolicy,
        rng: StdRng,
    ) -> Result<FundedTransaction> {
        crate::unshielded_caller::validate_guaranteed_caller_offer(snapshot, contract)
            .map_err(|_| Error::Intent)?;
        let base = one_intent(network_id, CONTRACT_SEGMENT, contract.clone());
        self.fund_base_inner(
            contract,
            base,
            network_id,
            parameters,
            material,
            srs,
            now,
            policy,
            true,
            rng,
        )
        .await
    }

    #[cfg(feature = "localnet")]
    pub(crate) async fn fund_unshielded_mint(
        &self,
        contract: &ProvedNativeIntent,
        network_id: &str,
        parameters: &LedgerParameters,
        material: &DustMaterial,
        srs: &TrustedParameters,
        now: Timestamp,
        policy: FeePolicy,
        rng: StdRng,
    ) -> Result<FundedTransaction> {
        crate::unshielded_mint::validate_user_output_offer(contract)
            .map_err(|_| Error::Intent)?;
        self.fund_base_inner(
            contract,
            one_intent(network_id, CONTRACT_SEGMENT, contract.clone()),
            network_id,
            parameters,
            material,
            srs,
            now,
            policy,
            true,
            rng,
        )
        .await
    }

    #[cfg(feature = "localnet")]
    pub(crate) async fn fund_shielded_receive(
        &self,
        contract: &ProvedNativeIntent,
        offer: ZswapOffer<Proof, Db>,
        offer_binding_randomness: PedersenRandomness,
        network_id: &str,
        parameters: &LedgerParameters,
        material: &DustMaterial,
        srs: &TrustedParameters,
        now: Timestamp,
        policy: FeePolicy,
        rng: StdRng,
    ) -> Result<FundedTransaction> {
        let Some(ContractAction::Call(call)) = contract.actions.get(0) else {
            return Err(Error::Intent);
        };
        let Some(transcript) = call.guaranteed_transcript.as_deref() else {
            return Err(Error::Intent);
        };
        let Some(output) = offer.outputs.get(0) else {
            return Err(Error::Intent);
        };
        if contract.actions.len() != 1
            || call.fallible_transcript.is_some()
            || transcript.effects.claimed_shielded_receives.size() != 1
            || !transcript
                .effects
                .claimed_shielded_receives
                .iter()
                .any(|commitment| **commitment == output.coin_com)
            || transcript.effects.shielded_mints.size() != 1
            || offer.outputs.len() != 1
            || !offer.inputs.is_empty()
            || !offer.transient.is_empty()
            || output.contract_address.as_deref() != Some(&call.address)
        {
            return Err(Error::Intent);
        }

        self.fund_shielded_offer(
            contract,
            offer,
            offer_binding_randomness,
            network_id,
            parameters,
            material,
            srs,
            now,
            policy,
            rng,
        )
        .await
    }

    /// Fund one shielded mint to a wallet key, with no contract-owned receive.
    #[cfg(feature = "localnet")]
    pub(crate) async fn fund_shielded_wallet_mint(
        &self,
        contract: &ProvedNativeIntent,
        offer: ZswapOffer<Proof, Db>,
        offer_binding_randomness: PedersenRandomness,
        domain: HashOutput,
        coin: &Info,
        recipient: PublicKey,
        network_id: &str,
        parameters: &LedgerParameters,
        material: &DustMaterial,
        srs: &TrustedParameters,
        now: Timestamp,
        policy: FeePolicy,
        rng: StdRng,
    ) -> Result<FundedTransaction> {
        let Some(ContractAction::Call(call)) = contract.actions.get(0) else {
            return Err(Error::Intent);
        };
        let Some(transcript) = call.guaranteed_transcript.as_deref() else {
            return Err(Error::Intent);
        };
        let Some(output) = offer.outputs.get(0) else {
            return Err(Error::Intent);
        };
        let Some(amount) = u64::try_from(coin.value).ok() else {
            return Err(Error::Intent);
        };
        let exact_mint_delta = {
            let mut deltas = offer.deltas.iter_deref();
            match (deltas.next(), deltas.next()) {
                (Some(delta), None) => {
                    delta.token_type == coin.type_ && delta.value == -i128::from(amount)
                }
                _ => false,
            }
        };
        let expected_commitment = coin.commitment(&Recipient::User(recipient));
        if contract.actions.len() != 1
            || call.fallible_transcript.is_some()
            || transcript.effects.claimed_nullifiers.size() != 0
            || transcript.effects.claimed_shielded_spends.size() != 0
            || transcript.effects.claimed_shielded_receives.size() != 0
            || transcript.effects.shielded_mints.size() != 1
            || transcript
                .effects
                .shielded_mints
                .get(&domain)
                .map(|value| *value)
                != Some(amount)
            || offer.inputs.len() != 0
            || offer.outputs.len() != 1
            || !offer.transient.is_empty()
            || coin.value == 0
            || coin.type_ != call.address.custom_shielded_token_type(domain)
            || output.coin_com != expected_commitment
            || output.contract_address.is_some()
            || output.ciphertext.is_none()
            || !exact_mint_delta
        {
            return Err(Error::Intent);
        }

        self.fund_shielded_offer(
            contract,
            offer,
            offer_binding_randomness,
            network_id,
            parameters,
            material,
            srs,
            now,
            policy,
            rng,
        )
        .await
    }

    /// Fund the pinned relay-to-destination transient and matching final output.
    #[cfg(feature = "localnet")]
    pub(crate) async fn fund_shielded_relay(
        &self,
        contract: &ProvedNativeIntent,
        offer: ZswapOffer<Proof, Db>,
        offer_binding_randomness: PedersenRandomness,
        relay_mint: &Info,
        mint_domain: HashOutput,
        network_id: &str,
        parameters: &LedgerParameters,
        material: &DustMaterial,
        srs: &TrustedParameters,
        now: Timestamp,
        policy: FeePolicy,
        rng: StdRng,
    ) -> Result<FundedTransaction> {
        if !shielded_relay_shape_valid(contract, &offer, relay_mint, mint_domain) {
            return Err(Error::Intent);
        }

        self.fund_shielded_offer(
            contract,
            offer,
            offer_binding_randomness,
            network_id,
            parameters,
            material,
            srs,
            now,
            policy,
            rng,
        )
        .await
    }

    /// Fund a minted contract transient split into the exact user output and contract change.
    #[cfg(feature = "localnet")]
    pub(crate) async fn fund_shielded_immediate_change(
        &self,
        contract: &ProvedNativeIntent,
        offer: ZswapOffer<Proof, Db>,
        offer_binding_randomness: PedersenRandomness,
        mint: &Info,
        mint_domain: HashOutput,
        recipient: PublicKey,
        network_id: &str,
        parameters: &LedgerParameters,
        material: &DustMaterial,
        srs: &TrustedParameters,
        now: Timestamp,
        policy: FeePolicy,
        rng: StdRng,
    ) -> Result<FundedTransaction> {
        if !shielded_immediate_change_shape_valid(
            contract,
            &offer,
            mint,
            mint_domain,
            recipient,
        ) {
            return Err(Error::Intent);
        }

        self.fund_shielded_offer(
            contract,
            offer,
            offer_binding_randomness,
            network_id,
            parameters,
            material,
            srs,
            now,
            policy,
            rng,
        )
        .await
    }

    /// Fund one wallet input into one contract-owned shielded receive.
    /// The call must claim only the receive commitment carried by the offer.
    #[cfg(feature = "localnet")]
    pub(crate) async fn fund_wallet_shielded_receive(
        &self,
        contract: &ProvedNativeIntent,
        offer: ZswapOffer<Proof, Db>,
        offer_binding_randomness: PedersenRandomness,
        network_id: &str,
        parameters: &LedgerParameters,
        material: &DustMaterial,
        srs: &TrustedParameters,
        now: Timestamp,
        policy: FeePolicy,
        rng: StdRng,
    ) -> Result<FundedTransaction> {
        let Some(ContractAction::Call(call)) = contract.actions.get(0) else {
            return Err(Error::Intent);
        };
        let Some(transcript) = call.guaranteed_transcript.as_deref() else {
            return Err(Error::Intent);
        };
        let Some(input) = offer.inputs.get(0) else {
            return Err(Error::Intent);
        };
        let Some(output) = offer.outputs.get(0) else {
            return Err(Error::Intent);
        };
        if contract.actions.len() != 1
            || call.fallible_transcript.is_some()
            || transcript.effects.claimed_nullifiers.size() != 0
            || transcript.effects.claimed_shielded_spends.size() != 0
            || transcript.effects.claimed_shielded_receives.size() != 1
            || !transcript
                .effects
                .claimed_shielded_receives
                .iter()
                .any(|commitment| **commitment == output.coin_com)
            || transcript.effects.shielded_mints.size() != 0
            || offer.inputs.len() != 1
            || offer.outputs.len() != 1
            || !offer.transient.is_empty()
            || input.contract_address.is_some()
            || output.contract_address.as_deref() != Some(&call.address)
        {
            return Err(Error::Intent);
        }

        self.fund_shielded_offer(
            contract,
            offer,
            offer_binding_randomness,
            network_id,
            parameters,
            material,
            srs,
            now,
            policy,
            rng,
        )
        .await
    }

    /// Fund one whole-coin contract spend to one encrypted user output.
    /// The proved call must claim exactly the offer's nullifier and output commitment.
    #[cfg(feature = "localnet")]
    pub(crate) async fn fund_shielded_transfer(
        &self,
        contract: &ProvedNativeIntent,
        offer: ZswapOffer<Proof, Db>,
        offer_binding_randomness: PedersenRandomness,
        network_id: &str,
        parameters: &LedgerParameters,
        material: &DustMaterial,
        srs: &TrustedParameters,
        now: Timestamp,
        policy: FeePolicy,
        rng: StdRng,
    ) -> Result<FundedTransaction> {
        let Some(ContractAction::Call(call)) = contract.actions.get(0) else {
            return Err(Error::Intent);
        };
        let Some(transcript) = call.guaranteed_transcript.as_deref() else {
            return Err(Error::Intent);
        };
        let Some(input) = offer.inputs.get(0) else {
            return Err(Error::Intent);
        };
        let Some(output) = offer.outputs.get(0) else {
            return Err(Error::Intent);
        };
        if contract.actions.len() != 1
            || call.fallible_transcript.is_some()
            || transcript.effects.claimed_nullifiers.size() != 1
            || !transcript
                .effects
                .claimed_nullifiers
                .iter()
                .any(|nullifier| **nullifier == input.nullifier)
            || transcript.effects.claimed_shielded_spends.size() != 1
            || !transcript
                .effects
                .claimed_shielded_spends
                .iter()
                .any(|commitment| **commitment == output.coin_com)
            || transcript.effects.claimed_shielded_receives.size() != 0
            || transcript.effects.shielded_mints.size() != 0
            || offer.inputs.len() != 1
            || offer.outputs.len() != 1
            || !offer.transient.is_empty()
            || input.contract_address.as_deref() != Some(&call.address)
            || output.contract_address.is_some()
            || output.ciphertext.is_none()
        {
            return Err(Error::Intent);
        }

        self.fund_shielded_offer(
            contract,
            offer,
            offer_binding_randomness,
            network_id,
            parameters,
            material,
            srs,
            now,
            policy,
            rng,
        )
        .await
    }

    /// Fund a booked contract-owned merge with a finalized or newly minted second coin.
    #[cfg(feature = "localnet")]
    pub(crate) async fn fund_shielded_merge(
        &self,
        contract: &ProvedNativeIntent,
        offer: ZswapOffer<Proof, Db>,
        offer_binding_randomness: PedersenRandomness,
        staged_mint: Option<(&Info, HashOutput)>,
        network_id: &str,
        parameters: &LedgerParameters,
        material: &DustMaterial,
        srs: &TrustedParameters,
        now: Timestamp,
        policy: FeePolicy,
        rng: StdRng,
    ) -> Result<FundedTransaction> {
        if !shielded_merge_shape_valid(contract, &offer, staged_mint) {
            return Err(Error::Intent);
        }

        self.fund_shielded_offer(
            contract,
            offer,
            offer_binding_randomness,
            network_id,
            parameters,
            material,
            srs,
            now,
            policy,
            rng,
        )
        .await
    }

    /// Fund one contract-owned coin split across one encrypted user output and one contract change.
    #[cfg(feature = "localnet")]
    pub(crate) async fn fund_shielded_split(
        &self,
        contract: &ProvedNativeIntent,
        offer: ZswapOffer<Proof, Db>,
        offer_binding_randomness: PedersenRandomness,
        network_id: &str,
        parameters: &LedgerParameters,
        material: &DustMaterial,
        srs: &TrustedParameters,
        now: Timestamp,
        policy: FeePolicy,
        rng: StdRng,
    ) -> Result<FundedTransaction> {
        let Some(ContractAction::Call(call)) = contract.actions.get(0) else {
            return Err(Error::Intent);
        };
        let Some(transcript) = call.guaranteed_transcript.as_deref() else {
            return Err(Error::Intent);
        };
        let Some(input) = offer.inputs.get(0) else {
            return Err(Error::Intent);
        };
        let Some(user_output) = offer
            .outputs
            .iter_deref()
            .find(|output| output.contract_address.is_none() && output.ciphertext.is_some())
        else {
            return Err(Error::Intent);
        };
        let Some(change_output) = offer.outputs.iter_deref().find(|output| {
            output.contract_address.as_deref() == Some(&call.address) && output.ciphertext.is_none()
        }) else {
            return Err(Error::Intent);
        };
        if contract.actions.len() != 1
            || call.fallible_transcript.is_some()
            || transcript.effects.claimed_nullifiers.size() != 1
            || !transcript
                .effects
                .claimed_nullifiers
                .iter()
                .any(|nullifier| **nullifier == input.nullifier)
            || transcript.effects.claimed_shielded_spends.size() != 2
            || !transcript
                .effects
                .claimed_shielded_spends
                .iter()
                .any(|commitment| **commitment == user_output.coin_com)
            || !transcript
                .effects
                .claimed_shielded_spends
                .iter()
                .any(|commitment| **commitment == change_output.coin_com)
            || transcript.effects.claimed_shielded_receives.size() != 1
            || !transcript
                .effects
                .claimed_shielded_receives
                .iter()
                .any(|commitment| **commitment == change_output.coin_com)
            || transcript.effects.shielded_mints.size() != 0
            || offer.inputs.len() != 1
            || offer.outputs.len() != 2
            || !offer.transient.is_empty()
            || user_output.coin_com == change_output.coin_com
            || input.contract_address.as_deref() != Some(&call.address)
        {
            return Err(Error::Intent);
        }

        self.fund_shielded_offer(
            contract,
            offer,
            offer_binding_randomness,
            network_id,
            parameters,
            material,
            srs,
            now,
            policy,
            rng,
        )
        .await
    }

    #[cfg(feature = "localnet")]
    async fn fund_shielded_offer(
        &self,
        contract: &ProvedNativeIntent,
        offer: ZswapOffer<Proof, Db>,
        offer_binding_randomness: PedersenRandomness,
        network_id: &str,
        parameters: &LedgerParameters,
        material: &DustMaterial,
        srs: &TrustedParameters,
        now: Timestamp,
        policy: FeePolicy,
        rng: StdRng,
    ) -> Result<FundedTransaction> {
        let mut base = one_intent(network_id, CONTRACT_SEGMENT, contract.clone());
        let Transaction::Standard(transaction) = &mut base else {
            return Err(Error::Intent);
        };
        transaction.guaranteed_coins = Some(Sp::new(offer));
        transaction.binding_randomness = transaction.binding_randomness + offer_binding_randomness;
        if transaction
            .balance(None)
            .map_err(|_| Error::Balance)?
            .iter()
            .any(|((token, _), delta)| *token != TokenType::Dust && *delta != 0)
        {
            return Err(Error::Balance);
        }

        self.fund_base(
            contract, base, network_id, parameters, material, srs, now, policy, rng,
        )
        .await
    }

    async fn fund_base(
        &self,
        contract: &ProvedNativeIntent,
        base: UnsealedTransaction,
        network_id: &str,
        parameters: &LedgerParameters,
        material: &DustMaterial,
        srs: &TrustedParameters,
        now: Timestamp,
        policy: FeePolicy,
        rng: StdRng,
    ) -> Result<FundedTransaction> {
        self.fund_base_inner(
            contract, base, network_id, parameters, material, srs, now, policy, false, rng,
        )
        .await
    }

    async fn fund_base_inner(
        &self,
        contract: &ProvedNativeIntent,
        base: UnsealedTransaction,
        network_id: &str,
        parameters: &LedgerParameters,
        material: &DustMaterial,
        srs: &TrustedParameters,
        now: Timestamp,
        policy: FeePolicy,
        allow_guaranteed_unshielded_offer: bool,
        mut rng: StdRng,
    ) -> Result<FundedTransaction> {
        policy.validate()?;
        if self.state.params != parameters.dust || now < self.state.sync_time {
            return Err(Error::Parameters);
        }
        if material.k != srs.k() {
            return Err(Error::Parameters);
        }
        if !admissible_actions(contract)
            || contract.guaranteed_unshielded_offer.is_some() != allow_guaranteed_unshielded_offer
            || contract.fallible_unshielded_offer.is_some()
            || contract.dust_actions.is_some()
            || contract.ttl <= now
            || network_id.is_empty()
            || network_id.len() > 128
        {
            return Err(Error::Intent);
        }
        let has_caller_inputs = contract.guaranteed_unshielded_offer.as_ref()
            .is_some_and(|offer| !offer.inputs.is_empty());
        let mut needed = 0u128;
        for _ in 0..10 {
            if needed > policy.max_dust {
                return Err(Error::Budget);
            }
            let candidate = if needed == 0 {
                base.clone()
            } else {
                let mut candidates: Vec<_> = self
                    .state
                    .utxos()
                    .filter_map(|output| {
                        let generation = self.state.generation_info(&output)?;
                        let amount = DustOutput::from(output).updated_value(
                            &generation,
                            now,
                            &parameters.dust,
                        );
                        (amount > 0).then_some((amount, output))
                    })
                    .collect();
                candidates.sort_by(|(a, _), (b, _)| b.cmp(a));
                let mut remaining = needed;
                let mut local = self.state.clone();
                let mut spends = Vec::new();
                for (amount, output) in candidates {
                    if remaining == 0 {
                        break;
                    }
                    if spends.len() == policy.max_spends {
                        return Err(Error::Limits);
                    }
                    let spent = remaining.min(amount);
                    let (next, spend) = local
                        .spend(&self.secret, &output, spent, now)
                        .map_err(|_| Error::Wallet)?;
                    local = next;
                    spends.push(spend);
                    remaining -= spent;
                }
                if remaining != 0 {
                    return Err(Error::Wallet);
                }
                let mut fee = Intent::<Signature, _, _, Db>::empty(&mut rng, contract.ttl);
                fee.dust_actions = Some(Sp::new(DustActions {
                    spends: spends.into(),
                    registrations: vec![].into(),
                    ctime: now,
                }));
                let prover = builtin_zkir::LocalProvingProvider {
                    rng: rng.split(),
                    resolver: material,
                    params: srs,
                };
                let (_, fee) = fee
                    .prove(
                        FUNDING_SEGMENT,
                        prover,
                        &parameters.cost_model.runtime_cost_model,
                    )
                    .await
                    .map_err(|_| Error::Proof)?;
                base.merge(&one_intent(network_id, FUNDING_SEGMENT, fee))
                    .map_err(|_| Error::Balance)?
            };
            // Binding seals have a fixed encoded size. Estimate from a real seal, without
            // binding a durable transaction identity or changing the retained contract intent.
            let signature_candidate = has_caller_inputs
                .then(|| caller_signature_fee_candidate(&candidate))
                .transpose()?;
            let fee_candidate = signature_candidate.as_ref().unwrap_or(&candidate);
            let fees = fee_candidate
                .seal(rng.split())
                .fees_with_margin(parameters, policy.margin_blocks)
                .map_err(|_| Error::Balance)?;
            if fees > policy.max_dust {
                return Err(Error::Budget);
            }
            let deltas = candidate.balance(Some(fees)).map_err(|_| Error::Balance)?;
            let mut missing = 0;
            for ((token, _), delta) in deltas {
                if token == TokenType::Dust && delta < 0 {
                    missing += delta.unsigned_abs();
                } else if delta < 0 {
                    return Err(Error::Balance);
                }
            }
            if missing == 0 {
                return Ok(FundedTransaction {
                    transaction: candidate,
                    spent_dust: needed,
                    estimated_fee: fees,
                });
            }
            needed = needed.checked_add(missing).ok_or(Error::Budget)?;
        }
        Err(Error::Balance)
    }
}

/// Still unsealed and unbound to a journal. A host signer must authorize the complete budget.
pub struct FundedTransaction {
    transaction: UnsealedTransaction,
    spent_dust: u128,
    estimated_fee: u128,
}
impl FundedTransaction {
    pub fn native(&self) -> &UnsealedTransaction {
        &self.transaction
    }
    pub fn spent_dust(&self) -> u128 {
        self.spent_dust
    }
    pub fn estimated_fee(&self) -> u128 {
        self.estimated_fee
    }
}

pub fn one_intent(
    network_id: &str,
    segment: u16,
    intent: ProvedNativeIntent,
) -> UnsealedTransaction {
    Transaction::Standard(StandardTransaction {
        network_id: network_id.to_owned(),
        binding_randomness: intent.binding_commitment,
        intents: [(segment, intent)].into_iter().collect(),
        guaranteed_coins: None,
        fallible_coins: Default::default(),
    })
}

fn caller_signature_fee_candidate(
    transaction: &UnsealedTransaction,
) -> Result<UnsealedTransaction> {
    let mut candidate = transaction.clone();
    let Transaction::Standard(standard) = &mut candidate else {
        return Err(Error::Intent);
    };
    let mut contract = (*standard
        .intents
        .get(&CONTRACT_SEGMENT)
        .ok_or(Error::Intent)?)
    .clone();
    let offer = contract
        .guaranteed_unshielded_offer
        .as_deref()
        .ok_or(Error::Intent)?;
    if !offer.signatures.is_empty() {
        return Err(Error::Intent);
    }
    let mut offer = (*offer).clone();
    let placeholders = offer
        .inputs
        .iter()
        .map(|spend| match &spend.owner {
            SignatureVerifyingKey::Schnorr(_) => Signature::Schnorr(Default::default()),
            SignatureVerifyingKey::ECDSA(_) => Signature::ECDSA(Default::default()),
        })
        .collect();
    offer.add_signatures(placeholders);
    contract.guaranteed_unshielded_offer = Some(Sp::new(offer));
    standard.intents = standard.intents.insert(CONTRACT_SEGMENT, contract);
    Ok(candidate)
}
