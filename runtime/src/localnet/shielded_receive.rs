use super::{DEVELOPMENT_GENESIS, DevelopmentFunding, Error, ProofCache, Result, check};
use crate::{
    Db,
    client::{BoundTransaction, HostFailure, SigningAdapter, Snapshot},
    proof::{
        ContractOperationTarget, ContractStateBinding, CurrentStateContext, LocalProver,
        PreparedProof, TrustedParameters,
    },
};
use base_crypto::{hash::HashOutput, rng::SplittableRng};
use coin_structure::{
    coin::{Commitment, Info, PublicKey},
    contract::ContractAddress,
    transfer::Recipient,
};
use ledger::structure::GUARANTEED_SEGMENT;
use rand::rngs::StdRng;
use serde_json::Value;
use std::{collections::BTreeMap, future::pending};
use transient_crypto::{
    commitment::PedersenRandomness,
    encryption,
    proofs::{Proof, ProofPreimage},
};
use zswap::{Input, Offer, Output, prove::ZswapResolver};

fn read_witness_bytes32(inputs: &BTreeMap<String, Value>, name: &str) -> Result<[u8; 32]> {
    let value = inputs.get(name).ok_or(Error::State)?;
    check(
        value.get("kind").and_then(Value::as_str) == Some("bytes"),
        Error::State,
    )?;
    let values = value
        .get("values")
        .and_then(Value::as_array)
        .ok_or(Error::State)?;
    check(values.len() == 32, Error::State)?;
    let mut bytes = [0; 32];
    for (slot, value) in bytes.iter_mut().zip(values) {
        *slot = u8::try_from(value.as_u64().ok_or(Error::State)?).map_err(|_| Error::State)?;
    }
    Ok(bytes)
}

fn read_witness_uint64(inputs: &BTreeMap<String, Value>, name: &str) -> Result<u64> {
    let value = inputs.get(name).ok_or(Error::State)?;
    if let Some(value) = value.as_u64() {
        return Ok(value);
    }
    value
        .as_str()
        .ok_or(Error::State)?
        .parse()
        .map_err(|_| Error::State)
}

pub(super) struct BookedOffer {
    pub(super) offer: Offer<Proof, Db>,
    pub(super) randomness: PedersenRandomness,
    address: ContractAddress,
    commitment: Commitment,
    index: u64,
    current_state: Vec<u8>,
}

impl BookedOffer {
    pub(super) fn check_booking(
        &self,
        snapshot: &Snapshot,
    ) -> std::result::Result<(), HostFailure> {
        let (_, indices) = snapshot
            .state
            .zswap
            .try_apply(&self.offer, None)
            .map_err(|_| HostFailure)?;
        let state = snapshot
            .state
            .contract
            .get(&self.address)
            .ok_or(HostFailure)?;
        let mut bytes = Vec::new();
        serialize::tagged_serialize(&*state, &mut bytes).map_err(|_| HostFailure)?;
        if indices.get(&self.commitment).as_deref() != Some(&self.index)
            || bytes != self.current_state
        {
            return Err(HostFailure);
        }
        Ok(())
    }
}

pub(super) struct BookedWalletOffer {
    pub(super) offer: Offer<Proof, Db>,
    pub(super) randomness: PedersenRandomness,
    address: ContractAddress,
    commitment: Commitment,
    index: u64,
    current_state: Vec<u8>,
}

pub(super) struct BookedWalletMint {
    pub(super) offer: Offer<Proof, Db>,
    pub(super) randomness: PedersenRandomness,
    pub(super) domain: HashOutput,
    pub(super) coin: Info,
    pub(super) recipient: PublicKey,
    address: ContractAddress,
    commitment: Commitment,
    index: u64,
    current_state: Vec<u8>,
}

impl BookedWalletMint {
    pub(super) fn check_booking(
        &self,
        snapshot: &Snapshot,
    ) -> std::result::Result<(), HostFailure> {
        let (_, indices) = snapshot
            .state
            .zswap
            .try_apply(&self.offer, None)
            .map_err(|_| HostFailure)?;
        let state = snapshot
            .state
            .contract
            .get(&self.address)
            .ok_or(HostFailure)?;
        let mut bytes = Vec::new();
        serialize::tagged_serialize(&*state, &mut bytes).map_err(|_| HostFailure)?;
        let Some(output) = self.offer.outputs.get(0) else {
            return Err(HostFailure);
        };
        if bytes != self.current_state
            || indices.get(&self.commitment).as_deref() != Some(&self.index)
            || self.offer.inputs.len() != 0
            || self.offer.outputs.len() != 1
            || !self.offer.transient.is_empty()
            || self.commitment != self.coin.commitment(&Recipient::User(self.recipient))
            || output.coin_com != self.commitment
            || output.contract_address.is_some()
            || output.ciphertext.is_none()
        {
            return Err(HostFailure);
        }
        Ok(())
    }
}

impl BookedWalletOffer {
    pub(super) fn check_booking(
        &self,
        snapshot: &Snapshot,
    ) -> std::result::Result<(), HostFailure> {
        let (_, indices) = snapshot
            .state
            .zswap
            .try_apply(&self.offer, None)
            .map_err(|_| HostFailure)?;
        let state = snapshot
            .state
            .contract
            .get(&self.address)
            .ok_or(HostFailure)?;
        let mut bytes = Vec::new();
        serialize::tagged_serialize(&*state, &mut bytes).map_err(|_| HostFailure)?;
        let zswap = &snapshot.state.zswap;
        let Some(input) = self.offer.inputs.get(0) else {
            return Err(HostFailure);
        };
        let Some(output) = self.offer.outputs.get(0) else {
            return Err(HostFailure);
        };
        if bytes != self.current_state
            || indices.get(&self.commitment).as_deref() != Some(&self.index)
            || !zswap.past_roots.contains(&input.merkle_tree_root)
            || zswap.nullifiers.contains_key(&input.nullifier)
            || self.offer.inputs.len() != 1
            || self.offer.outputs.len() != 1
            || !self.offer.transient.is_empty()
            || input.contract_address.is_some()
            || output.coin_com != self.commitment
            || output.contract_address.as_deref() != Some(&self.address)
            || output.ciphertext.is_some()
        {
            return Err(HostFailure);
        }
        Ok(())
    }
}

impl DevelopmentFunding<'_> {
    /// Bind one mint-funded contract-owned output from the development chain's
    /// current Zswap state. The caller approves the complete transaction before sealing.
    pub async fn bind_minted_shielded_receive(
        self,
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Value>,
        coin: &Info,
        parameters: &TrustedParameters,
        cache: &ProofCache,
        signer: &impl SigningAdapter,
        rng: StdRng,
    ) -> Result<BoundTransaction> {
        self.bind_minted_shielded_receive_with_binding(
            target, current, inputs, coin, parameters, cache, signer, rng,
        )
        .await
        .map(|(bound, _)| bound)
    }

    /// Mint one shielded coin directly to a wallet key and bind its exact output.
    pub async fn bind_minted_shielded_wallet(
        self,
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Value>,
        coin: &Info,
        recipient: PublicKey,
        recipient_encryption_key: encryption::PublicKey,
        parameters: &TrustedParameters,
        cache: &ProofCache,
        signer: &impl SigningAdapter,
        rng: StdRng,
    ) -> Result<BoundTransaction> {
        self.bind_minted_shielded_wallet_with_binding(
            target,
            current,
            inputs,
            coin,
            recipient,
            recipient_encryption_key,
            parameters,
            cache,
            signer,
            rng,
        )
        .await
        .map(|(bound, _)| bound)
    }

    pub(crate) async fn bind_minted_shielded_wallet_with_binding(
        mut self,
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Value>,
        coin: &Info,
        recipient: PublicKey,
        recipient_encryption_key: encryption::PublicKey,
        parameters: &TrustedParameters,
        cache: &ProofCache,
        signer: &impl SigningAdapter,
        mut rng: StdRng,
    ) -> Result<(BoundTransaction, ContractStateBinding)> {
        check(inputs.len() == 4, Error::State)?;
        let domain = HashOutput(read_witness_bytes32(&inputs, "domain")?);
        check(
            read_witness_bytes32(&inputs, "nonce")? == coin.nonce.0.0
                && read_witness_bytes32(&inputs, "recipient")? == recipient.0.0
                && read_witness_uint64(&inputs, "amount")?
                    == u64::try_from(coin.value).map_err(|_| Error::State)?,
            Error::State,
        )?;

        let policy = self.node.policy.clone();
        check(policy.genesis == DEVELOPMENT_GENESIS, Error::Policy)?;
        check(
            coin.value > 0 && coin.value <= u128::from(u64::MAX),
            Error::State,
        )?;
        let address_bytes = hex::decode(
            target
                .contract_address()
                .strip_prefix("0x")
                .unwrap_or(target.contract_address()),
        )
        .map_err(|_| Error::State)?;
        let address = ContractAddress(HashOutput(
            address_bytes.try_into().map_err(|_| Error::State)?,
        ));
        check(
            coin.type_ == address.custom_shielded_token_type(domain),
            Error::State,
        )?;

        let snapshot = self.node.sync()?;
        snapshot.validate(&policy).map_err(|_| Error::Network)?;
        check(policy == self.node.policy, Error::Policy)?;
        let mut current_rng = rng.split();
        let output = Output::<_, Db>::new(
            &mut current_rng,
            coin,
            Some(GUARANTEED_SEGMENT),
            &recipient,
            Some(recipient_encryption_key),
        )
        .map_err(|_| Error::State)?;
        let commitment = coin.commitment(&Recipient::User(recipient));
        check(output.coin_com == commitment, Error::State)?;
        let offer = Offer::new(vec![], vec![output], vec![]).ok_or(Error::State)?;
        let (_, indices) = snapshot
            .state
            .zswap
            .try_apply(&offer, None)
            .map_err(|_| Error::State)?;
        let index = *indices.get(&commitment).ok_or(Error::State)?;

        let prepared = PreparedProof::from_contract_witness_inputs_with_com_indices(
            target, current, inputs, indices, &mut rng,
        )
        .map_err(|_| Error::Proof)?;
        let proved = prepared
            .prove(
                &LocalProver::new(rng.split()),
                parameters,
                1_048_576,
                pending(),
            )
            .await
            .map_err(|_| Error::Proof)?;
        let binding = proved.contract_binding().ok_or(Error::State)?;
        let current_state = binding.current_state_bytes().ok_or(Error::State)?.to_vec();

        let mut provider = cache.provider.clone();
        provider.expected_data = zswap::ZSWAP_EXPECTED_FILES.to_vec();
        let resolver = ZswapResolver(provider);
        let randomness = offer.binding_randomness();
        let (_, offer) = offer
            .prove(
                builtin_zkir::LocalProvingProvider {
                    rng: rng.split(),
                    resolver: &resolver,
                    params: &resolver,
                },
                GUARANTEED_SEGMENT,
            )
            .await
            .map_err(|_| Error::Proof)?;
        self.wallet_shielded_mint = Some(BookedWalletMint {
            offer,
            randomness,
            domain,
            coin: *coin,
            recipient,
            address,
            commitment,
            index,
            current_state,
        });
        let expected = &self
            .wallet_shielded_mint
            .as_ref()
            .ok_or(Error::State)?
            .offer;
        let bound = BoundTransaction::prepare_shielded_receive(
            proved.native(),
            expected,
            policy,
            self.node,
            &self,
            signer,
        )
        .await
        .map_err(|_| Error::State)?;
        check(
            bound.expected_state() == binding.expected_state(),
            Error::State,
        )?;
        Ok((bound, binding.clone()))
    }

    /// Bind one wallet-owned input into one contract-owned Map coin.
    /// The caller builds the input with its wallet SDK. This method receives only the
    /// proof preimage, never wallet keys or wallet state.
    pub async fn bind_wallet_shielded_receive(
        mut self,
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Value>,
        coin: &Info,
        input: Input<ProofPreimage, Db>,
        parameters: &TrustedParameters,
        cache: &ProofCache,
        signer: &impl SigningAdapter,
        mut rng: StdRng,
    ) -> Result<BoundTransaction> {
        let policy = self.node.policy.clone();
        check(policy.genesis == DEVELOPMENT_GENESIS, Error::Policy)?;
        check(
            coin.value > 0 && coin.value <= i128::MAX as u128,
            Error::State,
        )?;
        check(input.contract_address.is_none(), Error::State)?;
        check(input.segment() == Some(GUARANTEED_SEGMENT), Error::State)?;

        let input_delta = input.delta();
        let bytes = hex::decode(
            target
                .contract_address()
                .strip_prefix("0x")
                .unwrap_or(target.contract_address()),
        )
        .map_err(|_| Error::State)?;
        let address = ContractAddress(HashOutput(bytes.try_into().map_err(|_| Error::State)?));
        let snapshot = self.node.sync()?;
        snapshot.validate(&policy).map_err(|_| Error::Network)?;
        check(policy == self.node.policy, Error::Policy)?;

        let output =
            Output::<_, Db>::new_contract_owned(&mut rng, coin, Some(GUARANTEED_SEGMENT), address)
                .map_err(|_| Error::State)?;
        let output_delta = output.delta();
        check(
            input_delta.token_type == output_delta.token_type
                && input_delta.value.checked_neg() == Some(output_delta.value),
            Error::State,
        )?;
        let commitment = output.coin_com;
        let offer = Offer::new(vec![input], vec![output], vec![]).ok_or(Error::State)?;
        let (_, indices) = snapshot
            .state
            .zswap
            .try_apply(&offer, None)
            .map_err(|_| Error::State)?;
        let index = *indices.get(&commitment).ok_or(Error::State)?;

        let prepared = PreparedProof::from_contract_witness_inputs_with_com_indices(
            target, current, inputs, indices, &mut rng,
        )
        .map_err(|_| Error::Proof)?;
        let proved = prepared
            .prove(
                &LocalProver::new(rng.split()),
                parameters,
                1_048_576,
                pending(),
            )
            .await
            .map_err(|_| Error::Proof)?;
        let binding = proved.contract_binding().ok_or(Error::State)?;
        let current_state = binding.current_state_bytes().ok_or(Error::State)?.to_vec();

        let mut provider = cache.provider.clone();
        provider.expected_data = zswap::ZSWAP_EXPECTED_FILES.to_vec();
        let resolver = ZswapResolver(provider);
        let randomness = offer.binding_randomness();
        let (_, offer) = offer
            .prove(
                builtin_zkir::LocalProvingProvider {
                    rng: rng.split(),
                    resolver: &resolver,
                    params: &resolver,
                },
                GUARANTEED_SEGMENT,
            )
            .await
            .map_err(|_| Error::Proof)?;
        self.wallet_shielded_receive = Some(BookedWalletOffer {
            offer,
            randomness,
            address,
            commitment,
            index,
            current_state,
        });
        let expected = &self
            .wallet_shielded_receive
            .as_ref()
            .ok_or(Error::State)?
            .offer;
        let bound = BoundTransaction::prepare_wallet_shielded_receive(
            proved.native(),
            expected,
            policy,
            self.node,
            &self,
            signer,
        )
        .await
        .map_err(|_| Error::State)?;
        check(
            bound.expected_state() == binding.expected_state(),
            Error::State,
        )?;
        Ok(bound)
    }

    pub(crate) async fn bind_minted_shielded_receive_with_binding(
        mut self,
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Value>,
        coin: &Info,
        parameters: &TrustedParameters,
        cache: &ProofCache,
        signer: &impl SigningAdapter,
        mut rng: StdRng,
    ) -> Result<(BoundTransaction, ContractStateBinding)> {
        let policy = self.node.policy.clone();
        check(policy.genesis == DEVELOPMENT_GENESIS, Error::Policy)?;
        check(
            coin.value > 0 && coin.value <= u128::from(u64::MAX),
            Error::State,
        )?;
        let bytes = hex::decode(target.contract_address()).map_err(|_| Error::State)?;
        let address = ContractAddress(HashOutput(bytes.try_into().map_err(|_| Error::State)?));
        let snapshot = self.node.sync()?;
        snapshot.validate(&policy).map_err(|_| Error::Network)?;
        let output =
            Output::<_, Db>::new_contract_owned(&mut rng, coin, Some(GUARANTEED_SEGMENT), address)
                .map_err(|_| Error::State)?;
        let commitment = output.coin_com;
        let offer = Offer::new(vec![], vec![output], vec![]).ok_or(Error::State)?;
        let (_, indices) = snapshot
            .state
            .zswap
            .try_apply(&offer, None)
            .map_err(|_| Error::State)?;
        let index = *indices.get(&commitment).ok_or(Error::State)?;
        let prepared = PreparedProof::from_contract_witness_inputs_with_com_indices(
            target, current, inputs, indices, &mut rng,
        )
        .map_err(|_| Error::State)?;
        let proved = prepared
            .prove(
                &LocalProver::new(rng.split()),
                parameters,
                1_048_576,
                pending(),
            )
            .await
            .map_err(|_| Error::Proof)?;
        let binding = proved.contract_binding().ok_or(Error::State)?;
        let current_state = binding.current_state_bytes().ok_or(Error::State)?.to_vec();

        let mut provider = cache.provider.clone();
        provider.expected_data = zswap::ZSWAP_EXPECTED_FILES.to_vec();
        let resolver = ZswapResolver(provider);
        let randomness = offer.binding_randomness();
        let (_, offer) = offer
            .prove(
                builtin_zkir::LocalProvingProvider {
                    rng: rng.split(),
                    resolver: &resolver,
                    params: &resolver,
                },
                GUARANTEED_SEGMENT,
            )
            .await
            .map_err(|_| Error::Proof)?;
        self.shielded_receive = Some(BookedOffer {
            offer,
            randomness,
            address,
            commitment,
            index,
            current_state,
        });
        let expected = &self.shielded_receive.as_ref().ok_or(Error::State)?.offer;
        let bound = BoundTransaction::prepare_shielded_receive(
            proved.native(),
            expected,
            policy,
            self.node,
            &self,
            signer,
        )
        .await
        .map_err(|_| Error::State)?;
        check(
            bound.expected_state() == binding.expected_state(),
            Error::State,
        )?;
        Ok((bound, binding.clone()))
    }
}

#[cfg(all(test, feature = "zkir-321"))]
mod tests {
    use super::*;
    use crate::{
        Plan,
        artifacts::{self, ContractBundleSet, Role},
        client::{ChainAdapter, FinalizedReceipt, NetworkPolicy, Submission},
        funding::{CONTRACT_SEGMENT, FeePolicy, SealedTransaction, UnsealedTransaction},
        localnet::{ExplicitSeal, Node, native_decode},
        proof::WitnessContractTarget,
        zkir::IrSource,
    };
    use anyhow::{Context, Result, ensure};
    use base_crypto::fab::AlignedValue;
    use coin_structure::transfer::{Recipient, SenderEvidence};
    use ledger::structure::Transaction;
    use onchain_runtime::state::{ContractState, StateValue};
    use rand::{SeedableRng, rngs::OsRng};
    use serde_json::json;
    use std::{
        borrow::Cow,
        env,
        path::Path,
        thread,
        time::{Duration, Instant},
    };
    use storage::arena::Sp;
    use transient_crypto::{
        merkle_tree::MerkleTreeCollapsedUpdate,
        proofs::{Proof, Zkir},
    };
    use zswap::{Offer, keys::SecretKeys, local::State as WalletState};

    async fn finalize(node: &Node, bound: &BoundTransaction) -> Result<FinalizedReceipt> {
        let sent = node
            .submit(bound)
            .await
            .map_err(|_| anyhow::anyhow!("submit failed"))?;
        ensure!(sent != Submission::Rejected, "node rejected transaction");
        let deadline = Instant::now() + Duration::from_secs(60);
        loop {
            if let Some(receipt) = node.finalized_receipt(bound)? {
                bound.check_receipt(&receipt)?;
                return Ok(receipt);
            }
            ensure!(
                Instant::now() < deadline,
                "finalized receipt did not arrive"
            );
            thread::sleep(Duration::from_millis(500));
        }
    }

    fn offer_from_bound(bound: &BoundTransaction) -> Result<Offer<Proof, Db>> {
        let sealed: SealedTransaction = serialize::tagged_deserialize(bound.bytes())?;
        let Transaction::Standard(transaction) = sealed else {
            anyhow::bail!("expected a standard transaction")
        };
        transaction
            .guaranteed_coins
            .as_deref()
            .cloned()
            .context("missing guaranteed shielded offer")
    }

    fn assert_nested_qualified_coin_owners_empty(
        state_bytes: &[u8],
        plan: &Plan,
        selected_owner: &[u8; 32],
        other_owner: &[u8; 32],
    ) -> Result<()> {
        use anyhow::ensure;

        let state: ContractState<Db> = native_decode(state_bytes)?;
        let StateValue::Array(slots) = state.data.get_ref() else {
            anyhow::bail!("expected initialized nested collection state slots");
        };
        let slot = |name: &str| {
            plan.state
                .iter()
                .position(|declaration| declaration.name == name)
                .with_context(|| format!("{name} state slot missing from plan"))
        };
        let owners = [
            AlignedValue::from(*selected_owner),
            AlignedValue::from(*other_owner),
        ];
        let set_slot = slot("coinSets")?;
        let Some(StateValue::Map(set_owners)) = slots.get(set_slot) else {
            anyhow::bail!("expected initialized owner Set map");
        };
        ensure!(
            set_owners.size() == 2,
            "initializer did not create both Set owners"
        );
        for owner in &owners {
            let Some(set) = set_owners.get(owner) else {
                anyhow::bail!("initializer omitted a Set owner");
            };
            let StateValue::Map(members) = &*set else {
                anyhow::bail!("expected initialized owner Set");
            };
            ensure!(members.size() == 0, "initialized owner Set is not empty");
        }

        let list_slot = slot("coinLists")?;
        let Some(StateValue::Map(list_owners)) = slots.get(list_slot) else {
            anyhow::bail!("expected initialized owner List map");
        };
        ensure!(
            list_owners.size() == 2,
            "initializer did not create both List owners"
        );
        for owner in &owners {
            let Some(list) = list_owners.get(owner) else {
                anyhow::bail!("initializer omitted a List owner");
            };
            let StateValue::Array(list) = &*list else {
                anyhow::bail!("expected initialized owner List");
            };
            ensure!(
                list.len() == 3
                    && matches!(list.get(0), Some(StateValue::Null))
                    && matches!(list.get(1), Some(StateValue::Null))
                    && matches!(list.get(2), Some(StateValue::Cell(length)) if **length == AlignedValue::from(0u64)),
                "initialized owner List is not empty"
            );
        }

        let root_map_slot = slot("rootCoinMap")?;
        let Some(StateValue::Map(root_coins)) = slots.get(root_map_slot) else {
            anyhow::bail!("expected initialized root qualified coin Map");
        };
        ensure!(root_coins.size() == 0, "initialized root coin Map is not empty");

        let coin_maps_slot = slot("coinMaps")?;
        let Some(StateValue::Map(coin_map_owners)) = slots.get(coin_maps_slot) else {
            anyhow::bail!("expected initialized owner-keyed qualified coin Map");
        };
        ensure!(
            coin_map_owners.size() == 2,
            "initializer did not create both qualified coin Map owners"
        );
        for owner in &owners {
            let Some(coins) = coin_map_owners.get(owner) else {
                anyhow::bail!("initializer omitted a qualified coin Map owner");
            };
            let StateValue::Map(coins) = &*coins else {
                anyhow::bail!("expected initialized owner qualified coin Map");
            };
            ensure!(coins.size() == 0, "initialized owner coin Map is not empty");
        }
        Ok(())
    }

    #[test]
    #[ignore = "requires a generated funded receive bundle and isolated development node"]
    fn funded_shielded_receive_localnet() -> Result<()> {
        futures::executor::block_on(async {
            let setting = |name| env::var(name).with_context(|| format!("missing {name}"));
            let nested_directory = env::var_os("NOCTIUM_NESTED_QUALIFIED_COIN_COLLECTIONS_BUNDLES");
            let nested_pins = env::var("NOCTIUM_NESTED_QUALIFIED_COIN_COLLECTIONS_MANIFESTS").ok();
            ensure!(
                nested_directory.is_some() == nested_pins.is_some(),
                "nested collection mode requires both nested bundle and manifest settings"
            );
            let nested = nested_directory.is_some();
            let root_bundle = if nested {
                None
            } else {
                Some(artifacts::verify(
                    Path::new(&setting("NOCTIUM_RECEIVE_BUNDLE")?),
                    Some(&setting("NOCTIUM_RECEIVE_MANIFEST_SHA256")?),
                )?)
            };
            let cache = ProofCache::new(
                setting("NOCTIUM_RECEIVE_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let policy = NetworkPolicy {
                network_id: "undeployed".into(),
                genesis: DEVELOPMENT_GENESIS.into(),
                spec_version: 2_001_100,
                transaction_version: 4,
                profile: crate::profile::NAME.into(),
                max_dust: 10u128.pow(22),
            };
            let node = Node::connect(
                &setting("NOCTIUM_RECEIVE_NODE")?,
                policy.clone(),
                Duration::from_secs(15),
                64 * 1024 * 1024,
                100_000,
            )?;
            let mut seed = [0; 32];
            seed[31] = 1;
            node.attach_dust_seed(&seed)?;
            let dust = cache.dust().await?;
            let dust_parameters = cache.parameters(dust.k()).await?;
            let ttl = node
                .sync()
                .context("replay the development ledger")?
                .block
                .tblock
                .to_secs()
                + 1800;
            let (target, operation, initializer, plan, circuit, parameters, initialize_parameters) =
                if nested {
                    let directory = Path::new(
                        nested_directory
                            .as_ref()
                            .expect("nested collection directory"),
                    );
                    let pins: BTreeMap<String, String> = serde_json::from_str(
                        nested_pins
                            .as_deref()
                            .expect("nested collection manifest pins"),
                    )?;
                    ensure!(
                        pins.len() == 2
                            && pins.contains_key("initializeOwners")
                            && pins.contains_key("tip"),
                        "nested collection manifest map must pin initializeOwners and tip"
                    );
                    let initialize_bundle = artifacts::verify(
                        &directory.join("initializeOwners"),
                        Some(&pins["initializeOwners"]),
                    )?;
                    let tip_bundle = artifacts::verify(&directory.join("tip"), Some(&pins["tip"]))?;
                    let initialize_circuit =
                        IrSource::load(initialize_bundle.file(Role::Circuit)?)?;
                    let tip_circuit = IrSource::load(tip_bundle.file(Role::Circuit)?)?;
                    let initialize_parameters = cache.parameters(initialize_circuit.k()).await?;
                    let parameters = cache.parameters(tip_circuit.k()).await?;
                    let state_config = br#"{"state":{"pot":[],"coinSets":[],"coinLists":[],"rootCoinMap":[],"coinMaps":[]}}"#;
                    let target = WitnessContractTarget::from_state_config(
                        ContractBundleSet::new(vec![initialize_bundle, tip_bundle])?,
                        state_config,
                        ttl,
                        &mut OsRng,
                    )?;
                    let initializer =
                        target.operation("initializeOwners", &initialize_parameters, ttl)?;
                    let operation = target.operation("tip", &parameters, ttl)?;
                    let plan: Plan = serde_json::from_slice(operation.bundle()?.file(Role::Plan)?)?;
                    (
                        target,
                        operation,
                        Some(initializer),
                        plan,
                        tip_circuit,
                        parameters,
                        Some(initialize_parameters),
                    )
                } else {
                    let bundle = root_bundle.expect("root receive bundle");
                    let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
                    let parameters = cache.parameters(circuit.k()).await?;
                    let zero_bytes = json!({"kind":"bytes", "values": vec![0; 32]});
                    let state_config = serde_json::to_vec(&json!({"state": {
                        "pot": [],
                        "held": {
                            "nonce": zero_bytes.clone(),
                            "color": zero_bytes,
                            "value": "0",
                            "mtIndex": "0"
                        },
                        "registry": [],
                        "coinList": []
                    }}))?;
                    let target = WitnessContractTarget::from_state_config(
                        ContractBundleSet::new(vec![bundle])?,
                        &state_config,
                        ttl,
                        &mut OsRng,
                    )?;
                    let operation = target.operation("tip", &parameters, ttl)?;
                    let plan: Plan = serde_json::from_slice(operation.bundle()?.file(Role::Plan)?)?;
                    (target, operation, None, plan, circuit, parameters, None)
                };
            let make_funding = || {
                DevelopmentFunding::new(
                    &node,
                    &dust,
                    &dust_parameters,
                    FeePolicy {
                        max_dust: policy.max_dust,
                        margin_blocks: 3,
                        max_spends: 8,
                    },
                    StdRng::from_entropy(),
                )
            };
            let approve = |_: &UnsealedTransaction, candidate: &NetworkPolicy| *candidate == policy;
            let signer = ExplicitSeal::new(approve, StdRng::from_entropy());
            let (_, deploy) = target
                .deployment_intent()
                .prove(
                    CONTRACT_SEGMENT,
                    builtin_zkir::LocalProvingProvider {
                        rng: StdRng::from_entropy(),
                        resolver: &dust,
                        params: &dust_parameters,
                    },
                    &node.sync()?.state.parameters.cost_model.runtime_cost_model,
                )
                .await
                .map_err(|error| anyhow::anyhow!("{error:?}"))?;
            let deploy =
                BoundTransaction::prepare(&deploy, policy.clone(), &node, &make_funding(), &signer)
                    .await
                    .context("fund the receive deployment")?;
            let deployed = finalize(&node, &deploy)
                .await
                .context("finalize the receive deployment")?;
            let deployment_entry = if nested { "initializeOwners" } else { "tip" };
            let mut current = Some(
                target
                    .deployment_binding(deployment_entry)?
                    .admit_committed_state(
                        &deployed.contract_state,
                        deploy.expected_state(),
                        &deployed.finalized_hash,
                        true,
                    )?,
            );
            let selected_owner = [1u8; 32];
            let other_owner = [2u8; 32];
            let mut before_funded_call = deployed.contract_state.clone();
            let initialization_observation = if let Some(initializer) = &initializer {
                let initialize_parameters = initialize_parameters
                    .as_ref()
                    .context("nested initializer parameters missing")?;
                let initialize_inputs = BTreeMap::from([
                    (
                        "selectedOwner".into(),
                        json!({"kind":"bytes", "values": selected_owner}),
                    ),
                    (
                        "otherOwner".into(),
                        json!({"kind":"bytes", "values": other_owner}),
                    ),
                ]);
                let proved = initializer
                    .prepare_call(
                        &mut current,
                        initialize_parameters,
                        initialize_inputs,
                        &mut OsRng,
                    )?
                    .prove(
                        &LocalProver::new(StdRng::from_entropy()),
                        initialize_parameters,
                        1_048_576,
                        futures::future::pending(),
                    )
                    .await?;
                let initialize_signer = ExplicitSeal::new(approve, StdRng::from_entropy());
                let bound = BoundTransaction::prepare(
                    proved.native(),
                    policy.clone(),
                    &node,
                    &make_funding(),
                    &initialize_signer,
                )
                .await
                .context("fund the owner initializer")?;
                let receipt = finalize(&node, &bound)
                    .await
                    .context("finalize the owner initializer")?;
                assert_nested_qualified_coin_owners_empty(
                    &receipt.contract_state,
                    &plan,
                    &selected_owner,
                    &other_owner,
                )?;
                before_funded_call = receipt.contract_state.clone();
                current = Some(
                    proved
                        .contract_binding()
                        .context("initializer proof omitted its contract binding")?
                        .admit_committed_state(
                            &receipt.contract_state,
                            bound.expected_state(),
                            &receipt.finalized_hash,
                            false,
                        )?,
                );
                Some(json!({
                    "height": receipt.height,
                    "blockHash": receipt.finalized_hash,
                    "transactionId": receipt.transaction_id,
                    "stateSha256": artifacts::digest(&receipt.contract_state),
                    "selectedOwner": hex::encode(selected_owner),
                    "otherOwner": hex::encode(other_owner),
                    "bothOwnersInitialized": true
                }))
            } else {
                None
            };
            let address = ContractAddress(HashOutput(
                hex::decode(target.contract_address())?
                    .try_into()
                    .map_err(|_| anyhow::anyhow!("wrong contract address size"))?,
            ));
            let domain = HashOutput([3; 32]);
            let public_key = [4u8; 32];
            let coin = Info::new(&mut OsRng, 5, address.custom_shielded_token_type(domain));
            let snapshot = node.sync()?;
            let expected_index = snapshot.state.zswap.first_free;
            let commitment = coin.commitment(&Recipient::Contract(address));
            let inputs = || {
                let mut values = BTreeMap::from([
                    ("domain".into(), json!({"kind":"bytes", "values":domain.0})),
                    (
                        "nonce".into(),
                        json!({"kind":"bytes", "values":coin.nonce.0.0}),
                    ),
                    (
                        "color".into(),
                        json!({"kind":"bytes", "values":coin.type_.0.0}),
                    ),
                ]);
                if nested {
                    values.insert(
                        "owner".into(),
                        json!({"kind":"bytes", "values":selected_owner}),
                    );
                    values.insert(
                        "key".into(),
                        json!({"kind":"bytes", "values":public_key}),
                    );
                }
                values
            };
            let mut absent = current;
            ensure!(
                operation
                    .prepare_call(&mut absent, &parameters, inputs(), &mut OsRng)
                    .is_err(),
                "receive without offer prepared"
            );
            let current = absent.context("missing offer consumed the current state")?;
            let other_coin = Info::new(&mut OsRng, coin.value, coin.type_);
            let signer = ExplicitSeal::new(approve, StdRng::from_entropy());
            ensure!(
                make_funding()
                    .bind_minted_shielded_receive(
                        &operation,
                        &current,
                        inputs(),
                        &other_coin,
                        &parameters,
                        &cache,
                        &signer,
                        StdRng::from_entropy(),
                    )
                    .await
                    .is_err(),
                "mismatched offer bound a transaction"
            );
            ensure!(
                node.finalized_contract_state(target.contract_address())?
                    .bytes
                    == before_funded_call,
                "invalid offer changed the Map"
            );
            let bound = make_funding()
                .bind_minted_shielded_receive(
                    &operation,
                    &current,
                    inputs(),
                    &coin,
                    &parameters,
                    &cache,
                    &signer,
                    StdRng::from_entropy(),
                )
                .await
                .context("fund the shielded mint and write")?;
            let receipt = finalize(&node, &bound)
                .await
                .context("finalize the shielded mint and write")?;
            let finalized = node.sync()?;
            let finalized_output = finalized
                .state
                .zswap
                .coin_coms
                .index(expected_index)
                .context("finalized minted output leaf missing")?;
            ensure!(
                finalized_output.0 == commitment.0
                    && finalized_output.1.as_deref() == Some(&address),
                "finalized Zswap leaf does not match the contract-owned mint"
            );
            let finalized_index = expected_index;
            let finalized_contract = node.finalized_contract_state(target.contract_address())?;
            ensure!(
                finalized_contract.bytes == receipt.contract_state,
                "finalized contract state differs from the call receipt"
            );
            let state: ContractState<Db> = native_decode(&finalized_contract.bytes)?;
            let StateValue::Array(slots) = state.data.get_ref() else {
                anyhow::bail!("expected native state array");
            };
            let slot = |name: &str| {
                plan.state
                    .iter()
                    .position(|declaration| declaration.name == name)
                    .with_context(|| format!("{name} state slot missing from plan"))
            };
            let map_slot = slot("pot")?;
            let Some(StateValue::Map(coins)) = slots.get(map_slot) else {
                anyhow::bail!("expected coin Map");
            };
            let qualified = AlignedValue::from(coin.qualify(finalized_index));
            ensure!(
                qualified.alignment.fits(&qualified.value),
                "qualified coin does not fit the Set key alignment"
            );
            ensure!(
                coins.get(&AlignedValue::from(coin.nonce)).as_deref()
                    == Some(&StateValue::Cell(Sp::new(AlignedValue::from(
                        coin.qualify(finalized_index)
                    )))),
                "finalized Map does not contain the Ledger-assigned qualified coin"
            );
            if nested {
                let selected_key = AlignedValue::from(selected_owner);
                let other_key = AlignedValue::from(other_owner);
                let set_slot = slot("coinSets")?;
                let list_slot = slot("coinLists")?;
                let Some(StateValue::Map(set_owners)) = slots.get(set_slot) else {
                    anyhow::bail!("expected owner-keyed qualified coin Set");
                };
                ensure!(
                    set_owners.size() == 2,
                    "qualified coin Set owner buckets differ"
                );
                let Some(selected_set) = set_owners.get(&selected_key) else {
                    anyhow::bail!("selected owner is missing from the qualified coin Set");
                };
                let StateValue::Map(selected_members) = &*selected_set else {
                    anyhow::bail!("expected selected owner's qualified coin Set");
                };
                ensure!(
                    selected_members.size() == 1
                        && matches!(selected_members.get(&qualified), Some(marker) if matches!(*marker, StateValue::Null)),
                    "selected owner Set does not contain the Ledger-assigned qualified coin"
                );
                let Some(other_set) = set_owners.get(&other_key) else {
                    anyhow::bail!("other owner is missing from the qualified coin Set");
                };
                let StateValue::Map(other_members) = &*other_set else {
                    anyhow::bail!("expected other owner's qualified coin Set");
                };
                ensure!(
                    other_members.size() == 0,
                    "qualified coin leaked into other owner Set"
                );

                let root_map_slot = slot("rootCoinMap")?;
                let Some(StateValue::Map(root_coins)) = slots.get(root_map_slot) else {
                    anyhow::bail!("expected finalized root qualified coin Map");
                };
                let public_key = AlignedValue::from(public_key);
                ensure!(
                    root_coins.size() == 1
                        && root_coins.get(&public_key).as_deref()
                            == Some(&StateValue::Cell(Sp::new(qualified.clone()))),
                    "root Map does not contain the Ledger-assigned qualified coin under the public key"
                );

                let coin_maps_slot = slot("coinMaps")?;
                let Some(StateValue::Map(coin_map_owners)) = slots.get(coin_maps_slot) else {
                    anyhow::bail!("expected owner-keyed finalized qualified coin Map");
                };
                ensure!(
                    coin_map_owners.size() == 2,
                    "qualified coin Map owner buckets differ"
                );
                let Some(selected_coin_map) = coin_map_owners.get(&selected_key) else {
                    anyhow::bail!("selected owner is missing from the qualified coin Map");
                };
                let StateValue::Map(selected_coins) = &*selected_coin_map else {
                    anyhow::bail!("expected selected owner's qualified coin Map");
                };
                ensure!(
                    selected_coins.size() == 1
                        && selected_coins.get(&public_key).as_deref()
                            == Some(&StateValue::Cell(Sp::new(qualified.clone()))),
                    "selected owner Map does not contain the Ledger-assigned qualified coin under the public key"
                );
                let Some(other_coin_map) = coin_map_owners.get(&other_key) else {
                    anyhow::bail!("other owner is missing from the qualified coin Map");
                };
                let StateValue::Map(other_coins) = &*other_coin_map else {
                    anyhow::bail!("expected other owner's qualified coin Map");
                };
                ensure!(other_coins.size() == 0, "qualified coin leaked into other owner Map");

                let Some(StateValue::Map(list_owners)) = slots.get(list_slot) else {
                    anyhow::bail!("expected owner-keyed qualified coin List");
                };
                ensure!(
                    list_owners.size() == 2,
                    "qualified coin List owner buckets differ"
                );
                let Some(selected_list) = list_owners.get(&selected_key) else {
                    anyhow::bail!("selected owner is missing from the qualified coin List");
                };
                let StateValue::Array(coin_list) = &*selected_list else {
                    anyhow::bail!("expected selected owner's qualified coin List");
                };
                ensure!(
                    coin_list.len() == 3,
                    "invalid selected qualified coin List node"
                );
                let Some(StateValue::Cell(list_head)) = coin_list.get(0) else {
                    anyhow::bail!("expected selected qualified coin List head");
                };
                ensure!(
                    **list_head == qualified,
                    "selected List head differs from the Ledger-assigned qualified coin"
                );
                let Some(StateValue::Array(list_tail)) = coin_list.get(1) else {
                    anyhow::bail!("expected selected qualified coin List tail");
                };
                ensure!(
                    list_tail.len() == 3
                        && matches!(list_tail.get(0), Some(StateValue::Null))
                        && matches!(list_tail.get(1), Some(StateValue::Null))
                        && matches!(list_tail.get(2), Some(StateValue::Cell(length)) if **length == AlignedValue::from(0u64)),
                    "selected qualified coin List has unexpected tail entries"
                );
                let Some(StateValue::Cell(list_length)) = coin_list.get(2) else {
                    anyhow::bail!("expected selected qualified coin List length");
                };
                ensure!(
                    **list_length == AlignedValue::from(1u64),
                    "selected qualified coin List must contain one value"
                );
                let Some(other_list) = list_owners.get(&other_key) else {
                    anyhow::bail!("other owner is missing from the qualified coin List");
                };
                let StateValue::Array(other_list) = &*other_list else {
                    anyhow::bail!("expected other owner's qualified coin List");
                };
                ensure!(
                    other_list.len() == 3
                        && matches!(other_list.get(0), Some(StateValue::Null))
                        && matches!(other_list.get(1), Some(StateValue::Null))
                        && matches!(other_list.get(2), Some(StateValue::Cell(length)) if **length == AlignedValue::from(0u64)),
                    "qualified coin leaked into other owner List"
                );
            } else {
                let cell_slot = slot("held")?;
                let set_slot = slot("registry")?;
                let list_slot = slot("coinList")?;
                let Some(StateValue::Cell(stored_cell)) = slots.get(cell_slot) else {
                    anyhow::bail!("expected qualified coin Cell");
                };
                ensure!(
                    &**stored_cell == &qualified,
                    "finalized Cell does not contain the Ledger-assigned qualified coin"
                );
                let Some(StateValue::Map(coin_set)) = slots.get(set_slot) else {
                    anyhow::bail!("expected qualified coin Set");
                };
                ensure!(
                    matches!(coin_set.get(&qualified), Some(marker) if matches!(*marker, StateValue::Null)),
                    "finalized Set does not contain the Ledger-assigned qualified coin"
                );
                let Some(StateValue::Array(coin_list)) = slots.get(list_slot) else {
                    anyhow::bail!("expected qualified coin List");
                };
                ensure!(coin_list.len() == 3, "invalid qualified coin List node");
                let Some(StateValue::Cell(list_head)) = coin_list.get(0) else {
                    anyhow::bail!("expected qualified coin List head");
                };
                ensure!(
                    **list_head == qualified,
                    "finalized List head does not contain the Ledger-assigned qualified coin"
                );
                let Some(StateValue::Array(list_tail)) = coin_list.get(1) else {
                    anyhow::bail!("expected qualified coin List tail");
                };
                ensure!(
                    list_tail.len() == 3
                        && matches!(list_tail.get(0), Some(StateValue::Null))
                        && matches!(list_tail.get(1), Some(StateValue::Null))
                        && matches!(list_tail.get(2), Some(StateValue::Cell(length)) if **length == AlignedValue::from(0u64)),
                    "qualified coin List contains unexpected tail entries"
                );
                let Some(StateValue::Cell(list_length)) = coin_list.get(2) else {
                    anyhow::bail!("expected qualified coin List length");
                };
                ensure!(
                    **list_length == AlignedValue::from(1u64),
                    "qualified coin List does not contain exactly one value"
                );
            }
            ensure!(
                finalized
                    .state
                    .zswap
                    .coin_coms_set
                    .contains_key(&commitment)
            );
            let mut evidence = json!({
                "deploymentHeight": deployed.height,
                "deploymentBlockHash": deployed.finalized_hash,
                "deploymentTransaction": deployed.transaction_id,
                "callHeight": receipt.height,
                "callTransaction": receipt.transaction_id,
                "finalizedBlockHash": receipt.finalized_hash,
                "contractAddress": receipt.contract_address,
                "commitment": hex::encode(commitment.0.0),
                "nonce": hex::encode(coin.nonce.0.0),
                "color": hex::encode(coin.type_.0.0),
                "value": coin.value.to_string(),
                "mtIndex": finalized_index,
                "mapCoinMatchesFinalizedOutput": true,
                "stateSha256": artifacts::digest(&finalized_contract.bytes),
                "initialization": initialization_observation,
                "k": circuit.k(),
                "rejected": ["missingOffer", "mismatchedOffer"]
            });
            if nested {
                evidence["selectedOwner"] = json!(hex::encode(selected_owner));
                evidence["otherOwner"] = json!(hex::encode(other_owner));
                evidence["nestedSetMatchesFinalizedOutput"] = json!(true);
                evidence["nestedListHeadMatchesFinalizedOutput"] = json!(true);
                evidence["otherOwnerSetEmpty"] = json!(true);
                evidence["otherOwnerListEmpty"] = json!(true);
                evidence["rootCoinMapMatchesFinalizedOutput"] = json!(true);
                evidence["nestedCoinMapMatchesFinalizedOutput"] = json!(true);
                evidence["otherOwnerCoinMapEmpty"] = json!(true);
                evidence["mapKey"] = json!(hex::encode(public_key));
            } else {
                evidence["cellCoinMatchesFinalizedOutput"] = json!(true);
                evidence["setCoinMatchesFinalizedOutput"] = json!(true);
                evidence["listCoinHeadMatchesFinalizedOutput"] = json!(true);
            }
            println!("{evidence}");
            Ok(())
        })
    }

    #[test]
    #[ignore = "requires one generated wallet-mint bundle and an isolated development node"]
    fn funded_shielded_wallet_mint_localnet() -> Result<()> {
        futures::executor::block_on(async {
            let setting = |name| env::var(name).with_context(|| format!("missing {name}"));
            let bundle = artifacts::verify(
                Path::new(&setting("NOCTIUM_WALLET_MINT_BUNDLE")?),
                Some(&setting("NOCTIUM_WALLET_MINT_MANIFEST_SHA256")?),
            )?;
            let bundle_manifest_sha256 = bundle
                .authenticated_manifest_sha256()
                .unwrap_or_default()
                .to_owned();
            let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
            let cache = ProofCache::new(
                setting("NOCTIUM_WALLET_MINT_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let policy = NetworkPolicy {
                network_id: "undeployed".into(),
                genesis: DEVELOPMENT_GENESIS.into(),
                spec_version: 2_001_100,
                transaction_version: 4,
                profile: crate::profile::NAME.into(),
                max_dust: 10u128.pow(22),
            };
            let node = Node::connect(
                &setting("NOCTIUM_WALLET_MINT_NODE")?,
                policy.clone(),
                Duration::from_secs(15),
                64 * 1024 * 1024,
                10_000,
            )?;
            let mut seed = [0; 32];
            seed[31] = 1;
            node.attach_dust_seed(&seed)?;
            let dust = cache.dust().await?;
            let dust_parameters = cache.parameters(dust.k()).await?;
            let parameters = cache.parameters(circuit.k()).await?;
            let ttl = node.sync()?.block.tblock.to_secs() + 1800;
            let zero_bytes = json!({"kind": "bytes", "values": vec![0; 32]});
            let state_config = serde_json::to_vec(&json!({"state": {
                "minted": {
                    "nonce": zero_bytes.clone(),
                    "color": zero_bytes,
                    "value": "0",
                    "mtIndex": "0"
                }
            }}))?;
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![bundle])?,
                &state_config,
                ttl,
                &mut OsRng,
            )?;
            let operation = target.operation("mintToWallet", &parameters, ttl)?;
            let make_funding = || {
                DevelopmentFunding::new(
                    &node,
                    &dust,
                    &dust_parameters,
                    FeePolicy {
                        max_dust: policy.max_dust,
                        margin_blocks: 3,
                        max_spends: 8,
                    },
                    StdRng::from_entropy(),
                )
            };
            let approve = |_: &UnsealedTransaction, candidate: &NetworkPolicy| *candidate == policy;
            let make_signer = || ExplicitSeal::new(approve, StdRng::from_entropy());
            let (_, deploy) = target
                .deployment_intent()
                .prove(
                    CONTRACT_SEGMENT,
                    builtin_zkir::LocalProvingProvider {
                        rng: StdRng::from_entropy(),
                        resolver: &dust,
                        params: &dust_parameters,
                    },
                    &node.sync()?.state.parameters.cost_model.runtime_cost_model,
                )
                .await
                .map_err(|error| anyhow::anyhow!("{error:?}"))?;
            let deploy = BoundTransaction::prepare(
                &deploy,
                policy.clone(),
                &node,
                &make_funding(),
                &make_signer(),
            )
            .await?;
            let deployed = finalize(&node, &deploy).await?;
            let current = target
                .deployment_binding("mintToWallet")?
                .admit_committed_state(
                    &deployed.contract_state,
                    deploy.expected_state(),
                    &deployed.finalized_hash,
                    true,
                )?;
            let address_bytes = hex::decode(
                target
                    .contract_address()
                    .strip_prefix("0x")
                    .unwrap_or(target.contract_address()),
            )?;
            let address = ContractAddress(HashOutput(
                address_bytes
                    .try_into()
                    .map_err(|_| anyhow::anyhow!("wrong contract address size"))?,
            ));
            let mut rng = StdRng::from_entropy();
            let domain = HashOutput([0x3d; 32]);
            let coin = Info::new(&mut rng, 5, address.custom_shielded_token_type(domain));
            let wallet_keys = SecretKeys::from_rng_seed(&mut rng);
            let recipient = wallet_keys.coin_public_key();
            let encryption_key = wallet_keys.enc_public_key();
            let before_call = node.sync()?;
            let expected_index = before_call.state.zswap.first_free;
            let mut wallet_state = WalletState::<Db>::new();
            if expected_index > 0 {
                let update = MerkleTreeCollapsedUpdate::new(
                    &before_call.state.zswap.coin_coms,
                    0,
                    expected_index - 1,
                )
                .context("build initial wallet Merkle sync")?;
                wallet_state = wallet_state
                    .apply_collapsed_update(&update)
                    .context("apply initial wallet Merkle sync")?;
            }
            let inputs = || {
                BTreeMap::from([
                    (
                        "domain".into(),
                        json!({"kind": "bytes", "values": domain.0}),
                    ),
                    (
                        "nonce".into(),
                        json!({"kind": "bytes", "values": coin.nonce.0.0}),
                    ),
                    ("amount".into(), json!(coin.value.to_string())),
                    (
                        "recipient".into(),
                        json!({"kind": "bytes", "values": recipient.0.0}),
                    ),
                ])
            };

            let current_state_before = node
                .finalized_contract_state(target.contract_address())?
                .bytes;
            let changed_recipient = PublicKey(HashOutput([0xa7; 32]));
            ensure!(
                make_funding()
                    .bind_minted_shielded_wallet(
                        &operation,
                        &current,
                        inputs(),
                        &coin,
                        changed_recipient,
                        encryption_key,
                        &parameters,
                        &cache,
                        &make_signer(),
                        StdRng::from_entropy(),
                    )
                    .await
                    .is_err(),
                "changed recipient bound a wallet mint"
            );
            ensure!(
                node.finalized_contract_state(target.contract_address())?
                    .bytes
                    == current_state_before,
                "recipient mismatch changed contract state"
            );

            let (bound, binding) = make_funding()
                .bind_minted_shielded_wallet_with_binding(
                    &operation,
                    &current,
                    inputs(),
                    &coin,
                    recipient,
                    encryption_key,
                    &parameters,
                    &cache,
                    &make_signer(),
                    StdRng::from_entropy(),
                )
                .await
                .context("bind shielded wallet mint")?;
            let receipt = finalize(&node, &bound)
                .await
                .context("finalize shielded wallet mint")?;
            let offer = offer_from_bound(&bound)?;
            ensure!(
                offer.inputs.is_empty() && offer.outputs.len() == 1 && offer.transient.is_empty(),
                "wallet mint offer has unexpected inputs, outputs or transients"
            );
            let commitment = coin.commitment(&Recipient::User(recipient));
            let Some(offer_output) = offer.outputs.get(0) else {
                anyhow::bail!("minted wallet output is missing")
            };
            ensure!(
                offer_output.coin_com == commitment
                    && offer_output.contract_address.is_none()
                    && offer_output.ciphertext.is_some(),
                "minted offer differs from the proof-bound wallet coin"
            );
            let final_snapshot = node.sync()?;
            let (leaf, owner) = final_snapshot
                .state
                .zswap
                .coin_coms
                .index(expected_index)
                .context("finalized user output leaf missing")?;
            ensure!(
                leaf == commitment.0 && owner.is_none(),
                "finalized output commitment or user ownership mismatch"
            );
            ensure!(
                final_snapshot
                    .state
                    .zswap
                    .coin_coms_set
                    .contains_key(&commitment),
                "finalized user output commitment is missing"
            );

            let finalized_contract = node.finalized_contract_state(target.contract_address())?;
            ensure!(
                finalized_contract.bytes == receipt.contract_state,
                "finalized contract state differs from the mint receipt"
            );
            let state: ContractState<Db> = native_decode(&finalized_contract.bytes)?;
            let StateValue::Array(slots) = state.data.get_ref() else {
                anyhow::bail!("expected root state array")
            };
            let Some(StateValue::Cell(stored)) = slots.get(0) else {
                anyhow::bail!("expected minted coin Cell")
            };
            let qualified = AlignedValue::from(coin.qualify(expected_index));
            ensure!(
                &**stored == &qualified,
                "finalized Cell differs from the wallet output index"
            );

            wallet_state = wallet_state
                .apply(&wallet_keys, &offer)
                .context("apply minted user output to wallet state")?;
            let nullifier = coin.nullifier(&SenderEvidence::User(Cow::Borrowed(
                &wallet_keys.coin_secret_key,
            )));
            let wallet_coin = wallet_state
                .coins
                .get(&nullifier)
                .map(|coin| *coin)
                .context("minted coin is missing from wallet state")?;
            ensure!(
                wallet_coin == coin.qualify(expected_index),
                "wallet state returned the wrong coin or index"
            );

            let current_after_mint = binding.admit_committed_state(
                &receipt.contract_state,
                bound.expected_state(),
                &receipt.finalized_hash,
                false,
            )?;
            ensure!(
                make_funding()
                    .bind_minted_shielded_wallet(
                        &operation,
                        &current_after_mint,
                        inputs(),
                        &coin,
                        recipient,
                        encryption_key,
                        &parameters,
                        &cache,
                        &make_signer(),
                        StdRng::from_entropy(),
                    )
                    .await
                    .is_err(),
                "replayed wallet mint was accepted"
            );
            ensure!(
                node.finalized_contract_state(target.contract_address())?
                    .bytes
                    == receipt.contract_state,
                "replayed wallet mint changed contract state"
            );

            println!(
                "{}",
                json!({
                    "entrypoint": "mintToWallet",
                    "deploymentHeight": deployed.height,
                    "callHeight": receipt.height,
                    "callTransaction": receipt.transaction_id,
                    "contractAddress": receipt.contract_address,
                    "domain": hex::encode(domain.0),
                    "nonce": hex::encode(coin.nonce.0.0),
                    "color": hex::encode(coin.type_.0.0),
                    "value": coin.value.to_string(),
                    "recipient": hex::encode(recipient.0.0),
                    "commitment": hex::encode(commitment.0.0),
                    "mtIndex": expected_index,
                    "finalizedOutputMatchesWalletCoin": true,
                    "walletStateMatchesMintedCoin": true,
                    "cellMatchesFinalizedOutput": true,
                    "changedRecipientRejectedBeforeSubmit": true,
                    "replayRejectedBeforeSubmit": true,
                    "k": circuit.k(),
                    "bundleManifestSha256": bundle_manifest_sha256,
                    "rejected": ["changedRecipient", "replay"]
                })
            );
            Ok(())
        })
    }

    #[test]
    #[ignore = "requires generated receive and whole-spend bundles and an isolated development node"]
    fn funded_wallet_shielded_receive_localnet() -> Result<()> {
        futures::executor::block_on(async {
            let setting = |name| env::var(name).with_context(|| format!("missing {name}"));
            let deposit_bundle = artifacts::verify(
                Path::new(&setting("NOCTIUM_WALLET_RECEIVE_DEPOSIT_BUNDLE")?),
                Some(&setting("NOCTIUM_WALLET_RECEIVE_DEPOSIT_MANIFEST_SHA256")?),
            )?;
            let seed_tip_bundle = artifacts::verify(
                Path::new(&setting("NOCTIUM_WALLET_RECEIVE_SEED_TIP_BUNDLE")?),
                Some(&setting("NOCTIUM_WALLET_RECEIVE_SEED_TIP_MANIFEST_SHA256")?),
            )?;
            let seed_spend_bundle = artifacts::verify(
                Path::new(&setting("NOCTIUM_WALLET_RECEIVE_SEED_SPEND_BUNDLE")?),
                Some(&setting(
                    "NOCTIUM_WALLET_RECEIVE_SEED_SPEND_MANIFEST_SHA256",
                )?),
            )?;
            let deposit_circuit = IrSource::load(deposit_bundle.file(Role::Circuit)?)?;
            let seed_tip_circuit = IrSource::load(seed_tip_bundle.file(Role::Circuit)?)?;
            let seed_spend_circuit = IrSource::load(seed_spend_bundle.file(Role::Circuit)?)?;
            let cache = ProofCache::new(
                setting("NOCTIUM_WALLET_RECEIVE_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let policy = NetworkPolicy {
                network_id: "undeployed".into(),
                genesis: DEVELOPMENT_GENESIS.into(),
                spec_version: 2_001_100,
                transaction_version: 4,
                profile: crate::profile::NAME.into(),
                max_dust: 10u128.pow(22),
            };
            let node = Node::connect(
                &setting("NOCTIUM_WALLET_RECEIVE_NODE")?,
                policy.clone(),
                Duration::from_secs(15),
                64 * 1024 * 1024,
                10_000,
            )?;
            let mut dust_seed = [0; 32];
            dust_seed[31] = 1;
            node.attach_dust_seed(&dust_seed)?;
            let dust = cache.dust().await?;
            let dust_parameters = cache.parameters(dust.k()).await?;
            let deposit_parameters = cache.parameters(deposit_circuit.k()).await?;
            let seed_tip_parameters = cache.parameters(seed_tip_circuit.k()).await?;
            let seed_spend_parameters = cache.parameters(seed_spend_circuit.k()).await?;
            let ttl = node.sync()?.block.tblock.to_secs() + 1800;
            let deposit_target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![deposit_bundle])?,
                br#"{"state":{"pot":[]}}"#,
                ttl,
                &mut OsRng,
            )?;
            let seed_target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![seed_tip_bundle, seed_spend_bundle])?,
                br#"{"state":{"pot":[]}}"#,
                ttl,
                &mut OsRng,
            )?;
            let deposit = deposit_target.operation("tip", &deposit_parameters, ttl)?;
            let seed_tip = seed_target.operation("tip", &seed_tip_parameters, ttl)?;
            let seed_spend = seed_target.operation("spend", &seed_spend_parameters, ttl)?;
            let make_funding = || {
                DevelopmentFunding::new(
                    &node,
                    &dust,
                    &dust_parameters,
                    FeePolicy {
                        max_dust: policy.max_dust,
                        margin_blocks: 3,
                        max_spends: 8,
                    },
                    StdRng::from_entropy(),
                )
            };
            let approve = |_: &UnsealedTransaction, candidate: &NetworkPolicy| *candidate == policy;
            let make_signer = || ExplicitSeal::new(approve, StdRng::from_entropy());

            let seed_snapshot = node.sync()?;
            let (_, seed_deploy_intent) = seed_target
                .deployment_intent()
                .prove(
                    CONTRACT_SEGMENT,
                    builtin_zkir::LocalProvingProvider {
                        rng: StdRng::from_entropy(),
                        resolver: &dust,
                        params: &dust_parameters,
                    },
                    &seed_snapshot.state.parameters.cost_model.runtime_cost_model,
                )
                .await
                .map_err(|error| anyhow::anyhow!("seed deployment proof: {error:?}"))?;
            let seed_deploy = BoundTransaction::prepare(
                &seed_deploy_intent,
                policy.clone(),
                &node,
                &make_funding(),
                &make_signer(),
            )
            .await?;
            let seed_deployed = finalize(&node, &seed_deploy)
                .await
                .context("finalize seed contract")?;
            let mut seed_current = seed_target
                .deployment_binding("tip")?
                .admit_committed_state(
                    &seed_deployed.contract_state,
                    seed_deploy.expected_state(),
                    &seed_deployed.finalized_hash,
                    true,
                )?;

            let deposit_snapshot = node.sync()?;
            let (_, deposit_deploy_intent) = deposit_target
                .deployment_intent()
                .prove(
                    CONTRACT_SEGMENT,
                    builtin_zkir::LocalProvingProvider {
                        rng: StdRng::from_entropy(),
                        resolver: &dust,
                        params: &dust_parameters,
                    },
                    &deposit_snapshot
                        .state
                        .parameters
                        .cost_model
                        .runtime_cost_model,
                )
                .await
                .map_err(|error| anyhow::anyhow!("deposit deployment proof: {error:?}"))?;
            let deposit_deploy = BoundTransaction::prepare(
                &deposit_deploy_intent,
                policy.clone(),
                &node,
                &make_funding(),
                &make_signer(),
            )
            .await?;
            let deposit_deployed = finalize(&node, &deposit_deploy)
                .await
                .context("finalize deposit contract")?;
            let deposit_current = deposit_target
                .deployment_binding("tip")?
                .admit_committed_state(
                    &deposit_deployed.contract_state,
                    deposit_deploy.expected_state(),
                    &deposit_deployed.finalized_hash,
                    true,
                )?;
            let seed_address = ContractAddress(HashOutput(
                hex::decode(
                    seed_target
                        .contract_address()
                        .strip_prefix("0x")
                        .unwrap_or(seed_target.contract_address()),
                )?
                .try_into()
                .map_err(|_| anyhow::anyhow!("wrong seed contract address size"))?,
            ));
            let deposit_address = ContractAddress(HashOutput(
                hex::decode(
                    deposit_target
                        .contract_address()
                        .strip_prefix("0x")
                        .unwrap_or(deposit_target.contract_address()),
                )?
                .try_into()
                .map_err(|_| anyhow::anyhow!("wrong deposit contract address size"))?,
            ));

            let mut shielded_rng = StdRng::from_entropy();
            let domain = HashOutput([0x42; 32]);
            let seed_coin = Info::new(
                &mut shielded_rng,
                5,
                seed_address.custom_shielded_token_type(domain),
            );
            let pre_seed_snapshot = node.sync()?;
            let seed_index = pre_seed_snapshot.state.zswap.first_free;
            let mut wallet_state = WalletState::<Db>::new();
            if seed_index > 0 {
                let update = MerkleTreeCollapsedUpdate::new(
                    &pre_seed_snapshot.state.zswap.coin_coms,
                    0,
                    seed_index - 1,
                )
                .context("build initial wallet Merkle sync")?;
                wallet_state = wallet_state
                    .apply_collapsed_update(&update)
                    .context("apply initial wallet Merkle sync")?;
            }
            let seed_tip_inputs = || {
                BTreeMap::from([
                    ("domain".into(), json!({"kind":"bytes", "values":domain.0})),
                    (
                        "nonce".into(),
                        json!({"kind":"bytes", "values":seed_coin.nonce.0.0}),
                    ),
                    (
                        "color".into(),
                        json!({"kind":"bytes", "values":seed_coin.type_.0.0}),
                    ),
                ])
            };
            let (seed_tip_bound, seed_tip_binding) = make_funding()
                .bind_minted_shielded_receive_with_binding(
                    &seed_tip,
                    &seed_current,
                    seed_tip_inputs(),
                    &seed_coin,
                    &seed_tip_parameters,
                    &cache,
                    &make_signer(),
                    StdRng::from_entropy(),
                )
                .await
                .context("bind whole-spend seed coin")?;
            let seed_tip_receipt = finalize(&node, &seed_tip_bound)
                .await
                .context("finalize whole-spend seed coin")?;
            seed_current = seed_tip_binding.admit_committed_state(
                &seed_tip_receipt.contract_state,
                seed_tip_bound.expected_state(),
                &seed_tip_receipt.finalized_hash,
                false,
            )?;

            let wallet_keys = SecretKeys::from_rng_seed(&mut shielded_rng);
            let wallet_public_key = wallet_keys.coin_public_key();
            let wallet_encryption_key = wallet_keys.enc_public_key();
            let wallet_output_index = node.sync()?.state.zswap.first_free;
            let spend_inputs = BTreeMap::from([
                (
                    "nonce".into(),
                    json!({"kind":"bytes", "values":seed_coin.nonce.0.0}),
                ),
                (
                    "recipient".into(),
                    json!({"kind":"bytes", "values":wallet_public_key.0.0}),
                ),
            ]);
            let seed_spend_bound = make_funding()
                .bind_shielded_map_spend(
                    &seed_spend,
                    &seed_current,
                    spend_inputs,
                    wallet_encryption_key,
                    &seed_spend_parameters,
                    &cache,
                    &make_signer(),
                    StdRng::from_entropy(),
                )
                .await
                .context("spend seed coin to ephemeral wallet")?;
            finalize(&node, &seed_spend_bound)
                .await
                .context("finalize seed spend")?;

            let seed_info = Info::from(&seed_coin.qualify(seed_index));
            let wallet_coin = seed_info.evolve_from(
                b"midnight:kernel:nonce_evolve",
                seed_coin.value,
                seed_coin.type_,
            );
            let tip_offer = offer_from_bound(&seed_tip_bound)?;
            let spend_offer = offer_from_bound(&seed_spend_bound)?;
            let wallet_state = wallet_state
                .apply(&wallet_keys, &tip_offer)
                .context("apply seed receive to ephemeral wallet state")?
                .apply(&wallet_keys, &spend_offer)
                .context("apply whole spend to ephemeral wallet state")?;
            let wallet_nullifier = wallet_coin.nullifier(&SenderEvidence::User(Cow::Borrowed(
                &wallet_keys.coin_secret_key,
            )));
            let wallet_qualified = wallet_state
                .coins
                .get(&wallet_nullifier)
                .map(|qualified| *qualified)
                .context("whole spend output missing from ephemeral wallet state")?;
            ensure!(
                wallet_qualified == wallet_coin.qualify(wallet_output_index),
                "wallet state assigned the wrong output index"
            );
            let (_, mismatched_input) = wallet_state
                .spend(
                    &mut shielded_rng,
                    &wallet_keys,
                    &wallet_qualified,
                    Some(GUARANTEED_SEGMENT),
                )
                .context("prepare mismatch input from ephemeral wallet")?;
            let mut mismatched_coin = wallet_coin;
            mismatched_coin.value += 1;
            ensure!(
                make_funding()
                    .bind_wallet_shielded_receive(
                        &deposit,
                        &deposit_current,
                        BTreeMap::from([
                            (
                                "nonce".into(),
                                json!({"kind":"bytes", "values":wallet_coin.nonce.0.0}),
                            ),
                            (
                                "color".into(),
                                json!({"kind":"bytes", "values":wallet_coin.type_.0.0}),
                            ),
                            ("amount".into(), json!(wallet_coin.value.to_string()),),
                        ]),
                        &mismatched_coin,
                        mismatched_input,
                        &deposit_parameters,
                        &cache,
                        &make_signer(),
                        StdRng::from_entropy(),
                    )
                    .await
                    .is_err(),
                "unequal-value wallet offer bound a receive"
            );
            ensure!(
                node.finalized_contract_state(deposit_target.contract_address())?
                    .bytes
                    == deposit_deployed.contract_state,
                "mismatched wallet offer changed the receive Map"
            );

            let (_, input) = wallet_state
                .spend(
                    &mut shielded_rng,
                    &wallet_keys,
                    &wallet_qualified,
                    Some(GUARANTEED_SEGMENT),
                )
                .context("prepare wallet input")?;
            let input_nullifier = input.nullifier;
            let receive_index = node.sync()?.state.zswap.first_free;
            let receive_commitment = wallet_coin.commitment(&Recipient::Contract(deposit_address));
            let inputs = || {
                BTreeMap::from([
                    (
                        "nonce".into(),
                        json!({"kind":"bytes", "values":wallet_coin.nonce.0.0}),
                    ),
                    (
                        "color".into(),
                        json!({"kind":"bytes", "values":wallet_coin.type_.0.0}),
                    ),
                    ("amount".into(), json!(wallet_coin.value.to_string())),
                ])
            };
            let bound = make_funding()
                .bind_wallet_shielded_receive(
                    &deposit,
                    &deposit_current,
                    inputs(),
                    &wallet_coin,
                    input,
                    &deposit_parameters,
                    &cache,
                    &make_signer(),
                    StdRng::from_entropy(),
                )
                .await
                .context("bind wallet-funded shielded receive")?;
            let receipt = finalize(&node, &bound)
                .await
                .context("finalize wallet-funded shielded receive")?;
            let state: ContractState<Db> = native_decode(&receipt.contract_state)?;
            let StateValue::Array(slots) = state.data.get_ref() else {
                anyhow::bail!("expected native receive state array")
            };
            let Some(StateValue::Map(coins)) = slots.get(0) else {
                anyhow::bail!("expected receive coin Map in slot 0")
            };
            ensure!(
                coins.get(&AlignedValue::from(wallet_coin.nonce)).as_deref()
                    == Some(&StateValue::Cell(Sp::new(AlignedValue::from(
                        wallet_coin.qualify(receive_index)
                    )))),
                "wallet receive Map entry lacks the Ledger-assigned output index"
            );
            let final_snapshot = node.sync()?;
            let (leaf, owner) = final_snapshot
                .state
                .zswap
                .coin_coms
                .index(receive_index)
                .context("wallet receive output leaf missing")?;
            ensure!(
                leaf == receive_commitment.0 && owner.as_deref() == Some(&deposit_address),
                "wallet receive output commitment has the wrong owner"
            );
            ensure!(
                final_snapshot
                    .state
                    .zswap
                    .nullifiers
                    .contains_key(&input_nullifier),
                "wallet input nullifier missing after finalization"
            );

            let (_, replayed_input) = wallet_state
                .spend(
                    &mut shielded_rng,
                    &wallet_keys,
                    &wallet_qualified,
                    Some(GUARANTEED_SEGMENT),
                )
                .context("prepare replay input")?;
            ensure!(
                make_funding()
                    .bind_wallet_shielded_receive(
                        &deposit,
                        &deposit_current,
                        inputs(),
                        &wallet_coin,
                        replayed_input,
                        &deposit_parameters,
                        &cache,
                        &make_signer(),
                        StdRng::from_entropy(),
                    )
                    .await
                    .is_err(),
                "spent wallet input replay bound another receive"
            );
            ensure!(
                node.finalized_contract_state(deposit_target.contract_address())?
                    .bytes
                    == receipt.contract_state,
                "replayed wallet input changed the receive Map"
            );
            println!(
                "{}",
                json!({
                    "seedTipHeight": seed_tip_receipt.height,
                    "depositHeight": receipt.height,
                    "depositTransaction": receipt.transaction_id,
                    "inputNullifier": hex::encode(input_nullifier.0.0),
                    "outputCommitment": hex::encode(receive_commitment.0.0),
                    "outputIndex": receive_index,
                    "value": wallet_coin.value.to_string(),
                    "rejected": ["unequalValue", "replayedInput"]
                })
            );
            Ok(())
        })
    }
}
