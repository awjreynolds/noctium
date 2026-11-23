use super::{DEVELOPMENT_GENESIS, DevelopmentFunding, Error, ProofCache, Result, check};
use crate::{
    Db,
    client::{BoundTransaction, HostFailure, SigningAdapter, Snapshot},
    proof::{
        ContractOperationTarget, ContractStateBinding, CurrentStateContext, LocalProver,
        PreparedProof, TrustedParameters,
    },
};
use base_crypto::{fab::AlignedValue, hash::HashOutput, rng::SplittableRng};
use coin_structure::{
    coin::{Commitment, Info, Nonce, Nullifier, PublicKey, QualifiedInfo},
    contract::ContractAddress,
    transfer::{Recipient, SenderEvidence},
};
use ledger::structure::GUARANTEED_SEGMENT;
use onchain_runtime::state::{ContractState, StateValue};
use rand::{CryptoRng, Rng, rngs::StdRng};
use serde_json::Value;
use std::{collections::BTreeMap, future::pending};
use transient_crypto::{
    commitment::PedersenRandomness,
    encryption,
    merkle_tree::MerkleTreeDigest,
    proofs::{Proof, ProofPreimage},
};
use zswap::{Input, Offer, Output, Transient, prove::ZswapResolver};

pub(super) struct StagedContractInput {
    pub(super) input: Input<ProofPreimage, Db>,
    pub(super) commitment: Commitment,
    pub(super) nullifier: Nullifier,
    pub(super) merkle_tree_root: MerkleTreeDigest,
}

pub(super) struct StagedContractOutput {
    pub(super) output: Output<ProofPreimage, Db>,
    pub(super) commitment: Commitment,
}

/// Stage one exact live contract-owned coin for a native offer.
///
/// The current root, indexed leaf, recipient-specific commitment, and unused nullifier must all
/// agree before the native input witness is created. The returned metadata is used by the host
/// binder to compare the completed offer with the proved contract effects.
pub(super) fn stage_contract_owned_input<R: Rng + CryptoRng + ?Sized>(
    zswap: &zswap::ledger::State<Db>,
    address: ContractAddress,
    coin: &QualifiedInfo,
    rng: &mut R,
) -> Result<StagedContractInput> {
    let info = Info::from(coin);
    let commitment = info.commitment(&Recipient::Contract(address));
    let nullifier = info.nullifier(&SenderEvidence::Contract(address));
    let capacity = 1u64
        .checked_shl(u32::from(zswap.coin_coms.height()))
        .ok_or(Error::State)?;
    let root = zswap.coin_coms.root().ok_or(Error::State)?;
    check(
        coin.mt_index < capacity
            && coin.mt_index < zswap.first_free
            && zswap.coin_coms_set.contains_key(&commitment)
            && !zswap.nullifiers.contains_key(&nullifier)
            && zswap.past_roots.contains(&root),
        Error::State,
    )?;
    let (leaf_hash, owner) = zswap.coin_coms.index(coin.mt_index).ok_or(Error::State)?;
    check(
        leaf_hash == commitment.0 && owner.as_deref() == Some(&address),
        Error::State,
    )?;

    let input = Input::<_, Db>::new_contract_owned(
        rng,
        coin,
        Some(GUARANTEED_SEGMENT),
        address,
        &zswap.coin_coms,
    )
    .map_err(|_| Error::State)?;
    check(
        input.nullifier == nullifier
            && input.merkle_tree_root == root
            && input.contract_address.as_deref() == Some(&address)
            && input.segment() == Some(GUARANTEED_SEGMENT),
        Error::State,
    )?;

    Ok(StagedContractInput {
        input,
        commitment,
        nullifier,
        merkle_tree_root: root,
    })
}

/// Stage one exact guaranteed contract-owned output for a native offer.
pub(super) fn stage_contract_owned_output<R: Rng + CryptoRng + ?Sized>(
    address: ContractAddress,
    coin: &Info,
    rng: &mut R,
) -> Result<StagedContractOutput> {
    let commitment = coin.commitment(&Recipient::Contract(address));
    let output = Output::<_, Db>::new_contract_owned(rng, coin, Some(GUARANTEED_SEGMENT), address)
        .map_err(|_| Error::State)?;
    check(
        output.coin_com == commitment
            && output.contract_address.as_deref() == Some(&address)
            && output.ciphertext.is_none()
            && output.segment() == Some(GUARANTEED_SEGMENT),
        Error::State,
    )?;
    Ok(StagedContractOutput { output, commitment })
}

/// Stage a commitment and its spend inside one guaranteed offer.
pub(super) fn stage_contract_owned_transient<R: Rng + CryptoRng + ?Sized>(
    address: ContractAddress,
    coin: &Info,
    rng: &mut R,
) -> Result<Transient<ProofPreimage, Db>> {
    let StagedContractOutput { output, commitment } =
        stage_contract_owned_output(address, coin, rng)?;
    let transient = Transient::new_from_contract_owned_output(
        rng,
        &coin.qualify(0),
        Some(GUARANTEED_SEGMENT),
        output,
    )
    .map_err(|_| Error::State)?;
    check(
        transient.coin_com == commitment
            && transient.nullifier == coin.nullifier(&SenderEvidence::Contract(address))
            && transient.contract_address.as_deref() == Some(&address)
            && transient.segment() == Some(GUARANTEED_SEGMENT),
        Error::State,
    )?;
    Ok(transient)
}

struct BookedOutput {
    commitment: Commitment,
    index: u64,
    contract_owned: bool,
    encrypted: bool,
}

pub(super) struct BookedTransfer {
    pub(super) offer: Offer<Proof, Db>,
    pub(super) randomness: PedersenRandomness,
    address: ContractAddress,
    current_state: Vec<u8>,
    qualified_coin: QualifiedInfo,
    input_commitment: Commitment,
    input_nullifier: Nullifier,
    input_root: transient_crypto::merkle_tree::MerkleTreeDigest,
    outputs: Vec<BookedOutput>,
}

impl BookedTransfer {
    pub(super) fn check_booking(
        &self,
        snapshot: &Snapshot,
    ) -> std::result::Result<(), HostFailure> {
        let (_, indices) = snapshot
            .state
            .zswap
            .try_apply(&self.offer, None)
            .map_err(|_| HostFailure)?;
        let current_state = snapshot
            .state
            .contract
            .get(&self.address)
            .ok_or(HostFailure)?;
        let mut bytes = Vec::new();
        serialize::tagged_serialize(&*current_state, &mut bytes).map_err(|_| HostFailure)?;
        let zswap = &snapshot.state.zswap;
        let info = Info::from(&self.qualified_coin);
        let commitment = info.commitment(&Recipient::Contract(self.address));
        let nullifier = info.nullifier(&SenderEvidence::Contract(self.address));
        let capacity = 1u64.checked_shl(u32::from(zswap.coin_coms.height()));
        let leaf = capacity
            .filter(|capacity| self.qualified_coin.mt_index < *capacity)
            .and_then(|_| zswap.coin_coms.index(self.qualified_coin.mt_index));
        let Some((leaf_hash, owner)) = leaf else {
            return Err(HostFailure);
        };

        if bytes != self.current_state
            || !zswap.coin_coms_set.contains_key(&commitment)
            || commitment != self.input_commitment
            || nullifier != self.input_nullifier
            || zswap.nullifiers.contains_key(&nullifier)
            || !zswap.past_roots.contains(&self.input_root)
            || leaf_hash != commitment.0
            || owner.as_deref() != Some(&self.address)
            || self.qualified_coin.mt_index >= zswap.first_free
            || self.offer.inputs.len() != 1
            || self.offer.outputs.len() != self.outputs.len()
            || !self.offer.transient.is_empty()
            || self.offer.inputs.get(0).is_none_or(|input| {
                input.nullifier != self.input_nullifier
                    || input.merkle_tree_root != self.input_root
                    || input.contract_address.as_deref() != Some(&self.address)
            })
            || self.outputs.iter().any(|expected| {
                indices.get(&expected.commitment).as_deref() != Some(&expected.index)
                    || self
                        .offer
                        .outputs
                        .iter_deref()
                        .find(|output| output.coin_com == expected.commitment)
                        .is_none_or(|output| {
                            let owner_matches = if expected.contract_owned {
                                output.contract_address.as_deref() == Some(&self.address)
                            } else {
                                output.contract_address.is_none()
                            };
                            !owner_matches || output.ciphertext.is_some() != expected.encrypted
                        })
            })
        {
            return Err(HostFailure);
        }
        Ok(())
    }
}

impl DevelopmentFunding<'_> {
    /// Bind a single contract-owned Map coin to one encrypted user output.
    pub async fn bind_shielded_map_spend(
        mut self,
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Value>,
        recipient_encryption_key: encryption::PublicKey,
        parameters: &TrustedParameters,
        cache: &ProofCache,
        signer: &impl SigningAdapter,
        mut rng: StdRng,
    ) -> Result<BoundTransaction> {
        let policy = self.node.policy.clone();
        check(policy.genesis == DEVELOPMENT_GENESIS, Error::Policy)?;
        let expected_input_count = if target.operation() == "spendRaw" {
            4
        } else {
            2
        };
        check(inputs.len() == expected_input_count, Error::State)?;
        let nonce = Nonce(read_bytes32(&inputs, "nonce")?);
        let recipient = PublicKey(read_bytes32(&inputs, "recipient")?);
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
        let current_contract = snapshot.state.contract.get(&address).ok_or(Error::State)?;
        let current_state = tagged_state_bytes(&current_contract)?;
        let qualified_coin = map_coin_by_nonce(&current_contract, nonce)?;
        check(qualified_coin.nonce == nonce, Error::State)?;

        let info = Info::from(&qualified_coin);
        let zswap = &snapshot.state.zswap;
        let staged_input = stage_contract_owned_input(zswap, address, &qualified_coin, &mut rng)?;
        let StagedContractInput {
            input,
            commitment,
            nullifier,
            merkle_tree_root: input_root,
        } = staged_input;

        let prepared =
            PreparedProof::from_contract_witness_inputs(target, current, inputs, &mut rng)
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
        check(
            binding.current_state_bytes() == Some(current_state.as_slice()),
            Error::State,
        )?;

        let output_info = info.evolve_from(
            b"midnight:kernel:nonce_evolve",
            qualified_coin.value,
            qualified_coin.type_,
        );
        let output = Output::<_, Db>::new(
            &mut rng,
            &output_info,
            Some(GUARANTEED_SEGMENT),
            &recipient,
            Some(recipient_encryption_key),
        )
        .map_err(|_| Error::State)?;
        let output_commitment = output.coin_com;
        let offer = Offer::new(vec![input], vec![output], vec![]).ok_or(Error::State)?;
        let (_, indices) = zswap.try_apply(&offer, None).map_err(|_| Error::State)?;
        let output_index = *indices.get(&output_commitment).ok_or(Error::State)?;

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

        self.shielded_transfer = Some(BookedTransfer {
            offer,
            randomness,
            address,
            current_state,
            qualified_coin,
            input_commitment: commitment,
            input_nullifier: nullifier,
            input_root,
            outputs: vec![BookedOutput {
                commitment: output_commitment,
                index: output_index,
                contract_owned: false,
                encrypted: true,
            }],
        });
        let expected = &self.shielded_transfer.as_ref().ok_or(Error::State)?.offer;
        let bound = BoundTransaction::prepare_shielded_transfer(
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

    /// Bind one contract-owned coin to an encrypted user output and contract change.
    pub async fn bind_shielded_map_split(
        self,
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Value>,
        recipient_encryption_key: encryption::PublicKey,
        parameters: &TrustedParameters,
        cache: &ProofCache,
        signer: &impl SigningAdapter,
        rng: StdRng,
    ) -> Result<BoundTransaction> {
        self.bind_shielded_map_split_with_binding(
            target,
            current,
            inputs,
            recipient_encryption_key,
            parameters,
            cache,
            signer,
            rng,
        )
        .await
        .map(|(bound, _)| bound)
    }

    pub(crate) async fn bind_shielded_map_split_with_binding(
        mut self,
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Value>,
        recipient_encryption_key: encryption::PublicKey,
        parameters: &TrustedParameters,
        cache: &ProofCache,
        signer: &impl SigningAdapter,
        mut rng: StdRng,
    ) -> Result<(BoundTransaction, ContractStateBinding)> {
        let policy = self.node.policy.clone();
        check(policy.genesis == DEVELOPMENT_GENESIS, Error::Policy)?;
        check(inputs.len() == 3, Error::State)?;
        let nonce = Nonce(read_bytes32(&inputs, "nonce")?);
        let send_amount = read_uint128(&inputs, "sendAmount")?;
        let recipient = PublicKey(read_bytes32(&inputs, "recipient")?);
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
        let current_contract = snapshot.state.contract.get(&address).ok_or(Error::State)?;
        let current_state = tagged_state_bytes(&current_contract)?;
        let qualified_coin = map_coin_by_nonce(&current_contract, nonce)?;
        let info = Info::from(&qualified_coin);
        check(send_amount > 0 && send_amount < info.value, Error::State)?;
        let change_amount = info.value.checked_sub(send_amount).ok_or(Error::State)?;
        let zswap = &snapshot.state.zswap;
        let StagedContractInput {
            input,
            commitment,
            nullifier,
            merkle_tree_root: input_root,
        } = stage_contract_owned_input(zswap, address, &qualified_coin, &mut rng)?;
        let user_info = info.evolve_from(
            b"midnight:kernel:nonce_evolve",
            send_amount,
            qualified_coin.type_,
        );
        let change_info = info.evolve_from(
            b"midnight:kernel:nonce_evolve/2",
            change_amount,
            qualified_coin.type_,
        );
        let user_output = Output::<_, Db>::new(
            &mut rng,
            &user_info,
            Some(GUARANTEED_SEGMENT),
            &recipient,
            Some(recipient_encryption_key),
        )
        .map_err(|_| Error::State)?;
        let StagedContractOutput {
            output: change_output,
            commitment: change_commitment,
        } = stage_contract_owned_output(address, &change_info, &mut rng)?;
        let user_commitment = user_output.coin_com;
        check(user_commitment != change_commitment, Error::State)?;
        let offer = Offer::new(vec![input], vec![user_output, change_output], vec![])
            .ok_or(Error::State)?;
        let (_, indices) = zswap.try_apply(&offer, None).map_err(|_| Error::State)?;
        let user_index = *indices.get(&user_commitment).ok_or(Error::State)?;
        let change_index = *indices.get(&change_commitment).ok_or(Error::State)?;

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
        check(
            binding.current_state_bytes() == Some(current_state.as_slice()),
            Error::State,
        )?;

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

        self.shielded_split = Some(BookedTransfer {
            offer,
            randomness,
            address,
            current_state,
            qualified_coin,
            input_commitment: commitment,
            input_nullifier: nullifier,
            input_root,
            outputs: vec![
                BookedOutput {
                    commitment: user_commitment,
                    index: user_index,
                    contract_owned: false,
                    encrypted: true,
                },
                BookedOutput {
                    commitment: change_commitment,
                    index: change_index,
                    contract_owned: true,
                    encrypted: false,
                },
            ],
        });
        let expected = &self.shielded_split.as_ref().ok_or(Error::State)?.offer;
        let bound = BoundTransaction::prepare_shielded_split(
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

fn read_bytes32(inputs: &BTreeMap<String, Value>, name: &str) -> Result<HashOutput> {
    let value = inputs.get(name).ok_or(Error::State)?;
    let object = value.as_object().ok_or(Error::State)?;
    check(
        object.len() == 2 && object.get("kind").and_then(Value::as_str) == Some("bytes"),
        Error::State,
    )?;
    let values = object
        .get("values")
        .and_then(Value::as_array)
        .ok_or(Error::State)?;
    check(values.len() == 32, Error::State)?;
    let mut bytes = [0u8; 32];
    for (output, value) in bytes.iter_mut().zip(values) {
        *output = u8::try_from(value.as_u64().ok_or(Error::State)?).map_err(|_| Error::State)?;
    }
    Ok(HashOutput(bytes))
}

fn read_uint128(inputs: &BTreeMap<String, Value>, name: &str) -> Result<u128> {
    let encoded = inputs
        .get(name)
        .and_then(Value::as_str)
        .ok_or(Error::State)?;
    let value = encoded.parse::<u128>().map_err(|_| Error::State)?;
    check(value.to_string() == encoded, Error::State)?;
    Ok(value)
}

fn tagged_state_bytes(state: &ContractState<Db>) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    serialize::tagged_serialize(state, &mut bytes).map_err(|_| Error::State)?;
    Ok(bytes)
}

fn map_coin_by_nonce(state: &ContractState<Db>, nonce: Nonce) -> Result<QualifiedInfo> {
    let StateValue::Array(slots) = state.data.get_ref() else {
        return Err(Error::State);
    };
    let Some(StateValue::Map(coins)) = slots.get(0) else {
        return Err(Error::State);
    };
    let value = coins.get(&AlignedValue::from(nonce)).ok_or(Error::State)?;
    let StateValue::Cell(cell) = &*value else {
        return Err(Error::State);
    };
    let aligned = &**cell;
    let qualified = QualifiedInfo::try_from(&*aligned.value).map_err(|_| Error::State)?;
    check(
        qualified.nonce == nonce && *aligned == AlignedValue::from(qualified),
        Error::State,
    )?;
    Ok(qualified)
}

#[cfg(all(test, feature = "zkir-321"))]
mod tests {
    use super::*;
    use crate::{
        artifacts::{self, ContractBundleSet, Role},
        client::{BoundTransaction, ChainAdapter, FinalizedReceipt, NetworkPolicy, Submission},
        funding::{CONTRACT_SEGMENT, FeePolicy, UnsealedTransaction},
        localnet::{ExplicitSeal, Node},
        proof::WitnessContractTarget,
        zkir::IrSource,
    };
    use anyhow::{Context, Result, ensure};
    use base_crypto::time::{Duration as LedgerDuration, Timestamp};
    use coin_structure::coin::{Info as CoinInfo, Nonce, ShieldedTokenType};
    use coin_structure::transfer::Recipient as CoinRecipient;
    use ledger::structure::Transaction;
    use rand::{SeedableRng, rngs::OsRng};
    use serde_json::json;
    use std::{
        env,
        path::Path,
        thread,
        time::{Duration, Instant},
    };
    use transient_crypto::proofs::Zkir;
    use zswap::keys::SecretKeys;

    #[test]
    fn staged_contract_coin_witnesses_match_live_native_booking() {
        let mut rng = StdRng::from_seed([0x5a; 32]);
        let address = ContractAddress(HashOutput([0x21; 32]));
        let coin = CoinInfo {
            nonce: Nonce(HashOutput([0x31; 32])),
            type_: ShieldedTokenType(HashOutput([0x41; 32])),
            value: 17,
        };
        let staged_output = stage_contract_owned_output(address, &coin, &mut rng).unwrap();
        assert_eq!(
            staged_output.commitment,
            coin.commitment(&Recipient::Contract(address))
        );
        assert_eq!(staged_output.output.coin_com, staged_output.commitment);
        assert_eq!(
            staged_output.output.contract_address.as_deref(),
            Some(&address)
        );
        assert!(staged_output.output.ciphertext.is_none());

        let initial = zswap::ledger::State::<Db>::new();
        let offer = Offer::new(Vec::new(), vec![staged_output.output], Vec::new()).unwrap();
        let (state, indices) = initial.try_apply(&offer, None).unwrap();
        let index = *indices.get(&staged_output.commitment).unwrap();
        let state =
            state.post_block_update(Timestamp::from_secs(1), LedgerDuration::from_secs(3600));
        let qualified = coin.qualify(index);

        let staged_input =
            stage_contract_owned_input(&state, address, &qualified, &mut rng).unwrap();
        assert_eq!(
            staged_input.commitment,
            coin.commitment(&Recipient::Contract(address))
        );
        assert_eq!(
            staged_input.nullifier,
            coin.nullifier(&SenderEvidence::Contract(address))
        );
        assert_eq!(
            staged_input.merkle_tree_root,
            state.coin_coms.root().unwrap()
        );
        assert_eq!(staged_input.input.nullifier, staged_input.nullifier);
        assert_eq!(staged_input.input.segment(), Some(GUARANTEED_SEGMENT));

        let wrong_owner = ContractAddress(HashOutput([0x22; 32]));
        assert!(stage_contract_owned_input(&state, wrong_owner, &qualified, &mut rng).is_err());
        let wrong_coin = QualifiedInfo {
            value: qualified.value + 1,
            ..qualified
        };
        assert!(stage_contract_owned_input(&state, address, &wrong_coin, &mut rng).is_err());

        let duplicate = Offer::new(
            vec![staged_input.input.clone(), staged_input.input],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        assert!(state.try_apply(&duplicate, None).is_err());
    }

    #[test]
    fn staged_transient_binds_same_offer_commitment_and_nullifier() {
        let mut rng = StdRng::from_seed([0x5a; 32]);
        let address = ContractAddress(HashOutput([0x21; 32]));
        let coin = CoinInfo {
            nonce: Nonce(HashOutput([0x31; 32])),
            type_: ShieldedTokenType(HashOutput([0x41; 32])),
            value: 17,
        };
        let commitment = coin.commitment(&Recipient::Contract(address));
        let nullifier = coin.nullifier(&SenderEvidence::Contract(address));
        let transient = stage_contract_owned_transient(address, &coin, &mut rng).unwrap();
        assert_eq!(transient.coin_com, commitment);
        assert_eq!(transient.nullifier, nullifier);
        assert_eq!(transient.contract_address.as_deref(), Some(&address));
        assert_eq!(transient.segment(), Some(GUARANTEED_SEGMENT));

        let offer = Offer::new(vec![], vec![], vec![transient]).unwrap();
        let initial = zswap::ledger::State::<Db>::new();
        let (state, indices) = initial.try_apply(&offer, None).unwrap();
        assert_eq!(*indices.get(&commitment).unwrap(), initial.first_free);
        assert!(state.nullifiers.contains_key(&nullifier));
        assert!(state.try_apply(&offer, None).is_err());
    }

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

    fn nonce_input(nonce: Nonce) -> Value {
        json!({"kind":"bytes", "values":nonce.0.0})
    }

    fn spend_inputs(nonce: Nonce, recipient: PublicKey) -> BTreeMap<String, Value> {
        BTreeMap::from([
            ("nonce".into(), nonce_input(nonce)),
            (
                "recipient".into(),
                json!({"kind":"bytes", "values":recipient.0.0}),
            ),
        ])
    }

    fn raw_spend_inputs(
        nonce: Nonce,
        recipient: PublicKey,
        input_nullifier: HashOutput,
        output_commitment: HashOutput,
    ) -> BTreeMap<String, Value> {
        BTreeMap::from([
            ("nonce".into(), nonce_input(nonce)),
            (
                "recipient".into(),
                json!({"kind":"bytes", "values":recipient.0.0}),
            ),
            (
                "inputNullifier".into(),
                json!({"kind":"bytes", "values":input_nullifier.0}),
            ),
            (
                "outputCommitment".into(),
                json!({"kind":"bytes", "values":output_commitment.0}),
            ),
        ])
    }

    fn partial_spend_inputs(
        nonce: Nonce,
        send_amount: u128,
        recipient: PublicKey,
    ) -> BTreeMap<String, Value> {
        let mut inputs = spend_inputs(nonce, recipient);
        inputs.insert("sendAmount".into(), json!(send_amount.to_string()));
        inputs
    }

    fn map_contains(state: &ContractState<Db>, nonce: Nonce) -> Result<bool> {
        let StateValue::Array(slots) = state.data.get_ref() else {
            anyhow::bail!("expected state array");
        };
        let Some(StateValue::Map(coins)) = slots.get(0) else {
            anyhow::bail!("expected qualified coin Map in slot 0");
        };
        Ok(coins.contains_key(&AlignedValue::from(nonce)))
    }

    #[test]
    #[ignore = "requires generated tip/spend bundles and isolated development node"]
    fn funded_shielded_map_spend_localnet() -> Result<()> {
        funded_shielded_map_localnet(false, false)
    }

    #[test]
    #[ignore = "requires generated tip/spend bundles and isolated development node"]
    fn funded_shielded_map_partial_spend_localnet() -> Result<()> {
        funded_shielded_map_localnet(true, false)
    }

    #[test]
    #[ignore = "requires generated raw spend and tip bundles and isolated development node"]
    fn funded_shielded_map_raw_spend_localnet() -> Result<()> {
        funded_shielded_map_localnet(false, true)
    }

    fn funded_shielded_map_localnet(split: bool, raw_spend: bool) -> Result<()> {
        ensure!(
            !split || !raw_spend,
            "raw shielded spend harness currently covers whole spends only"
        );
        futures::executor::block_on(async {
            let setting = |name: String| env::var(&name).with_context(|| format!("missing {name}"));
            let prefix = if raw_spend {
                "NOCTIUM_RAW_SPEND_"
            } else if split {
                "NOCTIUM_PARTIAL_SPEND_"
            } else {
                "NOCTIUM_TRANSFER_"
            };
            let setting_name = |suffix: &str| format!("{prefix}{suffix}");
            let tip_bundle_path = setting(setting_name("TIP_BUNDLE"))?;
            let tip_manifest = setting(setting_name("TIP_MANIFEST_SHA256"))?;
            let tip_bundle = artifacts::verify(Path::new(&tip_bundle_path), Some(&tip_manifest))?;
            let spend_bundle_path = setting(setting_name("SPEND_BUNDLE"))?;
            let spend_manifest = setting(setting_name("SPEND_MANIFEST_SHA256"))?;
            let spend_bundle =
                artifacts::verify(Path::new(&spend_bundle_path), Some(&spend_manifest))?;
            let tip_circuit = IrSource::load(tip_bundle.file(Role::Circuit)?)?;
            let spend_circuit = IrSource::load(spend_bundle.file(Role::Circuit)?)?;
            let cache = ProofCache::new(
                setting(setting_name("PARAMETER_CACHE"))?.into(),
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
            let node_url = setting(setting_name("NODE"))?;
            let node = Node::connect(
                &node_url,
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
            let tip_parameters = cache.parameters(tip_circuit.k()).await?;
            let spend_parameters = cache.parameters(spend_circuit.k()).await?;
            let ttl = node.sync()?.block.tblock.to_secs() + 1800;
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![tip_bundle, spend_bundle])?,
                br#"{"state":{"pot":[]}}"#,
                ttl,
                &mut OsRng,
            )?;
            let tip = target.operation("tip", &tip_parameters, ttl)?;
            let spend = target.operation(
                if raw_spend { "spendRaw" } else { "spend" },
                &spend_parameters,
                ttl,
            )?;
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
            let make_signer = || {
                let approve =
                    |_: &UnsealedTransaction, candidate: &NetworkPolicy| *candidate == policy;
                ExplicitSeal::new(approve, StdRng::from_entropy())
            };
            let deploy_signer = make_signer();
            let (_, deploy_intent) = target
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
                .map_err(|error| anyhow::anyhow!("deployment proof: {error:?}"))?;
            let deploy = BoundTransaction::prepare(
                &deploy_intent,
                policy.clone(),
                &node,
                &make_funding(),
                &deploy_signer,
            )
            .await
            .context("prepare deployment")?;
            let deployed = finalize(&node, &deploy)
                .await
                .context("finalize deployment")?;
            let mut current = target
                .deployment_binding("tip")?
                .admit_committed_state(
                    &deployed.contract_state,
                    deploy.expected_state(),
                    &deployed.finalized_hash,
                    true,
                )
                .context("restore post-deployment state")?;

            let address = ContractAddress(HashOutput(
                hex::decode(target.contract_address())?
                    .try_into()
                    .map_err(|_| anyhow::anyhow!("wrong contract address size"))?,
            ));
            let domain = HashOutput([7; 32]);
            let mut rng = StdRng::from_entropy();
            let coin = Info::new(&mut rng, 5, address.custom_shielded_token_type(domain));
            let snapshot = node.sync()?;
            let expected_index = snapshot.state.zswap.first_free;
            let commitment = coin.commitment(&CoinRecipient::Contract(address));
            let tip_inputs = || {
                BTreeMap::from([
                    ("domain".into(), json!({"kind":"bytes", "values":domain.0})),
                    ("nonce".into(), nonce_input(coin.nonce)),
                    (
                        "color".into(),
                        json!({"kind":"bytes", "values":coin.type_.0.0}),
                    ),
                ])
            };
            let tip_signer = make_signer();
            let receive = make_funding()
                .bind_minted_shielded_receive_with_binding(
                    &tip,
                    &current,
                    tip_inputs(),
                    &coin,
                    &tip_parameters,
                    &cache,
                    &tip_signer,
                    StdRng::from_entropy(),
                )
                .await
                .context("bind tip deposit")?;
            let tip_receipt = finalize(&node, &receive.0)
                .await
                .context("finalize tip deposit")?;
            current = receive
                .1
                .admit_committed_state(
                    &tip_receipt.contract_state,
                    receive.0.expected_state(),
                    &tip_receipt.finalized_hash,
                    false,
                )
                .context("restore post-tip state")?;
            let state: ContractState<Db> = super::super::native_decode(&tip_receipt.contract_state)
                .context("decode tip receipt state")?;
            let qualified_coin =
                map_coin_by_nonce(&state, coin.nonce).context("read tip Map coin")?;
            ensure!(
                qualified_coin.mt_index == expected_index,
                "tip did not book expected index"
            );
            ensure!(
                qualified_coin.value == 5,
                "tip did not deposit the nonzero fixture amount"
            );
            ensure!(
                snapshot
                    .state
                    .zswap
                    .coin_coms_set
                    .get(&commitment)
                    .is_none(),
                "fixture commitment unexpectedly existed before tip"
            );
            let deposited_snapshot = node.sync()?;
            let finalized_contract = deposited_snapshot
                .state
                .contract
                .get(&address)
                .ok_or_else(|| anyhow::anyhow!("finalized contract missing"))?;
            ensure!(
                tagged_state_bytes(&finalized_contract)? == tip_receipt.contract_state,
                "refreshed finalized state differs from the deposit receipt"
            );
            ensure!(
                map_coin_by_nonce(&finalized_contract, coin.nonce)? == qualified_coin
                    && deposited_snapshot
                        .state
                        .zswap
                        .coin_coms_set
                        .contains_key(&commitment),
                "refreshed finalized state does not contain the qualified deposit"
            );

            let keys = SecretKeys::from_rng_seed(&mut rng);
            let recipient_coin_key = keys.coin_public_key();
            let recipient_encryption_key = keys.enc_public_key();
            let raw_input_nullifier =
                Info::from(&qualified_coin).nullifier(&SenderEvidence::Contract(address));
            let raw_output_coin = Info::from(&qualified_coin).evolve_from(
                b"midnight:kernel:nonce_evolve",
                qualified_coin.value,
                qualified_coin.type_,
            );
            let raw_output_commitment =
                raw_output_coin.commitment(&CoinRecipient::User(recipient_coin_key));
            let spend_inputs_for_nonce = |nonce| {
                if raw_spend {
                    raw_spend_inputs(
                        nonce,
                        recipient_coin_key,
                        raw_input_nullifier.0,
                        raw_output_commitment.0,
                    )
                } else {
                    spend_inputs(nonce, recipient_coin_key)
                }
            };
            let expected_output_index = node.sync()?.state.zswap.first_free;
            let mismatch_signer = make_signer();
            let mismatch_inputs = if split {
                partial_spend_inputs(Nonce(HashOutput([0x55; 32])), 2, recipient_coin_key)
            } else {
                spend_inputs_for_nonce(Nonce(HashOutput([0x55; 32])))
            };
            let mismatch = if split {
                make_funding()
                    .bind_shielded_map_split(
                        &spend,
                        &current,
                        mismatch_inputs,
                        recipient_encryption_key,
                        &spend_parameters,
                        &cache,
                        &mismatch_signer,
                        StdRng::from_entropy(),
                    )
                    .await
            } else {
                make_funding()
                    .bind_shielded_map_spend(
                        &spend,
                        &current,
                        mismatch_inputs,
                        recipient_encryption_key,
                        &spend_parameters,
                        &cache,
                        &mismatch_signer,
                        StdRng::from_entropy(),
                    )
                    .await
            };
            ensure!(mismatch.is_err(), "mismatched nonce bound a spend");
            ensure!(
                node.finalized_contract_state(target.contract_address())?
                    .bytes
                    == tip_receipt.contract_state,
                "mismatched nonce changed the contract Map"
            );
            if raw_spend {
                let mut mismatched_output_commitment = raw_output_commitment.0;
                mismatched_output_commitment.0[0] ^= 1;
                ensure!(
                    mismatched_output_commitment != raw_output_commitment.0,
                    "raw output commitment mismatch did not change one byte"
                );
                let raw_mismatch = make_funding()
                    .bind_shielded_map_spend(
                        &spend,
                        &current,
                        raw_spend_inputs(
                            coin.nonce,
                            recipient_coin_key,
                            raw_input_nullifier.0,
                            mismatched_output_commitment,
                        ),
                        recipient_encryption_key,
                        &spend_parameters,
                        &cache,
                        &make_signer(),
                        StdRng::from_entropy(),
                    )
                    .await;
                ensure!(
                    matches!(raw_mismatch, Err(Error::State)),
                    "one-byte raw output commitment mismatch was not rejected by the exact offer binder"
                );
                ensure!(
                    node.finalized_contract_state(target.contract_address())?
                        .bytes
                        == tip_receipt.contract_state,
                    "rejected raw output commitment changed the contract Map"
                );
            }
            if split {
                let full_value_signer = make_signer();
                ensure!(
                    make_funding()
                        .bind_shielded_map_split(
                            &spend,
                            &current,
                            partial_spend_inputs(coin.nonce, 5, recipient_coin_key),
                            recipient_encryption_key,
                            &spend_parameters,
                            &cache,
                            &full_value_signer,
                            StdRng::from_entropy(),
                        )
                        .await
                        .is_err(),
                    "full-value split was accepted"
                );
                ensure!(
                    node.finalized_contract_state(target.contract_address())?
                        .bytes
                        == tip_receipt.contract_state,
                    "invalid split amount changed the contract Map"
                );
            }
            let spend_signer = make_signer();
            let (spend_bound, spend_binding) = if split {
                let (bound, binding) = make_funding()
                    .bind_shielded_map_split_with_binding(
                        &spend,
                        &current,
                        partial_spend_inputs(coin.nonce, 2, recipient_coin_key),
                        recipient_encryption_key,
                        &spend_parameters,
                        &cache,
                        &spend_signer,
                        StdRng::from_entropy(),
                    )
                    .await
                    .context("bind shielded Map split")?;
                (bound, Some(binding))
            } else {
                let bound = make_funding()
                    .bind_shielded_map_spend(
                        &spend,
                        &current,
                        spend_inputs_for_nonce(coin.nonce),
                        recipient_encryption_key,
                        &spend_parameters,
                        &cache,
                        &spend_signer,
                        StdRng::from_entropy(),
                    )
                    .await
                    .context("bind shielded Map spend")?;
                (bound, None)
            };
            let spend_receipt = finalize(&node, &spend_bound)
                .await
                .context("finalize shielded Map spend")?;
            if let Some(binding) = spend_binding {
                current = binding
                    .admit_committed_state(
                        &spend_receipt.contract_state,
                        spend_bound.expected_state(),
                        &spend_receipt.finalized_hash,
                        false,
                    )
                    .context("restore post-split state")?;
            }
            let spent_state: ContractState<Db> =
                super::super::native_decode(&spend_receipt.contract_state)
                    .context("decode spend receipt state")?;
            ensure!(
                !map_contains(&spent_state, coin.nonce)?,
                "spent Map entry remains"
            );
            let spent_snapshot = node.sync()?;
            let send_amount = if split { 2 } else { qualified_coin.value };
            let change_info = split.then(|| {
                Info::from(&qualified_coin).evolve_from(
                    b"midnight:kernel:nonce_evolve/2",
                    qualified_coin.value - send_amount,
                    qualified_coin.type_,
                )
            });
            let change_commitment = change_info
                .as_ref()
                .map(|info| info.commitment(&CoinRecipient::Contract(address)));
            if let (Some(change_info), Some(change_commitment)) =
                (&change_info, change_commitment.as_ref())
            {
                let change_coin = map_coin_by_nonce(&spent_state, change_info.nonce)
                    .context("read qualified change coin")?;
                ensure!(
                    change_coin.value == qualified_coin.value - send_amount
                        && change_coin.type_ == qualified_coin.type_
                        && Some(change_coin.mt_index) == expected_output_index.checked_add(1),
                    "change coin value, type, or output index mismatch"
                );
                let (change_leaf, change_owner) = spent_snapshot
                    .state
                    .zswap
                    .coin_coms
                    .index(change_coin.mt_index)
                    .ok_or_else(|| anyhow::anyhow!("contract change leaf missing"))?;
                ensure!(
                    change_leaf == change_commitment.0
                        && change_owner.as_deref() == Some(&address)
                        && spent_snapshot
                            .state
                            .zswap
                            .coin_coms_set
                            .contains_key(&change_commitment),
                    "finalized change commitment or owner mismatch"
                );
            }

            let input_nullifier =
                Info::from(&qualified_coin).nullifier(&SenderEvidence::Contract(address));
            ensure!(
                spent_snapshot
                    .state
                    .zswap
                    .nullifiers
                    .contains_key(&input_nullifier),
                "spend nullifier missing from finalized Zswap state"
            );
            let output_coin = Info::from(&qualified_coin).evolve_from(
                b"midnight:kernel:nonce_evolve",
                send_amount,
                qualified_coin.type_,
            );
            let output_commitment =
                output_coin.commitment(&CoinRecipient::User(recipient_coin_key));
            ensure!(
                !raw_spend
                    || (input_nullifier == raw_input_nullifier
                        && output_commitment == raw_output_commitment),
                "raw claim digests differ from the finalized offer"
            );
            let (output_leaf, output_owner) = spent_snapshot
                .state
                .zswap
                .coin_coms
                .index(expected_output_index)
                .ok_or_else(|| anyhow::anyhow!("encrypted output leaf missing"))?;
            ensure!(
                output_leaf == output_commitment.0
                    && output_owner.is_none()
                    && spent_snapshot
                        .state
                        .zswap
                        .coin_coms_set
                        .contains_key(&output_commitment),
                "finalized output commitment or owner mismatch"
            );
            ensure!(
                expected_index.checked_add(1) == Some(expected_output_index),
                "deposit did not advance the Zswap output cursor"
            );
            let sealed: crate::funding::SealedTransaction =
                serialize::tagged_deserialize(spend_bound.bytes())?;
            let Transaction::Standard(transaction) = sealed else {
                anyhow::bail!("expected a standard transaction");
            };
            let output = transaction
                .guaranteed_coins
                .as_deref()
                .ok_or_else(|| anyhow::anyhow!("missing guaranteed offer"))?;
            ensure!(
                output.outputs.len() == if split { 2 } else { 1 },
                "unexpected output count"
            );
            let ciphertext = output
                .outputs
                .get(0)
                .and_then(|output| output.ciphertext.as_deref())
                .ok_or_else(|| anyhow::anyhow!("missing encrypted output"))?;
            ensure!(
                keys.try_decrypt(ciphertext) == Some(output_coin),
                "recipient could not decrypt the exact output coin"
            );
            if split {
                let change_output = output
                    .outputs
                    .get(1)
                    .ok_or_else(|| anyhow::anyhow!("missing contract change output"))?;
                let expected_change_commitment = change_commitment
                    .as_ref()
                    .ok_or_else(|| anyhow::anyhow!("missing expected change commitment"))?;
                ensure!(
                    &change_output.coin_com == expected_change_commitment
                        && change_output.contract_address.as_deref() == Some(&address)
                        && change_output.ciphertext.is_none(),
                    "sealed change output mismatch"
                );
            }

            let replay_signer = make_signer();
            let replay_inputs = if split {
                partial_spend_inputs(coin.nonce, 2, recipient_coin_key)
            } else {
                spend_inputs_for_nonce(coin.nonce)
            };
            let replay = if split {
                make_funding()
                    .bind_shielded_map_split(
                        &spend,
                        &current,
                        replay_inputs,
                        recipient_encryption_key,
                        &spend_parameters,
                        &cache,
                        &replay_signer,
                        StdRng::from_entropy(),
                    )
                    .await
            } else {
                make_funding()
                    .bind_shielded_map_spend(
                        &spend,
                        &current,
                        replay_inputs,
                        recipient_encryption_key,
                        &spend_parameters,
                        &cache,
                        &replay_signer,
                        StdRng::from_entropy(),
                    )
                    .await
            };
            ensure!(replay.is_err(), "replayed nonce bound another spend");
            ensure!(
                node.finalized_contract_state(target.contract_address())?
                    .bytes
                    == spend_receipt.contract_state,
                "replayed nonce changed the contract Map"
            );
            let mut rejected = vec!["mismatchedNonce", "replayedNonce"];
            if split {
                rejected.insert(1, "fullValueAmount");
            }
            if raw_spend {
                rejected.insert(1, "rawOutputDigestMismatch");
            }
            println!(
                "{}",
                json!({
                    "deploymentHeight": deployed.height,
                    "tipHeight": tip_receipt.height,
                    "spendHeight": spend_receipt.height,
                    "spendTransaction": spend_receipt.transaction_id,
                    "inputNonce": hex::encode(coin.nonce.0.0),
                    "inputCommitment": hex::encode(commitment.0.0),
                    "inputNullifier": hex::encode(input_nullifier.0.0),
                    "outputCommitment": hex::encode(output_commitment.0.0),
                    "outputIndex": expected_output_index,
                    "sendAmount": send_amount,
                    "changeCommitment": change_commitment.as_ref().map(|value| hex::encode(value.0.0)),
                    "changeIndex": split.then(|| expected_output_index.checked_add(1)).flatten(),
                    "changeValue": split.then(|| qualified_coin.value - send_amount),
                    "spendEntrypoint": if raw_spend { "spendRaw" } else { "spend" },
                    "rawOutputDigestMismatchRejectedBeforeSubmit": raw_spend,
                    "decryptedOutput": true,
                    "rejected": rejected,
                    "contractStateSha256": artifacts::digest(&spend_receipt.contract_state)
                })
            );
            Ok(())
        })
    }
}
