use super::*;
use anyhow::{Context, Result, ensure};
use coin_structure::{
    coin::{Info as CoinInfo, ShieldedTokenType},
    transfer::Recipient as CoinRecipient,
};
use serde_json::json;
use std::path::Path;

fn immediate_change_inputs(
    domain: HashOutput,
    coin: &CoinInfo,
    recipient: PublicKey,
    send_amount: u128,
) -> BTreeMap<String, Value> {
    BTreeMap::from([
        ("domain".into(), json!({"kind":"bytes", "values":domain.0})),
        ("nonce".into(), nonce_input(coin.nonce)),
        (
            "color".into(),
            json!({"kind":"bytes", "values":coin.type_.0.0}),
        ),
        ("sendAmount".into(), json!(send_amount.to_string())),
        (
            "recipient".into(),
            json!({"kind":"bytes", "values":recipient.0.0}),
        ),
    ])
}

#[test]
#[ignore = "requires an authenticated ImmediateShieldedChange bundle and isolated development node"]
fn funded_shielded_immediate_change_localnet() -> Result<()> {
    futures::executor::block_on(async {
        let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
        let bundle = artifacts::verify(
            Path::new(&setting("NOCTIUM_IMMEDIATE_CHANGE_BUNDLE")?),
            Some(&setting("NOCTIUM_IMMEDIATE_CHANGE_MANIFEST_SHA256")?),
        )?;
        let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
        let cache = ProofCache::new(
            setting("NOCTIUM_IMMEDIATE_CHANGE_PARAMETER_CACHE")?.into(),
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
            &setting("NOCTIUM_IMMEDIATE_CHANGE_NODE")?,
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
        let split_parameters = cache.parameters(circuit.k()).await?;
        let ttl = node.sync()?.block.tblock.to_secs() + 1800;
        let target = WitnessContractTarget::from_state_config(
            ContractBundleSet::new(vec![bundle])?,
            br#"{"state":{"pot":[]}}"#,
            ttl,
            &mut OsRng,
        )?;
        let split = target.operation("splitImmediateShielded", &split_parameters, ttl)?;
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
            let approve = |_: &UnsealedTransaction, candidate: &NetworkPolicy| {
                *candidate == policy
            };
            ExplicitSeal::new(approve, StdRng::from_entropy())
        };
        let (_, deployment_intent) = target
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
            &deployment_intent,
            policy.clone(),
            &node,
            &make_funding(),
            &make_signer(),
        )
        .await
        .context("prepare immediate-change deployment")?;
        let deployed = finalize(&node, &deploy)
            .await
            .context("finalize immediate-change deployment")?;
        let current = target
            .deployment_binding("splitImmediateShielded")?
            .admit_committed_state(
                &deployed.contract_state,
                deploy.expected_state(),
                &deployed.finalized_hash,
                true,
            )
            .context("admit deployed immediate-change state")?;
        let address = ContractAddress(HashOutput(
            hex::decode(target.contract_address())?
                .try_into()
                .map_err(|_| anyhow::anyhow!("wrong contract address size"))?,
        ));
        let domain = HashOutput([7; 32]);
        let color: ShieldedTokenType = address.custom_shielded_token_type(domain);
        let mut rng = StdRng::from_entropy();
        let coin = CoinInfo::new(&mut rng, 5, color);
        let keys = SecretKeys::from_rng_seed(&mut rng);
        let recipient_coin_key = keys.coin_public_key();
        let recipient_encryption_key = keys.enc_public_key();
        let user_coin = coin.evolve_from(
            b"midnight:kernel:nonce_evolve",
            2,
            coin.type_,
        );
        let change_coin = coin.evolve_from(
            b"midnight:kernel:nonce_evolve/2",
            3,
            coin.type_,
        );
        let transient_commitment = coin.commitment(&CoinRecipient::Contract(address));
        let transient_nullifier = coin.nullifier(&SenderEvidence::Contract(address));
        let user_commitment = user_coin.commitment(&CoinRecipient::User(recipient_coin_key));
        let change_commitment = change_coin.commitment(&CoinRecipient::Contract(address));

        let before = node.sync()?;
        let deployed_contract = node.finalized_contract_state(target.contract_address())?;
        ensure!(
            deployed_contract.bytes == deployed.contract_state,
            "deployment receipt differs from finalized contract state"
        );
        let deployed_state: ContractState<Db> =
            super::super::super::native_decode(&deployed_contract.bytes)?;
        ensure!(
            !map_contains(&deployed_state, coin.nonce)?,
            "mint fixture nonce already exists in the contract Map"
        );

        let overspend = make_funding()
            .bind_shielded_immediate_change(
                &split,
                &current,
                immediate_change_inputs(domain, &coin, recipient_coin_key, 6),
                recipient_encryption_key,
                &split_parameters,
                &cache,
                &make_signer(),
                StdRng::from_entropy(),
            )
            .await;
        ensure!(overspend.is_err(), "overspend of 6 was accepted against a 5-unit mint");
        ensure!(
            node.finalized_contract_state(target.contract_address())?.bytes
                == deployed.contract_state,
            "rejected overspend changed the contract state"
        );
        let after_overspend = node.sync()?;
        ensure!(
            after_overspend.state.zswap.first_free == before.state.zswap.first_free
                && !after_overspend
                    .state
                    .zswap
                    .nullifiers
                    .contains_key(&transient_nullifier),
            "rejected overspend changed finalized Zswap state"
        );

        let bound = make_funding()
            .bind_shielded_immediate_change(
                &split,
                &current,
                immediate_change_inputs(domain, &coin, recipient_coin_key, 2),
                recipient_encryption_key,
                &split_parameters,
                &cache,
                &make_signer(),
                StdRng::from_entropy(),
            )
            .await
            .context("bind splitImmediateShielded for 5 to 2 plus 3")?;
        let sealed: crate::funding::SealedTransaction =
            serialize::tagged_deserialize(bound.bytes())?;
        let Transaction::Standard(transaction) = &sealed else {
            anyhow::bail!("expected a standard immediate-change transaction")
        };
        let offer = transaction
            .guaranteed_coins
            .as_deref()
            .context("missing guaranteed immediate-change offer")?;
        ensure!(
            offer.inputs.is_empty() && offer.outputs.len() == 2 && offer.transient.len() == 1,
            "immediate-change offer shape differs"
        );
        let transient = offer.transient.get(0).context("missing minted transient")?;
        ensure!(
            transient.coin_com == transient_commitment
                && transient.nullifier == transient_nullifier
                && transient.contract_address.as_deref() == Some(&address),
            "same-call transient differs from the 5-unit contract coin"
        );
        let user_output = offer.outputs.get(0).context("missing encrypted user output")?;
        let change_output = offer.outputs.get(1).context("missing contract change output")?;
        ensure!(
            user_output.coin_com == user_commitment
                && user_output.contract_address.is_none()
                && user_output.ciphertext.is_some(),
            "encrypted user output differs from the 2-unit transfer"
        );
        ensure!(
            change_output.coin_com == change_commitment
                && change_output.contract_address.as_deref() == Some(&address)
                && change_output.ciphertext.is_none(),
            "contract change output differs from the 3-unit change"
        );
        let encrypted = user_output
            .ciphertext
            .as_deref()
            .context("missing encrypted user ciphertext")?;
        ensure!(
            keys.try_decrypt(encrypted) == Some(user_coin),
            "recipient could not decrypt the exact 2-unit output"
        );
        let (_, booked_indices) = before.state.zswap.try_apply(offer, None)?;
        let transient_index = *booked_indices
            .get(&transient_commitment)
            .context("transient booking index missing")?;
        let user_index = *booked_indices
            .get(&user_commitment)
            .context("user output booking index missing")?;
        let change_index = *booked_indices
            .get(&change_commitment)
            .context("contract change booking index missing")?;
        ensure!(
            user_index == before.state.zswap.first_free
                && change_index == user_index + 1
                && transient_index == change_index + 1,
            "same-offer output and transient indices differ"
        );

        let receipt = finalize(&node, &bound)
            .await
            .context("finalize splitImmediateShielded")?;
        ensure!(
            receipt.contract_state == bound.expected_state(),
            "finalized immediate-change state differs from its prepared state"
        );
        let finalized_contract = node.finalized_contract_state(target.contract_address())?;
        ensure!(
            finalized_contract.bytes == receipt.contract_state,
            "finalized contract query differs from the transaction receipt"
        );
        let final_state: ContractState<Db> =
            super::super::super::native_decode(&finalized_contract.bytes)?;
        let StateValue::Array(final_slots) = final_state.data.get_ref() else {
            anyhow::bail!("expected finalized contract state array")
        };
        let Some(StateValue::Map(pot)) = final_slots.get(0) else {
            anyhow::bail!("expected finalized contract pot Map")
        };
        ensure!(
            pot.size() == 1
                && !pot.contains_key(&AlignedValue::from(coin.nonce))
                && pot.contains_key(&AlignedValue::from(change_coin.nonce))
                && !map_contains(&final_state, coin.nonce)?,
            "split did not replace the original Map key with only contract change"
        );
        let booked_change = map_coin_by_nonce(&final_state, change_coin.nonce)?;
        ensure!(
            booked_change.value == 3
                && booked_change.type_ == coin.type_
                && booked_change.mt_index == change_index,
            "contract Map change value or booking index differs"
        );
        let finalized = node.sync()?;
        let snapshot_contract = finalized
            .state
            .contract
            .get(&address)
            .context("finalized immediate-change contract missing from snapshot")?;
        ensure!(
            tagged_state_bytes(&snapshot_contract)? == receipt.contract_state,
            "synced contract state differs from the finalized receipt"
        );
        let (change_leaf, change_owner) = finalized
            .state
            .zswap
            .coin_coms
            .index(change_index)
            .context("finalized contract change leaf missing")?;
        ensure!(
            change_leaf == change_commitment.0
                && change_owner.as_deref() == Some(&address)
                && finalized
                    .state
                    .zswap
                    .coin_coms_set
                    .contains_key(&change_commitment),
            "finalized change leaf differs from its booked commitment or owner"
        );
        let (user_leaf, user_owner) = finalized
            .state
            .zswap
            .coin_coms
            .index(user_index)
            .context("finalized user output leaf missing")?;
        ensure!(
            user_leaf == user_commitment.0
                && user_owner.is_none()
                && finalized
                    .state
                    .zswap
                    .coin_coms_set
                    .contains_key(&user_commitment),
            "finalized encrypted user output commitment or owner differs"
        );
        let (transient_leaf, transient_owner) = finalized
            .state
            .zswap
            .coin_coms
            .index(transient_index)
            .context("finalized transient leaf missing")?;
        ensure!(
            transient_leaf == transient_commitment.0
                && transient_owner.as_deref() == Some(&address)
                && finalized
                    .state
                    .zswap
                    .nullifiers
                    .contains_key(&transient_nullifier),
            "same-call transient commitment or spent nullifier differs"
        );
        println!(
            "{}",
            json!({
                "deploymentHeight": deployed.height,
                "transactionHeight": receipt.height,
                "transactionId": receipt.transaction_id,
                "entrypoint": "splitImmediateShielded",
                "mintedTransientValue": 5,
                "transientIndex": transient_index,
                "transientNullifier": hex::encode(transient_nullifier.0.0),
                "userValue": 2,
                "userOutputIndex": user_index,
                "userOutputCommitment": hex::encode(user_commitment.0.0),
                "changeValue": booked_change.value,
                "changeIndex": booked_change.mt_index,
                "changeCommitment": hex::encode(change_commitment.0.0),
                "originalMapKeyRemoved": true,
                "overspendSixRejected": true,
                "bundleManifestSha256": setting("NOCTIUM_IMMEDIATE_CHANGE_MANIFEST_SHA256")?,
                "circuitK": circuit.k(),
            })
        );
        Ok(())
    })
}
