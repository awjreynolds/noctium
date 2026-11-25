use anyhow::{Context, Result, ensure};
use std::{
    env,
    thread::sleep,
    time::{Duration, Instant},
};

use crate::{
    Db,
    assembly::NativeIntent,
    client::{
        BoundTransaction, ChainAdapter, FinalizedReceipt, NetworkPolicy, Snapshot, Submission,
    },
    funding::{CONTRACT_SEGMENT, DustMaterial, FeePolicy, UnsealedTransaction},
    localnet::{DEVELOPMENT_GENESIS, DevelopmentFunding, ExplicitSeal, Node, ProofCache},
    proof::{ProvedNativeIntent, TrustedParameters},
};
use onchain_runtime::state::{ContractState, StateValue};
use rand::{SeedableRng, rngs::StdRng};
use serde_json::{Value as Json, json};
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

pub(super) struct Localnet {
    pub snapshot: Snapshot,
    node: Node,
    policy: NetworkPolicy,
    dust: DustMaterial,
    dust_parameters: TrustedParameters,
}

pub(super) async fn connect(endpoint: &str) -> Result<Localnet> {
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
        Duration::from_secs(30),
        64 * 1024 * 1024,
        100_000,
    )?;
    let mut seed = [0; 32];
    seed[31] = 1;
    node.attach_dust_seed(&seed)?;
    let cache = ProofCache::new(
        env::var_os("NOCTIUM_GUARDED_READS_PARAMETER_CACHE")
            .context("missing guarded-read development parameter cache")?
            .into(),
        "https://srs.midnight.network/".parse()?,
    )?;
    let dust = cache.dust().await?;
    let dust_parameters = cache.parameters(dust.k()).await?;
    let snapshot = node.sync()?;
    Ok(Localnet {
        snapshot,
        node,
        policy,
        dust,
        dust_parameters,
    })
}

async fn submit(context: &Localnet, intent: &ProvedNativeIntent) -> Result<FinalizedReceipt> {
    let funding = DevelopmentFunding::new(
        &context.node,
        &context.dust,
        &context.dust_parameters,
        FeePolicy {
            max_dust: context.policy.max_dust,
            margin_blocks: 3,
            max_spends: 8,
        },
        StdRng::from_entropy(),
    );
    let signing = ExplicitSeal::new(
        |_: &UnsealedTransaction, requested: &NetworkPolicy| requested == &context.policy,
        StdRng::from_entropy(),
    );
    let bound = BoundTransaction::prepare(
        intent,
        context.policy.clone(),
        &context.node,
        &funding,
        &signing,
    )
    .await?;
    ensure!(
        matches!(context.node.submit(&bound).await, Ok(Submission::Broadcast)),
        "guarded-read transaction did not broadcast"
    );
    let deadline = Instant::now() + Duration::from_secs(90);
    loop {
        if let Some(receipt) = context.node.finalized_receipt(&bound)? {
            bound.check_receipt(&receipt)?;
            return Ok(receipt);
        }
        ensure!(
            Instant::now() < deadline,
            "guarded-read transaction did not finalize"
        );
        sleep(Duration::from_secs(1));
    }
}

fn public_receipt(receipt: &FinalizedReceipt) -> Json {
    json!({
        "blockHash": receipt.block_hash,
        "height": receipt.height,
        "finalizedHash": receipt.finalized_hash,
        "finalizedHeight": receipt.finalized_height,
        "extrinsicHash": receipt.extrinsic_hash,
        "extrinsicIndex": receipt.extrinsic_index,
        "transactionId": receipt.transaction_id,
        "intentId": receipt.intent_id,
        "event": receipt.event,
        "stateSha256": crate::artifacts::digest(&receipt.contract_state),
    })
}

pub(super) async fn finalize(
    context: &Localnet,
    deployment: &NativeIntent,
    call: &ProvedNativeIntent,
) -> Result<Json> {
    let (_, deployment) = deployment
        .prove(
            CONTRACT_SEGMENT,
            builtin_zkir::LocalProvingProvider {
                rng: StdRng::from_entropy(),
                resolver: &context.dust,
                params: &context.dust_parameters,
            },
            &context
                .snapshot
                .state
                .parameters
                .cost_model
                .runtime_cost_model,
        )
        .await?;
    let deployed = submit(context, &deployment)
        .await
        .context("finalize guarded-read deployment")?;
    let called = submit(context, call)
        .await
        .context("finalize guarded-read update")?;
    ensure!(
        deployed.contract_address == called.contract_address && deployed.height < called.height,
        "deployment and call receipts must identify one ordered contract history"
    );
    let observed = context
        .node
        .finalized_contract_state(&called.contract_address)?;
    ensure!(
        observed.bytes == called.contract_state,
        "fetched final state differs from the checked receipt"
    );
    let state: ContractState<Db> = crate::proof::decode(&observed.bytes)?;
    let (marker, balance) = state_fields(&state)?;
    ensure!(
        marker == Fr::from(23u64) && balance == Fr::from(99u64),
        "finalized marker or balance differs from the source result"
    );
    let (runtime_code_hash, metadata_sha256) = context.node.runtime_fingerprint();
    Ok(json!({
        "chain": called.chain,
        "runtimeCodeHash": runtime_code_hash,
        "metadataSha256": metadata_sha256,
        "contractAddress": called.contract_address,
        "deployment": public_receipt(&deployed),
        "call": public_receipt(&called),
        "observedState": {"blockHash": observed.block_hash, "height": observed.height, "marker": "23", "balances": {"7": "99"}},
    }))
}

pub(super) fn state_fields(state: &ContractState<Db>) -> Result<(Fr, Fr)> {
    let StateValue::Array(slots) = state.data.get_ref() else {
        anyhow::bail!("expected guarded-read state array");
    };
    let marker = slots.get(0).context("missing marker cell")?;
    let StateValue::Cell(marker) = &*marker else {
        anyhow::bail!("expected guarded-read marker cell");
    };
    let balances = slots.get(1).context("missing balances map")?;
    let StateValue::Map(balances) = &*balances else {
        anyhow::bail!("expected guarded-read balances map");
    };
    let value = balances
        .get(&crate::field_value(Fr::from(7u64)))
        .context("missing account 7 from finalized map")?;
    let StateValue::Cell(value) = &*value else {
        anyhow::bail!("expected guarded-read balance cell");
    };
    let mut marker_fields = Vec::new();
    marker.value_only_field_repr(&mut marker_fields);
    let mut balance_fields = Vec::new();
    value.value_only_field_repr(&mut balance_fields);
    let ([marker], [balance]) = (marker_fields.as_slice(), balance_fields.as_slice()) else {
        anyhow::bail!("expected a scalar marker and balance");
    };
    Ok((*marker, *balance))
}
