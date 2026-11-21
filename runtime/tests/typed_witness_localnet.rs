//! Opt-in Rust qualification of the K7 scalar typed witness on a funded Ledger 9 localnet.
#![cfg(all(feature = "localnet", feature = "zkir-321"))]

use anyhow::{Context as _, Result, anyhow, bail, ensure};
use futures::{executor::block_on, future::pending};
use noctium_runtime::{
    Db, Plan,
    artifacts::{self, ContractBundleSet, Role},
    client::{
        ChainAdapter, FundingAdapter, JournalStore, NetworkPolicy, RecoveryRecord, SigningAdapter,
        Snapshot,
    },
    create_state,
    funding::{DustMaterial, FeePolicy, UnsealedTransaction},
    host,
    localnet::{
        DEVELOPMENT_GENESIS, DevelopmentFunding, ExplicitSeal, Node, ProofCache,
        journal::DirectoryJournal,
    },
    proof::{CurrentStateContext, LocalProver, TrustedParameters, WitnessContractTarget},
    witness_execution::{
        GeneratedBinding, WitnessClient, WitnessClientCommand as Command,
        WitnessClientReply as Reply, WitnessExecution,
    },
};
use onchain_runtime::state::{ChargedState, ContractState};
use rand::{
    RngCore, SeedableRng,
    rngs::{OsRng, StdRng},
};
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    env,
    path::Path,
    thread::sleep,
    time::{Duration, Instant},
};

const LOOKUP: &str = "noctium.lookup.v1";
const KEY: &str = "cache/last";
const EXPECTED_PARAMETERS_SHA256: &str =
    "e82ae890c080188355f37feaffe91372584cd810615082d9143d4dec0453fd9d";
const EXPECTED_CIRCUIT_SHA256: &str =
    "2633a900cefbc639c58b1fea4b8b003c145f637854543239ac832c243a45a0f7";
const EXPECTED_STATE_SHA256: &str =
    "f9b24f4480110e62fe9333e5c3be687073922bd24b0935fbd62c0eb1b699c600";

fn decode<T: serialize::Deserializable + serialize::Tagged>(bytes: &[u8]) -> Result<T> {
    let mut input = bytes;
    let value = serialize::tagged_deserialize(&mut input)?;
    ensure!(input.is_empty(), "trailing native bytes");
    Ok(value)
}

fn attempt_id() -> String {
    let mut bytes = [0; 32];
    OsRng.fill_bytes(&mut bytes);
    hex::encode(bytes)
}

struct Host<'a> {
    node: &'a Node,
    policy: &'a NetworkPolicy,
    dust: &'a DustMaterial,
    dust_parameters: &'a TrustedParameters,
    store: &'a DirectoryJournal,
    namespace: &'a str,
}

impl Host<'_> {
    fn private_value(&self) -> Result<Option<Json>> {
        self.store
            .private_value(self.namespace, KEY)
            .map_err(|_| anyhow!("typed-witness private value unavailable"))
    }

    fn context(&self, attempt: &str, providers: bool) -> Result<host::Context> {
        let revision = self
            .store
            .revision(self.namespace)
            .map_err(|_| anyhow!("typed-witness private revision unavailable"))?;
        let mut context: host::Context = serde_json::from_value(json!({
            "protocolVersion": 1,
            "namespace": self.namespace,
            "baseRevision": revision,
            "attemptId": attempt,
            "providers": [],
            "operations": [],
            "commitCapability": "commit",
            "capabilities": [
                {"id":"private","namespace":self.namespace,"keyPrefix":"cache/","operations":[host::READ, host::STAGE]},
                {"id":"commit","namespace":self.namespace,"keyPrefix":"cache/","operations":[host::CAS]}
            ]
        }))?;
        if providers {
            context.capabilities.push(host::Capability {
                id: "lookup".into(),
                namespace: self.namespace.into(),
                key_prefix: "lookup/".into(),
                operations: vec![LOOKUP.into()],
            });
            context.operations = vec![
                host::Operation {
                    operation: host::READ.into(),
                    argument_schema: BTreeMap::from([("key".into(), "Key".into())]),
                    result_schema: "UIntRange<256>".into(),
                },
                host::Operation {
                    operation: LOOKUP.into(),
                    argument_schema: BTreeMap::from([("seed".into(), "UIntRange<256>".into())]),
                    result_schema: "UIntRange<256>".into(),
                },
            ];
            context.providers = vec![
                host::Provider {
                    input: "cache".into(),
                    operation: host::READ.into(),
                    capability: "private".into(),
                    arguments: BTreeMap::from([("key".into(), json!(KEY))]),
                },
                host::Provider {
                    input: "lookup".into(),
                    operation: LOOKUP.into(),
                    capability: "lookup".into(),
                    arguments: BTreeMap::new(),
                },
            ];
        }
        Ok(context)
    }

    async fn finalize(
        &self,
        mut client: WitnessClient,
        expected: &ChargedState<Db>,
        staged: bool,
    ) -> Result<(CurrentStateContext, Json)> {
        let previous = self.private_value()?;
        let mut snapshot: Option<Snapshot> = None;
        let mut revision = None;
        let deadline = Instant::now() + Duration::from_secs(90);
        client.command(Command::Prepare)?;
        loop {
            ensure!(Instant::now() < deadline, "development client timed out");
            let status = client.poll()?;
            if let Some(request) = client.request()? {
                let payload = || {
                    request
                        .private_payload()
                        .context("host request has no payload")
                };
                let reply = match request.metadata["operation"].as_str().unwrap_or_default() {
                    "chain.snapshot.v1" => {
                        let live = self.node.sync()?;
                        snapshot = Some(Snapshot {
                            chain: live.chain.clone(),
                            finalized_hash: live.finalized_hash.clone(),
                            height: live.height,
                            state: live.state.clone(),
                            block: live.block.clone(),
                        });
                        Reply::Snapshot(live)
                    }
                    "funding.native.v1" => Reply::Funded(
                        DevelopmentFunding::new(
                            self.node,
                            self.dust,
                            self.dust_parameters,
                            FeePolicy {
                                max_dust: self.policy.max_dust,
                                margin_blocks: 3,
                                max_spends: 8,
                            },
                            StdRng::from_entropy(),
                        )
                        .fund(
                            &decode(payload()?)?,
                            snapshot.as_ref().context("funding snapshot")?,
                            self.policy,
                        )
                        .await
                        .map_err(|_| anyhow!("native funding failed"))?,
                    ),
                    "approval.sign.v1" => Reply::Signed(
                        ExplicitSeal::new(
                            |_: &UnsealedTransaction, policy: &NetworkPolicy| policy == self.policy,
                            StdRng::from_entropy(),
                        )
                        .approve_and_sign(
                            &decode(payload()?)?,
                            snapshot.as_ref().context("signing snapshot")?,
                            self.policy,
                        )
                        .await
                        .map_err(|_| anyhow!("native signing failed"))?,
                    ),
                    "chain.submit.v1" => Reply::Submitted(
                        self.node
                            .submit(request.transaction().context("submit binding")?)
                            .await
                            .map_err(|_| anyhow!("native submission failed"))?,
                    ),
                    "chain.observe.v1" => Reply::Observed(
                        self.node
                            .observe(request.transaction().context("observe binding")?)
                            .await
                            .map_err(|_| anyhow!("native receipt observation failed"))?,
                    ),
                    "journal.persist.v1" => {
                        let record = serde_json::from_slice(payload()?)?;
                        let acknowledgement = self
                            .store
                            .persist(&record, revision)
                            .await
                            .map_err(|_| anyhow!("journal persist failed"))?;
                        revision = Some(acknowledgement.revision);
                        Reply::Persisted(acknowledgement)
                    }
                    "private_state.compare_exchange.v1" => {
                        let record: RecoveryRecord = serde_json::from_slice(payload()?)?;
                        let journal: Json = serde_json::from_slice(record.journal_bytes())?;
                        let writes = journal["writes"].as_object().context("journal writes")?;
                        ensure!(
                            self.private_value()? == previous,
                            "private value changed before CAS"
                        );
                        if staged {
                            ensure!(
                                writes.len() == 1 && writes[KEY]["value"] == "14",
                                "wrong private write"
                            );
                        } else {
                            ensure!(writes.is_empty(), "unexpected private write");
                        }
                        Reply::Cas(
                            self.store
                                .compare_exchange(&record)
                                .await
                                .map_err(|_| anyhow!("private CAS failed"))?,
                        )
                    }
                    _ => bail!("unexpected native service request"),
                };
                client.complete(request.id, reply)?;
                continue;
            }
            ensure!(
                status["status"] != "failed" && status["status"] != "step_error",
                "native client failed: {status}"
            );
            match status["phase"].as_str().unwrap_or_default() {
                "Prepared" => {
                    client.command(Command::Submit)?;
                }
                "Submitted" | "Uncertain" => {
                    sleep(Duration::from_millis(500));
                    client.command(Command::Observe)?;
                }
                "AwaitingCas" => {
                    let bytes = client.receipt_state()?;
                    let accepted: ContractState<Db> = decode(&bytes)?;
                    ensure!(
                        accepted.data.get_ref() == expected.get_ref(),
                        "wrong finalized state"
                    );
                    let address = status["contractAddress"]
                        .as_str()
                        .context("finalized address")?;
                    ensure!(
                        self.node.finalized_contract_state(address)?.bytes == bytes,
                        "receipt state differs from finalized snapshot"
                    );
                    ensure!(
                        self.private_value()? == previous,
                        "private value changed before finality"
                    );
                    client.command(Command::Commit)?;
                }
                "Committed" => {
                    ensure!(
                        status["privateAcknowledged"] == true && status["privateCommitted"] == true,
                        "private commit failed"
                    );
                    let current = self.private_value()?;
                    if staged {
                        ensure!(
                            current.as_ref().is_some_and(|value| value["value"] == "14"),
                            "private value did not commit"
                        );
                    } else {
                        ensure!(current == previous, "deployment changed private state");
                    }
                    return Ok((client.current_state_context()?, status["receipt"].clone()));
                }
                _ => bail!("unexpected native client status: {status}"),
            }
        }
    }
}

fn run_source(execution: &mut WitnessExecution, attempt: &str) -> Result<Vec<String>> {
    let expected = ["cache", "cache", "lookup", "cache", "lookup"];
    let mut calls = Vec::new();
    for _ in 0..64 {
        let status = execution.advance()?;
        match status["status"].as_str().unwrap_or_default() {
            "completed" => {
                ensure!(
                    calls
                        .iter()
                        .map(String::as_str)
                        .eq(expected.iter().copied()),
                    "wrong provider sequence: {calls:?}"
                );
                ensure!(
                    status["result"] == "14",
                    "typed witness returned the wrong value"
                );
                return Ok(calls);
            }
            "need_host" => {
                let request = &status["request"];
                let name = request["name"].as_str().context("provider name")?;
                let index = calls.len();
                ensure!(
                    expected.get(index).copied() == Some(name),
                    "unexpected provider {name} at {index}"
                );
                calls.push(name.to_owned());
                let private = execution.private_request()?;
                ensure!(
                    private["invocationWrites"][KEY]["value"] == "1",
                    "staged cache value was not visible"
                );
                let (operation, capability, value) = match name {
                    "cache" => {
                        ensure!(
                            private["arguments"]["key"] == KEY,
                            "cache read used the wrong key"
                        );
                        (host::READ, "private", json!("1"))
                    }
                    "lookup" => {
                        ensure!(
                            private["arguments"]["seed"] == "7",
                            "lookup received the wrong seed"
                        );
                        (LOOKUP, "lookup", json!("14"))
                    }
                    _ => bail!("unknown typed provider {name}"),
                };
                execution.resume_typed(GeneratedBinding::reply(
                    request,
                    attempt,
                    (name, operation, capability, "UIntRange<256>"),
                    value,
                )?)?;
            }
            other => bail!("unexpected source status {other}"),
        }
    }
    bail!("typed witness exceeded the request bound")
}

fn required_env(name: &str) -> Result<String> {
    env::var(name).with_context(|| format!("missing {name}"))
}

async fn run() -> Result<Json> {
    let bundle_pin = required_env("NOCTIUM_TYPED_WITNESS_MANIFEST_SHA256")?;
    let bundle = artifacts::verify(
        Path::new(&required_env("NOCTIUM_TYPED_WITNESS_BUNDLE")?),
        Some(&bundle_pin),
    )?;
    let plan: Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
    let circuit_sha256 = artifacts::digest(bundle.file(Role::Circuit)?);
    let plan_sha256 = artifacts::digest(bundle.file(Role::Plan)?);
    ensure!(
        circuit_sha256 == EXPECTED_CIRCUIT_SHA256,
        "bundle circuit differs from published K7 typed-witness receipts"
    );
    let cache = ProofCache::new(
        required_env("NOCTIUM_TYPED_WITNESS_PARAMETER_CACHE")?.into(),
        "https://srs.midnight.network/".parse()?,
    )?;
    let parameters = cache.parameters(7).await?;
    ensure!(
        parameters.sha256() == EXPECTED_PARAMETERS_SHA256,
        "unexpected trusted K7 parameter digest"
    );
    let policy = NetworkPolicy {
        network_id: "undeployed".into(),
        genesis: DEVELOPMENT_GENESIS.into(),
        spec_version: 2_001_100,
        transaction_version: 4,
        profile: noctium_runtime::profile::NAME.into(),
        max_dust: 10u128.pow(22),
    };
    let node = Node::connect(
        &required_env("NOCTIUM_TYPED_WITNESS_NODE")?,
        policy.clone(),
        Duration::from_secs(30),
        64 * 1024 * 1024,
        100_000,
    )?;
    let mut seed = [0u8; 32];
    seed[31] = 1;
    node.attach_dust_seed(&seed)?;
    let dust = cache.dust().await?;
    let dust_parameters = cache.parameters(dust.k()).await?;
    let ttl = node.sync()?.block.tblock.to_secs() + 1_800;
    let state_config = br#"{"state":{"total":"0"}}"#;
    let target = WitnessContractTarget::from_state_config(
        ContractBundleSet::new(vec![bundle])?,
        state_config,
        ttl,
        &mut OsRng,
    )?;
    let namespace = format!("rust-typed-witness-{}", target.contract_address());
    let store = DirectoryJournal::new(
        Path::new(&required_env("NOCTIUM_TYPED_WITNESS_JOURNAL")?),
        Duration::from_secs(2),
    )
    .map_err(|_| anyhow!("typed-witness journal unavailable"))?;
    let host = Host {
        node: &node,
        policy: &policy,
        dust: &dust,
        dust_parameters: &dust_parameters,
        store: &store,
        namespace: &namespace,
    };
    ensure!(
        host.private_value()?.is_none(),
        "private fixture namespace is not fresh"
    );
    let descriptor = serde_json::to_vec(&json!({
        "abiVersion": 1,
        "policy": {
            "networkId": policy.network_id,
            "genesis": policy.genesis,
            "specVersion": policy.spec_version,
            "transactionVersion": policy.transaction_version,
            "profile": policy.profile,
            "maxDust": policy.max_dust.to_string()
        },
        "capabilities": {"chain":"chain", "funding":"wallet", "signing":"signer", "journal":"store"}
    }))?;
    let deployment_setup = serde_json::to_vec(&json!({
        "hostContext": host.context(&attempt_id(), false)?,
        "stages": []
    }))?;
    let deployment = target.start_deployment_client("claim", &descriptor, &deployment_setup)?;
    let expected_state =
        |total: &str| create_state(&plan, &BTreeMap::from([("total".into(), json!(total))]));
    let (initial, deployment_receipt) = host
        .finalize(deployment, &expected_state("0")?, false)
        .await?;
    ensure!(
        deployment_receipt["event"] == "Deploy",
        "wrong deployment receipt"
    );

    let operation = target.operation("claim", &parameters, ttl)?;
    let attempt = attempt_id();
    let mut current = Some(initial);
    let mut execution = WitnessExecution::begin_contract_operation(
        &operation,
        &mut current,
        BTreeMap::from([
            ("expected".into(), json!("14")),
            ("seed".into(), json!("7")),
        ]),
        host.context(&attempt, true)?,
        &parameters,
    )?;
    let callbacks = run_source(&mut execution, &attempt)?;
    let mut proof = execution.prepare_contract_proof(&mut OsRng)?;
    let mut proved = proof
        .prove(
            &LocalProver::new(StdRng::from_entropy()),
            &parameters,
            1_048_576,
            pending(),
        )
        .await?;
    ensure!(
        proved.contract_address() == target.contract_address(),
        "proof changed the contract target"
    );
    let (final_state, receipt) = host
        .finalize(
            proved.start_call_client(&descriptor)?,
            &expected_state("14")?,
            true,
        )
        .await?;
    ensure!(receipt["event"] == "Call", "wrong call receipt");
    ensure!(
        receipt["contractAddress"] == target.contract_address(),
        "call changed contract address"
    );
    let finalized = node.finalized_contract_state(target.contract_address())?;
    let state_sha256 = artifacts::digest(&finalized.bytes);
    ensure!(
        state_sha256 == EXPECTED_STATE_SHA256,
        "finalized state differs from browser and Swift receipts"
    );
    ensure!(
        finalized.bytes.len() == 1_482,
        "unexpected finalized state length"
    );
    ensure!(
        receipt["contractStateSha256"] == state_sha256,
        "receipt state hash differs from finalized bytes"
    );
    ensure!(
        receipt["contractStateBytes"] == finalized.bytes.len(),
        "receipt state length differs from finalized bytes"
    );
    ensure!(
        host.private_value()?
            .as_ref()
            .is_some_and(|value| value["value"] == "14"),
        "private commit missing"
    );
    let _ = final_state;

    Ok(json!({
        "entrypoint": "TypedWitness.ScalarWitness.claim",
        "profile": policy.profile,
        "genesis": policy.genesis,
        "manifestSha256": bundle_pin,
        "circuitSha256": circuit_sha256,
        "impactSha256": plan_sha256,
        "parametersSha256": parameters.sha256(),
        "providerCalls": callbacks,
        "sourceResult": "14",
        "privateValue": "14",
        "deployment": deployment_receipt,
        "receipt": receipt,
        "exactState": {"bytes": finalized.bytes.len(), "sha256": state_sha256},
        "privateCommitAfterFinality": true
    }))
}

#[test]
#[ignore = "requires the pinned K7 bundle, SRS/dust cache, and funded Ledger 9 development node"]
fn rust_typed_witness_k7_finalizes_and_commits() {
    println!(
        "{}",
        block_on(run()).expect("Rust K7 typed-witness localnet qualification")
    );
}
