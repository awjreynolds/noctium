//! Opt-in Ledger 9 qualification for public OpaqueBytes Map storage and reads.
use anyhow::{Context, Result, anyhow, bail, ensure};
use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use coin_structure::contract::ContractAddress;
use futures::{executor::block_on, future::pending};
use ledger::structure::ProofPreimageVersioned;
use noctium_runtime::{
    Db, Plan,
    artifacts::{self, ContractBundleSet, Role},
    client::{ChainAdapter, FundingAdapter, JournalStore, NetworkPolicy, SigningAdapter, Snapshot},
    funding::{DustMaterial, FeePolicy, UnsealedTransaction},
    host,
    localnet::{DevelopmentFunding, ExplicitSeal, Node, ProofCache, journal::DirectoryJournal},
    proof::{CurrentStateContext, LocalProver, TrustedParameters, WitnessContractTarget},
    witness_execution::{
        WitnessClient, WitnessClientCommand as Command, WitnessClientReply as Reply,
    },
    zkir::IrSource,
};
use onchain_runtime::state::{ContractState, StateValue};
use rand::{
    RngCore, SeedableRng,
    rngs::{OsRng, StdRng},
};
use serde::Deserialize;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{
    collections::BTreeMap,
    io::Read,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};
use transient_crypto::{curve::Fr, fab::AlignedValueExt, proofs::Zkir};
use zeroize::Zeroizing;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Configuration {
    endpoint: String,
    policy: NetworkPolicy,
    store_bundle: PathBuf,
    store_manifest_sha256: String,
    read_bundle: PathBuf,
    read_manifest_sha256: String,
    parameter_cache: PathBuf,
    parameter_source: String,
    journal_directory: PathBuf,
    receipt_output: PathBuf,
    approve_local_development: bool,
    wait_seconds: u64,
}

fn read(path: &Path, limit: usize) -> Result<Zeroizing<Vec<u8>>> {
    let mut bytes = Zeroizing::new(Vec::new());
    std::fs::File::open(path)?
        .take(limit as u64 + 1)
        .read_to_end(&mut bytes)?;
    ensure!(bytes.len() <= limit, "host file exceeds byte limit");
    Ok(bytes)
}

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

fn address_bytes(value: &str) -> Result<ContractAddress> {
    let bytes: [u8; 32] = hex::decode(value)?
        .try_into()
        .map_err(|_| anyhow!("invalid contract address"))?;
    Ok(ContractAddress(base_crypto::hash::HashOutput(bytes)))
}

fn compressed(bytes: &[u8]) -> Result<AlignedValue> {
    AlignedValue::new(
        FabValue(vec![ValueAtom::from(bytes)]),
        Alignment::singleton(AlignmentAtom::Compress),
    )
    .ok_or_else(|| anyhow!("invalid Compress bytes"))
}

fn assert_stored(
    state: &ContractState<Db>,
    plan: &Plan,
    key: &[u8; 32],
    expected: &[u8],
) -> Result<()> {
    let StateValue::Array(slots) = state.data.get_ref() else {
        bail!("expected native state slots");
    };
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == "payloads")
        .context("payload map declaration missing")?;
    let StateValue::Map(payloads) = &*slots.get(slot).context("payload map slot missing")? else {
        bail!("expected OpaqueBytes map");
    };
    let key: AlignedValue = (*key).into();
    let StateValue::Cell(value) = &*payloads.get(&key).context("stored payload entry missing")?
    else {
        bail!("expected OpaqueBytes cell");
    };
    ensure!(
        **value == compressed(expected)?,
        "finalized public map value differs from raw Compress bytes"
    );
    Ok(())
}

fn check_read_return(execution: &noctium_runtime::Execution, expected: &[u8]) -> Result<Vec<Fr>> {
    ensure!(
        execution.returns_json().get("payload")
            == Some(&json!({"kind":"opaqueBytes", "values":expected})),
        "native read return differs from expected OpaqueBytes"
    );
    let returns = execution.returns();
    ensure!(
        returns.len() == 1 && returns[0].0 == "payload",
        "unexpected native read outputs"
    );
    ensure!(
        returns[0].1.public_json() == json!({"kind":"opaqueBytes", "values":expected}),
        "typed native read return differs from expected OpaqueBytes"
    );
    let mut projection = Vec::new();
    compressed(expected)?.value_only_field_repr(&mut projection);
    ensure!(projection.len() == 1, "expected one Compress field");
    ensure!(
        execution.preimage.public_transcript_outputs.len() == 3,
        "unexpected native output transcript shape"
    );
    ensure!(
        &execution.preimage.public_transcript_outputs[2..] == projection.as_slice(),
        "native read return is not bound to the expected Compress field"
    );
    Ok(projection)
}

fn check_frozen_read_output(intent_bytes: &[u8], expected: &[Fr]) -> Result<()> {
    let intent: noctium_runtime::assembly::NativeIntent = decode(intent_bytes)?;
    let Some(ledger::structure::ContractAction::Call(call)) = intent.actions.iter_deref().next()
    else {
        bail!("read proof did not freeze one contract call");
    };
    ensure!(
        call.entry_point.0 == b"read",
        "read proof selected the wrong entrypoint"
    );
    let ProofPreimageVersioned::V2(preimage) = &call.proof else {
        bail!("read proof uses an unsupported preimage version");
    };
    ensure!(
        preimage.public_transcript_outputs.len() == expected.len() + 2
            && &preimage.public_transcript_outputs[2..] == expected,
        "frozen proof does not bind the expected OpaqueBytes return"
    );
    Ok(())
}

struct Host {
    node: Node,
    dust: DustMaterial,
    dust_parameters: TrustedParameters,
    journal: DirectoryJournal,
    policy: NetworkPolicy,
    wait: Duration,
}

impl Host {
    fn setup(&self, address: &str) -> Result<Vec<u8>> {
        let namespace = format!("opaque-map-{}", &address[..16]);
        let base_revision = self
            .journal
            .revision(&namespace)
            .map_err(|_| anyhow!("journal revision unavailable"))?;
        let context = json!({
            "protocolVersion":1,
            "namespace":namespace,
            "baseRevision":base_revision,
            "attemptId":attempt_id(),
            "capabilities":[{"id":"store","namespace":namespace,"keyPrefix":"opaque/","operations":[host::STAGE,host::CAS]}],
            "operations":[],
            "providers":[],
            "commitCapability":"store"
        });
        Ok(serde_json::to_vec(
            &json!({"hostContext":context,"stages":[]}),
        )?)
    }

    async fn finish(
        &mut self,
        mut client: WitnessClient,
        expected_address: &str,
        expected_event: &str,
    ) -> Result<(Vec<u8>, ContractState<Db>, CurrentStateContext, Json)> {
        if client.status()["busy"] != true {
            client.command(Command::Prepare)?;
        }
        let mut snapshot: Option<Snapshot> = None;
        let mut journal_revision = None;
        let deadline = Instant::now() + self.wait;
        loop {
            let status = client.poll()?;
            if let Some(request) = client.request()? {
                let payload = || {
                    request
                        .private_payload()
                        .context("private service payload missing")
                };
                let reply = match request.metadata["operation"]
                    .as_str()
                    .context("missing service operation")?
                {
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
                    "funding.native.v1" => {
                        let intent = decode(payload()?)?;
                        let funding = DevelopmentFunding::new(
                            &self.node,
                            &self.dust,
                            &self.dust_parameters,
                            FeePolicy {
                                max_dust: self.policy.max_dust,
                                margin_blocks: 3,
                                max_spends: 8,
                            },
                            StdRng::from_entropy(),
                        );
                        Reply::Funded(
                            funding
                                .fund(
                                    &intent,
                                    snapshot.as_ref().context("funding snapshot missing")?,
                                    &self.policy,
                                )
                                .await
                                .map_err(|_| anyhow!("native funding failed"))?,
                        )
                    }
                    "approval.sign.v1" => {
                        let transaction = decode::<UnsealedTransaction>(payload()?)?;
                        let signer = ExplicitSeal::new(
                            |_: &UnsealedTransaction, policy: &NetworkPolicy| {
                                *policy == self.policy
                            },
                            StdRng::from_entropy(),
                        );
                        Reply::Signed(
                            signer
                                .approve_and_sign(
                                    &transaction,
                                    snapshot.as_ref().context("signing snapshot missing")?,
                                    &self.policy,
                                )
                                .await
                                .map_err(|_| anyhow!("native signing failed"))?,
                        )
                    }
                    "chain.submit.v1" => Reply::Submitted(
                        self.node
                            .submit(request.transaction().context("submit binding missing")?)
                            .await
                            .map_err(|_| anyhow!("native submission unresolved"))?,
                    ),
                    "chain.observe.v1" => Reply::Observed(
                        self.node
                            .observe(request.transaction().context("observe binding missing")?)
                            .await
                            .map_err(|_| anyhow!("finalized receipt observation failed"))?,
                    ),
                    "journal.persist.v1" => {
                        let record = serde_json::from_slice(payload()?)?;
                        let ack = self
                            .journal
                            .persist(&record, journal_revision)
                            .await
                            .map_err(|_| anyhow!("journal persistence failed"))?;
                        journal_revision = Some(ack.revision);
                        Reply::Persisted(ack)
                    }
                    "journal.load.v1" => {
                        let id = std::str::from_utf8(payload()?)?;
                        let loaded = self
                            .journal
                            .load(id)
                            .await
                            .map_err(|_| anyhow!("journal recovery failed"))?;
                        journal_revision = Some(loaded.revision);
                        Reply::Loaded(loaded)
                    }
                    "private_state.compare_exchange.v1" => {
                        let record = serde_json::from_slice(payload()?)?;
                        Reply::Cas(
                            self.journal
                                .compare_exchange(&record)
                                .await
                                .map_err(|_| anyhow!("journal CAS failed"))?,
                        )
                    }
                    other => bail!("unsupported native host request: {other}"),
                };
                client.complete(request.id, reply)?;
                continue;
            }
            ensure!(
                status["status"] != "failed" && status["status"] != "step_error",
                "native client step failed: {status}"
            );
            if status["busy"] == true {
                continue;
            }
            match status["phase"].as_str().unwrap_or("") {
                "Prepared" => {
                    client.command(Command::Submit)?;
                }
                "Submitted" | "Uncertain" => {
                    ensure!(
                        Instant::now() < deadline,
                        "submission unresolved, preserve this attempt for recovery"
                    );
                    std::thread::sleep(Duration::from_millis(500));
                    client.command(Command::Observe)?;
                }
                "AwaitingCas" => {
                    client.command(Command::Commit)?;
                }
                "Committed" => {
                    if status["receipt"].is_null() || status["privateAcknowledged"] != true {
                        client.command(if status["receipt"].is_null() {
                            Command::Observe
                        } else {
                            Command::Commit
                        })?;
                        continue;
                    }
                    let receipt = status["receipt"].clone();
                    ensure!(
                        receipt["event"] == expected_event,
                        "unexpected finalized event"
                    );
                    ensure!(
                        receipt["contractAddress"] == expected_address,
                        "operation changed contract address"
                    );
                    let bytes = client.receipt_state()?;
                    let state = decode(&bytes)?;
                    let current = client.current_state_context()?;
                    return Ok((bytes, state, current, receipt));
                }
                "Rejected" | "Failed" | "Conflicted" | "Cancelled" => {
                    bail!("native lifecycle terminated: {}", status["phase"])
                }
                _ => bail!("native client stopped without a terminal phase: {status}"),
            }
        }
    }
}

async fn run(configuration: Configuration) -> Result<()> {
    ensure!(
        configuration.approve_local_development,
        "explicit local development approval required"
    );
    ensure!(
        (1..=300).contains(&configuration.wait_seconds),
        "invalid observation deadline"
    );
    ensure!(
        configuration.policy.genesis == noctium_runtime::localnet::DEVELOPMENT_GENESIS,
        "fixture only accepts the isolated development genesis"
    );

    let store_bundle = artifacts::verify(
        &configuration.store_bundle,
        Some(&configuration.store_manifest_sha256),
    )?;
    let read_bundle = artifacts::verify(
        &configuration.read_bundle,
        Some(&configuration.read_manifest_sha256),
    )?;
    let store_plan: Plan = serde_json::from_slice(store_bundle.file(Role::Plan)?)?;
    let read_plan: Plan = serde_json::from_slice(read_bundle.file(Role::Plan)?)?;
    ensure!(
        store_plan.entrypoint == "store" && read_plan.entrypoint == "read",
        "bundle entrypoint mismatch"
    );
    let store_circuit = IrSource::load(store_bundle.file(Role::Circuit)?)?;
    let read_circuit = IrSource::load(read_bundle.file(Role::Circuit)?)?;

    let node = Node::connect(
        &configuration.endpoint,
        configuration.policy.clone(),
        Duration::from_secs(30),
        64 * 1024 * 1024,
        100_000,
    )?;
    let mut seed = Zeroizing::new([0; 32]);
    seed[31] = 1;
    node.attach_dust_seed(&*seed)?;
    drop(seed);
    let snapshot = node.sync()?;
    let cache = ProofCache::new(
        configuration.parameter_cache,
        reqwest::Url::parse(&configuration.parameter_source)?,
    )?;
    let dust = cache.dust().await?;
    let dust_parameters = cache.parameters(dust.k()).await?;
    let store_parameters = cache.parameters(store_circuit.k()).await?;
    let read_parameters = cache.parameters(read_circuit.k()).await?;
    let set = ContractBundleSet::new(vec![store_bundle, read_bundle])?;
    let deployment_ttl = snapshot.block.tblock.to_secs() + 1800;
    let target = WitnessContractTarget::from_state_config(
        set,
        br#"{"state":{"payloads":[]}}"#,
        deployment_ttl,
        &mut OsRng,
    )?;
    let address = target.contract_address().to_owned();
    let journal = DirectoryJournal::new(&configuration.journal_directory, Duration::from_secs(2))
        .map_err(|_| anyhow!("journal unavailable"))?;
    let policy = configuration.policy;
    let descriptor = serde_json::to_vec(&json!({
        "abiVersion":1,
        "policy":{"networkId":policy.network_id,"genesis":policy.genesis,"specVersion":policy.spec_version,"transactionVersion":policy.transaction_version,"profile":policy.profile,"maxDust":policy.max_dust.to_string()},
        "capabilities":{"chain":"chain","funding":"wallet","signing":"signer","journal":"store"}
    }))?;
    let mut host = Host {
        node,
        dust,
        dust_parameters,
        journal,
        policy,
        wait: Duration::from_secs(configuration.wait_seconds),
    };

    let setup = host.setup(&address)?;
    let deployment = target.start_deployment_client("store", &descriptor, &setup)?;
    let (_, _, current, deploy_receipt) = host.finish(deployment, &address, "Deploy").await?;

    let key = [0x22; 32];
    let payload = [0x00, 0x01, 0xff];
    let store_operation = target.operation(
        "store",
        &store_parameters,
        host.node.sync()?.block.tblock.to_secs() + 1800,
    )?;
    let mut state_token = Some(current);
    let store_prepared = store_operation.prepare_call(
        &mut state_token,
        &store_parameters,
        BTreeMap::from([
            (
                "key".into(),
                json!({"kind":"bytes","values":key.as_slice()}),
            ),
            (
                "payload".into(),
                json!({"kind":"opaqueBytes","values":payload}),
            ),
        ]),
        &mut OsRng,
    )?;
    ensure!(
        state_token.is_none(),
        "store preparation did not consume its state token"
    );
    let store_proved = store_prepared
        .prove(
            &LocalProver::new(StdRng::from_entropy()),
            &store_parameters,
            1_048_576,
            pending(),
        )
        .await?;
    let mut store_proved = Some(store_proved);
    let setup = host.setup(&address)?;
    let store_client =
        target.start_call_client(&store_operation, &mut store_proved, &descriptor, &setup)?;
    let (store_state_bytes, store_state, current, store_receipt) =
        host.finish(store_client, &address, "Call").await?;
    assert_stored(&store_state, &store_plan, &key, &payload)?;

    let live = host.node.sync()?;
    let read_inputs = BTreeMap::from([(
        "key".into(),
        json!({"kind":"bytes","values":key.as_slice()}),
    )]);
    let contract_address = address_bytes(&address)?;
    let read_execution = noctium_runtime::prepare(
        &read_plan,
        &read_inputs,
        &store_state.data,
        &live.state.parameters,
        contract_address,
    )?;
    noctium_runtime::check(&read_execution, &read_circuit)?;
    let expected_projection = check_read_return(&read_execution, &payload)?;

    let read_operation =
        target.operation("read", &read_parameters, live.block.tblock.to_secs() + 1800)?;
    let mut state_token = Some(current);
    let read_prepared =
        read_operation.prepare_call(&mut state_token, &read_parameters, read_inputs, &mut OsRng)?;
    ensure!(
        state_token.is_none(),
        "read preparation did not consume its state token"
    );
    check_frozen_read_output(&read_prepared.private_intent_bytes()?, &expected_projection)?;
    let read_proved = read_prepared
        .prove(
            &LocalProver::new(StdRng::from_entropy()),
            &read_parameters,
            1_048_576,
            pending(),
        )
        .await?;
    let mut read_proved = Some(read_proved);
    let setup = host.setup(&address)?;
    let read_client =
        target.start_call_client(&read_operation, &mut read_proved, &descriptor, &setup)?;
    let (read_state_bytes, _, _current, read_receipt) =
        host.finish(read_client, &address, "Call").await?;
    ensure!(
        store_state_bytes == read_state_bytes,
        "read changed finalized contract state"
    );

    let report = json!({
        "schemaVersion":1,
        "profile":noctium_runtime::profile::NAME,
        "contractAddress":target.contract_address(),
        "payload":{"kind":"opaqueBytes","values":payload},
        "checks":{"deploymentFinalized":true,"storeProofAccepted":true,"rawCompressMapCellMatched":true,"readProofReturnMatched":true,"readTranscriptOutputMatched":true,"readFinalizedStateUnchanged":true},
        "receipts":{"deploy":deploy_receipt,"store":store_receipt,"read":read_receipt},
        "storeStateBytes":store_state_bytes.len(),
        "storeStateSha256":hex::encode(Sha256::digest(&store_state_bytes)),
        "readStateBytes":read_state_bytes.len(),
        "readStateSha256":hex::encode(Sha256::digest(&read_state_bytes))
    });
    if let Some(parent) = configuration.receipt_output.parent() {
        std::fs::create_dir_all(parent)?;
    }
    std::fs::write(
        &configuration.receipt_output,
        serde_json::to_vec_pretty(&report)?,
    )?;
    println!("{report}");
    Ok(())
}

fn main() {
    let result = (|| -> Result<()> {
        let mut args = std::env::args_os().skip(1);
        let path = args
            .next()
            .context("usage: opaque_byte_map_localnet HOST_CONFIG.json")?;
        ensure!(
            args.next().is_none(),
            "usage: opaque_byte_map_localnet HOST_CONFIG.json"
        );
        let bytes = read(Path::new(&path), 32_768)?;
        let configuration =
            serde_json::from_slice(&bytes).map_err(|_| anyhow!("invalid host configuration"))?;
        block_on(run(configuration))
    })();
    if let Err(error) = result {
        eprintln!("opaque byte map localnet failed: {error}");
        std::process::exit(1);
    }
}
