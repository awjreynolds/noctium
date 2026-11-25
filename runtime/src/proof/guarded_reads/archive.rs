use super::{ContractAction, ProofVersioned, freshly_emitted, localnet::state_fields};
use crate::{
    Db,
    artifacts::digest,
    client::{ChainIdentity, ContractEvent, NetworkPolicy},
    field_decimal,
    funding::CONTRACT_SEGMENT,
    localnet::{DEVELOPMENT_GENESIS, Node, Rpc},
    proof::{TrustedParameters, encode},
    zkir::IrSource,
};
use ledger::structure::{PedersenDowngradeable, Transaction};
use onchain_runtime::state::EntryPointBuf;
use serde_json::Value;
use std::{env, fs, time::Duration};
use transient_crypto::{
    commitment::PureGeneratorPedersen,
    curve::Fr,
    proofs::{ParamsVerifier, Zkir},
};

mod chain;

const RECEIPT: &str =
    include_str!("../../../../docs/development/native-guarded-read-localnet-receipt.json");

#[test]
#[ignore = "requires the retained development chain, rebuilt guarded-read artifacts, and pinned SRS"]
fn finalized_guarded_proof_verifies_with_the_installed_key() {
    let receipt: Value = serde_json::from_str(RECEIPT).expect("published receipt decodes");
    let proof_record = &receipt["proof"];
    assert_eq!(proof_record["version"], 3);
    let entrypoint = proof_record["entryPoint"].as_str().expect("entrypoint");
    let address = receipt["contractAddress"]
        .as_str()
        .expect("contract address");

    let impact = freshly_emitted("impact.json");
    let zkir = freshly_emitted("zkir");
    assert_eq!(digest(&impact), receipt["impactSha256"]);
    assert_eq!(digest(&zkir), receipt["zkirSha256"]);
    let circuit = IrSource::load(zkir.as_slice()).expect("rebuilt ZKIR decodes");
    assert_eq!(circuit.k(), 8);
    let srs_path = env::var_os("NOCTIUM_GUARDED_READS_SRS").expect("set the official k=8 SRS path");
    let srs = fs::read(srs_path).expect("read the official SRS");
    let srs_digest = proof_record["srsSha256"].as_str().expect("SRS digest");
    let parameters = TrustedParameters::from_bytes(&srs, circuit.k(), srs_digest)
        .expect("SRS digest, encoding and degree match");
    let verifier_parameters = ParamsVerifier::read(srs.as_slice()).expect("read verifier SRS");

    let endpoint = env::var("NOCTIUM_GUARDED_READS_NODE").expect("set the retained localnet URL");
    let policy = NetworkPolicy {
        network_id: "undeployed".into(),
        genesis: DEVELOPMENT_GENESIS.into(),
        spec_version: 2_001_100,
        transaction_version: 4,
        profile: crate::profile::NAME.into(),
        max_dust: 10u128.pow(22),
    };
    let timeout = Duration::from_secs(30);
    let max_response = 64 * 1024 * 1024;
    let node = Node::connect(&endpoint, policy.clone(), timeout, max_response, 100_000)
        .expect("connect to the retained localnet");
    let rpc = Rpc::new(&endpoint, timeout, max_response).expect("create read-only RPC client");
    let (runtime_code, metadata) = node.runtime_fingerprint();
    assert_eq!(runtime_code, receipt["runtimeCodeHash"]);
    assert_eq!(metadata, receipt["metadataSha256"]);
    let expected_identity: ChainIdentity =
        serde_json::from_value(receipt["chain"].clone()).expect("published chain identity");
    let deployed_at = receipt["deployment"]["blockHash"]
        .as_str()
        .expect("deployment block");
    let called_at = receipt["call"]["blockHash"].as_str().expect("call block");
    for block in [deployed_at, called_at] {
        node.check_runtime(block)
            .expect("historical runtime and metadata match");
        assert_eq!(
            rpc.chain_identity(block, &policy.profile)
                .expect("historical chain identity"),
            expected_identity
        );
    }
    let (_, deployed_state) = chain::read_finalized_transaction(
        &node,
        &rpc,
        &policy,
        address,
        &receipt["deployment"],
        ContractEvent::Deploy,
    );
    let (sealed_call, call_state) = chain::read_finalized_transaction(
        &node,
        &rpc,
        &policy,
        address,
        &receipt["call"],
        ContractEvent::Call,
    );
    let (marker, balance) = state_fields(&call_state).expect("read archived guarded values");
    assert_eq!(
        receipt["observedState"],
        serde_json::json!({
            "blockHash": called_at,
            "height": receipt["call"]["height"],
            "marker": field_decimal(marker),
            "balances": {"7": field_decimal(balance)},
        })
    );

    let entry = EntryPointBuf(entrypoint.as_bytes().to_vec());
    let deployed_operation = deployed_state
        .operations
        .get(&entry)
        .expect("deployed operation");
    let installed = deployed_operation
        .v3_vk()
        .expect("deployed V3 verifier key");
    let call_operation = call_state
        .operations
        .get(&entry)
        .expect("operation at the call block");
    let call_key = call_operation
        .v3_vk()
        .expect("V3 verifier key at the call block");
    let key_bytes = encode(installed).expect("serialize the installed verifier");
    assert_eq!(
        key_bytes,
        encode(call_key).expect("serialize the call-block verifier")
    );
    assert_eq!(digest(&key_bytes), proof_record["verifierKeySha256"]);
    let (_, regenerated) = futures::executor::block_on(circuit.keygen(&parameters))
        .expect("regenerate the verifier from the rebuilt ZKIR and checked SRS");
    assert_eq!(
        key_bytes,
        encode(&regenerated).expect("serialize the regenerated verifier")
    );

    let Transaction::Standard(transaction) = sealed_call else {
        panic!("archived call must be a standard transaction");
    };
    let intent = transaction
        .intents
        .get(&CONTRACT_SEGMENT)
        .expect("contract intent");
    assert_eq!(intent.actions.len(), 1);
    let Some(ContractAction::Call(call)) = intent.actions.iter_deref().next() else {
        panic!("archived action must be a contract call");
    };
    assert_eq!(hex::encode(call.address.0.0), address);
    assert_eq!(call.entry_point.0, entrypoint.as_bytes());
    let ProofVersioned::V3(proof) = &call.proof else {
        panic!("archived call must carry a V3 proof");
    };
    assert_eq!(digest(&proof.0), proof_record["proofSha256"]);
    let binding =
        <PureGeneratorPedersen as PedersenDowngradeable<Db>>::downgrade(&intent.binding_commitment);
    let mut fields = call
        .public_inputs(binding)
        .expect("archived call public inputs");
    assert_eq!(
        Some(fields.len() as u64),
        proof_record["publicFieldCount"].as_u64()
    );
    let decimal: Vec<_> = fields.iter().copied().map(field_decimal).collect();
    let statement = serde_json::to_vec(&decimal).expect("encode ordered decimal field strings");
    assert_eq!(digest(&statement), proof_record["publicFieldsSha256"]);
    installed
        .verify(&verifier_parameters, proof, fields.iter().copied())
        .expect("installed verifier accepts the archived proof and its exact statement");
    fields[0] = fields[0] + Fr::from(1u64);
    assert!(
        installed
            .verify(&verifier_parameters, proof, fields.into_iter())
            .is_err()
    );
    eprintln!(
        "finalized guarded-read call at {called_at}: verified archived V3 proof, regenerated key and {} public fields",
        decimal.len()
    );
}
