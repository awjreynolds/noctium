use super::*;
use ledger::structure::{ContractAction, ProofVersioned};
use rand::{SeedableRng, rngs::StdRng};
use serde_json::json;
use std::{env, fs, path::PathBuf};

fn freshly_emitted(suffix: &str) -> Vec<u8> {
    let directory = env::var_os("NOCTIUM_GUARDED_READS_DIR")
        .expect("set NOCTIUM_GUARDED_READS_DIR to freshly emitted Issue43 artifacts");
    fs::read(PathBuf::from(directory).join(format!("Issue43GuardedReads.update.{suffix}")))
        .expect("read freshly emitted guarded-read artifact")
}

#[test]
#[ignore = "requires freshly emitted guarded-read artifacts and a pinned official SRS"]
fn guarded_reads_generate_and_bind_a_native_v3_proof() {
    let impact = freshly_emitted("impact.json");
    let zkir = freshly_emitted("zkir");
    let plan: Plan = serde_json::from_slice(&impact).expect("fresh Impact plan parses");
    assert!(plan.reads.iter().any(|read| {
        read.name == "markerValue"
            && matches!(
                read.guard.as_ref(),
                Some(crate::Expr::Reference { name }) if name == "enabled"
            )
    }));
    let circuit = IrSource::load(zkir.as_slice()).expect("fresh ZKIR circuit parses");
    let k = circuit.k();
    eprintln!("guarded-read generated circuit k={k}");

    let srs_path = env::var_os("NOCTIUM_GUARDED_READS_SRS")
        .expect("set NOCTIUM_GUARDED_READS_SRS to the official SRS for this circuit k");
    let srs = fs::read(srs_path).expect("read official circuit SRS");
    let digest = env::var("NOCTIUM_GUARDED_READS_SRS_SHA256")
        .expect("set NOCTIUM_GUARDED_READS_SRS_SHA256 to its pinned catalog digest");
    let parameters = TrustedParameters::from_bytes(&srs, k, &digest)
        .expect("official SRS encoding and catalog digest match the generated circuit");
    let (prover, verifier) = futures::executor::block_on(circuit.keygen(&parameters))
        .expect("fresh native proving and verification keys generate");

    let material = Material {
        native: ProvingKeyMaterial {
            prover_key: encode(&prover).expect("proving key serializes in memory"),
            verifier_key: encode(&verifier).expect("verification key serializes in memory"),
            ir_source: zkir,
        },
        prover,
        circuit,
        verifier,
        parameters: ledger::structure::INITIAL_PARAMETERS.clone(),
        entrypoint: plan.entrypoint.clone(),
    };
    let config = Config {
        inputs: BTreeMap::from([
            ("account".to_owned(), json!("7")),
            ("enabled".to_owned(), json!(true)),
        ]),
        state: BTreeMap::from([
            ("marker".to_owned(), json!("23")),
            ("balances".to_owned(), json!([])),
        ]),
        negative_cases: Vec::new(),
    };
    let (deployment, intent) = crate::assembly::prepare_call(
        &plan,
        &config,
        &ledger::structure::INITIAL_PARAMETERS,
        material.verifier.clone(),
        &material.circuit,
        1_800_000_000,
        None,
        &mut StdRng::from_seed([7; 32]),
    )
    .expect("native call uses account=7, enabled=true, marker=23 and no balances");
    drop(deployment);

    let source_call = match intent.actions.iter_deref().next() {
        Some(ContractAction::Call(call)) => call.clone(),
        _ => panic!("native preparation emits one source call"),
    };
    let source_binding = intent.binding_commitment.into();
    let mut prepared = PreparedProof::freeze(material, intent).expect("freeze native call");
    assert!(prepared.activity.iter().any(Option::is_none));
    assert!(prepared.activity.iter().any(Option::is_some));

    let proved = futures::executor::block_on(prepared.prove(
        &LocalProver::new(rand::rngs::OsRng),
        &parameters,
        MAX_RESPONSE,
        futures::future::pending(),
    ))
    .expect("local native prover attaches a V3 proof");
    let Some(ContractAction::Call(attached_call)) = proved.native().actions.iter_deref().next()
    else {
        panic!("proved native intent retains its call")
    };
    let ProofVersioned::V3(attached_proof) = &attached_call.proof else {
        panic!("native ledger call carries a V3 proof")
    };
    let attached_fields = attached_call
        .public_inputs(proved.native().binding_commitment.into())
        .expect("attached V3 call exposes its exact public fields");
    assert_eq!(attached_fields, prepared.statement);

    let response = encode(&ProofVersioned::V2(attached_proof.clone()))
        .expect("preserved proof serializes in the native service format");
    prepared
        .verify_response(&parameters, &response, MAX_RESPONSE)
        .expect("preserved proof verifies against its frozen public fields");

    let marker_fields = prepared
        .statement
        .iter()
        .enumerate()
        .skip(2)
        .filter_map(|(index, field)| (*field == Fr::from(23u64)).then_some(index))
        .collect::<Vec<_>>();
    assert_eq!(marker_fields.len(), 1, "marker read has one public field");
    let marker_field = marker_fields[0];
    prepared.statement[marker_field] = Fr::from(24u64);
    assert_eq!(
        prepared.verify_response(&parameters, &response, MAX_RESPONSE),
        Err(Error::InvalidProof),
        "changing the active marker read field invalidates the preserved proof"
    );
    let active_reads = prepared
        .preimage()
        .expect("frozen call retains its proof preimage")
        .public_transcript_outputs
        .len();

    let statement_path = env::var_os("NOCTIUM_GUARDED_READS_STATEMENT_FILE");
    if let Some(path) = statement_path {
        let statement = crate::proof::guarded_partials::native_statement(
            &source_call,
            source_binding,
            &attached_fields,
        );
        fs::write(
            path,
            serde_json::to_vec_pretty(&statement).expect("native statement serializes as JSON"),
        )
        .expect("write native statement fixture to requested path");
    }

    eprintln!(
        "guarded-read native proof passed: k={k}, fields={}, active_reads={}, active_ops={}, skipped_ops={}, proof_bytes={}",
        attached_fields.len(),
        active_reads,
        prepared
            .activity
            .iter()
            .filter(|entry| entry.is_none())
            .count(),
        prepared
            .activity
            .iter()
            .filter(|entry| entry.is_some())
            .count(),
        attached_proof.0.len(),
    );
}
