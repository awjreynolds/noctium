#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Plan, Value,
    aggregates::Schema,
    check,
    control::{InvocationTarget, Session},
    create_state,
    foreign::{ForeignFamily, ForeignRole, ForeignType, ForeignValue},
    host::{self, Capability, Context, Limits},
    prepare,
    zkir::IrSource,
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::curve::{EmbeddedFr, EmbeddedGroupAffine, Fr};

const ENTRYPOINT: &str = "inspect";
const ENTRY: &str = "CurveAggregateContract.inspect";
const PAYLOAD_ID: &str = "CurveAggregateContract.Payload";

fn artifact_root() -> PathBuf {
    std::env::var_os("NOCTIUM_CURVE_AGGREGATE_DIR")
        .map(PathBuf::from)
        .expect("set NOCTIUM_CURVE_AGGREGATE_DIR to fresh CurveAggregateContract artifacts")
}

fn foreign(role: ForeignRole, bytes: &[u8]) -> Json {
    let ty = ForeignType::new(ForeignFamily::Secp256k1, role);
    Value::Foreign(ForeignValue::from_bytes(ty, bytes).expect("valid Secp256k1 value"))
        .public_json()
}

fn foreign_zero(role: ForeignRole) -> Json {
    let ty = ForeignType::new(ForeignFamily::Secp256k1, role);
    Value::Foreign(ForeignValue::zero(ty).expect("Secp256k1 zero or identity")).public_json()
}

fn payload(
    jubjub_scalar: u64,
    jubjub_point: EmbeddedGroupAffine,
    secp256k1_base: Json,
    secp256k1_point: Json,
) -> Json {
    let scalar = Value::JubjubScalar(EmbeddedFr::from(jubjub_scalar)).public_json();
    json!({
        "kind": "struct",
        "id": PAYLOAD_ID,
        "fields": [
            {"name":"jubjubScalar", "value":scalar.clone()},
            {"name":"jubjubPoint", "value":Value::JubjubPoint(jubjub_point).public_json()},
            {"name":"secp256k1Base", "value":secp256k1_base},
            {"name":"secp256k1Point", "value":secp256k1_point.clone()},
            {"name":"pair", "value":{"kind":"tuple", "items":[scalar, secp256k1_point]}}
        ]
    })
}

fn wire_session(control: &Json, value: Json) -> Result<Session> {
    let binding_text = control["binding"].as_str().expect("witness binding");
    let pin = hex::encode(Sha256::digest(binding_text.as_bytes()));
    Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([("payload".into(), value)]),
        Context {
            protocol_version: 1,
            namespace: "noctium".into(),
            base_revision: "r0".into(),
            attempt_id: "b".repeat(64),
            capabilities: vec![Capability {
                id: "commit".into(),
                namespace: "noctium".into(),
                key_prefix: "noctium/".into(),
                operations: vec![host::CAS.into()],
            }],
            operations: vec![],
            providers: vec![],
            commit_capability: "commit".into(),
            limits: Limits::default(),
        },
        Some(&pin),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: ENTRYPOINT.into(),
        }),
    )
}

fn native_inputs(
    plan: &Plan,
    schema: &Schema,
    payload: &Json,
    completion: &Json,
) -> Result<BTreeMap<String, Json>> {
    let leaves = schema.flatten_leaves_json(&serde_json::to_vec(payload)?)?;
    assert_eq!(leaves.len(), plan.circuit.inputs.len());
    assert_eq!(leaves.len(), 16);
    for input in &plan.circuit.inputs {
        assert_eq!(input.ty, "Native");
        assert_eq!(input.visibility, "public");
    }
    let expected: BTreeMap<_, _> = plan
        .circuit
        .inputs
        .iter()
        .zip(leaves)
        .map(|(input, leaf)| (input.name.clone(), leaf))
        .collect();
    let actual: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;
    assert_eq!(actual, expected);
    Ok(actual)
}

#[test]
#[ignore = "requires fresh CurveAggregateContract artifacts in NOCTIUM_CURVE_AGGREGATE_DIR"]
fn nested_curve_aggregate_roundtrips_and_rejects_bad_public_data() -> Result<()> {
    let root = artifact_root();
    let control: Json = serde_json::from_slice(&fs::read(
        root.join(format!("{ENTRY}.witness.control.json")),
    )?)?;
    let binding: Json = serde_json::from_str(control["binding"].as_str().expect("binding"))?;
    let plan: Plan = serde_json::from_slice(&fs::read(root.join(format!("{ENTRY}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(root.join(format!("{ENTRY}.zkir")))?)?;
    let view = plan
        .return_views
        .iter()
        .find(|view| view.name == "echoedPayload")
        .expect("nested echoedPayload return view");
    let schema = Schema::from_json(&serde_json::to_vec(&view.schema)?)?;
    assert_eq!(
        view.schema["layout"]["id"], PAYLOAD_ID,
        "return view keeps the checked payload identity"
    );
    let initial = create_state(&plan, &BTreeMap::new())?;
    let secp_generator =
        hex::decode("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")?;
    let mut base_42 = vec![0; 32];
    base_42[0] = 42;
    let cases = [
        (
            "identity",
            payload(
                0,
                EmbeddedGroupAffine::identity(),
                foreign_zero(ForeignRole::Base),
                foreign_zero(ForeignRole::Point),
            ),
            "0",
        ),
        (
            "generator",
            payload(
                17,
                EmbeddedGroupAffine::generator() * EmbeddedFr::from(17u64),
                foreign(ForeignRole::Base, &base_42),
                foreign(ForeignRole::Point, &secp_generator),
            ),
            "17",
        ),
    ];

    for (case_name, value, expected_scalar) in cases {
        let mut session = wire_session(&control, value.clone())?;
        assert_eq!(session.advance()?["status"], "completed", "{case_name}");
        let completion = session.private_completion(&binding["nativeRelation"])?;
        let inputs = native_inputs(&plan, &schema, &value, &completion)?;
        let mut execution = prepare(
            &plan,
            &inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )?;
        check(&execution, &circuit)?;
        let returns = execution.returns_json();
        assert_eq!(returns["echoedPayload"], value, "{case_name}");
        assert_eq!(
            returns["jubjubScalar"],
            json!(expected_scalar),
            "{case_name}"
        );
        assert_eq!(returns["base"], value["fields"][2]["value"], "{case_name}");

        let original = execution.preimage.public_transcript_outputs[0];
        execution.preimage.public_transcript_outputs[0] = original + Fr::from(1u64);
        assert!(
            check(&execution, &circuit).is_err(),
            "tampered {case_name} transcript"
        );
    }

    let mut malformed = payload(
        0,
        EmbeddedGroupAffine::identity(),
        foreign_zero(ForeignRole::Base),
        foreign_zero(ForeignRole::Point),
    );
    malformed["fields"][1]["value"]["x"] = json!("0");
    malformed["fields"][1]["value"]["y"] = json!("0");
    match wire_session(&control, malformed) {
        Ok(mut session) => assert_eq!(session.advance()?["status"], "failed"),
        Err(_) => {}
    }
    Ok(())
}
