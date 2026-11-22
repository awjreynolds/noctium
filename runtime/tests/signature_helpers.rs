#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Plan, check,
    control::{InvocationTarget, Session, TypedResponse},
    create_state, field_decimal,
    host::{self, Capability, Context, Limits, Operation, Provider},
    prepare,
    zkir::IrSource,
};
use num_bigint::BigUint;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::curve::{EmbeddedFr, EmbeddedGroupAffine, Fr};
use transient_crypto::hash::transient_hash;

const PLAN: &str =
    include_str!("fixtures/signature-helpers/321/SignatureChecks.verify.impact.json");
const CIRCUIT: &[u8] = include_bytes!("fixtures/signature-helpers/321/SignatureChecks.verify.zkir");

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes","values":value})
}

fn foreign(ty: &str, encoded: Vec<u8>) -> Json {
    json!({"kind":"foreign","type":ty,"bytes":encoded})
}

fn scalar_le(hex_be: &str) -> Vec<u8> {
    let mut bytes = hex::decode(hex_be).unwrap();
    assert_eq!(bytes.len(), 32);
    bytes.reverse();
    bytes
}

fn alternate_scalar(hex_be: &str, order: &str) -> Vec<u8> {
    let scalar = BigUint::parse_bytes(hex_be.as_bytes(), 16).unwrap();
    let order = BigUint::parse_bytes(order.as_bytes(), 16).unwrap();
    let mut bytes = (order - scalar).to_bytes_le();
    bytes.resize(32, 0);
    bytes
}

fn sec1_point(x: &str, y: &str) -> Vec<u8> {
    let x = hex::decode(x).unwrap();
    let y = hex::decode(y).unwrap();
    let mut encoded = vec![2 | (y[31] & 1)];
    encoded.extend(x);
    encoded
}

fn jubjub_point(point: EmbeddedGroupAffine) -> Json {
    json!({
        "kind":"jubjubPoint",
        "x":field_decimal(point.x().unwrap()),
        "y":field_decimal(point.y().unwrap()),
    })
}

fn jubjub_signature() -> (EmbeddedGroupAffine, EmbeddedGroupAffine, Fr) {
    let generator = EmbeddedGroupAffine::generator();
    let key = generator * EmbeddedFr::from(3u64);
    let announcement = generator * EmbeddedFr::from(5u64);
    let challenge = transient_hash(&[
        announcement.x().unwrap(),
        announcement.y().unwrap(),
        key.x().unwrap(),
        key.y().unwrap(),
        Fr::from(11u64),
        Fr::from(22u64),
    ]);
    let reduced = EmbeddedFr::from_le_bytes_wide(&challenge.as_le_bytes()).unwrap();
    let response = Fr::try_from(EmbeddedFr::from(5u64) + reduced * EmbeddedFr::from(3u64)).unwrap();
    (key, announcement, response)
}

fn jubjub_identity_announcement_signature() -> (EmbeddedGroupAffine, Fr) {
    let announcement = EmbeddedGroupAffine::identity();
    let key = EmbeddedGroupAffine::generator() * EmbeddedFr::from(3u64);
    let challenge = transient_hash(&[
        announcement.x().unwrap(),
        announcement.y().unwrap(),
        key.x().unwrap(),
        key.y().unwrap(),
        Fr::from(11u64),
        Fr::from(22u64),
    ]);
    let response = Fr::try_from(
        EmbeddedFr::from_le_bytes_wide(&challenge.as_le_bytes()).unwrap() * EmbeddedFr::from(3u64),
    )
    .unwrap();
    (announcement, response)
}

fn inputs() -> BTreeMap<String, Json> {
    let (j_key, j_announcement, j_response) = jubjub_signature();
    // RustCrypto k256 0.13.4 test_vectors/ecdsa.rs, in source big-endian form.
    BTreeMap::from([
        (
            "kDigest".into(),
            bytes(
                &hex::decode("4b688df40bcedbe641ddb16ff0a1842d9c67ea1c3bf63f3e0471baa664531d1a")
                    .unwrap(),
            ),
        ),
        (
            "kR".into(),
            foreign(
                "Secp256k1Scalar",
                scalar_le("241097efbf8b63bf145c8961dbdf10c310efbb3b2676bbc0f8b08505c9e2f795"),
            ),
        ),
        (
            "kS".into(),
            foreign(
                "Secp256k1Scalar",
                scalar_le("021006b7838609339e8b415a7f9acb1b661828131aef1ecbc7955dfb01f3ca0e"),
            ),
        ),
        (
            "kKey".into(),
            foreign(
                "Secp256k1Point",
                sec1_point(
                    "779dd197a5df977ed2cf6cb31d82d43328b790dc6b3b7d4437a427bd5847dfcd",
                    "e94b724a555b6d017bb7607c3e3281daf5b1699d6ef4124975c9237b917d426f",
                ),
            ),
        ),
        (
            "pDigest".into(),
            bytes(
                &hex::decode("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56")
                    .unwrap(),
            ),
        ),
        // RustCrypto p256 0.13.2 test_vectors/ecdsa.rs, in source big-endian form.
        (
            "pR".into(),
            foreign(
                "Secp256r1Scalar",
                scalar_le("f3ac8061b514795b8843e3d6629527ed2afd6b1f6a555a7acabb5e6f79c8c2ac"),
            ),
        ),
        (
            "pS".into(),
            foreign(
                "Secp256r1Scalar",
                scalar_le("8bf77819ca05a6b2786c76262bf7371cef97b218e96f175a3ccdda2acc058903"),
            ),
        ),
        (
            "pKey".into(),
            foreign(
                "Secp256r1Point",
                sec1_point(
                    "1ccbe91c075fc7f4f033bfa248db8fccd3565de94bbfb12f3c59ff46c271bf83",
                    "ce4014c68811f9a21a1fdb2c0e6113e06db7ca93b7404e78dc7ccd5ca89a4ca9",
                ),
            ),
        ),
        ("jMessage0".into(), json!(field_decimal(Fr::from(11u64)))),
        ("jMessage1".into(), json!(field_decimal(Fr::from(22u64)))),
        ("jAnnouncement".into(), jubjub_point(j_announcement)),
        ("jResponse".into(), json!(field_decimal(j_response))),
        ("jKey".into(), jubjub_point(j_key)),
        ("edEmpty".into(), bytes(&[])),
        ("edChanged".into(), bytes(&[0])),
        (
            "edR".into(),
            foreign(
                "Curve25519Point",
                hex::decode("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155")
                    .unwrap(),
            ),
        ),
        // RFC 8032 section 7.1, test 1.
        (
            "edS".into(),
            foreign(
                "Curve25519Scalar",
                hex::decode("5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")
                    .unwrap(),
            ),
        ),
        (
            "edKey".into(),
            foreign(
                "Curve25519Point",
                hex::decode("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
                    .unwrap(),
            ),
        ),
        (
            "ethKey".into(),
            foreign(
                "Secp256k1Point",
                hex::decode("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")
                    .unwrap(),
            ),
        ),
    ])
}

fn returns(k: bool, p: bool, schnorr: bool) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("secp256k1Valid".into(), json!(k)),
        ("p256Valid".into(), json!(p)),
        ("schnorrValid".into(), json!(schnorr)),
        ("ed25519Valid".into(), json!(true)),
        ("changedEd25519Valid".into(), json!(false)),
        (
            "ethereumAddress".into(),
            bytes(&hex::decode("7e5f4552091a69125d5dfcb7b8c2659029395bdf").unwrap()),
        ),
    ])
}

fn signature_record(name: &str, fields: [(&str, Json); 2]) -> Json {
    json!({
        "kind": "struct",
        "id": format!("Noctium.Crypto.{name}"),
        "fields": fields.map(|(name, value)| json!({ "name": name, "value": value }))
    })
}

fn readable_ecdsa_session(
    control: &Json,
    inputs: BTreeMap<String, Json>,
    attempt_id: &str,
) -> anyhow::Result<(Session, Json, Json)> {
    let binding_text = control["binding"].as_str().expect("embedded binding");
    let pin = hex::encode(Sha256::digest(binding_text.as_bytes()));
    let binding: Json = serde_json::from_str(binding_text)?;
    let entrypoint = binding["target"]["entrypoint"]
        .as_str()
        .expect("entrypoint binding")
        .to_owned();
    let witnesses = control["witnesses"].as_array().expect("witness metadata");
    anyhow::ensure!(witnesses.len() == 1, "expected one provider");
    let witness = &witnesses[0];
    anyhow::ensure!(witness["parameters"] == json!([]), "signature provider must take no args");
    let operation = witness["operation"].as_str().expect("provider operation").to_owned();
    let capability = witness["capability"].as_str().expect("provider capability").to_owned();
    let input = witness["name"].as_str().expect("provider name").to_owned();
    let result_type = witness["resultType"]
        .as_str()
        .expect("provider result type")
        .to_owned();
    let mut session = Session::from_json_with_invocation_target(
        control.clone(),
        inputs,
        Context {
            protocol_version: 1,
            namespace: "noctium".into(),
            base_revision: "r0".into(),
            attempt_id: attempt_id.into(),
            operations: vec![Operation {
                operation: operation.clone(),
                argument_schema: BTreeMap::new(),
                result_schema: result_type,
            }],
            providers: vec![Provider {
                input,
                operation: operation.clone(),
                capability: capability.clone(),
                arguments: BTreeMap::new(),
            }],
            commit_capability: "commit".into(),
            limits: Limits::default(),
            capabilities: vec![Capability {
                id: capability,
                namespace: "noctium".into(),
                key_prefix: "lookup/".into(),
                operations: vec![operation],
            }, Capability {
                id: "commit".into(),
                namespace: "noctium".into(),
                key_prefix: "noctium/".into(),
                operations: vec![host::CAS.into()],
            }],
        },
        Some(&pin),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint,
        }),
    )?;
    let pending = session.advance()?;
    anyhow::ensure!(pending["status"] == "need_host", "expected a signature provider request");
    Ok((session, pending, binding))
}

fn signature_provider_response(
    request: &Json,
    attempt_id: &str,
    value: Json,
) -> TypedResponse {
    serde_json::from_value(json!({
        "protocolVersion": 2,
        "requestId": request["requestId"],
        "attemptId": attempt_id,
        "outcome": "value",
        "operation": request["operation"],
        "capability": request["capability"],
        "schema": request["schema"],
        "value": value,
    }))
    .unwrap()
}

#[test]
#[ignore = "requires fresh ReadableECDSA artifacts in NOCTIUM_READABLE_ECDSA_DIR"]
fn readable_ecdsa_callbacks_match_vectors_and_reject_zero_s() -> anyhow::Result<()> {
    let directory = PathBuf::from(std::env::var_os("NOCTIUM_READABLE_ECDSA_DIR").unwrap());
    let supplied = inputs();
    let cases = [
        (
            "ReadableECDSA.k1",
            "keySignatureK1",
            "Secp256k1EcdsaSignature",
            "Secp256k1Scalar",
            "kDigest",
            "kKey",
            "kR",
            "kS",
        ),
        (
            "ReadableECDSA.r1",
            "keySignatureR1",
            "Secp256r1EcdsaSignature",
            "Secp256r1Scalar",
            "pDigest",
            "pKey",
            "pR",
            "pS",
        ),
    ];

    for (stem, provider, signature_type, scalar_type, digest_name, key_name, r_name, s_name) in
        cases
    {
        let control: Json = serde_json::from_reader(fs::File::open(
            directory.join(format!("{stem}.witness.control.json")),
        )?)?;
        let plan: Plan = serde_json::from_reader(fs::File::open(
            directory.join(format!("{stem}.impact.json")),
        )?)?;
        let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
        let initial = create_state(&plan, &BTreeMap::new())?;
        let base_digest = supplied[digest_name].clone();
        let key = supplied[key_name].clone();
        let valid_signature = signature_record(
            signature_type,
            [(
                "r",
                supplied[r_name].clone(),
            ), (
                "s",
                supplied[s_name].clone(),
            )],
        );
        let run = |digest: Json,
                   signature: Json,
                   suffix: char|
         -> anyhow::Result<(Session, Json, Json)> {
            let attempt_id = suffix.to_string().repeat(64);
            let call_inputs = BTreeMap::from([
                ("digest".into(), digest),
                ("key".into(), key.clone()),
            ]);
            let (mut session, pending, binding) =
                readable_ecdsa_session(&control, call_inputs, &attempt_id)?;
            let request = &pending["request"];
            anyhow::ensure!(request["name"] == provider, "unexpected ECDSA provider request");
            anyhow::ensure!(request["arguments"] == json!([]), "signature provider takes no args");
            anyhow::ensure!(session.advance()? == pending, "provider request lost correlation");
            session.resume_typed(signature_provider_response(
                request,
                &attempt_id,
                signature,
            ))?;
            let terminal = session.advance()?;
            Ok((session, terminal, binding))
        };
        let check_result = |session: &mut Session, binding: &Json, expected: bool| -> anyhow::Result<()> {
            let completion = session.private_completion(&binding["nativeRelation"])?;
            let native_inputs: BTreeMap<String, Json> =
                serde_json::from_value(completion["inputs"].clone())?;
            let execution = prepare(
                &plan,
                &native_inputs,
                &initial,
                &ledger::structure::INITIAL_PARAMETERS,
                coin_structure::contract::ContractAddress::default(),
            )?;
            assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
            let returns = execution.returns_json();
            assert_eq!(returns["signatureValid"], json!(expected));
            assert_eq!(returns.len(), 1);
            Ok(())
        };

        let (mut session, status, binding) = run(base_digest.clone(), valid_signature.clone(), 'b')?;
        assert_eq!(status["status"], "completed", "{stem} valid vector");
        check_result(&mut session, &binding, true)?;

        let mut changed_digest = base_digest;
        changed_digest["values"][0] = json!(5);
        let (mut session, status, binding) = run(changed_digest, valid_signature.clone(), 'c')?;
        assert_eq!(status["status"], "completed", "{stem} changed digest");
        check_result(&mut session, &binding, false)?;

        let zero_s = signature_record(
            signature_type,
            [
                ("r", supplied[r_name].clone()),
                ("s", foreign(scalar_type, vec![0; 32])),
            ],
        );
        let (mut session, status, binding) = run(supplied[digest_name].clone(), zero_s, 'd')?;
        assert_eq!(status["status"], "failed", "{stem} zero s accepted");
        assert!(session.private_completion(&binding["nativeRelation"]).is_err());
    }
    Ok(())
}

#[test]
#[ignore = "requires fresh ReadableSignatures artifacts in NOCTIUM_READABLE_SIGNATURES_DIR"]
fn readable_schnorr_and_ed25519_callbacks_match_vectors() -> anyhow::Result<()> {
    let directory = PathBuf::from(std::env::var_os("NOCTIUM_READABLE_SIGNATURES_DIR").unwrap());
    let supplied = inputs();

    let schnorr_stem = "ReadableSignatures.schnorr";
    let schnorr_control: Json = serde_json::from_reader(fs::File::open(
        directory.join(format!("{schnorr_stem}.witness.control.json")),
    )?)?;
    let schnorr_plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join(format!("{schnorr_stem}.impact.json")),
    )?)?;
    let schnorr_circuit = IrSource::load(fs::File::open(
        directory.join(format!("{schnorr_stem}.zkir")),
    )?)?;
    let schnorr_initial = create_state(&schnorr_plan, &BTreeMap::new())?;
    let schnorr_inputs = BTreeMap::from([
        ("message0".into(), supplied["jMessage0"].clone()),
        (
            "changedMessage0".into(),
            json!(field_decimal(Fr::from(12u64))),
        ),
        ("message1".into(), supplied["jMessage1"].clone()),
        ("key".into(), supplied["jKey"].clone()),
    ]);
    let schnorr_signature = signature_record(
        "JubjubSchnorrSignature",
        [
            ("announcement", supplied["jAnnouncement"].clone()),
            (
                "response",
                json!({"kind":"native", "value":supplied["jResponse"]}),
            ),
        ],
    );
    let schnorr_attempt = "e".repeat(64);
    let (mut schnorr_session, schnorr_pending, schnorr_binding) =
        readable_ecdsa_session(&schnorr_control, schnorr_inputs, &schnorr_attempt)?;
    let schnorr_request = &schnorr_pending["request"];
    assert_eq!(schnorr_request["name"], "schnorrSignature");
    assert_eq!(schnorr_request["arguments"], json!([]));
    assert_eq!(schnorr_session.advance()?, schnorr_pending);
    schnorr_session.resume_typed(signature_provider_response(
        schnorr_request,
        &schnorr_attempt,
        schnorr_signature,
    ))?;
    let schnorr_terminal = schnorr_session.advance()?;
    assert_eq!(schnorr_terminal["status"], "completed");
    assert!(schnorr_terminal.get("request").is_none());
    let schnorr_completion =
        schnorr_session.private_completion(&schnorr_binding["nativeRelation"])?;
    let schnorr_native_inputs: BTreeMap<String, Json> =
        serde_json::from_value(schnorr_completion["inputs"].clone())?;
    let schnorr_execution = prepare(
        &schnorr_plan,
        &schnorr_native_inputs,
        &schnorr_initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    assert_eq!(
        check(&schnorr_execution, &schnorr_circuit)?,
        schnorr_execution.activity_schedule
    );
    assert_eq!(schnorr_execution.returns_json()["signatureValid"], json!(true));
    assert_eq!(
        schnorr_execution.returns_json()["changedSignatureValid"],
        json!(false)
    );

    let ed_stem = "ReadableSignatures.ed25519";
    let ed_control: Json = serde_json::from_reader(fs::File::open(
        directory.join(format!("{ed_stem}.witness.control.json")),
    )?)?;
    let ed_plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join(format!("{ed_stem}.impact.json")),
    )?)?;
    let ed_circuit = IrSource::load(fs::File::open(directory.join(format!("{ed_stem}.zkir")))?)?;
    let ed_initial = create_state(&ed_plan, &BTreeMap::new())?;
    let ed_inputs = BTreeMap::from([
        ("message".into(), supplied["edEmpty"].clone()),
        ("changedMessage".into(), supplied["edChanged"].clone()),
        ("key".into(), supplied["edKey"].clone()),
    ]);
    let ed_signature = signature_record(
        "Ed25519Signature",
        [
            ("r", supplied["edR"].clone()),
            ("s", supplied["edS"].clone()),
        ],
    );
    let ed_attempt = "f".repeat(64);
    let (mut ed_session, ed_pending, ed_binding) =
        readable_ecdsa_session(&ed_control, ed_inputs, &ed_attempt)?;
    let ed_request = &ed_pending["request"];
    assert_eq!(ed_request["name"], "ed25519Signature");
    assert_eq!(ed_request["arguments"], json!([]));
    assert_eq!(ed_session.advance()?, ed_pending);
    ed_session.resume_typed(signature_provider_response(
        ed_request,
        &ed_attempt,
        ed_signature,
    ))?;
    let ed_terminal = ed_session.advance()?;
    assert_eq!(ed_terminal["status"], "completed");
    assert!(ed_terminal.get("request").is_none());
    let ed_completion = ed_session.private_completion(&ed_binding["nativeRelation"])?;
    let ed_native_inputs: BTreeMap<String, Json> =
        serde_json::from_value(ed_completion["inputs"].clone())?;
    let ed_execution = prepare(
        &ed_plan,
        &ed_native_inputs,
        &ed_initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    assert_eq!(
        check(&ed_execution, &ed_circuit)?,
        ed_execution.activity_schedule
    );
    assert_eq!(ed_execution.returns_json()["signatureValid"], json!(true));
    assert_eq!(
        ed_execution.returns_json()["changedSignatureValid"],
        json!(false)
    );

    Ok(())
}

#[test]
#[ignore = "requires fresh SignaturePayloads artifacts in NOCTIUM_SIGNATURE_PAYLOADS_DIR"]
fn portable_signature_records_roundtrip_and_reject_wrong_identity() -> anyhow::Result<()> {
    let dir = PathBuf::from(std::env::var_os("NOCTIUM_SIGNATURE_PAYLOADS_DIR").unwrap());
    let stem = "SignaturePayloads.echo";
    let control: Json = serde_json::from_reader(fs::File::open(
        dir.join(format!("{stem}.witness.control.json")),
    )?)?;
    let binding_text = control["binding"].as_str().expect("embedded binding");
    let pin = hex::encode(Sha256::digest(binding_text.as_bytes()));
    let binding: Json = serde_json::from_str(binding_text)?;
    let values = inputs();
    let signatures = BTreeMap::from([
        (
            "schnorr".into(),
            signature_record(
                "JubjubSchnorrSignature",
                [
                    ("announcement", values["jAnnouncement"].clone()),
                    (
                        "response",
                        json!({"kind": "native", "value": values["jResponse"]}),
                    ),
                ],
            ),
        ),
        (
            "k1".into(),
            signature_record(
                "Secp256k1EcdsaSignature",
                [("r", values["kR"].clone()), ("s", values["kS"].clone())],
            ),
        ),
        (
            "r1".into(),
            signature_record(
                "Secp256r1EcdsaSignature",
                [("r", values["pR"].clone()), ("s", values["pS"].clone())],
            ),
        ),
        (
            "ed".into(),
            signature_record(
                "Ed25519Signature",
                [("r", values["edR"].clone()), ("s", values["edS"].clone())],
            ),
        ),
    ]);
    let start = |inputs| {
        Session::from_json_with_invocation_target(
            control.clone(),
            inputs,
            Context {
                protocol_version: 1,
                namespace: "noctium".into(),
                base_revision: "r0".into(),
                attempt_id: "b".repeat(64),
                operations: vec![],
                providers: vec![],
                commit_capability: "commit".into(),
                limits: Limits::default(),
                capabilities: vec![Capability {
                    id: "commit".into(),
                    namespace: "noctium".into(),
                    key_prefix: "noctium/".into(),
                    operations: vec![host::CAS.into()],
                }],
            },
            Some(&pin),
            Some(InvocationTarget {
                contract_address: "a".repeat(64),
                entrypoint: "echo".into(),
            }),
        )
    };
    let mut wrong_identity = signatures.clone();
    wrong_identity.get_mut("k1").unwrap()["id"] = signatures["r1"]["id"].clone();
    assert!(start(wrong_identity).is_err());
    let mut wrong_curve = signatures.clone();
    wrong_curve.get_mut("k1").unwrap()["fields"][0]["value"] = values["pR"].clone();
    assert!(start(wrong_curve).is_err());

    let mut session = start(signatures.clone())?;
    assert_eq!(session.advance()?["status"], "completed");
    let completion = session.private_completion(&binding["nativeRelation"])?;
    let plan: Plan =
        serde_json::from_reader(fs::File::open(dir.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(dir.join(format!("{stem}.zkir")))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let mut execution = prepare(
        &plan,
        &serde_json::from_value(completion["inputs"].clone())?,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    let expected = signatures
        .into_iter()
        .map(|(name, value)| (format!("{name}Result"), value))
        .collect();
    assert_eq!(execution.returns_json(), expected);
    let (commitment, randomness) = execution.preimage.communications_commitment.unwrap();
    execution.preimage.communications_commitment = Some((commitment + Fr::from(1u64), randomness));
    assert!(check(&execution, &circuit).is_err());
    Ok(())
}

#[test]
fn signature_helpers_match_known_vectors_and_reject_invalid_preconditions() {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let circuit = IrSource::load(CIRCUIT).unwrap();
    let initial = create_state(&plan, &BTreeMap::new()).unwrap();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let supplied = inputs();
    let mut execution = prepare(&plan, &supplied, &initial, params, address).unwrap();
    assert_eq!(
        check(&execution, &circuit).unwrap(),
        execution.activity_schedule
    );
    assert_eq!(execution.returns_json(), returns(true, true, true));
    assert_eq!(execution.preimage.private_transcript.len(), 105);
    let original = execution.preimage.private_transcript[0];
    execution.preimage.private_transcript[0] = original + Fr::from(1u64);
    assert!(check(&execution, &circuit).is_err());

    let mut high_low_s = supplied.clone();
    high_low_s.insert(
        "kS".into(),
        foreign(
            "Secp256k1Scalar",
            alternate_scalar(
                "021006b7838609339e8b415a7f9acb1b661828131aef1ecbc7955dfb01f3ca0e",
                "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141",
            ),
        ),
    );
    high_low_s.insert(
        "pS".into(),
        foreign(
            "Secp256r1Scalar",
            alternate_scalar(
                "8bf77819ca05a6b2786c76262bf7371cef97b218e96f175a3ccdda2acc058903",
                "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
            ),
        ),
    );
    let high_low_s = prepare(&plan, &high_low_s, &initial, params, address).unwrap();
    check(&high_low_s, &circuit).unwrap();
    assert_eq!(high_low_s.returns_json(), returns(true, true, true));

    let (announcement, response) = jubjub_identity_announcement_signature();
    let mut identity_announcement = supplied.clone();
    identity_announcement.insert("jAnnouncement".into(), jubjub_point(announcement));
    identity_announcement.insert("jResponse".into(), json!(field_decimal(response)));
    let identity_announcement =
        prepare(&plan, &identity_announcement, &initial, params, address).unwrap();
    check(&identity_announcement, &circuit).unwrap();
    assert_eq!(
        identity_announcement.returns_json(),
        returns(true, true, true)
    );

    let mut changed = supplied.clone();
    changed.get_mut("kDigest").unwrap()["values"][0] = json!(5);
    changed.get_mut("pDigest").unwrap()["values"][0] = json!(5);
    changed.insert("jMessage0".into(), json!(field_decimal(Fr::from(12u64))));
    let changed = prepare(&plan, &changed, &initial, params, address).unwrap();
    check(&changed, &circuit).unwrap();
    assert_eq!(changed.returns_json(), returns(false, false, false));

    let rejects = |name: &str, invalid: &BTreeMap<String, Json>| {
        assert!(
            prepare(&plan, invalid, &initial, params, address).is_err(),
            "{name} should abort during prepare"
        );
    };
    let mut zero_r = supplied.clone();
    zero_r.insert("kR".into(), foreign("Secp256k1Scalar", vec![0; 32]));
    rejects("zero secp256k1 r", &zero_r);
    let mut zero_s = supplied.clone();
    zero_s.insert("pS".into(), foreign("Secp256r1Scalar", vec![0; 32]));
    rejects("zero P-256 s", &zero_s);
    let mut identity_k = supplied.clone();
    identity_k.insert("kKey".into(), foreign("Secp256k1Point", vec![0; 33]));
    rejects("identity secp256k1 key", &identity_k);
    let mut identity_key = supplied.clone();
    identity_key.insert("jKey".into(), jubjub_point(EmbeddedGroupAffine::identity()));
    rejects("identity Jubjub key", &identity_key);
    let mut identity_ed = supplied.clone();
    identity_ed.insert(
        "edKey".into(),
        foreign("Curve25519Point", [vec![1], vec![0; 31]].concat()),
    );
    rejects("identity Ed25519 key", &identity_ed);
    let mut identity_eth = supplied.clone();
    identity_eth.insert("ethKey".into(), foreign("Secp256k1Point", vec![0; 33]));
    rejects("identity Ethereum key", &identity_eth);

    let mut computed_identity = supplied;
    let mut digest_one = vec![0; 32];
    digest_one[31] = 1;
    let mut scalar_one = vec![0; 32];
    scalar_one[0] = 1;
    computed_identity.insert("kDigest".into(), bytes(&digest_one));
    computed_identity.insert("kR".into(), foreign("Secp256k1Scalar", scalar_one.clone()));
    computed_identity.insert("kS".into(), foreign("Secp256k1Scalar", scalar_one));
    computed_identity.insert(
        "kKey".into(),
        foreign(
            "Secp256k1Point",
            hex::decode("0379be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")
                .unwrap(),
        ),
    );
    rejects("computed identity ECDSA point", &computed_identity);
}
