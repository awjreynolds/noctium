use noctium_runtime::{
    control::{InvocationTarget, Session, TypedResponse},
    host::{self, Capability, Context, Limits, Operation, Provider},
    witness::{Parameter, WitnessSignature},
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

#[cfg(feature = "zkir-321")]
#[test]
#[ignore = "requires fresh Sha512Fab Lean artifacts"]
fn typed_fab_digests_use_the_provider_record_in_host_and_native_execution() -> anyhow::Result<()> {
    use coin_structure::contract::ContractAddress;
    use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
    use std::{fs, path::PathBuf};

    let root = PathBuf::from(std::env::var_os("NOCTIUM_SHA512_FAB_DIR").unwrap());
    let stem = "Sha512Fab.hashHosted";
    let control = fs::read_to_string(root.join(format!("{stem}.witness.control.json")))?;
    let sha = json!({"kind":"bytes", "values": hex::decode(
        "6f2b8bc408127949730a24dd6a4b5562a8ec69a7d895a79329c13976447a1c948c4a84e6d070af7e02ea37d89408d1a0679dee79fd6c3cb40e548e4438b7bfae"
    )?});
    let keccak = json!({"kind":"bytes", "values": hex::decode(
        "0a3cf3d2108f7463f9ef5896ebfd31c7fcdde34ac2171cc6b3c48f28d03e8683"
    )?});
    let payload = json!({"kind":"struct", "id":"Sha512Fab.Payload", "fields":[
        {"name":"octets", "value":{"kind":"bytes", "values": (1u8..=32).collect::<Vec<_>>()}},
        {"name":"flag", "value":{"kind":"bool", "value":true}},
        {"name":"counter", "value":{"kind":"uint", "maximum":"65535", "value":"257"}},
        {"name":"anchor", "value":{"kind":"native", "value":"42"}}
    ]});
    let attempt = "a".repeat(64);
    let (mut session, _) = bound_session(
        &control,
        BTreeMap::from([
            ("expectedSha".into(), sha.clone()),
            ("expectedKeccak".into(), keccak.clone()),
        ]),
        &attempt,
    );
    let pending = session.advance()?;
    assert_eq!(pending["status"], "need_host");
    let request = &pending["request"];
    let mut wrong_schema = payload.clone();
    wrong_schema["id"] = json!("Sha512Fab.Other");
    assert!(session
        .resume_typed(reply(request, &attempt, "value", Some(wrong_schema)))
        .is_err());
    assert_eq!(session.advance()?, pending);
    session.resume_typed(reply(request, &attempt, "value", Some(payload)))?;
    assert_eq!(session.advance()?["status"], "completed");
    let relation_bytes = fs::read(root.join(format!("{stem}.zkir")))?;
    let relation = serde_json::from_slice(&relation_bytes)?;
    let completion = session.private_completion(&relation)?;
    let inputs = serde_json::from_value(completion["inputs"].clone())?;
    let circuit = IrSource::load(relation_bytes.as_slice())?;
    let plan: Plan =
        serde_json::from_slice(&fs::read(root.join(format!("{stem}.impact.json")))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    let result = execution.returns_json();
    assert_eq!(result["shaDigest"], sha);
    assert_eq!(result["keccakDigest"], keccak);
    Ok(())
}

#[cfg(feature = "zkir-321")]
#[test]
#[ignore = "requires fresh TypedCallArguments Lean artifacts"]
fn hosted_arguments_move_to_the_native_header_without_changing_provider_inputs() {
    use coin_structure::contract::ContractAddress;
    use ledger::structure::INITIAL_PARAMETERS;
    use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
    use std::{fs, path::PathBuf};
    use transient_crypto::curve::Fr;

    let root = PathBuf::from(std::env::var_os("NOCTIUM_HOSTED_CALL_ARTIFACTS").unwrap());
    let stem = "HostedCallArguments.review";
    let control = fs::read_to_string(root.join(format!("{stem}.witness.control.json"))).unwrap();
    let plan: Plan =
        serde_json::from_slice(&fs::read(root.join(format!("{stem}.impact.json"))).unwrap())
            .unwrap();
    let relation_bytes = fs::read(root.join(format!("{stem}.zkir"))).unwrap();
    let circuit = IrSource::load(relation_bytes.as_slice()).unwrap();
    let relation = serde_json::from_slice(&relation_bytes).unwrap();
    let payload: Vec<u8> = (0..33).collect();
    let byte_input = json!({"kind":"bytes","values":payload});
    let inputs = BTreeMap::from([
        ("amount".into(), json!("32")),
        ("payload".into(), byte_input.clone()),
        ("zeroBound".into(), json!("0")),
        ("emptyPayload".into(), json!({"kind":"bytes","values":[]})),
        ("salt".into(), json!("7")),
    ]);
    let attempt = "e".repeat(64);
    let (mut session, plan_json) = bound_session(&control, inputs.clone(), &attempt);
    let pending = session.advance().unwrap();
    assert_eq!(pending["status"], "need_host");
    let private = session.private_request().unwrap();
    assert_eq!(private["arguments"]["payload"], byte_input);
    assert_eq!(private["arguments"]["amount"], "32");
    session
        .resume_typed(reply(&pending["request"], &attempt, "value", Some(json!(true))))
        .unwrap();
    let done = session.advance().unwrap();
    assert_eq!(done["status"], "completed");
    let completion = session.private_completion(&relation).unwrap();
    let native_inputs = serde_json::from_value(completion["inputs"].clone()).unwrap();
    let state = create_state(&plan, &BTreeMap::new()).unwrap();
    let mut execution = prepare(
        &plan,
        &native_inputs,
        &state,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    )
    .unwrap();
    check(&execution, &circuit).unwrap();
    let mut low = [0; 32];
    low[..31].copy_from_slice(&payload[..31]);
    assert_eq!(
        execution.preimage.inputs,
        [
            Fr::from(31 + 32 * 256u64),
            Fr::from_le_bytes(&low).unwrap(),
            Fr::from(32u64),
            Fr::from(0u64),
        ],
    );
    assert_eq!(
        execution.preimage.private_transcript,
        [Fr::from(7u64), Fr::from(1u64)]
    );
    assert_eq!(execution.returns_json()["approval"], true);
    execution.preimage.inputs[2] = Fr::from(31u64);
    assert!(check(&execution, &circuit).is_err());

    let mut reordered = binding(&plan_json);
    reordered["callInputs"].as_array_mut().unwrap().swap(0, 1);
    let mut altered = plan_json;
    let binding_text = reordered.to_string();
    let digest = hex::encode(Sha256::digest(binding_text.as_bytes()));
    altered["binding"] = json!(binding_text);
    let context = source_context(&signatures(&altered), &attempt);
    let result = Session::from_json_with_invocation_target(
        altered,
        inputs,
        context,
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: "review".into(),
        }),
    );
    let Err(error) = result else {
        panic!("reordered call header accepted")
    };
    assert!(error.to_string().contains("native circuit inputs"), "{error:#}");
}

#[cfg(feature = "zkir-321")]
#[test]
fn byte_witness_state_and_hash_helpers_bind_account_ciphertext_and_memo() {
    use noctium_runtime::{
        Plan, canonical_field, check, create_state, field_decimal, field_value, prepare,
        zkir::IrSource,
    };
    use num_bigint::BigUint;
    use onchain_runtime::state::StateValue;
    use transient_crypto::curve::{EmbeddedFr, EmbeddedGroupAffine, Fr};

    let source =
        include_str!("fixtures/hash-witness/321/HashWitness.register.witness.control.json");
    let plan: Json = serde_json::from_str(source).unwrap();
    let native_plan: Plan = serde_json::from_str(include_str!(
        "fixtures/hash-witness/321/HashWitness.register.impact.json"
    ))
    .unwrap();
    let circuit: &[u8] = include_bytes!("fixtures/hash-witness/321/HashWitness.register.zkir");
    let circuit = IrSource::load(circuit).unwrap();
    let account_secret = [0x11u8; 32];
    let encryption_secret = [0x22u8; 32];
    let seed = [0x33u8; 32];
    let bytes = |value: &[u8]| json!({"kind":"bytes", "values":value});
    let tag = |text: &str| {
        let mut value = [0u8; 32];
        value[..text.len()].copy_from_slice(text.as_bytes());
        value
    };
    let pair_hash = |left: &[u8], right: &[u8]| -> Vec<u8> {
        let mut hash = Sha256::new();
        hash.update(left);
        hash.update(right);
        hash.finalize().to_vec()
    };
    let field = |digest: &[u8]| {
        canonical_field(&BigUint::from_bytes_le(&digest[..31]).to_string()).unwrap()
    };
    let scalar = |digest: &[u8]| EmbeddedFr::try_from(field(digest)).unwrap();
    let account: [u8; 32] = Sha256::digest(account_secret).into();
    let secret = scalar(&pair_hash(
        &tag("ElGamal:secretToScalar"),
        &encryption_secret,
    ));
    let balance_r = scalar(&pair_hash(&seed, &tag("Noctium:balance")));
    let memo_r = scalar(&pair_hash(&seed, &tag("Noctium:memo")));
    let generator = EmbeddedGroupAffine::generator();
    let recipient = generator * secret;
    let c1 = generator * balance_r;
    let c2 = generator * EmbeddedFr::from(3u64) + recipient * balance_r;
    let ephemeral = generator * memo_r;
    let shared = recipient * memo_r;
    let point_digest = Sha256::digest(
        [
            shared.x().unwrap().as_le_bytes(),
            shared.y().unwrap().as_le_bytes(),
        ]
        .concat(),
    );
    let memo = Fr::from(3u64) + field(&pair_hash(&point_digest, &tag("Noctium:memo:amount")));
    let expected = [
        c1.x().unwrap(),
        c1.y().unwrap(),
        c2.x().unwrap(),
        c2.y().unwrap(),
        ephemeral.x().unwrap(),
        ephemeral.y().unwrap(),
        memo,
    ];
    for altered_account in [false, true] {
        let mut supplied_account = account;
        if altered_account {
            supplied_account[31] ^= 1;
        }
        let inputs = BTreeMap::from([
            ("account".into(), bytes(&supplied_account)),
            (
                "recipient".into(),
                json!({"kind":"jubjubPoint", "x":field_decimal(recipient.x().unwrap()), "y":field_decimal(recipient.y().unwrap())}),
            ),
        ]);
        let attempt = if altered_account { "d" } else { "e" }.repeat(64);
        let mut context = source_context(&signatures(&plan), &attempt);
        context
            .capabilities
            .iter_mut()
            .find(|capability| capability.id == "commit")
            .unwrap()
            .key_prefix = "noctium/Wallet/".into();
        let digest = hex::encode(Sha256::digest(plan["binding"].as_str().unwrap().as_bytes()));
        let mut session = Session::from_json_with_invocation_target(
            plan.clone(),
            inputs,
            context,
            Some(&digest),
            Some(InvocationTarget {
                contract_address: "a".repeat(64),
                entrypoint: "register".into(),
            }),
        )
        .unwrap();
        loop {
            let status = session.advance().unwrap();
            if status["status"] != "need_host" {
                assert_eq!(
                    status["status"],
                    if altered_account {
                        "failed"
                    } else {
                        "completed"
                    },
                    "{status}"
                );
                break;
            }
            let request = &status["request"];
            let value = if request["operation"] == host::READ {
                let private = session.private_request().unwrap();
                match private["arguments"]["key"].as_str().unwrap() {
                    "noctium/Wallet/accountSecret" => bytes(&account_secret),
                    "noctium/Wallet/encryptionSecret" => bytes(&encryption_secret),
                    other => panic!("unexpected private read {other}"),
                }
            } else {
                match request["name"].as_str().unwrap() {
                    "randomnessSeed" => bytes(&seed),
                    "plaintext" => json!("3"),
                    other => panic!("unexpected provider {other}"),
                }
            };
            session
                .resume_typed(reply(request, &attempt, "value", Some(value)))
                .unwrap();
        }
        let relation = binding(&plan)["nativeRelation"].clone();
        if altered_account {
            assert!(session.private_completion(&relation).is_err());
            continue;
        }
        let completion = session.private_completion(&relation).unwrap();
        assert_eq!(
            completion["hostWrites"]["noctium/Wallet/lastSeed"]["value"],
            bytes(&seed)
        );
        let names = ["c1x", "c1y", "c2x", "c2y", "memoX", "memoY", "memoAmount"];
        let initial = create_state(
            &native_plan,
            &names
                .iter()
                .map(|name| ((*name).into(), json!("0")))
                .collect(),
        )
        .unwrap();
        let native_inputs = serde_json::from_value(completion["inputs"].clone()).unwrap();
        let execution = prepare(
            &native_plan,
            &native_inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .unwrap();
        check(&execution, &circuit).unwrap();
        let StateValue::Array(state) = execution.after.state.get_ref() else {
            panic!("expected state array")
        };
        for (index, expected) in expected.into_iter().enumerate() {
            let StateValue::Cell(cell) = state.get(index).unwrap() else {
                panic!("expected ciphertext cell")
            };
            assert_eq!(**cell, field_value(expected));
        }
    }
}

#[cfg(feature = "zkir-321")]
#[test]
fn witness_backed_curve_helpers_bind_elgamal_outputs_and_reject_a_wrong_key() {
    use noctium_runtime::{
        Plan, check, create_state, field_decimal, field_value, prepare, zkir::IrSource,
    };
    use onchain_runtime::state::StateValue;
    use transient_crypto::curve::{EmbeddedFr, EmbeddedGroupAffine};

    let source =
        include_str!("fixtures/curve-helpers/321/CurveHelpers.encrypt.witness.control.json");
    let native_plan: Plan = serde_json::from_str(include_str!(
        "fixtures/curve-helpers/321/CurveHelpers.encrypt.impact.json"
    ))
    .unwrap();
    let circuit: &[u8] = include_bytes!("fixtures/curve-helpers/321/CurveHelpers.encrypt.zkir");
    let circuit = IrSource::load(circuit).unwrap();
    let generator = EmbeddedGroupAffine::generator();
    let recipient = generator * EmbeddedFr::from(7u64);
    for key in [7u64, 8] {
        let inputs = BTreeMap::from([(
            "recipient".into(),
            json!({"kind":"jubjubPoint", "x":field_decimal(recipient.x().unwrap()), "y":field_decimal(recipient.y().unwrap())}),
        )]);
        let attempt = format!("{key:064x}");
        let (mut session, plan) = bound_session(source, inputs, &attempt);
        loop {
            let status = session.advance().unwrap();
            if status["status"] != "need_host" {
                assert_eq!(
                    status["status"],
                    if key == 7 { "completed" } else { "failed" },
                    "{status}"
                );
                break;
            }
            let request = &status["request"];
            let value = match request["name"].as_str().unwrap() {
                "secret" => key,
                "randomness" => 11,
                "plaintext" => 3,
                other => panic!("unexpected provider {other}"),
            };
            session
                .resume_typed(reply(
                    request,
                    &attempt,
                    "value",
                    Some(json!(value.to_string())),
                ))
                .unwrap();
        }
        let relation = binding(&plan)["nativeRelation"].clone();
        if key != 7 {
            assert!(session.private_completion(&relation).is_err());
            continue;
        }
        let completion = session.private_completion(&relation).unwrap();
        let native_inputs = serde_json::from_value(completion["inputs"].clone()).unwrap();
        let initial = create_state(
            &native_plan,
            &BTreeMap::from([
                ("c1x".into(), json!("0")),
                ("c1y".into(), json!("0")),
                ("c2x".into(), json!("0")),
                ("c2y".into(), json!("0")),
            ]),
        )
        .unwrap();
        let execution = prepare(
            &native_plan,
            &native_inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .unwrap();
        check(&execution, &circuit).unwrap();
        let StateValue::Array(state) = execution.after.state.get_ref() else {
            panic!("expected state array")
        };
        let c1 = generator * EmbeddedFr::from(11u64);
        let c2 = generator * EmbeddedFr::from(80u64);
        for (index, expected) in [
            c1.x().unwrap(),
            c1.y().unwrap(),
            c2.x().unwrap(),
            c2.y().unwrap(),
        ]
        .into_iter()
        .enumerate()
        {
            let StateValue::Cell(cell) = state.get(index).unwrap() else {
                panic!("expected ciphertext cell")
            };
            assert_eq!(**cell, field_value(expected));
        }
    }
}

#[cfg(feature = "zkir-321")]
#[test]
fn typed_curve_witnesses_keep_private_values_and_feed_the_native_relation() {
    use noctium_runtime::{Plan, check, create_state, field_decimal, prepare, zkir::IrSource};
    use transient_crypto::curve::{EmbeddedFr, EmbeddedGroupAffine};

    let source = include_str!("fixtures/curve-witness/321/CurveWitness.claim.witness.control.json");
    let plan: Json = serde_json::from_str(source).unwrap();
    let scalar = json!({"kind":"jubjubScalar","value":"7"});
    let p = EmbeddedGroupAffine::generator() * EmbeddedFr::from(7u64);
    let point = json!({"kind":"jubjubPoint", "x":field_decimal(p.x().unwrap()), "y":field_decimal(p.y().unwrap())});
    let inputs = plan["inputs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|input| {
            let value = match input["type"].as_str().unwrap() {
                "JubjubScalar" => scalar.clone(),
                "JubjubPoint" => point.clone(),
                other => panic!("unexpected source type {other}"),
            };
            (input["name"].as_str().unwrap().to_owned(), value)
        })
        .collect();
    let attempt = "c".repeat(64);
    let (mut session, _) = bound_session(source, inputs, &attempt);
    let mut seen = BTreeSet::new();
    loop {
        let status = session.advance().unwrap();
        if status["status"] == "completed" {
            assert_eq!(status["result"], true);
            break;
        }
        assert_eq!(status["status"], "need_host");
        let request = &status["request"];
        let schema = request["schema"].as_str().unwrap();
        seen.insert(schema.to_owned());
        let value = match schema {
            "JubjubScalar" => scalar.clone(),
            "JubjubPoint" => {
                let invalid = json!({"kind":"jubjubPoint","x":"0","y":"0"});
                assert!(
                    session
                        .resume_typed(reply(request, &attempt, "value", Some(invalid)))
                        .is_err()
                );
                point.clone()
            }
            other => panic!("unexpected provider result {other}"),
        };
        let private = session.private_request().unwrap();
        assert_eq!(
            private["arguments"]
                .as_object()
                .unwrap()
                .values()
                .next()
                .unwrap(),
            &value
        );
        session
            .resume_typed(reply(request, &attempt, "value", Some(value)))
            .unwrap();
    }
    assert_eq!(
        seen,
        BTreeSet::from(["JubjubScalar".into(), "JubjubPoint".into()])
    );
    let relation = binding(&plan)["nativeRelation"].clone();
    let completion = session.private_completion(&relation).unwrap();
    let native_inputs = completion["inputs"]
        .as_object()
        .unwrap()
        .iter()
        .map(|(name, value)| (name.clone(), value.clone()))
        .collect();
    let native_plan: Plan = serde_json::from_str(include_str!(
        "fixtures/curve-witness/321/CurveWitness.claim.impact.json"
    ))
    .unwrap();
    let initial = create_state(&native_plan, &BTreeMap::new()).unwrap();
    let execution = prepare(
        &native_plan,
        &native_inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    let circuit =
        IrSource::load(&include_bytes!("fixtures/curve-witness/321/CurveWitness.claim.zkir")[..])
            .unwrap();
    check(&execution, &circuit).unwrap();
}

#[cfg(feature = "zkir-320")]
const SCALAR_PLAN: &str =
    include_str!("fixtures/witness/320/TypedWitness.ScalarWitness.claim.witness.control.json");
#[cfg(feature = "zkir-320")]
const PAIR_PLAN: &str =
    include_str!("fixtures/witness/320/TypedWitness.PairWitness.claim.witness.control.json");
#[cfg(feature = "zkir-320")]
const UNIT_PLAN: &str =
    include_str!("fixtures/witness/320/TypedWitness.unitRelation.witness.control.json");
#[cfg(feature = "zkir-320")]
const EMPTY_PLAN: &str =
    include_str!("fixtures/witness/320/TypedWitness.emptyRelation.witness.control.json");
#[cfg(feature = "zkir-321")]
const SCALAR_PLAN: &str =
    include_str!("fixtures/witness/321/TypedWitness.ScalarWitness.claim.witness.control.json");
#[cfg(feature = "zkir-321")]
const PAIR_PLAN: &str =
    include_str!("fixtures/witness/321/TypedWitness.PairWitness.claim.witness.control.json");
#[cfg(feature = "zkir-321")]
const UNIT_PLAN: &str =
    include_str!("fixtures/witness/321/TypedWitness.unitRelation.witness.control.json");
#[cfg(feature = "zkir-321")]
const EMPTY_PLAN: &str =
    include_str!("fixtures/witness/321/TypedWitness.emptyRelation.witness.control.json");

fn signatures(plan: &Json) -> Vec<WitnessSignature> {
    plan["witnesses"]
        .as_array()
        .unwrap()
        .iter()
        .map(|value| WitnessSignature {
            name: value["name"].as_str().unwrap().to_owned(),
            operation: value["operation"].as_str().unwrap().to_owned(),
            capability: value["capability"].as_str().unwrap().to_owned(),
            parameters: value["parameters"]
                .as_array()
                .unwrap()
                .iter()
                .map(|parameter| Parameter {
                    name: parameter["name"].as_str().unwrap().to_owned(),
                    type_token: parameter["type"].as_str().unwrap().to_owned(),
                })
                .collect(),
            result_type: value["resultType"].as_str().unwrap().to_owned(),
            private_key: value["privateKey"].as_str().map(str::to_owned),
        })
        .collect()
}

fn source_context(signatures: &[WitnessSignature], attempt_id: &str) -> Context {
    let mut operations = BTreeMap::<String, Operation>::new();
    let mut providers = Vec::new();
    let mut capability_map = BTreeMap::<String, (String, BTreeSet<String>)>::new();
    for signature in signatures {
        let mut arguments: BTreeMap<_, _> = signature
            .parameters
            .iter()
            .map(|parameter| (parameter.name.clone(), parameter.type_token.clone()))
            .collect();
        if signature.operation == host::READ {
            arguments.insert("key".into(), "Key".into());
        }
        let operation = Operation {
            operation: signature.operation.clone(),
            argument_schema: arguments,
            result_schema: signature.result_type.clone(),
        };
        if let Some(previous) = operations.insert(signature.operation.clone(), operation) {
            assert_eq!(
                previous.argument_schema,
                operations[&signature.operation].argument_schema
            );
            if signature.operation == host::READ && previous.result_schema != signature.result_type {
                operations.get_mut(host::READ).unwrap().result_schema = host::SOURCE_CELL_TYPE.into();
            } else {
                assert_eq!(previous.result_schema, signature.result_type);
            }
        }
        let prefix = signature
            .private_key
            .as_deref()
            .map(|key| match key.rsplit_once('/') {
                Some((root, _)) => format!("{root}/"),
                None => key.to_owned(),
            })
            .unwrap_or_else(|| "lookup/".into());
        let entry = capability_map
            .entry(signature.capability.clone())
            .or_insert_with(|| (prefix.clone(), BTreeSet::new()));
        assert_eq!(entry.0, prefix);
        entry.1.insert(signature.operation.clone());
        if signature.private_key.is_some() {
            entry.1.insert(host::STAGE.into());
        }
        providers.push(Provider {
            input: signature.name.clone(),
            operation: signature.operation.clone(),
            capability: signature.capability.clone(),
            arguments: signature
                .private_key
                .as_ref()
                .map(|key| BTreeMap::from([("key".into(), json!(key))]))
                .unwrap_or_default(),
        });
    }
    let private = capability_map
        .entry("private".into())
        .or_insert_with(|| ("cache/".into(), BTreeSet::new()));
    assert_eq!(private.0, "cache/");
    private.1.insert(host::STAGE.into());
    let mut capabilities = capability_map
        .into_iter()
        .map(|(id, (key_prefix, operations))| Capability {
            id,
            namespace: "noctium".into(),
            key_prefix,
            operations: operations.into_iter().collect(),
        })
        .collect::<Vec<_>>();
    capabilities.push(Capability {
        id: "commit".into(),
        namespace: "noctium".into(),
        key_prefix: "cache/".into(),
        operations: vec![host::CAS.into()],
    });
    Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "preview-r0".into(),
        attempt_id: attempt_id.into(),
        capabilities,
        operations: operations.into_values().collect(),
        providers,
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

fn bound_session(
    plan_text: &str,
    inputs: BTreeMap<String, Json>,
    attempt_id: &str,
) -> (Session, Json) {
    let plan: Json = serde_json::from_str(plan_text).unwrap();
    let digest = hex::encode(Sha256::digest(plan["binding"].as_str().unwrap().as_bytes()));
    let context = source_context(&signatures(&plan), attempt_id);
    let target = binding(&plan)["target"]["entrypoint"]
        .as_str()
        .map(str::to_owned)
        .unwrap_or_else(|| plan["name"].as_str().unwrap().to_owned());
    let session = Session::from_json_with_invocation_target(
        plan.clone(),
        inputs,
        context,
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: target,
        }),
    )
    .unwrap();
    (session, plan)
}

fn binding(plan: &Json) -> Json {
    serde_json::from_str(plan["binding"].as_str().unwrap()).unwrap()
}

fn reply_json(request: &Json, attempt_id: &str, outcome: &str, value: Option<Json>) -> Json {
    let mut response = json!({
        "protocolVersion": 2,
        "requestId": request["requestId"],
        "attemptId": attempt_id,
        "outcome": outcome,
        "operation": request["operation"],
        "capability": request["capability"],
        "schema": request["schema"],
    });
    if outcome == "value" {
        response["value"] = value.unwrap();
    } else {
        response["error"] = json!({"code":"provider_failed"});
    }
    response
}

fn reply(request: &Json, attempt_id: &str, outcome: &str, value: Option<Json>) -> TypedResponse {
    serde_json::from_value(reply_json(request, attempt_id, outcome, value)).unwrap()
}

fn scalar_inputs() -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("expected".into(), json!("14")),
        ("seed".into(), json!("7")),
    ])
}

fn respond_scalar(session: &mut Session, request: &Json, attempt_id: &str) {
    let name = request["name"].as_str().unwrap();
    let value = match name {
        "cache" => session.private_request().unwrap()["invocationWrites"]["cache/last"]["value"]
            .as_str()
            .map(str::to_owned)
            .map(Json::String)
            .unwrap_or_else(|| json!("0")),
        "lookup" => json!("14"),
        _ => panic!("unexpected provider name"),
    };
    session
        .resume_typed(reply(request, attempt_id, "value", Some(value)))
        .unwrap();
}

#[test]
fn typed_repeated_calls_bind_exact_relation_inputs_and_transfer_staged_runtime() {
    let attempt = "a".repeat(64);
    let (mut session, plan) = bound_session(SCALAR_PLAN, scalar_inputs(), &attempt);
    assert!(
        session
            .stage(host::Stage {
                abi_version: 2,
                operation: host::STAGE.into(),
                capability: "private".into(),
                key: "cache/forged".into(),
                ty: "UIntRange<256>".into(),
                value: json!("999"),
            })
            .is_err()
    );
    let first = session.advance().unwrap();
    assert_eq!(first["status"], "need_host");
    assert_eq!(first["request"]["protocolVersion"], 2);
    assert!(first["request"]["requestId"].as_str().is_some_and(|id| {
        id.parse::<u64>()
            .is_ok_and(|number| number.to_string() == id)
    }));
    assert_eq!(first["request"]["name"], "cache");
    assert!(first["request"].get("attemptId").is_some());
    assert!(first["request"].to_string().find("cache/last").is_none());
    let private = session.private_request().unwrap();
    assert_eq!(private["arguments"]["key"], "cache/last");
    assert_eq!(private["invocationWrites"]["cache/last"]["value"], "1");
    assert!(private["invocationWrites"].get("cache/forged").is_none());
    let wrong_attempt = reply(
        &first["request"],
        &"b".repeat(64),
        "value",
        Some(json!("0")),
    );
    assert!(session.resume_typed(wrong_attempt).is_err());
    assert_eq!(session.advance().unwrap(), first);
    respond_scalar(&mut session, &first["request"], &attempt);

    let second = session.advance().unwrap();
    assert_eq!(second["request"]["name"], "cache");
    assert_ne!(
        first["request"]["requestId"],
        second["request"]["requestId"]
    );
    assert_eq!(second["request"]["arguments"], json!([]));
    assert_eq!(
        session.private_request().unwrap()["arguments"]["key"],
        "cache/last"
    );
    respond_scalar(&mut session, &second["request"], &attempt);

    let third = session.advance().unwrap();
    assert_eq!(third["request"]["name"], "lookup");
    assert_eq!(
        third["request"]["arguments"],
        json!([{"name":"seed","type":"UIntRange<256>"}])
    );
    assert_eq!(session.private_request().unwrap()["arguments"]["seed"], "7");
    respond_scalar(&mut session, &third["request"], &attempt);

    let mut previous = third;
    for expected_name in ["cache", "lookup"] {
        let next = session.advance().unwrap();
        assert_eq!(next["request"]["name"], expected_name);
        assert!(
            session
                .resume_typed(reply(
                    &previous["request"],
                    &attempt,
                    "value",
                    Some(json!("14"))
                ))
                .is_err()
        );
        assert_eq!(session.advance().unwrap(), next);
        respond_scalar(&mut session, &next["request"], &attempt);
        previous = next;
    }
    let complete = session.advance().unwrap();
    assert_eq!(complete["status"], "completed");
    assert_eq!(complete["result"], "14");

    let relation = binding(&plan)["nativeRelation"].clone();
    let completion = session.private_completion(&relation).unwrap();
    assert_eq!(completion["inputs"]["expected"], "14");
    assert_eq!(completion["inputs"]["seed"], "7");
    assert_eq!(completion["inputs"]["$helper3"], "1");
    assert_eq!(completion["inputs"]["$helper6"], "1");
    assert_eq!(completion["inputs"]["$helper9"], "14");
    assert_eq!(completion["inputs"]["$helper12"], "1");
    assert_eq!(completion["inputs"]["$helper15"], "14");
    assert_eq!(completion["hostWrites"]["cache/last"]["value"], "14");
    let mut crossed = relation.clone();
    crossed["instructions"][0]["op"] = json!("private_input");
    assert!(session.private_completion(&crossed).is_err());

    assert_eq!(completion["target"]["entrypoint"], "claim");
}

#[test]
fn malformed_crossed_reordered_and_provider_failure_responses_keep_or_reject_the_right_state() {
    let attempt = "d".repeat(64);
    let (mut session, _) = bound_session(SCALAR_PLAN, scalar_inputs(), &attempt);
    let first = session.advance().unwrap();
    let mut malformed = reply_json(&first["request"], &attempt, "value", Some(json!("0")));
    malformed["requestId"] = json!("01");
    assert!(
        session
            .resume_typed(serde_json::from_value(malformed).unwrap())
            .is_err()
    );
    let bad_shape = reply(&first["request"], &attempt, "value", Some(json!("00")));
    assert!(session.resume_typed(bad_shape).is_err());
    assert_eq!(session.advance().unwrap(), first);
    respond_scalar(&mut session, &first["request"], &attempt);
    let second = session.advance().unwrap();
    let failed = reply(&second["request"], &attempt, "error", None);
    assert_eq!(session.resume_typed(failed).unwrap()["status"], "failed");
    assert_eq!(session.advance().unwrap()["status"], "failed");
    assert!(session.private_request().is_err());
}

#[test]
fn dishonest_provider_result_fails_independent_source_constraints() {
    let attempt = "e".repeat(64);
    let (mut session, _) = bound_session(SCALAR_PLAN, scalar_inputs(), &attempt);
    let first = session.advance().unwrap();
    respond_scalar(&mut session, &first["request"], &attempt);
    let second = session.advance().unwrap();
    respond_scalar(&mut session, &second["request"], &attempt);
    let third = session.advance().unwrap();
    assert_eq!(third["request"]["name"], "lookup");
    session
        .resume_typed(reply(
            &third["request"],
            &attempt,
            "value",
            Some(json!("0")),
        ))
        .unwrap();
    let fourth = session.advance().unwrap();
    respond_scalar(&mut session, &fourth["request"], &attempt);
    let fifth = session.advance().unwrap();
    respond_scalar(&mut session, &fifth["request"], &attempt);
    assert_eq!(session.advance().unwrap()["status"], "failed");
    assert!(session.private_request().is_err());
}

#[cfg(feature = "zkir-321")]
#[test]
fn readable_private_state_source_binds_callbacks_stages_and_native_constraints() {
    use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
    use onchain_runtime::state::StateValue;
    use transient_crypto::{curve::Fr, fab::AlignedValueExt};

    let plan: Json = serde_json::from_str(include_str!(
        "fixtures/private-authoring/321/NoctiumExamples.PrivateStateCounter.advance.witness.control.json"
    ))
    .unwrap();
    let native_plan: Plan = serde_json::from_str(include_str!(
        "fixtures/private-authoring/321/NoctiumExamples.PrivateStateCounter.advance.impact.json"
    ))
    .unwrap();
    let circuit = IrSource::load(
        include_bytes!(
            "fixtures/private-authoring/321/NoctiumExamples.PrivateStateCounter.advance.zkir"
        )
        .as_slice(),
    )
    .unwrap();
    let relation = binding(&plan)["nativeRelation"].clone();
    let key = "noctium/NoctiumExamples.Wallet/saved";
    assert_eq!(
        binding(&plan)["ledgerInputs"],
        json!([
            {"name":"current", "type":"UIntRange<256>", "visibility":"public"}
        ])
    );
    for answer in ["2", "3"] {
        let attempt = "7".repeat(64);
        let make_context = || {
            let mut context = source_context(&signatures(&plan), &attempt);
            context
                .capabilities
                .iter_mut()
                .find(|capability| capability.id == "commit")
                .unwrap()
                .key_prefix = "noctium/NoctiumExamples.Wallet/".into();
            context
        };
        let digest = hex::encode(Sha256::digest(plan["binding"].as_str().unwrap().as_bytes()));
        assert!(
            Session::from_json_with_invocation_target(
                plan.clone(),
                BTreeMap::from([
                    ("expected".into(), json!("2")),
                    ("current".into(), json!("1"))
                ]),
                make_context(),
                Some(&digest),
                Some(InvocationTarget {
                    contract_address: "a".repeat(64),
                    entrypoint: "advance".into(),
                }),
            )
            .is_err()
        );
        let mut session = Session::from_json_with_invocation_target(
            plan.clone(),
            BTreeMap::from([("expected".into(), json!("2"))]),
            make_context(),
            Some(&digest),
            Some(InvocationTarget {
                contract_address: "a".repeat(64),
                entrypoint: "advance".into(),
            }),
        )
        .unwrap();
        let read = session.advance().unwrap();
        assert_eq!(read["request"]["operation"], host::READ);
        assert_eq!(session.private_request().unwrap()["arguments"]["key"], key);
        session
            .resume_typed(reply(&read["request"], &attempt, "value", Some(json!("1"))))
            .unwrap();
        let call = session.advance().unwrap();
        assert_eq!(
            session.private_request().unwrap()["arguments"]["previous"],
            "1"
        );
        assert!(
            session
                .resume_typed(reply(
                    &call["request"],
                    &attempt,
                    "value",
                    Some(json!("256"))
                ))
                .is_err()
        );
        assert_eq!(session.advance().unwrap(), call);
        session
            .resume_typed(reply(
                &call["request"],
                &attempt,
                "value",
                Some(json!(answer)),
            ))
            .unwrap();
        let complete = session.advance().unwrap();
        if answer == "3" {
            assert_eq!(complete["status"], "failed");
            assert!(session.private_completion(&relation).is_err());
            continue;
        }
        assert_eq!(complete["status"], "completed", "{complete}");
        assert_eq!(complete["result"], "2");
        let completion = session.private_completion(&relation).unwrap();
        assert!(completion["inputs"].get("current").is_none());
        assert_eq!(completion["hostWrites"][key]["value"], "2");
        let inputs = serde_json::from_value(completion["inputs"].clone()).unwrap();
        let state = create_state(
            &native_plan,
            &BTreeMap::from([(native_plan.state[0].name.clone(), json!("1"))]),
        )
        .unwrap();
        let mut execution = prepare(
            &native_plan,
            &inputs,
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .unwrap();
        check(&execution, &circuit).unwrap();
        let wrong_state = create_state(
            &native_plan,
            &BTreeMap::from([(native_plan.state[0].name.clone(), json!("7"))]),
        )
        .unwrap();
        if let Ok(wrong) = prepare(
            &native_plan,
            &inputs,
            &wrong_state,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        ) {
            assert!(check(&wrong, &circuit).is_err());
        }
        let StateValue::Array(state) = execution.after.state.get_ref() else {
            panic!("expected public state array")
        };
        let StateValue::Cell(count) = &*state.get(0).unwrap() else {
            panic!("expected public counter cell")
        };
        let mut fields = Vec::new();
        count.value_only_field_repr(&mut fields);
        assert_eq!(fields, vec![Fr::from(2u64)]);
        // Alter the private read after host validation to exercise the native relation alone.
        execution.preimage.private_transcript[0] = Fr::from(9u64);
        assert!(check(&execution, &circuit).is_err());
    }
}

#[cfg(feature = "zkir-321")]
#[test]
#[ignore = "requires fresh TypedPointKeccak Lean artifacts"]
fn typed_point_keccak_runs_through_the_witness_plan() -> anyhow::Result<()> {
    use coin_structure::contract::ContractAddress;
    use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
    use std::{fs, path::PathBuf};

    let root = PathBuf::from(std::env::var_os("NOCTIUM_HOSTED_POINT_KECCAK_DIR").unwrap());
    let stem = "TypedPointKeccak.hashHosted";
    let control = fs::read_to_string(root.join(format!("{stem}.witness.control.json")))?;
    let expected = json!({"kind":"bytes", "values":hex::decode(
        "571cf838e63c171196cd7a301bb8fab87d13d946769a41e1004d9da49f6bfca8"
    )?});
    let attempt = "c".repeat(64);
    let (mut session, _) = bound_session(
        &control,
        BTreeMap::from([("expected".into(), expected.clone())]),
        &attempt,
    );
    let pending = session.advance()?;
    assert_eq!(pending["status"], "need_host");
    let request = &pending["request"];
    let wrong_curve = json!({"kind":"foreign", "type":"Secp256r1Point", "bytes": vec![0; 33]});
    assert!(session
        .resume_typed(reply(request, &attempt, "value", Some(wrong_curve)))
        .is_err());
    assert_eq!(session.advance()?, pending);
    let point = json!({"kind":"foreign", "type":"Secp256k1Point", "bytes": hex::decode(
        "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"
    )?});
    session.resume_typed(reply(request, &attempt, "value", Some(point)))?;
    assert_eq!(session.advance()?["status"], "completed");

    let relation_bytes = fs::read(root.join(format!("{stem}.zkir")))?;
    let relation = serde_json::from_slice(&relation_bytes)?;
    let completion = session.private_completion(&relation)?;
    let inputs = serde_json::from_value(completion["inputs"].clone())?;
    let plan: Plan =
        serde_json::from_slice(&fs::read(root.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(relation_bytes.as_slice())?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    assert_eq!(execution.returns_json()["pointDigest"], expected);
    Ok(())
}

#[cfg(feature = "zkir-321")]
#[test]
#[ignore = "requires fresh PrivateStateMixed Lean artifacts"]
fn typed_private_cells_bind_distinct_read_types() {
    use coin_structure::contract::ContractAddress;
    use ledger::structure::INITIAL_PARAMETERS;
    use noctium_runtime::{Plan, check, create_state, field_decimal, prepare, zkir::IrSource};
    use std::{fs, path::PathBuf};
    use transient_crypto::curve::{EmbeddedFr, EmbeddedGroupAffine, Fr};

    let root = PathBuf::from(std::env::var_os("NOCTIUM_MIXED_PRIVATE_STATE_ARTIFACTS").unwrap());
    let stem = "PrivateStateMixed.Meter.advance";
    let control: Json = serde_json::from_slice(
        &fs::read(root.join(format!("{stem}.witness.control.json"))).unwrap(),
    )
    .unwrap();
    let attempt = "e".repeat(64);
    let witness_signatures = signatures(&control);
    let receipt_schema = &witness_signatures
        .iter()
        .find(|signature| {
            signature.private_key.as_deref() == Some("noctium/PrivateStateMixed.Wallet/receipt")
        })
        .unwrap()
        .result_type;
    assert!(receipt_schema.starts_with("Aggregate:"));
    let mut context = source_context(&witness_signatures, &attempt);
    context
        .capabilities
        .iter_mut()
        .find(|c| c.id == "commit")
        .unwrap()
        .key_prefix = "noctium/PrivateStateMixed.Wallet/".into();
    let pin = hex::encode(Sha256::digest(
        control["binding"].as_str().unwrap().as_bytes(),
    ));
    let point = |value: EmbeddedGroupAffine| json!({"kind":"jubjubPoint", "x":field_decimal(value.x().unwrap()), "y":field_decimal(value.y().unwrap())});
    let scalar = |value: &str| json!({"kind":"jubjubScalar", "value":value});
    let generator = EmbeddedGroupAffine::generator();
    let recipient = generator * EmbeddedFr::from(7u64);
    let mut session = Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([
            ("expected".into(), json!("2")),
            ("replacement".into(), scalar("11")),
        ]),
        context,
        Some(&pin),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: "advance".into(),
        }),
    )
    .unwrap();
    for (key, schema, response, invalid) in [
        ("saved", "UIntRange<256>", json!("1"), json!(true)),
        ("enabled", "Bool", json!(true), json!("1")),
        ("secret", "JubjubScalar", scalar("7"), scalar("07")),
        (
            "recipient",
            "JubjubPoint",
            point(recipient),
            json!({"kind":"jubjubPoint", "x":"0", "y":"0"}),
        ),
        (
            "receipt",
            receipt_schema.as_str(),
            json!({"kind":"struct", "id":"MeterReceipt", "fields":[
                {"name":"amount", "value":{"kind":"uint","maximum":"255","value":"2"}},
                {"name":"okay", "value":{"kind":"bool","value":true}}
            ]}),
            json!({"kind":"struct", "id":"MeterReceipt", "fields":[]}),
        ),
    ] {
        let pending = session.advance().unwrap();
        let request = &pending["request"];
        assert_eq!(request["operation"], host::READ);
        assert_eq!(request["schema"], schema);
        assert_eq!(
            session.private_request().unwrap()["arguments"]["key"],
            format!("noctium/PrivateStateMixed.Wallet/{key}")
        );
        assert!(
            session
                .resume_typed(reply(request, &attempt, "value", Some(invalid)))
                .is_err()
        );
        assert_eq!(session.advance().unwrap(), pending);
        session
            .resume_typed(reply(request, &attempt, "value", Some(response)))
            .unwrap();
    }
    let staged_receipt = json!({"kind":"struct", "id":"MeterReceipt", "fields":[
        {"name":"amount", "value":{"kind":"uint","maximum":"255","value":"3"}},
        {"name":"okay", "value":{"kind":"bool","value":false}}
    ]});
    let receipt_key = "noctium/PrivateStateMixed.Wallet/receipt";
    let pending = session.advance().unwrap();
    let request = &pending["request"];
    assert_eq!(request["operation"], host::READ);
    assert_eq!(request["schema"], receipt_schema.as_str());
    let private = session.private_request().unwrap();
    assert_eq!(private["arguments"]["key"], receipt_key);
    assert_eq!(
        private["invocationWrites"][receipt_key]["value"], staged_receipt
    );
    let mut substituted = staged_receipt.clone();
    substituted["fields"][0]["value"]["value"] = json!("2");
    assert!(session
        .resume_typed(reply(request, &attempt, "value", Some(substituted)))
        .is_err());
    assert_eq!(session.advance().unwrap(), pending);
    session
        .resume_typed(reply(request, &attempt, "value", Some(staged_receipt.clone())))
        .unwrap();
    let public = session.advance().unwrap();
    assert_eq!(public["status"], "completed");
    assert!(public.get("hostWrites").is_none());
    let completed = session
        .private_completion(&binding(&control)["nativeRelation"])
        .unwrap();
    assert_eq!(completed["hostWrites"][receipt_key]["value"], staged_receipt);
    assert_eq!(
        completed["hostWrites"]["noctium/PrivateStateMixed.Wallet/saved"]["value"],
        "2"
    );
    assert_eq!(
        completed["hostWrites"]["noctium/PrivateStateMixed.Wallet/enabled"]["value"],
        false
    );
    assert_eq!(
        completed["hostWrites"]["noctium/PrivateStateMixed.Wallet/secret"]["value"],
        scalar("11")
    );
    assert_eq!(
        completed["hostWrites"]["noctium/PrivateStateMixed.Wallet/recipient"]["value"],
        point(generator * EmbeddedFr::from(11u64))
    );
    let plan: Plan =
        serde_json::from_slice(&fs::read(root.join(format!("{stem}.impact.json"))).unwrap())
            .unwrap();
    let circuit =
        IrSource::load(fs::File::open(root.join(format!("{stem}.zkir"))).unwrap()).unwrap();
    let state = create_state(&plan, &BTreeMap::from([("count".into(), json!("1"))])).unwrap();
    let mut execution = prepare(
        &plan,
        &serde_json::from_value(completed["inputs"].clone()).unwrap(),
        &state,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    )
    .unwrap();
    check(&execution, &circuit).unwrap();
    assert_eq!(execution.returns_json()["accepted"], true);
    assert_eq!(
        execution.preimage.private_transcript,
        [
            Fr::from(11u64),
            Fr::from(1u64),
            Fr::from(1u64),
            Fr::from(7u64),
            recipient.x().unwrap(),
            recipient.y().unwrap(),
            Fr::from(2u64),
            Fr::from(1u64),
            Fr::from(3u64),
            Fr::from(0u64),
        ]
    );
    execution.preimage.private_transcript[2] = Fr::from(0u64);
    assert!(check(&execution, &circuit).is_err());
    execution.preimage.private_transcript[2] = Fr::from(1u64);
    execution.preimage.private_transcript[3] = Fr::from(8u64);
    assert!(check(&execution, &circuit).is_err());
    execution.preimage.private_transcript[3] = Fr::from(7u64);
    execution.preimage.private_transcript[6] = Fr::from(3u64);
    assert!(check(&execution, &circuit).is_err());
}

fn pair_value(amount: &str) -> Json {
    json!({
        "kind":"struct",
        "id":"TypedWitness.Pair",
        "fields":[
            {"name":"amount","value":{"kind":"uint","maximum":"255","value":amount}},
            {"name":"okay","value":{"kind":"bool","value":true}}
        ]
    })
}

#[test]
fn fixed_composite_arguments_and_results_keep_component_types_and_private_leaves() {
    let attempt = "f".repeat(64);
    let request = pair_value("7");
    let inputs = BTreeMap::from([
        ("expected".into(), json!("14")),
        ("request".into(), request.clone()),
    ]);
    let (mut session, plan) = bound_session(PAIR_PLAN, inputs, &attempt);
    let pending = session.advance().unwrap();
    assert_eq!(pending["request"]["name"], "pair");
    assert_eq!(
        pending["request"]["arguments"],
        json!([{"name":"request","type":"Aggregate:t0"}])
    );
    assert_eq!(
        session.private_request().unwrap()["arguments"]["request"],
        request
    );
    let result = pair_value("14");
    session
        .resume_typed(reply(&pending["request"], &attempt, "value", Some(result)))
        .unwrap();
    let complete = session.advance().unwrap();
    assert_eq!(complete["status"], "completed");
    assert_eq!(complete["result"]["kind"], "struct");
    let completion = session
        .private_completion(&binding(&plan)["nativeRelation"])
        .unwrap();
    assert_eq!(completion["inputs"]["request.amount"], "7");
    assert_eq!(completion["inputs"]["request.okay"], "1");
    assert_eq!(completion["inputs"]["$helper7"], "14");
    assert_eq!(completion["inputs"]["$helper8"], "1");
    assert_eq!(completion["hostWrites"]["cache/last"]["value"], "14");
}

#[cfg(feature = "zkir-321")]
#[test]
#[ignore = "requires fresh WitnessSource Lean artifacts"]
fn aggregate_argument_binds_hosted_callee_and_typed_caller() {
    use base_crypto::hash::HashOutput;
    use coin_structure::contract::ContractAddress;
    use ledger::structure::INITIAL_PARAMETERS;
    use noctium_runtime::{
        Plan,
        assembly::{CheckedNativeCall, assemble_checked_calls},
        create_state, prepare,
        zkir::IrSource,
    };
    use onchain_runtime::{context::QueryContext, state::EntryPointBuf};
    use rand::rngs::OsRng;
    use std::{fs, path::PathBuf};
    use transient_crypto::curve::Fr;

    let artifacts = PathBuf::from(std::env::var_os("NOCTIUM_AGGREGATE_ARGUMENT_ARTIFACTS").unwrap());
    let load = |stem: &str| {
        let plan = serde_json::from_slice::<Plan>(
            &fs::read(artifacts.join(format!("{stem}.impact.json"))).unwrap(),
        )
        .unwrap();
        let circuit =
            IrSource::load(fs::File::open(artifacts.join(format!("{stem}.zkir"))).unwrap())
                .unwrap();
        (plan, circuit)
    };
    let callee_stem = "TypedWitness.PairCallArguments.claim";
    let (callee_plan, callee_circuit) = load(callee_stem);
    let (caller_plan, caller_circuit) = load("TypedWitness.PairCaller.forward");
    let control =
        fs::read_to_string(artifacts.join(format!("{callee_stem}.witness.control.json"))).unwrap();
    let request = pair_value("7");
    let inputs = BTreeMap::from([
        ("expected".into(), json!("14")),
        ("request".into(), request.clone()),
    ]);
    let attempt = "f".repeat(64);
    let (mut session, control) = bound_session(&control, inputs.clone(), &attempt);
    let pending = session.advance().unwrap();
    assert_eq!(session.private_request().unwrap()["arguments"]["request"], request);
    session
        .resume_typed(reply(&pending["request"], &attempt, "value", Some(pair_value("14"))))
        .unwrap();
    assert_eq!(session.advance().unwrap()["status"], "completed");
    let handoff = session
        .private_completion(&binding(&control)["nativeRelation"])
        .unwrap();
    let callee_address = ContractAddress(HashOutput([9; 32]));
    let caller_address = ContractAddress(HashOutput([8; 32]));
    let callee_state =
        create_state(&callee_plan, &BTreeMap::from([("total".into(), json!("1"))])).unwrap();
    let callee = prepare(
        &callee_plan,
        &serde_json::from_value(handoff["inputs"].clone()).unwrap(),
        &callee_state,
        &INITIAL_PARAMETERS,
        callee_address,
    )
    .unwrap();
    assert_eq!(callee.preimage.inputs, [Fr::from(7u64), Fr::from(1u64)]);
    assert_eq!(callee.preimage.private_transcript, [Fr::from(14u64), Fr::from(1u64)]);
    assert_eq!(callee.returns_json()["amount"], "14");
    let caller_state = create_state(
        &caller_plan,
        &BTreeMap::from([("route".into(), json!({"kind":"bytes", "values":callee_address.0.0}))]),
    )
    .unwrap();
    let assemble = |amount: &str| {
        let caller = prepare(
            &caller_plan,
            &BTreeMap::from([
                ("opening".into(), json!("101")),
                ("requestAmount".into(), json!(amount)),
                ("requestOkay".into(), json!(true)),
                ("expected".into(), json!("14")),
            ]),
            &caller_state,
            &INITIAL_PARAMETERS,
            caller_address,
        )
        .unwrap();
        assemble_checked_calls(
            &[
                CheckedNativeCall {
                    execution: &caller,
                    circuit: &caller_circuit,
                    initial_context: QueryContext::new(caller_state.clone(), caller_address),
                    entry_point: EntryPointBuf(b"forward".to_vec()),
                    communication_commitment_rand: Fr::from(53u64),
                },
                CheckedNativeCall {
                    execution: &callee,
                    circuit: &callee_circuit,
                    initial_context: QueryContext::new(callee_state.clone(), callee_address),
                    entry_point: EntryPointBuf(b"claim".to_vec()),
                    communication_commitment_rand: Fr::from(101u64),
                },
            ],
            &INITIAL_PARAMETERS,
            1_800_000_000,
            &mut OsRng,
        )
    };
    let intent = assemble("7").unwrap();
    let mut calls = intent.calls();
    assert!(calls.next().unwrap().calls(calls.next().unwrap()));
    assert!(assemble("6").is_err());

    for fields in [
        json!(["request.okay", "request.amount"]),
        json!(["request.amount"]),
    ] {
        let mut changed = binding(&control);
        changed["callInputs"] = fields;
        let text = changed.to_string();
        let digest = hex::encode(Sha256::digest(text.as_bytes()));
        let context = source_context(&signatures(&control), &attempt);
        let mut altered = control.clone();
        altered["binding"] = json!(text);
        let rejected = Session::from_json_with_invocation_target(
            altered,
            inputs.clone(),
            context,
            Some(&digest),
            Some(InvocationTarget {
                contract_address: "a".repeat(64),
                entrypoint: "claim".into(),
            }),
        );
        let Err(error) = rejected else {
            panic!("invalid aggregate call arguments were accepted")
        };
        assert!(error.to_string().contains("all leaves in layout order"), "{error:#}");
    }
}

#[test]
fn same_provider_across_live_sessions_rejects_crossed_replies() {
    let (mut first, _) = bound_session(SCALAR_PLAN, scalar_inputs(), &"1".repeat(64));
    let (mut second, _) = bound_session(
        SCALAR_PLAN,
        BTreeMap::from([
            ("expected".into(), json!("22")),
            ("seed".into(), json!("9")),
        ]),
        &"2".repeat(64),
    );
    let a = first.advance().unwrap();
    let b = second.advance().unwrap();
    assert_eq!(a["request"]["name"], b["request"]["name"]);
    assert_ne!(a["request"]["requestId"], b["request"]["requestId"]);
    assert!(
        second
            .resume_typed(reply(
                &a["request"],
                &"1".repeat(64),
                "value",
                Some(json!("0"))
            ))
            .is_err()
    );
    assert!(
        first
            .resume_typed(reply(
                &b["request"],
                &"2".repeat(64),
                "value",
                Some(json!("0"))
            ))
            .is_err()
    );
    assert_eq!(first.advance().unwrap(), a);
    assert_eq!(second.advance().unwrap(), b);
}

#[test]
fn unit_and_zero_leaf_nominal_calls_have_canonical_values_and_keep_call_records() {
    let attempt = "9".repeat(64);
    let (mut unit, unit_plan) = bound_session(UNIT_PLAN, BTreeMap::new(), &attempt);
    let pending = unit.advance().unwrap();
    assert_eq!(pending["request"]["name"], "unit");
    assert_eq!(pending["request"]["arguments"], json!([]));
    assert!(
        unit.resume_typed(reply(
            &pending["request"],
            &attempt,
            "value",
            Some(Json::Null)
        ))
        .is_err()
    );
    let mut missing = reply_json(
        &pending["request"],
        &attempt,
        "value",
        Some(json!({"kind":"unit"})),
    );
    missing.as_object_mut().unwrap().remove("value");
    assert!(
        unit.resume_typed(serde_json::from_value::<TypedResponse>(missing).unwrap())
            .is_err()
    );
    assert_eq!(unit.advance().unwrap(), pending);
    unit.resume_typed(reply(
        &pending["request"],
        &attempt,
        "value",
        Some(json!({"kind":"unit"})),
    ))
    .unwrap();
    assert_eq!(unit.advance().unwrap()["status"], "completed");
    let relation = binding(&unit_plan)["nativeRelation"].clone();
    assert_eq!(
        unit.private_completion(&relation).unwrap()["inputs"],
        json!({})
    );

    let (mut empty, empty_plan) = bound_session(EMPTY_PLAN, BTreeMap::new(), &attempt);
    let pending = empty.advance().unwrap();
    assert_eq!(pending["request"]["arguments"], json!([]));
    empty
        .resume_typed(reply(
            &pending["request"],
            &attempt,
            "value",
            Some(json!({"kind":"struct","id":"TypedWitness.Empty","fields":[]})),
        ))
        .unwrap();
    assert_eq!(empty.advance().unwrap()["status"], "completed");
    let relation = binding(&empty_plan)["nativeRelation"].clone();
    assert_eq!(
        empty.private_completion(&relation).unwrap()["inputs"],
        json!({})
    );

    let (mut failed, _) = bound_session(UNIT_PLAN, BTreeMap::new(), &attempt);
    let pending = failed.advance().unwrap();
    assert_eq!(
        failed
            .resume_typed(reply(&pending["request"], &attempt, "error", None))
            .unwrap()["status"],
        "failed"
    );
}

#[test]
fn native_typed_plans_require_a_frozen_matching_target_before_execution() {
    let plan: Json = serde_json::from_str(SCALAR_PLAN).unwrap();
    let digest = hex::encode(Sha256::digest(plan["binding"].as_str().unwrap().as_bytes()));
    let attempt = "8".repeat(64);
    let context = source_context(&signatures(&plan), &attempt);
    assert!(
        Session::from_json_with_binding_sha256(
            plan.clone(),
            scalar_inputs(),
            context,
            Some(&digest),
        )
        .is_err()
    );
    let wrong_context = source_context(&signatures(&plan), &attempt);
    assert!(
        Session::from_json_with_invocation_target(
            plan,
            scalar_inputs(),
            wrong_context,
            Some(&digest),
            Some(InvocationTarget {
                contract_address: "a".repeat(64),
                entrypoint: "other".into(),
            }),
        )
        .is_err()
    );
}

#[test]
fn typed_witness_providers_cannot_impersonate_reserved_state_journal_operations() {
    let attempt = "c".repeat(64);
    for operation in [host::STAGE, host::CAS] {
        let mut plan: Json = serde_json::from_str(UNIT_PLAN).unwrap();
        plan["mode"] = json!("host");
        plan["binding"] = Json::Null;
        plan["witnesses"][0]["operation"] = json!(operation);
        let context = source_context(&signatures(&plan), &attempt);
        assert!(Session::from_json(plan, BTreeMap::new(), context).is_err());
    }
}
