#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{check, control::Session, create_state, host, prepare, zkir::IrSource, Plan};
use serde_json::{json, Value as Json};
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::curve::Fr;

#[test]
#[ignore = "requires fresh NamedProofUnit artifacts in NOCTIUM_NAMED_PROOF_UNIT_DIR"]
fn named_proof_unit_enforces_the_predicate_without_effects_or_returns() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_NAMED_PROOF_UNIT_DIR").expect("NOCTIUM_NAMED_PROOF_UNIT_DIR"),
    );
    let stem = "NamedProofUnit.checkGate";
    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let prepare_for = |allowed| {
        prepare(
            &plan,
            &BTreeMap::<String, Json>::from([("allowed".into(), json!(allowed))]),
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
    };

    let accepted = prepare_for(true)?;
    assert_eq!(check(&accepted, &circuit)?, accepted.activity_schedule);
    assert!(accepted.returns_json().is_empty());
    assert_eq!(accepted.after.state, state);

    let rejected = prepare_for(false)?;
    assert!(check(&rejected, &circuit).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh NamedProofUnit artifacts in NOCTIUM_NAMED_PROOF_UNIT_DIR"]
fn nested_unit_assertion_blocks_the_continuation_on_false() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_NAMED_PROOF_UNIT_DIR").expect("NOCTIUM_NAMED_PROOF_UNIT_DIR"),
    );
    let stem = "NamedProofUnit.checkNestedGate";
    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    let control_path = directory.join(format!("{stem}.witness.control.json"));
    let mut portable_plan: Json = serde_json::from_slice(&fs::read(control_path)?)?;
    let portable_object = portable_plan.as_object_mut().expect("control plan object");
    portable_object.insert("schemaVersion".into(), json!(1));
    portable_object.remove("types");
    portable_object.remove("mode");
    portable_object.remove("binding");
    let portable_context = || host::Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "fixture-r0".into(),
        attempt_id: "d".repeat(64),
        capabilities: vec![
            host::Capability {
                id: "commit".into(),
                namespace: "noctium".into(),
                key_prefix: "cache/".into(),
                operations: vec![host::CAS.into()],
            },
            host::Capability {
                id: "private".into(),
                namespace: "noctium".into(),
                key_prefix: "cache/".into(),
                operations: vec![host::STAGE.into()],
            },
        ],
        operations: vec![],
        providers: vec![],
        commit_capability: "commit".into(),
        limits: host::Limits::default(),
    };
    let run_host = |enabled, allowed, second_allowed| {
        let inputs = BTreeMap::from([
            ("enabled".into(), json!(enabled)),
            ("allowed".into(), json!(allowed)),
            ("secondAllowed".into(), json!(second_allowed)),
        ]);
        let mut session = Session::from_json(portable_plan.clone(), inputs, portable_context())?;
        session.advance()
    };
    let completed = run_host(false, false, false)?;
    assert_eq!(completed["result"], json!("9"));
    let first_failure = run_host(true, false, true)?;
    assert_eq!(first_failure["status"], "failed");
    assert_eq!(first_failure["error"]["message"], "first gate denied");
    let second_failure = run_host(true, true, false)?;
    assert_eq!(second_failure["status"], "failed");
    assert_eq!(second_failure["error"]["message"], "second gate denied");
    let mut generic_plan: Json = serde_json::from_slice(&fs::read(
        directory.join("NamedProofUnit.checkGate.witness.control.json"),
    )?)?;
    let generic_object = generic_plan.as_object_mut().expect("control plan object");
    generic_object.insert("schemaVersion".into(), json!(1));
    generic_object.remove("types");
    generic_object.remove("mode");
    generic_object.remove("binding");
    let mut generic_session = Session::from_json(
        generic_plan,
        BTreeMap::from([("allowed".into(), json!(false))]),
        portable_context(),
    )?;
    let generic_failure = generic_session.advance()?;
    assert_eq!(generic_failure["status"], "failed");
    assert!(generic_failure["error"].get("message").is_none());

    let state = create_state(&plan, &BTreeMap::new())?;
    let prepare_for = |enabled, allowed, second_allowed| {
        prepare(
            &plan,
            &BTreeMap::<String, Json>::from([
                ("enabled".into(), json!(enabled)),
                ("allowed".into(), json!(allowed)),
                ("secondAllowed".into(), json!(second_allowed)),
            ]),
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
    };

    for (enabled, allowed, second_allowed, expected) in
        [(false, false, false, "9"), (true, true, true, "7")]
    {
        let accepted = prepare_for(enabled, allowed, second_allowed)?;
        check(&accepted, &circuit)?;
        assert_eq!(
            accepted.returns_json(),
            BTreeMap::from([("result".into(), json!(expected))])
        );
    }

    assert!(prepare_for(true, false, true).is_err());
    assert!(prepare_for(true, true, false).is_err());

    let mut relation_rejection = prepare_for(true, true, true)?;
    relation_rejection.preimage.public_transcript_inputs[1] = Fr::from(0u64);
    assert!(check(&relation_rejection, &circuit).is_err());
    Ok(())
}
