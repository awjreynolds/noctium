#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{check, control::Session, create_state, host, prepare, zkir::IrSource, Plan};
use serde_json::{json, Value as Json};
use std::{collections::BTreeMap, fs, path::{Path, PathBuf}};
use transient_crypto::curve::Fr;

fn run_portable_fixture(
    directory: &Path,
    stem: &str,
    inputs: BTreeMap<String, Json>,
) -> anyhow::Result<Json> {
    let path = directory.join(format!("{stem}.witness.control.json"));
    let mut plan: Json = serde_json::from_slice(&fs::read(path)?)?;
    let object = plan.as_object_mut().expect("control plan object");
    object.insert("schemaVersion".into(), json!(1));
    object.remove("types");
    object.remove("mode");
    object.remove("binding");
    let context = host::Context {
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
    Session::from_json(plan, inputs, context)?.advance()
}

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
    let run_host = |enabled, allowed, second_allowed| {
        let inputs = BTreeMap::from([
            ("enabled".into(), json!(enabled)),
            ("allowed".into(), json!(allowed)),
            ("secondAllowed".into(), json!(second_allowed)),
        ]);
        run_portable_fixture(&directory, stem, inputs)
    };
    let completed = run_host(false, false, false)?;
    assert_eq!(completed["result"], json!("9"));
    let first_failure = run_host(true, false, true)?;
    assert_eq!(first_failure["status"], "failed");
    assert_eq!(first_failure["error"]["message"], "first gate denied");
    let second_failure = run_host(true, true, false)?;
    assert_eq!(second_failure["status"], "failed");
    assert_eq!(second_failure["error"]["message"], "second gate denied");
    let generic_failure = run_portable_fixture(
        &directory,
        "NamedProofUnit.checkGate",
        BTreeMap::from([("allowed".into(), json!(false))]),
    )?;
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

#[test]
#[ignore = "requires fresh NamedProofUnit artifacts in NOCTIUM_NAMED_PROOF_UNIT_DIR"]
fn conditional_unit_assertions_check_only_the_selected_branch() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_NAMED_PROOF_UNIT_DIR").expect("NOCTIUM_NAMED_PROOF_UNIT_DIR"),
    );
    let stem = "NamedProofUnit.checkConditionalUnit";
    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let inputs = |choice, first, second| {
        BTreeMap::from([
            ("choice".into(), json!(choice)),
            ("first".into(), json!(first)),
            ("second".into(), json!(second)),
        ])
    };
    let prepare_for = |choice, first, second| {
        prepare(
            &plan,
            &inputs(choice, first, second),
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
    };

    for (choice, first, second) in [(true, true, false), (false, false, true)] {
        let accepted = prepare_for(choice, first, second)?;
        check(&accepted, &circuit)?;
        assert_eq!(
            accepted.returns_json(),
            BTreeMap::from([("result".into(), json!("7"))])
        );
    }
    for (choice, first, second, message) in [
        (true, false, true, "positive arm denied"),
        (false, true, false, "negative arm denied"),
    ] {
        assert!(prepare_for(choice, first, second).is_err());
        let failed = run_portable_fixture(&directory, stem, inputs(choice, first, second))?;
        assert_eq!(failed["status"], "failed");
        assert_eq!(failed["error"]["message"], message);
    }

    let mut relation_rejection = prepare_for(true, true, false)?;
    assert!(relation_rejection.preimage.public_transcript_inputs.len() >= 3);
    relation_rejection.preimage.public_transcript_inputs[1] = Fr::from(0u64);
    assert!(check(&relation_rejection, &circuit).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh NamedProofUnit artifacts in NOCTIUM_NAMED_PROOF_UNIT_DIR"]
fn unit_helper_argument_assertion_rejects_false_and_binds_the_input() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_NAMED_PROOF_UNIT_DIR").expect("NOCTIUM_NAMED_PROOF_UNIT_DIR"),
    );
    let stem = "NamedProofUnit.checkUnitHelperArgument";
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
    check(&accepted, &circuit)?;
    assert_eq!(
        accepted.returns_json(),
        BTreeMap::from([("result".into(), json!("11"))])
    );
    assert!(accepted.preimage.inputs.is_empty());
    assert!(accepted.preimage.private_transcript.is_empty());
    assert!(prepare_for(false).is_err());
    let failed = run_portable_fixture(
        &directory,
        stem,
        BTreeMap::from([("allowed".into(), json!(false))]),
    )?;
    assert_eq!(failed["status"], "failed");
    assert_eq!(failed["error"]["message"], "helper argument denied");

    let mut relation_rejection = accepted;
    assert!(!relation_rejection.preimage.public_transcript_inputs.is_empty());
    relation_rejection.preimage.public_transcript_inputs[0] = Fr::from(0u64);
    assert!(check(&relation_rejection, &circuit).is_err());
    Ok(())
}
