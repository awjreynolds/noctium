#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs, path::PathBuf};

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
    let state = create_state(&plan, &BTreeMap::new())?;
    let prepare_for = |enabled, allowed| {
        prepare(
            &plan,
            &BTreeMap::<String, Json>::from([
                ("enabled".into(), json!(enabled)),
                ("allowed".into(), json!(allowed)),
            ]),
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
    };

    for (enabled, allowed, expected) in [(false, false, "9"), (true, true, "7")] {
        let accepted = prepare_for(enabled, allowed)?;
        check(&accepted, &circuit)?;
        assert_eq!(
            accepted.returns_json(),
            BTreeMap::from([("result".into(), json!(expected))])
        );
    }

    if let Ok(rejected) = prepare_for(true, false) {
        assert!(check(&rejected, &circuit).is_err());
    }
    Ok(())
}
