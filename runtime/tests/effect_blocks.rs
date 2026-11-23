#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Db, Expr, Instruction, Plan, check, create_state, field_decimal, prepare, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    env, fs,
    path::{Path, PathBuf},
};
use transient_crypto::curve::Fr;
use transient_crypto::fab::AlignedValueExt;

const PLAN: &str = include_str!(
    "fixtures/generic-state/issue43-effect-blocks/321/Issue43EffectBlocks.update.impact.json"
);
const CIRCUIT: &[u8] = include_bytes!(
    "fixtures/generic-state/issue43-effect-blocks/321/Issue43EffectBlocks.update.zkir"
);

const ARTIFACTS_ENV: &str = "NOCTIUM_EFFECT_BLOCKS_DIR";
const ARTIFACT_STEM: &str = "Issue43EffectBlocks.update";

struct Fixture {
    plan: Plan,
    circuit: IrSource,
    range_checks: usize,
}

fn range_check_count(circuit: &[u8]) -> usize {
    let document: Json = serde_json::from_slice(circuit).expect("source ZKIR JSON parses");
    document["instructions"]
        .as_array()
        .expect("ZKIR contains instructions")
        .iter()
        .filter(|instruction| instruction["op"] == "constrain_bits")
        .count()
}

fn fixture(directory: Option<&Path>) -> Fixture {
    let (plan_bytes, circuit_bytes) = match directory {
        Some(directory) => (
            fs::read(directory.join(format!("{ARTIFACT_STEM}.impact.json")))
                .expect("fresh Impact artifact exists"),
            fs::read(directory.join(format!("{ARTIFACT_STEM}.zkir")))
                .expect("fresh ZKIR artifact exists"),
        ),
        None => (PLAN.as_bytes().to_vec(), CIRCUIT.to_vec()),
    };
    Fixture {
        plan: serde_json::from_slice(&plan_bytes).expect("effect-block plan parses"),
        circuit: IrSource::load(circuit_bytes.as_slice()).expect("source ZKIR parses"),
        range_checks: range_check_count(&circuit_bytes),
    }
}

fn state(plan: &Plan) -> ChargedState<Db> {
    create_state(
        plan,
        &BTreeMap::from([
            ("left".to_owned(), json!("11")),
            ("right".to_owned(), json!("22")),
            ("selected".to_owned(), json!("0")),
            ("nested".to_owned(), json!("0")),
            ("final".to_owned(), json!("0")),
        ]),
    )
    .expect("source state creates native ledger state")
}

fn cell(state: &ChargedState<Db>, slot: usize) -> String {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Cell(cell) = &*array.get(slot).expect("cell slot exists") else {
        panic!("expected state cell")
    };
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    field_decimal(fields[0])
}

fn inputs(choose: bool, wide: u64) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("choose".to_owned(), json!(choose)),
        ("wide".to_owned(), json!(wide.to_string())),
    ])
}

fn execute(
    plan: &Plan,
    choose: bool,
    wide: u64,
    initial: &ChargedState<Db>,
) -> noctium_runtime::Execution {
    prepare(
        plan,
        &inputs(choose, wide),
        initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .expect("source effects materialize against native state")
}

#[test]
fn nested_effect_blocks_bind_branch_locals_and_preserve_order() {
    let generated_root = env::var_os(ARTIFACTS_ENV).map(PathBuf::from);
    let fixtures = match generated_root.as_deref() {
        Some(root) => {
            let default = fixture(Some(&root.join("default")));
            let dedup = fixture(Some(&root.join("dedup")));
            assert_eq!(
                default.range_checks, dedup.range_checks,
                "both pinned 3.2.1 build modes deduplicate range checks"
            );
            vec![default, dedup]
        }
        None => vec![fixture(None)],
    };

    for fixture in fixtures {
        let Fixture { plan, circuit, .. } = fixture;
        let initial = state(&plan);

        let then_branch = execute(&plan, true, 3, &initial);
        assert_eq!(cell(&then_branch.after.state, 2), "11");
        assert_eq!(cell(&then_branch.after.state, 3), "31");
        assert_eq!(cell(&then_branch.after.state, 4), "11");
        assert_eq!(
            check(&then_branch, &circuit).unwrap(),
            then_branch.activity_schedule
        );

        let nested_else = execute(&plan, true, 2, &initial);
        assert_eq!(cell(&nested_else.after.state, 2), "11");
        assert_eq!(cell(&nested_else.after.state, 3), "32");
        assert_eq!(cell(&nested_else.after.state, 4), "11");
        assert!(check(&nested_else, &circuit).is_ok());

        // The nested narrowing cast is out of range. Its parent branch is inactive,
        // so preparation skips it and the selected else arm still runs.
        let else_branch = execute(&plan, false, 8, &initial);
        assert_eq!(cell(&else_branch.after.state, 2), "22");
        assert_eq!(cell(&else_branch.after.state, 3), "42");
        assert_eq!(cell(&else_branch.after.state, 4), "22");
        assert_eq!(
            check(&else_branch, &circuit).unwrap(),
            else_branch.activity_schedule
        );

        assert!(
            prepare(
                &plan,
                &inputs(true, 8),
                &initial,
                &ledger::structure::INITIAL_PARAMETERS,
                coin_structure::contract::ContractAddress::default(),
            )
            .is_err()
        );

        let mut altered_guard = plan.clone();
        let Some(Instruction::Guarded { guard, .. }) = altered_guard
            .operations
            .iter_mut()
            .find(|operation| matches!(operation, Instruction::Guarded { .. }))
        else {
            panic!("branch Impact operation is guarded")
        };
        *guard = Expr::Bool { value: false };
        let mismatched = prepare(
            &altered_guard,
            &inputs(true, 3),
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        );
        if let Ok(mismatched) = mismatched {
            assert!(check(&mismatched, &circuit).is_err());
        }

        let mut altered_transcript = execute(&plan, true, 3, &initial);
        let last = altered_transcript
            .preimage
            .public_transcript_inputs
            .last_mut()
            .expect("active branch reads bind transcript fields");
        *last = Fr::from(9999u64);
        assert!(check(&altered_transcript, &circuit).is_err());
    }
}
