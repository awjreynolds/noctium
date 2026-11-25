#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Db, Expr, Instruction, Plan, check, create_state, field_decimal, prepare, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::fab::AlignedValueExt;

const PLAN: &str = include_str!(
    "fixtures/generic-state/issue43-guarded-partials/321/Issue43GuardedPartialWrites.update.impact.json"
);
const CIRCUIT: &[u8] = include_bytes!(
    "fixtures/generic-state/issue43-guarded-partials/321/Issue43GuardedPartialWrites.update.zkir"
);

fn plan() -> Plan {
    serde_json::from_slice(&artifact("impact.json", PLAN.as_bytes()))
        .expect("source-generated guarded partial plan parses")
}

fn artifact(suffix: &str, committed: &[u8]) -> Vec<u8> {
    let Some(directory) = std::env::var_os("NOCTIUM_GUARDED_PARTIALS_DIR") else {
        return committed.to_vec();
    };
    let path = std::path::PathBuf::from(directory)
        .join(format!("Issue43GuardedPartialWrites.update.{suffix}"));
    std::fs::read(path).expect("read freshly compiled guarded partial artifact")
}

fn enabled_guarded_operation(instruction: &Instruction) -> &Instruction {
    let Instruction::Guarded { guard, operation } = instruction else {
        panic!("scalar plan operation is guarded")
    };
    assert_eq!(
        guard,
        &Expr::Reference {
            name: "enabled".to_owned()
        }
    );
    operation
}

#[test]
fn guarded_scalar_plan_decodes_order_guards_and_partial_operands() {
    let plan = plan();
    assert_eq!(plan.entrypoint, "update");
    assert_eq!(
        plan.state
            .iter()
            .map(|declaration| declaration.name.as_str())
            .collect::<Vec<_>>(),
        vec!["underflowed", "narrowed", "asserted", "shadowed", "valid"]
    );
    assert_eq!(plan.operations.len(), 15);

    for (slot, operations) in plan.operations.chunks_exact(3).enumerate() {
        let Instruction::Push {
            storage: false,
            expression: Expr::Constant { value },
            alignment,
        } = enabled_guarded_operation(&operations[0])
        else {
            panic!("each scalar write starts with its ordered Cell slot")
        };
        assert_eq!(value, &slot.to_string());
        assert_eq!(alignment, "field");

        let Instruction::Push {
            storage: true,
            expression,
            alignment,
        } = enabled_guarded_operation(&operations[1])
        else {
            panic!("each scalar write stores its value after the Cell slot")
        };
        assert_eq!(alignment, "field");
        if slot == 0 {
            let Expr::Cast { ty, value } = expression else {
                panic!("the value stored in the first Cell is widened to Native");
            };
            assert_eq!(ty, "Native");
            assert!(matches!(value.as_ref(), Expr::Let { body, .. }
                if matches!(body.as_ref(), Expr::Usub { maximum, .. } if maximum == "255")));
        }

        assert!(matches!(
            enabled_guarded_operation(&operations[2]),
            Instruction::Insert { n: 1 }
        ));
    }
}

fn state(plan: &Plan) -> ChargedState<Db> {
    create_state(
        plan,
        &BTreeMap::from([
            ("underflowed".to_owned(), json!("0")),
            ("narrowed".to_owned(), json!("0")),
            ("asserted".to_owned(), json!("0")),
            ("shadowed".to_owned(), json!("0")),
            ("valid".to_owned(), json!("0")),
        ]),
    )
    .expect("source cells create native ledger state")
}

fn inputs(
    enabled: bool,
    check_enabled: bool,
    left: u64,
    right: u64,
    wide: u64,
    approved: bool,
) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("enabled".to_owned(), json!(enabled)),
        ("checkEnabled".to_owned(), json!(check_enabled)),
        ("left".to_owned(), json!(left.to_string())),
        ("right".to_owned(), json!(right.to_string())),
        ("wide".to_owned(), json!(wide.to_string())),
        ("approved".to_owned(), json!(approved)),
    ])
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

fn prepare_case(
    plan: &Plan,
    initial: &ChargedState<Db>,
    values: BTreeMap<String, Json>,
) -> anyhow::Result<noctium_runtime::Execution> {
    prepare(
        plan,
        &values,
        initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
}

#[test]
fn guarded_partial_scalar_expressions_are_safe_and_keep_active_semantics() {
    let plan = plan();
    let circuit = IrSource::load(artifact("zkir", CIRCUIT).as_slice()).expect("source ZKIR parses");
    let initial = state(&plan);

    let inactive = prepare_case(&plan, &initial, inputs(false, false, 1, 2, 8, false))
        .expect("inactive underflow, narrowing, assertions, and shadowing are totalized");
    assert!(inactive.program.is_empty());
    assert!(check(&inactive, &circuit).is_ok());

    assert!(prepare_case(&plan, &initial, inputs(true, false, 1, 2, 3, true)).is_err());
    assert!(prepare_case(&plan, &initial, inputs(true, false, 3, 2, 8, true)).is_err());
    assert!(prepare_case(&plan, &initial, inputs(true, false, 3, 2, 3, false)).is_err());

    let active_require = prepare_case(&plan, &initial, inputs(false, true, 1, 2, 8, false))
        .expect("prepare skips inactive writes and defers the relation requirement to ZKIR");
    assert!(check(&active_require, &circuit).is_err());

    let active = prepare_case(&plan, &initial, inputs(true, true, 3, 2, 3, true))
        .expect("active partial expressions with valid operands preserve source behavior");
    assert!(check(&active, &circuit).is_ok());
    assert_eq!(cell(&active.after.state, 0), "1");
    assert_eq!(cell(&active.after.state, 1), "3");
    assert_eq!(cell(&active.after.state, 2), "7");
    assert_eq!(cell(&active.after.state, 3), "1");
    assert_eq!(cell(&active.after.state, 4), "3");
}
