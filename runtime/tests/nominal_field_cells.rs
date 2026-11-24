#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{Db, Plan, check, construct_state, field_value, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::json;
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

const PLAN: &str = include_str!(
    "fixtures/nominal-field-cells/321/NominalFieldCells.Account.updateWithHelper.impact.json"
);
const CIRCUIT: &[u8] = include_bytes!(
    "fixtures/nominal-field-cells/321/NominalFieldCells.Account.updateWithHelper.zkir"
);

fn cell<'a>(
    plan: &Plan,
    state: &'a ChargedState<Db>,
    name: &str,
) -> &'a base_crypto::fab::AlignedValue {
    let slot = plan.state.iter().position(|decl| decl.name == name).unwrap();
    let StateValue::Array(root) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Cell(value) = root.get(slot).unwrap() else {
        panic!("expected cell")
    };
    value
}

#[test]
fn nominal_field_cell_returns_preserve_native_values() -> anyhow::Result<()> {
    let plan: Plan = serde_json::from_str(PLAN)?;
    let relation = IrSource::load(CIRCUIT)?;
    let initial = construct_state(
        &plan,
        &BTreeMap::from([("seed".into(), json!("11")), ("rawCap".into(), json!("77"))]),
    )?;
    for (enabled, expected) in [(false, "11"), (true, "22")] {
        let inputs = BTreeMap::from([
            ("enabled".into(), json!(enabled)),
            ("next".into(), json!("9")),
            ("raw".into(), json!("13")),
            ("other".into(), json!("23")),
        ]);
        let execution = prepare(
            &plan,
            &inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )?;
        assert_eq!(check(&execution, &relation)?, execution.activity_schedule);
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([("result".into(), json!(expected))])
        );
        assert_eq!(
            cell(&plan, &execution.after.state, "balance"),
            &field_value(Fr::from(expected.parse::<u64>()?))
        );
        assert_eq!(
            cell(&plan, &execution.after.state, "cap"),
            &field_value(Fr::from(77u64))
        );
        assert_eq!(
            execution.after.state.get_ref() == initial.get_ref(),
            !enabled
        );
    }
    Ok(())
}
