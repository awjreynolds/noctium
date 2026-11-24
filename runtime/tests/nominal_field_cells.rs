#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, construct_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};

#[test]
#[ignore = "requires fresh NominalFieldCells artifacts in NOCTIUM_NOMINAL_FIELD_CELLS_DIR"]
fn nominal_field_cell_returns_preserve_native_values() -> anyhow::Result<()> {
    let directory = PathBuf::from(std::env::var_os("NOCTIUM_NOMINAL_FIELD_CELLS_DIR").unwrap());
    let stem = "NominalFieldCells.Account.update";
    let plan: Plan =
        serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?;
    let relation = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;
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
            BTreeMap::from([
                ("balanceAfter".into(), json!(expected)),
                ("capAfter".into(), json!("77")),
            ])
        );
        assert_eq!(
            execution.after.state.get_ref() == initial.get_ref(),
            !enabled
        );
    }
    Ok(())
}
