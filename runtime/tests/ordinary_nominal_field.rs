#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, env, fs, path::PathBuf};

#[test]
#[ignore = "requires fresh OrdinaryNominalField artifacts in NOCTIUM_ORDINARY_NOMINAL_FIELD_DIR"]
fn attached_nominal_field_scalar_return_keeps_native_abi_and_checks() -> Result<()> {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_ORDINARY_NOMINAL_FIELD_DIR")
            .expect("NOCTIUM_ORDINARY_NOMINAL_FIELD_DIR must point at fresh compiler outputs"),
    );
    let stem = "OrdinaryNominalField.FieldContractAlias.echo";
    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(fs::read(directory.join(format!("{stem}.zkir")))?.as_slice())?;

    assert_eq!(plan.entrypoint, "echo");
    assert_eq!(plan.returns.len(), 1);
    assert_eq!(plan.returns[0].name, "returned");
    assert_eq!(plan.returns[0].ty, "Native");
    assert_eq!(plan.circuit.outputs.len(), 3);
    assert!(plan.circuit.outputs.iter().all(|output| output.ty == "Native"));

    let initial = create_state(&plan, &BTreeMap::new())?;
    let inputs = BTreeMap::from([("left".into(), json!("19")), ("right".into(), json!("23"))]);
    let execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    assert_eq!(execution.returns_json()["returned"], json!("42"));
    Ok(())
}
