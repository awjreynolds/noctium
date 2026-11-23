#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Plan, Value, check, create_state,
    foreign::{ForeignType, ForeignValue},
    prepare,
    zkir::IrSource,
};
use std::{collections::BTreeMap, fs::File, path::PathBuf};

#[test]
#[ignore = "requires fresh module artifacts in NOCTIUM_GENERIC_FOREIGN_CURVE_MODULE_DIR"]
fn specialized_identity_stores_the_foreign_scalar_checked_by_zkir() -> anyhow::Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_GENERIC_FOREIGN_CURVE_MODULE_DIR")?);
    let stem = "ForeignCurveGenericIdentity.secp256k1ScalarIdentity";
    let plan: Plan =
        serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?;
    let relation = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;

    assert_eq!(plan.entrypoint, "secp256k1ScalarIdentity");
    assert_eq!(plan.circuit.inputs.len(), 1);
    assert_eq!(plan.circuit.inputs[0].name, "value");
    assert_eq!(plan.circuit.inputs[0].ty, "Secp256k1Scalar");
    assert_eq!(plan.circuit.outputs.len(), 1);
    assert_eq!(plan.circuit.outputs[0].name, "result");
    assert_eq!(plan.circuit.outputs[0].ty, "Secp256k1Scalar");
    assert_eq!(plan.state.len(), 1);
    let result = &plan.state[0];
    assert_eq!(result.kind["cell"], "Secp256k1Scalar");

    let ty = ForeignType::parse_source_name("Secp256k1Scalar")?;
    let zero = Value::Foreign(ForeignValue::from_bytes(ty, &[0; 32])?).public_json();
    let mut bytes = [0; 32];
    bytes[0] = 37;
    let value = Value::Foreign(ForeignValue::from_bytes(ty, &bytes)?).public_json();
    let initial = create_state(&plan, &BTreeMap::from([(result.name.clone(), zero)]))?;
    let expected = create_state(
        &plan,
        &BTreeMap::from([(result.name.clone(), value.clone())]),
    )?;
    let execution = prepare(
        &plan,
        &BTreeMap::from([("value".into(), value)]),
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &relation)?, execution.activity_schedule);
    assert_eq!(execution.after.state, expected);
    Ok(())
}
