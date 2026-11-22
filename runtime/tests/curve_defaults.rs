#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Plan, Value, check, create_state,
    foreign::{ForeignFamily, ForeignRole, ForeignType, ForeignValue},
    prepare,
    zkir::IrSource,
};
use serde_json::json;
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

fn checked_returns(
    directory: &Path,
    entry: &str,
) -> anyhow::Result<BTreeMap<String, serde_json::Value>> {
    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{entry}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{entry}.zkir")))?)?;
    let inputs = BTreeMap::new();
    let initial = create_state(&plan, &inputs)?;
    let execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    Ok(execution.returns_json())
}

#[test]
#[ignore = "requires fresh compiler outputs in NOCTIUM_CURVE_DEFAULTS_DIR"]
fn curve_defaults_return_canonical_zero_and_identity_values() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_CURVE_DEFAULTS_DIR").expect("NOCTIUM_CURVE_DEFAULTS_DIR"),
    );
    let returns = checked_returns(&directory, "CurveDefaults.inspect")?;
    assert_eq!(returns.len(), 11);
    assert_eq!(
        returns["jubjubScalar"],
        json!({"kind":"jubjubScalar","value":"0"})
    );
    assert_eq!(
        returns["jubjubPoint"],
        json!({"kind":"jubjubPoint","x":"0","y":"1"})
    );
    for (prefix, family) in [
        ("k1", ForeignFamily::Secp256k1),
        ("r1", ForeignFamily::Secp256r1),
        ("c25519", ForeignFamily::Curve25519),
    ] {
        for (suffix, role) in [
            ("Base", ForeignRole::Base),
            ("Scalar", ForeignRole::Scalar),
            ("Point", ForeignRole::Point),
        ] {
            let key = format!("{prefix}{suffix}");
            let expected = ForeignValue::zero(ForeignType::new(family, role))?;
            assert_eq!(returns[&key], Value::Foreign(expected).public_json());
        }
    }
    assert_eq!(
        checked_returns(&directory.join("readable"), "ReadableCurveDefaults.inspect")?,
        BTreeMap::from([("result".to_owned(), json!(true))])
    );
    Ok(())
}
