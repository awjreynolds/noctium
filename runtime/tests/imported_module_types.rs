#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, Value, check, create_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs, path::PathBuf};

fn artifact_directory() -> PathBuf {
    PathBuf::from(
        env::var_os("NOCTIUM_IMPORTED_MODULE_TYPES_DIR")
            .expect("NOCTIUM_IMPORTED_MODULE_TYPES_DIR must point to fresh compiler outputs"),
    )
}

fn check_entrypoint(
    directory: &PathBuf,
    entrypoint: &str,
    inputs: BTreeMap<String, Json>,
) -> Result<Vec<(String, Value)>> {
    let stem = format!("ImportedModuleTypes.{entrypoint}");
    let plan: Plan = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let circuit = IrSource::load(fs::read(directory.join(format!("{stem}.zkir")))?.as_slice())?;
    assert_eq!(plan.entrypoint, entrypoint);

    let initial = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    Ok(execution.returns().to_vec())
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_IMPORTED_MODULE_TYPES_DIR"]
fn imported_record_enum_and_nominal_uint_types_pass_the_native_checker() -> Result<()> {
    let directory = artifact_directory();

    let packet_returns = check_entrypoint(
        &directory,
        "inspect",
        BTreeMap::from([
            ("packet.value".into(), json!("19")),
            ("packet.valid".into(), json!("1")),
        ]),
    )?;
    assert_eq!(packet_returns, [("accepted".into(), Value::Bool(true))]);

    let flag_returns = check_entrypoint(
        &directory,
        "flagOrdinal",
        BTreeMap::from([("flag.$tag".into(), json!("1"))]),
    )?;
    assert_eq!(
        flag_returns,
        [("flagTag".into(), Value::Native(transient_crypto::curve::Fr::from(1u64)))]
    );

    let count_returns = check_entrypoint(
        &directory,
        "echoCount",
        BTreeMap::from([("count".into(), json!("7"))]),
    )?;
    assert_eq!(
        count_returns,
        [(
            "result".into(),
            Value::UInt {
                number: 7u8.into(),
                maximum: 255u16.into(),
            },
        )]
    );
    Ok(())
}
