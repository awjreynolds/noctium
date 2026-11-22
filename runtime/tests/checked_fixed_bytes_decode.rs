#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{MODULUS, Plan, check, create_state, prepare, zkir::IrSource};
use num_bigint::BigUint;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs, path::PathBuf};

const STEM: &str = "CheckedFixedBytesDecode.decode";

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn little_endian(value: &BigUint, width: usize) -> Vec<u8> {
    let mut bytes = value.to_bytes_le();
    assert!(
        bytes.len() <= width,
        "value does not fit requested byte width"
    );
    bytes.resize(width, 0);
    bytes
}

fn execute(
    plan: &Plan,
    circuit: &IrSource,
    native: &[u8],
    uint: [u8; 3],
) -> Result<noctium_runtime::Execution> {
    let supplied = BTreeMap::from([
        ("nativeBytes".into(), bytes(native)),
        ("uintBytes".into(), bytes(&uint)),
    ]);
    let initial = create_state(plan, &BTreeMap::new())?;
    let execution = prepare(
        plan,
        &supplied,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, circuit)?, execution.activity_schedule);
    Ok(execution)
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_CHECKED_FIXED_BYTES_DECODE_DIR"]
fn checked_fixed_bytes_decode_enforces_native_and_uint_boundaries() -> Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_CHECKED_FIXED_BYTES_DECODE_DIR")
            .expect("NOCTIUM_CHECKED_FIXED_BYTES_DECODE_DIR"),
    );
    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{STEM}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{STEM}.zkir")))?)?;
    let modulus = BigUint::parse_bytes(MODULUS.as_bytes(), 10).expect("valid field modulus");
    let native_maximum = &modulus - BigUint::from(1u8);

    let valid = execute(
        &plan,
        &circuit,
        &[little_endian(&native_maximum, 32), vec![0]].concat(),
        [255, 255, 0],
    )?;
    let returns = valid.returns_json();
    assert_eq!(
        returns.get("nativeValue"),
        Some(&json!(native_maximum.to_str_radix(10)))
    );
    assert_eq!(returns.get("uintValue"), Some(&json!("65535")));

    let noncanonical = little_endian(&modulus, 32);
    assert!(
        execute(
            &plan,
            &circuit,
            &[noncanonical, vec![0]].concat(),
            [0, 0, 0]
        )
        .is_err()
    );

    let nonzero_tail = [&little_endian(&BigUint::from(513u16), 32)[..], &[1][..]].concat();
    assert!(execute(&plan, &circuit, &nonzero_tail, [0, 0, 0]).is_err());

    assert!(
        execute(
            &plan,
            &circuit,
            &[little_endian(&native_maximum, 32), vec![0]].concat(),
            [0, 0, 1],
        )
        .is_err()
    );
    Ok(())
}
