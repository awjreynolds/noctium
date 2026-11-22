#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, fs, path::PathBuf};

#[test]
#[ignore = "requires fresh compiler outputs in NOCTIUM_FIXED_NUMERIC_BYTES_DIR"]
fn numeric_bytes_accept_exact_fits_and_reject_overflow() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_FIXED_NUMERIC_BYTES_DIR")
            .expect("NOCTIUM_FIXED_NUMERIC_BYTES_DIR"),
    );
    let boundary = num_bigint::BigUint::from(1u8) << 248u32;
    let maximum = (&boundary - 1u8).to_string();
    let overflow = boundary.to_string();
    for (entry, value, width, overflow) in [
        ("FixedNumericBytes.fieldOne", "255", 1, Some("256")),
        ("ReadableFixedNumericBytes.uintOne", "255", 1, Some("256")),
        (
            "FixedNumericBytes.field31",
            maximum.as_str(),
            31,
            Some(overflow.as_str()),
        ),
        ("FixedNumericBytes.fieldWide", "513", 32, None),
    ] {
        let plan: Plan =
            serde_json::from_slice(&fs::read(directory.join(format!("{entry}.impact.json")))?)?;
        let relation = IrSource::load(fs::File::open(directory.join(format!("{entry}.zkir")))?)?;
        let initial = create_state(&plan, &BTreeMap::new())?;
        let execute = |value| {
            prepare(
                &plan,
                &BTreeMap::from([("value".into(), json!(value))]),
                &initial,
                &ledger::structure::INITIAL_PARAMETERS,
                ContractAddress::default(),
            )
        };
        let execution = execute(value)?;
        assert_eq!(check(&execution, &relation)?, execution.activity_schedule);
        let returns = execution.returns_json();
        if let Some(overflow) = overflow {
            assert_eq!(
                returns["encoded"],
                json!({"kind":"bytes","values":vec![255u8; width]})
            );
            if let Ok(overflow) = execute(overflow) {
                assert!(
                    check(&overflow, &relation).is_err(),
                    "{entry} accepted overflow"
                );
            }
        } else {
            for (label, width) in [("word", 32), ("padded33", 33), ("padded64", 64)] {
                let mut bytes = vec![0u8; width];
                bytes[..2].copy_from_slice(&[1, 2]);
                assert_eq!(returns[label], json!({"kind":"bytes","values":bytes}));
            }
        }
    }
    Ok(())
}
