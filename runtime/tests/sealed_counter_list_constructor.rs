#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, construct_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_SEALED_ADT_CONSTRUCTOR_DIR"]
fn seeded_sealed_counter_and_list_match_the_compact_read() -> anyhow::Result<()> {
    let dir = PathBuf::from(
        std::env::var_os("NOCTIUM_SEALED_ADT_CONSTRUCTOR_DIR")
            .expect("NOCTIUM_SEALED_ADT_CONSTRUCTOR_DIR"),
    );
    let plan: Plan = serde_json::from_reader(File::open(
        dir.join("SealedCounterListConstructor.inspect.impact.json"),
    )?)?;
    let relation = IrSource::load(File::open(
        dir.join("SealedCounterListConstructor.inspect.zkir"),
    )?)?;
    let args = |amount| {
        BTreeMap::from([
            ("amount".into(), json!(amount)),
            ("first".into(), json!("17")),
        ])
    };
    let before = construct_state(&plan, &args("5"))?;
    let read = prepare(
        &plan,
        &BTreeMap::new(),
        &before,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&read, &relation)?, read.activity_schedule);
    assert_eq!(
        read.returns_json(),
        BTreeMap::from([
            ("amountRead".into(), json!("70005")),
            ("lengthRead".into(), json!("2")),
            ("headRead".into(), json!("42")),
        ])
    );
    assert_eq!(read.after.state.get_ref(), before.get_ref());
    assert!(construct_state(&plan, &args("65536")).is_err());
    Ok(())
}
