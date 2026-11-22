#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs::File, path::PathBuf};

#[test]
#[ignore = "requires fresh CheckedEnumCasts artifacts in NOCTIUM_CHECKED_ENUM_CASTS_DIR"]
fn numeric_enum_casts_match_the_compact_ordinals_and_bounds() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_CHECKED_ENUM_CASTS_DIR").expect("NOCTIUM_CHECKED_ENUM_CASTS_DIR"),
    );
    let run = |entrypoint: &str,
               inputs: &[(&str, &str)]|
     -> anyhow::Result<BTreeMap<String, Json>> {
        let stem = format!("CheckedEnumCasts.CheckedEnumCasts.{entrypoint}");
        let plan: Plan =
            serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?;
        let circuit = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;
        let initial = create_state(&plan, &BTreeMap::new())?;
        let inputs = inputs
            .iter()
            .map(|(name, value)| ((*name).into(), json!(value)))
            .collect();
        let execution = prepare(
            &plan,
            &inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        Ok(execution.returns_json())
    };

    let converted = run("convert", &[("fieldOrdinal", "0"), ("uintOrdinal", "2")])?;
    assert_eq!(converted["fromField"]["variant"], "Pending");
    assert_eq!(converted["fromUInt"]["variant"], "Done");
    assert_eq!(converted["first"]["variant"], "Pending");
    assert!(run("convert", &[("fieldOrdinal", "3"), ("uintOrdinal", "0")]).is_err());
    assert!(run("convert", &[("fieldOrdinal", "0"), ("uintOrdinal", "3")]).is_err());

    let extracted = run("extract", &[("choice.$tag", "2")])?;
    assert_eq!(extracted["fieldValue"], "2");
    assert_eq!(extracted["unsignedValue"], "2");
    assert_eq!(run("narrow", &[("choice.$tag", "1")])?["narrowValue"], "1");
    assert!(run("narrow", &[("choice.$tag", "2")]).is_err());
    Ok(())
}
