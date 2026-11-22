#![cfg(feature = "zkir-321")]

use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};

#[test]
#[ignore = "requires fresh compiler outputs in NOCTIUM_NESTED_TRANSIENT_HASH_DIR"]
fn nested_transient_hash_matches_compact_and_native_relation() -> anyhow::Result<()> {
    let directory = std::env::var_os("NOCTIUM_NESTED_TRANSIENT_HASH_DIR")
        .map(PathBuf::from)
        .expect("NOCTIUM_NESTED_TRANSIENT_HASH_DIR");
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("NestedTransientHash.digest.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("NestedTransientHash.digest.zkir"),
    )?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let mut inputs = BTreeMap::from([
        ("head".into(), json!("11")),
        ("tag".into(), json!({"kind":"bytes", "values":[18, 52]})),
        ("enabled".into(), json!(true)),
        ("amount".into(), json!("513")),
        ("pairHead".into(), json!("31")),
        ("tail".into(), json!("99")),
    ]);

    for (first, second, expected) in [
        (
            "41",
            "42",
            "15768837897521911811722696040654606308073209539648838630070805017733391969083",
        ),
        (
            "42",
            "41",
            "16758168218473546073028353208286085426324112504107359563775906790860030679182",
        ),
    ] {
        inputs.insert("firstItem".into(), json!(first));
        inputs.insert("secondItem".into(), json!(second));
        let execution = prepare(&plan, &inputs, &initial, parameters, address)?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        let returns = execution.returns_json();
        assert_eq!(returns.get("digest"), Some(&json!(expected)));
        assert_eq!(returns.get("emptyDigest"), Some(&json!("0")));
    }
    Ok(())
}
