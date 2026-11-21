#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_FLAT_RECORD_CELL_DIR"]
fn reset_flat_record_cell_preserves_the_adjacent_slot_and_inactive_state() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_FLAT_RECORD_CELL_DIR").expect("NOCTIUM_FLAT_RECORD_CELL_DIR"),
    );
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("FlatRecordCellReset.guardedClear.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("FlatRecordCellReset.guardedClear.zkir"),
    )?)?;
    let state = |issued: &str, spent: &str| {
        create_state(
            &plan,
            &BTreeMap::from([
                ("marker".into(), json!("37")),
                (
                    "ledger".into(),
                    json!({
                        "kind":"struct",
                        "id":"FlatRecordCellReset.Ledger",
                        "fields":[
                            {"name":"issued","value":{"kind":"native","value":issued}},
                            {"name":"spent","value":{"kind":"native","value":spent}}
                        ]
                    }),
                ),
            ]),
        )
    };
    let original = state("5", "42")?;
    let cleared = state("0", "0")?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();
    let inputs = |enabled| BTreeMap::from([("enabled".into(), json!(enabled))]);

    for (enabled, expected) in [(false, &original), (true, &cleared)] {
        let execution = prepare(&plan, &inputs(enabled), &original, parameters, address)?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        assert_eq!(execution.after.state.get_ref(), expected.get_ref());
    }

    let mut sealed = plan.clone();
    sealed.state[1].sealed = true;
    let error = prepare(&sealed, &inputs(true), &original, parameters, address)
        .err()
        .expect("reset must reject a sealed record Cell");
    assert!(error.to_string().contains("record Cell is sealed"));

    let mut different_schema = plan.clone();
    different_schema.state[1].kind["tree"]["composite"]["counts"]["leaves"] = json!(3);
    let error = prepare(
        &different_schema,
        &inputs(true),
        &original,
        parameters,
        address,
    )
    .err()
    .expect("reset must reject a different state schema");
    assert!(
        error
            .to_string()
            .contains("record Cell write differs from state schema")
    );
    Ok(())
}
