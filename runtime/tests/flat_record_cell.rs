#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Plan, Value, check, constructor::construct_state, create_state, prepare, zkir::IrSource,
};
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

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_TYPED_RECORD_CELL_DIR"]
fn typed_record_cell_defaults_round_trip_and_reset() -> anyhow::Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_TYPED_RECORD_CELL_DIR")?);
    let load = |entry: &str| -> anyhow::Result<(Plan, IrSource)> {
        let stem = format!("TypedRecordCell.{entry}");
        Ok((
            serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?,
            IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?,
        ))
    };
    let (read, read_relation) = load("inspectMemo")?;
    let (write, write_relation) = load("storeMemo")?;
    let (reset, reset_relation) = load("clearMemo")?;
    let no_inputs = BTreeMap::new();
    let initial = construct_state(&read, &no_inputs)?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();
    let mut inputs = BTreeMap::from([
        ("active".into(), json!(true)),
        ("amount".into(), json!("513")),
    ]);
    let populated = prepare(&write, &inputs, &initial, parameters, address)?;
    check(&populated, &write_relation)?;

    let expected = |active: bool, amount: u16| {
        [
            Value::Bool(active).public_json(),
            Value::UInt {
                number: amount.into(),
                maximum: u16::MAX.into(),
            }
            .public_json(),
        ]
    };
    for (state, active, amount) in [(&initial, false, 0), (&populated.after.state, true, 513)] {
        let result = prepare(&read, &no_inputs, state, parameters, address)?;
        check(&result, &read_relation)?;
        let values = result.returns_json();
        assert_eq!(
            [&values["activeResult"], &values["amountResult"]],
            expected(active, amount).each_ref()
        );
        assert_eq!(result.after.state.get_ref(), state.get_ref());
    }

    let cleared = prepare(
        &reset,
        &no_inputs,
        &populated.after.state,
        parameters,
        address,
    )?;
    check(&cleared, &reset_relation)?;
    let values = cleared.returns_json();
    assert_eq!(
        [&values["activeAfterReset"], &values["amountAfterReset"]],
        expected(false, 0).each_ref()
    );
    assert_eq!(cleared.after.state.get_ref(), initial.get_ref());

    inputs.insert("amount".into(), json!("65536"));
    assert!(prepare(&write, &inputs, &initial, parameters, address).is_err());
    Ok(())
}
