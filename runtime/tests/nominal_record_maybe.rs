#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};

#[test]
#[ignore = "requires fresh NominalRecordMaybe Ledger 9 / ZKIR 3.2.1 artifacts"]
fn nominal_record_head_checks_present_and_absent_payloads() -> Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_NOMINAL_RECORD_MAYBE_DIR")?);
    let load = |entry: &str| -> Result<(Plan, IrSource)> {
        let name = format!("NominalRecordMaybeFixture.NominalRecordMaybe.{entry}");
        let plan = serde_json::from_reader(File::open(
            directory.join(format!("{name}.impact.json")),
        )?)?;
        let circuit = IrSource::load(File::open(directory.join(format!("{name}.zkir")))?)?;
        Ok((plan, circuit))
    };
    let (mut plan, circuit) = load("inspect")?;
    let [view] = plan.return_views.as_slice() else {
        anyhow::bail!("expected one optional record return view");
    };
    let identities: Vec<_> = view
        .nominal_uint_fields
        .iter()
        .map(|field| (field.path.join("."), field.name.as_str(), field.maximum.as_str()))
        .collect();
    assert_eq!(
        identities,
        [
            ("value.amount".into(), "NominalRecordMaybeFixture.Amount", "255"),
            ("value.count".into(), "NominalRecordMaybeFixture.Count", "255"),
        ]
    );
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();
    let empty = create_state(&plan, &BTreeMap::from([("history".into(), json!([]))]))?;
    let (remember, remember_circuit) = load("remember")?;
    let inserted = prepare(
        &remember,
        &BTreeMap::from([("amount".into(), json!("19")), ("count".into(), json!("7"))]),
        &empty,
        parameters,
        address,
    )?;
    check(&inserted, &remember_circuit)?;
    for (state, present, amount, count) in [
        (&empty, false, "0", "0"),
        (&inserted.after.state, true, "19", "7"),
    ] {
        let execution = prepare(&plan, &BTreeMap::new(), state, parameters, address)?;
        check(&execution, &circuit)?;
        let returns = execution.returns_json();
        let fields = &returns["latestPosition"]["fields"];
        assert_eq!(fields[0]["value"], json!({"kind":"bool", "value":present}));
        assert_eq!(
            fields[1]["value"]["fields"],
            json!([
                {"name":"amount", "value":{"kind":"uint", "maximum":"255", "value":amount}},
                {"name":"count", "value":{"kind":"uint", "maximum":"255", "value":count}},
                {"name":"active", "value":{"kind":"bool", "value":present}},
            ])
        );
        assert_eq!(&execution.after.state, state);
    }
    plan.return_views[0].nominal_uint_fields[0].maximum = "254".into();
    assert!(prepare(&plan, &BTreeMap::new(), &empty, parameters, address).is_err());
    Ok(())
}
