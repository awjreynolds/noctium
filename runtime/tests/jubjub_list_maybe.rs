#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{Expr, Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs, path::PathBuf};

const GENERATOR_X: &str =
    "28336281903124990867587793011069573392383982287722241916350956173377953689573";
const GENERATOR_Y: &str =
    "39385640392217313770878525135509063452020585410343666726093009378539878503883";

fn load(directory: &PathBuf, entry: &str) -> Result<(Plan, IrSource)> {
    let stem = format!("JubjubListMaybe.{entry}");
    Ok((
        serde_json::from_reader(fs::File::open(
            directory.join(format!("{stem}.impact.json")),
        )?)?,
        IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?,
    ))
}

fn maybe_fields(present: bool, value: Json) -> Json {
    json!([
        {"name":"is_some", "value":{"kind":"bool", "value":present}},
        {"name":"value", "value":value},
    ])
}

#[test]
#[ignore = "requires fresh JubjubListMaybe artifacts in NOCTIUM_JUBJUB_LIST_MAYBE_DIR"]
fn bare_jubjub_list_heads_return_typed_maybes() -> Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_JUBJUB_LIST_MAYBE_DIR")?);
    let (inspect, inspect_circuit) = load(&directory, "inspect")?;
    let (mut append, append_circuit) = load(&directory, "append")?;
    let address = ContractAddress::default();
    let empty = create_state(
        &inspect,
        &BTreeMap::from([("scalars".into(), json!([])), ("points".into(), json!([]))]),
    )?;

    let absent = prepare(
        &inspect,
        &BTreeMap::new(),
        &empty,
        &INITIAL_PARAMETERS,
        address,
    )?;
    check(&absent, &inspect_circuit)?;
    let absent_returns = absent.returns_json();
    assert_eq!(
        absent_returns["scalarMaybe"]["fields"],
        maybe_fields(
            false,
            json!({"kind":"jubjubScalar", "value":"0"}),
        )
    );
    assert_eq!(
        absent_returns["pointMaybe"]["fields"],
        maybe_fields(
            false,
            json!({"kind":"jubjubPoint", "x":"0", "y":"1"}),
        )
    );

    let populated = prepare(
        &append,
        &BTreeMap::from([
            ("scalar".into(), json!({"kind":"jubjubScalar", "value":"7"})),
            (
                "point".into(),
                json!({"kind":"jubjubPoint", "x":GENERATOR_X, "y":GENERATOR_Y}),
            ),
        ]),
        &empty,
        &INITIAL_PARAMETERS,
        address,
    )?;
    check(&populated, &append_circuit)?;
    let append_returns = populated.returns_json();
    assert_eq!(
        append_returns["scalarMaybe"]["fields"],
        maybe_fields(
            true,
            json!({"kind":"jubjubScalar", "value":"7"}),
        )
    );
    assert_eq!(
        append_returns["pointMaybe"]["fields"],
        maybe_fields(
            true,
            json!({"kind":"jubjubPoint", "x":GENERATOR_X, "y":GENERATOR_Y}),
        )
    );

    let present = prepare(
        &inspect,
        &BTreeMap::new(),
        &populated.after.state,
        &INITIAL_PARAMETERS,
        address,
    )?;
    check(&present, &inspect_circuit)?;
    assert_eq!(present.returns_json(), append_returns);

    let point_x = append
        .returns
        .iter_mut()
        .find(|output| output.name == "pointMaybe_value_x")
        .expect("JubjubPoint x coordinate output");
    point_x.expression = Expr::Constant { value: "0".into() };
    let point_y = append
        .returns
        .iter_mut()
        .find(|output| output.name == "pointMaybe_value_y")
        .expect("JubjubPoint y coordinate output");
    point_y.expression = Expr::Constant { value: "1".into() };
    let changed_coordinate = prepare(
        &append,
        &BTreeMap::from([
            ("scalar".into(), json!({"kind":"jubjubScalar", "value":"7"})),
            (
                "point".into(),
                json!({"kind":"jubjubPoint", "x":GENERATOR_X, "y":GENERATOR_Y}),
            ),
        ]),
        &empty,
        &INITIAL_PARAMETERS,
        address,
    )?;
    assert!(check(&changed_coordinate, &append_circuit).is_err());
    Ok(())
}
