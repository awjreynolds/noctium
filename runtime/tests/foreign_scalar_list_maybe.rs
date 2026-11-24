#![cfg(feature = "zkir-321")]

use anyhow::{Context, Result};
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::foreign::{ForeignFamily, ForeignRole, ForeignType, ForeignValue};
use noctium_runtime::{check, create_state, prepare, zkir::IrSource, Plan, Value};
use serde_json::{json, Value as Json};
use std::{collections::BTreeMap, fs, path::PathBuf};

fn scalar(number: u8) -> Json {
    let ty = ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Scalar);
    let mut bytes = [0; 32];
    bytes[0] = number;
    Value::Foreign(ForeignValue::from_bytes(ty, &bytes).unwrap()).public_json()
}

fn maybe_fields(present: bool, value: Json) -> Json {
    json!([
        {"name":"is_some", "value":{"kind":"bool", "value":present}},
        {"name":"value", "value":value},
    ])
}

fn load(directory: &PathBuf, entry: &str) -> Result<(Plan, IrSource)> {
    let stem = format!("ForeignScalarListMaybe.{entry}");
    Ok((
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?,
        IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?,
    ))
}

#[test]
#[ignore = "requires fresh ForeignScalarListMaybe artifacts in NOCTIUM_FOREIGN_SCALAR_LIST_MAYBE_DIR"]
fn secp256k1_scalar_list_head_returns_a_checked_typed_maybe() -> Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_FOREIGN_SCALAR_LIST_MAYBE_DIR")?);
    let (head, head_circuit) = load(&directory, "head")?;
    let (push, push_circuit) = load(&directory, "push")?;
    let (pop, pop_circuit) = load(&directory, "pop")?;
    let empty = create_state(&head, &BTreeMap::from([("values".into(), json!([]))]))?;
    let address = ContractAddress::default();

    let absent = prepare(
        &head,
        &BTreeMap::new(),
        &empty,
        &INITIAL_PARAMETERS,
        address,
    )?;
    check(&absent, &head_circuit).context("checking absent scalar List head")?;
    assert_eq!(
        absent.returns_json()["maybeHead"]["fields"],
        maybe_fields(false, scalar(0)),
    );

    let pushed = prepare(
        &push,
        &BTreeMap::from([("value".into(), scalar(7))]),
        &empty,
        &INITIAL_PARAMETERS,
        address,
    )?;
    check(&pushed, &push_circuit).context("checking scalar List push")?;
    let present = prepare(
        &head,
        &BTreeMap::new(),
        &pushed.after.state,
        &INITIAL_PARAMETERS,
        address,
    )?;
    check(&present, &head_circuit).context("checking present scalar List head")?;
    assert_eq!(
        present.returns_json()["maybeHead"]["fields"],
        maybe_fields(true, scalar(7)),
    );

    let mut changed_head = head.clone();
    let low_limb = changed_head
        .returns
        .iter_mut()
        .find(|output| output.name == "maybeHead_value_low")
        .expect("foreign scalar low-limb output");
    low_limb.expression = noctium_runtime::Expr::Constant { value: "0".into() };
    let changed_binding = prepare(
        &changed_head,
        &BTreeMap::new(),
        &pushed.after.state,
        &INITIAL_PARAMETERS,
        address,
    )?;
    assert!(check(&changed_binding, &head_circuit).is_err());

    let removed = prepare(
        &pop,
        &BTreeMap::new(),
        &pushed.after.state,
        &INITIAL_PARAMETERS,
        address,
    )?;
    check(&removed, &pop_circuit).context("checking scalar List pop")?;
    let after_pop = prepare(
        &head,
        &BTreeMap::new(),
        &removed.after.state,
        &INITIAL_PARAMETERS,
        address,
    )?;
    check(&after_pop, &head_circuit).context("checking absent head after scalar List pop")?;
    assert_eq!(
        after_pop.returns_json()["maybeHead"]["fields"],
        maybe_fields(false, scalar(0)),
    );

    Ok(())
}
