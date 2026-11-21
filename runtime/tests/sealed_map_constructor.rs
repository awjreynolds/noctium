#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Expr, Instruction, Plan, check, construct_state, field_value, prepare, zkir::IrSource,
};
use onchain_runtime::state::StateValue;
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};
use transient_crypto::curve::Fr;

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_SEALED_MAP_CONSTRUCTOR_DIR"]
fn sealed_maps_allow_constructor_inserts_and_reads_but_reject_call_writes() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_SEALED_MAP_CONSTRUCTOR_DIR")
            .expect("NOCTIUM_SEALED_MAP_CONSTRUCTOR_DIR"),
    );
    let artifacts = |name: &str| -> anyhow::Result<(Plan, IrSource)> {
        let stem = format!("SealedMapConstructor.{name}");
        Ok((
            serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?,
            IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?,
        ))
    };
    let (get, get_relation) = artifacts("get")?;
    let (touch, touch_relation) = artifacts("touch")?;
    let args = BTreeMap::from([("key".into(), json!("5")), ("value".into(), json!("42"))]);
    let initial = construct_state(&get, &args)?;
    let slot = |name: &str| get.state.iter().position(|decl| decl.name == name).unwrap();
    let entries = slot("entries");
    let empty = slot("emptyEntries");
    let marker = slot("marker");
    let StateValue::Array(before) = initial.get_ref() else {
        panic!("expected root state array");
    };
    let StateValue::Map(seeded) = &*before.get(entries).unwrap() else {
        panic!("expected seeded Map");
    };
    let StateValue::Map(defaulted) = &*before.get(empty).unwrap() else {
        panic!("expected empty Map");
    };
    let key = field_value(Fr::from(5u64));
    let StateValue::Cell(value) = &*seeded.get(&key).expect("constructor key") else {
        panic!("expected scalar map value");
    };
    assert_eq!(seeded.size(), 1);
    assert_eq!(&**value, &field_value(Fr::from(42u64)));
    assert_eq!(defaulted.size(), 0);

    let mut wrong_target = get.clone();
    wrong_target.constructor.as_mut().unwrap().map_inserts[0].state = "marker".into();
    let error = construct_state(&wrong_target, &args)
        .err()
        .expect("constructor Map insert must have a Map target");
    assert!(error.to_string().contains("requires a flat scalar Map"));

    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();
    let read = prepare(
        &get,
        &BTreeMap::from([("key".into(), json!("5"))]),
        &initial,
        params,
        address,
    )?;
    assert_eq!(check(&read, &get_relation)?, read.activity_schedule);
    assert_eq!(read.returns_json().get("storedValue"), Some(&json!("42")));
    assert_eq!(read.after.state.get_ref(), initial.get_ref());

    let written = prepare(&touch, &BTreeMap::new(), &initial, params, address)?;
    assert_eq!(check(&written, &touch_relation)?, written.activity_schedule);
    let StateValue::Array(after) = written.after.state.get_ref() else {
        panic!("expected root state array");
    };
    assert_eq!(after.get(entries), before.get(entries));
    assert_eq!(after.get(empty), before.get(empty));
    let StateValue::Cell(changed) = &*after.get(marker).unwrap() else {
        panic!("expected marker Cell");
    };
    assert_eq!(&**changed, &field_value(Fr::from(37u64)));

    let push = |value: &str, storage| Instruction::Push {
        storage,
        expression: Expr::Constant {
            value: value.into(),
        },
        alignment: "field".into(),
    };
    let mut rejected = touch.clone();
    rejected.operations = vec![
        Instruction::Index {
            slot: u32::try_from(entries)?,
            push_path: true,
            key: None,
        },
        push("5", false),
        push("17", true),
        Instruction::Insert { n: 2 },
    ];
    let error = prepare(&rejected, &BTreeMap::new(), &initial, params, address)
        .err()
        .expect("an entrypoint write to a sealed Map must fail");
    assert!(error.to_string().contains("sealed state cell"), "{error:#}");
    Ok(())
}
