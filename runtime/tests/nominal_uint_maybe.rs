#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, Value, check, create_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs, path::PathBuf};
use transient_crypto::curve::Fr;

fn return_view<'a>(plan: &'a Plan, name: &str) -> &'a noctium_runtime::ReturnView {
    plan.return_views
        .iter()
        .find(|view| view.name == name)
        .unwrap_or_else(|| panic!("missing {name} logical return view"))
}

fn view_id(plan: &Plan, name: &str) -> String {
    return_view(plan, name)
        .schema
        .get("layout")
        .and_then(|layout| layout.get("id"))
        .and_then(Json::as_str)
        .unwrap_or_else(|| panic!("{name} nominal return id"))
        .to_owned()
}

fn assert_nominal_uint_field(plan: &Plan, view_name: &str, identity_suffix: &str) {
    let view = return_view(plan, view_name);
    let [field] = view.nominal_uint_fields.as_slice() else {
        panic!("{view_name} must describe one nominal UInt field")
    };
    assert_eq!(field.path, ["value"]);
    assert_eq!(field.maximum, "255");
    assert_eq!(field.name.rsplit('.').next(), Some(identity_suffix));
}

fn maybe(id: &str, is_some: bool, value: &str) -> Json {
    json!({
        "kind": "struct",
        "id": id,
        "fields": [
            {"name": "is_some", "value": {"kind": "bool", "value": is_some}},
            {"name": "value", "value": {"kind": "uint", "maximum": "255", "value": value}}
        ]
    })
}

#[test]
#[ignore = "requires fresh NominalUIntMaybeNative.consume Ledger 9 / ZKIR 3.2.1 artifacts in NOCTIUM_NOMINAL_UINT_MAYBE_DIR"]
fn nominal_uint_maybe_constructors_keep_payload_identity_and_canonical_lanes() -> Result<()> {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_NOMINAL_UINT_MAYBE_DIR")
            .expect("NOCTIUM_NOMINAL_UINT_MAYBE_DIR must point to fresh compiler outputs"),
    );
    let stem = "NominalUIntMaybeFixture.NominalUIntMaybeNative.consume";
    let plan: Plan = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let circuit = IrSource::load(
        fs::read(directory.join(format!("{stem}.zkir")))?.as_slice(),
    )?;

    assert_eq!(plan.entrypoint, "consume");
    assert_eq!(plan.call_inputs, ["amount"]);
    assert_nominal_uint_field(&plan, "presentChoice", "Amount");
    assert_nominal_uint_field(&plan, "absentChoice", "Amount");
    assert_nominal_uint_field(&plan, "otherAbsent", "Other");

    let amount_id = view_id(&plan, "presentChoice");
    assert_eq!(view_id(&plan, "absentChoice"), amount_id);
    let other_id = view_id(&plan, "otherAbsent");
    assert_ne!(other_id, amount_id, "same-shaped nominal types keep distinct ABI identities");

    let state = create_state(&plan, &BTreeMap::new())?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();
    for (amount, physical_payload) in [("37", 37u64), ("0", 0u64)] {
        let execution = prepare(
            &plan,
            &BTreeMap::from([("amount".into(), json!(amount))]),
            &state,
            parameters,
            address,
        )?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);

        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([
                ("presentChoice".into(), maybe(&amount_id, true, amount)),
                ("absentChoice".into(), maybe(&amount_id, false, "0")),
                ("otherAbsent".into(), maybe(&other_id, false, "0")),
            ])
        );
        assert_eq!(
            execution
                .returns()
                .iter()
                .map(|(_, value)| value.clone())
                .collect::<Vec<_>>(),
            [1u64, physical_payload, 0, 0, 0, 0]
                .map(|value| Value::Native(Fr::from(value)))
        );
    }

    assert!(prepare(
        &plan,
        &BTreeMap::from([("amount".into(), json!("256"))]),
        &state,
        parameters,
        address,
    )
    .is_err());
    Ok(())
}
