mod common;
use noctium_runtime::{
    Expr, Plan, ScalarType, Value, canonical_field, canonical_unsigned, create_state, environment,
    evaluate, max_uint,
};
use num_bigint::BigUint;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;

fn eval(tree: Json) -> anyhow::Result<Value> {
    evaluate(&serde_json::from_value::<Expr>(tree)?, &BTreeMap::new())
}
fn uint(maximum: &str, value: &str) -> Json {
    json!({"tag":"uint","maximum":maximum,"value":value})
}
fn cast(ty: &str, value: Json) -> Json {
    json!({"tag":"cast","type":ty,"value":value})
}
fn plan(ty: &str) -> Plan {
    let value = serde_json::from_value(json!({
        "schemaVersion":1,"entrypoint":"unsigned",
        "circuit":{"inputs":[{"name":"value","type":ty,"visibility":"private"}],"outputs":[]},
        "state":[],"operations":[],"reads":[]
    }))
    .unwrap();
    common::selected(value)
}

#[test]
fn unsigned_type_and_decimal_boundaries() {
    let max = max_uint();
    let largest = format!("UIntRange<{}>", &max + 1u8);
    assert_eq!(
        ScalarType::parse(&largest).unwrap(),
        ScalarType::UInt(max.clone())
    );
    assert!(ScalarType::parse(&format!("UIntRange<{}>", &max + 2u8)).is_err());
    assert!(canonical_unsigned(&max.to_string(), &max).is_ok());
    assert!(canonical_unsigned(&(&max + 1u8).to_string(), &max).is_err());
    assert!(canonical_unsigned("0", &BigUint::from(0u8)).is_ok());
    assert!(canonical_unsigned("1", &BigUint::from(0u8)).is_err());
    for malformed in ["", "00", "01", "-1", "+1", " 1", "1.0", "1e1", "١"] {
        assert!(canonical_unsigned(malformed, &max).is_err());
    }
    assert!(canonical_unsigned(&"9".repeat(10_000), &max).is_err());
    for malformed in [
        "UIntRange<0>",
        "UIntRange<01>",
        "UIntRange<+2>",
        "UIntRange<2> ",
        "UIntRange<-1>",
        "UIntRange<2.0>",
        "UIntRange<>",
        "UInt<8>",
    ] {
        assert!(ScalarType::parse(malformed).is_err());
    }
}

#[test]
fn unsigned_arithmetic_obeys_inferred_type_ranges() {
    for (tag, maximum, value) in [
        ("uadd", "510", "510"),
        ("umul", "65025", "65025"),
        ("usub", "255", "0"),
    ] {
        let result = eval(
            json!({"tag":tag,"maximum":maximum,"left":uint("255","255"),"right":uint("255","255")}),
        )
        .unwrap();
        assert_eq!(result.public_json(), json!(value));
        assert_eq!(
            result.scalar_type(),
            ScalarType::UInt(maximum.parse().unwrap())
        );
    }
    assert!(
        eval(json!({"tag":"uadd","maximum":"511","left":uint("255","0"),"right":uint("255","0")}))
            .is_err()
    );
    assert!(
        eval(json!({"tag":"usub","maximum":"255","left":uint("255","3"),"right":uint("255","5")}))
            .is_err()
    );
    let max = max_uint().to_string();
    assert!(
        eval(json!({"tag":"uadd","maximum":max,"left":uint(&max,"0"),"right":uint("1","0")}))
            .is_err()
    );
    assert!(
        eval(json!({"tag":"umul","maximum":max,"left":uint(&max,"0"),"right":uint("2","0")}))
            .is_err()
    );
    assert!(eval(json!({"tag":"uadd","maximum":"1","left":{"tag":"bool","value":true},"right":uint("0","0")})).is_err());
    assert!(
        eval(json!({"tag":"add","left":uint("255","1"),"right":{"tag":"constant","value":"1"}}))
            .is_err()
    );
    assert!(eval(uint("255", "256")).is_err());
}

#[test]
fn checked_scalar_conversions_match_policy() {
    for value in ["0", "1", "2", "255"] {
        assert_eq!(
            eval(cast("Bool", uint("255", value))).unwrap(),
            Value::Bool(value != "0")
        );
    }
    assert_eq!(
        eval(cast("Bool", json!({"tag":"constant","value":"256"}))).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval(cast(
            "UIntRange<256>",
            json!({"tag":"constant","value":"255"})
        ))
        .unwrap()
        .public_json(),
        json!("255")
    );
    assert!(
        eval(cast(
            "UIntRange<256>",
            json!({"tag":"constant","value":"256"})
        ))
        .is_err()
    );
    assert!(eval(cast("UIntRange<1>", json!({"tag":"bool","value":true}))).is_err());
    assert_eq!(
        eval(cast("UIntRange<1>", json!({"tag":"bool","value":false})))
            .unwrap()
            .public_json(),
        json!("0")
    );
    assert_eq!(
        eval(cast("Native", uint("255", "255"))).unwrap(),
        Value::Native(canonical_field("255").unwrap())
    );
    assert!(eval(cast("UIntRange<16>", uint("255", "16"))).is_err());
    assert_eq!(
        eval(cast("UIntRange<256>", uint("15", "15")))
            .unwrap()
            .scalar_type(),
        ScalarType::UInt(255u32.into())
    );
    assert_eq!(eval(json!({"tag":"sub","left":{"tag":"constant","value":"0"},"right":{"tag":"constant","value":"1"}})).unwrap().public_json(),json!("52435875175126190479447740508185965837690552500527637822603658699938581184512"));
}

#[test]
fn unsigned_input_output_and_storage_types_are_exact() {
    let mut p = plan("UIntRange<256>");
    for bad in [
        json!(256),
        json!(true),
        json!("256"),
        json!("0255"),
        json!("-1"),
    ] {
        assert!(environment(&p, &BTreeMap::from([("value".into(), bad)])).is_err());
    }
    let inputs = BTreeMap::from([("value".into(), json!("255"))]);
    assert!(environment(&p, &inputs).is_ok());
    p.circuit.outputs.push(serde_json::from_value(json!({"visibility":"public","type":"UIntRange<16>","name":"out","expression":{"tag":"reference","name":"value"}})).unwrap());
    assert!(environment(&p, &inputs).is_err());
    p.circuit.outputs[0].ty = "UIntRange<256>".into();
    assert!(environment(&p, &inputs).is_ok());
    p.circuit.outputs[0].visibility = "private".into();
    assert!(environment(&p, &inputs).is_err());
    p.state = serde_json::from_value(json!([{"name":"amount","kind":{"cell":"UIntRange<256>"}}]))
        .unwrap();
    assert!(create_state(&p, &BTreeMap::from([("amount".into(), json!("255"))])).is_ok());
    assert!(create_state(&p, &BTreeMap::from([("amount".into(), json!("256"))])).is_err());
}

#[test]
fn unsigned_equality_and_eager_selection_reject_type_confusion() {
    assert!(eval(json!({"tag":"eq","left":uint("255","1"),"right":uint("15","1")})).is_err());
    assert!(
        eval(json!({"tag":"eq","left":uint("255","1"),"right":{"tag":"constant","value":"1"}}))
            .is_err()
    );
    assert!(eval(json!({"tag":"select","condition":{"tag":"bool","value":true},"yes":uint("255","1"),"no":uint("15","1")})).is_err());
    assert!(eval(json!({"tag":"select","condition":{"tag":"bool","value":true},"yes":uint("255","1"),"no":cast("UIntRange<256>",json!({"tag":"constant","value":"256"}))})).is_err());
}

#[test]
fn source_generated_unsigned_plan_passes_official_checker() {
    let p: Plan = serde_json::from_value(common::unsigned_json()).unwrap();
    let ir = noctium_runtime::zkir::IrSource::load(
        include_bytes!("fixtures/unsigned/circuit.zkir").as_slice(),
    )
    .unwrap();
    let inputs = BTreeMap::from([
        ("left".into(), json!("255")),
        ("right".into(), json!("255")),
        ("expected".into(), json!("510")),
    ]);
    let state = create_state(&p, &BTreeMap::from([("total".into(), json!("0"))])).unwrap();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let execution = noctium_runtime::prepare(&p, &inputs, &state, params, address).unwrap();
    assert_eq!(noctium_runtime::check(&execution, &ir).unwrap().len(), 8);
    let mut wrong = inputs.clone();
    wrong.insert("expected".into(), json!("509"));
    let wrong_execution = noctium_runtime::prepare(&p, &wrong, &state, params, address).unwrap();
    assert!(noctium_runtime::check(&wrong_execution, &ir).is_err());
    let mut out_of_range = inputs.clone();
    out_of_range.insert("left".into(), json!("256"));
    assert!(noctium_runtime::prepare(&p, &out_of_range, &state, params, address).is_err());
    assert!(
        noctium_runtime::prepare(&p, &inputs, &execution.after.state, params, address)
            .and_then(|e| noctium_runtime::check(&e, &ir))
            .is_err()
    );
}

#[cfg(feature = "zkir-321")]
#[test]
#[ignore = "requires fresh BoundedUintHelper artifacts in NOCTIUM_BOUNDED_HELPER_DIR"]
fn bounded_uint_addition_crosses_the_checked_helper_boundary() -> anyhow::Result<()> {
    let directory = std::path::PathBuf::from(
        std::env::var_os("NOCTIUM_BOUNDED_HELPER_DIR").expect("NOCTIUM_BOUNDED_HELPER_DIR"),
    );
    let stem = "BoundedUintHelper.addViaHelper";
    let plan: Plan = serde_json::from_reader(std::fs::File::open(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let circuit = noctium_runtime::zkir::IrSource::load(std::fs::File::open(
        directory.join(format!("{stem}.zkir")),
    )?)?;
    assert_eq!(
        plan.circuit
            .inputs
            .iter()
            .map(|input| (input.name.as_str(), input.ty.as_str()))
            .collect::<Vec<_>>(),
        [("left", "UIntRange<256>"), ("right", "UIntRange<256>")],
    );
    let [result] = plan.returns.as_slice() else {
        panic!("expected one bounded helper result");
    };
    assert_eq!(result.name, "sum");
    assert_eq!(result.ty, "UIntRange<511>");
    let inputs = BTreeMap::from([
        ("left".into(), json!("255")),
        ("right".into(), json!("255")),
    ]);
    let state = create_state(&plan, &BTreeMap::new())?;
    let execution = noctium_runtime::prepare(
        &plan,
        &inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    noctium_runtime::check(&execution, &circuit)?;
    assert_eq!(
        execution.returns(),
        &[(
            "sum".into(),
            Value::UInt {
                number: 510u32.into(),
                maximum: 510u32.into()
            }
        )],
    );
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([("sum".into(), json!("510"))])
    );
    Ok(())
}
