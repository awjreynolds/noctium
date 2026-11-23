#![cfg(feature = "zkir-321")]

use anyhow::{Result, ensure};
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Execution, Plan, Value, check, create_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};
use transient_crypto::curve::Fr;

const TEXT: &str = "A\0B";
const BYTES: [u8; 4] = [0, 255, 0, 1];

fn fixture(directory: &Path, entrypoint: &str) -> Result<(Plan, IrSource)> {
    let stem = format!("OpaqueGenericCircuit.{entrypoint}");
    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(fs::read(directory.join(format!("{stem}.zkir")))?.as_slice())?;
    ensure!(
        plan.entrypoint == entrypoint,
        "wrong opaque generic circuit plan"
    );
    ensure!(
        plan.state.is_empty(),
        "opaque echo circuit should not declare state"
    );
    ensure!(plan.circuit.inputs.len() == 1, "expected one opaque input");
    ensure!(
        plan.circuit.inputs[0].name == "value",
        "expected `value` input"
    );
    ensure!(
        plan.circuit.outputs.len() == 1,
        "expected one opaque circuit output"
    );
    ensure!(
        plan.circuit.outputs[0].name == "result",
        "expected `result` circuit output"
    );
    ensure!(plan.returns.len() == 1, "expected one source return");
    ensure!(
        plan.returns[0].name == entrypoint,
        "expected the source return named {entrypoint}"
    );
    Ok((plan, circuit))
}

fn assert_typed_result(execution: &Execution, return_name: &str, expected: Value) {
    let expected_json = expected.public_json();
    assert_eq!(execution.returns().len(), 1);
    assert_eq!(execution.returns()[0].0, return_name);
    assert_eq!(execution.returns()[0].1, expected);
    assert_eq!(execution.returns()[0].1.public_json(), expected_json);
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([(return_name.into(), expected_json)]),
    );
}

fn assert_tampered_output_rejected(mut execution: Execution, circuit: &IrSource) {
    assert_eq!(execution.preimage.public_transcript_outputs.len(), 1);
    let output = &mut execution.preimage.public_transcript_outputs[0];
    *output = *output + Fr::from(1u64);
    assert!(check(&execution, circuit).is_err());
}

#[test]
#[ignore = "requires fresh OpaqueGenericCircuit artifacts in NOCTIUM_OPAQUE_GENERIC_CIRCUIT_DIR"]
fn generic_opaque_echoes_preserve_typed_values_and_bind_the_return() -> Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_OPAQUE_GENERIC_CIRCUIT_DIR")?);
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();

    let (string_plan, string_circuit) = fixture(&directory, "echoString")?;
    ensure!(
        string_plan.circuit.inputs[0].ty == "OpaqueString",
        "wrong string input type"
    );
    ensure!(
        string_plan.circuit.outputs[0].ty == "OpaqueString",
        "wrong string circuit output type"
    );
    ensure!(
        string_plan.returns[0].ty == "OpaqueString",
        "wrong string return type"
    );
    let string_state = create_state(&string_plan, &BTreeMap::new())?;
    let string_inputs =
        BTreeMap::from([("value".into(), json!({"kind":"opaqueString", "value":TEXT}))]);
    let string_execution = prepare(
        &string_plan,
        &string_inputs,
        &string_state,
        parameters,
        address,
    )?;
    assert_eq!(
        check(&string_execution, &string_circuit)?,
        string_execution.activity_schedule
    );
    assert_eq!(string_execution.after.state, string_state);
    assert_typed_result(
        &string_execution,
        "echoString",
        Value::OpaqueString(TEXT.into()),
    );
    assert_tampered_output_rejected(string_execution, &string_circuit);

    let (bytes_plan, bytes_circuit) = fixture(&directory, "echoBytes")?;
    ensure!(
        bytes_plan.circuit.inputs[0].ty == "OpaqueBytes",
        "wrong bytes input type"
    );
    ensure!(
        bytes_plan.circuit.outputs[0].ty == "OpaqueBytes",
        "wrong bytes circuit output type"
    );
    ensure!(
        bytes_plan.returns[0].ty == "OpaqueBytes",
        "wrong bytes return type"
    );
    let bytes_state = create_state(&bytes_plan, &BTreeMap::new())?;
    let bytes_inputs = BTreeMap::from([(
        "value".into(),
        json!({"kind":"opaqueBytes", "values":BYTES}),
    )]);
    let bytes_execution = prepare(
        &bytes_plan,
        &bytes_inputs,
        &bytes_state,
        parameters,
        address,
    )?;
    assert_eq!(
        check(&bytes_execution, &bytes_circuit)?,
        bytes_execution.activity_schedule
    );
    assert_eq!(bytes_execution.after.state, bytes_state);
    assert_typed_result(
        &bytes_execution,
        "echoBytes",
        Value::OpaqueBytes(BYTES.to_vec()),
    );
    assert_tampered_output_rejected(bytes_execution, &bytes_circuit);

    assert!(
        prepare(
            &string_plan,
            &BTreeMap::from([(
                "value".into(),
                Value::OpaqueBytes(BYTES.to_vec()).public_json()
            )]),
            &string_state,
            parameters,
            address,
        )
        .is_err()
    );
    assert!(
        prepare(
            &bytes_plan,
            &BTreeMap::from([(
                "value".into(),
                Value::OpaqueString(TEXT.into()).public_json()
            )]),
            &bytes_state,
            parameters,
            address,
        )
        .is_err()
    );
    Ok(())
}
