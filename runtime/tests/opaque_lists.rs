#![cfg(feature = "zkir-321")]

use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use noctium_runtime::{check, create_state, prepare, zkir::IrSource, Db, Execution, Expr, Plan};
use onchain_runtime::{
    context::QueryContext,
    state::{ChargedState, StateValue},
};
use serde_json::{json, Value as Json};
use std::{
    collections::BTreeMap,
    fs::File,
    path::{Path, PathBuf},
};
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

fn fixture(directory: &Path, entry: &str) -> (Plan, IrSource) {
    let stem = format!("OpaqueLists.{entry}");
    let plan = serde_json::from_slice(
        &std::fs::read(directory.join(format!("{stem}.impact.json"))).unwrap(),
    )
    .unwrap();
    let circuit =
        IrSource::load(File::open(directory.join(format!("{stem}.zkir"))).unwrap()).unwrap();
    (plan, circuit)
}

fn inputs(text: &str, bytes: &[u8]) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("text".into(), json!({"kind":"opaqueString", "value":text})),
        (
            "bytes".into(),
            json!({"kind":"opaqueBytes", "values":bytes}),
        ),
    ])
}

fn compressed(bytes: &[u8]) -> AlignedValue {
    AlignedValue::new(
        FabValue(vec![ValueAtom::from(bytes)]),
        Alignment::singleton(AlignmentAtom::Compress),
    )
    .expect("canonical opaque Compress value")
}

fn assert_heads(execution: &Execution, present: [bool; 2], text: &str, bytes: &[u8]) {
    let returns = execution.returns_json();
    assert_eq!(
        returns["stringHead"],
        json!({
            "kind": "struct",
            "id": "OpaqueLists.MaybeOpaqueString",
            "fields": [
                {"name": "is_some", "value": {"kind": "bool", "value": present[0]}},
                {"name": "value", "value": {"kind": "opaqueString", "value": text}},
            ]
        })
    );
    assert_eq!(
        returns["bytesHead"],
        json!({
            "kind": "struct",
            "id": "OpaqueLists.MaybeOpaqueBytes",
            "fields": [
                {"name": "is_some", "value": {"kind": "bool", "value": present[1]}},
                {"name": "value", "value": {"kind": "opaqueBytes", "values": bytes}},
            ]
        })
    );
}

fn assert_stored(state: &ChargedState<Db>, plan: &Plan, name: &str, expected: &[u8]) {
    let StateValue::Array(root) = state.get_ref() else {
        panic!("expected native state slots");
    };
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == name)
        .expect("List state declaration");
    let StateValue::Array(node) = root.get(slot).expect("List state") else {
        panic!("expected native List node");
    };
    let StateValue::Cell(head) = node.get(0).expect("List head") else {
        panic!("expected List head cell");
    };
    assert_eq!(**head, compressed(expected));
}

#[test]
#[ignore = "requires fresh Lean artifacts and the pinned Compact oracle"]
fn opaque_lists_match_typed_heads_and_lifo_state() {
    let artifacts = PathBuf::from(
        std::env::var_os("NOCTIUM_OPAQUE_LISTS_DIR")
            .expect("set fresh OpaqueLists outputs in NOCTIUM_OPAQUE_LISTS_DIR"),
    );
    let oracle_path = std::env::var_os("NOCTIUM_OPAQUE_LISTS_COMPACT")
        .expect("set Compact output in NOCTIUM_OPAQUE_LISTS_COMPACT");
    let oracle: Json = serde_json::from_slice(&std::fs::read(oracle_path).unwrap()).unwrap();
    assert!(oracle["compact"]
        .as_str()
        .unwrap()
        .starts_with("0.36.1 (7fa3a117c"));
    assert_eq!(oracle["runtime"], "0.21.0");
    let decode = |row: &Json, key: &str, index: usize| {
        hex::decode(row[key][index].as_str().unwrap()).unwrap()
    };

    let (push, push_circuit) = fixture(&artifacts, "push");
    let (inspect, inspect_circuit) = fixture(&artifacts, "inspect");
    let (pop, pop_circuit) = fixture(&artifacts, "pop");
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let state = create_state(
        &push,
        &BTreeMap::from([
            ("strings".into(), json!([])),
            ("byteArrays".into(), json!([])),
        ]),
    )
    .expect("root opaque List states create");
    let read = |state| {
        let execution = prepare(&inspect, &BTreeMap::new(), state, parameters, address)
            .expect("opaque List heads prepare");
        check(&execution, &inspect_circuit).expect("opaque List head relation checks");
        execution
    };
    let drop_head = |state| {
        let execution = prepare(&pop, &BTreeMap::new(), state, parameters, address)
            .expect("opaque List pop prepares");
        check(&execution, &pop_circuit).expect("opaque List pop relation checks");
        execution
    };

    assert_heads(
        &read(&state),
        serde_json::from_value(oracle["initial"].clone()).unwrap(),
        "",
        &[],
    );

    let after_two_pushes = &oracle["afterTwoPushes"];
    let first_text = String::from_utf8(decode(after_two_pushes, "texts", 1)).unwrap();
    let first_bytes = decode(after_two_pushes, "blobs", 1);
    let first = prepare(
        &push,
        &inputs(&first_text, &first_bytes),
        &state,
        parameters,
        address,
    )
    .expect("first opaque List push prepares");
    check(&first, &push_circuit).expect("first opaque List push relation checks");
    let text = String::from_utf8(decode(after_two_pushes, "texts", 0)).unwrap();
    let bytes = decode(after_two_pushes, "blobs", 0);
    let mut second = prepare(
        &push,
        &inputs(&text, &bytes),
        &first.after.state,
        parameters,
        address,
    )
    .expect("second opaque List push prepares");
    check(&second, &push_circuit).expect("second opaque List push relation checks");

    let mut expected_inputs = Vec::new();
    compressed(text.as_bytes()).value_only_field_repr(&mut expected_inputs);
    compressed(&bytes).value_only_field_repr(&mut expected_inputs);
    assert_eq!(expected_inputs.len(), 2);
    for value in expected_inputs {
        let index = second
            .preimage
            .public_transcript_inputs
            .iter()
            .position(|field| *field == value)
            .expect("opaque List value is bound through Compress");
        second.preimage.public_transcript_inputs[index] = value + Fr::from(1u64);
        assert!(check(&second, &push_circuit).is_err());
        second.preimage.public_transcript_inputs[index] = value;
    }

    let populated = &second.after.state;
    assert_stored(populated, &push, "strings", text.as_bytes());
    assert_stored(populated, &push, "byteArrays", &bytes);
    assert_heads(&read(populated), [true, true], &text, &bytes);

    let mut altered = inspect.clone();
    altered
        .returns
        .iter_mut()
        .find(|output| output.name == "stringHead_value")
        .unwrap()
        .expression = Expr::OpaqueEmpty {
        ty: "OpaqueString".into(),
    };
    let changed = prepare(&altered, &BTreeMap::new(), populated, parameters, address)
        .expect("altered host output prepares");
    assert!(check(&changed, &inspect_circuit).is_err());

    let after_first_pop = &oracle["afterFirstPop"];
    let remaining_text = String::from_utf8(decode(after_first_pop, "texts", 0)).unwrap();
    let remaining_bytes = decode(after_first_pop, "blobs", 0);
    let first_pop = drop_head(populated);
    assert_heads(
        &read(&first_pop.after.state),
        [true, true],
        &remaining_text,
        &remaining_bytes,
    );
    let second_pop = drop_head(&first_pop.after.state);
    assert_heads(
        &read(&second_pop.after.state),
        serde_json::from_value(oracle["afterSecondPop"]["heads"].clone()).unwrap(),
        "",
        &[],
    );

    let empty_pop = drop_head(&second_pop.after.state);
    let result = QueryContext::new(second_pop.after.state.clone(), address)
        .query(
            &empty_pop.program,
            None,
            &parameters.cost_model.runtime_cost_model,
        )
        .unwrap();
    let StateValue::Array(root) = result.context.state.get_ref() else {
        panic!("expected native state slots");
    };
    assert_eq!(oracle["afterEmptyPop"], json!(["null", "null"]));
    assert!(matches!(root.get(0), Some(StateValue::Null)));
    assert!(matches!(root.get(1), Some(StateValue::Null)));
    assert!(prepare(
        &inspect,
        &BTreeMap::new(),
        &result.context.state,
        parameters,
        address,
    )
    .is_err());

    assert!(prepare(&push, &inputs("bad\0", &bytes), &state, parameters, address).is_err());
    assert!(prepare(
        &push,
        &inputs(&text, &[0x41, 0x00]),
        &state,
        parameters,
        address
    )
    .is_err());
}
