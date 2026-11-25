#![cfg(feature = "zkir-321")]

use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use noctium_runtime::{Db, Execution, Expr, Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::{
    context::QueryContext,
    state::{ChargedState, StateValue},
};
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    fs::File,
    path::{Path, PathBuf},
};
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

fn fixture(directory: &Path, contract: &str, entry: &str) -> (Plan, IrSource) {
    let stem = format!("{contract}.{entry}");
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
    assert!(
        oracle["compact"]
            .as_str()
            .unwrap()
            .starts_with("0.36.1 (7fa3a117c")
    );
    assert_eq!(oracle["runtime"], "0.21.0");
    let decode = |row: &Json, key: &str, index: usize| {
        hex::decode(row[key][index].as_str().unwrap()).unwrap()
    };

    let (push, push_circuit) = fixture(&artifacts, "OpaqueLists", "push");
    let (inspect, inspect_circuit) = fixture(&artifacts, "OpaqueLists", "inspect");
    let (pop, pop_circuit) = fixture(&artifacts, "OpaqueLists", "pop");
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
    assert!(
        prepare(
            &inspect,
            &BTreeMap::new(),
            &result.context.state,
            parameters,
            address,
        )
        .is_err()
    );

    assert!(prepare(&push, &inputs("bad\0", &bytes), &state, parameters, address).is_err());
    assert!(
        prepare(
            &push,
            &inputs(&text, &[0x41, 0x00]),
            &state,
            parameters,
            address
        )
        .is_err()
    );
}

#[test]
#[ignore = "requires fresh NestedOpaqueBytesList artifacts and the pinned Compact oracle"]
fn nested_opaque_bytes_list_distinguishes_absence_from_present_empty() {
    let artifacts = PathBuf::from(
        std::env::var_os("NOCTIUM_NESTED_OPAQUE_BYTES_LIST_DIR").expect(
            "set fresh NestedOpaqueBytesList artifacts in NOCTIUM_NESTED_OPAQUE_BYTES_LIST_DIR",
        ),
    );
    let oracle_path = std::env::var_os("NOCTIUM_NESTED_OPAQUE_BYTES_LIST_COMPACT")
        .expect("set Compact output in NOCTIUM_NESTED_OPAQUE_BYTES_LIST_COMPACT");
    let oracle: Json = serde_json::from_slice(&std::fs::read(oracle_path).unwrap()).unwrap();
    assert!(
        oracle["compact"]
            .as_str()
            .unwrap()
            .starts_with("0.36.1 (7fa3a117c")
    );
    assert_eq!(oracle["runtime"], "0.21.0");
    for (name, byte) in [("owner", 0x11), ("sibling", 0x22), ("missingOwner", 0x33)] {
        assert_eq!(
            oracle[name].as_str(),
            Some(hex::encode([byte; 32]).as_str())
        );
    }
    assert_eq!(oracle["siblingValue"], json!([0x80, 0, 0xfe]));
    assert_eq!(oracle["missingOwnerRejected"], json!(true));

    let (clear, clear_circuit) = fixture(&artifacts, "NestedOpaqueBytesList", "clear");
    let (push, push_circuit) = fixture(&artifacts, "NestedOpaqueBytesList", "push");
    let (inspect, inspect_circuit) = fixture(&artifacts, "NestedOpaqueBytesList", "inspect");
    let (pop, pop_circuit) = fixture(&artifacts, "NestedOpaqueBytesList", "pop");
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let initial = create_state(&clear, &BTreeMap::from([("byteArrays".into(), json!([]))]))
        .expect("nested opaque byte List state creates");
    let at_owner = |owner: u8, bytes: Option<&[u8]>| {
        let key = [owner; 32];
        let mut values = BTreeMap::from([("owner".into(), json!({"kind":"bytes", "values":key}))]);
        if let Some(bytes) = bytes {
            values.insert(
                "bytes".into(),
                json!({"kind":"opaqueBytes", "values": bytes}),
            );
        }
        values
    };
    let run = |plan, circuit, state, owner, bytes| {
        let execution = prepare(plan, &at_owner(owner, bytes), state, parameters, address)
            .expect("native List operation prepares");
        check(&execution, circuit).expect("native List relation checks");
        execution
    };
    assert!(
        prepare(
            &inspect,
            &at_owner(0x33, None),
            &initial,
            parameters,
            address
        )
        .is_err()
    );

    let owner_clear = run(&clear, &clear_circuit, &initial, 0x11, None);
    let sibling_clear = run(&clear, &clear_circuit, &owner_clear.after.state, 0x22, None);
    let seeded = run(
        &push,
        &push_circuit,
        &sibling_clear.after.state,
        0x22,
        Some(&[0x80, 0, 0xfe]),
    );
    let empty = run(&push, &push_circuit, &seeded.after.state, 0x11, Some(&[]));
    let binary = run(
        &push,
        &push_circuit,
        &empty.after.state,
        0x11,
        Some(&[0, 0xff]),
    );
    let first_pop = run(&pop, &pop_circuit, &binary.after.state, 0x11, None);
    let final_pop = run(&pop, &pop_circuit, &first_pop.after.state, 0x11, None);

    let list_for = |state: &ChargedState<Db>, owner: u8| {
        let StateValue::Array(root) = state.get_ref() else {
            panic!("expected native state slots");
        };
        let StateValue::Map(buckets) = root.get(0).expect("byteArrays Map slot") else {
            panic!("expected native owner Map");
        };
        let key = AlignedValue::from([owner; 32]);
        (*buckets.get(&key).expect("owner List exists")).clone()
    };
    let sibling_state = list_for(&seeded.after.state, 0x22);
    for (stage, state) in [
        ("afterClear", &seeded.after.state),
        ("afterEmptyPush", &empty.after.state),
        ("afterBinaryPush", &binary.after.state),
        ("afterFirstPop", &first_pop.after.state),
        ("afterFinalPop", &final_pop.after.state),
    ] {
        assert_eq!(list_for(state, 0x22), sibling_state);
        for (name, owner) in [("owner", 0x11), ("sibling", 0x22)] {
            let expected = &oracle[stage][name];
            let present = expected["is_some"].as_bool().expect("Compact Maybe tag");
            let bytes: Vec<u8> = serde_json::from_value(expected["value"].clone()).unwrap();
            let head = run(&inspect, &inspect_circuit, state, owner, None);
            assert_eq!(head.after.state.get_ref(), state.get_ref());
            assert_eq!(
                head.returns_json()["bytesHead"],
                json!({
                    "kind": "struct",
                    "id": "NestedOpaqueBytesList.MaybeOpaqueBytes",
                    "fields": [
                        {"name": "is_some", "value": {"kind": "bool", "value": present}},
                        {"name": "value", "value": {"kind": "opaqueBytes", "values": bytes}},
                    ]
                })
            );
            let StateValue::Array(ref list) = list_for(state, owner) else {
                panic!("expected a native List node");
            };
            match (present, list.get(0)) {
                (false, Some(StateValue::Null)) => assert!(bytes.is_empty()),
                (true, Some(StateValue::Cell(cell))) => assert_eq!(**cell, compressed(&bytes)),
                _ => panic!("expected a native List head matching the Compact Maybe tag"),
            }
        }
    }
}
