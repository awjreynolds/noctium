#![cfg(feature = "zkir-321")]

use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use noctium_runtime::{check, create_state, prepare, zkir::IrSource, Db, Plan};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{json, Value as Json};
use std::{
    collections::BTreeMap,
    fs::File,
    path::{Path, PathBuf},
};
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

fn artifacts() -> PathBuf {
    PathBuf::from(
        std::env::var_os("NOCTIUM_OPAQUE_LISTS_DIR")
            .expect("set fresh OpaqueLists outputs in NOCTIUM_OPAQUE_LISTS_DIR"),
    )
}

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

fn assert_heads(
    execution: &noctium_runtime::Execution,
    string_present: bool,
    string: &str,
    bytes_present: bool,
    bytes: &[u8],
) {
    let returns = execution.returns_json();
    assert_eq!(returns.get("stringIsPresent"), Some(&json!(string_present)));
    assert_eq!(
        returns.get("stringValue"),
        Some(&json!({"kind":"opaqueString", "value":string}))
    );
    assert_eq!(returns.get("bytesArePresent"), Some(&json!(bytes_present)));
    assert_eq!(
        returns.get("bytesValue"),
        Some(&json!({"kind":"opaqueBytes", "values":bytes}))
    );

    let mut expected_outputs = vec![Fr::from(u64::from(string_present))];
    if string_present {
        compressed(string.as_bytes()).value_only_field_repr(&mut expected_outputs);
    }
    expected_outputs.push(Fr::from(u64::from(bytes_present)));
    if bytes_present {
        compressed(bytes).value_only_field_repr(&mut expected_outputs);
    }
    assert_eq!(
        execution.preimage.public_transcript_outputs,
        expected_outputs
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
#[ignore = "requires fresh Lean artifacts in NOCTIUM_OPAQUE_LISTS_DIR"]
fn opaque_root_lists_admit_compress_storage_and_round_trip_heads_after_pop() {
    let artifacts = artifacts();
    let (push_plan, push_circuit) = fixture(&artifacts, "push");
    let (inspect_plan, inspect_circuit) = fixture(&artifacts, "inspect");
    let (pop_plan, pop_circuit) = fixture(&artifacts, "pop");
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let state = create_state(
        &push_plan,
        &BTreeMap::from([
            ("strings".into(), json!([])),
            ("byteArrays".into(), json!([])),
        ]),
    )
    .expect("root OpaqueString and OpaqueBytes List states create");

    let empty = prepare(&inspect_plan, &BTreeMap::new(), &state, parameters, address)
        .expect("empty opaque List heads prepare");
    check(&empty, &inspect_circuit).expect("empty opaque List head relation checks");
    assert_heads(&empty, false, "", false, &[]);

    let text = "é\0λ";
    let bytes = [0x00, 0x01, 0xff, 0x41];
    let before = state.clone();
    let mut push = prepare(
        &push_plan,
        &inputs(text, &bytes),
        &state,
        parameters,
        address,
    )
    .expect("canonical opaque List pushes prepare");
    check(&push, &push_circuit).expect("opaque List push relation checks");
    assert_eq!(state, before);

    let mut expected_inputs = Vec::new();
    compressed(text.as_bytes()).value_only_field_repr(&mut expected_inputs);
    compressed(&bytes).value_only_field_repr(&mut expected_inputs);
    assert_eq!(expected_inputs.len(), 2);
    for value in expected_inputs {
        let index = push
            .preimage
            .public_transcript_inputs
            .iter()
            .position(|field| *field == value)
            .expect("opaque List value is bound through Compress");
        let original = push.preimage.public_transcript_inputs[index];
        push.preimage.public_transcript_inputs[index] = original + Fr::from(1u64);
        assert!(check(&push, &push_circuit).is_err());
        push.preimage.public_transcript_inputs[index] = original;
    }

    let populated = push.after.state.clone();
    assert_stored(&populated, &push_plan, "strings", text.as_bytes());
    assert_stored(&populated, &push_plan, "byteArrays", &bytes);
    let read = prepare(
        &inspect_plan,
        &BTreeMap::new(),
        &populated,
        parameters,
        address,
    )
    .expect("opaque List head reads prepare");
    check(&read, &inspect_circuit).expect("opaque List head relation checks");
    assert_heads(&read, true, text, true, &bytes);

    let pop = prepare(&pop_plan, &BTreeMap::new(), &populated, parameters, address)
        .expect("opaque List pops prepare");
    check(&pop, &pop_circuit).expect("opaque List pop relation checks");
    let empty_again = prepare(
        &inspect_plan,
        &BTreeMap::new(),
        &pop.after.state,
        parameters,
        address,
    )
    .expect("popped opaque Lists return typed empty heads");
    check(&empty_again, &inspect_circuit).expect("popped empty heads relation checks");
    assert_heads(&empty_again, false, "", false, &[]);

    assert!(prepare(
        &push_plan,
        &inputs("bad\0", &bytes),
        &state,
        parameters,
        address
    )
    .is_err());
    assert!(prepare(
        &push_plan,
        &inputs(text, &[0x41, 0x00]),
        &state,
        parameters,
        address
    )
    .is_err());
}
