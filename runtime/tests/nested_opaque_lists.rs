#![cfg(feature = "zkir-321")]

use anyhow::Result;
use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use coin_structure::contract::ContractAddress;
use noctium_runtime::{check, create_state, prepare, zkir::IrSource, Execution, Plan};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{json, Value as Json};
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::curve::Fr;
use transient_crypto::fab::AlignedValueExt;

fn artifacts() -> PathBuf {
    PathBuf::from(
        std::env::var_os("NOCTIUM_NESTED_OPAQUE_LISTS_DIR")
            .expect("set fresh NestedOpaqueLists outputs in NOCTIUM_NESTED_OPAQUE_LISTS_DIR"),
    )
}

fn compact_oracle() -> Json {
    let path = std::env::var_os("NOCTIUM_NESTED_OPAQUE_LISTS_COMPACT")
        .expect("set pinned Compact output in NOCTIUM_NESTED_OPAQUE_LISTS_COMPACT");
    let oracle: Json = serde_json::from_slice(&fs::read(path).expect("read Compact output"))
        .expect("parse Compact output");
    assert!(oracle["compact"]
        .as_str()
        .unwrap()
        .starts_with("0.36.1 (7fa3a117c"));
    assert_eq!(oracle["runtime"], "0.21.0");
    oracle
}

fn fixture(directory: &PathBuf, entry: &str) -> (Plan, IrSource) {
    let stem = format!("NestedOpaqueLists.{entry}");
    let plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json"))).unwrap())
            .unwrap();
    let circuit = IrSource::load(
        fs::read(directory.join(format!("{stem}.zkir")))
            .unwrap()
            .as_slice(),
    )
    .unwrap();
    (plan, circuit)
}

fn owner_bytes(oracle: &Json, name: &str) -> [u8; 32] {
    hex::decode(oracle[name].as_str().unwrap())
        .unwrap()
        .try_into()
        .unwrap()
}

fn inputs(plan: &Plan, owner: [u8; 32], text: &str) -> BTreeMap<String, Json> {
    plan.circuit
        .inputs
        .iter()
        .map(|input| {
            let value = match input.name.as_str() {
                "owner" => json!({"kind":"bytes", "values":owner}),
                "text" => json!({"kind":"opaqueString", "value":text}),
                other => panic!("unexpected input {other}"),
            };
            (input.name.clone(), value)
        })
        .collect()
}

fn compressed(bytes: &[u8]) -> AlignedValue {
    AlignedValue::new(
        FabValue(vec![ValueAtom::from(bytes)]),
        Alignment::singleton(AlignmentAtom::Compress),
    )
    .expect("canonical opaque string Compress value")
}

fn run(
    plan: &Plan,
    circuit: &IrSource,
    owner: [u8; 32],
    text: &str,
    state: &ChargedState<noctium_runtime::Db>,
) -> Execution {
    let execution = prepare(
        plan,
        &inputs(plan, owner, text),
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )
    .expect("native execution prepares");
    check(&execution, circuit).expect("native ZKIR relation checks");
    execution
}

fn assert_head(execution: &Execution, compact_expected: &Json) {
    let is_some = compact_expected["is_some"].as_bool().unwrap();
    let text = compact_expected["value"].as_str().unwrap();
    let native_expected = json!({
        "kind": "struct",
        "id": "NestedOpaqueLists.MaybeOpaqueString",
        "fields": [
            {"name":"is_some", "value":{"kind":"bool", "value":is_some}},
            {"name":"value", "value":{"kind":"opaqueString", "value":text}},
        ]
    });
    assert_eq!(execution.returns_json()["textHead"], native_expected);
}

fn assert_map_list(
    state: &ChargedState<noctium_runtime::Db>,
    plan: &Plan,
    owner: [u8; 32],
    expected: Option<&[u8]>,
) {
    let StateValue::Array(root) = state.get_ref() else {
        panic!("expected root state array")
    };
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == "texts")
        .expect("texts Map declaration");
    let StateValue::Map(map) = root.get(slot).expect("texts Map slot") else {
        panic!("expected root Map")
    };
    let key: AlignedValue = owner.into();
    let Some(value) = map.get(&key) else {
        assert!(expected.is_none(), "expected owner Map entry");
        return;
    };
    let StateValue::Array(list) = &*value else {
        panic!("expected nested List node")
    };
    match expected {
        Some(bytes) => {
            let StateValue::Cell(head) = list.get(0).expect("nested List head") else {
                panic!("expected nested List head Cell")
            };
            assert_eq!(**head, compressed(bytes));
        }
        None => assert!(matches!(list.get(0), Some(StateValue::Null))),
    }
}

#[test]
#[ignore = "requires fresh NestedOpaqueLists artifacts and pinned Compact output"]
fn nested_opaque_string_lists_match_compact_and_preserve_map_siblings() -> Result<()> {
    let directory = artifacts();
    let oracle = compact_oracle();
    let first_text = oracle["first"].as_str().unwrap();
    let second_text = oracle["second"].as_str().unwrap();
    let sibling_text = oracle["siblingValue"].as_str().unwrap();
    let owner = owner_bytes(&oracle, "owner");
    let sibling = owner_bytes(&oracle, "sibling");
    let (clear, clear_circuit) = fixture(&directory, "clear");
    let (push, push_circuit) = fixture(&directory, "push");
    let (inspect, inspect_circuit) = fixture(&directory, "inspect");
    let (pop, pop_circuit) = fixture(&directory, "pop");
    let initial = create_state(&clear, &BTreeMap::from([("texts".into(), json!([]))]))?;

    assert!(
        prepare(
            &inspect,
            &inputs(&inspect, owner, ""),
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
        .is_err(),
        "active read through a missing parent must reject"
    );

    let owner_clear = run(&clear, &clear_circuit, owner, "", &initial);
    let sibling_clear = run(
        &clear,
        &clear_circuit,
        sibling,
        "",
        &owner_clear.after.state,
    );
    assert_head(
        &run(
            &inspect,
            &inspect_circuit,
            owner,
            "",
            &sibling_clear.after.state,
        ),
        &oracle["absent"],
    );

    let first_push = run(
        &push,
        &push_circuit,
        owner,
        first_text,
        &sibling_clear.after.state,
    );
    let first_projection = compressed(first_text.as_bytes());
    let mut expected_projection = Vec::new();
    first_projection.value_only_field_repr(&mut expected_projection);
    assert_eq!(expected_projection.len(), 1);
    let projection = expected_projection[0];
    let transcript_index = first_push
        .preimage
        .public_transcript_inputs
        .iter()
        .position(|field| *field == projection)
        .expect("disclosed OpaqueString binds its Compress projection");
    let mut tampered = prepare(
        &push,
        &inputs(&push, owner, first_text),
        &sibling_clear.after.state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    tampered.preimage.public_transcript_inputs[transcript_index] = projection + Fr::from(1u64);
    assert!(
        check(&tampered, &push_circuit).is_err(),
        "changed bound payload must reject"
    );

    let sibling_push = run(
        &push,
        &push_circuit,
        sibling,
        sibling_text,
        &first_push.after.state,
    );
    let second_push = run(
        &push,
        &push_circuit,
        owner,
        second_text,
        &sibling_push.after.state,
    );
    let after_pushes = &second_push.after.state;
    assert_head(
        &run(&inspect, &inspect_circuit, owner, "", after_pushes),
        &oracle["afterPushes"]["owner"],
    );
    assert_head(
        &run(&inspect, &inspect_circuit, sibling, "", after_pushes),
        &oracle["afterPushes"]["sibling"],
    );
    assert_map_list(after_pushes, &push, owner, Some(second_text.as_bytes()));
    assert_map_list(after_pushes, &push, sibling, Some(sibling_text.as_bytes()));

    let first_pop = run(&pop, &pop_circuit, owner, "", after_pushes);
    assert_head(
        &run(
            &inspect,
            &inspect_circuit,
            owner,
            "",
            &first_pop.after.state,
        ),
        &oracle["afterPop"]["owner"],
    );
    assert_head(
        &run(
            &inspect,
            &inspect_circuit,
            sibling,
            "",
            &first_pop.after.state,
        ),
        &oracle["afterPop"]["sibling"],
    );
    assert_map_list(
        &first_pop.after.state,
        &push,
        owner,
        Some(first_text.as_bytes()),
    );
    assert_map_list(
        &first_pop.after.state,
        &push,
        sibling,
        Some(sibling_text.as_bytes()),
    );

    let final_pop = run(&pop, &pop_circuit, owner, "", &first_pop.after.state);
    assert_head(
        &run(
            &inspect,
            &inspect_circuit,
            owner,
            "",
            &final_pop.after.state,
        ),
        &oracle["afterFinalPop"]["owner"],
    );
    assert_head(
        &run(
            &inspect,
            &inspect_circuit,
            sibling,
            "",
            &final_pop.after.state,
        ),
        &oracle["afterFinalPop"]["sibling"],
    );
    assert_map_list(&final_pop.after.state, &push, owner, None);
    assert_map_list(
        &final_pop.after.state,
        &push,
        sibling,
        Some(sibling_text.as_bytes()),
    );
    Ok(())
}
