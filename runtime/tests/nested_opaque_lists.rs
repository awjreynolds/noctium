#![cfg(feature = "zkir-321")]

use anyhow::Result;
use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Execution, Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
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
    assert!(
        oracle["compact"]
            .as_str()
            .unwrap()
            .starts_with("0.36.1 (7fa3a117c")
    );
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

fn inputs(plan: &Plan, keys: &[[u8; 32]], text: &str) -> BTreeMap<String, Json> {
    plan.circuit
        .inputs
        .iter()
        .map(|input| {
            let value = match input.name.as_str() {
                "owner" => json!({"kind":"bytes", "values":keys[0]}),
                "group" => json!({"kind":"bytes", "values":keys[1]}),
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
    keys: &[[u8; 32]],
    text: &str,
    state: &ChargedState<noctium_runtime::Db>,
) -> Execution {
    let execution = prepare(
        plan,
        &inputs(plan, keys, text),
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
    name: &str,
    keys: &[[u8; 32]],
    expected: Option<&[u8]>,
) {
    let StateValue::Array(root) = state.get_ref() else {
        panic!("expected root state array")
    };
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == name)
        .expect("List Map declaration");
    let mut value = root.get(slot).expect("List Map slot").clone();
    for key in keys {
        let StateValue::Map(map) = &value else {
            panic!("expected a Map on the List path")
        };
        value = (*map.get(&AlignedValue::from(*key)).expect("List Map entry")).clone();
    }
    let StateValue::Array(list) = &value else {
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
    let owner = &[owner_bytes(&oracle, "owner")];
    let sibling = &[owner_bytes(&oracle, "sibling")];
    let (clear, clear_circuit) = fixture(&directory, "clear");
    let (push, push_circuit) = fixture(&directory, "push");
    let (inspect, inspect_circuit) = fixture(&directory, "inspect");
    let (pop, pop_circuit) = fixture(&directory, "pop");
    let config = BTreeMap::from([("texts".into(), json!([])), ("deepTexts".into(), json!([]))]);
    let initial = create_state(&clear, &config)?;

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
    assert_map_list(
        after_pushes,
        &push,
        "texts",
        owner,
        Some(second_text.as_bytes()),
    );
    assert_map_list(
        after_pushes,
        &push,
        "texts",
        sibling,
        Some(sibling_text.as_bytes()),
    );

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
        "texts",
        owner,
        Some(first_text.as_bytes()),
    );
    assert_map_list(
        &first_pop.after.state,
        &push,
        "texts",
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
    assert_map_list(&final_pop.after.state, &push, "texts", owner, None);
    assert_map_list(
        &final_pop.after.state,
        &push,
        "texts",
        sibling,
        Some(sibling_text.as_bytes()),
    );

    let deep = &oracle["deep"];
    let owner = owner_bytes(deep, "owner");
    let group_a = owner_bytes(deep, "groupA");
    let path_a = &[owner, group_a];
    let path_b = &[owner, owner_bytes(deep, "groupB")];
    let missing_owner = &[owner_bytes(deep, "missingOwner"), group_a];
    let missing_group = &[owner, owner_bytes(deep, "missingGroup")];
    let (clear, clear_circuit) = fixture(&directory, "clearDeep");
    let (push, push_circuit) = fixture(&directory, "pushDeep");
    let (inspect, inspect_circuit) = fixture(&directory, "inspectDeep");
    let (pop, pop_circuit) = fixture(&directory, "popDeep");

    let mut malformed_plan = clear.clone();
    let deep_map = malformed_plan
        .state
        .iter_mut()
        .find(|declaration| declaration.name == "deepTexts")
        .expect("two-parent List declaration");
    deep_map.kind["tree"]["map"][1]["map"][0] = json!("Bytes<31>");
    let error = create_state(&malformed_plan, &config).expect_err("mixed key width rejected");
    assert!(
        error
            .to_string()
            .contains("OpaqueString Lists require a root or up to two Bytes32 Map keys")
    );

    let mut state = final_pop.after.state;
    let clear_a = run(&clear, &clear_circuit, path_a, "", &state);
    for (flag, path, state) in [
        ("missingOwnerRejected", missing_owner, &state),
        ("missingGroupRejected", missing_group, &clear_a.after.state),
    ] {
        assert_eq!(deep[flag].as_bool(), Some(true));
        assert!(
            prepare(
                &inspect,
                &inputs(&inspect, path, ""),
                state,
                &ledger::structure::INITIAL_PARAMETERS,
                ContractAddress::default(),
            )
            .is_err(),
            "strict inspection through a missing parent must reject"
        );
    }
    state = run(&clear, &clear_circuit, path_b, "", &clear_a.after.state)
        .after
        .state;
    let empty_head = run(&inspect, &inspect_circuit, path_a, "", &state);
    assert_head(&empty_head, &deep["emptyAfterClear"]);
    assert_map_list(&state, &inspect, "deepTexts", path_a, None);

    for (path, name, text) in [
        (path_a, "first", "A\0夜\0B"),
        (path_b, "siblingValue", "group-b"),
        (path_a, "second", "deep-second"),
    ] {
        assert_eq!(deep[name].as_str(), Some(text));
        state = run(&push, &push_circuit, path, text, &state).after.state;
    }
    let after_pop = run(&pop, &pop_circuit, path_a, "", &state).after.state;
    let after_final_pop = run(&pop, &pop_circuit, path_a, "", &after_pop).after.state;
    for (stage, state) in [
        ("afterPush", &state),
        ("afterPop", &after_pop),
        ("afterFinalPop", &after_final_pop),
    ] {
        for (group, path) in [("groupA", path_a), ("groupB", path_b)] {
            let expected = &deep[stage][group];
            let head = run(&inspect, &inspect_circuit, path, "", state);
            assert_head(&head, expected);
            let raw_head = expected["is_some"]
                .as_bool()
                .unwrap()
                .then(|| expected["value"].as_str().unwrap().as_bytes());
            assert_map_list(state, &inspect, "deepTexts", path, raw_head);
            assert_eq!(head.after.state.get_ref(), state.get_ref());
        }
    }
    Ok(())
}
