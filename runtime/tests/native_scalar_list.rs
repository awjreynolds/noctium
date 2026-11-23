#![cfg(feature = "zkir-321")]

use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use noctium_runtime::{Db, Plan, check, create_state, field_value, prepare, zkir::IrSource};
use onchain_runtime::{
    context::QueryContext,
    ops::{Key, Op, expect_checked},
    program_fragments::List_pop_front,
    result_mode::ResultModeGather,
    state::{ChargedState, StateValue},
};
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    env,
    path::{Path, PathBuf},
};
use storage::arena::Sp;
use storage::storage::HashMap;
use transient_crypto::curve::Fr;

fn artifacts() -> PathBuf {
    env::var_os("NOCTIUM_NATIVE_SCALAR_LIST_DIR")
        .map(PathBuf::from)
        .expect("set fresh outputs in NOCTIUM_NATIVE_SCALAR_LIST_DIR")
}

fn fixture(directory: &Path, entry: &str) -> (Plan, IrSource) {
    let stem = format!("NativeScalarList.{entry}");
    let plan = serde_json::from_slice(
        &std::fs::read(directory.join(format!("{stem}.impact.json"))).unwrap(),
    )
    .unwrap();
    let circuit = IrSource::load(
        std::fs::read(directory.join(format!("{stem}.zkir")))
            .unwrap()
            .as_slice(),
    )
    .unwrap();
    (plan, circuit)
}

fn bytes_json(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn inputs(
    plan: &Plan,
    owner: u8,
    amount: u64,
    payload: &[u8],
    enabled: bool,
) -> BTreeMap<String, Json> {
    plan.circuit
        .inputs
        .iter()
        .map(|input| {
            let value = match input.name.as_str() {
                "owner" => json!({"kind":"bytes", "values":vec![owner; 32]}),
                "amount" => json!(amount.to_string()),
                "payload" => bytes_json(payload),
                "empty" => bytes_json(&[]),
                "enabled" => json!(enabled),
                other => panic!("unexpected input {other}"),
            };
            (input.name.clone(), value)
        })
        .collect()
}

fn bytes_alignment(value: &[u8]) -> AlignedValue {
    AlignedValue::new(
        FabValue(vec![ValueAtom::from(value)]),
        Alignment::singleton(AlignmentAtom::Bytes {
            length: value.len() as u32,
        }),
    )
    .unwrap()
}

fn native_atom(value: u64) -> AlignedValue {
    field_value(Fr::from(value))
}

fn assert_list(node: &StateValue<Db>, expected: &[AlignedValue]) {
    let StateValue::Array(node) = node else {
        panic!("expected native List array")
    };
    assert_eq!(node.len(), 3);
    let StateValue::Cell(length) = node.get(2).unwrap() else {
        panic!("expected List length Cell")
    };
    assert_eq!(**length, AlignedValue::from(expected.len() as u64));
    if let Some((head, tail)) = expected.split_first() {
        let StateValue::Cell(value) = node.get(0).unwrap() else {
            panic!("expected List head Cell")
        };
        assert_eq!(**value, *head);
        assert_list(node.get(1).unwrap(), tail);
    } else {
        assert!(matches!(node.get(0), Some(StateValue::Null)));
        assert!(matches!(node.get(1), Some(StateValue::Null)));
    }
}

fn assert_state(
    state: &ChargedState<Db>,
    plan: &Plan,
    native_values: &[u64],
    zero_values: usize,
    payload_values: &[Vec<u8>],
) {
    let StateValue::Array(root) = state.get_ref() else {
        panic!("expected contract state array")
    };
    let slot = |name: &str| {
        plan.state
            .iter()
            .position(|decl| decl.name == name)
            .unwrap()
    };
    let native = native_values
        .iter()
        .copied()
        .map(native_atom)
        .collect::<Vec<_>>();
    assert_list(root.get(slot("values")).unwrap(), &native);
    let zero = vec![bytes_alignment(&[]); zero_values];
    assert_list(root.get(slot("zeroBytes")).unwrap(), &zero);
    let StateValue::Map(memos) = root.get(slot("memos")).unwrap() else {
        panic!("expected memo map")
    };
    let owner: AlignedValue = [7u8; 32].into();
    let payloads = payload_values
        .iter()
        .map(|value| bytes_alignment(value))
        .collect::<Vec<_>>();
    assert_list(&memos.get(&owner).unwrap(), &payloads);
}

fn assert_bytes128_head(state: &ChargedState<Db>, plan: &Plan, expected: &[u8]) {
    let StateValue::Array(root) = state.get_ref() else {
        panic!("expected contract state array")
    };
    let memos_slot = plan
        .state
        .iter()
        .position(|decl| decl.name == "memos")
        .unwrap();
    let StateValue::Map(memos) = root.get(memos_slot).unwrap() else {
        panic!("expected memo map")
    };
    let owner: AlignedValue = [7u8; 32].into();
    let StateValue::Array(list) = &*memos.get(&owner).unwrap() else {
        panic!("expected nested List")
    };
    let StateValue::Cell(head) = list.get(0).unwrap() else {
        panic!("expected Bytes128 head cell")
    };
    assert_eq!(**head, bytes_alignment(expected));
    assert_eq!(head.value.0.len(), 1, "Bytes128 is one FAB atom");
    assert_eq!(head.value.0[0].0.as_slice(), expected);
    assert_eq!(
        head.alignment,
        Alignment::singleton(AlignmentAtom::Bytes { length: 128 })
    );
}

fn assert_bytes128_chunks(plan: &Plan, read_name: &str) {
    let read = plan
        .reads
        .iter()
        .find(|read| read.name == read_name)
        .expect("Bytes128 List read exists");
    let projections = read
        .projections
        .as_ref()
        .expect("Bytes128 read has field projections");
    assert_eq!(
        projections.len(),
        5,
        "Bytes128 uses five 31-byte field chunks"
    );
    for (index, projection) in projections.iter().enumerate() {
        assert_eq!(
            projection.name,
            format!("_noctium_bytes_{read_name}_{index}")
        );
    }
}

fn expected_snapshot(
    native_present: bool,
    native: u64,
    zero_present: bool,
    payload_present: bool,
    payload: &[u8],
    native_length: u64,
    zero_length: u64,
    payload_length: u64,
) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("nativePresentResult".into(), json!(native_present)),
        ("nativeDefault".into(), json!(native.to_string())),
        ("emptyPresentResult".into(), json!(zero_present)),
        ("emptyDefault".into(), bytes_json(&[])),
        ("payloadPresentResult".into(), json!(payload_present)),
        ("payloadDefault".into(), bytes_json(payload)),
        ("nativeCount".into(), json!(native_length.to_string())),
        ("emptyCount".into(), json!(zero_length.to_string())),
        ("payloadCount".into(), json!(payload_length.to_string())),
        ("nativeIsEmpty".into(), json!(native_length == 0)),
        ("zeroBytesIsEmpty".into(), json!(zero_length == 0)),
        ("payloadIsEmpty".into(), json!(payload_length == 0)),
    ])
}

fn run(
    plan: &Plan,
    circuit: &IrSource,
    amount: u64,
    payload: &[u8],
    state: &ChargedState<Db>,
) -> noctium_runtime::Execution {
    execute(plan, circuit, 7, true, amount, payload, state)
}

fn execute(
    plan: &Plan,
    circuit: &IrSource,
    owner: u8,
    enabled: bool,
    amount: u64,
    payload: &[u8],
    state: &ChargedState<Db>,
) -> noctium_runtime::Execution {
    let execution = prepare(
        plan,
        &inputs(plan, owner, amount, payload, enabled),
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    check(&execution, circuit).unwrap();
    execution
}

fn native_query_succeeds(state: &ChargedState<Db>, execution: &noctium_runtime::Execution) -> bool {
    QueryContext::new(
        state.clone(),
        coin_structure::contract::ContractAddress::default(),
    )
    .query(
        &execution.program,
        None,
        &ledger::structure::INITIAL_PARAMETERS.cost_model.runtime_cost_model,
    )
    .is_ok()
}

#[test]
#[ignore = "requires fresh NativeScalarList outputs in NOCTIUM_NATIVE_SCALAR_LIST_DIR"]
fn native_scalar_lists_round_trip_defaults_pops_resets_and_alignment() {
    let directory = artifacts();
    let (append, append_circuit) = fixture(&directory, "append");
    let (inspect, inspect_circuit) = fixture(&directory, "inspect");
    let (guard_missing, guard_missing_circuit) = fixture(&directory, "guardMissing");
    let (pop, pop_circuit) = fixture(&directory, "pop");
    let (pop_root, pop_root_circuit) = fixture(&directory, "popRoot");
    let (pop_nested, pop_nested_circuit) = fixture(&directory, "popNested");
    let (guarded_pop, guarded_pop_circuit) = fixture(&directory, "guardedPop");
    let (clear, clear_circuit) = fixture(&directory, "clear");
    assert_bytes128_chunks(&inspect, "payloadValue");

    let base = create_state(
        &append,
        &BTreeMap::from([
            ("values".into(), json!([])),
            ("zeroBytes".into(), json!([])),
            ("memos".into(), json!([])),
        ]),
    )
    .unwrap();
    let cleared = run(&clear, &clear_circuit, 0, &vec![0; 128], &base);
    assert_eq!(
        cleared.returns_json(),
        expected_snapshot(false, 0, false, false, &vec![0; 128], 0, 0, 0)
    );
    let empty = cleared.after.state;
    assert_state(&empty, &clear, &[], 0, &[]);

    assert!(prepare(
        &pop_root,
        &inputs(&pop_root, 7, 0, &vec![0; 128], true),
        &empty,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .is_err());
    assert!(prepare(
        &pop_nested,
        &inputs(&pop_nested, 7, 0, &vec![0; 128], true),
        &empty,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .is_err());

    let guarded_empty_or_absent = execute(
        &guarded_pop,
        &guarded_pop_circuit,
        8,
        false,
        0,
        &vec![0; 128],
        &base,
    );
    assert_eq!(guarded_empty_or_absent.after.state, base);
    assert!(native_query_succeeds(&base, &guarded_empty_or_absent));

    assert!(prepare(
        &pop_nested,
        &inputs(&pop_nested, 8, 0, &vec![0; 128], true),
        &base,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .is_err());

    let empty_view = run(&inspect, &inspect_circuit, 0, &vec![0; 128], &empty);
    assert_eq!(
        empty_view.returns_json(),
        expected_snapshot(false, 0, false, false, &vec![0; 128], 0, 0, 0)
    );
    let missing_path = prepare(
        &guard_missing,
        &inputs(&guard_missing, 8, 0, &vec![0; 128], false),
        &empty,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    check(&missing_path, &guard_missing_circuit).unwrap();
    assert_eq!(
        missing_path.returns_json(),
        BTreeMap::from([
            ("hasPayload".into(), json!(false)),
            ("optionalPayload".into(), bytes_json(&vec![0; 128])),
            ("pathEmpty".into(), json!(false)),
        ])
    );

    let first: Vec<u8> = (0..128).collect();
    let second: Vec<u8> = (128..=255).collect();
    let first_push = run(&append, &append_circuit, 5, &first, &empty);
    assert_eq!(first_push.returns_json()["headValue"], json!("5"));
    assert_eq!(first_push.returns_json()["headPayload"], bytes_json(&first));
    assert_eq!(
        first_push.returns_json()["nativePresentResult"],
        json!(true)
    );
    assert_eq!(first_push.returns_json()["emptyPresentResult"], json!(true));
    assert_eq!(first_push.returns_json()["emptyOptional"], bytes_json(&[]));
    assert_eq!(first_push.returns_json()["emptyCount"], json!("1"));
    let state = first_push.after.state;
    assert_state(&state, &append, &[5], 1, std::slice::from_ref(&first));
    assert_bytes128_head(&state, &append, &first);

    let second_push = run(&append, &append_circuit, 300, &second, &state);
    assert_eq!(second_push.returns_json()["headValue"], json!("300"));
    assert_eq!(
        second_push.returns_json()["headPayload"],
        bytes_json(&second)
    );
    assert_eq!(second_push.returns_json()["nativeCount"], json!("2"));
    assert_eq!(second_push.returns_json()["payloadCount"], json!("2"));
    let state = second_push.after.state;
    assert_state(
        &state,
        &append,
        &[300, 5],
        2,
        &[second.clone(), first.clone()],
    );
    assert_bytes128_head(&state, &append, &second);

    let root_only_pop = run(&pop_root, &pop_root_circuit, 0, &vec![0; 128], &state);
    assert_state(
        &root_only_pop.after.state,
        &pop_root,
        &[5],
        2,
        &[second.clone(), first.clone()],
    );
    assert!(!native_query_succeeds(&empty, &root_only_pop));

    let nested_only_pop = run(&pop_nested, &pop_nested_circuit, 0, &vec![0; 128], &state);
    assert_state(
        &nested_only_pop.after.state,
        &pop_nested,
        &[300, 5],
        2,
        &[first.clone()],
    );
    assert!(!native_query_succeeds(&empty, &nested_only_pop));
    assert!(!native_query_succeeds(&base, &nested_only_pop));

    let malformed = replace_nested_payload_head(&state, &append, &second);
    assert!(
        prepare(
            &inspect,
            &inputs(&inspect, 7, 0, &vec![0; 128], true),
            &malformed,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .is_err()
    );

    let popped = run(&pop, &pop_circuit, 0, &vec![0; 128], &state);
    assert_eq!(
        popped.returns_json(),
        expected_snapshot(true, 5, true, true, &first, 1, 1, 1)
    );
    let state = popped.after.state;
    assert_state(&state, &pop, &[5], 1, std::slice::from_ref(&first));

    let cleared = run(&clear, &clear_circuit, 0, &vec![0; 128], &state);
    assert_eq!(
        cleared.returns_json(),
        expected_snapshot(false, 0, false, false, &vec![0; 128], 0, 0, 0)
    );
    assert_state(&cleared.after.state, &clear, &[], 0, &[]);
}

fn replace_nested_payload_head(
    state: &ChargedState<Db>,
    plan: &Plan,
    expected: &[u8],
) -> ChargedState<Db> {
    let StateValue::Array(root) = state.get_ref() else {
        panic!("expected contract state array")
    };
    let slot = plan
        .state
        .iter()
        .position(|decl| decl.name == "memos")
        .unwrap();
    let StateValue::Map(memos) = root.get(slot).unwrap() else {
        panic!("expected memo map")
    };
    let owner: AlignedValue = [7u8; 32].into();
    let StateValue::Array(list) = &*memos.get(&owner).unwrap() else {
        panic!("expected nested List")
    };
    let invalid = AlignedValue {
        value: FabValue(vec![ValueAtom::from(expected)]),
        alignment: Alignment::singleton(AlignmentAtom::Bytes { length: 127 }),
    };
    let invalid_list =
        StateValue::Array(list.insert(0, StateValue::Cell(Sp::new(invalid))).unwrap());
    let invalid_memos = memos.insert(owner, invalid_list);
    ChargedState::new(StateValue::Array(
        root.insert(slot, StateValue::Map(invalid_memos)).unwrap(),
    ))
}

fn ledger_empty_list() -> StateValue<Db> {
    StateValue::Array(
        vec![
            StateValue::Null,
            StateValue::Null,
            StateValue::Cell(Sp::new(AlignedValue::from(0u64))),
        ]
        .into(),
    )
}

fn ledger_list_pop_program(keys: Vec<Key>) -> [Op<ResultModeGather, Db>; 3] {
    List_pop_front!(keys, false, u64)
}

#[test]
fn pinned_ledger_empty_pop_writes_null_and_preserves_siblings() {
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let cost = &parameters.cost_model.runtime_cost_model;
    let address = coin_structure::contract::ContractAddress::default();
    let empty = ledger_empty_list();

    let root_sibling = ledger_empty_list();
    let root_context = QueryContext::new(
        ChargedState::new(StateValue::Array(
            vec![empty.clone(), root_sibling.clone()].into(),
        )),
        address,
    );
    let root_program =
        ledger_list_pop_program(vec![Key::Value(expect_checked(AlignedValue::from(0u8)))]);
    let root_result = root_context.query(&root_program, None, cost).unwrap();
    let StateValue::Array(root) = root_result.context.state.get_ref() else {
        panic!("expected root contract state")
    };
    assert!(matches!(root.get(0), Some(StateValue::Null)));
    assert_eq!(root.get(1), Some(&root_sibling));

    let owner = AlignedValue::from([1u8; 32]);
    let sibling_owner = AlignedValue::from([2u8; 32]);
    let missing_owner = AlignedValue::from([3u8; 32]);
    let mut owners: HashMap<AlignedValue, StateValue<Db>, Db> = HashMap::default();
    owners = owners.insert(owner.clone(), empty.clone());
    owners = owners.insert(sibling_owner.clone(), empty.clone());
    let unrelated_root = empty.clone();
    let nested_context = QueryContext::new(
        ChargedState::new(StateValue::Array(
            vec![unrelated_root.clone(), StateValue::Map(owners)].into(),
        )),
        address,
    );
    let nested_program = ledger_list_pop_program(vec![
        Key::Value(expect_checked(AlignedValue::from(1u8))),
        Key::Value(expect_checked(owner.clone())),
    ]);
    let nested_result = nested_context.query(&nested_program, None, cost).unwrap();
    let StateValue::Array(nested_root) = nested_result.context.state.get_ref() else {
        panic!("expected nested root contract state")
    };
    assert_eq!(nested_root.get(0), Some(&unrelated_root));
    let StateValue::Map(nested_owners) = nested_root.get(1).unwrap() else {
        panic!("expected owner Map to stay typed")
    };
    assert!(
        matches!(nested_owners.get(&owner), Some(value) if matches!(&*value, StateValue::Null))
    );
    assert!(matches!(nested_owners.get(&sibling_owner), Some(value) if &*value == &empty));

    let missing_context = nested_context.clone();
    let missing_program = ledger_list_pop_program(vec![
        Key::Value(expect_checked(AlignedValue::from(1u8))),
        Key::Value(expect_checked(missing_owner)),
    ]);
    assert!(missing_context.query(&missing_program, None, cost).is_err());
    assert_eq!(missing_context.state, nested_context.state);
}
