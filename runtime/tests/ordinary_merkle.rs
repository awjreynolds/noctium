#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Db, Execution, Plan, check, create_state, field_decimal, prepare, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value, json};
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::fab::AlignedValueExt;

fn fixture(contract: &str, entry: &str) -> (Plan, IrSource) {
    let artifacts = PathBuf::from(std::env::var_os("NOCTIUM_NATIVE_TEST_ARTIFACTS").unwrap());
    let prefix = format!("{contract}.{entry}");
    let plan =
        serde_json::from_slice(&fs::read(artifacts.join(format!("{prefix}.impact.json"))).unwrap())
            .unwrap();
    let relation =
        IrSource::load(fs::File::open(artifacts.join(format!("{prefix}.zkir"))).unwrap()).unwrap();
    (plan, relation)
}

fn assert_tree_state(state: &ChargedState<Db>, expected_cursor: usize, expected_root: &str) {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected contract state array")
    };
    let StateValue::Array(node) = slots.get(0).unwrap() else {
        panic!("expected Merkle state array")
    };
    let StateValue::BoundedMerkleTree(tree) = node.get(0).unwrap() else {
        panic!("expected native tree")
    };
    let StateValue::Cell(cursor) = node.get(1).unwrap() else {
        panic!("expected Merkle cursor")
    };
    let mut cursor_fields = Vec::new();
    cursor.value_only_field_repr(&mut cursor_fields);
    assert_eq!(cursor_fields.len(), 1);
    assert_eq!(field_decimal(cursor_fields[0]), expected_cursor.to_string());
    assert_eq!(field_decimal(tree.root().unwrap().0), expected_root);
}

#[test]
#[ignore = "requires fresh Lean output set via NOCTIUM_NATIVE_TEST_ARTIFACTS"]
fn ordinary_merkle_appends_match_compact_and_reset_exactly() {
    let address = coin_structure::contract::ContractAddress::default();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let run = |plan: &Plan,
               circuit: &IrSource,
               args: BTreeMap<String, Value>,
               state: &ChargedState<Db>| {
        let execution = prepare(plan, &args, state, params, address).unwrap();
        check(&execution, circuit).unwrap();
        execution
    };
    let (append, circuit) = fixture("NativeMerkleTree", "append");
    let initial = create_state(&append, &BTreeMap::from([("claims".into(), json!([]))])).unwrap();
    let (full_status, full_circuit) = fixture("NativeMerkleTree", "fullStatus");
    let read = |state: &ChargedState<Db>| -> Execution {
        run(&full_status, &full_circuit, BTreeMap::new(), state)
    };
    assert_eq!(read(&initial).returns_json()["fullStatus"], false);
    let mut state = initial.clone();
    let args = |byte| {
        BTreeMap::from([(
            "leafHash".into(),
            json!({"kind":"bytes","values":vec![byte;32]}),
        )])
    };

    // Root sequence from the pinned Compact OrdinaryMerkle fixture.
    let roots = [
        "17029979906787068148615464077443109129720490673751283300379954364685288014954",
        "45137749480565895385758122683212244915529195091359138341472597836969923504049",
        "25117124299835895250907896203532552792670032528542297288772531067357116679580",
        "47912772248769352372635417155431636398353714911972954164866311838310133535619",
    ];
    for (index, expected_root) in roots.into_iter().enumerate() {
        let call = run(&append, &circuit, args(index + 1), &state);
        assert_eq!(call.returns_json()["fullStatus"], index == 3);
        state = call.after.state;
        assert_tree_state(&state, index + 1, expected_root);
    }
    let mut full = read(&state);
    assert_eq!(full.returns_json()["fullStatus"], true);
    full.preimage.public_transcript_outputs[0] = 0u64.into();
    assert!(check(&full, &full_circuit).is_err());
    let Err(error) = prepare(&append, &args(5), &state, params, address) else {
        panic!("the fifth append must fail")
    };
    assert!(error.to_string().contains("MerkleTree is full"));

    let (check_current, check_circuit) = fixture("NativeMerkleTree", "checkCurrent");
    let read_root = |active, expected, state: &ChargedState<Db>| {
        run(
            &check_current,
            &check_circuit,
            BTreeMap::from([
                ("active".into(), json!(active)),
                ("expectedRoot".into(), json!(expected)),
            ]),
            state,
        )
    };
    let mut matching_empty = read_root(true, "0", &initial);
    assert_eq!(matching_empty.returns_json()["isValid"], true);
    assert_eq!(matching_empty.after.state, initial);
    assert_eq!(
        matching_empty.preimage.public_transcript_outputs[0],
        1u64.into()
    );
    matching_empty.preimage.public_transcript_outputs[0] = 0u64.into();
    assert!(check(&matching_empty, &check_circuit).is_err());
    assert_eq!(
        read_root(true, "1", &initial).returns_json()["isValid"],
        false
    );
    let skipped = read_root(false, "0", &initial);
    assert_eq!(skipped.returns_json()["isValid"], false);
    assert_eq!(skipped.after.state, initial);

    let (append_and_check, append_check_circuit) = fixture("NativeMerkleTree", "appendAndCheck");
    let append_check = |expected| {
        let mut inputs = args(1);
        inputs.insert("expectedRoot".into(), json!(expected));
        run(&append_and_check, &append_check_circuit, inputs, &initial)
    };
    let appended = append_check(roots[0]);
    assert_eq!(appended.returns_json()["isValid"], true);
    assert_eq!(append_check("0").returns_json()["isValid"], false);
    let unchanged = read_root(true, roots[0], &appended.after.state);
    assert_eq!(unchanged.returns_json()["isValid"], true);
    assert_eq!(unchanged.after.state, appended.after.state);
    let stale = read_root(true, "0", &appended.after.state);
    assert_eq!(stale.returns_json()["isValid"], false);
    assert_eq!(stale.after.state, appended.after.state);
    let skipped = read_root(false, roots[0], &appended.after.state);
    assert_eq!(skipped.returns_json()["isValid"], false);
    assert_eq!(skipped.after.state, appended.after.state);

    let (reset, reset_circuit) = fixture("NativeMerkleTree", "resetAndCheck");
    let reset_result = run(&reset, &reset_circuit, BTreeMap::new(), &state);
    assert_eq!(reset_result.returns_json()["resetStatus"], false);
    assert_eq!(reset_result.after.state, initial);
}

#[test]
#[ignore = "requires fresh Lean output set via NOCTIUM_NATIVE_TEST_ARTIFACTS"]
fn indexed_merkle_writes_match_compact_and_keep_the_highest_cursor() {
    let hash = fixture("NativeMerkleIndexed", "writeHashIndex");
    let field = fixture("NativeMerkleIndexed", "writeFieldIndex");
    let guarded = fixture("NativeMerkleIndexed", "guardedHashIndex");
    let digest = |byte: u8| json!({"kind":"bytes","values":vec![byte;32]});
    let inputs = |position: u64, name: &str, value| {
        BTreeMap::from([
            ("position".into(), json!(position.to_string())),
            (name.into(), value),
        ])
    };
    let mut state = create_state(&hash.0, &BTreeMap::from([("claims".into(), json!([]))])).unwrap();
    let address = coin_structure::contract::ContractAddress::default();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let cases = [
        (
            &hash,
            inputs(2, "leafHash", digest(1)),
            3,
            "51991420613583242718883085486858320823211002246065564903180331239782599797141",
        ),
        (
            &field,
            inputs(0, "leaf", json!("256")),
            3,
            "35353483718869055914222302344647120627768057225804816879361904442332651631283",
        ),
        (
            &hash,
            inputs(3, "leafHash", digest(2)),
            4,
            "15993209544944421617169220437185678647295688860149730429255710766206171374113",
        ),
        (
            &field,
            inputs(
                2,
                "leaf",
                json!(
                    "52435875175126190479447740508185965837690552500527637822603658699938581184512"
                ),
            ),
            4,
            "47033499625330606981492581121965573308439173789648377028248552381297333663326",
        ),
        (
            &field,
            inputs(0, "leaf", json!("0")),
            4,
            "52111365062746240321013939218221021836800885542874228729907370631401335031010",
        ),
    ];
    for ((plan, relation), args, cursor, root) in cases {
        let execution = prepare(plan, &args, &state, params, address).unwrap();
        check(&execution, relation).unwrap();
        assert_eq!(execution.returns_json()["fullStatus"], cursor == 4);
        state = execution.after.state;
        assert_tree_state(&state, cursor, root);
    }
    for index in [4, u64::MAX] {
        let args = inputs(index, "leafHash", digest(3));
        assert!(prepare(&hash.0, &args, &state, params, address).is_err());
    }
    let mut args = inputs(u64::MAX, "leafHash", digest(3));
    args.insert("active".into(), json!(false));
    let inactive = prepare(&guarded.0, &args, &state, params, address).unwrap();
    check(&inactive, &guarded.1).unwrap();
    assert_eq!(inactive.after.state, state);
}
