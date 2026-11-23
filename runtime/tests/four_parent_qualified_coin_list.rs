#![cfg(feature = "zkir-321")]

use anyhow::Context;
use base_crypto::{fab::AlignedValue, hash::HashOutput};
use coin_structure::{
    coin::{Info as ShieldedCoinInfo, Nonce, ShieldedTokenType},
    contract::ContractAddress,
    transfer::Recipient,
};
use noctium_runtime::{Db, Plan, check, create_state, prepare_with_context, zkir::IrSource};
use onchain_runtime::context::QueryContext;
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs::File, path::PathBuf};

fn artifacts() -> PathBuf {
    std::env::var_os("NOCTIUM_FOUR_PARENT_QUALIFIED_COIN_LIST_DIR")
        .map(PathBuf::from)
        .expect("NOCTIUM_FOUR_PARENT_QUALIFIED_COIN_LIST_DIR")
}

fn deep_coin_list_artifacts() -> PathBuf {
    std::env::var_os("NOCTIUM_DEEP_BOOKED_COIN_LIST_DIR")
        .map(PathBuf::from)
        .expect("NOCTIUM_DEEP_BOOKED_COIN_LIST_DIR")
}

fn bytes32(value: &[u8; 32]) -> Json {
    json!({"kind": "bytes", "values": value})
}

fn path_inputs(
    first: &[u8; 32],
    second: &[u8; 32],
    third: &[u8; 32],
    fourth: &[u8; 32],
) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("first".into(), bytes32(first)),
        ("second".into(), bytes32(second)),
        ("third".into(), bytes32(third)),
        ("fourth".into(), bytes32(fourth)),
    ])
}

fn initialization_inputs(
    first: &[u8; 32],
    second: &[u8; 32],
    third: &[u8; 32],
    fourth: &[u8; 32],
    sibling_third: &[u8; 32],
    sibling_fourth: &[u8; 32],
) -> BTreeMap<String, Json> {
    let mut inputs = path_inputs(first, second, third, fourth);
    inputs.insert("siblingThird".into(), bytes32(sibling_third));
    inputs.insert("siblingFourth".into(), bytes32(sibling_fourth));
    inputs
}

fn push_inputs(
    first: &[u8; 32],
    second: &[u8; 32],
    third: &[u8; 32],
    fourth: &[u8; 32],
    coin: &ShieldedCoinInfo,
) -> BTreeMap<String, Json> {
    let mut inputs = path_inputs(first, second, third, fourth);
    inputs.insert("nonce".into(), bytes32(&coin.nonce.0.0));
    inputs.insert("color".into(), bytes32(&coin.type_.0.0));
    inputs.insert("amount".into(), json!(coin.value.to_string()));
    inputs
}

fn push_to_inputs(
    first: &[u8; 32],
    second: &[u8; 32],
    third: &[u8; 32],
    fourth: &[u8; 32],
    coin: &ShieldedCoinInfo,
    recipient: ContractAddress,
) -> BTreeMap<String, Json> {
    let mut inputs = push_inputs(first, second, third, fourth, coin);
    inputs.insert("isContract".into(), json!(true));
    inputs.insert("recipient".into(), bytes32(&recipient.0.0));
    inputs
}

fn context_with_booking(
    state: ChargedState<Db>,
    own: ContractAddress,
    coin: &ShieldedCoinInfo,
    recipient: Option<ContractAddress>,
    index: u64,
) -> QueryContext<Db> {
    let mut context = QueryContext::new(state, own);
    if let Some(recipient) = recipient {
        context.call_context.com_indices = context
            .call_context
            .com_indices
            .insert(coin.commitment(&Recipient::Contract(recipient)), index);
    }
    context
}

fn assert_coin_list(value: &StateValue<Db>, expected: &[AlignedValue]) {
    let StateValue::Array(node) = value else {
        panic!("expected native List array");
    };
    assert_eq!(node.len(), 3);
    let StateValue::Cell(length) = node.get(2).unwrap() else {
        panic!("expected List length Cell");
    };
    assert_eq!(**length, AlignedValue::from(expected.len() as u64));
    if let Some((head, tail)) = expected.split_first() {
        let StateValue::Cell(value) = node.get(0).unwrap() else {
            panic!("expected qualified coin head");
        };
        assert_eq!(**value, *head);
        assert_coin_list(node.get(1).unwrap(), tail);
    } else {
        assert!(matches!(node.get(0), Some(StateValue::Null)));
        assert!(matches!(node.get(1), Some(StateValue::Null)));
    }
}

fn map_entry(value: &StateValue<Db>, key: &[u8; 32]) -> StateValue<Db> {
    let StateValue::Map(entries) = value else {
        panic!("expected nested Map");
    };
    let key: AlignedValue = (*key).into();
    (*entries.get(&key).expect("initialized Map path key")).clone()
}

fn assert_nested_coin_list(
    state: &ChargedState<Db>,
    plan: &Plan,
    keys: [&[u8; 32]; 4],
    expected: &[AlignedValue],
) {
    let StateValue::Array(root) = state.get_ref() else {
        panic!("expected native state slots");
    };
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == "coinLists")
        .expect("coinLists state slot");
    let mut value = root.get(slot).expect("coinLists state").clone();
    for key in keys {
        value = map_entry(&value, key);
    }
    assert_coin_list(&value, expected);
}

fn coin(nonce: u8, color: u8, value: u128) -> ShieldedCoinInfo {
    ShieldedCoinInfo {
        nonce: Nonce(HashOutput([nonce; 32])),
        type_: ShieldedTokenType(HashOutput([color; 32])),
        value,
    }
}

fn deep_coin_list_push_inputs(
    owner: &[u8; 32],
    group: &[u8; 32],
    leaf: &[u8; 32],
    coin: &ShieldedCoinInfo,
) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("owner".into(), bytes32(owner)),
        ("group".into(), bytes32(group)),
        ("leaf".into(), bytes32(leaf)),
        ("nonce".into(), bytes32(&coin.nonce.0.0)),
        ("color".into(), bytes32(&coin.type_.0.0)),
        ("amount".into(), json!(coin.value.to_string())),
    ])
}

fn deep_coin_list_at(
    state: &ChargedState<Db>,
    plan: &Plan,
    owner: &[u8; 32],
    group: &[u8; 32],
    leaf: &[u8; 32],
) -> StateValue<Db> {
    let StateValue::Array(root) = state.get_ref() else {
        panic!("expected native state slots");
    };
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == "coinLists")
        .expect("coinLists state slot");
    let mut value = root.get(slot).expect("coinLists state").clone();
    let mut keys = Vec::with_capacity(13);
    keys.push(owner);
    keys.extend(std::iter::repeat(group).take(11));
    keys.push(leaf);
    for key in keys {
        value = map_entry(&value, key);
    }
    value
}

fn deep_coin_list_leaf_exists(
    state: &ChargedState<Db>,
    plan: &Plan,
    owner: &[u8; 32],
    group: &[u8; 32],
    leaf: &[u8; 32],
) -> bool {
    let StateValue::Array(root) = state.get_ref() else {
        panic!("expected native state slots");
    };
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == "coinLists")
        .expect("coinLists state slot");
    let mut value = root.get(slot).expect("coinLists state").clone();
    let mut keys = Vec::with_capacity(12);
    keys.push(owner);
    keys.extend(std::iter::repeat(group).take(11));
    for key in keys {
        value = map_entry(&value, key);
    }
    let StateValue::Map(leaves) = &value else {
        panic!("expected final parent Map");
    };
    let leaf_key: AlignedValue = (*leaf).into();
    leaves.contains_key(&leaf_key)
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_FOUR_PARENT_QUALIFIED_COIN_LIST_DIR"]
fn four_parent_coin_list_preserves_booking_order_and_sibling_paths() -> anyhow::Result<()> {
    let directory = artifacts();
    let initialize: Plan = serde_json::from_reader(File::open(
        directory.join("FourParentQualifiedCoinList.initializePaths.impact.json"),
    )?)?;
    let initialize_circuit = IrSource::load(File::open(
        directory.join("FourParentQualifiedCoinList.initializePaths.zkir"),
    )?)?;
    let plan_path = directory.join("FourParentQualifiedCoinList.pushCoin.impact.json");
    let plan: Plan = serde_json::from_reader(File::open(&plan_path)?)?;
    let circuit = IrSource::load(File::open(
        directory.join("FourParentQualifiedCoinList.pushCoin.zkir"),
    )?)?;
    let push_to: Plan = serde_json::from_reader(File::open(
        directory.join("FourParentQualifiedCoinList.pushCoinTo.impact.json"),
    )?)?;
    let push_to_circuit = IrSource::load(File::open(
        directory.join("FourParentQualifiedCoinList.pushCoinTo.zkir"),
    )?)?;

    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let own = ContractAddress(HashOutput([9; 32]));
    let explicit_recipient = ContractAddress(HashOutput([8; 32]));
    let first = [1; 32];
    let second = [2; 32];
    let third = [3; 32];
    let fourth = [4; 32];
    let sibling_third = [5; 32];
    let sibling_fourth = [6; 32];
    let missing_first = [7; 32];
    let missing_third = [8; 32];
    let missing_fourth = [9; 32];
    let initial = create_state(&plan, &BTreeMap::from([("coinLists".into(), json!([]))]))?;

    let initialized = prepare_with_context(
        &initialize,
        &initialization_inputs(
            &first,
            &second,
            &third,
            &fourth,
            &sibling_third,
            &sibling_fourth,
        ),
        QueryContext::new(initial, own),
        parameters,
    )
    .context("initialize three depth-four List leaves")?;
    assert_eq!(
        check(&initialized, &initialize_circuit)?,
        initialized.activity_schedule
    );
    let state = initialized.after.state;

    let selected_coin = coin(2, 1, 5);
    let sibling_fourth_coin = coin(3, 1, 7);
    let sibling_third_coin = coin(4, 1, 11);
    let mut state = state;
    for (path, booked_coin, index) in [
        ([&first, &second, &third, &fourth], &selected_coin, 31),
        (
            [&first, &second, &third, &sibling_fourth],
            &sibling_fourth_coin,
            7,
        ),
        (
            [&first, &second, &sibling_third, &fourth],
            &sibling_third_coin,
            19,
        ),
    ] {
        let execution = prepare_with_context(
            &plan,
            &push_inputs(path[0], path[1], path[2], path[3], booked_coin),
            context_with_booking(state, own, booked_coin, Some(own), index),
            parameters,
        )
        .context("seed a selected or sibling depth-four List")?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        state = execution.after.state;
    }

    assert_nested_coin_list(
        &state,
        &plan,
        [&first, &second, &third, &fourth],
        &[AlignedValue::from(selected_coin.qualify(31))],
    );
    assert_nested_coin_list(
        &state,
        &plan,
        [&first, &second, &third, &sibling_fourth],
        &[AlignedValue::from(sibling_fourth_coin.qualify(7))],
    );
    assert_nested_coin_list(
        &state,
        &plan,
        [&first, &second, &sibling_third, &fourth],
        &[AlignedValue::from(sibling_third_coin.qualify(19))],
    );

    let next_coin = coin(5, 1, 13);
    let explicit_inputs = push_to_inputs(
        &first,
        &second,
        &third,
        &fourth,
        &next_coin,
        explicit_recipient,
    );
    let explicit_push = prepare_with_context(
        &push_to,
        &explicit_inputs,
        context_with_booking(state.clone(), own, &next_coin, Some(explicit_recipient), 42),
        parameters,
    )
    .context("prepend a coin booked to the explicit contract recipient")?;
    assert_eq!(
        check(&explicit_push, &push_to_circuit)?,
        explicit_push.activity_schedule
    );
    state = explicit_push.after.state;
    assert_nested_coin_list(
        &state,
        &plan,
        [&first, &second, &third, &fourth],
        &[
            AlignedValue::from(next_coin.qualify(42)),
            AlignedValue::from(selected_coin.qualify(31)),
        ],
    );
    assert_nested_coin_list(
        &state,
        &plan,
        [&first, &second, &third, &sibling_fourth],
        &[AlignedValue::from(sibling_fourth_coin.qualify(7))],
    );
    assert_nested_coin_list(
        &state,
        &plan,
        [&first, &second, &sibling_third, &fourth],
        &[AlignedValue::from(sibling_third_coin.qualify(19))],
    );

    let missing_booking_coin = coin(6, 1, 17);
    let implicit_inputs = push_inputs(&first, &second, &third, &fourth, &missing_booking_coin);
    for recipient in [None, Some(explicit_recipient)] {
        let context =
            context_with_booking(state.clone(), own, &missing_booking_coin, recipient, 53);
        let error = prepare_with_context(&plan, &implicit_inputs, context.clone(), parameters)
            .err()
            .expect("implicit push requires a booking for the current contract");
        assert!(
            error
                .to_string()
                .contains("absent from the current transaction")
        );
        assert_eq!(context.state, state);
    }

    let explicit_unbooked_coin = coin(7, 1, 19);
    let explicit_unbooked_inputs = push_to_inputs(
        &first,
        &second,
        &third,
        &fourth,
        &explicit_unbooked_coin,
        explicit_recipient,
    );
    for booked_recipient in [None, Some(own)] {
        let context = context_with_booking(
            state.clone(),
            own,
            &explicit_unbooked_coin,
            booked_recipient,
            54,
        );
        let error = prepare_with_context(
            &push_to,
            &explicit_unbooked_inputs,
            context.clone(),
            parameters,
        )
        .err()
        .expect("explicit recipient must match a transaction booking");
        assert!(
            error
                .to_string()
                .contains("absent from the current transaction")
        );
        assert_eq!(context.state, state);
    }

    let missing_path_coin = coin(8, 1, 23);
    for path in [
        [&first, &second, &third, &missing_fourth],
        [&first, &second, &missing_third, &fourth],
        [&missing_first, &second, &third, &fourth],
    ] {
        let inputs = push_inputs(path[0], path[1], path[2], path[3], &missing_path_coin);
        let context = context_with_booking(state.clone(), own, &missing_path_coin, Some(own), 55);
        let error = prepare_with_context(&plan, &inputs, context.clone(), parameters)
            .err()
            .expect("every Map parent and the List leaf must be initialized");
        assert!(error.to_string().contains("missing map path key"));
        assert_eq!(context.state, state);
    }

    Ok(())
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_DEEP_BOOKED_COIN_LIST_DIR"]
fn thirteen_parent_coin_list_preserves_booking_order_and_rejects_fourteen() -> anyhow::Result<()> {
    let directory = deep_coin_list_artifacts();
    let initialize: Plan = serde_json::from_reader(File::open(
        directory.join("DeepBookedCoinListBoundary.initializePaths.impact.json"),
    )?)?;
    let initialize_circuit = IrSource::load(File::open(
        directory.join("DeepBookedCoinListBoundary.initializePaths.zkir"),
    )?)?;
    let plan_path = directory.join("DeepBookedCoinListBoundary.pushCoin.impact.json");
    let raw_plan: Json = serde_json::from_reader(File::open(&plan_path)?)?;
    let operation = raw_plan["operations"]
        .as_array()
        .expect("native operation array")
        .iter()
        .find(|operation| operation["op"] == "listPushFrontCoin")
        .expect("qualified coin List push operation");
    assert_eq!(
        operation["keys"].as_array().expect("native Map path").len(),
        13,
        "emitted List push selects a 13-parent path"
    );
    let plan: Plan = serde_json::from_value(raw_plan.clone())?;
    let circuit = IrSource::load(File::open(
        directory.join("DeepBookedCoinListBoundary.pushCoin.zkir"),
    )?)?;

    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let own = ContractAddress(HashOutput([9; 32]));
    let wrong_contract = ContractAddress(HashOutput([8; 32]));
    let owner = [1; 32];
    let group = [2; 32];
    let leaf = [3; 32];
    let sibling_leaf = [4; 32];
    let absent_leaf = [5; 32];
    let initial = create_state(&plan, &BTreeMap::from([("coinLists".into(), json!([]))]))?;

    let initialized = prepare_with_context(
        &initialize,
        &BTreeMap::from([
            ("owner".into(), bytes32(&owner)),
            ("group".into(), bytes32(&group)),
            ("leaf".into(), bytes32(&leaf)),
            ("siblingLeaf".into(), bytes32(&sibling_leaf)),
        ]),
        QueryContext::new(initial, own),
        parameters,
    )
    .context("initialize selected and sibling thirteen-parent Lists")?;
    assert_eq!(
        check(&initialized, &initialize_circuit).context("check the initializer preimage")?,
        initialized.activity_schedule
    );
    let mut state = initialized.after.state;

    let selected_coin = coin(2, 1, 5);
    let sibling_coin = coin(3, 1, 7);
    for (leaf_key, booked_coin, index) in [
        (&leaf, &selected_coin, 31),
        (&sibling_leaf, &sibling_coin, 7),
    ] {
        let execution = prepare_with_context(
            &plan,
            &deep_coin_list_push_inputs(&owner, &group, leaf_key, booked_coin),
            context_with_booking(state, own, booked_coin, Some(own), index),
            parameters,
        )
        .context("seed a selected or sibling thirteen-parent List")?;
        assert_eq!(
            check(&execution, &circuit).context("check the prepend preimage")?,
            execution.activity_schedule
        );
        state = execution.after.state;
    }
    assert_coin_list(
        &deep_coin_list_at(&state, &plan, &owner, &group, &leaf),
        &[AlignedValue::from(selected_coin.qualify(31))],
    );
    assert_coin_list(
        &deep_coin_list_at(&state, &plan, &owner, &group, &sibling_leaf),
        &[AlignedValue::from(sibling_coin.qualify(7))],
    );

    let next_coin = coin(4, 1, 11);
    let execution = prepare_with_context(
        &plan,
        &deep_coin_list_push_inputs(&owner, &group, &leaf, &next_coin),
        context_with_booking(state.clone(), own, &next_coin, Some(own), 42),
        parameters,
    )
    .context("prepend a self-booked coin at thirteen Map parents")?;
    assert_eq!(
        check(&execution, &circuit).context("check the prepend preimage")?,
        execution.activity_schedule
    );
    state = execution.after.state;
    assert_coin_list(
        &deep_coin_list_at(&state, &plan, &owner, &group, &leaf),
        &[
            AlignedValue::from(next_coin.qualify(42)),
            AlignedValue::from(selected_coin.qualify(31)),
        ],
    );
    assert_coin_list(
        &deep_coin_list_at(&state, &plan, &owner, &group, &sibling_leaf),
        &[AlignedValue::from(sibling_coin.qualify(7))],
    );

    let rejected_coin = coin(5, 1, 13);
    for recipient in [None, Some(wrong_contract)] {
        let context = context_with_booking(state.clone(), own, &rejected_coin, recipient, 53);
        let error = prepare_with_context(
            &plan,
            &deep_coin_list_push_inputs(&owner, &group, &leaf, &rejected_coin),
            context.clone(),
            parameters,
        )
        .err()
        .expect("the selected List requires a current-contract booking");
        assert!(
            error
                .to_string()
                .contains("absent from the current transaction")
        );
        assert_eq!(context.state, state);
    }

    let missing_parent_coin = coin(6, 1, 17);
    let missing_parent_context =
        context_with_booking(state.clone(), own, &missing_parent_coin, Some(own), 54);
    let missing_parent_error = prepare_with_context(
        &plan,
        &deep_coin_list_push_inputs(&owner, &group, &absent_leaf, &missing_parent_coin),
        missing_parent_context.clone(),
        parameters,
    )
    .err()
    .expect("the final Map parent key must already exist");
    assert!(
        missing_parent_error
            .to_string()
            .contains("missing map path key")
    );
    assert_eq!(missing_parent_context.state, state);
    assert!(!deep_coin_list_leaf_exists(
        &state,
        &plan,
        &owner,
        &group,
        &absent_leaf,
    ));

    let mut too_deep_json = raw_plan;
    let too_deep_operation = too_deep_json["operations"]
        .as_array_mut()
        .expect("native operation array")
        .iter_mut()
        .find(|operation| operation["op"] == "listPushFrontCoin")
        .expect("qualified coin List push operation");
    too_deep_operation["keys"]
        .as_array_mut()
        .expect("native Map path")
        .push(json!({
            "alignment": "bytes32",
            "expression": {"tag": "reference", "name": "group"}
        }));
    let too_deep_plan: Plan = serde_json::from_value(too_deep_json)?;
    let too_deep_coin = coin(7, 1, 19);
    let too_deep_error = prepare_with_context(
        &too_deep_plan,
        &deep_coin_list_push_inputs(&owner, &group, &leaf, &too_deep_coin),
        context_with_booking(state, own, &too_deep_coin, Some(own), 55),
        parameters,
    )
    .err()
    .expect("native Plans must reject fourteen Map parents");
    assert!(
        too_deep_error
            .to_string()
            .contains("supports at most thirteen parent keys")
    );
    Ok(())
}
