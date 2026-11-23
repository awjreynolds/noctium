#![cfg(feature = "zkir-321")]

use anyhow::Context;
use base_crypto::{fab::AlignedValue, hash::HashOutput};
use coin_structure::{
    coin::{Info as ShieldedCoinInfo, Nonce, ShieldedTokenType},
    contract::ContractAddress,
    transfer::Recipient,
};
use noctium_runtime::{Plan, check, create_state, prepare_with_context, zkir::IrSource};
use onchain_runtime::{context::QueryContext, state::StateValue};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs::File, path::PathBuf};

fn artifacts() -> PathBuf {
    std::env::var_os("NOCTIUM_QUALIFIED_COIN_LIST_DIR")
        .map(PathBuf::from)
        .expect("NOCTIUM_QUALIFIED_COIN_LIST_DIR")
}

fn bytes(byte: u8) -> Json {
    json!({"kind": "bytes", "values": vec![byte; 32]})
}

fn inputs(nonce: u8, color: u8, amount: u64) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("nonce".into(), bytes(nonce)),
        ("color".into(), bytes(color)),
        ("amount".into(), json!(amount.to_string())),
    ])
}

fn assert_coin_list(value: &StateValue<noctium_runtime::Db>, expected: &[AlignedValue]) {
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

fn nested_inputs(owner: u8, nonce: u8, color: u8, amount: u128) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("owner".into(), bytes(owner)),
        ("nonce".into(), bytes(nonce)),
        ("color".into(), bytes(color)),
        ("amount".into(), json!(amount.to_string())),
    ])
}

fn assert_nested_coin_list(
    state: &onchain_runtime::state::ChargedState<noctium_runtime::Db>,
    plan: &Plan,
    owner: &[u8; 32],
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
    let StateValue::Map(owners) = root.get(slot).expect("coinLists state") else {
        panic!("expected owner Map");
    };
    let owner_key: AlignedValue = (*owner).into();
    let list = owners.get(&owner_key).expect("initialized owner List");
    assert_coin_list(&list, expected);
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_QUALIFIED_COIN_LIST_DIR"]
fn push_front_coin_uses_current_booking_and_preserves_list_order() -> anyhow::Result<()> {
    let directory = artifacts();
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("QualifiedCoinList.pushFrontCoin.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("QualifiedCoinList.pushFrontCoin.zkir"),
    )?)?;
    let prior_coin = ShieldedCoinInfo {
        nonce: Nonce(HashOutput([4; 32])),
        type_: ShieldedTokenType(HashOutput([5; 32])),
        value: 9,
    };
    let initial = create_state(&plan, &BTreeMap::from([("coinList".into(), json!([]))]))?;
    let own = ContractAddress(HashOutput([9; 32]));
    let other = ContractAddress(HashOutput([8; 32]));
    let coin = ShieldedCoinInfo {
        nonce: Nonce(HashOutput([2; 32])),
        type_: ShieldedTokenType(HashOutput([1; 32])),
        value: 5,
    };
    let new_inputs = inputs(2, 1, 5);
    let context_with_booking = |state, coin: &ShieldedCoinInfo, recipient| {
        let mut context = QueryContext::new(state, own);
        if let Some(recipient) = recipient {
            context.call_context.com_indices = context
                .call_context
                .com_indices
                .insert(coin.commitment(&Recipient::Contract(recipient)), 42);
        }
        context
    };

    let prior_inputs = inputs(4, 5, 9);
    let seed_context = QueryContext::new(initial.clone(), own);
    let mut seed_context = seed_context;
    seed_context.call_context.com_indices = seed_context
        .call_context
        .com_indices
        .insert(prior_coin.commitment(&Recipient::Contract(own)), 17);
    let seed = prepare_with_context(
        &plan,
        &prior_inputs,
        seed_context,
        &ledger::structure::INITIAL_PARAMETERS,
    )
    .context("seed the existing qualified coin")?;
    assert_eq!(check(&seed, &circuit)?, seed.activity_schedule);

    let seed_state = seed.after.state;
    let execution = prepare_with_context(
        &plan,
        &new_inputs,
        context_with_booking(seed_state.clone(), &coin, Some(own)),
        &ledger::structure::INITIAL_PARAMETERS,
    )
    .context("prepend the new qualified coin")?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == "coinList")
        .expect("coinList state slot");
    let StateValue::Array(root) = execution.after.state.get_ref() else {
        panic!("expected native state slots");
    };
    assert_coin_list(
        root.get(slot).expect("coinList state"),
        &[
            AlignedValue::from(coin.qualify(42)),
            AlignedValue::from(prior_coin.qualify(17)),
        ],
    );
    assert_eq!(
        execution
            .after
            .effects
            .claimed_shielded_receives
            .iter()
            .count(),
        0
    );

    for recipient in [None, Some(other)] {
        let context = context_with_booking(seed_state.clone(), &coin, recipient);
        let error = prepare_with_context(
            &plan,
            &new_inputs,
            context.clone(),
            &ledger::structure::INITIAL_PARAMETERS,
        )
        .err()
        .expect("a booking for the current contract is required");
        assert!(
            error
                .to_string()
                .contains("absent from the current transaction")
        );
        assert_eq!(context.state, seed_state);
    }
    Ok(())
}

#[test]
#[ignore = "requires fresh nested artifacts in NOCTIUM_QUALIFIED_COIN_LIST_DIR"]
fn nested_push_front_coin_uses_owner_path_and_preserves_booking_checks() -> anyhow::Result<()> {
    let directory = artifacts();
    let initialize: Plan = serde_json::from_reader(File::open(
        directory.join("NestedQualifiedCoinList.initializeOwner.impact.json"),
    )?)?;
    let initialize_circuit = IrSource::load(File::open(
        directory.join("NestedQualifiedCoinList.initializeOwner.zkir"),
    )?)?;
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("NestedQualifiedCoinList.pushCoin.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("NestedQualifiedCoinList.pushCoin.zkir"),
    )?)?;
    let push_to: Plan = serde_json::from_reader(File::open(
        directory.join("NestedQualifiedCoinList.pushCoinTo.impact.json"),
    )?)?;
    let push_to_circuit = IrSource::load(File::open(
        directory.join("NestedQualifiedCoinList.pushCoinTo.zkir"),
    )?)?;

    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let own = ContractAddress(HashOutput([9; 32]));
    let other = ContractAddress(HashOutput([8; 32]));
    let owner_a = [1; 32];
    let owner_b = [2; 32];
    let initial = create_state(&plan, &BTreeMap::from([("coinLists".into(), json!([]))]))?;

    let mut state = initial;
    for owner in [owner_a, owner_b] {
        let execution = prepare_with_context(
            &initialize,
            &BTreeMap::from([("owner".into(), bytes(owner[0]))]),
            QueryContext::new(state, own),
            parameters,
        )
        .context("initialize a nested owner List")?;
        assert_eq!(
            check(&execution, &initialize_circuit)?,
            execution.activity_schedule
        );
        state = execution.after.state;
    }
    assert_nested_coin_list(&state, &plan, &owner_a, &[]);
    assert_nested_coin_list(&state, &plan, &owner_b, &[]);

    let coin_a = ShieldedCoinInfo {
        nonce: Nonce(HashOutput([2; 32])),
        type_: ShieldedTokenType(HashOutput([1; 32])),
        value: 5,
    };
    let coin_b = ShieldedCoinInfo {
        nonce: Nonce(HashOutput([4; 32])),
        type_: ShieldedTokenType(HashOutput([1; 32])),
        value: 11,
    };
    let context_with_booking = |state, coin: &ShieldedCoinInfo, recipient, index| {
        let mut context = QueryContext::new(state, own);
        if let Some(recipient) = recipient {
            context.call_context.com_indices = context
                .call_context
                .com_indices
                .insert(coin.commitment(&Recipient::Contract(recipient)), index);
        }
        context
    };

    let first_owner_push = prepare_with_context(
        &plan,
        &nested_inputs(owner_a[0], 2, 1, 5),
        context_with_booking(state, &coin_a, Some(own), 0),
        parameters,
    )
    .context("push the first coin under owner A")?;
    assert_eq!(
        check(&first_owner_push, &circuit)?,
        first_owner_push.activity_schedule
    );

    let mut explicit_inputs = nested_inputs(owner_b[0], 4, 1, 11);
    explicit_inputs.insert("isContract".into(), json!(true));
    explicit_inputs.insert("recipient".into(), bytes(9));
    let second_owner_push = prepare_with_context(
        &push_to,
        &explicit_inputs,
        context_with_booking(first_owner_push.after.state, &coin_b, Some(own), 0),
        parameters,
    )
    .context("push an independent coin under owner B")?;
    assert_eq!(
        check(&second_owner_push, &push_to_circuit)?,
        second_owner_push.activity_schedule
    );
    state = second_owner_push.after.state;
    assert_nested_coin_list(
        &state,
        &plan,
        &owner_a,
        &[AlignedValue::from(coin_a.qualify(0))],
    );
    assert_nested_coin_list(
        &state,
        &plan,
        &owner_b,
        &[AlignedValue::from(coin_b.qualify(0))],
    );

    let coin_a_next = ShieldedCoinInfo {
        nonce: Nonce(HashOutput([3; 32])),
        type_: ShieldedTokenType(HashOutput([1; 32])),
        value: 7,
    };
    let inputs = nested_inputs(owner_a[0], 3, 1, 7);

    for recipient in [None, Some(other)] {
        let context = context_with_booking(state.clone(), &coin_a_next, recipient, 1);
        let error = prepare_with_context(&plan, &inputs, context.clone(), parameters)
            .err()
            .expect("a booking for the current contract is required");
        assert!(
            error
                .to_string()
                .contains("absent from the current transaction")
        );
        assert_eq!(context.state, state);
    }

    let execution = prepare_with_context(
        &plan,
        &inputs,
        context_with_booking(state, &coin_a_next, Some(own), 0),
        parameters,
    )
    .context("prepend the next coin under owner A")?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    assert_nested_coin_list(
        &execution.after.state,
        &plan,
        &owner_a,
        &[
            AlignedValue::from(coin_a_next.qualify(0)),
            AlignedValue::from(coin_a.qualify(0)),
        ],
    );
    assert_nested_coin_list(
        &execution.after.state,
        &plan,
        &owner_b,
        &[AlignedValue::from(coin_b.qualify(0))],
    );
    Ok(())
}
