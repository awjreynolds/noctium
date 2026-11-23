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
    std::env::var_os("NOCTIUM_TWO_PARENT_QUALIFIED_COIN_LIST_DIR")
        .map(PathBuf::from)
        .expect("NOCTIUM_TWO_PARENT_QUALIFIED_COIN_LIST_DIR")
}

fn bytes32(value: &[u8; 32]) -> Json {
    json!({"kind": "bytes", "values": value})
}

fn path_inputs(owner: &[u8; 32], bucket: &[u8; 32]) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("owner".into(), bytes32(owner)),
        ("bucket".into(), bytes32(bucket)),
    ])
}

fn push_inputs(
    owner: &[u8; 32],
    bucket: &[u8; 32],
    coin: &ShieldedCoinInfo,
) -> BTreeMap<String, Json> {
    let mut inputs = path_inputs(owner, bucket);
    inputs.insert("nonce".into(), bytes32(&coin.nonce.0.0));
    inputs.insert("color".into(), bytes32(&coin.type_.0.0));
    inputs.insert("amount".into(), json!(coin.value.to_string()));
    inputs
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

fn assert_nested_coin_list(
    state: &onchain_runtime::state::ChargedState<noctium_runtime::Db>,
    plan: &Plan,
    owner: &[u8; 32],
    bucket: &[u8; 32],
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
        panic!("expected outer Map");
    };
    let owner_key: AlignedValue = (*owner).into();
    let buckets = owners.get(&owner_key).expect("initialized owner Map");
    let StateValue::Map(buckets) = &*buckets else {
        panic!("expected nested bucket Map");
    };
    let bucket_key: AlignedValue = (*bucket).into();
    let list = buckets.get(&bucket_key).expect("initialized bucket List");
    assert_coin_list(&list, expected);
}

fn coin(nonce: u8, color: u8, value: u128) -> ShieldedCoinInfo {
    ShieldedCoinInfo {
        nonce: Nonce(HashOutput([nonce; 32])),
        type_: ShieldedTokenType(HashOutput([color; 32])),
        value,
    }
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_TWO_PARENT_QUALIFIED_COIN_LIST_DIR"]
fn nested_coin_list_push_preserves_parent_buckets_and_checks_booking() -> anyhow::Result<()> {
    let directory = artifacts();
    let initialize: Plan = serde_json::from_reader(File::open(
        directory.join("TwoParentQualifiedCoinList.initializeList.impact.json"),
    )?)?;
    let initialize_circuit = IrSource::load(File::open(
        directory.join("TwoParentQualifiedCoinList.initializeList.zkir"),
    )?)?;
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("TwoParentQualifiedCoinList.pushCoin.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("TwoParentQualifiedCoinList.pushCoin.zkir"),
    )?)?;

    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let own = ContractAddress(HashOutput([9; 32]));
    let other = ContractAddress(HashOutput([8; 32]));
    let owner_a = [1; 32];
    let owner_b = [2; 32];
    let bucket_selected = [10; 32];
    let bucket_sibling = [11; 32];
    let bucket_missing = [12; 32];
    let owner_missing = [3; 32];
    let initial = create_state(&plan, &BTreeMap::from([("coinLists".into(), json!([]))]))?;

    let mut state = initial;
    for (owner, bucket) in [
        (&owner_a, &bucket_selected),
        (&owner_a, &bucket_sibling),
        (&owner_b, &bucket_selected),
    ] {
        let execution = prepare_with_context(
            &initialize,
            &path_inputs(owner, bucket),
            QueryContext::new(state, own),
            parameters,
        )
        .context("initialize a two-parent coin List")?;
        assert_eq!(
            check(&execution, &initialize_circuit)?,
            execution.activity_schedule
        );
        state = execution.after.state;
    }

    let selected_coin = coin(2, 1, 5);
    let sibling_coin = coin(3, 1, 7);
    let other_owner_coin = coin(4, 1, 11);
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

    let mut state = state;
    for (owner, bucket, booked_coin, index) in [
        (&owner_a, &bucket_selected, &selected_coin, 31),
        (&owner_a, &bucket_sibling, &sibling_coin, 7),
        (&owner_b, &bucket_selected, &other_owner_coin, 19),
    ] {
        let execution = prepare_with_context(
            &plan,
            &push_inputs(owner, bucket, booked_coin),
            context_with_booking(state, booked_coin, Some(own), index),
            parameters,
        )
        .context("seed a selected or sibling List")?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        state = execution.after.state;
    }
    assert_nested_coin_list(
        &state,
        &plan,
        &owner_a,
        &bucket_selected,
        &[AlignedValue::from(selected_coin.qualify(31))],
    );
    assert_nested_coin_list(
        &state,
        &plan,
        &owner_a,
        &bucket_sibling,
        &[AlignedValue::from(sibling_coin.qualify(7))],
    );
    assert_nested_coin_list(
        &state,
        &plan,
        &owner_b,
        &bucket_selected,
        &[AlignedValue::from(other_owner_coin.qualify(19))],
    );

    let next_coin = coin(5, 1, 13);
    let next_inputs = push_inputs(&owner_a, &bucket_selected, &next_coin);
    for recipient in [None, Some(other)] {
        let context = context_with_booking(state.clone(), &next_coin, recipient, 42);
        let error = prepare_with_context(&plan, &next_inputs, context.clone(), parameters)
            .err()
            .expect("a current-contract booking is required");
        assert!(
            error
                .to_string()
                .contains("absent from the current transaction")
        );
        assert_eq!(context.state, state);
    }

    for (owner, bucket) in [
        (&owner_a, &bucket_missing),
        (&owner_missing, &bucket_selected),
    ] {
        let context = context_with_booking(state.clone(), &next_coin, Some(own), 42);
        let error = prepare_with_context(
            &plan,
            &push_inputs(owner, bucket, &next_coin),
            context.clone(),
            parameters,
        )
        .err()
        .expect("both Map parents must already exist");
        assert_eq!(context.state, state);
        assert!(error.to_string().contains("missing map path key"));
    }

    let execution = prepare_with_context(
        &plan,
        &next_inputs,
        context_with_booking(state, &next_coin, Some(own), 42),
        parameters,
    )
    .context("prepend under the selected owner and bucket")?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    assert_nested_coin_list(
        &execution.after.state,
        &plan,
        &owner_a,
        &bucket_selected,
        &[
            AlignedValue::from(next_coin.qualify(42)),
            AlignedValue::from(selected_coin.qualify(31)),
        ],
    );
    assert_nested_coin_list(
        &execution.after.state,
        &plan,
        &owner_a,
        &bucket_sibling,
        &[AlignedValue::from(sibling_coin.qualify(7))],
    );
    assert_nested_coin_list(
        &execution.after.state,
        &plan,
        &owner_b,
        &bucket_selected,
        &[AlignedValue::from(other_owner_coin.qualify(19))],
    );
    Ok(())
}
