#![cfg(feature = "zkir-321")]

use anyhow::Context;
use base_crypto::{fab::AlignedValue, hash::HashOutput};
use coin_structure::{
    coin::{Info, Nonce, ShieldedTokenType},
    contract::ContractAddress,
    transfer::Recipient,
};
use noctium_runtime::{
    Db, Execution, Plan, check, create_state, prepare_with_context, zkir::IrSource,
};
use onchain_runtime::{
    context::QueryContext,
    state::{ChargedState, StateValue},
};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs::File, path::PathBuf};

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_QUALIFIED_COIN_SET_DIR"]
fn qualified_coin_set_uses_current_booking_and_is_idempotent() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_QUALIFIED_COIN_SET_DIR").expect("NOCTIUM_QUALIFIED_COIN_SET_DIR"),
    );
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("QualifiedCoinSet.insertCoin.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("QualifiedCoinSet.insertCoin.zkir"),
    )?)?;
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let own = ContractAddress(HashOutput([9; 32]));
    let other = ContractAddress(HashOutput([8; 32]));
    let initial = create_state(&plan, &BTreeMap::from([("coinSet".into(), json!([]))]))?;
    let first = Info {
        nonce: Nonce(HashOutput([2; 32])),
        type_: ShieldedTokenType(HashOutput([1; 32])),
        value: 5,
    };
    let second = Info {
        nonce: Nonce(HashOutput([3; 32])),
        value: 7,
        ..first.clone()
    };

    let bytes = |value: &[u8; 32]| json!({"kind":"bytes", "values":value});
    let inputs = |coin: &Info| {
        BTreeMap::from([
            ("nonce".into(), bytes(&coin.nonce.0.0)),
            ("color".into(), bytes(&coin.type_.0.0)),
            ("amount".into(), json!(coin.value.to_string())),
        ])
    };
    let context = |state: &ChargedState<Db>,
                   coin: &Info,
                   booking: Option<(ContractAddress, u64)>|
     -> QueryContext<Db> {
        let mut context = QueryContext::new(state.clone(), own);
        if let Some((recipient, index)) = booking {
            context.call_context.com_indices = context
                .call_context
                .com_indices
                .insert(coin.commitment(&Recipient::Contract(recipient)), index);
        }
        context
    };
    let run = |state: &ChargedState<Db>, coin: &Info, index: u64| -> anyhow::Result<Execution> {
        let execution = prepare_with_context(
            &plan,
            &inputs(coin),
            context(state, coin, Some((own, index))),
            params,
        )?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        Ok(execution)
    };
    let has_member = |state: &ChargedState<Db>, coin: &Info, index: u64| -> bool {
        let StateValue::Array(slots) = state.get_ref() else {
            panic!("expected native state slots");
        };
        let slot = plan
            .state
            .iter()
            .position(|declaration| declaration.name == "coinSet")
            .expect("qualified coin Set declaration");
        let StateValue::Map(members) = &*slots.get(slot).expect("qualified coin Set") else {
            panic!("expected native Set map");
        };
        let key = AlignedValue::from(coin.qualify(index));
        assert!(key.alignment.fits(&key.value));
        matches!(members.get(&key), Some(marker) if matches!(*marker, StateValue::Null))
    };

    let first_write = run(&initial, &first, 17)?;
    assert!(has_member(&first_write.after.state, &first, 17));
    assert_eq!(
        first_write
            .after
            .effects
            .claimed_shielded_receives
            .iter()
            .count(),
        0
    );

    let second_write = run(&first_write.after.state, &second, 42)?;
    assert!(has_member(&second_write.after.state, &first, 17));
    assert!(has_member(&second_write.after.state, &second, 42));
    let StateValue::Array(slots) = second_write.after.state.get_ref() else {
        panic!("expected native state slots");
    };
    let StateValue::Map(members) = &*slots.get(0).expect("qualified coin Set") else {
        panic!("expected native Set map");
    };
    assert_eq!(members.iter().count(), 2);

    let repeated = run(&second_write.after.state, &second, 42)?;
    assert_eq!(repeated.after.state, second_write.after.state);
    assert!(has_member(&repeated.after.state, &first, 17));
    assert!(has_member(&repeated.after.state, &second, 42));

    let without_booking = context(&initial, &first, None);
    let unchanged = initial.clone();
    let error = prepare_with_context(&plan, &inputs(&first), without_booking, params)
        .err()
        .expect("Set insertion requires the current contract's commitment booking");
    assert!(
        error
            .to_string()
            .contains("absent from the current transaction")
    );
    let wrong_recipient = context(&initial, &first, Some((other, 17)));
    assert!(prepare_with_context(&plan, &inputs(&first), wrong_recipient, params).is_err());
    assert_eq!(initial, unchanged);
    Ok(())
}

fn nested_bytes(value: &[u8; 32]) -> Json {
    json!({"kind": "bytes", "values": value})
}

fn nested_coin_inputs(owner: &[u8; 32], coin: &Info) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("owner".into(), nested_bytes(owner)),
        ("nonce".into(), nested_bytes(&coin.nonce.0.0)),
        ("color".into(), nested_bytes(&coin.type_.0.0)),
        ("amount".into(), json!(coin.value.to_string())),
    ])
}

fn assert_nested_coin_set(
    state: &ChargedState<Db>,
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
        .position(|declaration| declaration.name == "coinSets")
        .expect("coinSets state slot");
    let StateValue::Map(owners) = root.get(slot).expect("coinSets state") else {
        panic!("expected owner Map");
    };
    let owner_key: AlignedValue = (*owner).into();
    let set = owners.get(&owner_key).expect("initialized owner Set");
    let StateValue::Map(members) = &*set else {
        panic!("expected nested Set Map");
    };
    assert_eq!(members.iter().count(), expected.len());
    for member in expected {
        assert!(
            members
                .get(member)
                .is_some_and(|marker| matches!(&*marker, StateValue::Null))
        );
    }
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_QUALIFIED_COIN_SET_DIR"]
fn nested_qualified_coin_set_isolated_by_owner_and_checks_bookings() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_QUALIFIED_COIN_SET_DIR").expect("NOCTIUM_QUALIFIED_COIN_SET_DIR"),
    );
    let initialize: Plan = serde_json::from_reader(File::open(
        directory.join("NestedQualifiedCoinSet.initializeOwner.impact.json"),
    )?)?;
    let initialize_circuit = IrSource::load(File::open(
        directory.join("NestedQualifiedCoinSet.initializeOwner.zkir"),
    )?)?;
    let insert: Plan = serde_json::from_reader(File::open(
        directory.join("NestedQualifiedCoinSet.insertCoin.impact.json"),
    )?)?;
    let insert_circuit = IrSource::load(File::open(
        directory.join("NestedQualifiedCoinSet.insertCoin.zkir"),
    )?)?;
    let insert_to: Plan = serde_json::from_reader(File::open(
        directory.join("NestedQualifiedCoinSet.insertCoinTo.impact.json"),
    )?)?;
    let insert_to_circuit = IrSource::load(File::open(
        directory.join("NestedQualifiedCoinSet.insertCoinTo.zkir"),
    )?)?;

    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let own = ContractAddress(HashOutput([9; 32]));
    let other = ContractAddress(HashOutput([8; 32]));
    let owner_a = [1; 32];
    let owner_b = [2; 32];
    let owner_missing = [3; 32];
    let initial = create_state(&insert, &BTreeMap::from([("coinSets".into(), json!([]))]))?;

    let mut state = initial;
    for owner in [&owner_a, &owner_b] {
        let execution = prepare_with_context(
            &initialize,
            &BTreeMap::from([("owner".into(), nested_bytes(owner))]),
            QueryContext::new(state, own),
            parameters,
        )
        .context("initialize a nested owner Set")?;
        assert_eq!(
            check(&execution, &initialize_circuit)?,
            execution.activity_schedule
        );
        state = execution.after.state;
    }
    assert_nested_coin_set(&state, &insert, &owner_a, &[]);
    assert_nested_coin_set(&state, &insert, &owner_b, &[]);

    let coin_a = Info {
        nonce: Nonce(HashOutput([2; 32])),
        type_: ShieldedTokenType(HashOutput([1; 32])),
        value: 5,
    };
    let coin_b = Info {
        nonce: Nonce(HashOutput([4; 32])),
        value: 11,
        ..coin_a.clone()
    };
    let coin_a_next = Info {
        nonce: Nonce(HashOutput([3; 32])),
        value: 7,
        ..coin_a.clone()
    };
    let context_with_booking =
        |state: &ChargedState<Db>, coin: &Info, booking: Option<(ContractAddress, u64)>| {
            let mut context = QueryContext::new(state.clone(), own);
            if let Some((recipient, index)) = booking {
                context.call_context.com_indices = context
                    .call_context
                    .com_indices
                    .insert(coin.commitment(&Recipient::Contract(recipient)), index);
            }
            context
        };

    let owner_a_insert = prepare_with_context(
        &insert,
        &nested_coin_inputs(&owner_a, &coin_a),
        context_with_booking(&state, &coin_a, Some((own, 41))),
        parameters,
    )
    .context("insert a booked coin under owner A")?;
    assert_eq!(
        check(&owner_a_insert, &insert_circuit)?,
        owner_a_insert.activity_schedule
    );

    let mut state = owner_a_insert.after.state;
    for (owner, coin, index) in [(&owner_b, &coin_b, 42), (&owner_a, &coin_a_next, 43)] {
        let mut inputs = nested_coin_inputs(owner, coin);
        inputs.insert("isContract".into(), json!(true));
        inputs.insert("recipient".into(), nested_bytes(&own.0.0));
        let execution = prepare_with_context(
            &insert_to,
            &inputs,
            context_with_booking(&state, coin, Some((own, index))),
            parameters,
        )
        .with_context(|| format!("insert booked coin {index} for owner {}", owner[0]))?;
        assert_eq!(
            check(&execution, &insert_to_circuit)?,
            execution.activity_schedule
        );
        state = execution.after.state;
    }

    assert_nested_coin_set(
        &state,
        &insert,
        &owner_a,
        &[
            AlignedValue::from(coin_a.qualify(41)),
            AlignedValue::from(coin_a_next.qualify(43)),
        ],
    );
    assert_nested_coin_set(
        &state,
        &insert,
        &owner_b,
        &[AlignedValue::from(coin_b.qualify(42))],
    );

    for booking in [None, Some((other, 44))] {
        let context = context_with_booking(&state, &coin_a_next, booking);
        let error = prepare_with_context(
            &insert,
            &nested_coin_inputs(&owner_a, &coin_a_next),
            context.clone(),
            parameters,
        )
        .err()
        .expect("a matching booking is required");
        assert!(
            error
                .to_string()
                .contains("absent from the current transaction")
        );
        assert_eq!(context.state, state);
    }

    let missing_owner_context = context_with_booking(&state, &coin_a, Some((own, 41)));
    let error = prepare_with_context(
        &insert,
        &nested_coin_inputs(&owner_missing, &coin_a),
        missing_owner_context.clone(),
        parameters,
    )
    .err()
    .expect("the owner Set must be initialized before insertion");
    assert!(error.to_string().contains("missing map path key"));
    assert_eq!(missing_owner_context.state, state);

    Ok(())
}
