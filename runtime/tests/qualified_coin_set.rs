#![cfg(feature = "zkir-321")]

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
use serde_json::json;
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
