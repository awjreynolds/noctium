#![cfg(feature = "zkir-321")]

use base_crypto::{fab::AlignedValue, hash::HashOutput};
use coin_structure::{
    coin::{Commitment, Info as ShieldedCoinInfo, Nonce, ShieldedTokenType},
    contract::ContractAddress,
    transfer::Recipient,
};
use noctium_runtime::{Db, Instruction, Plan, check, prepare_with_context, zkir::IrSource};
use onchain_runtime::{
    context::QueryContext,
    state::{ChargedState, StateValue},
};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs, path::PathBuf};
use storage::{arena::Sp, storage::HashMap};

type StateMap = HashMap<AlignedValue, StateValue<Db>, Db>;

fn artifacts() -> PathBuf {
    env::var_os("NOCTIUM_NESTED_SHIELDED_RECEIVE_DIR")
        .map(PathBuf::from)
        .expect("set fresh NestedShieldedReceive outputs in NOCTIUM_NESTED_SHIELDED_RECEIVE_DIR")
}

fn fixture(directory: &std::path::Path) -> anyhow::Result<(Plan, IrSource)> {
    let plan: Plan = serde_json::from_slice(&fs::read(
        directory.join("NestedShieldedReceive.receive.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        directory.join("NestedShieldedReceive.receive.zkir"),
    )?)?;
    Ok((plan, circuit))
}

fn coin(nonce: u8, color: u8, value: u128) -> ShieldedCoinInfo {
    ShieldedCoinInfo {
        nonce: Nonce(HashOutput([nonce; 32])),
        type_: ShieldedTokenType(HashOutput([color; 32])),
        value,
    }
}

fn address() -> ContractAddress {
    ContractAddress(HashOutput([3; 32]))
}

fn commitment(coin: &ShieldedCoinInfo) -> Commitment {
    coin.commitment(&Recipient::Contract(address()))
}

fn inputs(owner: &[u8; 32], coin: &ShieldedCoinInfo) -> BTreeMap<String, Json> {
    BTreeMap::from([
        (
            "owner".into(),
            json!({"kind":"bytes", "values":owner.as_slice()}),
        ),
        (
            "nonce".into(),
            json!({"kind":"bytes", "values":coin.nonce.0.0.as_slice()}),
        ),
        (
            "color".into(),
            json!({"kind":"bytes", "values":coin.type_.0.0.as_slice()}),
        ),
        ("amount".into(), json!(coin.value.to_string())),
    ])
}

fn coin_map(coins: &[ShieldedCoinInfo]) -> StateMap {
    coins.iter().fold(StateMap::default(), |map, coin| {
        map.insert(
            AlignedValue::from(coin.nonce),
            StateValue::Cell(Sp::new(AlignedValue::from(coin.qualify(17)))),
        )
    })
}

fn state_with_parents(
    owner: &[u8; 32],
    parent: Option<StateMap>,
    other_owner: &[u8; 32],
    other_parent: StateMap,
) -> ChargedState<Db> {
    let mut owners = StateMap::default();
    if let Some(parent) = parent {
        owners = owners.insert(AlignedValue::from(*owner), StateValue::Map(parent));
    }
    owners = owners.insert(
        AlignedValue::from(*other_owner),
        StateValue::Map(other_parent),
    );
    ChargedState::new(StateValue::Array(vec![StateValue::Map(owners)].into()))
}

fn context(state: ChargedState<Db>, booking: Option<(Commitment, u64)>) -> QueryContext<Db> {
    let mut context = QueryContext::new(state, address());
    if let Some((commitment, index)) = booking {
        context.call_context.com_indices =
            context.call_context.com_indices.insert(commitment, index);
    }
    context
}

fn qualified(coin: &ShieldedCoinInfo, index: u64) -> StateValue<Db> {
    StateValue::Cell(Sp::new(AlignedValue::from(coin.qualify(index))))
}

#[test]
#[ignore = "requires fresh NestedShieldedReceive artifacts in NOCTIUM_NESTED_SHIELDED_RECEIVE_DIR"]
fn nested_receive_uses_booked_index_and_preserves_siblings() -> anyhow::Result<()> {
    let (plan, circuit) = fixture(&artifacts())?;
    let receive_paths = plan
        .operations
        .iter()
        .filter_map(|operation| match operation {
            Instruction::ReceiveShieldedToMap { slot, keys, .. } => Some((*slot, keys.len())),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        receive_paths,
        [(0, 1)],
        "receive path must contain its parent key only"
    );

    let owner = [0x31; 32];
    let other_owner = [0x32; 32];
    let incoming = coin(0x41, 0x51, 7);
    let sibling = coin(0x42, 0x52, 11);
    let other_owner_coin = coin(0x43, 0x53, 13);
    let source_commitment = commitment(&incoming);
    let sibling_value = qualified(&sibling, 17);
    let other_owner_value = qualified(&other_owner_coin, 17);
    let state = state_with_parents(
        &owner,
        Some(coin_map(std::slice::from_ref(&sibling))),
        &other_owner,
        coin_map(std::slice::from_ref(&other_owner_coin)),
    );

    let execution = prepare_with_context(
        &plan,
        &inputs(&owner, &incoming),
        context(state, Some((source_commitment, 42))),
        &ledger::structure::INITIAL_PARAMETERS,
    )?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    assert!(
        execution
            .after
            .effects
            .claimed_shielded_receives
            .iter()
            .any(|entry| **entry == source_commitment)
    );

    let StateValue::Array(slots) = execution.after.state.get_ref() else {
        panic!("expected native state slots")
    };
    let StateValue::Map(owners) = slots.get(0).expect("coinMaps slot exists") else {
        panic!("expected owner Map")
    };
    assert_eq!(owners.size(), 2);
    let selected_value = owners
        .get(&AlignedValue::from(owner))
        .expect("selected owner parent exists");
    let StateValue::Map(selected) = &*selected_value else {
        panic!("expected selected owner coin Map")
    };
    assert_eq!(selected.size(), 2);
    assert_eq!(
        selected.get(&AlignedValue::from(incoming.nonce)).as_deref(),
        Some(&qualified(&incoming, 42))
    );
    assert_eq!(
        selected.get(&AlignedValue::from(sibling.nonce)).as_deref(),
        Some(&sibling_value)
    );
    assert_eq!(
        owners.get(&AlignedValue::from(other_owner)).as_deref(),
        Some(&StateValue::Map(coin_map(std::slice::from_ref(
            &other_owner_coin
        ))))
    );
    assert_eq!(
        owners
            .get(&AlignedValue::from(other_owner))
            .and_then(|value| match &*value {
                StateValue::Map(coins) => coins.get(&AlignedValue::from(other_owner_coin.nonce)),
                _ => None,
            })
            .as_deref(),
        Some(&other_owner_value)
    );

    let absent_parent = state_with_parents(
        &owner,
        None,
        &other_owner,
        coin_map(std::slice::from_ref(&other_owner_coin)),
    );
    assert!(
        prepare_with_context(
            &plan,
            &inputs(&owner, &incoming),
            context(absent_parent, Some((source_commitment, 42))),
            &ledger::structure::INITIAL_PARAMETERS,
        )
        .is_err()
    );

    let duplicate_parent = coin_map(&[incoming.clone(), sibling]);
    let duplicate_state = state_with_parents(
        &owner,
        Some(duplicate_parent),
        &other_owner,
        coin_map(std::slice::from_ref(&other_owner_coin)),
    );
    assert!(
        prepare_with_context(
            &plan,
            &inputs(&owner, &incoming),
            context(duplicate_state, Some((source_commitment, 42))),
            &ledger::structure::INITIAL_PARAMETERS,
        )
        .is_err()
    );

    let missing_booking_state = state_with_parents(
        &owner,
        Some(coin_map(std::slice::from_ref(&sibling))),
        &other_owner,
        coin_map(std::slice::from_ref(&other_owner_coin)),
    );
    assert!(
        prepare_with_context(
            &plan,
            &inputs(&owner, &incoming),
            context(missing_booking_state.clone(), None),
            &ledger::structure::INITIAL_PARAMETERS,
        )
        .is_err()
    );
    let wrong_booking = commitment(&coin(0x44, 0x54, 19));
    assert!(
        prepare_with_context(
            &plan,
            &inputs(&owner, &incoming),
            context(missing_booking_state.clone(), Some((wrong_booking, 42))),
            &ledger::structure::INITIAL_PARAMETERS,
        )
        .is_err()
    );
    Ok(())
}
