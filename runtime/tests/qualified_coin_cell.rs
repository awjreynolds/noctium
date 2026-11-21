#![cfg(feature = "zkir-321")]

use base_crypto::{fab::AlignedValue, hash::HashOutput};
use coin_structure::{
    coin::{Info as ShieldedCoinInfo, Nonce, ShieldedTokenType},
    contract::ContractAddress,
    transfer::Recipient,
};
use noctium_runtime::{Plan, check, create_state, prepare_with_context, zkir::IrSource};
use onchain_runtime::{context::QueryContext, state::StateValue};
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_QUALIFIED_COIN_CELL_DIR"]
fn write_qualified_cell_uses_the_current_transaction_index() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_QUALIFIED_COIN_CELL_DIR")
            .expect("NOCTIUM_QUALIFIED_COIN_CELL_DIR"),
    );
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("QualifiedCoinCell.writeCoin.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("QualifiedCoinCell.writeCoin.zkir"),
    )?)?;
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let bytes = |byte: u8| json!({"kind": "bytes", "values": vec![byte; 32]});
    let state = create_state(
        &plan,
        &BTreeMap::from([(
            "coinSlot".into(),
            json!({"nonce": bytes(0), "color": bytes(0), "value": "0", "mtIndex": "0"}),
        )]),
    )?;
    let own = ContractAddress(HashOutput([9; 32]));
    let other = ContractAddress(HashOutput([8; 32]));
    let coin = ShieldedCoinInfo {
        nonce: Nonce(HashOutput([2; 32])),
        type_: ShieldedTokenType(HashOutput([1; 32])),
        value: 5,
    };
    let inputs = BTreeMap::from([
        ("nonce".into(), bytes(2)),
        ("color".into(), bytes(1)),
        ("amount".into(), json!("5")),
    ]);
    let context_with_booking = |recipient| {
        let mut context = QueryContext::new(state.clone(), own);
        if let Some(recipient) = recipient {
            context.call_context.com_indices = context
                .call_context
                .com_indices
                .insert(coin.commitment(&Recipient::Contract(recipient)), 42);
        }
        context
    };

    let execution = prepare_with_context(&plan, &inputs, context_with_booking(Some(own)), params)?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    let StateValue::Array(slots) = execution.after.state.get_ref() else {
        panic!("expected root state array");
    };
    let StateValue::Cell(stored) = &*slots.get(0).expect("qualified coin Cell") else {
        panic!("expected Cell state");
    };
    assert_eq!(&**stored, &AlignedValue::from(coin.qualify(42)));
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
        let context = context_with_booking(recipient);
        let error = prepare_with_context(&plan, &inputs, context.clone(), params)
            .err()
            .expect("a booking for the current contract is required");
        assert!(
            error
                .to_string()
                .contains("absent from the current transaction")
        );
        assert_eq!(context.state, state);
    }
    Ok(())
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_QUALIFIED_COIN_CELL_DIR"]
fn reset_qualified_cell_preserves_the_adjacent_slot_and_inactive_state() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_QUALIFIED_COIN_CELL_DIR")
            .expect("NOCTIUM_QUALIFIED_COIN_CELL_DIR"),
    );
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("QualifiedCoinCellReset.guardedClear.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("QualifiedCoinCellReset.guardedClear.zkir"),
    )?)?;
    let bytes = |byte: u8| json!({"kind":"bytes","values":vec![byte; 32]});
    let values = |nonce, color, amount: &str, index: &str| {
        BTreeMap::from([
            ("marker".into(), json!("37")),
            (
                "coinSlot".into(),
                json!({"nonce":bytes(nonce),"color":bytes(color),"value":amount,"mtIndex":index}),
            ),
        ])
    };
    let original = create_state(&plan, &values(2, 1, "5", "42"))?;
    let cleared = create_state(&plan, &values(0, 0, "0", "0"))?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();
    let inputs = |enabled| BTreeMap::from([("enabled".into(), json!(enabled))]);

    for (enabled, expected) in [(false, &original), (true, &cleared)] {
        let execution =
            noctium_runtime::prepare(&plan, &inputs(enabled), &original, parameters, address)?;
        let schedule = check(&execution, &circuit)
            .map_err(|error| anyhow::anyhow!("checking reset with enabled={enabled}: {error}"))?;
        assert_eq!(schedule, execution.activity_schedule);
        assert_eq!(execution.after.state.get_ref(), expected.get_ref());
    }

    let mut sealed = plan.clone();
    sealed.state[1].sealed = true;
    let error = noctium_runtime::prepare(&sealed, &inputs(true), &original, parameters, address)
        .err()
        .expect("reset must reject a sealed record Cell");
    assert!(error.to_string().contains("shielded coin Cell is sealed"));
    Ok(())
}
