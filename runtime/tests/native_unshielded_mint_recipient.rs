#![cfg(feature = "zkir-321")]

use base_crypto::hash::HashOutput;
use coin_structure::{
    coin::{PublicAddress, TokenType, UnshieldedTokenType, UserAddress},
    contract::ContractAddress,
};
use noctium_runtime::{Plan, check, create_state, prepare_with_context, zkir::IrSource};
use onchain_runtime::context::{ClaimedUnshieldedSpendsKey, QueryContext};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs, path::PathBuf};

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

#[test]
#[ignore = "requires fresh Lean output in NOCTIUM_UNSHIELDED_MINT_RECIPIENT_DIR"]
fn recipient_mint_returns_color_and_credits_only_contract_self() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_UNSHIELDED_MINT_RECIPIENT_DIR")
            .expect("NOCTIUM_UNSHIELDED_MINT_RECIPIENT_DIR"),
    );
    let plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join("NativeUnshieldedMintRecipient.mint.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        directory.join("NativeUnshieldedMintRecipient.mint.zkir"),
    )?)?;

    let params = &ledger::structure::INITIAL_PARAMETERS;
    let domain = HashOutput(std::array::from_fn(|index| (index + 1) as u8));
    let own = ContractAddress(HashOutput([9; 32]));
    let context = QueryContext::new(create_state(&plan, &BTreeMap::new())?, own);
    let amount = 7u64;
    let expected_color = HashOutput([
        0xd1, 0x25, 0x5d, 0x23, 0xad, 0xb5, 0xb1, 0x8d, 0x3f, 0x55, 0x8f, 0x31, 0xfe, 0xfb, 0x9d,
        0x06, 0xc1, 0x8e, 0x38, 0xf7, 0x71, 0xd0, 0x50, 0x6c, 0x24, 0x6f, 0x59, 0x98, 0x3d, 0x6d,
        0x9d, 0xa7,
    ]);
    let token = TokenType::Unshielded(UnshieldedTokenType(expected_color));
    let inputs = |is_contract: bool, recipient: &[u8; 32], enabled: bool| {
        BTreeMap::from([
            ("domain".into(), bytes(&domain.0)),
            ("amount".into(), json!(amount.to_string())),
            ("isContract".into(), json!(is_contract)),
            ("recipient".into(), bytes(recipient)),
            ("enabled".into(), json!(enabled)),
        ])
    };

    for (is_contract, recipient_bytes, self_credit) in [
        (true, [9; 32], true),
        (true, [23; 32], false),
        (false, [9; 32], false),
    ] {
        let recipient = HashOutput(recipient_bytes);
        let execution = prepare_with_context(
            &plan,
            &inputs(is_contract, &recipient.0, true),
            context.clone(),
            params,
        )?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        assert_eq!(execution.returns_json()["color"], bytes(&expected_color.0));

        let effects = context
            .query(
                &execution.program,
                None,
                &params.cost_model.runtime_cost_model,
            )?
            .context
            .effects;
        let target = if is_contract {
            PublicAddress::Contract(ContractAddress(recipient))
        } else {
            PublicAddress::User(UserAddress(recipient))
        };
        assert_eq!(
            effects.unshielded_mints.get(&domain).map(|value| *value),
            Some(amount)
        );
        assert_eq!(effects.unshielded_mints.size(), 1);
        assert_eq!(effects.unshielded_inputs.size(), usize::from(self_credit));
        assert_eq!(
            effects.unshielded_inputs.get(&token).map(|value| *value),
            self_credit.then_some(amount as u128)
        );
        assert_eq!(effects.unshielded_outputs.size(), 0);
        assert_eq!(effects.claimed_unshielded_spends.size(), 1);
        assert_eq!(
            effects
                .claimed_unshielded_spends
                .get(&ClaimedUnshieldedSpendsKey(token, target))
                .map(|value| *value),
            Some(amount as u128)
        );
    }

    let inactive = prepare_with_context(
        &plan,
        &inputs(true, &own.0.0, false),
        context.clone(),
        params,
    )?;
    assert_eq!(check(&inactive, &circuit)?, inactive.activity_schedule);
    assert_eq!(inactive.returns_json()["color"], bytes(&[0; 32]));
    let inactive_effects = context
        .query(
            &inactive.program,
            None,
            &params.cost_model.runtime_cost_model,
        )?
        .context
        .effects;
    assert_eq!(inactive_effects.unshielded_mints.size(), 0);
    assert_eq!(inactive_effects.unshielded_inputs.size(), 0);
    assert_eq!(inactive_effects.unshielded_outputs.size(), 0);
    assert_eq!(inactive_effects.claimed_unshielded_spends.size(), 0);

    let mut forged = prepare_with_context(
        &plan,
        &inputs(true, &own.0.0, true),
        context.clone(),
        params,
    )?
    .preimage;
    forged.public_transcript_inputs =
        prepare_with_context(&plan, &inputs(false, &own.0.0, true), context, params)?
            .preimage
            .public_transcript_inputs
            .clone();
    assert!(forged.check(&circuit).is_err());
    Ok(())
}
