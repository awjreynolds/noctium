#![cfg(feature = "zkir-321")]

use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, env, fs, path::PathBuf};

#[test]
#[ignore = "requires fresh ShieldedBurnAddress.lean outputs"]
fn burn_returns_both_typed_address_arms_without_ledger_effects() -> anyhow::Result<()> {
    let directory =
        PathBuf::from(env::var_os("NOCTIUM_BURN_ADDRESS_DIR").expect("set artifact directory"));
    let plan: Plan = serde_json::from_slice(&fs::read(
        directory.join("ShieldedBurnAddressReturnFixture.burn.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        directory.join("ShieldedBurnAddressReturnFixture.burn.zkir"),
    )?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &BTreeMap::new(),
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    check(&execution, &circuit)?;
    let address = |id: &str| {
        json!({"kind":"struct","id":id,"fields":[
            {"name":"bytes","value":{"kind":"bytes","values":vec![0u8; 32]}}
        ]})
    };
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([(
            "result".into(),
            json!({
                "kind":"struct",
                "id":"Noctium.Midnight.ShieldedBurnAddressResult",
                "fields":[
                    {"name":"is_left","value":{"kind":"bool","value":true}},
                    {"name":"left","value":address("Noctium.Midnight.ZswapCoinPublicKey")},
                    {"name":"right","value":address("Noctium.Midnight.ContractAddress")}
                ]
            })
        )]),
    );
    assert_eq!(execution.after.state, state);
    assert!(execution.guaranteed.is_none() && execution.fallible.is_none());
    Ok(())
}
