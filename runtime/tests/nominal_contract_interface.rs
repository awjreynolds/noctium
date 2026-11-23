#![cfg(feature = "zkir-321")]

use anyhow::Result;
use base_crypto::hash::HashOutput;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Plan,
    assembly::{CheckedNativeCall, assemble_checked_calls},
    create_state, prepare,
    zkir::IrSource,
};
use onchain_runtime::{context::QueryContext, state::EntryPointBuf};
use rand::rngs::OsRng;
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};
use transient_crypto::curve::Fr;

use ledger::structure::INITIAL_PARAMETERS;

#[test]
#[ignore = "requires fresh TypedContractReference artifacts in NOCTIUM_TYPED_CONTRACT_REFERENCE_DIR"]
fn nominal_uint_interface_assembles_matching_caller_and_callee() -> Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_TYPED_CONTRACT_REFERENCE_DIR")
            .expect("NOCTIUM_TYPED_CONTRACT_REFERENCE_DIR"),
    );
    let load = |stem: &str| -> Result<(Plan, IrSource)> {
        let plan = serde_json::from_reader(File::open(
            directory.join(format!("{stem}.impact.json")),
        )?)?;
        let circuit = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;
        Ok((plan, circuit))
    };
    let (target_plan, target_circuit) = load("NominalUIntInterfaceTarget.update")?;
    let (caller_plan, caller_circuit) = load("NominalUIntInterfaceCaller.call")?;

    let target = ContractAddress(HashOutput([9; 32]));
    let caller = ContractAddress(HashOutput([8; 32]));
    let target_state = create_state(
        &target_plan,
        &BTreeMap::from([("total".into(), json!("0"))]),
    )?;
    let caller_state = create_state(
        &caller_plan,
        &BTreeMap::from([(
            "route".into(),
            json!({"kind": "bytes", "values": target.0.0}),
        )]),
    )?;

    let target_inputs = BTreeMap::from([("amount".into(), json!("7"))]);
    let target_execution = prepare(
        &target_plan,
        &target_inputs,
        &target_state,
        &INITIAL_PARAMETERS,
        target,
    )?;
    assert_eq!(
        target_execution.returns_json(),
        BTreeMap::from([("updated".into(), json!("7"))])
    );

    let caller_inputs = BTreeMap::from([
        ("amount".into(), json!("7")),
        ("expected".into(), json!("7")),
    ]);
    let caller_execution = prepare(
        &caller_plan,
        &caller_inputs,
        &caller_state,
        &INITIAL_PARAMETERS,
        caller,
    )?;
    let assemble = |source: &noctium_runtime::Execution| {
        assemble_checked_calls(
            &[
                CheckedNativeCall {
                    execution: source,
                    circuit: &caller_circuit,
                    initial_context: QueryContext::new(caller_state.clone(), caller),
                    entry_point: EntryPointBuf(b"call".to_vec()),
                    communication_commitment_rand: Fr::from(53u64),
                },
                CheckedNativeCall {
                    execution: &target_execution,
                    circuit: &target_circuit,
                    initial_context: QueryContext::new(target_state.clone(), target),
                    entry_point: EntryPointBuf(b"update".to_vec()),
                    communication_commitment_rand: Fr::from(1u64),
                },
            ],
            &INITIAL_PARAMETERS,
            1_800_000_000,
            &mut OsRng,
        )
    };

    let intent = assemble(&caller_execution)?;
    let calls = intent.calls().collect::<Vec<_>>();
    assert_eq!(calls.len(), 2);
    assert!(calls[0].calls(calls[1]));
    assert_eq!(calls[1].address, target);

    let mut wrong_expected = caller_inputs;
    wrong_expected.insert("expected".into(), json!("8"));
    let wrong_expected_execution = prepare(
        &caller_plan,
        &wrong_expected,
        &caller_state,
        &INITIAL_PARAMETERS,
        caller,
    )?;
    assert!(assemble(&wrong_expected_execution).is_err());
    Ok(())
}
