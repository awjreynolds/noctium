#![cfg(feature = "zkir-321")]

use anyhow::Context;
use base_crypto::hash::HashOutput;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Db, Plan,
    assembly::{CheckedNativeCall, assemble_checked_calls},
    check, create_state, prepare,
    zkir::IrSource,
};
use onchain_runtime::{
    context::QueryContext,
    state::{ChargedState, EntryPointBuf},
};
use rand::rngs::OsRng;
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};
use transient_crypto::curve::Fr;

use ledger::structure::INITIAL_PARAMETERS;

#[test]
#[ignore = "requires fresh TypedContractReference ZKIR 3.2.1 artifacts"]
fn typed_contract_reference_routes_to_the_stored_target_and_selector() -> anyhow::Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_TYPED_CONTRACT_REFERENCE_DIR")?);
    let load = |stem: &str| -> anyhow::Result<(Plan, IrSource)> {
        let plan = serde_json::from_reader(File::open(
            directory.join(format!("TypedRef{stem}.impact.json")),
        )?)?;
        let circuit = IrSource::load(File::open(directory.join(format!("TypedRef{stem}.zkir")))?)?;
        Ok((plan, circuit))
    };
    let (target_plan, target_circuit) = load("Target.update")?;
    let (caller_plan, caller_circuit) = load("Caller.forward")?;

    let target = ContractAddress(HashOutput([9; 32]));
    let caller = ContractAddress(HashOutput([8; 32]));
    let other_target = ContractAddress(HashOutput([10; 32]));
    let target_state = |total: &str| {
        create_state(
            &target_plan,
            &BTreeMap::from([("total".into(), json!(total))]),
        )
    };
    let initial_target = target_state("0")?;
    let target_inputs = BTreeMap::from([("amount".into(), json!("7"))]);
    let target_execution = prepare(
        &target_plan,
        &target_inputs,
        &initial_target,
        &INITIAL_PARAMETERS,
        target,
    )?;
    assert_eq!(target_execution.after.state, target_state("7")?);
    assert_eq!(
        target_execution.returns_json(),
        BTreeMap::from([("stored".into(), json!("7"))])
    );

    let caller_state = |routed_to: ContractAddress| {
        create_state(
            &caller_plan,
            &BTreeMap::from([(
                "route".into(),
                json!({"kind": "bytes", "values": routed_to.0.0}),
            )]),
        )
    };
    let initial_caller = caller_state(target)?;
    let forward_inputs = BTreeMap::from([
        ("opening".into(), json!("101")),
        ("amount".into(), json!("7")),
        ("expected".into(), json!("7")),
    ]);
    let assemble = |source: &noctium_runtime::Execution,
                    circuit: &IrSource,
                    route: &ChargedState<Db>,
                    routed_to: ContractAddress,
                    child: &noctium_runtime::Execution,
                    selector: EntryPointBuf| {
        assemble_checked_calls(
            &[
                CheckedNativeCall {
                    execution: source,
                    circuit,
                    initial_context: QueryContext::new(route.clone(), caller),
                    entry_point: EntryPointBuf(b"forward".to_vec()),
                    communication_commitment_rand: Fr::from(53u64),
                },
                CheckedNativeCall {
                    execution: child,
                    circuit: &target_circuit,
                    initial_context: QueryContext::new(initial_target.clone(), routed_to),
                    entry_point: selector,
                    communication_commitment_rand: Fr::from(101u64),
                },
            ],
            &INITIAL_PARAMETERS,
            1_800_000_000,
            &mut OsRng,
        )
    };

    let update = EntryPointBuf(b"update".to_vec());
    let other_execution = prepare(
        &target_plan,
        &target_inputs,
        &initial_target,
        &INITIAL_PARAMETERS,
        other_target,
    )?;
    let assert_route =
        |forward: &Plan, circuit: &IrSource, stored: &ChargedState<Db>| -> anyhow::Result<()> {
            let execution = prepare(
                forward,
                &forward_inputs,
                stored,
                &INITIAL_PARAMETERS,
                caller,
            )?;
            let composed = assemble(
                &execution,
                circuit,
                stored,
                target,
                &target_execution,
                update.clone(),
            )?;
            let calls = composed.calls().collect::<Vec<_>>();
            assert_eq!(calls.len(), 2);
            assert!(calls[0].calls(calls[1]));
            assert_eq!(calls[1].address, target);
            assert!(
                assemble(
                    &execution,
                    circuit,
                    stored,
                    other_target,
                    &other_execution,
                    update.clone(),
                )
                .is_err()
            );
            assert!(
                assemble(
                    &execution,
                    circuit,
                    stored,
                    target,
                    &target_execution,
                    EntryPointBuf(b"other".to_vec()),
                )
                .is_err()
            );
            Ok(())
        };

    assert_route(&caller_plan, &caller_circuit, &initial_caller)?;

    let empty_list = BTreeMap::from([("routes".into(), json!([]))]);
    let record_cell = BTreeMap::from([(
        "route".into(),
        json!({
            "target": {"kind": "bytes", "values": other_target.0.0},
            "enabled": false
        }),
    )]);
    let inputs = BTreeMap::from([(
        "replacement".into(),
        json!({"kind": "bytes", "values": target.0.0}),
    )]);
    for (write, forward, initial) in [
        ("ListCaller.addRoute", "ListCaller.forward", &empty_list),
        (
            "RecordCaller.setRoute",
            "RecordCaller.forward",
            &record_cell,
        ),
        (
            "RecordListCaller.addRoute",
            "RecordListCaller.forward",
            &empty_list,
        ),
    ] {
        let (write_plan, write_circuit) = load(write)?;
        let (forward_plan, forward_circuit) = load(forward)?;
        let state =
            create_state(&write_plan, initial).with_context(|| format!("{write} initial state"))?;
        let written = prepare(&write_plan, &inputs, &state, &INITIAL_PARAMETERS, caller)
            .with_context(|| format!("{write} execution"))?;
        check(&written, &write_circuit).with_context(|| format!("{write} relation"))?;
        assert_route(&forward_plan, &forward_circuit, &written.after.state)
            .with_context(|| format!("{forward} call assembly"))?;
    }
    Ok(())
}
