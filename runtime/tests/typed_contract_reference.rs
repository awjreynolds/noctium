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
    let assert_route = |forward: &Plan,
                        circuit: &IrSource,
                        stored: &ChargedState<Db>,
                        inputs: &BTreeMap<String, serde_json::Value>|
     -> anyhow::Result<()> {
        let execution = prepare(forward, inputs, stored, &INITIAL_PARAMETERS, caller)?;
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

    assert_route(
        &caller_plan,
        &caller_circuit,
        &initial_caller,
        &forward_inputs,
    )?;

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
        assert_route(
            &forward_plan,
            &forward_circuit,
            &written.after.state,
            &forward_inputs,
        )
        .with_context(|| format!("{forward} call assembly"))?;
    }

    let owner = json!({"kind": "bytes", "values": ([1u8; 32])});
    let list_owner_inputs = BTreeMap::from([("owner".into(), owner.clone())]);
    let mut nested_write_inputs = inputs;
    nested_write_inputs.insert("owner".into(), owner.clone());
    let mut nested_call_inputs = forward_inputs.clone();
    nested_call_inputs.insert("owner".into(), owner);
    let mut missing_owner_inputs = nested_call_inputs.clone();
    missing_owner_inputs.insert(
        "owner".into(),
        json!({"kind": "bytes", "values": ([2u8; 32])}),
    );
    for (init, write, forward, two_keys) in [
        (
            None,
            "NestedMapCaller.insertRoute",
            "NestedMapCaller.forward",
            false,
        ),
        (
            Some(("NestedListCaller.initializeOwner", false)),
            "NestedListCaller.addRoute",
            "NestedListCaller.forward",
            false,
        ),
        (
            Some(("DeepMapCaller.initializeOwner", false)),
            "DeepMapCaller.insertRoute",
            "DeepMapCaller.forward",
            true,
        ),
        (
            Some(("DeepListCaller.initializeBucket", true)),
            "DeepListCaller.addRoute",
            "DeepListCaller.forward",
            true,
        ),
    ] {
        let (write_plan, write_circuit) = load(write)?;
        let (forward_plan, forward_circuit) = load(forward)?;
        let state = create_state(&write_plan, &empty_list)?;
        let mut write_inputs = nested_write_inputs.clone();
        let mut call_inputs = nested_call_inputs.clone();
        let mut absent_owner = missing_owner_inputs.clone();
        let bucket = json!({"kind": "bytes", "values": ([3u8; 32])});
        if two_keys {
            write_inputs.insert("bucket".into(), bucket.clone());
            call_inputs.insert("bucket".into(), bucket.clone());
            absent_owner.insert("bucket".into(), bucket.clone());
        }
        let state = if let Some((init, needs_bucket)) = init {
            let (plan, circuit) = load(init)?;
            let mut inputs = list_owner_inputs.clone();
            if needs_bucket {
                inputs.insert("bucket".into(), bucket);
            }
            let initialized = prepare(&plan, &inputs, &state, &INITIAL_PARAMETERS, caller)
                .with_context(|| format!("{init} execution"))?;
            check(&initialized, &circuit).with_context(|| format!("{init} relation"))?;
            initialized.after.state
        } else {
            state
        };
        let written = prepare(
            &write_plan,
            &write_inputs,
            &state,
            &INITIAL_PARAMETERS,
            caller,
        )
        .with_context(|| format!("{write} execution"))?;
        check(&written, &write_circuit).with_context(|| format!("{write} relation"))?;
        assert_route(
            &forward_plan,
            &forward_circuit,
            &written.after.state,
            &call_inputs,
        )
        .with_context(|| format!("{forward} call assembly"))?;
        assert!(
            prepare(
                &forward_plan,
                &absent_owner,
                &written.after.state,
                &INITIAL_PARAMETERS,
                caller,
            )
            .is_err(),
            "{forward} accepted a missing owner"
        );
        if two_keys {
            call_inputs.insert(
                "bucket".into(),
                json!({"kind": "bytes", "values": ([4u8; 32])}),
            );
            assert!(
                prepare(
                    &forward_plan,
                    &call_inputs,
                    &written.after.state,
                    &INITIAL_PARAMETERS,
                    caller
                )
                .is_err(),
                "{forward} accepted a missing bucket"
            );
        }
    }

    let (echo_target_plan, echo_target_circuit) = load("EchoTarget.echo")?;
    let (echo_caller_plan, echo_caller_circuit) = load("EchoCaller.forward")?;
    let echo_target_address = ContractAddress(HashOutput([11; 32]));
    let echo_caller_address = ContractAddress(HashOutput([12; 32]));
    let echo_value = ContractAddress(HashOutput([13; 32]));
    let substitute = ContractAddress(HashOutput([14; 32]));
    let bytes_value = |address: ContractAddress| json!({"kind": "bytes", "values": address.0.0});
    let empty_echo_target = create_state(&echo_target_plan, &BTreeMap::new())?;
    let empty_echo_caller = create_state(&echo_caller_plan, &BTreeMap::new())?;
    let echo_target_execution = prepare(
        &echo_target_plan,
        &BTreeMap::from([("target".into(), bytes_value(echo_value))]),
        &empty_echo_target,
        &INITIAL_PARAMETERS,
        echo_target_address,
    )?;
    assert_eq!(
        echo_target_execution.returns_json(),
        BTreeMap::from([("result".into(), bytes_value(echo_value))])
    );

    let echo_inputs = BTreeMap::from([
        ("opening".into(), json!("101")),
        ("target".into(), bytes_value(echo_target_address)),
        ("argument".into(), bytes_value(echo_value)),
        ("expected".into(), bytes_value(echo_value)),
    ]);
    let echo_entry = EntryPointBuf(b"echo".to_vec());
    let prepare_echo_caller = |inputs: &BTreeMap<String, serde_json::Value>| {
        prepare(
            &echo_caller_plan,
            inputs,
            &empty_echo_caller,
            &INITIAL_PARAMETERS,
            echo_caller_address,
        )
    };
    let assemble_echo = |caller: &noctium_runtime::Execution,
                         target: &noctium_runtime::Execution| {
        assemble_checked_calls(
            &[
                CheckedNativeCall {
                    execution: caller,
                    circuit: &echo_caller_circuit,
                    initial_context: QueryContext::new(
                        empty_echo_caller.clone(),
                        echo_caller_address,
                    ),
                    entry_point: EntryPointBuf(b"forward".to_vec()),
                    communication_commitment_rand: Fr::from(151u64),
                },
                CheckedNativeCall {
                    execution: target,
                    circuit: &echo_target_circuit,
                    initial_context: QueryContext::new(
                        empty_echo_target.clone(),
                        echo_target_address,
                    ),
                    entry_point: echo_entry.clone(),
                    communication_commitment_rand: Fr::from(101u64),
                },
            ],
            &INITIAL_PARAMETERS,
            1_800_000_000,
            &mut OsRng,
        )
    };
    let echo_caller_execution = prepare_echo_caller(&echo_inputs)?;
    let claims = &echo_caller_execution.after.effects.claimed_contract_calls;
    assert_eq!(claims.iter().count(), 1);
    let (_, claimed_address, selector, _) = claims.iter().next().unwrap().into_inner();
    assert_eq!(claimed_address, echo_target_address);
    assert_eq!(selector, echo_entry.ep_hash());

    let echo_intent = assemble_echo(&echo_caller_execution, &echo_target_execution)?;
    let echo_calls = echo_intent.calls().collect::<Vec<_>>();
    assert_eq!(echo_calls.len(), 2);
    assert!(echo_calls[0].calls(echo_calls[1]));
    assert_eq!(echo_calls[1].address, echo_target_address);

    let mut wrong_expected = echo_inputs.clone();
    wrong_expected.insert("expected".into(), bytes_value(substitute));
    let wrong_expected_execution = prepare_echo_caller(&wrong_expected)?;
    assert!(assemble_echo(&wrong_expected_execution, &echo_target_execution).is_err());

    let mut wrong_argument = echo_inputs;
    wrong_argument.insert("argument".into(), bytes_value(substitute));
    let wrong_argument_execution = prepare_echo_caller(&wrong_argument)?;
    assert!(assemble_echo(&wrong_argument_execution, &echo_target_execution).is_err());
    Ok(())
}
