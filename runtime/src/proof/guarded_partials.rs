use super::preview_call_activity;
use crate::{
    Db, Execution, Expr, Instruction, Plan, check, create_state, field_decimal, prepare,
    zkir::IrSource,
};
use ledger::structure::{ContractAction, ContractCall, ProofPreimageVersioned};
use onchain_runtime::context::QueryContext;
use onchain_runtime::state::{ChargedState, StateValue};
use rand::{SeedableRng, rngs::StdRng};
use serde_json::{Value as Json, json};
use serialize::Serializable;
use std::{collections::BTreeMap, env, fs};
use transient_crypto::fab::AlignedValueExt;
use transient_crypto::{commitment::Pedersen, curve::Fr};

const PLAN: &str = include_str!(
    "../../tests/fixtures/generic-state/issue43-guarded-partials/321/Issue43GuardedPartialWrites.update.impact.json"
);
const CIRCUIT: &[u8] = include_bytes!(
    "../../tests/fixtures/generic-state/issue43-guarded-partials/321/Issue43GuardedPartialWrites.update.zkir"
);

fn plan() -> Plan {
    serde_json::from_slice(&artifact("impact.json", PLAN.as_bytes()))
        .expect("source-generated guarded partial plan parses")
}

fn artifact(suffix: &str, committed: &[u8]) -> Vec<u8> {
    let Some(directory) = std::env::var_os("NOCTIUM_GUARDED_PARTIALS_DIR") else {
        return committed.to_vec();
    };
    let path = std::path::PathBuf::from(directory)
        .join(format!("Issue43GuardedPartialWrites.update.{suffix}"));
    std::fs::read(path).expect("read freshly compiled guarded partial artifact")
}

fn enabled_guarded_operation(instruction: &Instruction) -> &Instruction {
    let Instruction::Guarded { guard, operation } = instruction else {
        panic!("scalar plan operation is guarded")
    };
    assert_eq!(
        guard,
        &Expr::Reference {
            name: "enabled".to_owned()
        }
    );
    operation
}

#[test]
fn guarded_scalar_plan_decodes_order_guards_and_partial_operands() {
    let plan = plan();
    assert_eq!(plan.entrypoint, "update");
    assert_eq!(
        plan.state
            .iter()
            .map(|declaration| declaration.name.as_str())
            .collect::<Vec<_>>(),
        vec!["underflowed", "narrowed", "asserted", "shadowed", "valid"]
    );
    assert_eq!(plan.operations.len(), 15);

    for (slot, operations) in plan.operations.chunks_exact(3).enumerate() {
        let Instruction::Push {
            storage: false,
            expression: Expr::Constant { value },
            alignment,
        } = enabled_guarded_operation(&operations[0])
        else {
            panic!("each scalar write starts with its ordered Cell slot")
        };
        assert_eq!(value, &slot.to_string());
        assert_eq!(alignment, "field");

        let Instruction::Push {
            storage: true,
            expression,
            alignment,
        } = enabled_guarded_operation(&operations[1])
        else {
            panic!("each scalar write stores its value after the Cell slot")
        };
        assert_eq!(alignment, "field");
        if slot == 0 {
            let Expr::Cast { ty, value } = expression else {
                panic!("the value stored in the first Cell is widened to Native");
            };
            assert_eq!(ty, "Native");
            assert!(matches!(value.as_ref(), Expr::Let { body, .. }
                if matches!(body.as_ref(), Expr::Usub { maximum, .. } if maximum == "255")));
        }

        assert!(matches!(
            enabled_guarded_operation(&operations[2]),
            Instruction::Insert { n: 1 }
        ));
    }
}

fn state(plan: &Plan) -> ChargedState<Db> {
    create_state(
        plan,
        &BTreeMap::from([
            ("underflowed".to_owned(), json!("0")),
            ("narrowed".to_owned(), json!("0")),
            ("asserted".to_owned(), json!("0")),
            ("shadowed".to_owned(), json!("0")),
            ("valid".to_owned(), json!("0")),
        ]),
    )
    .expect("source cells create native ledger state")
}

fn inputs(
    enabled: bool,
    check_enabled: bool,
    left: u64,
    right: u64,
    wide: u64,
    approved: bool,
) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("enabled".to_owned(), json!(enabled)),
        ("checkEnabled".to_owned(), json!(check_enabled)),
        ("left".to_owned(), json!(left.to_string())),
        ("right".to_owned(), json!(right.to_string())),
        ("wide".to_owned(), json!(wide.to_string())),
        ("approved".to_owned(), json!(approved)),
    ])
}

fn serialized<T: Serializable>(value: &T) -> Vec<u8> {
    let mut bytes = Vec::new();
    value
        .serialize(&mut bytes)
        .expect("in-memory serialization succeeds");
    bytes
}

fn transcript_statement(transcript: Option<&onchain_runtime::transcript::Transcript<Db>>) -> Json {
    let Some(transcript) = transcript else {
        return Json::Null;
    };
    json!({
        "operationCount": u64::try_from(transcript.program.len()).expect("program length fits u64"),
        "readTime": transcript.gas.read_time.into_picoseconds(),
        "computeTime": transcript.gas.compute_time.into_picoseconds(),
        "bytesWritten": transcript.gas.bytes_written,
        "bytesDeleted": transcript.gas.bytes_deleted,
        "effects": serialized(&transcript.effects),
    })
}

fn native_statement<P: ledger::structure::ProofKind<Db>>(
    call: &ContractCall<P, Db>,
    parent_pedersen: Pedersen,
    fields: &[Fr],
) -> Json {
    let parent_pedersen_bytes = serialized(&parent_pedersen);
    let cost_model = &ledger::structure::INITIAL_PARAMETERS
        .cost_model
        .runtime_cost_model;

    json!({
        "address": call.address.0.0.to_vec(),
        "entryPoint": &call.entry_point.0,
        "parentPedersen": parent_pedersen_bytes,
        "communication": field_decimal(call.communication_commitment),
        "noopConstant": cost_model.noop_constant.into_picoseconds(),
        "noopCoefficient": cost_model.noop_coeff_arg.into_picoseconds(),
        "guaranteed": transcript_statement(call.guaranteed_transcript.as_deref()),
        "fallible": transcript_statement(call.fallible_transcript.as_deref()),
        "fields": fields.iter().copied().map(field_decimal).collect::<Vec<_>>(),
    })
}

fn check_native_statement(
    destination: &str,
    plan: &Plan,
    circuit: &IrSource,
    execution: &Execution,
    initial: &ChargedState<Db>,
) {
    let address = coin_structure::contract::ContractAddress::default();
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let context = QueryContext::new(initial.clone(), address);
    let mut rng = StdRng::from_seed([7; 32]);
    let intent = crate::assembly::assemble_checked_calls(
        &[crate::assembly::CheckedNativeCall {
            execution,
            circuit,
            initial_context: context.clone(),
            entry_point: onchain_runtime::state::EntryPointBuf(plan.entrypoint.as_bytes().to_vec()),
            communication_commitment_rand: transient_crypto::curve::Fr::from(1u64),
        }],
        parameters,
        1_800_000_000,
        &mut rng,
    )
    .expect("assemble the checked native call");
    let ContractAction::Call(source_call) =
        intent.actions.iter_deref().next().expect("one call action")
    else {
        panic!("assembly emits a native contract call");
    };
    let before_guaranteed = source_call.guaranteed_transcript.as_deref();
    let before_fallible = source_call.fallible_transcript.as_deref();
    let ProofPreimageVersioned::V2(preimage) = &source_call.proof else {
        panic!("assembly emits a V2 proof preimage");
    };
    assert_eq!(
        preimage
            .communications_commitment
            .map(|(commitment, _)| commitment),
        Some(source_call.communication_commitment),
        "the circuit preimage binds the native communication commitment"
    );
    let activity = preimage
        .check(circuit)
        .expect("assembled proof preimage derives the circuit activity schedule");
    let cost_model = &parameters.cost_model.runtime_cost_model;
    let preview = preview_call_activity(
        source_call,
        &activity,
        intent.binding_commitment.into(),
        cost_model,
    )
    .expect("production activity preview builds the native public statement");
    let mut bound_preimage = (**preimage).clone();
    bound_preimage.binding_input = preview.statement[0];
    let rebound_activity = bound_preimage
        .check(circuit)
        .expect("source preimage remains valid after public binding");
    assert_eq!(
        rebound_activity, activity,
        "binding the public statement preserves selected circuit activity"
    );
    if execution.program.is_empty() {
        assert!(execution.guaranteed.is_none() && execution.fallible.is_none());
        let before = before_guaranteed.expect("assembly adds the required empty partition");
        assert!(before.program.is_empty() && before_fallible.is_none());
        // The checked inactive schedule has one contiguous run of 55 skipped fields.
        let program: crate::Program = vec![onchain_runtime::ops::Op::Noop { n: 55 }];
        let query = context
            .query(&program, None, cost_model)
            .expect("the native runtime executes and prices the single Noop");
        let previewed = preview
            .call
            .guaranteed_transcript
            .as_deref()
            .expect("production preview keeps the empty guaranteed partition");
        let mut preview_program = previewed.program.iter_deref();
        assert!(matches!(
            preview_program.next(),
            Some(onchain_runtime::ops::Op::Noop { n: 55 })
        ));
        assert!(
            preview_program.next().is_none(),
            "the 55 skipped fields coalesce"
        );
        assert_eq!(previewed.gas, query.gas_cost);
        assert_eq!(previewed.effects, query.context.effects);
        assert!(preview.call.fallible_transcript.is_none());
    }
    assert_eq!(
        preview.statement.get(1),
        Some(&source_call.communication_commitment)
    );
    let Some(path) = env::var_os(destination) else {
        return;
    };
    let statement = native_statement(
        source_call,
        intent.binding_commitment.into(),
        &preview.statement,
    );
    fs::write(
        path,
        serde_json::to_vec_pretty(&statement).expect("native call statement serializes as JSON"),
    )
    .expect("write native call statement to requested path");
}

#[test]
fn binding_serialization_matches_pinned_midnight_vectors() {
    let uint_vectors: &[(u64, &[u8])] = &[
        (0, &[0x00]),
        (1, &[0x04]),
        (15, &[0x3c]),
        (63, &[0xfc]),
        (64, &[0x01, 0x01]),
        (1 << 14, &[0x02, 0x00, 0x01, 0x00]),
        (1 << 30, &[0x03, 0x00, 0x00, 0x00, 0x40]),
        (
            u64::MAX,
            &[0x13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff],
        ),
    ];
    for (value, expected) in uint_vectors {
        assert_eq!(
            serialized(value).as_slice(),
            *expected,
            "u64 binding value {value}"
        );
    }

    let entrypoint = onchain_runtime::state::EntryPointBuf(b"update".to_vec());
    assert_eq!(
        serialized(&entrypoint).as_slice(),
        &[0x18, b'u', b'p', b'd', b'a', b't', b'e']
    );

    let address = coin_structure::contract::ContractAddress::default();
    assert_eq!(serialized(&address), vec![0; 32]);

    let cost = base_crypto::cost_model::RunningCost {
        read_time: base_crypto::cost_model::CostDuration::from_picoseconds(1),
        compute_time: base_crypto::cost_model::CostDuration::from_picoseconds(120),
        bytes_written: 2,
        bytes_deleted: 3,
    };
    assert_eq!(serialized(&cost).as_slice(), &[4, 225, 1, 8, 12]);
}

fn cell(state: &ChargedState<Db>, slot: usize) -> String {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Cell(cell) = &*array.get(slot).expect("cell slot exists") else {
        panic!("expected state cell")
    };
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    field_decimal(fields[0])
}

fn prepare_case(
    plan: &Plan,
    initial: &ChargedState<Db>,
    values: BTreeMap<String, Json>,
) -> anyhow::Result<crate::Execution> {
    prepare(
        plan,
        &values,
        initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
}

#[test]
fn guarded_partial_scalar_expressions_are_safe_and_keep_active_semantics() {
    let plan = plan();
    let circuit = IrSource::load(artifact("zkir", CIRCUIT).as_slice()).expect("source ZKIR parses");
    let initial = state(&plan);

    let inactive = prepare_case(&plan, &initial, inputs(false, false, 1, 2, 8, false))
        .expect("inactive underflow, narrowing, assertions, and shadowing are totalized");
    assert!(inactive.program.is_empty());
    assert_eq!(
        check(&inactive, &circuit).expect("inactive activity schedule checks"),
        [Some(5), Some(5), Some(1)].repeat(5)
    );

    assert!(prepare_case(&plan, &initial, inputs(true, false, 1, 2, 3, true)).is_err());
    assert!(prepare_case(&plan, &initial, inputs(true, false, 3, 2, 8, true)).is_err());
    assert!(prepare_case(&plan, &initial, inputs(true, false, 3, 2, 3, false)).is_err());

    let active_require = prepare_case(&plan, &initial, inputs(false, true, 1, 2, 8, false))
        .expect("prepare skips inactive writes and defers the relation requirement to ZKIR");
    assert!(check(&active_require, &circuit).is_err());

    let active = prepare_case(&plan, &initial, inputs(true, true, 3, 2, 3, true))
        .expect("active partial expressions with valid operands preserve source behavior");
    let active_schedule = check(&active, &circuit).expect("active activity schedule checks");
    assert_eq!(active_schedule, vec![None; 15]);
    let checked_active_operations = active_schedule
        .iter()
        .filter(|activity| activity.is_none())
        .count();
    let partitioned_operations = active
        .guaranteed
        .iter()
        .chain(active.fallible.iter())
        .map(|transcript| transcript.program.len())
        .sum::<usize>();
    assert_eq!(
        partitioned_operations, checked_active_operations,
        "active transcript partitions account for all checked operations"
    );
    assert_eq!(cell(&active.after.state, 0), "1");
    assert_eq!(cell(&active.after.state, 1), "3");
    assert_eq!(cell(&active.after.state, 2), "7");
    assert_eq!(cell(&active.after.state, 3), "1");
    assert_eq!(cell(&active.after.state, 4), "3");
    check_native_statement(
        "NOCTIUM_GUARDED_PARTIALS_STATEMENT_FILE",
        &plan,
        &circuit,
        &active,
        &initial,
    );
    check_native_statement(
        "NOCTIUM_GUARDED_PARTIALS_INACTIVE_STATEMENT_FILE",
        &plan,
        &circuit,
        &inactive,
        &initial,
    );
}
