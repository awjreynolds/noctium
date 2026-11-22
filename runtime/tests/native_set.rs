#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, Expr, Instruction, PathPart, Plan, check, create_state, field_value, prepare,
    zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, path::Path};
use transient_crypto::curve::Fr;

fn set_artifacts() -> std::path::PathBuf {
    std::env::var_os("NOCTIUM_SET_DIR")
        .map(std::path::PathBuf::from)
        .expect("set tests require fresh outputs in NOCTIUM_SET_DIR")
}

fn load_plan(directory: &Path, name: &str) -> Plan {
    serde_json::from_slice(&std::fs::read(directory.join(name)).unwrap()).unwrap()
}

fn load_circuit(directory: &Path, name: &str) -> IrSource {
    IrSource::load(std::fs::read(directory.join(name)).unwrap().as_slice()).unwrap()
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_TYPED_RECORD_SET_DIR"]
fn typed_record_set_keeps_both_fields_in_one_key() -> anyhow::Result<()> {
    let directory = std::path::PathBuf::from(
        std::env::var_os("NOCTIUM_TYPED_RECORD_SET_DIR").expect("typed record Set artifacts"),
    );
    let plan = load_plan(&directory, "TypedSetKey.update.impact.json");
    let circuit = load_circuit(&directory, "TypedSetKey.update.zkir");
    let mut state = create_state(&plan, &BTreeMap::from([("memoSet".into(), json!([]))]))?;
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let inputs = |active, amount: u32, adding, removing| {
        BTreeMap::from([
            ("active".into(), json!(active)),
            ("amount".into(), json!(amount.to_string())),
            ("adding".into(), json!(adding)),
            ("removing".into(), json!(removing)),
        ])
    };
    for (active, amount, adding, removing, before, count) in [
        (true, 513, false, false, false, 0),
        (true, 513, true, false, false, 1),
        (false, 513, false, false, false, 1),
        (true, 514, false, false, false, 1),
        (false, 513, true, false, false, 2),
        (true, 513, false, true, true, 1),
        (true, 513, false, false, false, 1),
        (false, 513, false, false, true, 1),
    ] {
        let args = inputs(active, amount, adding, removing);
        let result = prepare(&plan, &args, &state, params, address)?;
        check(&result, &circuit)?;
        assert_eq!(result.returns_json()["wasPresent"], json!(before));
        if !adding && !removing {
            assert_eq!(result.after.state.get_ref(), state.get_ref());
        }
        state = result.after.state;
        let StateValue::Array(slots) = state.get_ref() else {
            anyhow::bail!("expected a state array");
        };
        let Some(StateValue::Map(set)) = slots.get(0) else {
            anyhow::bail!("expected a Set-backed map");
        };
        let key = AlignedValue::concat(
            [
                field_value(Fr::from(u8::from(active))),
                field_value(Fr::from(amount)),
            ]
            .iter(),
        );
        assert_eq!(set.size(), count);
        assert_eq!(set.get(&key).is_some(), (before || adding) && !removing);
    }

    assert!(
        prepare(
            &plan,
            &inputs(true, 65536, true, false),
            &state,
            params,
            address
        )
        .is_err()
    );
    let mut mismatched = plan.clone();
    mismatched.state[0].kind["tree"]["set"]["composite"]["fields"]
        .as_array_mut()
        .expect("typed key schema fields")
        .swap(0, 1);
    assert!(
        prepare(
            &mismatched,
            &inputs(true, 513, true, false),
            &state,
            params,
            address
        )
        .is_err()
    );
    Ok(())
}

fn inputs(
    bucket: u64,
    tag: u8,
    adding: bool,
    removing: bool,
    clearing: bool,
) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("bucket".into(), json!(bucket.to_string())),
        (
            "tag".into(),
            json!({"kind":"bytes", "values":vec![tag; 32]}),
        ),
        ("adding".into(), json!(adding)),
        ("removing".into(), json!(removing)),
        ("clearing".into(), json!(clearing)),
    ])
}

fn initial_state(plan: &Plan) -> ChargedState<Db> {
    create_state(
        plan,
        &BTreeMap::from([
            ("registered".into(), json!([])),
            ("groups".into(), json!([])),
        ]),
    )
    .unwrap()
}

fn assert_set(state: &ChargedState<Db>, slot: usize, members: &[[u8; 32]]) {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected contract state array");
    };
    let StateValue::Map(set) = slots.get(slot).expect("set slot exists") else {
        panic!("expected Set-backed map");
    };
    assert_eq!(set.size(), members.len());
    for member in members {
        let key: AlignedValue = (*member).into();
        let value = set.get(&key).expect("Set member exists");
        assert!(matches!(&*value, StateValue::Null));
    }
}

fn append_set_key_to_path(operation: &mut Instruction) -> bool {
    match operation {
        Instruction::Guarded { operation, .. } => append_set_key_to_path(operation),
        Instruction::IndexPath { slot: 0, keys, .. } if keys.is_empty() => {
            let invalid_key = || PathPart {
                alignment: "field".into(),
                expression: Expr::Constant { value: "0".into() },
            };
            *keys = vec![invalid_key(), invalid_key()];
            true
        }
        _ => false,
    }
}

#[test]
#[ignore = "requires fresh Noctium Set artifacts from NOCTIUM_SET_DIR"]
fn native_sets_initialize_mutate_reset_and_preserve_siblings() {
    let directory = set_artifacts();
    let plan = load_plan(&directory, "NativeSet.update.impact.json");
    let circuit = load_circuit(&directory, "NativeSet.update.zkir");
    let initial = initial_state(&plan);
    assert_set(&initial, 0, &[]);
    let StateValue::Array(initial_slots) = initial.get_ref() else {
        panic!("expected contract state array");
    };
    assert!(matches!(
        initial_slots.get(1).unwrap(),
        StateValue::Map(groups) if groups.size() == 0
    ));

    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let cases = [
        (
            inputs(1, 7, true, false, false),
            1,
            1,
            true,
            true,
            vec![[7; 32]],
        ),
        (
            inputs(1, 7, true, false, false),
            1,
            1,
            true,
            true,
            vec![[7; 32]],
        ),
        (
            inputs(2, 8, true, false, false),
            2,
            1,
            true,
            true,
            vec![[7; 32], [8; 32]],
        ),
        (
            inputs(1, 9, false, true, false),
            2,
            1,
            false,
            false,
            vec![[7; 32], [8; 32]],
        ),
        (
            inputs(1, 7, false, true, false),
            1,
            0,
            false,
            false,
            vec![[8; 32]],
        ),
        (
            inputs(1, 7, false, true, false),
            1,
            0,
            false,
            false,
            vec![[8; 32]],
        ),
        (inputs(1, 7, false, false, true), 0, 0, false, false, vec![]),
    ];
    let mut state = initial;
    let mut state_with_two_groups = None;
    for (arguments, total, group, present, in_group, members) in cases {
        let step = prepare(&plan, &arguments, &state, parameters, address).unwrap();
        assert_eq!(check(&step, &circuit).unwrap(), step.activity_schedule);
        let returns = step.returns_json();
        assert_eq!(returns["totalTags"], json!(total.to_string()));
        assert_eq!(returns["groupTags"], json!(group.to_string()));
        assert_eq!(returns["containsTag"], json!(present));
        assert_eq!(returns["groupContainsTag"], json!(in_group));
        assert_eq!(returns["isEmpty"], json!(total == 0));
        state = step.after.state;
        assert_set(&state, 0, &members);
        if total == 2 {
            state_with_two_groups = Some(state.clone());
        }
    }

    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected contract state array");
    };
    let StateValue::Map(groups) = slots.get(1).unwrap() else {
        panic!("expected map of Sets");
    };
    let group_two_key = field_value(Fr::from(2u64));
    let group_two = groups.get(&group_two_key).expect("sibling group remains");
    let StateValue::Map(group_two) = &*group_two else {
        panic!("expected nested Set");
    };
    assert_eq!(group_two.size(), 1);
    let tag_eight: AlignedValue = [8; 32].into();
    assert!(matches!(
        &*group_two.get(&tag_eight).expect("sibling member remains"),
        StateValue::Null
    ));

    let mut malformed = plan.clone();
    assert!(malformed.operations.iter_mut().any(append_set_key_to_path));
    assert!(
        prepare(
            &malformed,
            &inputs(1, 7, true, false, false),
            &state_with_two_groups.expect("second group was initialized"),
            parameters,
            address,
        )
        .is_err()
    );
}

#[test]
#[ignore = "requires fresh Noctium Set artifacts from NOCTIUM_SET_DIR"]
fn guarded_set_emptiness_does_not_reveal_cardinality() {
    let directory = set_artifacts();
    let update = load_plan(&directory, "NativeSet.update.impact.json");
    let inspect = load_plan(&directory, "NativeSet.inspect.impact.json");
    let circuit = load_circuit(&directory, "NativeSet.inspect.zkir");
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let inspect_inputs = |enabled| {
        BTreeMap::from([
            ("bucket".into(), json!("1")),
            ("enabled".into(), json!(enabled)),
        ])
    };
    let initial = initial_state(&inspect);
    let skipped_empty = prepare(
        &inspect,
        &inspect_inputs(false),
        &initial,
        parameters,
        address,
    )
    .unwrap();
    assert_eq!(
        check(&skipped_empty, &circuit).unwrap(),
        skipped_empty.activity_schedule
    );
    assert_eq!(skipped_empty.returns_json()["registeredEmpty"], json!(true));
    assert_eq!(skipped_empty.returns_json()["groupsEmpty"], json!(true));
    assert_eq!(skipped_empty.returns_json()["selectedEmpty"], json!(false));
    assert!(
        prepare(
            &inspect,
            &inspect_inputs(true),
            &initial,
            parameters,
            address
        )
        .is_err()
    );

    let change = |state: &ChargedState<Db>, tag: u8, clearing: bool| {
        prepare(
            &update,
            &inputs(1, tag, !clearing, false, clearing),
            state,
            parameters,
            address,
        )
        .unwrap()
        .after
        .state
    };
    let one_member = change(&initial, 7, false);
    let two_members = change(&one_member, 8, false);
    let skipped_one = prepare(
        &inspect,
        &inspect_inputs(false),
        &one_member,
        parameters,
        address,
    )
    .unwrap();
    let skipped_two = prepare(
        &inspect,
        &inspect_inputs(false),
        &two_members,
        parameters,
        address,
    )
    .unwrap();
    assert_eq!(
        check(&skipped_one, &circuit).unwrap(),
        skipped_one.activity_schedule
    );
    assert_eq!(
        check(&skipped_two, &circuit).unwrap(),
        skipped_two.activity_schedule
    );
    assert_eq!(skipped_one.returns_json(), skipped_two.returns_json());
    assert_eq!(skipped_one.returns_json()["selectedEmpty"], json!(false));
    assert_eq!(
        skipped_one.preimage.public_transcript_inputs,
        skipped_two.preimage.public_transcript_inputs
    );
    assert_eq!(skipped_one.after.state, one_member);
    assert_eq!(skipped_two.after.state, two_members);

    let active_one = prepare(
        &inspect,
        &inspect_inputs(true),
        &one_member,
        parameters,
        address,
    )
    .unwrap();
    let active_two = prepare(
        &inspect,
        &inspect_inputs(true),
        &two_members,
        parameters,
        address,
    )
    .unwrap();
    assert_eq!(
        check(&active_one, &circuit).unwrap(),
        active_one.activity_schedule
    );
    assert_eq!(
        check(&active_two, &circuit).unwrap(),
        active_two.activity_schedule
    );
    assert_eq!(active_one.returns_json()["selectedEmpty"], json!(false));
    assert_eq!(active_two.returns_json()["selectedEmpty"], json!(false));
    assert_eq!(
        active_one.preimage.public_transcript_outputs,
        active_two.preimage.public_transcript_outputs
    );
    assert_eq!(
        active_one.preimage.public_transcript_inputs,
        active_two.preimage.public_transcript_inputs
    );

    let cleared = change(&two_members, 7, true);
    let after_clear = prepare(
        &inspect,
        &inspect_inputs(true),
        &cleared,
        parameters,
        address,
    )
    .unwrap();
    assert_eq!(
        check(&after_clear, &circuit).unwrap(),
        after_clear.activity_schedule
    );
    assert_eq!(after_clear.returns_json()["registeredEmpty"], json!(true));
    assert_eq!(after_clear.returns_json()["groupsEmpty"], json!(false));
    assert_eq!(after_clear.returns_json()["selectedEmpty"], json!(true));
}
