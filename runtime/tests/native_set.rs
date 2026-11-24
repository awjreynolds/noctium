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

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_NOMINAL_FIELD_RECORD_SET_DIR"]
fn nominal_field_record_set_keeps_exact_native_key() -> anyhow::Result<()> {
    let directory = std::path::PathBuf::from(
        std::env::var_os("NOCTIUM_NOMINAL_FIELD_RECORD_SET_DIR")
            .expect("nominal Field record Set artifacts"),
    );
    let plan = load_plan(
        &directory,
        "NominalFieldRecordSet.RecordSet.update.impact.json",
    );
    let circuit = load_circuit(&directory, "NominalFieldRecordSet.RecordSet.update.zkir");
    let mut state = create_state(&plan, &BTreeMap::from([("members".into(), json!([]))]))?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let inputs = |adding, removing| {
        BTreeMap::from([
            ("amount".into(), json!("17")),
            ("adding".into(), json!(adding)),
            ("removing".into(), json!(removing)),
        ])
    };
    let key = field_value(Fr::from(17u8));

    let inserted = prepare(&plan, &inputs(true, false), &state, parameters, address)?;
    check(&inserted, &circuit)?;
    let returns = inserted.returns_json();
    assert_eq!(returns["before"], json!(false));
    assert_eq!(returns["afterInsert"], json!(true));
    assert_eq!(returns["afterRemove"], json!(true));
    state = inserted.after.state;
    let StateValue::Array(slots) = state.get_ref() else {
        anyhow::bail!("expected state slots");
    };
    let Some(StateValue::Map(members)) = slots.get(0) else {
        anyhow::bail!("expected root record Set");
    };
    assert_eq!(members.size(), 1);
    let value = members
        .get(&key)
        .expect("exact Native field record key exists");
    assert!(matches!(&*value, StateValue::Null));

    let removed = prepare(&plan, &inputs(false, true), &state, parameters, address)?;
    check(&removed, &circuit)?;
    let returns = removed.returns_json();
    assert_eq!(returns["before"], json!(true));
    assert_eq!(returns["afterInsert"], json!(true));
    assert_eq!(returns["afterRemove"], json!(false));
    let StateValue::Array(slots) = removed.after.state.get_ref() else {
        anyhow::bail!("expected state slots after removal");
    };
    let Some(StateValue::Map(members)) = slots.get(0) else {
        anyhow::bail!("expected root record Set after removal");
    };
    assert_eq!(members.size(), 0);
    assert!(members.get(&key).is_none());
    Ok(())
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_RECORD_SET_COLLECTIONS_DIR"]
fn typed_record_set_reports_size_and_resets() -> anyhow::Result<()> {
    let directory = std::path::PathBuf::from(std::env::var("NOCTIUM_RECORD_SET_COLLECTIONS_DIR")?);
    let plan = load_plan(&directory, "RecordSetCollections.update.impact.json");
    let circuit = load_circuit(&directory, "RecordSetCollections.update.zkir");
    let initial = create_state(&plan, &BTreeMap::from([("memoSet".into(), json!([]))]))?;
    let mut state = initial.clone();
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    for (active, adding, clear, size) in [
        (true, false, false, 0),
        (true, true, false, 1),
        (false, true, false, 2),
        (true, false, false, 2),
        (false, false, true, 0),
    ] {
        let inputs = BTreeMap::from([
            ("active".into(), json!(active)),
            ("amount".into(), json!("513")),
            ("adding".into(), json!(adding)),
            ("clear".into(), json!(clear)),
        ]);
        let step = prepare(&plan, &inputs, &state, parameters, address)?;
        assert_eq!(check(&step, &circuit)?, step.activity_schedule);
        let returns = step.returns_json();
        assert_eq!(returns["size"], json!(size.to_string()));
        assert_eq!(returns["isEmpty"], json!(size == 0));
        if !adding && !clear {
            assert_eq!(step.after.state.get_ref(), state.get_ref());
        }
        state = step.after.state;
    }
    assert_eq!(state.get_ref(), initial.get_ref());
    Ok(())
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_NESTED_RECORD_SET_DIR"]
fn nested_record_set_preserves_members_and_sibling_buckets() -> anyhow::Result<()> {
    let directory = std::path::PathBuf::from(std::env::var("NOCTIUM_NESTED_RECORD_SET_DIR")?);
    let init = load_plan(&directory, "NestedRecordSet.initOwner.impact.json");
    let init_circuit = load_circuit(&directory, "NestedRecordSet.initOwner.zkir");
    let plan = load_plan(&directory, "NestedRecordSet.update.impact.json");
    let circuit = load_circuit(&directory, "NestedRecordSet.update.zkir");
    let mut state = create_state(&plan, &BTreeMap::from([("buckets".into(), json!([]))]))?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let owner_input = |owner: u8| {
        let owner_bytes = [owner; 32];
        json!({"kind": "bytes", "values": owner_bytes.as_slice()})
    };
    for owner in [0x11, 0x22] {
        let args = BTreeMap::from([("owner".into(), owner_input(owner))]);
        let step = prepare(&init, &args, &state, parameters, address)?;
        assert_eq!(check(&step, &init_circuit)?, step.activity_schedule);
        state = step.after.state;
    }
    let inputs = |owner, active, amount: u32, adding, removing| {
        BTreeMap::from([
            ("owner".into(), owner_input(owner)),
            ("active".into(), json!(active)),
            ("amount".into(), json!(amount.to_string())),
            ("adding".into(), json!(adding)),
            ("removing".into(), json!(removing)),
        ])
    };
    for (owner, active, amount, adding, removing, before, after, size) in [
        (0x11, true, 513, true, false, false, true, 1),
        (0x11, true, 513, true, false, true, true, 1),
        (0x11, false, 513, true, false, false, true, 2),
        (0x11, true, 514, false, false, false, false, 2),
        (0x22, true, 513, true, false, false, true, 1),
        (0x11, true, 513, false, true, true, false, 1),
        (0x11, false, 513, false, false, true, true, 1),
        (0x22, true, 513, false, false, true, true, 1),
    ] {
        let args = inputs(owner, active, amount, adding, removing);
        let step = prepare(&plan, &args, &state, parameters, address)?;
        assert_eq!(check(&step, &circuit)?, step.activity_schedule);
        let returns = step.returns_json();
        assert_eq!(returns["presentBefore"], json!(before));
        assert_eq!(returns["presentAfter"], json!(after));
        assert_eq!(returns["bucketSize"], json!(size.to_string()));
        let StateValue::Array(slots) = step.after.state.get_ref() else {
            anyhow::bail!("expected a state array");
        };
        let Some(StateValue::Map(buckets)) = slots.get(0) else {
            anyhow::bail!("expected a Map of Sets");
        };
        let bucket_key: AlignedValue = [owner; 32].into();
        let selected = buckets.get(&bucket_key).expect("selected bucket exists");
        let StateValue::Map(set) = &*selected else {
            anyhow::bail!("expected a Set-backed map in the selected bucket");
        };
        assert_eq!(set.size(), size);
        state = step.after.state;
    }
    assert!(
        prepare(
            &plan,
            &inputs(0x11, true, 65536, true, false),
            &state,
            parameters,
            address
        )
        .is_err()
    );
    let mut wrong_schema = plan.clone();
    wrong_schema.state[0].kind["tree"]["map"][1]["set"]["composite"]["fields"]
        .as_array_mut()
        .expect("nested typed key schema fields")
        .swap(0, 1);
    assert!(
        prepare(
            &wrong_schema,
            &inputs(0x11, true, 513, false, true),
            &state,
            parameters,
            address
        )
        .is_err()
    );
    Ok(())
}

fn bytes_value(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn fixed_bytes_record_key(tag: &[u8], id: &[u8]) -> AlignedValue {
    use base_crypto::fab::{Alignment, AlignmentAtom, Value as FabValue, ValueAtom};

    fn aligned_bytes(value: &[u8]) -> AlignedValue {
        AlignedValue::new(
            FabValue(vec![ValueAtom::from(value)]),
            Alignment::singleton(AlignmentAtom::Bytes {
                length: value.len() as u32,
            }),
        )
        .unwrap()
    }

    AlignedValue::concat(&[aligned_bytes(tag), aligned_bytes(id)])
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_FIXED_BYTE_RECORD_SET_DIR"]
fn fixed_byte_record_set_keys_distinguish_late_bytes_and_sibling_buckets() -> anyhow::Result<()> {
    let directory = std::path::PathBuf::from(
        std::env::var_os("NOCTIUM_FIXED_BYTE_RECORD_SET_DIR")
            .expect("fixed-byte record Set artifacts"),
    );
    let plan = load_plan(&directory, "FixedByteRecordSet.update.impact.json");
    let circuit = load_circuit(&directory, "FixedByteRecordSet.update.zkir");
    let mut state = create_state(&plan, &BTreeMap::from([("buckets".into(), json!([]))]))?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let owner = [1u8; 32];
    let sibling_owner = [2u8; 32];
    let tag = [7u8];
    let first_id = [3u8; 33];
    let mut late_id = first_id;
    late_id[32] = 4;
    let mut absent_id = first_id;
    absent_id[32] = 5;
    let inputs = BTreeMap::from([
        ("owner".into(), bytes_value(&owner)),
        ("siblingOwner".into(), bytes_value(&sibling_owner)),
        ("tag".into(), bytes_value(&tag)),
        ("firstId".into(), bytes_value(&first_id)),
        ("lateId".into(), bytes_value(&late_id)),
        ("missingKeyId".into(), bytes_value(&absent_id)),
    ]);
    let result = prepare(&plan, &inputs, &state, parameters, address)?;
    check(&result, &circuit)?;
    let returns = result.returns_json();
    assert_eq!(returns["first"], json!(true));
    assert_eq!(returns["late"], json!(true));
    assert_eq!(returns["missingKey"], json!(false));
    assert_eq!(returns["sibling"], json!(true));
    assert_eq!(returns["count"], json!("2"));
    assert_eq!(returns["siblingCount"], json!("1"));
    state = result.after.state;

    let StateValue::Array(slots) = state.get_ref() else {
        anyhow::bail!("expected state slots");
    };
    let Some(StateValue::Map(buckets)) = slots.get(0) else {
        anyhow::bail!("expected Bytes32-keyed buckets");
    };
    assert_eq!(buckets.size(), 2);
    let owner_key: AlignedValue = owner.into();
    let sibling_key: AlignedValue = sibling_owner.into();
    let selected = buckets.get(&owner_key).expect("owner bucket exists");
    let sibling = buckets.get(&sibling_key).expect("sibling bucket exists");
    let StateValue::Map(selected_set) = &*selected else {
        anyhow::bail!("expected selected Set");
    };
    let StateValue::Map(sibling_set) = &*sibling else {
        anyhow::bail!("expected sibling Set");
    };
    assert_eq!(selected_set.size(), 2);
    assert_eq!(selected_set.get(&fixed_bytes_record_key(&tag, &first_id)).is_some(), true);
    assert_eq!(selected_set.get(&fixed_bytes_record_key(&tag, &late_id)).is_some(), true);
    assert_eq!(selected_set.get(&fixed_bytes_record_key(&tag, &absent_id)).is_some(), false);
    assert_eq!(sibling_set.size(), 1);
    assert_eq!(sibling_set.get(&fixed_bytes_record_key(&tag, &first_id)).is_some(), true);
    Ok(())
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_ROOT_FIXED_BYTE_RECORD_SET_DIR"]
fn root_fixed_byte_record_set_keeps_exact_late_byte_after_removal() -> anyhow::Result<()> {
    let directory = std::path::PathBuf::from(
        std::env::var_os("NOCTIUM_ROOT_FIXED_BYTE_RECORD_SET_DIR")
            .expect("root fixed-byte record Set artifacts"),
    );
    let plan = load_plan(&directory, "RootFixedByteRecordSet.update.impact.json");
    let circuit = load_circuit(&directory, "RootFixedByteRecordSet.update.zkir");
    let state = create_state(&plan, &BTreeMap::from([("members".into(), json!([]))]))?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let tag = [7u8];
    let first_id = [3u8; 33];
    let mut late_id = first_id;
    late_id[32] = 4;
    let mut inputs = BTreeMap::from([
        ("tag".into(), bytes_value(&tag)),
        ("firstId".into(), bytes_value(&first_id)),
        ("lateId".into(), bytes_value(&late_id)),
    ]);

    let result = prepare(&plan, &inputs, &state, parameters, address)?;
    check(&result, &circuit)?;
    let returns = result.returns_json();
    assert_eq!(returns["first"], json!(true));
    assert_eq!(returns["late"], json!(true));
    assert_eq!(returns["firstAfter"], json!(false));
    assert_eq!(returns["lateAfter"], json!(true));
    assert_eq!(returns["count"], json!("1"));

    let StateValue::Array(slots) = result.after.state.get_ref() else {
        anyhow::bail!("expected state slots");
    };
    let Some(StateValue::Map(members)) = slots.get(0) else {
        anyhow::bail!("expected root Set");
    };
    assert_eq!(members.size(), 1);
    assert!(members.get(&fixed_bytes_record_key(&tag, &first_id)).is_none());
    assert!(members.get(&fixed_bytes_record_key(&tag, &late_id)).is_some());

    inputs.insert("lateId".into(), bytes_value(&late_id[..32]));
    assert!(prepare(&plan, &inputs, &state, parameters, address).is_err());
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

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_RECORD_SET_CONSTRUCTOR_DIR"]
fn record_set_constructor_checks_guard_key_encoding_and_duplicates() -> anyhow::Result<()> {
    let directory = std::path::PathBuf::from(
        std::env::var_os("NOCTIUM_RECORD_SET_CONSTRUCTOR_DIR")
            .expect("record Set constructor artifacts"),
    );
    let plan = load_plan(&directory, "RecordSetConstructor.inspect.impact.json");
    assert!(plan.state[0].sealed);
    let circuit = load_circuit(&directory, "RecordSetConstructor.inspect.zkir");
    let tag = [7];
    let first_id = [3; 33];
    let mut late_id = first_id;
    late_id[32] = 4;
    let inputs = BTreeMap::from([
        ("tag".into(), bytes_value(&tag)),
        ("firstId".into(), bytes_value(&first_id)),
        ("lateId".into(), bytes_value(&late_id)),
    ]);
    let mut arguments = inputs.clone();
    for (enabled, count) in [(false, "1"), (true, "2")] {
        arguments.insert("enabled".into(), json!(enabled));
        let state = noctium_runtime::construct_state(&plan, &arguments)?;
        let execution = prepare(
            &plan,
            &inputs,
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )?;
        check(&execution, &circuit)?;
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([
                ("first".into(), json!(true)),
                ("late".into(), json!(enabled)),
                ("count".into(), json!(count)),
            ])
        );
        assert_eq!(execution.after.state, state);
    }
    arguments.insert("lateId".into(), bytes_value(&late_id[..32]));
    assert!(noctium_runtime::construct_state(&plan, &arguments).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_NOMINAL_FIELD_RECORD_SET_CONSTRUCTOR_DIR"]
fn nominal_field_record_set_constructor_preserves_native_keys() -> anyhow::Result<()> {
    let directory = std::path::PathBuf::from(
        std::env::var_os("NOCTIUM_NOMINAL_FIELD_RECORD_SET_CONSTRUCTOR_DIR")
            .expect("nominal Field record Set constructor artifacts"),
    );
    let entry = "NominalFieldRecordSetConstructor.Registry.inspect";
    let plan = load_plan(&directory, &format!("{entry}.impact.json"));
    let circuit = load_circuit(&directory, &format!("{entry}.zkir"));
    assert!(plan.state[0].sealed);
    for enabled in [false, true] {
        let state = noctium_runtime::construct_state(
            &plan,
            &BTreeMap::from([
                ("seed".into(), json!("17")),
                ("extra".into(), json!("42")),
                ("enabled".into(), json!(enabled)),
            ]),
        )?;
        let StateValue::Array(slots) = state.get_ref() else {
            anyhow::bail!("expected a state array");
        };
        let Some(StateValue::Map(members)) = slots.get(0) else {
            anyhow::bail!("expected a Set-backed map");
        };
        assert_eq!(members.size(), if enabled { 2 } else { 1 });
        for (amount, expected) in [(17u64, true), (42, enabled), (99, false)] {
            assert_eq!(
                members.get(&field_value(Fr::from(amount))).is_some(),
                expected
            );
            let execution = prepare(
                &plan,
                &BTreeMap::from([("amount".into(), json!(amount.to_string()))]),
                &state,
                &ledger::structure::INITIAL_PARAMETERS,
                coin_structure::contract::ContractAddress::default(),
            )?;
            assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
            assert_eq!(execution.returns_json()["isPresent"], json!(expected));
            assert_eq!(execution.after.state, state);
        }
    }
    Ok(())
}
