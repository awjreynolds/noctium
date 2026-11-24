#![cfg(feature = "zkir-321")]

use anyhow::Result;
use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use noctium_runtime::{Db, Execution, Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs::File, path::Path};

fn load(directory: &Path, entry: &str) -> Result<(Plan, IrSource)> {
    let stem = format!("NestedFixedByteMapRecordValues.{entry}");
    let plan = serde_json::from_reader(File::open(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let circuit = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;
    Ok((plan, circuit))
}

fn bytes_value(value: &[u8]) -> Json {
    json!({"kind": "bytes", "values": value})
}

fn aligned_bytes(value: &[u8]) -> AlignedValue {
    AlignedValue::new(
        FabValue(vec![ValueAtom::from(value)]),
        Alignment::singleton(AlignmentAtom::Bytes {
            length: value.len() as u32,
        }),
    )
    .unwrap()
}

fn aligned_profile(label: &[u8], digest: &[u8]) -> AlignedValue {
    AlignedValue::concat(&[aligned_bytes(label), aligned_bytes(digest)])
}

fn digest(last: u8) -> [u8; 33] {
    let mut value = [3; 33];
    value[32] = last;
    value
}

fn owner(byte: u8) -> [u8; 32] {
    [byte; 32]
}

fn initialize_inputs(owner: &[u8; 32]) -> BTreeMap<String, Json> {
    BTreeMap::from([("owner".into(), bytes_value(owner))])
}

fn exercise_inputs() -> BTreeMap<String, Json> {
    let first_key = [0x10; 32];
    let sibling_key = [0x20; 32];
    BTreeMap::from([
        ("ownerA".into(), bytes_value(&owner(1))),
        ("ownerB".into(), bytes_value(&owner(2))),
        ("firstKey".into(), bytes_value(&first_key)),
        ("siblingKey".into(), bytes_value(&sibling_key)),
        ("inputFirstLabel".into(), bytes_value(&[11])),
        ("inputFirstDigest".into(), bytes_value(&digest(4))),
        ("inputSiblingLabel".into(), bytes_value(&[12])),
        ("inputSiblingDigest".into(), bytes_value(&digest(5))),
        ("inputOwnerBLabel".into(), bytes_value(&[21])),
        ("inputOwnerBDigest".into(), bytes_value(&digest(6))),
        ("replacementLabel".into(), bytes_value(&[13])),
        ("replacementDigest".into(), bytes_value(&digest(7))),
    ])
}

fn inspect_inputs() -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("ownerA".into(), bytes_value(&owner(1))),
        ("ownerB".into(), bytes_value(&owner(2))),
        ("firstKey".into(), bytes_value(&[0x10; 32])),
        ("siblingKey".into(), bytes_value(&[0x20; 32])),
    ])
}

fn outputs(execution: &Execution) -> Json {
    Json::Object(execution.returns_json().into_iter().collect())
}

fn run(
    operation: &(Plan, IrSource),
    inputs: &BTreeMap<String, Json>,
    state: &ChargedState<Db>,
) -> Result<Execution> {
    let execution = prepare(
        &operation.0,
        inputs,
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    check(&execution, &operation.1)?;
    Ok(execution)
}

fn empty_state(plan: &Plan) -> Result<ChargedState<Db>> {
    create_state(plan, &BTreeMap::from([("profiles".into(), json!([]))]))
}

fn assert_surviving_profiles(
    state: &ChargedState<Db>,
    compact: &Json,
    sibling_label: &[u8],
    sibling_digest: &[u8],
    owner_b_label: &[u8],
    owner_b_digest: &[u8],
) -> Result<()> {
    let StateValue::Array(slots) = state.get_ref() else {
        anyhow::bail!("expected contract state slots");
    };
    let Some(StateValue::Map(owners)) = slots.first() else {
        anyhow::bail!("expected the outer owner Map state");
    };
    assert_eq!(owners.size(), compact["parents"]["buckets"].as_u64().unwrap() as usize);

    let owner_a_key: AlignedValue = owner(1).into();
    let owner_a = owners.get(&owner_a_key).expect("owner A bucket exists");
    let StateValue::Map(owner_a_profiles) = &**owner_a else {
        anyhow::bail!("expected owner A's nested Profile Map");
    };
    let counts = compact["entriesPerParentAfterRemoval"]
        .as_array()
        .expect("Compact per-parent counts");
    assert_eq!(owner_a_profiles.size(), counts[0].as_u64().unwrap() as usize);
    let first_key: AlignedValue = [0x10; 32].into();
    assert!(owner_a_profiles.get(&first_key).is_none());
    let sibling_key: AlignedValue = [0x20; 32].into();
    let sibling = owner_a_profiles
        .get(&sibling_key)
        .expect("sibling profile remains at exact byte key");
    let StateValue::Cell(sibling) = &**sibling else {
        anyhow::bail!("expected sibling Profile in one native cell");
    };
    assert_eq!(**sibling, aligned_profile(sibling_label, sibling_digest));

    let owner_b_key: AlignedValue = owner(2).into();
    let owner_b = owners.get(&owner_b_key).expect("owner B bucket exists");
    let StateValue::Map(owner_b_profiles) = &**owner_b else {
        anyhow::bail!("expected owner B's nested Profile Map");
    };
    assert_eq!(owner_b_profiles.size(), counts[1].as_u64().unwrap() as usize);
    let owner_b_profile = owner_b_profiles
        .get(&first_key)
        .expect("owner B profile remains at shared byte key");
    let StateValue::Cell(owner_b_profile) = &**owner_b_profile else {
        anyhow::bail!("expected owner B Profile in one native cell");
    };
    assert_eq!(
        **owner_b_profile,
        aligned_profile(owner_b_label, owner_b_digest)
    );
    Ok(())
}

#[test]
#[ignore = "requires fresh NestedFixedByteMapRecordValues artifacts and Compact output JSON"]
fn nested_fixed_byte_record_values_match_compact_and_preserve_survivors() -> Result<()> {
    let artifacts_directory = env::var_os("NOCTIUM_NESTED_FIXED_BYTE_RECORD_VALUES_DIR")
        .map(std::path::PathBuf::from)
        .expect("NOCTIUM_NESTED_FIXED_BYTE_RECORD_VALUES_DIR must point at fresh Noctium artifacts");
    let compact_path = env::var_os("NOCTIUM_NESTED_FIXED_BYTE_RECORD_VALUES_COMPACT")
        .map(std::path::PathBuf::from)
        .expect("NOCTIUM_NESTED_FIXED_BYTE_RECORD_VALUES_COMPACT must point at Compact output JSON");
    let compact: Json = serde_json::from_reader(File::open(compact_path)?)?;
    assert_eq!(compact["compact"], "0.36.1 (7fa3a117c 2026-11-11)");
    assert_eq!(compact["runtime"], "0.21.0");

    let initialize = load(&artifacts_directory, "initializeOwner")?;
    let exercise = load(&artifacts_directory, "exercise")?;
    let inspect = load(&artifacts_directory, "inspect")?;
    let lookup_absent = load(&artifacts_directory, "lookupAbsent")?;
    let mut state = empty_state(&exercise.0)?;
    for owner_byte in [1, 2] {
        state = run(&initialize, &initialize_inputs(&owner(owner_byte)), &state)?.after.state;
    }

    let inputs = exercise_inputs();
    let first_digest = digest(4);
    let sibling_label = [12];
    let sibling_digest = digest(5);
    let owner_b_label = [21];
    let owner_b_digest = digest(6);
    let exercise_result = run(&exercise, &inputs, &state)?;
    assert_eq!(outputs(&exercise_result), compact["outputs"]);
    assert_surviving_profiles(
        &exercise_result.after.state,
        &compact,
        &sibling_label,
        &sibling_digest,
        &owner_b_label,
        &owner_b_digest,
    )?;

    let mut wrong_width = inputs.clone();
    wrong_width.insert(
        "inputFirstDigest".into(),
        bytes_value(&first_digest[..32]),
    );
    assert!(run(&exercise, &wrong_width, &state).is_err());
    assert_eq!(compact["wrongDigestWidthRejected"], true);

    let inspect_result = run(&inspect, &inspect_inputs(), &exercise_result.after.state)?;
    assert_eq!(
        outputs(&inspect_result),
        json!({
            "firstPresent": false,
            "siblingPresent": true,
            "ownerBPresent": true,
            "siblingLabel": bytes_value(&sibling_label),
            "siblingDigest": bytes_value(&sibling_digest),
            "ownerBLabel": bytes_value(&owner_b_label),
            "ownerBDigest": bytes_value(&owner_b_digest),
        }),
    );

    let absent_inputs = BTreeMap::from([
        ("owner".into(), bytes_value(&owner(1))),
        ("missingKey".into(), bytes_value(&[0x10; 32])),
    ]);
    assert!(run(&lookup_absent, &absent_inputs, &exercise_result.after.state).is_err());
    assert_eq!(compact["absentLookupRejectedWithoutChangingSiblingOrOtherParent"], true);
    let after_rejected_lookup = run(&inspect, &inspect_inputs(), &exercise_result.after.state)?;
    assert_eq!(outputs(&after_rejected_lookup), outputs(&inspect_result));
    assert_surviving_profiles(
        &exercise_result.after.state,
        &compact,
        &sibling_label,
        &sibling_digest,
        &owner_b_label,
        &owner_b_digest,
    )?;
    Ok(())
}
