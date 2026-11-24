#![cfg(feature = "zkir-321")]

use anyhow::Result;
use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use noctium_runtime::{Db, Execution, Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs::File, path::Path};

fn load(directory: &Path, entry: &str) -> Result<(Plan, IrSource)> {
    let stem = format!("NestedRecordKeyByteValues.{entry}");
    let plan = serde_json::from_reader(File::open(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let circuit = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;
    Ok((plan, circuit))
}

fn bytes(value: &[u8]) -> Json {
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

fn aligned_pair(first: &[u8], second: &[u8]) -> AlignedValue {
    AlignedValue::concat(&[aligned_bytes(first), aligned_bytes(second)])
}

fn compact_bytes(value: &Json) -> Vec<u8> {
    value["values"]
        .as_array()
        .expect("Compact byte value")
        .iter()
        .map(|byte| byte.as_u64().expect("Compact byte") as u8)
        .collect()
}

fn id(last: u8) -> [u8; 33] {
    let mut value = [3; 33];
    value[32] = last;
    value
}

fn digest(last: u8) -> [u8; 33] {
    let mut value = [6; 33];
    value[32] = last;
    value
}

fn owner(byte: u8) -> [u8; 32] {
    [byte; 32]
}

fn store_inputs(owner_byte: u8, id: &[u8], label: &[u8], digest: &[u8]) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("owner".into(), bytes(&owner(owner_byte))),
        ("tag".into(), bytes(&[7])),
        ("id".into(), bytes(id)),
        ("label".into(), bytes(label)),
        ("digest".into(), bytes(digest)),
    ])
}

fn lookup_inputs(owner_byte: u8, id: &[u8]) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("owner".into(), bytes(&owner(owner_byte))),
        ("tag".into(), bytes(&[7])),
        ("id".into(), bytes(id)),
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

fn assert_survivors(state: &ChargedState<Db>, compact: &Json) -> Result<()> {
    let StateValue::Array(slots) = state.get_ref() else {
        anyhow::bail!("expected contract state slots");
    };
    let Some(StateValue::Map(owners)) = slots.first() else {
        anyhow::bail!("expected the outer owner Map state");
    };
    assert_eq!(
        owners.size(),
        compact["ownerBucketsAfterRemoval"].as_u64().unwrap() as usize
    );

    let owner_a = owners
        .get(&aligned_bytes(&owner(1)))
        .expect("owner A bucket remains after removal");
    let StateValue::Map(owner_a_profiles) = &*owner_a else {
        anyhow::bail!("expected owner A's nested Profile Map");
    };
    assert_eq!(
        owner_a_profiles.size(),
        compact["entriesPerParentAfterRemoval"][0]
            .as_u64()
            .unwrap() as usize
    );
    assert!(owner_a_profiles.get(&aligned_pair(&[7], &id(4))).is_none());
    let sibling = owner_a_profiles
        .get(&aligned_pair(&[7], &id(5)))
        .expect("owner A's sibling profile remains at its record key");
    let StateValue::Cell(sibling) = &*sibling else {
        anyhow::bail!("expected sibling Profile in one native cell");
    };
    assert_eq!(
        **sibling,
        aligned_pair(
            &compact_bytes(&compact["outputs"]["survivingSibling"]["label"]),
            &compact_bytes(&compact["outputs"]["survivingSibling"]["digest"]),
        )
    );

    let owner_b = owners
        .get(&aligned_bytes(&owner(2)))
        .expect("owner B bucket remains");
    let StateValue::Map(owner_b_profiles) = &*owner_b else {
        anyhow::bail!("expected owner B's nested Profile Map");
    };
    assert_eq!(
        owner_b_profiles.size(),
        compact["entriesPerParentAfterRemoval"][1]
            .as_u64()
            .unwrap() as usize
    );
    let other_owner = owner_b_profiles
        .get(&aligned_pair(&[7], &id(4)))
        .expect("owner B's profile remains at the shared record key");
    let StateValue::Cell(other_owner) = &*other_owner else {
        anyhow::bail!("expected owner B Profile in one native cell");
    };
    assert_eq!(
        **other_owner,
        aligned_pair(
            &compact_bytes(&compact["outputs"]["survivingOtherOwner"]["label"]),
            &compact_bytes(&compact["outputs"]["survivingOtherOwner"]["digest"]),
        )
    );
    Ok(())
}

#[test]
#[ignore = "requires fresh NestedRecordKeyByteValues Impact/ZKIR artifacts and Compact output JSON"]
fn nested_record_byte_keys_match_compact_and_preserve_parent_buckets() -> Result<()> {
    let artifacts_directory = env::var_os("NOCTIUM_NESTED_RECORD_KEY_BYTE_VALUES_DIR")
        .map(std::path::PathBuf::from)
        .expect("NOCTIUM_NESTED_RECORD_KEY_BYTE_VALUES_DIR must point at fresh Noctium artifacts");
    let compact_path = env::var_os("NOCTIUM_NESTED_RECORD_KEY_BYTE_VALUES_COMPACT")
        .map(std::path::PathBuf::from)
        .expect("NOCTIUM_NESTED_RECORD_KEY_BYTE_VALUES_COMPACT must point at Compact output JSON");
    let compact: Json = serde_json::from_reader(File::open(compact_path)?)?;
    assert_eq!(compact["compact"], "0.36.1 (7fa3a117c 2026-11-11)");
    assert_eq!(compact["runtime"], "0.21.0");

    let store = load(&artifacts_directory, "store")?;
    let lookup = load(&artifacts_directory, "lookup")?;
    let remove = load(&artifacts_directory, "remove")?;
    let config = BTreeMap::from([("profiles".into(), json!([]))]);
    let mut state = create_state(&store.0, &config)?;

    let first_id = id(4);
    let sibling_id = id(5);
    let first_digest = digest(4);
    let sibling_digest = digest(5);
    let other_owner_digest = digest(6);
    let initial_first = run(
        &store,
        &store_inputs(1, &first_id, &[11], &first_digest),
        &state,
    )?;
    state = initial_first.after.state;
    let first_lookup = run(&lookup, &lookup_inputs(1, &first_id), &state)?;
    assert_eq!(outputs(&first_lookup), compact["outputs"]["initialFirst"]);

    let initial_sibling = run(
        &store,
        &store_inputs(1, &sibling_id, &[12], &sibling_digest),
        &state,
    )?;
    state = initial_sibling.after.state;
    let sibling_lookup = run(&lookup, &lookup_inputs(1, &sibling_id), &state)?;
    assert_eq!(outputs(&sibling_lookup), compact["outputs"]["initialSibling"]);

    let initial_other_owner = run(
        &store,
        &store_inputs(2, &first_id, &[21], &other_owner_digest),
        &state,
    )?;
    state = initial_other_owner.after.state;
    let other_owner_lookup = run(&lookup, &lookup_inputs(2, &first_id), &state)?;
    assert_eq!(
        outputs(&other_owner_lookup),
        compact["outputs"]["initialOtherOwner"]
    );

    let overwritten = run(
        &store,
        &store_inputs(1, &first_id, &[13], &digest(7)),
        &state,
    )?;
    state = overwritten.after.state;
    let overwrite_lookup = run(&lookup, &lookup_inputs(1, &first_id), &state)?;
    assert_eq!(outputs(&overwrite_lookup), compact["outputs"]["overwritten"]);

    let remove_result = run(&remove, &lookup_inputs(1, &first_id), &state)?;
    state = remove_result.after.state;
    assert_eq!(compact["entriesPerParentAfterRemoval"], json!([1, 1]));
    assert_survivors(&state, &compact)?;

    let surviving_sibling = run(&lookup, &lookup_inputs(1, &sibling_id), &state)?;
    assert_eq!(
        outputs(&surviving_sibling),
        compact["outputs"]["survivingSibling"]
    );
    let surviving_other_owner = run(&lookup, &lookup_inputs(2, &first_id), &state)?;
    assert_eq!(
        outputs(&surviving_other_owner),
        compact["outputs"]["survivingOtherOwner"]
    );

    let wrong_id = [3; 32];
    assert!(run(&lookup, &lookup_inputs(1, &wrong_id), &state).is_err());
    assert_eq!(compact["wrongIdWidthRejected"], true);
    assert!(run(
        &store,
        &store_inputs(1, &first_id, &[13], &[6; 32]),
        &state,
    )
    .is_err());
    assert_eq!(compact["wrongDigestWidthRejected"], true);
    assert!(run(&lookup, &lookup_inputs(1, &first_id), &state).is_err());
    assert_eq!(compact["removedLookupRejected"], true);
    Ok(())
}
