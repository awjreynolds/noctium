#![cfg(feature = "zkir-321")]

use anyhow::{Result, ensure};
use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use noctium_runtime::{Db, Execution, Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs, path::PathBuf};
use transient_crypto::fab::AlignedValueExt;

const COMPACT_VERSION: &str = "0.36.1 (7fa3a117c 2026-11-11)";

fn artifacts() -> Result<PathBuf> {
    Ok(PathBuf::from(env::var_os("NOCTIUM_NESTED_OPAQUE_MAP_DIR").ok_or_else(
        || anyhow::anyhow!("set fresh NestedOpaqueMap artifacts in NOCTIUM_NESTED_OPAQUE_MAP_DIR"),
    )?))
}

fn compact_reference() -> Result<Json> {
    let path = env::var_os("NOCTIUM_NESTED_OPAQUE_MAP_COMPACT_JSON").ok_or_else(|| {
        anyhow::anyhow!("set the pinned Compact output in NOCTIUM_NESTED_OPAQUE_MAP_COMPACT_JSON")
    })?;
    Ok(serde_json::from_slice(&fs::read(path)?)?)
}

fn fixture(directory: &PathBuf, entry: &str) -> Result<(Plan, IrSource)> {
    let stem = format!("NestedOpaqueMap.{entry}");
    let plan = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let circuit = IrSource::load(
        fs::read(directory.join(format!("{stem}.zkir")))?.as_slice(),
    )?;
    Ok((plan, circuit))
}

fn bytes_json(value: &[u8]) -> Json {
    json!({"kind": "bytes", "values": value})
}

fn opaque_bytes_json(value: &[u8]) -> Json {
    json!({"kind": "opaqueBytes", "values": value})
}

fn opaque_string_json(value: &str) -> Json {
    json!({"kind": "opaqueString", "value": value})
}

fn owner(byte: u8) -> [u8; 32] {
    [byte; 32]
}

fn key(byte: u8) -> [u8; 32] {
    [byte; 32]
}

fn aligned_bytes32(value: &[u8; 32]) -> AlignedValue {
    AlignedValue::new(
        FabValue(vec![ValueAtom::from(value.as_slice())]),
        Alignment::singleton(AlignmentAtom::Bytes { length: 32 }),
    )
    .expect("canonical Bytes32 Map key")
}

fn compressed(value: &[u8]) -> AlignedValue {
    AlignedValue::new(
        FabValue(vec![ValueAtom::from(value)]),
        Alignment::singleton(AlignmentAtom::Compress),
    )
    .expect("canonical opaque Compress value")
}

fn store_bytes_inputs(owner_byte: u8, key_byte: u8, payload: &[u8]) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("owner".into(), bytes_json(&owner(owner_byte))),
        ("key".into(), bytes_json(&key(key_byte))),
        ("payload".into(), opaque_bytes_json(payload)),
    ])
}

fn store_string_inputs(owner_byte: u8, key_byte: u8, value: &str) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("owner".into(), bytes_json(&owner(owner_byte))),
        ("key".into(), bytes_json(&key(key_byte))),
        ("value".into(), opaque_string_json(value)),
    ])
}

fn path_inputs(owner_byte: u8, key_byte: u8) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("owner".into(), bytes_json(&owner(owner_byte))),
        ("key".into(), bytes_json(&key(key_byte))),
    ])
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
    assert_eq!(check(&execution, &operation.1)?, execution.activity_schedule);
    Ok(execution)
}

fn assert_bool(execution: &Execution, expected: bool) {
    assert_eq!(execution.returns_json().get("found"), Some(&json!(expected)));
    assert_eq!(execution.returns().len(), 1);
    assert_eq!(execution.returns()[0].0, "found");
    assert_eq!(execution.returns()[0].1.public_json(), json!(expected));
}

fn assert_opaque_read(execution: &Execution, name: &str, expected: Json, raw: &[u8]) {
    assert_eq!(execution.returns_json().get(name), Some(&expected));
    let returns = execution.returns();
    assert_eq!(returns.len(), 1);
    assert_eq!(returns[0].0, name);
    assert_eq!(returns[0].1.public_json(), expected);

    let mut projection = Vec::new();
    compressed(raw).value_only_field_repr(&mut projection);
    assert!(execution.preimage.public_transcript_outputs.ends_with(&projection));
}

fn assert_nested_value(
    state: &ChargedState<Db>,
    plan: &Plan,
    map_name: &str,
    owner_byte: u8,
    key_byte: u8,
    expected: &[u8],
) {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected nested opaque Map state slots");
    };
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == map_name)
        .expect("nested Map declaration");
    let StateValue::Map(owners) = &*slots.get(slot).expect("nested Map state slot") else {
        panic!("expected nested opaque outer Map");
    };
    let owner_key = aligned_bytes32(&owner(owner_byte));
    let owner_bucket = owners.get(&owner_key).expect("owner bucket initialized");
    let StateValue::Map(entries) = &**owner_bucket else {
        panic!("expected inner opaque Map");
    };
    let entry_key = aligned_bytes32(&key(key_byte));
    let entry = entries.get(&entry_key).expect("nested opaque entry exists");
    let StateValue::Cell(value) = &**entry else {
        panic!("expected an opaque value Cell at each inner Map leaf");
    };
    assert_eq!(**value, compressed(expected));
}

fn assert_bucket_sizes(
    state: &ChargedState<Db>,
    plan: &Plan,
    map_name: &str,
    expected_owner_count: usize,
    owner_one_size: usize,
    owner_two_size: usize,
) {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected nested opaque Map state slots");
    };
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == map_name)
        .expect("nested Map declaration");
    let StateValue::Map(owners) = &*slots.get(slot).expect("nested Map state slot") else {
        panic!("expected nested opaque outer Map");
    };
    assert_eq!(owners.size(), expected_owner_count);
    for (owner_byte, expected_size) in [(0x11, owner_one_size), (0x22, owner_two_size)] {
        let owner_key = aligned_bytes32(&owner(owner_byte));
        let owner_bucket = owners.get(&owner_key).expect("owner bucket exists");
        let StateValue::Map(entries) = &**owner_bucket else {
            panic!("expected inner opaque Map");
        };
        assert_eq!(entries.size(), expected_size);
    }
}

fn decode_hex(value: &str) -> Result<Vec<u8>> {
    ensure!(value.len() % 2 == 0, "Compact returned an odd-length byte string");
    value
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let digits = std::str::from_utf8(pair)?;
            Ok(u8::from_str_radix(digits, 16)?)
        })
        .collect()
}

#[test]
#[ignore = "requires fresh Lean artifacts and pinned Compact output in NOCTIUM_NESTED_OPAQUE_MAP_DIR and NOCTIUM_NESTED_OPAQUE_MAP_COMPACT_JSON"]
fn nested_opaque_maps_match_compact_and_bind_exact_compress_payloads() -> Result<()> {
    let compact = compact_reference()?;
    assert_eq!(compact["compact"], COMPACT_VERSION);
    assert_eq!(compact["runtime"], "0.21.0");

    let directory = artifacts()?;
    let store_bytes = fixture(&directory, "storeBytes")?;
    let has_bytes = fixture(&directory, "hasBytes")?;
    let read_bytes = fixture(&directory, "readBytes")?;
    let store_string = fixture(&directory, "storeString")?;
    let has_string = fixture(&directory, "hasString")?;
    let read_string = fixture(&directory, "readString")?;

    let config = BTreeMap::from([
        ("byteBuckets".into(), json!([])),
        ("stringBuckets".into(), json!([])),
    ]);
    let mut state = create_state(&store_bytes.0, &config)?;
    let byte_cases = [
        ("ownerOneEmpty", 0x11, 0x44),
        ("ownerOneBinary", 0x11, 0x55),
        ("ownerTwoSameKey", 0x22, 0x44),
    ];
    for (name, owner_byte, key_byte) in byte_cases {
        let payload = decode_hex(compact["byteReads"][name].as_str().expect("Compact byte hex"))?;
        let stored = run(
            &store_bytes,
            &store_bytes_inputs(owner_byte, key_byte, &payload),
            &state,
        )?;
        assert!(stored.returns().is_empty());
        assert_nested_value(
            &stored.after.state,
            &store_bytes.0,
            "byteBuckets",
            owner_byte,
            key_byte,
            &payload,
        );
        state = stored.after.state;
    }

    let string_cases = [
        ("ownerOneText", 0x11, 0x44),
        ("ownerOneSibling", 0x11, 0x55),
        ("ownerTwoSameKey", 0x22, 0x44),
    ];
    for (name, owner_byte, key_byte) in string_cases {
        let value = compact["stringReads"][name]
            .as_str()
            .expect("Compact raw string");
        let stored = run(
            &store_string,
            &store_string_inputs(owner_byte, key_byte, value),
            &state,
        )?;
        assert!(stored.returns().is_empty());
        assert_nested_value(
            &stored.after.state,
            &store_string.0,
            "stringBuckets",
            owner_byte,
            key_byte,
            value.as_bytes(),
        );
        state = stored.after.state;
    }

    assert_bucket_sizes(&state, &store_bytes.0, "byteBuckets", 2, 2, 1);
    assert_bucket_sizes(&state, &store_bytes.0, "stringBuckets", 2, 2, 1);

    for (name, owner_byte, key_byte) in byte_cases {
        let payload = decode_hex(compact["byteReads"][name].as_str().expect("Compact byte hex"))?;
        let inputs = path_inputs(owner_byte, key_byte);
        let present = run(&has_bytes, &inputs, &state)?;
        assert_bool(&present, compact["bytePresence"][name].as_bool().unwrap());
        let read = run(&read_bytes, &inputs, &state)?;
        assert_opaque_read(
            &read,
            "payload",
            opaque_bytes_json(&payload),
            &payload,
        );
    }

    for (name, owner_byte, key_byte) in string_cases {
        let value = compact["stringReads"][name]
            .as_str()
            .expect("Compact raw string");
        let inputs = path_inputs(owner_byte, key_byte);
        let present = run(&has_string, &inputs, &state)?;
        assert_bool(&present, compact["stringPresence"][name].as_bool().unwrap());
        let read = run(&read_string, &inputs, &state)?;
        assert_opaque_read(
            &read,
            "value",
            opaque_string_json(value),
            value.as_bytes(),
        );
    }

    let missing_child = path_inputs(0x11, 0x66);
    let missing_owner = path_inputs(0x33, 0x44);
    let missing_byte_child = run(&has_bytes, &missing_child, &state)?;
    assert_bool(
        &missing_byte_child,
        compact["bytePresence"]["missingKey"].as_bool().unwrap(),
    );
    let missing_byte_owner = run(&has_bytes, &missing_owner, &state)?;
    assert_bool(
        &missing_byte_owner,
        compact["bytePresence"]["missingOwner"].as_bool().unwrap(),
    );
    let missing_string_child = run(&has_string, &missing_child, &state)?;
    assert_bool(
        &missing_string_child,
        compact["stringPresence"]["missingKey"].as_bool().unwrap(),
    );
    let missing_string_owner = run(&has_string, &missing_owner, &state)?;
    assert_bool(
        &missing_string_owner,
        compact["stringPresence"]["missingOwner"].as_bool().unwrap(),
    );

    for (operation, inputs) in [(&read_bytes, &missing_child), (&read_bytes, &missing_owner)] {
        assert!(prepare(
            &operation.0,
            inputs,
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .is_err());
    }
    for (operation, inputs) in [(&read_string, &missing_child), (&read_string, &missing_owner)] {
        assert!(prepare(
            &operation.0,
            inputs,
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .is_err());
    }

    ensure!(compact["missingReadsRejected"]["byteChild"].as_bool() == Some(true));
    ensure!(compact["missingReadsRejected"]["byteOwner"].as_bool() == Some(true));
    ensure!(compact["missingReadsRejected"]["stringChild"].as_bool() == Some(true));
    ensure!(compact["missingReadsRejected"]["stringOwner"].as_bool() == Some(true));
    Ok(())
}
