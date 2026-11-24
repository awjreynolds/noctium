#![cfg(feature = "zkir-321")]

use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::state::StateValue;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;

fn bytes_value(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
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

fn fixed_bytes_record_key(tag: &[u8], id: &[u8]) -> AlignedValue {
    AlignedValue::concat(&[aligned_bytes(tag), aligned_bytes(id)])
}

fn fixed_bytes_record_value(label: &[u8], digest: &[u8]) -> AlignedValue {
    AlignedValue::concat(&[aligned_bytes(label), aligned_bytes(digest)])
}

#[test]
fn root_fixed_byte_record_values_match_compact_for_scalar_and_record_keys() -> anyhow::Result<()> {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/root-fixed-byte-record-valued-map/321/RootFixedByteRecordValuedMap.update.impact.json"
    ))?;
    let circuit = IrSource::load(
        include_bytes!("fixtures/root-fixed-byte-record-valued-map/321/RootFixedByteRecordValuedMap.update.zkir")
            .as_slice(),
    )?;
    let compact: Json = serde_json::from_str(include_str!(
        "fixtures/root-fixed-byte-record-valued-map/compact-0.36.1.json"
    ))?;
    assert_eq!(compact["compact"], "0.36.1 (7fa3a117c 2026-11-11)");
    assert_eq!(compact["runtime"], "0.21.0");
    let state = create_state(
        &plan,
        &BTreeMap::from([
            ("receipts".into(), json!([])),
            ("profiles".into(), json!([])),
        ]),
    )?;

    let empty_state = BTreeMap::from([
        ("receipts".into(), json!([])),
        ("profiles".into(), json!([])),
    ]);
    let mut nested_scalar_json: Json = serde_json::from_str(include_str!(
        "fixtures/root-fixed-byte-record-valued-map/321/RootFixedByteRecordValuedMap.update.impact.json"
    ))?;
    nested_scalar_json["state"][1]["kind"]["tree"] = json!({
        "map": ["Bytes<32>", {"map": ["Bytes<32>", {"composite": {
            "id": "RootFixedByteRecordValuedMap.Profile",
            "fields": [
                {"name": "label", "type": "Bytes<1>"},
                {"name": "digest", "type": "Bytes<33>"}
            ]
        }}]}]
    });
    let nested_scalar_plan: Plan = serde_json::from_value(nested_scalar_json)?;
    assert!(create_state(&nested_scalar_plan, &empty_state).is_err());

    let mut nested_record_key_json: Json = serde_json::from_str(include_str!(
        "fixtures/root-fixed-byte-record-valued-map/321/RootFixedByteRecordValuedMap.update.impact.json"
    ))?;
    nested_record_key_json["state"][0]["kind"]["tree"] = json!({
        "map": ["Bytes<32>", {"map": [
            {"composite": {
                "id": "RootFixedByteRecordValuedMap.Key",
                "fields": [
                    {"name": "tag", "type": "Bytes<1>"},
                    {"name": "id", "type": "Bytes<33>"}
                ]
            }},
            {"composite": {
                "id": "RootFixedByteRecordValuedMap.Receipt",
                "fields": [
                    {"name": "label", "type": "Bytes<1>"},
                    {"name": "digest", "type": "Bytes<33>"}
                ]
            }}
        ]}]
    });
    let nested_record_key_plan: Plan = serde_json::from_value(nested_record_key_json)?;
    assert!(create_state(&nested_record_key_plan, &empty_state).is_err());

    let tag = [7u8];
    let first_id = [3u8; 33];
    let mut late_id = first_id;
    late_id[32] = 4;
    let first_receipt_label = [11u8];
    let first_receipt_digest = [21u8; 33];
    let late_receipt_label = [12u8];
    let late_receipt_digest = [22u8; 33];
    let first_account = [5u8; 32];
    let late_account = [6u8; 32];
    let first_profile_label = [31u8];
    let first_profile_digest = [41u8; 33];
    let late_profile_label = [32u8];
    let late_profile_digest = [42u8; 33];
    let mut inputs = BTreeMap::from([
        ("tag".into(), bytes_value(&tag)),
        ("firstId".into(), bytes_value(&first_id)),
        ("lateId".into(), bytes_value(&late_id)),
        ("firstReceiptLabel".into(), bytes_value(&first_receipt_label)),
        ("firstReceiptDigest".into(), bytes_value(&first_receipt_digest)),
        ("lateReceiptLabel".into(), bytes_value(&late_receipt_label)),
        ("lateReceiptDigest".into(), bytes_value(&late_receipt_digest)),
        ("firstAccount".into(), bytes_value(&first_account)),
        ("lateAccount".into(), bytes_value(&late_account)),
        ("firstProfileLabel".into(), bytes_value(&first_profile_label)),
        ("firstProfileDigest".into(), bytes_value(&first_profile_digest)),
        ("lateProfileLabel".into(), bytes_value(&late_profile_label)),
        ("lateProfileDigest".into(), bytes_value(&late_profile_digest)),
    ]);

    let result = prepare(
        &plan,
        &inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    check(&result, &circuit)?;
    let actual_outputs = Json::Object(result.returns_json().into_iter().collect());
    assert_eq!(actual_outputs, compact["outputs"]);

    let StateValue::Array(slots) = result.after.state.get_ref() else {
        anyhow::bail!("expected contract state slots");
    };
    let Some(StateValue::Map(receipts)) = slots.get(0) else {
        anyhow::bail!("expected the root record-key Map state");
    };
    assert_eq!(receipts.size(), compact["remainingEntries"]["receipts"].as_u64().unwrap() as usize);
    assert!(receipts.get(&fixed_bytes_record_key(&tag, &first_id)).is_none());
    let stored_receipt = receipts
        .get(&fixed_bytes_record_key(&tag, &late_id))
        .expect("late record key remains after removing its sibling");
    let StateValue::Cell(stored_receipt) = &*stored_receipt else {
        anyhow::bail!("expected Receipt in one native cell");
    };
    assert_eq!(
        **stored_receipt,
        fixed_bytes_record_value(&late_receipt_label, &late_receipt_digest)
    );

    let Some(StateValue::Map(profiles)) = slots.get(1) else {
        anyhow::bail!("expected the root scalar-key Map state");
    };
    assert_eq!(profiles.size(), compact["remainingEntries"]["profiles"].as_u64().unwrap() as usize);
    assert!(profiles.get(&aligned_bytes(&first_account)).is_none());
    let stored_profile = profiles
        .get(&aligned_bytes(&late_account))
        .expect("late scalar key remains after removing its sibling");
    let StateValue::Cell(stored_profile) = &*stored_profile else {
        anyhow::bail!("expected Profile in one native cell");
    };
    assert_eq!(
        **stored_profile,
        fixed_bytes_record_value(&late_profile_label, &late_profile_digest)
    );

    inputs.insert("lateId".into(), bytes_value(&late_id[..32]));
    assert!(prepare(
        &plan,
        &inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .is_err());
    inputs.insert("lateId".into(), bytes_value(&late_id));
    inputs.insert("lateReceiptDigest".into(), bytes_value(&late_receipt_digest[..32]));
    assert!(prepare(
        &plan,
        &inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .is_err());
    inputs.insert("lateReceiptDigest".into(), bytes_value(&late_receipt_digest));
    inputs.insert("lateProfileDigest".into(), bytes_value(&late_profile_digest[..32]));
    assert!(prepare(
        &plan,
        &inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .is_err());
    Ok(())
}
