#![cfg(feature = "zkir-321")]

use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use noctium_runtime::{Plan, check, create_state, field_value, prepare, zkir::IrSource};
use onchain_runtime::state::StateValue;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

fn bytes_value(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn fixed_bytes_record_key(tag: &[u8], id: &[u8]) -> AlignedValue {
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
fn root_fixed_byte_record_map_keys_match_compact_and_keep_the_other_entry() -> anyhow::Result<()> {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/root-fixed-byte-record-map/321/RootFixedByteRecordMap.update.impact.json"
    ))?;
    let circuit = IrSource::load(
        include_bytes!("fixtures/root-fixed-byte-record-map/321/RootFixedByteRecordMap.update.zkir")
            .as_slice(),
    )?;
    let compact: Json = serde_json::from_str(include_str!(
        "fixtures/root-fixed-byte-record-map/compact-0.36.1.json"
    ))?;
    assert_eq!(compact["compact"], "0.36.1 (7fa3a117c 2026-11-11)");
    assert_eq!(compact["runtime"], "0.21.0");
    let state = create_state(&plan, &BTreeMap::from([("memos".into(), json!([]))]))?;
    let tag = [7u8];
    let first_id = [3u8; 33];
    let mut late_id = first_id;
    late_id[32] = 4;
    let mut inputs = BTreeMap::from([
        ("tag".into(), bytes_value(&tag)),
        ("firstId".into(), bytes_value(&first_id)),
        ("lateId".into(), bytes_value(&late_id)),
        ("firstValue".into(), json!("101")),
        ("lateValue".into(), json!("303")),
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
    let Some(StateValue::Map(memos)) = slots.get(0) else {
        anyhow::bail!("expected the root Map state");
    };
    assert_eq!(memos.size(), compact["remainingEntries"].as_u64().unwrap() as usize);
    assert!(memos.get(&fixed_bytes_record_key(&tag, &first_id)).is_none());
    let stored = memos
        .get(&fixed_bytes_record_key(&tag, &late_id))
        .expect("late-byte key remains after removing its sibling");
    let StateValue::Cell(stored) = &*stored else {
        anyhow::bail!("expected the retained UInt16 value Cell");
    };
    assert_eq!(**stored, field_value(Fr::from(303u64)));

    inputs.insert("lateId".into(), bytes_value(&late_id[..32]));
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
