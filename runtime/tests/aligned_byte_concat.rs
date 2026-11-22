#![cfg(feature = "zkir-321")]

use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::curve::Fr;

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

#[test]
#[ignore = "requires fresh AlignedByteConcat artifacts in NOCTIUM_ALIGNED_BYTE_CONCAT_DIR"]
fn aligned_byte_concat_preserves_the_last_byte_and_binds_the_return() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_ALIGNED_BYTE_CONCAT_DIR")
            .expect("NOCTIUM_ALIGNED_BYTE_CONCAT_DIR"),
    );
    let stem = "AlignedByteConcat.joinTail";
    let plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let front: Vec<u8> = (1..=31).collect();
    let inputs = BTreeMap::from([
        ("front".into(), bytes(&front)),
        ("sourceBytes".into(), bytes(&[0, 32])),
    ]);
    let mut execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);

    let mut expected = front;
    expected.push(32);
    assert_eq!(expected.len(), 32);
    assert_eq!(
        execution.returns_json().get("joinedResult"),
        Some(&bytes(&expected))
    );

    assert!(!execution.preimage.public_transcript_outputs.is_empty());
    let original = execution.preimage.public_transcript_outputs[0];
    execution.preimage.public_transcript_outputs[0] = original + Fr::from(1u64);
    assert!(check(&execution, &circuit).is_err());
    Ok(())
}
