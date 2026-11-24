//! Focused checks against freshly compiled event artifacts.
#![cfg(feature = "zkir-321")]

use anyhow::Result;
use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value, ValueAtom};
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::{ops::LogEventType, state::StateValue};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::PathBuf};

#[test]
#[ignore = "requires fresh StandardEvents Lean artifacts"]
fn standard_events_bind_payload_order_and_activity() -> Result<()> {
    let output = PathBuf::from(std::env::var("NOCTIUM_EVENT_ARTIFACTS")?);
    let plan: Plan = serde_json::from_slice(&fs::read(
        output.join("StandardEvents.Token.logSpend.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        output.join("StandardEvents.Token.logSpend.zkir"),
    )?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let execute = |active: bool, nullifier: &[u8]| {
        prepare(
            &plan,
            &BTreeMap::from([
                ("active".into(), json!(active)),
                (
                    "nullifier".into(),
                    json!({"kind": "bytes", "values": nullifier}),
                ),
            ]),
            &state,
            &INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
    };
    let nullifier: Vec<u8> = (1..=32).collect();
    let mut active = execute(true, &nullifier)?;
    let inactive = execute(false, &nullifier)?;
    for execution in [&active, &inactive] {
        check(execution, &circuit)?;
        assert!(execution.logs.iter().all(|event| event.version == 1));
        assert_eq!(execution.logs[0].event_type, LogEventType::Paused);
        assert_eq!(
            execution.logs.last().unwrap().event_type,
            LogEventType::Unpaused
        );
    }
    assert_eq!(inactive.logs.len(), 2);
    assert_eq!(active.logs.len(), 3);
    assert_eq!(active.logs[1].event_type, LogEventType::ShieldedSpend);
    let StateValue::Cell(data) = &active.logs[1].data else {
        panic!("expected a byte cell");
    };
    assert_eq!(
        **data,
        AlignedValue {
            value: Value(vec![ValueAtom(nullifier)]),
            alignment: Alignment::singleton(AlignmentAtom::Bytes { length: 32 }),
        }
    );
    active.preimage.public_transcript_inputs = execute(true, &[42; 32])?
        .preimage
        .public_transcript_inputs
        .clone();
    assert!(check(&active, &circuit).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh StandardEvents Lean artifacts"]
fn standard_event_from_checked_helper_preserves_activity_and_order() -> Result<()> {
    use LogEventType::*;

    let output = PathBuf::from(std::env::var("NOCTIUM_EVENT_ARTIFACTS")?);
    let plan: Plan = serde_json::from_slice(&fs::read(
        output.join("StandardEvents.Token.logHelperSpend.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        output.join("StandardEvents.Token.logHelperSpend.zkir"),
    )?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let execute = |active: bool, nullifier: &[u8]| {
        prepare(
            &plan,
            &BTreeMap::from([
                ("active".into(), json!(active)),
                (
                    "nullifier".into(),
                    json!({"kind": "bytes", "values": nullifier}),
                ),
            ]),
            &state,
            &INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
    };
    let nullifier: Vec<u8> = (1..=32).collect();
    let mut active = execute(true, &nullifier)?;
    let inactive = execute(false, &nullifier)?;
    for execution in [&active, &inactive] {
        check(execution, &circuit)?;
        assert!(execution.logs.iter().all(|event| event.version == 1));
    }
    assert_eq!(
        active
            .logs
            .iter()
            .map(|event| event.event_type)
            .collect::<Vec<_>>(),
        [Paused, ShieldedSpend, Unpaused]
    );
    assert_eq!(
        inactive
            .logs
            .iter()
            .map(|event| event.event_type)
            .collect::<Vec<_>>(),
        [Paused, Unpaused]
    );
    let StateValue::Cell(data) = &active.logs[1].data else {
        panic!("expected a byte cell");
    };
    assert_eq!(
        **data,
        AlignedValue {
            value: Value(vec![ValueAtom(nullifier)]),
            alignment: Alignment::singleton(AlignmentAtom::Bytes { length: 32 }),
        }
    );
    active.preimage.public_transcript_inputs = execute(true, &[42; 32])?
        .preimage
        .public_transcript_inputs
        .clone();
    assert!(check(&active, &circuit).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh GuardedPauseEvents Lean artifacts"]
fn guarded_pause_events_bind_empty_ordered_logs() -> Result<()> {
    let output = PathBuf::from(std::env::var("NOCTIUM_GUARDED_PAUSE_ARTIFACTS")?);
    let plan: Plan = serde_json::from_slice(&fs::read(
        output.join("GuardedPauseEvents.logGuardedPause.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        output.join("GuardedPauseEvents.logGuardedPause.zkir"),
    )?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let execute = |active| {
        prepare(
            &plan,
            &BTreeMap::from([("active".into(), json!(active))]),
            &state,
            &INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
    };
    let mut active = execute(true)?;
    let inactive = execute(false)?;
    check(&active, &circuit)?;
    check(&inactive, &circuit)?;
    assert_eq!(
        active.logs.iter().map(|event| event.event_type).collect::<Vec<_>>(),
        [LogEventType::Paused, LogEventType::Unpaused],
    );
    for event in &active.logs {
        assert_eq!(event.version, 1);
        let StateValue::Cell(data) = &event.data else {
            panic!("expected a zero-width byte cell");
        };
        assert_eq!(
            **data,
            AlignedValue {
                value: Value(vec![ValueAtom(Vec::new())]),
                alignment: Alignment::singleton(AlignmentAtom::Bytes { length: 0 }),
            }
        );
    }
    assert!(inactive.logs.is_empty());
    active.preimage.public_transcript_inputs = inactive.preimage.public_transcript_inputs.clone();
    assert!(check(&active, &circuit).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh StandardEvents Lean artifacts"]
fn standard_event_catalog_matches_pinned_reference_payloads() -> Result<()> {
    use LogEventType::*;

    let output = PathBuf::from(std::env::var("NOCTIUM_EVENT_ARTIFACTS")?);
    let plan: Plan = serde_json::from_slice(&fs::read(
        output.join("StandardEvents.Token.logCatalog.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        output.join("StandardEvents.Token.logCatalog.zkir"),
    )?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let bytes = |size, start| {
        let values: Vec<_> = (0..size)
            .map(|index| ((start + index) % 256) as u8)
            .collect();
        json!({"kind": "bytes", "values": values})
    };
    let inputs = BTreeMap::from([
        ("commitment".into(), bytes(32, 1)),
        ("domain".into(), bytes(32, 225)),
        ("ciphertext".into(), bytes(512, 1)),
        ("memo".into(), bytes(256, 2)),
        (
            "value".into(),
            json!(((1u128 << 127) + 0x10203).to_string()),
        ),
    ]);
    let execution = prepare(
        &plan,
        &inputs,
        &state,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    check(&execution, &circuit)?;

    assert_eq!(execution.program.len(), 28);
    assert_eq!(execution.preimage.public_transcript_outputs.len(), 12);

    // SHA-256 of the full-width payloads emitted by Compact 0.36.1.
    let expected = [
        (
            ShieldedSpend,
            32,
            "ae216c2ef5247a3782c135efa279a3e4cdc61094270f5d2be58c6204b7a612c9",
        ),
        (
            ShieldedReceive,
            578,
            "1f894f5631ee86b966eb75cb30000fb875358b76941b3bd74240ef6ab8ede75f",
        ),
        (
            ShieldedMint,
            81,
            "b329b5b9d69bf9cc6ab38fd41b423a9affad55818d6b6b3986480d8cba3cb70c",
        ),
        (
            ShieldedBurn,
            49,
            "613499b3079da64d91e1a334445d217519649cda4ed3884dfa6342b3d57011ac",
        ),
        (
            UnshieldedSpend,
            145,
            "a8d750bd5550bc06d48b3b48ede2c4288fe6936c14134b069c736cd0af16360c",
        ),
        (
            UnshieldedReceive,
            145,
            "e78bc48c9e71b2f201d3cac5a096ee7893bec1416f0650a347c0304b37d976cd",
        ),
        (
            UnshieldedMint,
            80,
            "e347b43bac53302784c05ab04d42504d02b4f73db937e9d7c084472474c77d08",
        ),
        (
            UnshieldedBurn,
            113,
            "aeb91a0abf52d4a369ae937e8b9776c4d0dcb29cc58e6b7833fa6b231a77508b",
        ),
        (
            Paused,
            0,
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        ),
        (
            Unpaused,
            0,
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        ),
        (
            Misc,
            288,
            "3cb9fe229efe9f4eb74a3865ded415c6d9e549235a1a96b68f93f8d5a3cf08a8",
        ),
    ];
    assert_eq!(execution.logs.len(), expected.len());
    for (event, (kind, length, digest)) in execution.logs.iter().zip(expected) {
        assert_eq!(event.version, 1);
        assert_eq!(event.event_type, kind);
        let StateValue::Cell(data) = &event.data else {
            panic!("expected event payload cell");
        };
        assert_eq!(
            data.alignment,
            Alignment::singleton(AlignmentAtom::Bytes { length })
        );
        let [atom] = data.value.0.as_slice() else {
            panic!("expected a single byte atom");
        };
        assert!(atom.0.len() <= length as usize);
        let mut bytes = atom.0.clone();
        bytes.resize(length as usize, 0);
        assert_eq!(hex::encode(Sha256::digest(bytes)), digest, "{kind:?}");
    }
    Ok(())
}
