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
        active
            .logs
            .iter()
            .map(|event| event.event_type)
            .collect::<Vec<_>>(),
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
    let execute = |inputs: &BTreeMap<String, serde_json::Value>| {
        prepare(
            &plan,
            inputs,
            &state,
            &INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
    };
    let mut execution = execute(&inputs)?;
    check(&execution, &circuit)?;

    assert_eq!(execution.program.len(), 28);
    assert_eq!(execution.preimage.public_transcript_outputs.len(), 12);

    let compact: serde_json::Value = serde_json::from_str(include_str!(
        "../../tests/standard-event-catalog-compact.json"
    ))?;
    assert_eq!(compact["compiler"], "0.36.1 (7fa3a117c 2026-11-11)");
    assert_eq!(compact["runtime"], "0.21.0");
    let expected = compact["events"].as_array().expect("Compact event catalog");
    let event_types = [
        ShieldedSpend,
        ShieldedReceive,
        ShieldedMint,
        ShieldedBurn,
        UnshieldedSpend,
        UnshieldedReceive,
        UnshieldedMint,
        UnshieldedBurn,
        Paused,
        Unpaused,
        Misc,
    ];
    assert_eq!(execution.logs.len(), expected.len());
    assert_eq!(execution.logs.len(), event_types.len());
    for (tag, (event, reference)) in execution.logs.iter().zip(expected).enumerate() {
        assert_eq!(reference["tag"], json!(tag));
        assert_eq!(reference["version"], json!(event.version));
        let kind = event_types[tag];
        assert_eq!(event.event_type, kind);
        let length = u32::try_from(reference["payloadLength"].as_u64().expect("payload width"))?;
        let digest = reference["payloadSha256"].as_str().expect("payload digest");
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
    for (name, malformed) in [
        ("memo", bytes(255, 2)),
        ("value", json!("340282366920938463463374607431768211456")),
    ] {
        let mut bad = inputs.clone();
        bad.insert(name.into(), malformed);
        assert!(
            execute(&bad).is_err(),
            "{name} must meet the declared input type"
        );
    }

    for (name, replacement, event) in [
        ("memo", bytes(256, 3), Misc),
        ("value", json!("0"), UnshieldedMint),
    ] {
        let mut changed = inputs.clone();
        changed.insert(name.into(), replacement);
        let alternate = execute(&changed)?;
        check(&alternate, &circuit)?;
        let index = event_types.iter().position(|kind| *kind == event).unwrap();
        assert_ne!(execution.logs[index].data, alternate.logs[index].data);
        execution
            .preimage
            .public_transcript_inputs
            .clone_from(&alternate.preimage.public_transcript_inputs);
        assert!(
            check(&execution, &circuit).is_err(),
            "changed {event:?} payload must fail"
        );
    }
    Ok(())
}
