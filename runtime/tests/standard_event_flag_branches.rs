//! Exact choice and optional-field parity against the pinned Compact reference.
#![cfg(feature = "zkir-321")]

use anyhow::Result;
use base_crypto::fab::{Alignment, AlignmentAtom};
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::{ops::LogEventType, state::StateValue};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::PathBuf};

#[test]
#[ignore = "requires fresh EventFlagBranches Lean artifacts"]
fn standard_event_optional_and_address_flags_match_pinned_compact() -> Result<()> {
    use LogEventType::*;

    let output = PathBuf::from(std::env::var("NOCTIUM_EVENT_FLAG_ARTIFACTS")?);
    let plan: Plan = serde_json::from_slice(&fs::read(
        output.join("EventFlagBranches.emitFlagBranches.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        output.join("EventFlagBranches.emitFlagBranches.zkir"),
    )?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let execute = |inputs: &BTreeMap<String, Value>| {
        prepare(
            &plan,
            inputs,
            &state,
            &INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
    };
    let compact: Value = serde_json::from_str(include_str!(
        "../../tests/standard-event-flag-branches-compact.json"
    ))?;
    assert_eq!(compact["compiler"], "0.36.1 (7fa3a117c 2026-11-11)");
    assert_eq!(compact["runtime"], "0.21.0");
    let expected_cases = compact["cases"].as_array().expect("Compact flag cases");
    assert_eq!(expected_cases.len(), 4);
    let fixed_inputs: BTreeMap<String, Value> = compact["nativeInputs"]
        .as_object()
        .expect("shared native inputs")
        .iter()
        .map(|(name, value)| (name.clone(), value.clone()))
        .collect();
    let inputs = |present: bool, route: bool| {
        let mut inputs = fixed_inputs.clone();
        inputs.insert("present".into(), json!(present));
        inputs.insert("route".into(), json!(route));
        inputs
    };
    let event_types = [
        ShieldedReceive,
        ShieldedMint,
        ShieldedBurn,
        UnshieldedSpend,
        UnshieldedReceive,
        UnshieldedBurn,
    ];
    let event_names = [
        "shielded-receive",
        "shielded-mint",
        "shielded-burn",
        "unshielded-spend",
        "unshielded-receive",
        "unshielded-burn",
    ];
    let event_tags = [1, 2, 3, 4, 5, 7];

    let mut first_execution = None;
    let mut alternate_tape = None;
    for (case_index, (present, route)) in
        [(false, false), (false, true), (true, false), (true, true)]
            .into_iter()
            .enumerate()
    {
        let case_inputs = inputs(present, route);
        let execution = execute(&case_inputs)?;
        check(&execution, &circuit)?;
        let reference = &expected_cases[case_index];
        assert_eq!(reference["present"], json!(present));
        assert_eq!(reference["route"], json!(route));
        let expected = reference["events"].as_array().expect("Compact events");
        assert_eq!(execution.logs.len(), event_types.len());
        assert_eq!(expected.len(), event_types.len());
        for (tag, (event, reference)) in execution.logs.iter().zip(expected).enumerate() {
            assert_eq!(reference["order"], json!(tag));
            assert_eq!(reference["tag"], json!(event_tags[tag]));
            assert_eq!(reference["version"], json!(event.version));
            assert_eq!(reference["eventType"], json!(event_names[tag]));
            assert_eq!(event.event_type, event_types[tag]);
            let length =
                u32::try_from(reference["payloadLength"].as_u64().expect("payload width"))?;
            let digest = reference["payloadSha256"].as_str().expect("payload digest");
            let StateValue::Cell(data) = &event.data else {
                panic!("expected a byte cell for {kind:?}", kind = event.event_type);
            };
            assert_eq!(
                data.alignment,
                Alignment::singleton(AlignmentAtom::Bytes { length })
            );
            let [atom] = data.value.0.as_slice() else {
                panic!("expected one event byte atom");
            };
            assert!(atom.0.len() <= length as usize);
            let mut padded = atom.0.clone();
            padded.resize(length as usize, 0);
            assert_eq!(hex::encode(Sha256::digest(padded)), digest, "tag {tag}");
        }
        let public_tape = execution.preimage.public_transcript_inputs.clone();
        if case_index == 0 {
            first_execution = Some(execution);
        }
        if case_index == 3 {
            alternate_tape = Some(public_tape);
        }
    }

    let mut first = first_execution.expect("first flag case");
    first.preimage.public_transcript_inputs = alternate_tape.expect("alternate flag tape");
    assert!(
        check(&first, &circuit).is_err(),
        "a substituted flag tape must fail"
    );
    Ok(())
}
