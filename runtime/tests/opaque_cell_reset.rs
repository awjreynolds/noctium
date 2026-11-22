#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{Expr, Plan, check, create_state, evaluate, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};
use transient_crypto::curve::Fr;

#[test]
#[ignore = "requires fresh OpaqueCellReset artifacts in NOCTIUM_OPAQUE_RESET_DIR"]
fn guarded_opaque_reset_clears_canonical_cells_and_binds_returns() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_OPAQUE_RESET_DIR").expect("NOCTIUM_OPAQUE_RESET_DIR"),
    );
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("OpaqueCellReset.clear.impact.json"),
    )?)?;
    let relation = IrSource::load(File::open(directory.join("OpaqueCellReset.clear.zkir"))?)?;
    let text = json!({"kind":"opaqueString","value":"é\0λ"});
    let bytes = json!({"kind":"opaqueBytes","values":[0,1,255]});
    let empty_text = json!({"kind":"opaqueString","value":""});
    let empty_bytes = json!({"kind":"opaqueBytes","values":[]});
    let state = |text, bytes| {
        create_state(
            &plan,
            &BTreeMap::from([("text".into(), text), ("bytes".into(), bytes)]),
        )
    };
    let seeded = state(text.clone(), bytes.clone())?;
    let empty = state(empty_text.clone(), empty_bytes.clone())?;

    for (enabled, expected, text, bytes) in [
        (false, &seeded, text, bytes),
        (true, &empty, empty_text, empty_bytes),
    ] {
        let mut execution = prepare(
            &plan,
            &BTreeMap::from([("enabled".into(), json!(enabled))]),
            &seeded,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )?;
        check(&execution, &relation)?;
        assert_eq!(execution.after.state.get_ref(), expected.get_ref());
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([("textAfter".into(), text), ("bytesAfter".into(), bytes)])
        );
        assert_eq!(execution.preimage.public_transcript_outputs.len(), 2);
        if enabled {
            assert_eq!(
                execution.preimage.public_transcript_outputs,
                vec![Fr::from(0u64); 2]
            );
        }
        let first_output = &mut execution.preimage.public_transcript_outputs[0];
        *first_output = *first_output + Fr::from(1u64);
        assert!(check(&execution, &relation).is_err());
    }

    let invalid: Expr = serde_json::from_value(json!({"tag":"opaqueEmpty","type":"Native"}))?;
    assert!(evaluate(&invalid, &BTreeMap::new()).is_err());
    Ok(())
}
