//! Native block-time operations need current compiler artifacts and the ledger context.
#[cfg(feature = "zkir-321")]
#[test]
#[ignore = "requires fresh NativeBlockTime artifacts in NOCTIUM_BLOCK_TIME_DIR"]
fn strict_and_inclusive_block_time_reads_bind_the_native_result() {
    use base_crypto::time::Timestamp;
    use coin_structure::contract::ContractAddress;
    use noctium_runtime::{
        Plan, PreparationCursor, check, create_state, prepare, prepare_with_context, zkir::IrSource,
    };
    use onchain_runtime::context::QueryContext;
    use serde_json::{Value as Json, json};
    use std::{collections::BTreeMap, fs, path::PathBuf};
    use transient_crypto::curve::Fr;

    let artifacts =
        PathBuf::from(std::env::var_os("NOCTIUM_BLOCK_TIME_DIR").expect("NOCTIUM_BLOCK_TIME_DIR"));
    let plan: Plan = serde_json::from_slice(
        &fs::read(artifacts.join("NativeBlockTime.checkTime.impact.json")).unwrap(),
    )
    .unwrap();
    let circuit_bytes = fs::read(artifacts.join("NativeBlockTime.checkTime.zkir")).unwrap();
    let circuit = IrSource::load(circuit_bytes.as_slice()).unwrap();
    let state = create_state(&plan, &BTreeMap::new()).unwrap();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();
    let context = |time| {
        let mut context = QueryContext::new(state.clone(), address);
        context.call_context.tblock = Timestamp::from_secs(time);
        context.call_context.tblock_err = 3;
        context
    };
    let inputs = |cutoff: u64, enabled: bool| {
        BTreeMap::<String, Json>::from([
            ("cutoff".into(), json!(cutoff.to_string())),
            ("enabled".into(), json!(enabled)),
        ])
    };

    let compact_max_safe = 9_007_199_254_740_991;
    for (time, cutoff, before, after) in [
        (9, 10, true, false),
        (10, 10, false, false),
        (11, 10, false, true),
        (0, 0, false, false),
        (0, u64::MAX, true, false),
        (compact_max_safe, compact_max_safe, false, false),
        (compact_max_safe, compact_max_safe + 1, true, false),
        (compact_max_safe, compact_max_safe - 1, false, true),
        (u64::MAX, 0, false, true),
        (u64::MAX, u64::MAX, false, false),
    ] {
        let execution =
            prepare_with_context(&plan, &inputs(cutoff, true), context(time), params).unwrap();
        assert_eq!(
            check(&execution, &circuit).unwrap(),
            execution.activity_schedule
        );
        let returns = execution.returns_json();
        assert_eq!(returns["beforeDeadline"], json!(before));
        assert_eq!(returns["afterDeadline"], json!(after));
        assert_eq!(returns["atOrAfterDeadline"], json!(!before));
        assert_eq!(returns["atOrBeforeDeadline"], json!(!after));
    }

    let execution = prepare_with_context(&plan, &inputs(10, true), context(9), params).unwrap();
    let same_side = prepare_with_context(&plan, &inputs(10, true), context(8), params).unwrap();
    assert_eq!(
        execution.preimage.public_transcript_outputs,
        same_side.preimage.public_transcript_outputs
    );
    assert!(
        context(8)
            .query(
                &execution.program,
                None,
                &params.cost_model.runtime_cost_model,
            )
            .is_ok()
    );
    assert!(
        context(10)
            .query(
                &execution.program,
                None,
                &params.cost_model.runtime_cost_model,
            )
            .is_err()
    );

    let mut corrupted = prepare_with_context(&plan, &inputs(10, true), context(9), params).unwrap();
    let block_time_output = corrupted
        .preimage
        .public_transcript_outputs
        .last_mut()
        .expect("block-time kernel output");
    *block_time_output = *block_time_output + Fr::from(1u64);
    assert!(corrupted.preimage.check(&circuit).is_err());

    let error = prepare(&plan, &inputs(10, true), &state, params, address)
        .err()
        .expect("active time comparison requires an explicit context");
    assert!(
        error
            .to_string()
            .contains("requires explicit block context")
    );
    let mut cursor =
        PreparationCursor::new(&plan, &inputs(10, true), &state, params, address).unwrap();
    let cursor_error = (0..plan.operations.len())
        .find_map(|_| cursor.step().err())
        .expect("cursor time comparison requires an explicit context");
    assert!(
        cursor_error
            .to_string()
            .contains("requires explicit block context")
    );

    let inactive = prepare(&plan, &inputs(10, false), &state, params, address).unwrap();
    assert_eq!(
        check(&inactive, &circuit).unwrap(),
        inactive.activity_schedule
    );
    assert_eq!(inactive.returns_json()["beforeDeadline"], json!(false));
    assert_eq!(inactive.returns_json()["afterDeadline"], json!(false));
    assert_eq!(inactive.returns_json()["atOrAfterDeadline"], json!(false));
    assert_eq!(inactive.returns_json()["atOrBeforeDeadline"], json!(false));
}
