#![cfg(feature = "zkir-321")]

use noctium_runtime::zkir::IrSource;
use noctium_runtime::{Expr, Plan, check, create_state, prepare};
use serde_json::json;
use std::{collections::BTreeMap, env, fs, path::PathBuf};
use transient_crypto::curve::Fr;

#[test]
fn typed_boolean_gates_bind_truth_tables_and_eager_assertions() {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/boolean-gates/321/BooleanGates.truthTable.impact.json"
    ))
    .unwrap();
    let circuit = IrSource::load(
        include_bytes!("fixtures/boolean-gates/321/BooleanGates.truthTable.zkir").as_slice(),
    )
    .unwrap();
    let initial = create_state(&plan, &BTreeMap::new()).unwrap();
    for left in [false, true] {
        for right in [false, true] {
            let inputs =
                BTreeMap::from([("left".into(), json!(left)), ("right".into(), json!(right))]);
            let execution = prepare(
                &plan,
                &inputs,
                &initial,
                &ledger::structure::INITIAL_PARAMETERS,
                coin_structure::contract::ContractAddress::default(),
            )
            .unwrap();
            check(&execution, &circuit).unwrap();
            assert_eq!(
                execution.returns_json(),
                BTreeMap::from([
                    ("andResult".into(), json!(left && right)),
                    ("orResult".into(), json!(left || right)),
                    ("notLeftResult".into(), json!(!left)),
                    ("xorResult".into(), json!(left ^ right)),
                    ("xorThreeResult".into(), json!(left ^ right ^ true)),
                ])
            );
            let mut forged = plan.clone();
            forged.returns[0].expression = Expr::Bool {
                value: !(left && right),
            };
            let forged = prepare(
                &forged,
                &inputs,
                &initial,
                &ledger::structure::INITIAL_PARAMETERS,
                coin_structure::contract::ContractAddress::default(),
            )
            .unwrap();
            assert!(check(&forged, &circuit).is_err());
        }
    }
    for (plan_json, circuit_json, name, expected) in [
        (
            include_str!("fixtures/boolean-gates/321/BooleanGates.andEager.impact.json"),
            include_bytes!("fixtures/boolean-gates/321/BooleanGates.andEager.zkir").as_slice(),
            "andGuardResult",
            false,
        ),
        (
            include_str!("fixtures/boolean-gates/321/BooleanGates.orEager.impact.json"),
            include_bytes!("fixtures/boolean-gates/321/BooleanGates.orEager.zkir").as_slice(),
            "orGuardResult",
            true,
        ),
    ] {
        let plan: Plan = serde_json::from_str(plan_json).unwrap();
        let circuit = IrSource::load(circuit_json).unwrap();
        let initial = create_state(&plan, &BTreeMap::new()).unwrap();
        let mut execution = prepare(
            &plan,
            &BTreeMap::from([("enabled".into(), json!(true))]),
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .unwrap();
        check(&execution, &circuit).unwrap();
        assert_eq!(execution.returns_json()[name], json!(expected));
        execution.preimage.private_transcript[0] = Fr::from(0u64);
        assert!(check(&execution, &circuit).is_err());
        assert!(
            prepare(
                &plan,
                &BTreeMap::from([("enabled".into(), json!(false))]),
                &initial,
                &ledger::structure::INITIAL_PARAMETERS,
                coin_structure::contract::ContractAddress::default(),
            )
            .is_err()
        );
    }
}

fn lazy_boolean_inputs(
    and_enabled: bool,
    or_enabled: bool,
    nested_outer: bool,
    nested_inner: bool,
    amount: u8,
) -> BTreeMap<String, serde_json::Value> {
    BTreeMap::from([
        ("andEnabled".into(), json!(and_enabled)),
        ("orEnabled".into(), json!(or_enabled)),
        ("nestedOuter".into(), json!(nested_outer)),
        ("nestedInner".into(), json!(nested_inner)),
        ("amount".into(), json!(amount.to_string())),
    ])
}

#[test]
#[ignore = "requires fresh LazyBoolean outputs in NOCTIUM_LAZY_BOOLEAN_DIR"]
fn lazy_boolean_gates_skip_inactive_uint1_narrowing() -> anyhow::Result<()> {
    let directory =
        PathBuf::from(env::var_os("NOCTIUM_LAZY_BOOLEAN_DIR").expect("NOCTIUM_LAZY_BOOLEAN_DIR"));
    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join("LazyBoolean.lazy.impact.json")).unwrap())
            .unwrap();
    let circuit_bytes = fs::read(directory.join("LazyBoolean.lazy.zkir")).unwrap();
    let circuit = IrSource::load(circuit_bytes.as_slice()).unwrap();
    let initial = create_state(&plan, &BTreeMap::new()).unwrap();
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();

    let inactive_narrowing = prepare(
        &plan,
        &lazy_boolean_inputs(false, true, false, false, 2),
        &initial,
        parameters,
        address,
    )
    .expect("false AND and true OR skip UInt1 narrowing");
    check(&inactive_narrowing, &circuit).unwrap();
    assert_eq!(
        inactive_narrowing.returns_json(),
        BTreeMap::from([
            ("andResult".into(), json!(false)),
            ("orResult".into(), json!(true)),
            ("nestedResult".into(), json!(false)),
        ])
    );
    assert_eq!(
        inactive_narrowing.preimage.private_transcript,
        vec![
            Fr::from(0u64),
            Fr::from(1u64),
            Fr::from(0u64),
            Fr::from(0u64),
            Fr::from(2u64),
        ]
    );
    let nested_short_circuit = prepare(
        &plan,
        &lazy_boolean_inputs(false, true, true, true, 2),
        &initial,
        parameters,
        address,
    )
    .expect("nested true OR skips UInt1 narrowing");
    check(&nested_short_circuit, &circuit).unwrap();
    assert_eq!(
        nested_short_circuit.returns_json()["nestedResult"],
        json!(true)
    );

    let valid_narrowing = prepare(
        &plan,
        &lazy_boolean_inputs(true, false, true, false, 1),
        &initial,
        parameters,
        address,
    )?;
    check(&valid_narrowing, &circuit)?;
    assert_eq!(
        valid_narrowing.returns_json(),
        BTreeMap::from([
            ("andResult".into(), json!(true)),
            ("orResult".into(), json!(true)),
            ("nestedResult".into(), json!(true)),
        ])
    );

    let mut active_and = inactive_narrowing;
    active_and.preimage.private_transcript[0] = Fr::from(1u64);
    assert_eq!(
        active_and.returns_json()["andResult"],
        json!(false),
        "the forged active input keeps the accepted public result"
    );
    assert!(
        check(&active_and, &circuit).is_err(),
        "native relation rejects active UInt1 narrowing even when the public result stays unchanged"
    );

    for (and_enabled, or_enabled, nested_outer, nested_inner) in [
        (true, true, false, false),
        (false, false, false, false),
        (false, true, true, false),
    ] {
        assert!(
            prepare(
                &plan,
                &lazy_boolean_inputs(and_enabled, or_enabled, nested_outer, nested_inner, 2),
                &initial,
                parameters,
                address,
            )
            .is_err(),
            "active UInt1 narrowing must reject amount 2"
        );
    }
    Ok(())
}

#[test]
#[ignore = "requires fresh LazyConditional outputs in NOCTIUM_LAZY_CONDITIONAL_DIR"]
fn lazy_conditionals_check_both_skipped_cast_branches() {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_LAZY_CONDITIONAL_DIR").expect("NOCTIUM_LAZY_CONDITIONAL_DIR"),
    );
    let plan: Plan = serde_json::from_slice(
        &fs::read(directory.join("LazyConditional.branches.impact.json")).unwrap(),
    )
    .unwrap();
    let circuit_bytes = fs::read(directory.join("LazyConditional.branches.zkir")).unwrap();
    let circuit = IrSource::load(circuit_bytes.as_slice()).unwrap();
    let initial = create_state(&plan, &BTreeMap::new()).unwrap();
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let inputs = |then_condition: bool, else_condition: bool| {
        BTreeMap::from([
            ("thenCondition".into(), json!(then_condition)),
            ("elseCondition".into(), json!(else_condition)),
            ("amount".into(), json!("3")),
        ])
    };
    let accepted_inputs = inputs(false, true);

    let accepted = prepare(&plan, &accepted_inputs, &initial, parameters, address)
        .expect("false then and true else skip both invalid UInt1 casts");
    check(&accepted, &circuit).unwrap();
    assert_eq!(
        accepted.returns_json(),
        BTreeMap::from([
            ("thenResult".into(), json!(true)),
            ("elseResult".into(), json!(true)),
        ])
    );
    assert_eq!(
        accepted.preimage.private_transcript,
        vec![Fr::from(0u64), Fr::from(1u64), Fr::from(3u64)]
    );

    for (private_index, active_then, active_else, active_value, result_name) in [
        (0, true, true, 1u64, "thenResult"),
        (1, false, false, 0u64, "elseResult"),
    ] {
        let active_inputs = inputs(active_then, active_else);
        assert!(
            prepare(&plan, &active_inputs, &initial, parameters, address).is_err(),
            "host preparation rejects active {result_name} narrowing"
        );
        let mut forged = prepare(&plan, &accepted_inputs, &initial, parameters, address).unwrap();
        forged.preimage.private_transcript[private_index] = Fr::from(active_value);
        assert_eq!(
            forged.returns_json()[result_name],
            json!(true),
            "active invalid narrowing keeps the accepted result"
        );
        assert!(
            check(&forged, &circuit).is_err(),
            "native relation rejects active UInt1 narrowing for {result_name}"
        );
    }
}
