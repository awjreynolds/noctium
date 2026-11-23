#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Db, Expr, Plan, check, construct_state, prepare, zkir::IrSource,
    constructor::{ConstructorAction, CounterIncrement},
};
use onchain_runtime::state::ChargedState;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs::File, path::PathBuf};

fn artifacts() -> PathBuf {
    env::var_os("NOCTIUM_ORDERED_CONSTRUCTOR_COUNTER_READ_DIR")
        .map(PathBuf::from)
        .expect("set fresh outputs in NOCTIUM_ORDERED_CONSTRUCTOR_COUNTER_READ_DIR")
}

fn constructor_arguments(enabled: bool, amount: u16) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("enabled".into(), json!(enabled)),
        ("amount".into(), json!(amount.to_string())),
    ])
}

fn increment_mut(plan: &mut Plan) -> &mut Expr {
    plan.constructor
        .as_mut()
        .expect("constructor metadata")
        .actions
        .iter_mut()
        .find_map(|action| match action {
            ConstructorAction::CounterIncrement { amount, .. } => Some(amount),
            _ => None,
        })
        .expect("ordered Counter increment")
}

fn read_and_check(
    plan: &Plan,
    relation: &IrSource,
    state: &ChargedState<Db>,
    total: u64,
    before: u64,
    after: u64,
) -> anyhow::Result<()> {
    let execution = prepare(
        plan,
        &BTreeMap::new(),
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, relation)?, execution.activity_schedule);
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([
            ("totalRead".into(), json!(total.to_string())),
            ("beforeRead".into(), json!(before.to_string())),
            ("afterRead".into(), json!(after.to_string())),
        ])
    );
    assert_eq!(execution.after.state.get_ref(), state.get_ref());
    Ok(())
}

#[test]
#[ignore = "requires fresh outputs in NOCTIUM_ORDERED_CONSTRUCTOR_COUNTER_READ_DIR"]
fn ordered_constructor_counter_reads_observe_prior_actions() -> anyhow::Result<()> {
    let directory = artifacts();
    let stem = "OrderedConstructorCounterRead.readBack";
    let plan: Plan =
        serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?;
    let relation = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;
    let constructor = plan.constructor.as_ref().expect("constructor metadata");
    assert_eq!(constructor.actions.len(), 3);
    assert!(matches!(
        &constructor.actions[0],
        ConstructorAction::InitializeCellFromCounter { state, counter }
            if state == "before" && counter == "total"
    ));
    assert!(matches!(
        &constructor.actions[1],
        ConstructorAction::CounterIncrement {
            state,
            guard: Some(_),
            ..
        } if state == "total"
    ));
    assert!(matches!(
        &constructor.actions[2],
        ConstructorAction::InitializeCellFromCounter { state, counter }
            if state == "after" && counter == "total"
    ));

    for amount in [0, 7, u16::MAX] {
        let state = construct_state(&plan, &constructor_arguments(true, amount))?;
        read_and_check(&plan, &relation, &state, u64::from(amount), 0, u64::from(amount))?;
    }

    let disabled = construct_state(&plan, &constructor_arguments(false, 7))?;
    read_and_check(&plan, &relation, &disabled, 0, 0, 0)?;

    // The false guard skips amount evaluation as well as the increment.
    let mut lazy = plan.clone();
    *increment_mut(&mut lazy) = Expr::Reference {
        name: "missingAmount".into(),
    };
    let lazy_state = construct_state(&lazy, &constructor_arguments(false, 7))?;
    read_and_check(&plan, &relation, &lazy_state, 0, 0, 0)?;

    // Constructor UInt16 values are widened by a checked UInt32 expression.
    let mut wrong_width = plan.clone();
    *increment_mut(&mut wrong_width) = Expr::Uint {
        maximum: "65535".into(),
        value: "7".into(),
    };
    let error = construct_state(&wrong_width, &constructor_arguments(true, 7))
        .err()
        .expect("wrong-width Counter amount must reject");
    assert!(
        error
            .to_string()
            .contains("constructor Counter increment amount must use the native UInt32 width"),
        "{error:#}"
    );

    // Ordered initializers share duplicate detection with ordinary initializers.
    let mut duplicate = plan.clone();
    let before = duplicate.constructor.as_ref().unwrap().actions[0].clone();
    duplicate
        .constructor
        .as_mut()
        .unwrap()
        .actions
        .insert(1, before);
    let error = construct_state(&duplicate, &constructor_arguments(true, 7))
        .err()
        .expect("duplicate Counter snapshot initializer must reject");
    assert!(
        error.to_string().contains("duplicate constructor initializer"),
        "{error:#}"
    );

    let mut mixed_counter_paths = plan.clone();
    mixed_counter_paths
        .constructor
        .as_mut()
        .unwrap()
        .counter_increments
        .push(CounterIncrement {
            state: "total".into(),
            amount: Expr::Uint {
                maximum: "4294967295".into(),
                value: "1".into(),
            },
            guard: None,
        });
    let error = construct_state(&mixed_counter_paths, &constructor_arguments(true, 7))
        .err()
        .expect("ordered and batched Counter actions must reject together");
    assert!(
        error
            .to_string()
            .contains("ordered constructor Counter actions cannot be mixed"),
        "{error:#}"
    );

    Ok(())
}
