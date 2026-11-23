#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{check, construct_state, prepare, zkir::IrSource, Db, Expr, Plan};
use onchain_runtime::state::ChargedState;
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_GUARDED_CONSTRUCTOR_LIST_COUNTER_DIR"]
fn guarded_constructor_counter_and_list_match_native_readback() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_GUARDED_CONSTRUCTOR_LIST_COUNTER_DIR")
            .expect("NOCTIUM_GUARDED_CONSTRUCTOR_LIST_COUNTER_DIR"),
    );
    let stem = "GuardedConstructorListCounter.readBack";
    let plan: Plan =
        serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?;
    let relation = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;
    let constructor = plan.constructor.as_ref().expect("constructor metadata");
    assert_eq!(constructor.counter_increments.len(), 1);
    assert!(constructor.counter_increments[0].guard.is_some());
    assert_eq!(constructor.list_pushes.len(), 1);
    assert!(constructor.list_pushes[0].guard.is_some());

    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();
    let entry_inputs = BTreeMap::new();
    let constructor_arguments = |enabled| {
        BTreeMap::from([
            ("enabled".into(), json!(enabled)),
            ("amount".into(), json!("1234")),
            ("first".into(), json!("42")),
        ])
    };
    let read_and_check = |state: &ChargedState<Db>, enabled: bool| -> anyhow::Result<()> {
        let execution = prepare(&plan, &entry_inputs, state, parameters, address)?;
        assert_eq!(check(&execution, &relation)?, execution.activity_schedule);
        let returns = execution.returns_json();
        assert_eq!(
            returns["amountRead"],
            json!(if enabled { "1234" } else { "0" })
        );
        assert_eq!(
            returns["lengthRead"],
            json!(if enabled { "1" } else { "0" })
        );
        assert_eq!(returns["head"]["kind"], json!("struct"));
        assert_eq!(
            returns["head"]["fields"],
            json!([
                {"name": "is_some", "value": {"kind": "bool", "value": enabled}},
                {"name": "value", "value": {"kind": "native", "value": if enabled { "42" } else { "0" }}}
            ])
        );
        assert_eq!(execution.after.state.get_ref(), state.get_ref());
        Ok(())
    };

    for enabled in [false, true] {
        let initial = construct_state(&plan, &constructor_arguments(enabled))?;
        read_and_check(&initial, enabled)?;
    }

    let mut skipped_expressions_plan = plan.clone();
    let constructor = skipped_expressions_plan.constructor.as_mut().unwrap();
    constructor.counter_increments[0].amount = Expr::Reference {
        name: "missingAmount".into(),
    };
    constructor.list_pushes[0].value = Expr::Reference {
        name: "missingFirst".into(),
    };
    let disabled_state = construct_state(&skipped_expressions_plan, &constructor_arguments(false))?;
    read_and_check(&disabled_state, false)?;
    Ok(())
}
