#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, construct_state, field_value, prepare, zkir::IrSource};
use onchain_runtime::state::StateValue;
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};
use transient_crypto::curve::Fr;

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_SEALED_SET_CONSTRUCTOR_DIR"]
fn sealed_set_constructor_inserts_duplicate_once() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_SEALED_SET_CONSTRUCTOR_DIR")
            .expect("NOCTIUM_SEALED_SET_CONSTRUCTOR_DIR"),
    );
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("SealedRootSetConstructor.inspect.impact.json"),
    )?)?;
    let relation = IrSource::load(File::open(
        directory.join("SealedRootSetConstructor.inspect.zkir"),
    )?)?;
    assert_eq!(
        plan.constructor
            .as_ref()
            .expect("constructor metadata")
            .set_inserts
            .len(),
        2
    );

    let key_argument = BTreeMap::from([("key".into(), json!("17"))]);
    let initial = construct_state(&plan, &key_argument)?;
    let slot = |name: &str| plan.state.iter().position(|decl| decl.name == name).unwrap();
    let StateValue::Array(root) = initial.get_ref() else {
        anyhow::bail!("expected constructor state array")
    };
    let Some(StateValue::Map(registered)) = root.get(slot("registered")) else {
        anyhow::bail!("expected registered Set map")
    };
    let Some(StateValue::Map(empty_set)) = root.get(slot("emptySet")) else {
        anyhow::bail!("expected emptySet map")
    };
    assert_eq!(registered.size(), 1, "duplicate insertion must be idempotent");
    assert!(matches!(
        &*registered
            .get(&field_value(Fr::from(17u64)))
            .expect("inserted Set member"),
        StateValue::Null
    ));
    assert_eq!(empty_set.size(), 0, "neighboring sealed Set stays empty");

    let execution = prepare(
        &plan,
        &key_argument,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &relation)?, execution.activity_schedule);
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([
            ("present".into(), json!(true)),
            ("size".into(), json!("1")),
            ("neighborEmpty".into(), json!(true)),
        ])
    );
    assert_eq!(execution.after.state.get_ref(), initial.get_ref());

    let mut wrong_target = plan.clone();
    let registered_slot = slot("registered");
    wrong_target.state[registered_slot].kind = json!({"cell":"Native"});
    wrong_target.state[registered_slot].sealed = false;
    let error = construct_state(&wrong_target, &key_argument)
        .err()
        .expect("Set constructor insert must target a root Set");
    assert!(error.to_string().contains("root scalar Set"), "{error:#}");
    Ok(())
}
