#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{Db, Execution, Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::state::ChargedState;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs::File, path::Path};

fn artifacts(dir: &Path, contract: &str, entry: &str) -> anyhow::Result<(Plan, IrSource)> {
    let stem = format!("{contract}.{entry}");
    Ok((
        serde_json::from_reader(File::open(dir.join(format!("{stem}.impact.json")))?)?,
        IrSource::load(File::open(dir.join(format!("{stem}.zkir")))?)?,
    ))
}

fn empty_state(plan: &Plan) -> anyhow::Result<ChargedState<Db>> {
    let config = plan
        .state
        .iter()
        .map(|state| (state.name.clone(), json!([])))
        .collect();
    create_state(plan, &config)
}

fn run(
    operation: &(Plan, IrSource),
    state: &ChargedState<Db>,
    inputs: &BTreeMap<String, Json>,
) -> anyhow::Result<Execution> {
    let execution = prepare(
        &operation.0,
        inputs,
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(
        check(&execution, &operation.1)?,
        execution.activity_schedule
    );
    Ok(execution)
}

#[test]
#[ignore = "requires Noctium artifacts generated from tests/FixedByteCollectionKeys.lean"]
fn fixed_byte_collection_keys_roundtrip() -> anyhow::Result<()> {
    let directory = env::var("NOCTIUM_FIXED_BYTE_KEYS_DIR")?;
    let directory = Path::new(&directory);
    let direct = artifacts(directory, "FixedByteCollectionKeys", "exerciseDirect")?;
    let direct_state = empty_state(&direct.0)?;
    let short = [167u8];
    let wide: Vec<u8> = (1..=33).collect();
    let direct_inputs = BTreeMap::from([
        ("emptyKey".into(), json!({"kind":"bytes","values":[]})),
        ("shortKey".into(), json!({"kind":"bytes","values":short})),
        ("longKey".into(), json!({"kind":"bytes","values":wide})),
        ("value".into(), json!("71")),
    ]);
    let direct_output = run(&direct, &direct_state, &direct_inputs)?.returns_json();
    for name in ["zeroResult", "oneResult", "wideResult"] {
        assert_eq!(direct_output[name], json!("71"));
    }
    assert_eq!(direct_output["nestedResult"], json!(true));

    let mut invalid = direct_inputs;
    invalid.insert("longKey".into(), json!({"kind":"bytes","values":[1]}));
    assert!(run(&direct, &direct_state, &invalid).is_err());

    for (suffix, key, value) in [
        ("Zero", &[][..], "9"),
        ("One", short.as_slice(), "17"),
        ("Wide", wide.as_slice(), "42"),
    ] {
        let contract = "FixedByteGenericCollectionKeys";
        let put = artifacts(directory, contract, &format!("put{suffix}"))?;
        let lookup = artifacts(directory, contract, &format!("lookup{suffix}"))?;
        let state = empty_state(&put.0)?;
        let flattened_key: BTreeMap<_, _> = key
            .iter()
            .enumerate()
            .map(|(index, byte)| (format!("key.{index}"), json!(byte.to_string())))
            .collect();
        let mut insert = flattened_key.clone();
        insert.insert("enabled".into(), json!(true));
        insert.insert("next".into(), json!(value));
        let after = run(&put, &state, &insert)?.after.state;
        let read = run(&lookup, &after, &flattened_key)?;
        assert_eq!(read.returns_json()["result"], json!(value));
        assert_eq!(read.after.state, after);
    }
    Ok(())
}
