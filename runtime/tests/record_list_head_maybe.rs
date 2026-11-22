#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{Plan, Value, check, create_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};
use transient_crypto::curve::Fr;

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_RECORD_LIST_HEAD_MAYBE_DIR"]
fn record_list_head_returns_one_ordered_maybe() -> Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_RECORD_LIST_HEAD_MAYBE_DIR")?);
    let load = |entry: &str| -> Result<(Plan, IrSource)> {
        let stem = format!("RecordListHeadMaybe.{entry}");
        Ok((
            serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?,
            IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?,
        ))
    };
    let (head, circuit) = load("peek")?;
    let (seed, seed_circuit) = load("seed")?;
    let empty = create_state(&head, &BTreeMap::from([("inbox".into(), json!([]))]))?;
    let no_inputs = BTreeMap::new();
    let address = ContractAddress::default();
    let populated = prepare(&seed, &no_inputs, &empty, &INITIAL_PARAMETERS, address)?;
    check(&populated, &seed_circuit)?;

    for (state, present, first, second) in [
        (&empty, false, 0u64, 0u64),
        (&populated.after.state, true, 17u64, 23u64),
    ] {
        let result = prepare(&head, &no_inputs, state, &INITIAL_PARAMETERS, address)?;
        check(&result, &circuit)?;
        assert_eq!(result.after.state, *state);
        let returns = result.returns_json();
        assert_eq!(returns.len(), 1);
        assert_eq!(returns["head"]["kind"], "struct");
        assert_eq!(
            returns["head"]["fields"],
            json!([
                {"name":"is_some","value":{"kind":"bool","value":present}},
                {"name":"value","value":{
                    "kind":"struct","id":"RecordListHeadMaybe.Memo","fields":[
                        {"name":"first","value":{"kind":"native","value":first.to_string()}},
                        {"name":"second","value":{"kind":"native","value":second.to_string()}}
                    ]
                }}
            ])
        );
        assert_eq!(
            result
                .returns()
                .iter()
                .map(|(_, value)| value.clone())
                .collect::<Vec<_>>(),
            [
                Value::Native(Fr::from(u8::from(present))),
                Value::Native(Fr::from(first)),
                Value::Native(Fr::from(second)),
            ]
        );
    }
    Ok(())
}
