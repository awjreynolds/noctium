#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{check, create_state, prepare, zkir::IrSource, Expr, Plan};
use serde_json::{json, Value as Json};
use std::{collections::BTreeMap, fs, path::PathBuf};

#[test]
#[ignore = "requires fresh FixedByteListMaybe artifacts and the pinned Compact oracle"]
fn fixed_byte_list_heads_match_typed_compact_maybes() -> Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_FIXED_BYTE_LIST_MAYBE_DIR")?);
    let oracle: Json = serde_json::from_reader(fs::File::open(std::env::var(
        "NOCTIUM_FIXED_BYTE_LIST_MAYBE_COMPACT",
    )?)?)?;
    assert!(oracle["compact"]
        .as_str()
        .unwrap()
        .starts_with("0.36.1 (7fa3a117c"));
    assert_eq!(oracle["runtime"], "0.21.0");
    let load = |entry: &str| -> Result<(Plan, IrSource)> {
        let stem = format!("FixedByteListMaybe.{entry}");
        Ok((
            serde_json::from_reader(fs::File::open(
                directory.join(format!("{stem}.impact.json")),
            )?)?,
            IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?,
        ))
    };
    let (mut head, head_circuit) = load("head")?;
    let (push, push_circuit) = load("push")?;
    let widths = [1, 32, 128];
    let field_counts: Vec<_> = head
        .return_views
        .iter()
        .map(|view| view.fields.len())
        .collect();
    assert_eq!(json!(field_counts), oracle["nativeOutputFields"]);
    assert_eq!(json!(head.returns.len()), oracle["zkirOutputs"]);

    let address = ContractAddress::default();
    let empty = create_state(
        &head,
        &BTreeMap::from(widths.map(|width| (format!("bytes{width}"), json!([])))),
    )?;
    let added = prepare(
        &push,
        &widths
            .iter()
            .enumerate()
            .map(|(index, width)| {
                (
                    format!("byte{width}"),
                    json!({"kind": "bytes", "values": oracle["populated"][index]["value"]}),
                )
            })
            .collect(),
        &empty,
        &INITIAL_PARAMETERS,
        address,
    )?;
    check(&added, &push_circuit)?;

    for (state, case) in [(&empty, "empty"), (&added.after.state, "populated")] {
        let result = prepare(&head, &BTreeMap::new(), state, &INITIAL_PARAMETERS, address)?;
        check(&result, &head_circuit)?;
        let returns = result.returns_json();
        assert_eq!(returns.len(), 3);
        for (index, width) in widths.iter().enumerate() {
            let expected = &oracle[case][index];
            let view = &returns[&format!("maybe{width}")];
            assert_eq!(view["id"], format!("FixedByteListMaybe.MaybeBytes{width}"));
            assert_eq!(
                view["fields"],
                json!([
                    {"name": "is_some", "value": {"kind": "bool", "value": expected["is_some"]}},
                    {"name": "value", "value": {"kind": "bytes", "values": expected["value"]}},
                ])
            );
        }
    }

    head.returns
        .iter_mut()
        .find(|output| output.name == "maybe32_value_chunk_0")
        .expect("high chunk of the first multi-field byte return")
        .expression = Expr::Constant { value: "0".into() };
    let changed = prepare(
        &head,
        &BTreeMap::new(),
        &added.after.state,
        &INITIAL_PARAMETERS,
        address,
    )?;
    assert!(check(&changed, &head_circuit).is_err());
    Ok(())
}
