#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, construct_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};

#[test]
#[ignore = "requires fresh NamedCompositeConstructor.inspect artifacts in NOCTIUM_NAMED_COMPOSITE_CONSTRUCTOR_DIR"]
fn named_composite_constructor_preserves_one_checked_argument() -> Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_NAMED_COMPOSITE_CONSTRUCTOR_DIR")
            .expect("NOCTIUM_NAMED_COMPOSITE_CONSTRUCTOR_DIR"),
    );
    let stem = "NamedCompositeConstructor.inspect";
    let plan: Plan =
        serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?;
    let relation = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;
    let arguments = BTreeMap::from([(
        "seed".into(),
        json!({
            "kind": "struct",
            "id": "NamedCompositeConstructor.Payload",
            "fields": [
                {"name": "position", "value": {
                    "kind": "struct",
                    "id": "NamedCompositeConstructor.Position",
                    "fields": [
                        {"name": "amount", "value": {"kind": "uint", "maximum": "255", "value": "17"}},
                        {"name": "enabled", "value": {"kind": "bool", "value": true}},
                        {"name": "ignored", "value": {"kind": "uint", "maximum": "255", "value": "240"}},
                    ],
                }},
                {"name": "extras", "value": {
                    "kind": "tuple",
                    "items": [
                        {"kind": "uint", "maximum": "65535", "value": "23"},
                        {"kind": "uint", "maximum": "255", "value": "241"},
                    ],
                }},
            ],
        }),
    )]);
    let initial = construct_state(&plan, &arguments)?;
    let execution = prepare(
        &plan,
        &BTreeMap::new(),
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &relation)?, execution.activity_schedule);
    assert_eq!(execution.after.state, initial);
    assert_eq!(
        serde_json::to_value(execution.returns_json())?,
        json!({
            "amountResult": "17",
            "enabledResult": true,
            "countResult": "23",
        })
    );

    for (path, value) in [
        ("/id", json!("WrongPayload")),
        ("/fields/0/value/fields/0/value/value", json!("seventeen")),
        ("/fields/0/value/fields/0/value/value", json!("256")),
        ("/fields/0/value/fields/1/value/value", json!("true")),
        ("/fields/0/value/fields/2/value/value", json!("240.0")),
        ("/fields/0/value/fields/2/value/value", json!("256")),
        ("/fields/1/value/items/0/value", json!("65536")),
        ("/fields/1/value/items/1/value", json!("241.0")),
        ("/fields/1/value/items/1/value", json!("256")),
    ] {
        let mut invalid = arguments.clone();
        *invalid
            .get_mut("seed")
            .and_then(|seed| seed.pointer_mut(path))
            .expect("path in seed fixture") = value;
        assert!(
            construct_state(&plan, &invalid).is_err(),
            "native constructor accepted invalid argument at {path}"
        );
    }
    Ok(())
}
