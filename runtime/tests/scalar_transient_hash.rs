#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

const FIELD_ZERO: &str =
    "9620025776880078320084866401708960911381310259544672466178048295274965038202";
const FIELD_SEVEN: &str =
    "38736647962766302285471997525105643408071412124637099941878267108985079060536";
const FLAG_TRUE: &str =
    "17188582201390813395271572040516706359096240541392850241580803164279358646045";
const BYTE_255: &str =
    "24950185806055691809115319438305670656167725047316057740233702636209249196133";

fn inputs(field: &str, flag: bool, byte: &str) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("fieldValue".into(), json!(field)),
        ("flagValue".into(), json!(flag)),
        ("byteValue".into(), json!(byte)),
    ])
}

fn fixture(directory: &Path, entrypoint: &str) -> Result<(Plan, IrSource)> {
    let stem = format!("ScalarTransientHash.{entrypoint}");
    let plan = serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    Ok((plan, circuit))
}

#[test]
#[ignore = "requires fresh ScalarTransientHash outputs in NOCTIUM_SCALAR_TRANSIENT_HASH_DIR"]
fn scalar_transient_hash_matches_pinned_compact_digests_for_native_inputs() -> Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_SCALAR_TRANSIENT_HASH_DIR")
            .expect("NOCTIUM_SCALAR_TRANSIENT_HASH_DIR"),
    );
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();
    let cases = [
        (
            "0",
            false,
            "0",
            BTreeMap::from([
                ("fieldResult".into(), json!(FIELD_ZERO)),
                ("flagResult".into(), json!(FIELD_ZERO)),
                ("byteResult".into(), json!(FIELD_ZERO)),
            ]),
        ),
        (
            "7",
            true,
            "7",
            BTreeMap::from([
                ("fieldResult".into(), json!(FIELD_SEVEN)),
                ("flagResult".into(), json!(FLAG_TRUE)),
                ("byteResult".into(), json!(FIELD_SEVEN)),
            ]),
        ),
        (
            "7",
            false,
            "255",
            BTreeMap::from([
                ("fieldResult".into(), json!(FIELD_SEVEN)),
                ("flagResult".into(), json!(FIELD_ZERO)),
                ("byteResult".into(), json!(BYTE_255)),
            ]),
        ),
    ];

    for entrypoint in ["ordinary", "readable"] {
        let (plan, circuit) = fixture(&directory, entrypoint)?;
        let initial = create_state(&plan, &BTreeMap::new())?;
        for (field, flag, byte, expected) in &cases {
            let execution = prepare(
                &plan,
                &inputs(*field, *flag, *byte),
                &initial,
                params,
                address,
            )?;
            assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
            assert_eq!(
                &execution.returns_json(),
                expected,
                "{entrypoint}: {field}/{flag}/{byte}"
            );
        }

        let overflow = prepare(&plan, &inputs("7", false, "256"), &initial, params, address);
        match overflow {
            Err(_) => {}
            Ok(execution) => assert!(
                check(&execution, &circuit).is_err(),
                "{entrypoint} accepted UInt8 input 256"
            ),
        }
    }
    Ok(())
}
