#![cfg(feature = "zkir-321")]

use noctium_runtime::{Expr, Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs::File, path::PathBuf};

const PLAN: &str =
    include_str!("fixtures/native-byte-packing/321/NativeBytePacking.pack.impact.json");
const CIRCUIT: &[u8] =
    include_bytes!("fixtures/native-byte-packing/321/NativeBytePacking.pack.zkir");
const ZERO_SUFFIX_PLAN: &str = include_str!(
    "fixtures/byte-pack-zero-padding/321/BytePackZeroPadding.decode.impact.json"
);
const ZERO_SUFFIX_CIRCUIT: &[u8] = include_bytes!(
    "fixtures/byte-pack-zero-padding/321/BytePackZeroPadding.decode.zkir"
);

#[test]
fn mixed_byte_pack_zero_suffix_matches_zero_and_one_and_rejects_forged_values() {
    let plan: Plan = serde_json::from_str(ZERO_SUFFIX_PLAN).unwrap();
    let circuit = IrSource::load(ZERO_SUFFIX_CIRCUIT).unwrap();
    let initial = create_state(&plan, &BTreeMap::new()).unwrap();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();

    for value in [0u8, 1] {
        let inputs = BTreeMap::from([(
            "value".into(),
            json!({"kind":"bytes","values":[value]}),
        )]);
        let expected = value.to_string();
        let execution = prepare(&plan, &inputs, &initial, params, address).unwrap();
        check(&execution, &circuit).unwrap();
        assert_eq!(execution.returns_json()["decodedResult"], json!(expected));

        let mut forged = plan.clone();
        forged.returns[0].expression = Expr::Constant {
            value: (1 - value).to_string(),
        };
        let forged = prepare(&forged, &inputs, &initial, params, address).unwrap();
        assert!(check(&forged, &circuit).is_err());
    }
}

#[test]
fn typed_byte_packing_preserves_chunk_order_and_committed_results() {
    let source: Json = serde_json::from_slice(CIRCUIT).unwrap();
    let packing_counts: Vec<_> = source["instructions"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|instruction| instruction["op"] == "bytes_into_natives")
        .map(|instruction| instruction["outputs"].as_array().unwrap().len())
        .collect();
    assert_eq!(packing_counts, [1, 1, 2, 2, 3]);

    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let circuit = IrSource::load(CIRCUIT).unwrap();
    let initial = create_state(&plan, &BTreeMap::new()).unwrap();
    let mut inputs = BTreeMap::from([("empty0".into(), json!({"kind":"bytes","values":[]}))]);
    let mut expected =
        BTreeMap::from([("emptyResult".into(), json!({"kind":"bytes","values":[]}))]);
    for length in [1, 31, 32, 62, 63] {
        let mut bytes: Vec<u8> = (0..length).map(|index| (index * 37 + 19) as u8).collect();
        inputs.insert(format!("b{length}"), json!({"kind":"bytes","values":bytes}));
        bytes.reverse();
        expected.insert(format!("r{length}"), json!({"kind":"bytes","values":bytes}));
    }
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let execution = prepare(&plan, &inputs, &initial, params, address).unwrap();
    check(&execution, &circuit).unwrap();
    assert_eq!(execution.returns_json(), expected);

    let mut forged = plan;
    let returned = forged
        .returns
        .iter_mut()
        .find(|output| output.name == "r63")
        .unwrap();
    let mut changed: Vec<u8> = expected["r63"]["values"]
        .as_array()
        .unwrap()
        .iter()
        .map(|value| value.as_u64().unwrap() as u8)
        .collect();
    changed[62] ^= 1;
    returned.expression = Expr::BytesLiteral {
        length: 63,
        values: changed,
    };
    let execution = prepare(&forged, &inputs, &initial, params, address).unwrap();
    assert!(check(&execution, &circuit).is_err());
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_HASH_VECTOR_FOLD_DIR"]
fn mixed_hash_vector_matches_reference_and_rejects_changed_digest() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_HASH_VECTOR_FOLD_DIR").expect("NOCTIUM_HASH_VECTOR_FOLD_DIR"),
    );
    let mut plan: Plan = serde_json::from_reader(File::open(
        directory.join("HashVectorFold.measureHashVector.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("HashVectorFold.measureHashVector.zkir"),
    )?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let payload: Vec<u8> = (0..32).map(|index| (index * 37 + 19) as u8).collect();
    let inputs = BTreeMap::from([("payload".into(), json!({"kind":"bytes","values":payload}))]);
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let execution = prepare(&plan, &inputs, &state, params, address)?;
    check(&execution, &circuit)?;

    // Compact runtime 0.21.0 persistentHash over Vector<2, Bytes<32>>.
    let mut digest =
        hex::decode("eb0509340ad024a26240beabba4fec0cb19825494f6fbeea40e7e4ea553a9cd0")?;
    assert_eq!(
        execution.returns_json()["digest"],
        json!({"kind":"bytes","values":digest})
    );
    digest[0] ^= 1;
    let returned = plan
        .returns
        .iter_mut()
        .find(|item| item.name == "digest")
        .unwrap();
    returned.expression = Expr::BytesLiteral {
        length: 32,
        values: digest,
    };
    let changed = prepare(&plan, &inputs, &state, params, address)?;
    assert!(check(&changed, &circuit).is_err());
    Ok(())
}
