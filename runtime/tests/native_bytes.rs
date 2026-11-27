#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Expr, Plan, ScalarType, Value, check, create_state, field_value, prepare, witness::Registry,
    zkir::IrSource,
};
use onchain_runtime::state::StateValue;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn wide_fixture(directory: &std::path::Path, entry: &str) -> anyhow::Result<(Plan, IrSource, Json)> {
    let stem = format!("WidePublicBytes.{entry}");
    let plan: Plan = serde_json::from_slice(&std::fs::read(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let relation = std::fs::read(directory.join(format!("{stem}.zkir")))?;
    let circuit = IrSource::load(relation.as_slice())?;
    let relation = serde_json::from_slice(&relation)?;
    Ok((plan, circuit, relation))
}

fn patterned_bytes(length: usize) -> Vec<u8> {
    let mut payload: Vec<u8> = (0..length).map(|index| (index % 251) as u8).collect();
    payload[length - 2..].copy_from_slice(&[0xa5, 0x5a]);
    payload
}

fn little_endian_limb(bytes: &[u8]) -> Fr {
    let mut encoded = [0; 32];
    encoded[..bytes.len()].copy_from_slice(bytes);
    Fr::from_le_bytes(&encoded).expect("31-byte limb fits in the field")
}

fn expected_limbs(payload: &[u8]) -> Vec<Fr> {
    let first_width = payload.len() % 31;
    let mut limbs = Vec::with_capacity(payload.len().div_ceil(31));
    if first_width != 0 {
        limbs.push(little_endian_limb(&payload[payload.len() - first_width..]));
    }
    let full_length = payload.len() - first_width;
    limbs.extend(payload[..full_length].chunks_exact(31).rev().map(little_endian_limb));
    limbs
}

fn assert_wide_public_round_trip(
    output: &std::path::Path,
    entry: &str,
    length: usize,
) -> anyhow::Result<()> {
    let (plan, circuit, relation) = wide_fixture(output, entry)?;
    let instructions = relation["instructions"]
        .as_array()
        .expect("ZKIR instructions array");
    let input_count = length.div_ceil(31);
    let input_fields: Vec<_> = instructions
        .iter()
        .filter(|item| item["op"] == "public_input")
        .map(|item| {
            item["output"]
                .as_str()
                .expect("public input name")
                .to_owned()
        })
        .collect();
    assert_eq!(
        input_fields,
        (0..input_count)
            .map(|index| format!("%input__noctium_bytes_payload_{index}"))
            .collect::<Vec<_>>()
    );
    let first_width = length % 31;
    assert_ne!(first_width, 0, "fixture should exercise a partial first limb");
    assert!(instructions.iter().any(|item| {
        item["op"] == "constrain_bits"
            && item["val"] == "%input__noctium_bytes_payload_0"
            && item["bits"] == first_width * 8
    }));

    let initial = create_state(&plan, &BTreeMap::new())?;
    let payload = patterned_bytes(length);
    let mut inputs = BTreeMap::from([("payload".into(), bytes(&payload))]);
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let mut execution = prepare(&plan, &inputs, &initial, params, address)?;
    check(&execution, &circuit)?;
    assert_eq!(
        execution.preimage.public_transcript_outputs,
        expected_limbs(&payload)
    );
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([("result".into(), bytes(&payload))])
    );

    inputs.insert("payload".into(), bytes(&payload[..length - 1]));
    assert!(prepare(&plan, &inputs, &initial, params, address).is_err());

    let (commitment, randomness) = execution.preimage.communications_commitment
        .expect("prepared communication commitment");
    execution.preimage.communications_commitment = Some((commitment + Fr::from(1), randomness));
    assert!(check(&execution, &circuit).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh WidePublicBytes artifacts in NOCTIUM_WIDE_PUBLIC_BYTES_ARTIFACTS"]
fn public_bytes_1025_1055_and_4096_preserve_limb_order_and_tail() -> anyhow::Result<()> {
    let output = std::path::PathBuf::from(
        std::env::var_os("NOCTIUM_WIDE_PUBLIC_BYTES_ARTIFACTS")
            .expect("set NOCTIUM_WIDE_PUBLIC_BYTES_ARTIFACTS"),
    );
    for (entry, length) in [
        ("roundTrip", 1025),
        ("roundTrip1055", 1055),
        ("roundTrip4096", 4096),
    ] {
        assert_wide_public_round_trip(&output, entry, length)?;
    }
    Ok(())
}

#[test]
fn general_bytes_preserve_chunk_boundaries_types_and_committed_returns() {
    let (plan, circuit): (Plan, IrSource) = if let Some(output) =
        std::env::var_os("NOCTIUM_NATIVE_BYTES_ARTIFACTS")
    {
        let output = std::path::PathBuf::from(output);
        (
            serde_json::from_slice(
                &std::fs::read(output.join("NativeBytes.inspect.impact.json")).unwrap(),
            )
            .unwrap(),
            IrSource::load(std::fs::File::open(output.join("NativeBytes.inspect.zkir")).unwrap())
                .unwrap(),
        )
    } else {
        (
            serde_json::from_str(include_str!(
                "fixtures/native-bytes/321/NativeBytes.inspect.impact.json"
            ))
            .unwrap(),
            IrSource::load(
                include_bytes!("fixtures/native-bytes/321/NativeBytes.inspect.zkir").as_slice(),
            )
            .unwrap(),
        )
    };
    let names = [
        "payload31",
        "payload32",
        "payload62",
        "payload63",
        "selectedFirst",
        "selectedLast",
        "joined31",
        "joined32",
        "joined62",
        "joined63",
        "sliceFirst",
        "sliceLast",
        "literalLast",
    ];
    let initial = create_state(
        &plan,
        &names
            .iter()
            .map(|name| ((*name).into(), json!("0")))
            .collect(),
    )
    .unwrap();
    let payload: Vec<u8> = (0..64).collect();
    let other: Vec<u8> = (100..131).collect();
    let wide: Vec<u8> = (200..233).collect();
    let joined: Vec<_> = other.iter().chain(&wide).copied().collect();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let mut last_inputs = BTreeMap::new();
    for choose_reverse in [false, true] {
        let inputs = BTreeMap::from([
            ("payload".into(), bytes(&payload)),
            ("other31".into(), bytes(&other)),
            ("wide33".into(), bytes(&wide)),
            ("empty0".into(), bytes(&[])),
            ("chooseReverse".into(), json!(choose_reverse)),
        ]);
        let execution = prepare(&plan, &inputs, &initial, params, address).unwrap();
        check(&execution, &circuit).unwrap();
        let mut selected = payload.clone();
        if choose_reverse {
            selected.reverse();
        }
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([
                ("selectedBytes".into(), bytes(&selected)),
                ("joinedBytes".into(), bytes(&joined)),
                ("sliceBytes".into(), bytes(&payload[31..63])),
                ("otherBytes".into(), bytes(&other)),
                ("wideBytes".into(), bytes(&wide)),
                ("emptyBytes".into(), bytes(&[])),
            ])
        );
        let StateValue::Array(state) = execution.after.state.get_ref() else {
            panic!("expected state array");
        };
        let expected = [
            31,
            32,
            62,
            63,
            selected[0],
            selected[63],
            200,
            201,
            231,
            232,
            31,
            62,
            68,
        ];
        for (index, byte) in expected.into_iter().enumerate() {
            let StateValue::Cell(cell) = state.get(index).unwrap() else {
                panic!("expected byte cell");
            };
            assert_eq!(**cell, field_value(Fr::from(byte as u64)));
        }
        last_inputs = inputs;
    }
    let mut forged = plan.clone();
    let mut changed = payload.clone();
    changed.reverse();
    changed[62] ^= 1;
    forged.returns[0].expression = Expr::BytesLiteral {
        length: 64,
        values: changed,
    };
    let forged = prepare(&forged, &last_inputs, &initial, params, address).unwrap();
    assert!(check(&forged, &circuit).is_err());
    last_inputs.insert("payload".into(), bytes(&payload[..63]));
    assert!(prepare(&plan, &last_inputs, &initial, params, address).is_err());

    let registry = Registry::default();
    for length in [0, 1, 31, 32, 33, 62, 63, 64, 1024, 1025, 1054, 1055, 4096] {
        let token = format!("Bytes<{length}>");
        let value = vec![255; length];
        assert_eq!(
            ScalarType::parse(&token).unwrap().bytes_length(),
            Some(length)
        );
        Value::Bytes(value.clone()).validate().unwrap();
        registry.validate(&token, &bytes(&value)).unwrap();
        assert!(
            registry
                .validate(&token, &bytes(&vec![0; length + 1]))
                .is_err()
        );
    }
    assert_eq!(ScalarType::parse("Bytes<32>").unwrap(), ScalarType::Bytes32);
    for token in ["Bytes<4097>", "Bytes<01>", "Bytes<-1>", "Bytes<>"] {
        assert!(ScalarType::parse(token).is_err());
    }
    assert!(Value::Bytes(vec![0; 4097]).validate().is_err());

    let empty_plan: Plan = serde_json::from_str(include_str!(
        "fixtures/native-bytes/321/NativeEmptyBytes.inspect.impact.json"
    ))
    .unwrap();
    let empty_circuit = IrSource::load(
        include_bytes!("fixtures/native-bytes/321/NativeEmptyBytes.inspect.zkir").as_slice(),
    )
    .unwrap();
    let empty_state = create_state(&empty_plan, &BTreeMap::new()).unwrap();
    let mut empty_execution = prepare(
        &empty_plan,
        &BTreeMap::from([
            ("enabled".into(), json!(true)),
            ("empty0".into(), bytes(&[])),
        ]),
        &empty_state,
        params,
        address,
    )
    .unwrap();
    check(&empty_execution, &empty_circuit).unwrap();
    assert_eq!(empty_execution.preimage.private_transcript.len(), 1);
    empty_execution.preimage.private_transcript[0] = Fr::from(0u64);
    assert!(check(&empty_execution, &empty_circuit).is_err());
}
