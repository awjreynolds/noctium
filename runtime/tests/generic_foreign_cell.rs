#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{
    Plan, Value, check, construct_state,
    foreign::{ForeignRole, ForeignType, ForeignUnaryOp, ForeignValue},
    prepare,
    zkir::IrSource,
};
use serde_json::json;
use std::{collections::BTreeMap, env, fs::File, path::Path};

fn artifacts(dir: &Path, ty: &str, entry: &str) -> anyhow::Result<(Plan, IrSource)> {
    let stem = format!("GenericForeignCell{ty}.{entry}");
    Ok((
        serde_json::from_reader(File::open(dir.join(format!("{stem}.impact.json")))?)?,
        IrSource::load(File::open(dir.join(format!("{stem}.zkir")))?)?,
    ))
}

fn field_value(ty: ForeignType, byte: u8) -> anyhow::Result<ForeignValue> {
    let mut bytes = [0; 32];
    bytes[0] = byte;
    ForeignValue::from_bytes(ty, &bytes)
}

#[test]
#[ignore = "requires fresh GenericForeignCell artifacts in NOCTIUM_GENERIC_FOREIGN_CELL_DIR"]
fn generic_foreign_cells_preserve_all_nine_typed_encodings() -> anyhow::Result<()> {
    let directory = env::var("NOCTIUM_GENERIC_FOREIGN_CELL_DIR")?;
    let directory = Path::new(&directory);
    for (name, initial_byte, next_byte) in [
        ("Secp256k1Base", 1, 2),
        ("Secp256k1Scalar", 37, 41),
        ("Secp256k1Point", 1, 2),
        ("Secp256r1Base", 3, 5),
        ("Secp256r1Scalar", 4, 8),
        ("Secp256r1Point", 1, 2),
        ("Curve25519Base", 5, 7),
        ("Curve25519Scalar", 6, 9),
        ("Curve25519Point", 1, 2),
    ] {
        let ty = ForeignType::parse_source_name(name)?;
        let typed_value = |byte| -> anyhow::Result<_> {
            let value = match ty.role() {
                ForeignRole::Point => {
                    field_value(ForeignType::new(ty.family(), ForeignRole::Scalar), byte)?
                        .unary(ForeignUnaryOp::MulGenerator)?
                }
                _ => field_value(ty, byte)?,
            };
            Ok(Value::Foreign(value).public_json())
        };
        let initial = typed_value(initial_byte)?;
        let next = typed_value(next_byte)?;
        let (read, read_relation) = artifacts(directory, name, "read")?;
        let (update, update_relation) = artifacts(directory, name, "update")?;
        let state = construct_state(
            &read,
            &BTreeMap::from([("initial".into(), initial.clone())]),
        )?;
        let query = |current| {
            prepare(
                &read,
                &BTreeMap::new(),
                current,
                &INITIAL_PARAMETERS,
                ContractAddress::default(),
            )
        };
        let before = query(&state)?;
        check(&before, &read_relation)?;
        assert_eq!(before.returns_json()["result"], initial, "{name}");

        let result = prepare(
            &update,
            &BTreeMap::from([("next".into(), next.clone())]),
            &state,
            &INITIAL_PARAMETERS,
            ContractAddress::default(),
        )?;
        check(&result, &update_relation)?;
        assert_eq!(result.returns_json()["result"], next, "{name}");
        let after = query(&result.after.state)?;
        check(&after, &read_relation)?;
        assert_eq!(after.returns_json()["result"], next, "{name}");

        let mut wrong_family = next.clone();
        wrong_family["type"] = if name.starts_with("Secp256k1") {
            json!(name.replace("Secp256k1", "Secp256r1"))
        } else {
            json!(
                name.replace("Secp256r1", "Secp256k1")
                    .replace("Curve25519", "Secp256k1")
            )
        };
        assert!(
            prepare(
                &update,
                &BTreeMap::from([("next".into(), wrong_family)]),
                &result.after.state,
                &INITIAL_PARAMETERS,
                ContractAddress::default(),
            )
            .is_err(),
            "{name}"
        );
        let retained = query(&result.after.state)?;
        check(&retained, &read_relation)?;
        assert_eq!(retained.returns_json()["result"], next, "{name}");
    }
    Ok(())
}
