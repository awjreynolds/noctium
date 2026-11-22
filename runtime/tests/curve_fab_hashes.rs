#![cfg(feature = "zkir-321")]

use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::curve::Fr;

fn artifacts() -> PathBuf {
    std::env::var_os("NOCTIUM_CURVE_FAB_HASHES_DIR")
        .map(PathBuf::from)
        .expect("NOCTIUM_CURVE_FAB_HASHES_DIR")
}

fn foreign(ty: &str, bytes: &[u8]) -> Json {
    json!({"kind":"foreign", "type":ty, "bytes":bytes})
}

fn inputs() -> BTreeMap<String, Json> {
    let mut secp_base = [0u8; 32];
    secp_base[0] = 42;
    BTreeMap::from([
        (
            "jubjubScalar".into(),
            json!({"kind":"jubjubScalar", "value":"17"}),
        ),
        (
            "jubjubPoint".into(),
            json!({
                "kind":"jubjubPoint",
                "x":"28336281903124990867587793011069573392383982287722241916350956173377953689573",
                "y":"39385640392217313770878525135509063452020585410343666726093009378539878503883"
            }),
        ),
        ("secpBase".into(), foreign("Secp256k1Base", &secp_base)),
        (
            "secpPoint".into(),
            foreign(
                "Secp256k1Point",
                &hex::decode("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")
                    .unwrap(),
            ),
        ),
        (
            "pairJubjubPoint".into(),
            json!({"kind":"jubjubPoint", "x":"0", "y":"1"}),
        ),
        ("pairSecpPoint".into(), foreign("Secp256k1Point", &[0; 33])),
    ])
}

#[test]
#[ignore = "requires fresh Lean outputs in NOCTIUM_CURVE_FAB_HASHES_DIR"]
fn curve_fab_hashes_match_compact_oracles_and_bind_return_commitment() -> anyhow::Result<()> {
    let directory = artifacts();
    let stem = "CurveFabHashes.hash";
    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let mut execution = prepare(
        &plan,
        &inputs(),
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;

    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([
            (
                "persistentResult".into(),
                json!({
                    "kind":"bytes",
                    "values":hex::decode(
                        "f7a88f2c30c717772757acbd8d86c87b4c1e8cc88cdfe2f5efb608a1e61ed7b8"
                    )?
                }),
            ),
            (
                "transientResult".into(),
                json!(
                    "22293029467289654224445560286591595292864875000282287882633570107188179417385"
                ),
            ),
            (
                "curveResult".into(),
                json!({
                    "kind":"jubjubPoint",
                    "x":"5187241681299452555252327364509344370508477903483857193377192133060431926242",
                    "y":"23820288451142401238103521862534681424716203618312892062945957612621911308121"
                }),
            ),
        ])
    );

    let (commitment, randomness) = execution
        .preimage
        .communications_commitment
        .expect("the native return commitment");
    execution.preimage.communications_commitment = Some((commitment + Fr::from(1u64), randomness));
    assert!(check(&execution, &circuit).is_err());
    Ok(())
}
