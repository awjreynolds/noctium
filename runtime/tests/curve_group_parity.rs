#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Plan, check, create_state, prepare, proof::TrustedParameters, zkir::IrSource,
};
use num_bigint::BigUint;
use rand::rngs::OsRng;
use serde_json::Value as Json;
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, env, fs, path::PathBuf};
use transient_crypto::{
    curve::Fr,
    proofs::{ParamsVerifier, Zkir},
};

const OFFICIAL_GROUP_SRS: [(u8, &str); 4] = [
    (
        11,
        "9901589d7956ff58be0d85569b2f455b77b58c3758026ffb5bbe4807000b96d1",
    ),
    (
        15,
        "724c7c3d779148bb113c7ee9c034b2f27db16e6bdf315fde90105a9bad00b1de",
    ),
    (
        16,
        "09c877216d6589b370263e18af40a030a901b41a7a7c37ef58c9901db41f05c6",
    ),
    (
        17,
        "4a9ef6c7c0619aab74eede44b13e753e3ba54508a02dd3b7106a949aabb73b74",
    ),
];

fn artifact_directory() -> PathBuf {
    PathBuf::from(
        env::var_os("NOCTIUM_CURVE_GROUP_PARITY_DIR")
            .expect("NOCTIUM_CURVE_GROUP_PARITY_DIR must point to fresh Lean outputs"),
    )
}

fn compact_results() -> PathBuf {
    PathBuf::from(
        env::var_os("NOCTIUM_CURVE_GROUP_PARITY_COMPACT_RESULTS").expect(
            "NOCTIUM_CURVE_GROUP_PARITY_COMPACT_RESULTS must point to pinned Compact output",
        ),
    )
}

fn proof_parameters_directory() -> PathBuf {
    PathBuf::from(
        env::var_os("NOCTIUM_CURVE_GROUP_PARITY_SRS_DIR")
            .expect("NOCTIUM_CURVE_GROUP_PARITY_SRS_DIR must point to pinned native SRS files"),
    )
}

fn inputs(values: &Json) -> BTreeMap<String, Json> {
    values
        .as_object()
        .expect("Compact case inputs must be an object")
        .iter()
        .map(|(name, value)| (name.clone(), value.clone()))
        .collect()
}

fn returns(values: &Json) -> BTreeMap<String, Json> {
    values
        .as_object()
        .expect("Compact expected outputs must be an object")
        .iter()
        .map(|(name, value)| (name.clone(), value.clone()))
        .collect()
}

#[test]
#[ignore = "requires fresh CurveGroupParity artifacts and pinned Compact results"]
fn native_curve_group_overloads_match_pinned_compact() -> anyhow::Result<()> {
    let directory = artifact_directory();
    let oracle: Json = serde_json::from_slice(&fs::read(compact_results())?)?;
    assert!(
        oracle["compiler"]
            .as_str()
            .unwrap()
            .starts_with("0.36.1 (7fa3a117c")
    );
    assert_eq!(oracle["runtime"], "0.21.0");
    let cases = oracle["cases"].as_array().expect("Compact cases array");
    assert_eq!(cases.len(), 72);

    for case in cases {
        let entry = case["entry"].as_str().expect("entry name");
        let stem = format!("CurveGroupParity.{entry}");
        let plan: Plan =
            serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
        let relation =
            IrSource::load(fs::read(directory.join(format!("{stem}.zkir")))?.as_slice())?;
        let initial = create_state(&plan, &BTreeMap::new())?;
        let execution = prepare(
            &plan,
            &inputs(&case["inputs"]),
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )?;
        assert_eq!(
            check(&execution, &relation)?,
            execution.activity_schedule,
            "{}",
            case["id"]
        );
        assert_eq!(
            execution.returns_json(),
            returns(&case["expected"]),
            "{}",
            case["id"]
        );
    }
    Ok(())
}

#[test]
#[ignore = "requires fresh CurveGroupParity artifacts"]
fn curve_group_inputs_reject_the_first_noncanonical_scalar() -> anyhow::Result<()> {
    let directory = artifact_directory();
    let oracle: Json = serde_json::from_slice(&fs::read(compact_results())?)?;
    for (entry, order) in [
        (
            "jubjubGroup",
            "6554484396890773809930967563523245729705921265872317281365359162392183254199",
        ),
        (
            "secp256k1Group",
            "115792089237316195423570985008687907852837564279074904382605163141518161494337",
        ),
        (
            "secp256r1Group",
            "115792089210356248762697446949407573529996955224135760342422259061068512044369",
        ),
        (
            "curve25519Group",
            "7237005577332262213973186563042994240857116359379907606001950938285454250989",
        ),
    ] {
        let case = oracle["cases"]
            .as_array()
            .unwrap()
            .iter()
            .find(|case| case["entry"] == entry)
            .expect("family vector");
        let mut supplied = inputs(&case["inputs"]);
        let scalar = if entry == "jubjubGroup" {
            serde_json::json!({"kind":"jubjubScalar", "value":order})
        } else {
            let mut full = BigUint::parse_bytes(order.as_bytes(), 10)
                .expect("scalar order")
                .to_bytes_le();
            full.resize(32, 0);
            serde_json::json!({"kind":"foreign", "type":match entry {
                "secp256k1Group" => "Secp256k1Scalar",
                "secp256r1Group" => "Secp256r1Scalar",
                _ => "Curve25519Scalar",
            }, "bytes":full})
        };
        supplied.insert("scalar".into(), scalar);
        let stem = format!("CurveGroupParity.{entry}");
        let plan: Plan =
            serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
        let initial = create_state(&plan, &BTreeMap::new())?;
        assert!(
            prepare(
                &plan,
                &supplied,
                &initial,
                &ledger::structure::INITIAL_PARAMETERS,
                coin_structure::contract::ContractAddress::default(),
            )
            .is_err(),
            "{entry} accepted scalar order"
        );
    }
    Ok(())
}

#[test]
#[ignore = "requires fresh CurveGroupParity artifacts, pinned Compact results, and official SRS files"]
fn native_curve_group_proofs_bind_compact_matched_results() -> anyhow::Result<()> {
    use futures::executor::block_on;

    let directory = artifact_directory();
    let srs_directory = proof_parameters_directory();
    let oracle: Json = serde_json::from_slice(&fs::read(compact_results())?)?;
    let cases = oracle["cases"].as_array().expect("Compact cases array");

    for entry in [
        "jubjubGroup",
        "secp256k1Group",
        "secp256r1Group",
        "curve25519Group",
    ] {
        let family = entry.strip_suffix("Group").expect("group entry");
        let case_id = format!("{family}-point-1-scalar-2");
        let case = cases
            .iter()
            .find(|case| case["id"] == case_id)
            .unwrap_or_else(|| panic!("missing Compact proof vector {case_id}"));
        let stem = format!("CurveGroupParity.{entry}");
        let plan: Plan =
            serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
        let relation_bytes = fs::read(directory.join(format!("{stem}.zkir")))?;
        let relation = IrSource::load(relation_bytes.as_slice())?;
        let k = relation.k();
        let srs_hash = OFFICIAL_GROUP_SRS
            .iter()
            .find_map(|(supported_k, hash)| (*supported_k == k).then_some(*hash))
            .unwrap_or_else(|| panic!("no pinned group SRS is available for {entry} at k={k}"));
        let parameter_bytes = fs::read(srs_directory.join(format!("bls_midnight_2p{k}")))?;
        assert_eq!(hex::encode(Sha256::digest(&parameter_bytes)), srs_hash);
        let parameters = TrustedParameters::from_bytes(&parameter_bytes, k, srs_hash)?;
        let verifier_parameters = ParamsVerifier::read(parameter_bytes.as_slice())?;

        let initial = create_state(&plan, &BTreeMap::new())?;
        let execution = prepare(
            &plan,
            &inputs(&case["inputs"]),
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )?;
        assert_eq!(
            check(&execution, &relation)?,
            execution.activity_schedule,
            "{entry}"
        );
        assert_eq!(
            execution.returns_json(),
            returns(&case["expected"]),
            "{entry}"
        );

        let (prover_key, verifier_key) = block_on(relation.keygen(&parameters))?;
        let (proof, statement, activity) =
            block_on(relation.prove(OsRng, &parameters, prover_key, &execution.preimage))?;
        assert_eq!(activity, execution.activity_schedule, "{entry}");
        verifier_key.verify(&verifier_parameters, &proof, statement.iter().copied())?;

        let (commitment, _) = execution
            .preimage
            .communications_commitment
            .expect("public group results have a communication commitment");
        assert_eq!(statement.get(1), Some(&commitment), "{entry}");
        let mut changed_statement = statement;
        changed_statement[1] = commitment + Fr::from(1u64);
        assert!(
            verifier_key
                .verify(
                    &verifier_parameters,
                    &proof,
                    changed_statement.iter().copied(),
                )
                .is_err(),
            "{entry} proof accepted an altered public result commitment"
        );

        println!(
            "{entry} proof passed: k={k}, srs_sha256={srs_hash}, proof_bytes={}, altered_return_commitment=rejected",
            proof.0.len()
        );
    }
    Ok(())
}
