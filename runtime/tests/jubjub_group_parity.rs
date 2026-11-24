#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Plan, check, create_state, field_decimal, prepare, proof::TrustedParameters, zkir::IrSource,
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, env, fs, path::PathBuf};
use transient_crypto::curve::{EmbeddedFr, EmbeddedGroupAffine};

const JUBJUB_PROJECTION_K: u8 = 6;
const JUBJUB_PROJECTION_RELATION_SHA256: &str =
    "153c6e451fc5eb9e8e87221b0ec9074c0af9c91d5b69b9c6a8238d81454a7a21";
const OFFICIAL_K6_SRS_SHA256: &str =
    "cf2ad6be7d0fedf5bec2aaa35f6be4aca33053d74268fdf5aa54fcb2891ea6df";

fn artifact_directory() -> PathBuf {
    PathBuf::from(
        env::var_os("NOCTIUM_JUBJUB_GROUP_PARITY_DIR")
            .expect("NOCTIUM_JUBJUB_GROUP_PARITY_DIR must point to fresh Lean outputs"),
    )
}

fn fixture(directory: &PathBuf, entry: &str) -> anyhow::Result<(Plan, IrSource)> {
    let stem = format!("JubjubGroupParity.{entry}");
    let plan = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let relation = IrSource::load(fs::read(directory.join(format!("{stem}.zkir")))?.as_slice())?;
    Ok((plan, relation))
}

fn point_json(point: EmbeddedGroupAffine) -> Json {
    let x = field_decimal(point.x().expect("point x-coordinate"));
    let y = field_decimal(point.y().expect("point y-coordinate"));
    json!({"kind":"jubjubPoint", "x":x, "y":y})
}

fn point_coordinates(point: EmbeddedGroupAffine) -> (String, String) {
    (
        field_decimal(point.x().expect("point x-coordinate")),
        field_decimal(point.y().expect("point y-coordinate")),
    )
}

#[test]
#[ignore = "requires fresh JubjubGroupParity artifacts in NOCTIUM_JUBJUB_GROUP_PARITY_DIR"]
fn native_jubjub_group_operations_match_compact_group_parity() -> anyhow::Result<()> {
    let directory = artifact_directory();
    let plan: Plan = serde_json::from_slice(&fs::read(
        directory.join("JubjubGroupParity.groupParity.impact.json"),
    )?)?;
    let circuit =
        IrSource::load(fs::read(directory.join("JubjubGroupParity.groupParity.zkir"))?.as_slice())?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();

    let point = EmbeddedGroupAffine::generator();
    let identity = EmbeddedGroupAffine::identity();
    let scalar = EmbeddedFr::from(1u64);
    let [point_x, point_y] = [point.x().unwrap(), point.y().unwrap()];
    let inputs = BTreeMap::<String, Json>::from([
        ("pointX".into(), json!(field_decimal(point_x))),
        ("pointY".into(), json!(field_decimal(point_y))),
        ("rawScalar".into(), json!("1")),
    ]);

    let execution = prepare(&plan, &inputs, &initial, parameters, address)?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);

    let generated = EmbeddedGroupAffine::generator() * scalar;
    let multiplied = point * scalar;
    let sum = point + identity;
    let negated = -point;
    let cancelled = point + negated;
    let identity_negated = -identity;
    let coordinates =
        |value: EmbeddedGroupAffine| [value.x().unwrap(), value.y().unwrap()].map(field_decimal);
    let [checked_x, checked_y] = coordinates(point);
    let [generator_x, generator_y] = coordinates(generated);
    let [multiplied_x, multiplied_y] = coordinates(multiplied);
    let [sum_x, sum_y] = coordinates(sum);
    let [negated_x, negated_y] = coordinates(negated);
    let [cancelled_x, cancelled_y] = coordinates(cancelled);
    let [identity_negated_x, identity_negated_y] = coordinates(identity_negated);

    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([
            ("resultCheckedX".into(), json!(checked_x)),
            ("resultCheckedY".into(), json!(checked_y)),
            ("resultGeneratorX".into(), json!(generator_x)),
            ("resultGeneratorY".into(), json!(generator_y)),
            ("resultMultipliedX".into(), json!(multiplied_x)),
            ("resultMultipliedY".into(), json!(multiplied_y)),
            ("resultSumX".into(), json!(sum_x)),
            ("resultSumY".into(), json!(sum_y)),
            ("resultNegatedX".into(), json!(negated_x)),
            ("resultNegatedY".into(), json!(negated_y)),
            ("resultCancelledX".into(), json!(cancelled_x)),
            ("resultCancelledY".into(), json!(cancelled_y)),
            ("resultIdentityNegatedX".into(), json!(identity_negated_x)),
            ("resultIdentityNegatedY".into(), json!(identity_negated_y)),
            ("resultScalar".into(), json!("1")),
        ])
    );
    assert_eq!(sum, point, "adding the identity preserves the point");
    assert_eq!(cancelled, identity, "a point plus its negation is identity");
    assert_eq!(
        identity_negated, identity,
        "negating identity preserves identity"
    );
    Ok(())
}

#[test]
#[ignore = "requires fresh JubjubGroupParity artifacts in NOCTIUM_JUBJUB_GROUP_PARITY_DIR"]
fn jubjub_group_point_projection_accepts_generator_and_identity() -> anyhow::Result<()> {
    let directory = artifact_directory();
    let (plan, relation) = fixture(&directory, "project")?;
    assert_eq!(plan.entrypoint, "project");
    assert_eq!(plan.circuit.inputs.len(), 1);
    assert_eq!(plan.circuit.inputs[0].name, "point");
    assert_eq!(plan.circuit.inputs[0].ty, "JubjubPoint");
    assert_eq!(plan.circuit.inputs[0].visibility, "private");
    assert_eq!(
        plan.returns
            .iter()
            .map(|output| (output.name.as_str(), output.ty.as_str()))
            .collect::<Vec<_>>(),
        [("resultX", "Native"), ("resultY", "Native")]
    );

    let initial = create_state(&plan, &BTreeMap::new())?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    for (point, x, y) in [
        (
            EmbeddedGroupAffine::generator(),
            "28336281903124990867587793011069573392383982287722241916350956173377953689573",
            "39385640392217313770878525135509063452020585410343666726093009378539878503883",
        ),
        (EmbeddedGroupAffine::identity(), "0", "1"),
    ] {
        let inputs = BTreeMap::from([("point".into(), point_json(point))]);
        let execution = prepare(&plan, &inputs, &initial, parameters, address)?;
        assert_eq!(check(&execution, &relation)?, execution.activity_schedule);
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([("resultX".into(), json!(x)), ("resultY".into(), json!(y))])
        );
        assert_eq!(execution.after.state.get_ref(), initial.get_ref());
    }

    let malformed = BTreeMap::from([(
        "point".into(),
        json!({"kind":"jubjubPoint", "x":"0", "y":"0"}),
    )]);
    assert!(
        prepare(&plan, &malformed, &initial, parameters, address).is_err(),
        "an off-curve Jubjub point must reject"
    );
    Ok(())
}

#[test]
#[ignore = "requires fresh JubjubGroupParity artifacts in NOCTIUM_JUBJUB_GROUP_PARITY_DIR and the official k6 SRS in NOCTIUM_JUBJUB_PROJECTION_PROOF_PARAMETERS"]
fn jubjub_projection_generates_and_binds_native_proof() -> anyhow::Result<()> {
    use futures::executor::block_on;
    use rand::rngs::OsRng;
    use transient_crypto::{
        curve::Fr,
        proofs::{ParamsVerifier, Zkir},
    };

    let directory = artifact_directory();
    let plan: Plan = serde_json::from_slice(&fs::read(
        directory.join("JubjubGroupParity.project.impact.json"),
    )?)?;
    let relation_bytes = fs::read(directory.join("JubjubGroupParity.project.zkir"))?;
    assert_eq!(
        hex::encode(Sha256::digest(&relation_bytes)),
        JUBJUB_PROJECTION_RELATION_SHA256
    );
    let relation = IrSource::load(relation_bytes.as_slice())?;
    assert_eq!(relation.k(), JUBJUB_PROJECTION_K);
    let parameter_bytes = fs::read(
        env::var_os("NOCTIUM_JUBJUB_PROJECTION_PROOF_PARAMETERS")
            .expect("NOCTIUM_JUBJUB_PROJECTION_PROOF_PARAMETERS"),
    )?;
    let parameters = TrustedParameters::from_bytes(
        &parameter_bytes,
        JUBJUB_PROJECTION_K,
        OFFICIAL_K6_SRS_SHA256,
    )?;
    assert_eq!(parameters.sha256(), OFFICIAL_K6_SRS_SHA256);
    let verifier_parameters = ParamsVerifier::read(parameter_bytes.as_slice())?;

    let initial = create_state(&plan, &BTreeMap::new())?;
    let point = EmbeddedGroupAffine::generator();
    let (x, y) = point_coordinates(point);
    let inputs = BTreeMap::from([("point".into(), point_json(point))]);
    let execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &relation)?, execution.activity_schedule);
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([("resultX".into(), json!(x)), ("resultY".into(), json!(y))])
    );

    let (prover_key, verifier_key) = block_on(relation.keygen(&parameters))?;
    let (proof, statement, activity) = block_on(relation.prove(
        OsRng,
        &parameters,
        prover_key,
        &execution.preimage,
    ))?;
    assert_eq!(activity, execution.activity_schedule);
    verifier_key.verify(&verifier_parameters, &proof, statement.iter().copied())?;

    let (commitment, _) = execution
        .preimage
        .communications_commitment
        .expect("the two projected coordinates are bound by the communication commitment");
    assert_eq!(statement.get(1), Some(&commitment));
    let mut changed_statement = statement;
    changed_statement[1] = commitment + Fr::from(1u64);
    assert!(verifier_key
        .verify(
            &verifier_parameters,
            &proof,
            changed_statement.iter().copied(),
        )
        .is_err());

    println!(
        "Jubjub projection proof passed: k={}, relation_sha256={}, srs_sha256={}, proof_bytes={}, altered_return_commitment=rejected",
        JUBJUB_PROJECTION_K,
        JUBJUB_PROJECTION_RELATION_SHA256,
        parameters.sha256(),
        proof.0.len(),
    );
    Ok(())
}
