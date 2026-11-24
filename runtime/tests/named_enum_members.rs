#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use futures::executor::block_on;
use noctium_runtime::{
    Plan, check,
    control::{InvocationTarget, Session},
    create_state,
    host::{self, Capability, Context, Limits},
    prepare,
    proof::TrustedParameters,
    zkir::IrSource,
};
use rand::rngs::OsRng;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::{
    curve::Fr,
    proofs::{ParamsVerifier, Zkir},
};

const TYPE_ID: &str = "NamedEnumMembers.RecipientKind";
const MODULE_TYPE_ID: &str = "OtherModule.RecipientKind";
const MODULE_ENUM_K: u8 = 8;
const MODULE_ENUM_RELATION_SHA256: &str =
    "152f9f74ce36f3cabae5b39f87d13a75c56463b3103cd13d285fe1f668efc4cd";
const OFFICIAL_SRS_SHA256: &str =
    "909b707551eaaea79828e883cde6fc46ab15986c3b1d791bed462c9e2805c933";

fn choice(type_id: &str, variant: &str) -> Json {
    json!({
        "kind":"enum",
        "id":type_id,
        "variant":variant,
        "fields":[]
    })
}

fn session(
    control: &Json,
    attempt_id: &str,
    entrypoint: &str,
    inputs: BTreeMap<String, Json>,
) -> anyhow::Result<Session> {
    let binding = control["binding"]
        .as_str()
        .expect("embedded witness binding");
    let digest = hex::encode(Sha256::digest(binding.as_bytes()));
    Ok(Session::from_json_with_invocation_target(
        control.clone(),
        inputs,
        Context {
            protocol_version: 1,
            namespace: "noctium".into(),
            base_revision: "r0".into(),
            attempt_id: attempt_id.into(),
            capabilities: vec![Capability {
                id: "commit".into(),
                namespace: "noctium".into(),
                key_prefix: "noctium/".into(),
                operations: vec![host::CAS.into()],
            }],
            operations: Vec::new(),
            providers: Vec::new(),
            commit_capability: "commit".into(),
            limits: Limits::default(),
        },
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: entrypoint.into(),
        }),
    )?)
}

#[test]
#[ignore = "requires fresh NamedEnumMembers artifacts in NOCTIUM_NAMED_ENUM_MEMBERS_DIR"]
fn named_enum_members_preserve_nominal_variant_order_in_native_circuit() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_NAMED_ENUM_MEMBERS_DIR").expect("NOCTIUM_NAMED_ENUM_MEMBERS_DIR"),
    );
    let stem = "NamedEnumMembers.describe";
    let binding: Json =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.witness.json")))?)?;
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.witness.control.json")),
    )?)?;
    assert_eq!(
        serde_json::from_str::<Json>(control["binding"].as_str().unwrap())?,
        binding
    );

    let logical_inputs = control["inputs"].as_array().expect("logical inputs");
    assert_eq!(logical_inputs.len(), 1);
    assert_eq!(logical_inputs[0]["name"], "choice");
    let type_token = logical_inputs[0]["type"]
        .as_str()
        .expect("aggregate input type");
    let type_id = type_token
        .strip_prefix("Aggregate:")
        .expect("choice input is an aggregate");
    assert_eq!(logical_inputs[0]["visibility"], "public");
    assert!(binding["types"].as_array().is_some_and(|types| {
        types.iter().any(|ty| {
            ty["id"] == type_id
                && ty["schema"]["layout"]["kind"] == "enum"
                && ty["schema"]["layout"]["id"] == TYPE_ID
        })
    }));

    let plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    for (attempt_digit, variant, expected_is_contract) in
        [("1", "ShieldedUser", false), ("2", "Contract", true)]
    {
        let attempt = attempt_digit.repeat(64);
        let mut invocation = session(
            &control,
            &attempt,
            "describe",
            BTreeMap::from([("choice".into(), choice(TYPE_ID, variant))]),
        )?;
        assert_eq!(invocation.advance()?["status"], "completed");
        let completion = invocation.private_completion(&binding["nativeRelation"])?;
        let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;
        let execution = prepare(
            &plan,
            &inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        let returns = execution.returns_json();
        assert_eq!(
            returns.get("isContract"),
            Some(&json!(expected_is_contract))
        );
        assert_eq!(returns.get("selectedTag"), Some(&json!("2")));
    }
    Ok(())
}

#[test]
#[ignore = "requires fresh NamedEnumMembers artifacts in NOCTIUM_NAMED_ENUM_MEMBERS_DIR"]
fn module_enum_comparison_and_cast_preserve_wire_ids() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_NAMED_ENUM_MEMBERS_DIR").expect("NOCTIUM_NAMED_ENUM_MEMBERS_DIR"),
    );
    let stem = "NamedEnumMembers.compareModules";
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.witness.control.json")),
    )?)?;
    let binding: Json = serde_json::from_str(control["binding"].as_str().expect("binding"))?;
    let plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let relation = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    for (digit, left, right, expected) in [
        ("3", "ShieldedUser", "ShieldedUser", true),
        ("4", "Contract", "UnshieldedUser", false),
    ] {
        let mut invocation = session(
            &control,
            &digit.repeat(64),
            "compareModules",
            BTreeMap::from([
                ("choice".into(), choice(TYPE_ID, left)),
                ("selected".into(), choice(MODULE_TYPE_ID, right)),
            ]),
        )?;
        assert_eq!(invocation.advance()?["status"], "completed");
        let completion = invocation.private_completion(&binding["nativeRelation"])?;
        let inputs = serde_json::from_value(completion["inputs"].clone())?;
        let execution = prepare(
            &plan,
            &inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )?;
        assert_eq!(check(&execution, &relation)?, execution.activity_schedule);
        assert_eq!(execution.returns_json()["same"], expected);
        assert_eq!(execution.returns_json()["converted"], choice(MODULE_TYPE_ID, left));
    }

    let wrong_input = session(
        &control,
        &"5".repeat(64),
        "compareModules",
        BTreeMap::from([
            ("choice".into(), choice(TYPE_ID, "Contract")),
            ("selected".into(), choice(TYPE_ID, "Contract")),
        ]),
    );
    assert!(wrong_input.is_err(), "the wire ABI rejects the other module's enum ID");
    Ok(())
}

#[test]
#[ignore = "requires fresh NamedEnumMembers artifacts and the pinned trusted SRS"]
fn module_enum_comparison_generates_and_binds_native_proof() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_NAMED_ENUM_MEMBERS_DIR").expect("NOCTIUM_NAMED_ENUM_MEMBERS_DIR"),
    );
    let stem = "NamedEnumMembers.compareModules";
    let relation_bytes = fs::read(directory.join(format!("{stem}.zkir")))?;
    assert_eq!(
        hex::encode(Sha256::digest(&relation_bytes)),
        MODULE_ENUM_RELATION_SHA256
    );
    let relation = IrSource::load(relation_bytes.as_slice())?;
    assert_eq!(relation.k(), MODULE_ENUM_K);

    let plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &BTreeMap::from([
            ("choice.$tag".into(), json!("2")),
            ("selected.$tag".into(), json!("1")),
        ]),
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(
        execution.preimage.public_transcript_outputs,
        [Fr::from(2u64), Fr::from(1u64)]
    );
    assert_eq!(check(&execution, &relation)?, execution.activity_schedule);
    let returns = execution.returns_json();
    assert_eq!(returns["same"], json!(false));
    assert_eq!(returns["converted"], choice(MODULE_TYPE_ID, "Contract"));

    for input in 0..2 {
        let mut invalid_ordinal = execution.preimage.clone();
        invalid_ordinal.public_transcript_outputs[input] = Fr::from(3u64);
        assert!(invalid_ordinal.check(&relation).is_err());
    }

    let parameter_bytes = fs::read(
        std::env::var_os("NOCTIUM_MODULE_ENUM_PROOF_PARAMETERS")
            .expect("NOCTIUM_MODULE_ENUM_PROOF_PARAMETERS"),
    )?;
    let parameters =
        TrustedParameters::from_bytes(&parameter_bytes, MODULE_ENUM_K, OFFICIAL_SRS_SHA256)?;
    assert_eq!(parameters.sha256(), OFFICIAL_SRS_SHA256);
    let verifier_parameters = ParamsVerifier::read(parameter_bytes.as_slice())?;
    let (prover_key, verifier_key) = block_on(relation.keygen(&parameters))?;
    let (proof, statement, activity) = block_on(relation.prove(
        OsRng,
        &parameters,
        prover_key,
        &execution.preimage,
    ))?;
    assert_eq!(activity, execution.activity_schedule);
    let (return_commitment, _) = execution
        .preimage
        .communications_commitment
        .expect("public returns are bound by the communication commitment");
    assert_eq!(statement.get(1), Some(&return_commitment));
    verifier_key.verify(&verifier_parameters, &proof, statement.iter().copied())?;

    let mut changed_return_commitment = statement;
    changed_return_commitment[1] = return_commitment + Fr::from(1u64);
    assert!(verifier_key
        .verify(
            &verifier_parameters,
            &proof,
            changed_return_commitment.iter().copied(),
        )
        .is_err());
    Ok(())
}
