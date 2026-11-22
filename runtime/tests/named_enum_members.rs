#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Plan, check,
    control::{InvocationTarget, Session},
    create_state,
    host::{self, Capability, Context, Limits},
    prepare,
    zkir::IrSource,
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::PathBuf};

const TYPE_ID: &str = "NamedEnumMembers.RecipientKind";

fn choice(variant: &str) -> Json {
    json!({
        "kind":"enum",
        "id":TYPE_ID,
        "variant":variant,
        "fields":[]
    })
}

fn session(control: &Json, attempt_id: &str, value: Json) -> anyhow::Result<Session> {
    let binding = control["binding"]
        .as_str()
        .expect("embedded witness binding");
    let digest = hex::encode(Sha256::digest(binding.as_bytes()));
    Ok(Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([("choice".into(), value)]),
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
            entrypoint: "describe".into(),
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
        let mut invocation = session(&control, &attempt, choice(variant))?;
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
