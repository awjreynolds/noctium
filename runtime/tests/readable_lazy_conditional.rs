#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    check,
    control::{InvocationTarget, Session, TypedResponse},
    create_state,
    host::{self, Capability, Context, Limits, Operation, Provider},
    prepare,
    zkir::IrSource,
    Plan,
};
use serde_json::{json, Value as Json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::PathBuf};

const SOURCE_NAMESPACE: &str = "ReadableLazyConditional";
const PROFILE: &str = "midnight-ledger-9-zkir-3.2.1";
const PAYLOAD_ID: &str = "ReadableLazyConditional.Payload";

fn payload(amount: &str, enabled: bool) -> Json {
    json!({
        "kind":"struct",
        "id":PAYLOAD_ID,
        "fields":[
            {"name":"amount","value":{"kind":"native","value":amount}},
            {"name":"extra","value":{
                "kind":"struct",
                "id":"ReadableLazyConditional.Extra",
                "fields":[{"name":"enabled","value":{"kind":"bool","value":enabled}}]
            }}
        ]
    })
}

fn context(control: &Json, attempt_id: &str) -> Context {
    let mut operations = BTreeMap::<String, Operation>::new();
    let mut providers = Vec::new();
    let mut capability_operations = BTreeMap::<String, Vec<String>>::new();
    for witness in control["witnesses"]
        .as_array()
        .expect("witness declarations")
    {
        let name = witness["name"].as_str().expect("witness name").to_owned();
        let operation = witness["operation"]
            .as_str()
            .expect("witness operation")
            .to_owned();
        let capability = witness["capability"]
            .as_str()
            .expect("witness capability")
            .to_owned();
        let argument_schema = witness["parameters"]
            .as_array()
            .expect("witness parameters")
            .iter()
            .map(|parameter| {
                (
                    parameter["name"].as_str().unwrap().to_owned(),
                    parameter["type"].as_str().unwrap().to_owned(),
                )
            })
            .collect();
        operations.insert(
            operation.clone(),
            Operation {
                operation: operation.clone(),
                argument_schema,
                result_schema: witness["resultType"]
                    .as_str()
                    .expect("witness result type")
                    .to_owned(),
            },
        );
        capability_operations
            .entry(capability.clone())
            .or_default()
            .push(operation.clone());
        providers.push(Provider {
            input: name,
            operation,
            capability,
            arguments: BTreeMap::new(),
        });
    }
    let mut capabilities = capability_operations
        .into_iter()
        .map(|(id, operations)| Capability {
            id,
            namespace: "noctium".into(),
            key_prefix: "lookup/".into(),
            operations,
        })
        .collect::<Vec<_>>();
    capabilities.push(Capability {
        id: "commit".into(),
        namespace: "noctium".into(),
        key_prefix: "noctium/".into(),
        operations: vec![host::CAS.into()],
    });
    Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "r0".into(),
        attempt_id: attempt_id.into(),
        capabilities,
        operations: operations.into_values().collect(),
        providers,
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

fn typed_reply(request: &Json, attempt_id: &str, value: Json) -> Result<TypedResponse> {
    Ok(serde_json::from_value(json!({
        "protocolVersion": 2,
        "requestId": request["requestId"],
        "attemptId": attempt_id,
        "outcome": "value",
        "operation": request["operation"],
        "capability": request["capability"],
        "schema": request["schema"],
        "value": value,
    }))?)
}

struct Fixture {
    entrypoint: String,
    binding: Json,
    control: Json,
    plan: Plan,
    circuit: IrSource,
}

impl Fixture {
    fn load(entrypoint: &str) -> Result<Self> {
        let directory = PathBuf::from(
            std::env::var_os("NOCTIUM_READABLE_LAZY_CONDITIONAL_DIR")
                .expect("NOCTIUM_READABLE_LAZY_CONDITIONAL_DIR"),
        );
        let stem = format!("{SOURCE_NAMESPACE}.{entrypoint}");
        let binding: Json =
            serde_json::from_slice(&fs::read(directory.join(format!("{stem}.witness.json")))?)?;
        let control: Json = serde_json::from_slice(&fs::read(
            directory.join(format!("{stem}.witness.control.json")),
        )?)?;
        assert_eq!(
            serde_json::from_str::<Json>(control["binding"].as_str().expect("control binding"))?,
            binding
        );
        assert_eq!(
            binding["sourceExport"],
            format!("noctium.witness-circuit.{stem}.v1")
        );
        let plan: Plan =
            serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
        assert_eq!(plan.target.as_deref(), Some(PROFILE));
        let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
        Ok(Self {
            entrypoint: entrypoint.into(),
            binding,
            control,
            plan,
            circuit,
        })
    }

    fn session(&self, choice: bool, expected: &str, attempt_id: &str) -> Result<Session> {
        let binding = self.control["binding"].as_str().expect("control binding");
        let digest = hex::encode(Sha256::digest(binding.as_bytes()));
        Ok(Session::from_json_with_invocation_target(
            self.control.clone(),
            BTreeMap::from([
                ("choice".into(), json!(choice)),
                ("expected".into(), json!(expected)),
            ]),
            context(&self.control, attempt_id),
            Some(&digest),
            Some(InvocationTarget {
                contract_address: "a".repeat(64),
                entrypoint: self.entrypoint.clone(),
            }),
        )?)
    }
}

fn assert_fixture_shape(fixture: &Fixture) {
    assert_eq!(fixture.control["inputs"][0]["name"], "choice");
    assert_eq!(fixture.control["inputs"][0]["visibility"], "public");
    assert_eq!(fixture.control["inputs"][1]["name"], "expected");
    assert_eq!(fixture.control["inputs"][1]["visibility"], "public");
    assert_eq!(
        fixture.binding["circuitOutputs"].as_array().unwrap().len(),
        2
    );
    assert!(fixture.binding["types"].as_array().is_some_and(|types| {
        types.iter().any(|ty| {
            ty["schema"]["layout"]["id"] == PAYLOAD_ID
                && ty["schema"]["layout"]["fields"]
                    .as_array()
                    .is_some_and(|fields| fields.iter().any(|field| field["name"] == "extra"))
        })
    }));
}

fn run_case(
    fixture: &Fixture,
    choice: bool,
    expected: &str,
    attempt: usize,
    accepted: bool,
) -> Result<()> {
    let attempt_id = format!("{attempt:064x}");
    let mut session = fixture.session(choice, expected, &attempt_id)?;
    let selected = if choice { "loadLeft" } else { "loadRight" };
    let expected_provider = format!("{SOURCE_NAMESPACE}.{selected}");
    let amount = if choice { "7" } else { "9" };
    let mut providers = 0;
    let outcome = loop {
        let status = session.advance()?;
        match status["status"].as_str().expect("session status") {
            "need_host" => {
                let request = &status["request"];
                let name = request["name"].as_str().expect("provider name");
                assert_eq!(name, expected_provider);
                providers += 1;
                session.resume_typed(typed_reply(
                    request,
                    &attempt_id,
                    payload(amount, choice),
                )?)?;
            }
            terminal @ ("completed" | "failed") => break terminal.to_owned(),
            other => anyhow::bail!("unexpected witness status {other}"),
        }
    };
    assert_eq!(providers, 1, "only one branch provider must run");
    assert_eq!(outcome, if accepted { "completed" } else { "failed" });
    if !accepted {
        return Ok(());
    }

    let completion = session.private_completion(&fixture.binding["nativeRelation"])?;
    let mut inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;
    let initial = create_state(&fixture.plan, &BTreeMap::new())?;
    let execution = prepare(
        &fixture.plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(execution.returns_json()["observed"], amount);
    assert_eq!(execution.returns_json()["enabled"], choice);
    assert_eq!(
        check(&execution, &fixture.circuit)?,
        execution.activity_schedule
    );

    let wrong_expected = if choice { "9" } else { "7" };
    assert_eq!(
        inputs.insert("expected".into(), json!(wrong_expected)),
        Some(json!(expected))
    );
    let rejected = prepare(
        &fixture.plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert!(check(&rejected, &fixture.circuit).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh ReadableLazyConditional artifacts in NOCTIUM_READABLE_LAZY_CONDITIONAL_DIR"]
fn readable_aggregate_conditional_runs_only_the_selected_provider_and_assertion() -> Result<()> {
    let fixture = Fixture::load("choose")?;
    assert_fixture_shape(&fixture);

    run_case(&fixture, true, "7", 1, true)?;
    run_case(&fixture, false, "9", 2, true)?;
    run_case(&fixture, true, "9", 3, false)?;
    Ok(())
}

#[test]
#[ignore = "requires fresh ReadableLazyConditional artifacts in NOCTIUM_READABLE_LAZY_CONDITIONAL_DIR"]
fn readable_short_circuit_skips_inactive_provider_and_rejects_wrong_expectation() -> Result<()> {
    let fixture = Fixture::load("shortCircuit")?;
    assert_fixture_shape(&fixture);

    run_case(&fixture, true, "7", 4, true)?;
    run_case(&fixture, false, "9", 5, true)?;
    run_case(&fixture, true, "9", 6, false)?;
    Ok(())
}
