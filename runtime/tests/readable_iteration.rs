#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Plan, check,
    control::{InvocationTarget, Session, TypedResponse},
    create_state,
    host::{self, Capability, Context, Limits, Operation, Provider},
    prepare,
    zkir::IrSource,
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::curve::Fr;

const SOURCE_NAME: &str = "ReadableIterationBlock";
const ENTRYPOINT: &str = "run";
const PROFILE: &str = "midnight-ledger-9-zkir-3.2.1";

fn items() -> Json {
    json!({
        "kind":"vector",
        "items":[
            {"kind":"uint","maximum":"255","value":"2"},
            {"kind":"uint","maximum":"255","value":"3"}
        ]
    })
}

fn output(first: &str, second: &str, total: &str) -> Json {
    json!({
        "kind":"struct",
        "id":"blockIteration.Output",
        "fields":[
            {"name":"first","value":{"kind":"native","value":first}},
            {"name":"second","value":{"kind":"native","value":second}},
            {"name":"total","value":{"kind":"native","value":total}}
        ]
    })
}

fn source_context(control: &Json, attempt_id: &str) -> Context {
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
                    parameter["name"]
                        .as_str()
                        .expect("parameter name")
                        .to_owned(),
                    parameter["type"]
                        .as_str()
                        .expect("parameter type")
                        .to_owned(),
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

fn reply(request: &Json, attempt_id: &str, value: Json) -> anyhow::Result<TypedResponse> {
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
    binding: Json,
    control: Json,
    plan: Plan,
    circuit: IrSource,
}

impl Fixture {
    fn load() -> anyhow::Result<Self> {
        let directory = PathBuf::from(
            std::env::var_os("NOCTIUM_READABLE_ITERATION_DIR")
                .expect("NOCTIUM_READABLE_ITERATION_DIR"),
        );
        let stem = format!("{SOURCE_NAME}.{ENTRYPOINT}");
        let binding: Json =
            serde_json::from_slice(&fs::read(directory.join(format!("{stem}.witness.json")))?)?;
        let control: Json = serde_json::from_slice(&fs::read(
            directory.join(format!("{stem}.witness.control.json")),
        )?)?;
        assert_eq!(
            serde_json::from_str::<Json>(control["binding"].as_str().expect("binding"))?,
            binding
        );
        assert_eq!(
            binding["sourceExport"],
            "noctium.witness-circuit.blockIteration.v1"
        );
        assert_eq!(binding["target"]["entrypoint"], ENTRYPOINT);
        let calls = binding["calls"].as_array().expect("emitted witness calls");
        assert_eq!(calls.len(), 2);
        assert_eq!(calls[0]["name"], "blockItems");
        assert_eq!(calls[1]["name"], "blockOffset");

        let plan: Plan =
            serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
        assert_eq!(plan.target.as_deref(), Some(PROFILE));
        let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
        Ok(Self {
            binding,
            control,
            plan,
            circuit,
        })
    }

    fn session(&self, attempt_id: &str) -> anyhow::Result<Session> {
        let binding_text = self.control["binding"].as_str().expect("control binding");
        let digest = hex::encode(Sha256::digest(binding_text.as_bytes()));
        Ok(Session::from_json_with_invocation_target(
            self.control.clone(),
            BTreeMap::from([("seed".into(), json!("7"))]),
            source_context(&self.control, attempt_id),
            Some(&digest),
            Some(InvocationTarget {
                contract_address: "a".repeat(64),
                entrypoint: ENTRYPOINT.into(),
            }),
        )?)
    }
}

struct EmptyIdentityFixture {
    binding: Json,
    control: Json,
    plan: Plan,
    circuit: IrSource,
}

impl EmptyIdentityFixture {
    fn load() -> anyhow::Result<Self> {
        let directory = PathBuf::from(
            std::env::var_os("NOCTIUM_READABLE_ITERATION_DIR")
                .expect("NOCTIUM_READABLE_ITERATION_DIR"),
        );
        let stem = "ReadableIteration.emptyIdentity";
        let binding: Json =
            serde_json::from_slice(&fs::read(directory.join(format!("{stem}.witness.json")))?)?;
        let control: Json = serde_json::from_slice(&fs::read(
            directory.join(format!("{stem}.witness.control.json")),
        )?)?;
        assert_eq!(
            serde_json::from_str::<Json>(control["binding"].as_str().expect("binding"))?,
            binding
        );
        assert_eq!(
            binding["sourceExport"],
            "noctium.witness-circuit.emptyNativeMap.v1"
        );
        assert_eq!(binding["target"]["entrypoint"], "emptyIdentity");
        let calls = binding["calls"].as_array().expect("emitted witness calls");
        assert_eq!(calls.len(), 2);
        assert_eq!(calls[0]["name"], "iterationEmptyTuple");
        assert_eq!(calls[1]["name"], "acceptEmptyNativeVector");

        let plan: Plan =
            serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
        assert_eq!(plan.target.as_deref(), Some(PROFILE));
        let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
        Ok(Self {
            binding,
            control,
            plan,
            circuit,
        })
    }

    fn session(&self, attempt_id: &str) -> anyhow::Result<Session> {
        let binding_text = self.control["binding"].as_str().expect("control binding");
        let digest = hex::encode(Sha256::digest(binding_text.as_bytes()));
        Ok(Session::from_json_with_invocation_target(
            self.control.clone(),
            BTreeMap::new(),
            source_context(&self.control, attempt_id),
            Some(&digest),
            Some(InvocationTarget {
                contract_address: "a".repeat(64),
                entrypoint: "emptyIdentity".into(),
            }),
        )?)
    }
}

fn run_case(
    fixture: &Fixture,
    offset: &str,
    attempt_number: usize,
) -> anyhow::Result<(Session, Json, Vec<(String, String)>)> {
    let attempt_id = format!("{attempt_number:064x}");
    let mut session = fixture.session(&attempt_id)?;
    let callbacks = [
        ("blockItems", "7", items()),
        ("blockOffset", "8", json!(offset)),
    ];
    let mut trace = Vec::new();
    for (name, marker, value) in callbacks {
        let pending = session.advance()?;
        assert_eq!(pending["status"], "need_host");
        assert_eq!(pending["request"]["name"], name);
        assert_eq!(
            session.private_request()?["arguments"]["seed"],
            marker,
            "unexpected argument for {name}"
        );
        trace.push((name.to_owned(), marker.to_owned()));
        session.resume_typed(reply(&pending["request"], &attempt_id, value)?)?;
    }
    let terminal = session.advance()?;
    Ok((session, terminal, trace))
}

fn prepare_execution(
    fixture: &Fixture,
    inputs: &BTreeMap<String, Json>,
) -> anyhow::Result<noctium_runtime::Execution> {
    let initial = create_state(&fixture.plan, &BTreeMap::new())?;
    Ok(prepare(
        &fixture.plan,
        inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?)
}

#[test]
#[ignore = "requires fresh ReadableIterationBlock artifacts in NOCTIUM_READABLE_ITERATION_DIR"]
fn statement_bodied_map_and_fold_match_host_and_native_relations() -> anyhow::Result<()> {
    let fixture = Fixture::load()?;

    let (mut accepted_session, completed, success_trace) = run_case(&fixture, "10", 1)?;
    assert_eq!(completed["status"], "completed");
    assert_eq!(completed["result"], output("12", "13", "25"));

    let completion = accepted_session.private_completion(&fixture.binding["nativeRelation"])?;
    let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;
    let mut execution = prepare_execution(&fixture, &inputs)?;
    assert_eq!(execution.returns_json()["mappedFirst"], "12");
    assert_eq!(execution.returns_json()["mappedSecond"], "13");
    assert_eq!(execution.returns_json()["sum"], "25");
    assert_eq!(
        check(&execution, &fixture.circuit)?,
        execution.activity_schedule
    );

    assert_eq!(
        execution.preimage.private_transcript,
        [2u64, 3, 10].map(Fr::from)
    );
    execution.preimage.private_transcript[2] = Fr::from(40u64);
    assert!(check(&execution, &fixture.circuit).is_err());

    let (_rejected_session, rejected, failure_trace) = run_case(&fixture, "40", 2)?;
    assert_eq!(rejected["status"], "failed");
    assert_eq!(failure_trace, success_trace);
    Ok(())
}

#[test]
#[ignore = "requires fresh ReadableIteration outputs in NOCTIUM_READABLE_ITERATION_DIR"]
fn empty_identity_map_passes_an_empty_native_vector_without_a_map_callback() -> anyhow::Result<()> {
    let fixture = EmptyIdentityFixture::load()?;
    let attempt_id = format!("{:064x}", 3);
    let mut session = fixture.session(&attempt_id)?;

    let first = session.advance()?;
    assert_eq!(first["status"], "need_host");
    assert_eq!(first["request"]["name"], "iterationEmptyTuple");
    assert_eq!(session.private_request()?["arguments"], json!({}));
    session.resume_typed(reply(
        &first["request"],
        &attempt_id,
        json!({"kind":"tuple","items":[]}),
    )?)?;

    let second = session.advance()?;
    assert_eq!(second["status"], "need_host");
    assert_eq!(second["request"]["name"], "acceptEmptyNativeVector");
    assert_eq!(
        session.private_request()?["arguments"]["values"],
        json!({"kind":"vector","items":[]})
    );
    session.resume_typed(reply(&second["request"], &attempt_id, json!("41"))?)?;

    let completed = session.advance()?;
    assert_eq!(completed["status"], "completed");
    assert_eq!(completed["result"], "41");

    let completion = session.private_completion(&fixture.binding["nativeRelation"])?;
    let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;
    let initial = create_state(
        &fixture.plan,
        &BTreeMap::from([("total".into(), json!("0"))]),
    )?;
    let execution = prepare(
        &fixture.plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(execution.returns_json()["mapped"], "41");
    assert_eq!(check(&execution, &fixture.circuit)?, execution.activity_schedule);
    Ok(())
}
