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

const SOURCE_NAMESPACE: &str = "ReadableBindPatterns";
const PROFILE: &str = "midnight-ledger-9-zkir-3.2.1";
const PROVIDER: &str = "ReadableBindPatterns.load";

fn packet() -> Json {
    json!({
        "kind":"struct",
        "id":"ReadableBindPatterns.Packet",
        "fields":[
            {"name":"reading","value":{
                "kind":"struct",
                "id":"ReadableBindPatterns.Reading",
                "fields":[
                    {"name":"count","value":{"kind":"uint","maximum":"255","value":"17"}},
                    {"name":"active","value":{"kind":"bool","value":true}}
                ]
            }},
            {"name":"measures","value":{"kind":"tuple","items":[
                {"kind":"native","value":"9"},
                {"kind":"bool","value":false}
            ]}},
            {"name":"omitted","value":{"kind":"native","value":"5"}}
        ]
    })
}

fn source_context(attempt_id: &str, result_type: &str) -> Context {
    let operation = format!("noctium.witness.{PROVIDER}.v1");
    Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "r0".into(),
        attempt_id: attempt_id.into(),
        capabilities: vec![
            Capability {
                id: "commit".into(),
                namespace: "noctium".into(),
                key_prefix: "noctium/".into(),
                operations: vec![host::CAS.into()],
            },
            Capability {
                id: PROVIDER.into(),
                namespace: "noctium".into(),
                key_prefix: "noctium/".into(),
                operations: vec![operation.clone()],
            },
        ],
        operations: vec![Operation {
            operation: operation.clone(),
            argument_schema: BTreeMap::from([("seed".into(), "Native".into())]),
            result_schema: result_type.into(),
        }],
        providers: vec![Provider {
            input: PROVIDER.into(),
            operation,
            capability: PROVIDER.into(),
            arguments: BTreeMap::new(),
        }],
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

fn session(
    control: &Json,
    entrypoint: &str,
    attempt_id: &str,
    result_type: &str,
) -> anyhow::Result<Session> {
    let binding = control["binding"]
        .as_str()
        .expect("embedded witness binding");
    let digest = hex::encode(Sha256::digest(binding.as_bytes()));
    Ok(Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([("seed".into(), json!("7"))]),
        source_context(attempt_id, result_type),
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: entrypoint.into(),
        }),
    )?)
}

fn packet_session(control: &Json, packet: Json, attempt_id: &str) -> anyhow::Result<Session> {
    let binding = control["binding"]
        .as_str()
        .expect("embedded witness binding");
    let digest = hex::encode(Sha256::digest(binding.as_bytes()));
    Ok(Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([("packet".into(), packet)]),
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
            entrypoint: "summarize".into(),
        }),
    )?)
}

fn reply(request: &Json, attempt_id: &str, value: Json) -> TypedResponse {
    serde_json::from_value(json!({
        "protocolVersion": 2,
        "requestId": request["requestId"],
        "attemptId": attempt_id,
        "outcome": "value",
        "operation": request["operation"],
        "capability": request["capability"],
        "schema": request["schema"],
        "value": value,
    }))
    .expect("typed host response")
}

struct Fixture {
    binding: Json,
    control: Json,
    plan: Plan,
    circuit: IrSource,
}

impl Fixture {
    fn load(entrypoint: &str) -> anyhow::Result<Self> {
        let directory = PathBuf::from(
            std::env::var_os("NOCTIUM_BIND_PATTERNS_DIR").expect("NOCTIUM_BIND_PATTERNS_DIR"),
        );
        let stem = format!("{SOURCE_NAMESPACE}.{entrypoint}");
        let binding: Json =
            serde_json::from_slice(&fs::read(directory.join(format!("{stem}.witness.json")))?)?;
        let control: Json = serde_json::from_slice(&fs::read(
            directory.join(format!("{stem}.witness.control.json")),
        )?)?;
        assert_eq!(
            serde_json::from_str::<Json>(control["binding"].as_str().unwrap())?,
            binding
        );
        assert_eq!(
            binding["sourceExport"],
            format!("noctium.witness-circuit.{stem}.v1")
        );
        let plan: Plan = serde_json::from_reader(fs::File::open(
            directory.join(format!("{stem}.impact.json")),
        )?)?;
        assert_eq!(plan.target.as_deref(), Some(PROFILE));
        assert_eq!(
            plan.target_profile
                .as_ref()
                .and_then(|profile| profile["name"].as_str()),
            Some(PROFILE)
        );
        let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
        Ok(Self {
            binding,
            control,
            plan,
            circuit,
        })
    }

    fn check_returns(&self, session: &mut Session) -> anyhow::Result<BTreeMap<String, Json>> {
        let completion = session.private_completion(&self.binding["nativeRelation"])?;
        let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;
        let initial = create_state(&self.plan, &BTreeMap::new())?;
        let execution = prepare(
            &self.plan,
            &inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )?;
        assert_eq!(
            check(&execution, &self.circuit)?,
            execution.activity_schedule
        );
        Ok(execution.returns_json())
    }
}

#[test]
#[ignore = "requires fresh ReadableBindPatterns artifacts in NOCTIUM_BIND_PATTERNS_DIR"]
fn readable_bind_patterns_unpack_one_packet_and_check_the_native_returns() -> anyhow::Result<()> {
    let attempt = "6".repeat(64);
    for entrypoint in ["unpack", "unpackViews"] {
        let fixture = Fixture::load(entrypoint)?;
        let result_type = fixture.control["witnesses"]
            .as_array()
            .expect("witness declarations")
            .iter()
            .find(|witness| witness["name"] == PROVIDER)
            .and_then(|witness| witness["resultType"].as_str())
            .expect("load aggregate result type");
        let type_id = result_type
            .strip_prefix("Aggregate:")
            .expect("load result is an aggregate");
        assert!(fixture.binding["types"].as_array().is_some_and(|types| {
            types.iter().any(|ty| {
                ty["id"] == type_id && ty["schema"]["layout"]["id"] == "ReadableBindPatterns.Packet"
            })
        }));

        let mut session = session(&fixture.control, entrypoint, &attempt, result_type)?;
        let pending = session.advance()?;
        assert_eq!(pending["status"], "need_host");
        assert_eq!(pending["request"]["name"], PROVIDER);
        assert_eq!(
            pending["request"]["operation"],
            "noctium.witness.ReadableBindPatterns.load.v1"
        );
        assert_eq!(pending["request"]["schema"], result_type);
        assert_eq!(session.private_request()?["arguments"]["seed"], "7");
        session.resume_typed(reply(&pending["request"], &attempt, packet()))?;
        let completed = session.advance()?;
        assert_eq!(completed["status"], "completed");

        let returns = fixture.check_returns(&mut session)?;
        assert_eq!(returns["totalResult"], "26");
        if entrypoint == "unpack" {
            assert_eq!(completed["result"], "26");
            assert_eq!(returns.len(), 1);
        } else {
            assert_eq!(returns["activeResult"], true);
            assert_eq!(returns.len(), 2);
        }
    }
    Ok(())
}

#[test]
#[ignore = "requires fresh ReadableBindPatterns artifacts in NOCTIUM_BIND_PATTERNS_DIR"]
fn readable_bind_patterns_summarize_typed_packet_without_a_provider() -> anyhow::Result<()> {
    let fixture = Fixture::load("summarize")?;
    let inputs = fixture.control["inputs"]
        .as_array()
        .expect("logical inputs");
    assert_eq!(inputs.len(), 1);
    assert_eq!(inputs[0]["name"], "packet");
    assert_eq!(inputs[0]["visibility"], "public");
    let attempt = "7".repeat(64);
    let mut session = packet_session(&fixture.control, packet(), &attempt)?;
    assert_eq!(session.advance()?["status"], "completed");
    assert_eq!(
        fixture.check_returns(&mut session)?,
        BTreeMap::from([
            ("activeResult".into(), json!(true)),
            ("totalResult".into(), json!("26"))
        ])
    );
    Ok(())
}
