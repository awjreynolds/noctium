#![cfg(feature = "zkir-321")]

use anyhow::Result;
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

fn wire_session(control: &Json, coin: Json) -> Result<Session> {
    let binding = control["binding"].as_str().expect("witness binding");
    let pin = hex::encode(Sha256::digest(binding.as_bytes()));
    Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([("coin".into(), coin)]),
        Context {
            protocol_version: 1,
            namespace: "noctium".into(),
            base_revision: "r0".into(),
            attempt_id: "b".repeat(64),
            capabilities: vec![Capability {
                id: "commit".into(),
                namespace: "noctium".into(),
                key_prefix: "noctium/".into(),
                operations: vec![host::CAS.into()],
            }],
            operations: vec![],
            providers: vec![],
            commit_capability: "commit".into(),
            limits: Limits::default(),
        },
        Some(&pin),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: "echo".into(),
        }),
    )
}

fn coin(nonce: &[u8], color: &[u8], value: &str, mt_index: &str) -> Json {
    json!({
        "kind":"struct",
        "id":"Noctium.Midnight.QualifiedShieldedCoinInfo",
        "fields":[
            {"name":"nonce","value":{"kind":"bytes","values":nonce}},
            {"name":"color","value":{"kind":"bytes","values":color}},
            {"name":"value","value":{"kind":"uint","maximum":"340282366920938463463374607431768211455","value":value}},
            {"name":"mt_index","value":{"kind":"uint","maximum":"18446744073709551615","value":mt_index}}
        ]
    })
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_QUALIFIED_COIN_ABI_DIR"]
fn qualified_shielded_coin_info_roundtrips_full_width_values() -> Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_QUALIFIED_COIN_ABI_DIR").expect("NOCTIUM_QUALIFIED_COIN_ABI_DIR"),
    );
    let name = "QualifiedShieldedCoinInfoWireFixture.echo";
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{name}.witness.control.json")),
    )?)?;
    let binding: Json = serde_json::from_str(control["binding"].as_str().expect("binding"))?;
    assert_eq!(control["inputs"][0]["name"], "coin");
    assert_eq!(control["inputs"][0]["visibility"], "public");
    assert_eq!(binding["target"]["entrypoint"], "echo");

    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{name}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{name}.zkir")))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let nonce: Vec<u8> = (1..=32).collect();
    let color: Vec<u8> = (224..=255).rev().collect();
    let cases = [
        coin(&nonce, &color, "0", "0"),
        coin(
            &nonce,
            &color,
            "340282366920938463463374607431768211455",
            "18446744073709551615",
        ),
    ];
    for expected in cases {
        let mut session = wire_session(&control, expected.clone())?;
        assert_eq!(session.advance()?["status"], "completed");
        let completion = session.private_completion(&binding["nativeRelation"])?;
        let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;
        let execution = prepare(
            &plan,
            &inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )?;
        check(&execution, &circuit)?;
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([("echoed".into(), expected)])
        );
    }

    assert!(
        wire_session(
            &control,
            coin(
                &nonce,
                &color,
                "340282366920938463463374607431768211456",
                "0"
            ),
        )
        .is_err()
    );
    assert!(wire_session(&control, coin(&nonce, &color, "0", "18446744073709551616"),).is_err());
    Ok(())
}
