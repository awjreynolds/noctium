#![cfg(feature = "zkir-321")]

use anyhow::{Context as _, Result};
use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Expr, Plan, check,
    control::{InvocationTarget, Session},
    create_state,
    host::{self, Capability, Context, Limits},
    prepare,
    zkir::IrSource,
};
use onchain_runtime::state::StateValue;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs::File, path::PathBuf};
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

#[test]
#[ignore = "requires fresh OpaqueEquality artifacts and pinned Compact output"]
fn opaque_equality_matches_compact_and_binds_the_result() -> Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_OPAQUE_EQUALITY_DIR")?);
    let compact: Json = serde_json::from_reader(File::open(std::env::var(
        "NOCTIUM_OPAQUE_EQUALITY_COMPACT",
    )?)?)?;
    let address = ContractAddress::default();
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    for (entry, family) in [("recordString", "strings"), ("recordBytes", "bytes")] {
        let stem = format!("OpaqueEquality.{entry}");
        let plan: Plan =
            serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?;
        let relation = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;
        let state = create_state(&plan, &BTreeMap::new())?;
        let cases = compact[family]
            .as_array()
            .context("missing Compact cases")?;
        for case in cases {
            let expected = case["same"].as_bool().context("missing Compact result")?;
            let inputs = BTreeMap::from(["a", "b"].map(|name| {
                let value = if family == "strings" {
                    json!({"kind":"opaqueString","value":case[name]})
                } else {
                    json!({"kind":"opaqueBytes","values":case[name]})
                };
                (name.to_owned(), value)
            }));
            let execution = prepare(&plan, &inputs, &state, parameters, address)?;
            check(&execution, &relation)?;
            assert_eq!(execution.returns_json()["same"], expected);
            let StateValue::Array(slots) = execution.after.state.get_ref() else {
                anyhow::bail!("missing ledger state");
            };
            let slot = slots.get(0).context("missing Bool Cell")?;
            let StateValue::Cell(cell) = &*slot else {
                anyhow::bail!("expected a Bool Cell");
            };
            let mut fields = Vec::new();
            cell.value_only_field_repr(&mut fields);
            assert_eq!(fields, [Fr::from(u64::from(expected))]);

            if entry == "recordBytes" {
                let control: Json = serde_json::from_reader(File::open(
                    directory.join(format!("{stem}.witness.control.json")),
                )?)?;
                let binding = control["binding"]
                    .as_str()
                    .context("missing witness binding")?;
                let pin = hex::encode(Sha256::digest(binding.as_bytes()));
                let binding: Json = serde_json::from_str(binding)?;
                let mut session = Session::from_json_with_invocation_target(
                    control,
                    inputs.clone(),
                    Context {
                        protocol_version: 1,
                        namespace: "noctium".into(),
                        base_revision: "r0".into(),
                        attempt_id: "d".repeat(64),
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
                        contract_address: hex::encode(address.0.0),
                        entrypoint: entry.into(),
                    }),
                )?;
                assert_eq!(session.advance()?["status"], "completed");
                let completion = session.private_completion(&binding["nativeRelation"])?;
                let witness_inputs = serde_json::from_value(completion["inputs"].clone())?;
                let from_witness = prepare(&plan, &witness_inputs, &state, parameters, address)?;
                check(&from_witness, &relation)?;
                assert_eq!(from_witness.returns_json()["same"], expected);
            }

            let mut altered = plan.clone();
            altered.returns[0].expression = Expr::Bool { value: !expected };
            let changed = prepare(&altered, &inputs, &state, parameters, address)?;
            assert_ne!(
                execution.preimage.communications_commitment,
                changed.preimage.communications_commitment,
            );
            assert!(check(&changed, &relation).is_err());
        }
    }
    Ok(())
}
