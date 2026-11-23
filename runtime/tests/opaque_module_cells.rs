#![cfg(feature = "zkir-321")]

use anyhow::{Result, bail, ensure};
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, construct_state, create_state, prepare, zkir::IrSource};
use onchain_runtime::state::ChargedState;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs, path::PathBuf};

const TEXT: &str = "A\0B";
const BYTES: [u8; 4] = [0, 255, 0, 1];
const TEXT_DIGEST: &str =
    "22320326593834792867740549375846381842323839331830720512622781725421649163502";
const BYTES_DIGEST: &str =
    "49167104757628121071352926025422038687503644974786430215210367604432277057487";

fn fixture(directory: &PathBuf, entry: &str) -> Result<(Plan, IrSource)> {
    let stem = format!("OpaqueModuleCells.{entry}");
    let plan = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let relation = IrSource::load(
        fs::read(directory.join(format!("{stem}.zkir")))?.as_slice(),
    )?;
    Ok((plan, relation))
}

fn state_types(plan: &Plan) -> Result<BTreeMap<String, String>> {
    let mut result = BTreeMap::new();
    for declaration in &plan.state {
        let ty = if declaration.kind.get("opaqueString") == Some(&Json::Bool(true)) {
            "OpaqueString"
        } else if let Some(ty) = declaration.kind.get("cell").and_then(Json::as_str) {
            ty
        } else {
            bail!("unexpected OpaqueModuleCells state kind for {}", declaration.name);
        };
        ensure!(
            matches!(ty, "OpaqueString" | "OpaqueBytes"),
            "unexpected OpaqueModuleCells state type {ty}"
        );
        ensure!(
            result.insert(declaration.name.clone(), ty.to_owned()).is_none(),
            "duplicate OpaqueModuleCells state name {}",
            declaration.name
        );
    }
    ensure!(result.len() == 2, "expected two imported opaque root cells");
    let mut types: Vec<_> = result.values().map(String::as_str).collect();
    types.sort_unstable();
    ensure!(
        types == vec!["OpaqueBytes", "OpaqueString"],
        "expected one OpaqueString and one OpaqueBytes root Cell"
    );
    Ok(result)
}

fn concrete_state_values(plan: &Plan) -> Result<BTreeMap<String, Json>> {
    let types = state_types(plan)?;
    plan.state
        .iter()
        .map(|declaration| {
            let value = match types[&declaration.name].as_str() {
                "OpaqueString"
                    if declaration.kind.get("opaqueString") == Some(&Json::Bool(true)) =>
                {
                    json!(TEXT)
                }
                "OpaqueString" => json!({"kind":"opaqueString", "value":TEXT}),
                "OpaqueBytes" => json!({"kind":"opaqueBytes", "values":BYTES}),
                _ => bail!("unsupported opaque state type"),
            };
            Ok((declaration.name.clone(), value))
        })
        .collect()
}

fn check_digest(
    plan: &Plan,
    relation: &IrSource,
    state: &ChargedState<noctium_runtime::Db>,
    entrypoint: &str,
    expected: &str,
) -> Result<()> {
    ensure!(plan.entrypoint == entrypoint, "wrong OpaqueModuleCells entrypoint");
    ensure!(
        plan.circuit.inputs.is_empty(),
        "opaque module hash entrypoint should not take inputs"
    );
    let execution = prepare(
        plan,
        &BTreeMap::new(),
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, relation)?, execution.activity_schedule);
    assert_eq!(execution.after.state.get_ref(), state.get_ref());
    assert_eq!(execution.returns_json().len(), 1);
    assert_eq!(execution.returns_json()["digest"], json!(expected));
    Ok(())
}

#[test]
#[ignore = "requires fresh OpaqueModuleCells artifacts in NOCTIUM_OPAQUE_MODULE_CELLS_DIR"]
fn opaque_generic_module_cells_match_concrete_state_and_compact_hashes() -> Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_OPAQUE_MODULE_CELLS_DIR")?);
    let (string_plan, string_relation) = fixture(&directory, "hashString")?;
    let (bytes_plan, bytes_relation) = fixture(&directory, "hashBytes")?;
    assert_eq!(state_types(&string_plan)?, state_types(&bytes_plan)?);

    let constructor_arguments = BTreeMap::from([
        ("initialString".into(), json!(TEXT)),
        (
            "initialBytes".into(),
            json!({"kind":"opaqueBytes", "values":BYTES}),
        ),
    ]);
    let constructed = construct_state(&string_plan, &constructor_arguments)?;
    let constructed_bytes = construct_state(&bytes_plan, &constructor_arguments)?;
    let concrete = create_state(&string_plan, &concrete_state_values(&string_plan)?)?;
    assert_eq!(constructed, concrete);
    assert_eq!(constructed_bytes, concrete);

    check_digest(
        &string_plan,
        &string_relation,
        &constructed,
        "hashString",
        TEXT_DIGEST,
    )?;
    check_digest(
        &bytes_plan,
        &bytes_relation,
        &constructed,
        "hashBytes",
        BYTES_DIGEST,
    )?;
    Ok(())
}
