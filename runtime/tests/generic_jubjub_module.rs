#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, Value, check, create_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};
use transient_crypto::curve::{EmbeddedFr, EmbeddedGroupAffine};

#[test]
#[ignore = "requires fresh module artifacts in NOCTIUM_GENERIC_JUBJUB_MODULE_DIR"]
fn generic_module_specializations_roundtrip_jubjub_scalar_and_point() -> anyhow::Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_GENERIC_JUBJUB_MODULE_DIR")?);
    for (entrypoint, cell_type, expected) in [
        ("scalarIdentity", "JubjubScalar", Value::JubjubScalar(EmbeddedFr::from(37u64))),
        ("pointIdentity", "JubjubPoint", Value::JubjubPoint(EmbeddedGroupAffine::generator())),
    ] {
        let stem = format!("JubjubGenericIdentity.{entrypoint}");
        let plan: Plan = serde_json::from_reader(File::open(
            directory.join(format!("{stem}.impact.json")),
        )?)?;
        let circuit = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;
        assert_eq!(plan.entrypoint, entrypoint);
        assert_eq!(plan.circuit.inputs.len(), 1);
        assert_eq!(plan.circuit.inputs[0].name, "value");
        assert_eq!(plan.circuit.inputs[0].ty, cell_type);

        let mut state_config = BTreeMap::new();
        let mut result_cell = None;
        for declaration in &plan.state {
            let ty = declaration.kind["cell"].as_str();
            let value = match ty {
                Some("JubjubScalar") => json!({"kind":"jubjubScalar", "value":"0"}),
                Some("JubjubPoint") => json!({"kind":"jubjubPoint", "x":"0", "y":"1"}),
                _ => anyhow::bail!("unexpected Jubjub fixture state type"),
            };
            state_config.insert(declaration.name.clone(), value);
            if ty == Some(cell_type) {
                result_cell = Some(declaration.name.clone());
            }
        }
        let initial = create_state(&plan, &state_config)?;
        let expected_value = expected.public_json();
        let execution = prepare(
            &plan,
            &BTreeMap::from([("value".into(), expected_value.clone())]),
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )?;
        check(&execution, &circuit)?;
        assert_eq!(execution.returns_json()["result"], expected_value);
        state_config.insert(result_cell.expect("specialized result cell"), expected_value);
        assert_eq!(execution.after.state, create_state(&plan, &state_config)?);
    }
    Ok(())
}
