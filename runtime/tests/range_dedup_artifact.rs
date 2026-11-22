#![cfg(feature = "zkir-321")]

use noctium_runtime::{Instruction, Plan};
use serde_json::Value;

const DEFAULT_IMPACT: &str =
    include_str!("../../tests/fixtures/range-dedup/default.impact.json");
const DEDUPLICATED_IMPACT: &str =
    include_str!("../../tests/fixtures/range-dedup/deduplicated.impact.json");

fn plan(json: &str) -> Plan {
    serde_json::from_str(json).expect("typed Impact Plan decodes")
}

fn operation_order(plan: &Plan) -> Vec<&'static str> {
    plan.operations
        .iter()
        .map(|operation| match operation {
            Instruction::Push { .. } => "push",
            Instruction::Popeq { .. } => "popeq",
            _ => "other",
        })
        .collect()
}

#[test]
fn exact_impact_plans_decode_and_retain_operation_order() {
    assert_eq!(DEFAULT_IMPACT.as_bytes(), DEDUPLICATED_IMPACT.as_bytes());

    let default = plan(DEFAULT_IMPACT);
    let deduplicated = plan(DEDUPLICATED_IMPACT);
    assert_eq!(default.schema_version, 1);
    assert_eq!(default.entrypoint, "echo");
    assert_eq!(operation_order(&default), ["push", "popeq", "push", "popeq"]);
    assert_eq!(operation_order(&deduplicated), operation_order(&default));

    let mut reordered: Value = serde_json::from_str(DEFAULT_IMPACT).unwrap();
    let operations = reordered["operations"].as_array_mut().unwrap();
    operations.swap(0, 1);
    let reordered = plan(&reordered.to_string());
    assert_eq!(operation_order(&reordered), ["popeq", "push", "push", "popeq"]);
    assert_ne!(operation_order(&reordered), operation_order(&default));
}
