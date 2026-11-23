//! Public constructor evaluation and immutable deployment cells.
use crate::{
    Db, Expr, Plan, ScalarType, StateDecl, Value, create_state, evaluate, input_value, scalars,
};
use anyhow::{Result, anyhow, bail, ensure};
use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue};
use onchain_runtime::state::{ChargedState, StateValue};
use serde::Deserialize;
use serde_json::{Value as Json, json};
use std::collections::{BTreeMap, BTreeSet};
use storage::{arena::Sp, storage::HashMap};

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Constructor {
    pub parameters: Vec<Parameter>,
    pub initializers: Vec<Initializer>,
    #[serde(default)]
    pub actions: Vec<ConstructorAction>,
    #[serde(default, rename = "mapInserts")]
    pub map_inserts: Vec<MapInsert>,
    #[serde(default, rename = "setInserts")]
    pub set_inserts: Vec<SetInsert>,
    #[serde(default, rename = "counterIncrements")]
    pub counter_increments: Vec<CounterIncrement>,
    #[serde(default, rename = "listPushes")]
    pub list_pushes: Vec<ListPush>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Parameter {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Initializer {
    pub state: String,
    #[serde(rename = "type")]
    pub ty: String,
    pub value: InitialValue,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MapInsert {
    pub state: String,
    pub key: Expr,
    pub value: Expr,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase", deny_unknown_fields)]
pub enum ConstructorAction {
    MapInsert {
        state: String,
        key: Expr,
        value: Expr,
        #[serde(default)]
        guard: Option<Expr>,
    },
    CounterIncrement {
        state: String,
        amount: Expr,
        #[serde(default)]
        guard: Option<Expr>,
    },
    InitializeCellFromCounter {
        state: String,
        counter: String,
    },
    InitializeCellFromMapMember {
        state: String,
        map: String,
        key: Expr,
    },
    InitializeRecordCell {
        state: String,
        fields: Vec<Expr>,
    },
    InsertRecordMap {
        state: String,
        key: Expr,
        fields: Vec<Expr>,
    },
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SetInsert {
    pub name: String,
    pub key: Expr,
    #[serde(default)]
    pub guard: Option<Expr>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CounterIncrement {
    pub state: String,
    pub amount: Expr,
    #[serde(default)]
    pub guard: Option<Expr>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ListPush {
    pub state: String,
    pub value: Expr,
    #[serde(default)]
    pub guard: Option<Expr>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase", deny_unknown_fields)]
pub enum InitialValue {
    ScalarExpression { expression: Expr },
    OpaqueStringParameter { name: String },
    OpaqueStringLiteral { value: String },
}

pub(crate) fn opaque_string(value: &Json) -> Result<AlignedValue> {
    let text = value
        .as_str()
        .ok_or_else(|| anyhow!("expected opaque UTF-8 string"))?;
    let atom = scalars::opaque_string_atom(text)?;
    AlignedValue::new(
        FabValue(vec![atom]),
        Alignment::singleton(AlignmentAtom::Compress),
    )
    .ok_or_else(|| anyhow!("invalid opaque string alignment"))
}

/// Decode a canonical UTF-8 metadata atom.
pub fn decode_opaque_string(value: &AlignedValue) -> Result<String> {
    ensure!(
        value.alignment == Alignment::singleton(AlignmentAtom::Compress)
            && value.value.0.len() == 1,
        "invalid opaque string alignment"
    );
    let atom = &value.value.0[0];
    let bytes = &atom.0;
    scalars::validate_opaque_string_atom(atom)?;
    Ok(String::from_utf8(bytes.clone())?)
}

fn cell_type(decl: &StateDecl) -> Result<&str> {
    if decl.kind.get("opaqueString") == Some(&Json::Bool(true)) {
        Ok("OpaqueString")
    } else {
        decl.kind
            .get("cell")
            .and_then(Json::as_str)
            .ok_or_else(|| anyhow!("constructor initializer must select a cell"))
    }
}

fn scalar_zero(ty: &str) -> Result<Json> {
    Ok(match ScalarType::parse(ty)? {
        ScalarType::Native | ScalarType::UInt(_) => json!("0"),
        ScalarType::Bool => json!(false),
        ScalarType::Bytes32 => json!({"kind":"bytes", "values":vec![0u8;32]}),
        ScalarType::Bytes(length) => json!({"kind":"bytes", "values":vec![0u8;length]}),
        ScalarType::OpaqueBytes => json!({"kind":"opaqueBytes", "values":Vec::<u8>::new()}),
        ScalarType::OpaqueString => {
            bail!("OpaqueString requires the dedicated opaque string state kind")
        }
        ScalarType::JubjubScalar => json!({"kind":"jubjubScalar", "value":"0"}),
        ScalarType::JubjubPoint => json!({"kind":"jubjubPoint", "x":"0", "y":"1"}),
        #[cfg(feature = "zkir-321")]
        ScalarType::Foreign(ty) => {
            let value = crate::foreign::ForeignValue::zero(ty)?;
            json!({"kind":"foreign", "type":ty.source_name(), "bytes":value.to_bytes()?})
        }
    })
}

fn default_value(decl: &StateDecl) -> Result<Json> {
    if decl.kind.get("opaqueString") == Some(&Json::Bool(true)) {
        return Ok(json!(""));
    }
    if let Some(ty) = decl.kind.get("cell").and_then(Json::as_str) {
        return scalar_zero(ty);
    }
    if let Some(schema) = decl.kind.get("tree") {
        if schema.get("counter") == Some(&Json::Bool(true)) {
            return Ok(json!("0"));
        }
        if schema.get("set").is_some() {
            return Ok(json!([]));
        }
        if let Some(ty) = schema.get("scalar").and_then(Json::as_str) {
            return scalar_zero(ty);
        }
        if let Some(record) = schema.get("composite") {
            return crate::default_record_value(record);
        }
    }
    // create_state validates collection schemas and requires these defaults to be empty.
    Ok(json!([]))
}

fn flat_map_types(decl: &StateDecl) -> Result<Option<(ScalarType, ScalarType)>> {
    let Some(types) = decl.kind.get("map").and_then(Json::as_array) else {
        if decl.kind.get("map").is_some() {
            bail!("unsupported constructor Map schema")
        }
        return Ok(None);
    };
    ensure!(types.len() == 2, "unsupported constructor Map schema");
    let key = crate::ledger_key_type(&types[0])?;
    let value = ScalarType::parse(
        types[1]
            .as_str()
            .ok_or_else(|| anyhow!("invalid constructor Map value schema"))?,
    )?;
    ensure!(
        value != ScalarType::OpaqueString,
        "OpaqueString is not supported in constructor Map values"
    );
    Ok(Some((key, value)))
}

fn root_scalar_set_type(decl: &StateDecl) -> Result<Option<ScalarType>> {
    let Some(tree) = decl.kind.get("tree") else {
        return Ok(None);
    };
    let Some(key) = tree.get("set") else {
        return Ok(None);
    };
    ensure!(
        decl.kind.as_object().is_some_and(|kind| kind.len() == 1)
            && tree.as_object().is_some_and(|fields| fields.len() == 1),
        "constructor Set insert requires a root Set"
    );
    Ok(Some(crate::ledger_key_type(key)?))
}

type ConstructorMap = HashMap<AlignedValue, StateValue<Db>, Db>;

fn constructor_counter(decl: &StateDecl) -> bool {
    decl.kind == json!({"tree":{"counter":true}})
}

fn constructor_counter_slot(plan: &Plan, name: &str) -> Result<usize> {
    let (slot, declaration) = plan
        .state
        .iter()
        .enumerate()
        .find(|(_, declaration)| declaration.name == name)
        .ok_or_else(|| anyhow!("unknown constructor Counter state"))?;
    ensure!(
        constructor_counter(declaration),
        "constructor Counter operation requires a root Counter"
    );
    Ok(slot)
}

fn constructor_counter_cell_slot(plan: &Plan, name: &str) -> Result<usize> {
    let (slot, declaration) = plan
        .state
        .iter()
        .enumerate()
        .find(|(_, declaration)| declaration.name == name)
        .ok_or_else(|| anyhow!("unknown constructor state cell"))?;
    ensure!(
        declaration.kind.as_object().is_some_and(|kind| {
            kind.len() == 1 && kind.contains_key("cell")
        }) && cell_type(declaration)? == "UIntRange<18446744073709551616>",
        "constructor Counter initializer requires a root UInt64 cell"
    );
    Ok(slot)
}

fn flat_scalar_list_type(decl: &StateDecl) -> Result<Option<ScalarType>> {
    let Some(tree) = decl.kind.get("tree") else {
        return Ok(None);
    };
    let Some(list) = tree.get("list") else {
        return Ok(None);
    };
    ensure!(
        decl.kind.as_object().is_some_and(|kind| kind.len() == 1)
            && tree.as_object().is_some_and(|fields| fields.len() == 1),
        "constructor List requires a root List state"
    );
    let element = list
        .as_object()
        .filter(|element| element.len() == 1)
        .ok_or_else(|| anyhow!("constructor List requires a scalar element"))?;
    let ty = element
        .get("scalar")
        .and_then(Json::as_str)
        .ok_or_else(|| anyhow!("constructor List requires a scalar element"))?;
    let ty = crate::validate_tree_scalar_type(ty)?;
    ensure!(
        ty != ScalarType::OpaqueString,
        "OpaqueString is not supported in constructor Lists"
    );
    Ok(Some(ty))
}

fn counter_totals(
    plan: &Plan,
    increments: &[CounterIncrement],
    environment: &BTreeMap<String, Value>,
) -> Result<BTreeMap<String, u64>> {
    let mut totals = BTreeMap::<String, u64>::new();
    for increment in increments {
        let declaration = plan
            .state
            .iter()
            .find(|declaration| declaration.name == increment.state)
            .ok_or_else(|| anyhow!("unknown constructor Counter state"))?;
        ensure!(
            constructor_counter(declaration),
            "constructor Counter increment requires a root Counter"
        );
        if !counter_increment_enabled(increment.guard.as_ref(), environment)? {
            continue;
        }
        let amount = counter_increment_amount(&increment.amount, environment)?;
        let total = totals.entry(increment.state.clone()).or_default();
        *total = total
            .checked_add(amount)
            .ok_or_else(|| anyhow!("constructor Counter sum exceeds UInt64"))?;
    }
    Ok(totals)
}

fn counter_increment_enabled(
    guard: Option<&Expr>,
    environment: &BTreeMap<String, Value>,
) -> Result<bool> {
    let Some(guard) = guard else {
        return Ok(true);
    };
    let guard = evaluate(guard, environment)?;
    ensure!(
        guard.scalar_type() == ScalarType::Bool,
        "constructor Counter increment guard must be Bool"
    );
    let Value::Bool(guard) = guard else {
        bail!("constructor Counter increment guard must be Bool")
    };
    Ok(guard)
}

fn counter_increment_amount(
    expression: &Expr,
    environment: &BTreeMap<String, Value>,
) -> Result<u64> {
    let amount_type = ScalarType::parse("UIntRange<4294967296>")?;
    let amount = evaluate(expression, environment)?;
    ensure!(
        amount.scalar_type() == amount_type,
        "constructor Counter increment amount must use the native UInt32 width"
    );
    amount.validate()?;
    let Value::UInt { number, .. } = amount else {
        bail!("constructor Counter increment amount must use the native UInt32 width")
    };
    u64::try_from(number).map_err(|_| anyhow!("constructor Counter amount exceeds UInt64"))
}

fn apply_map_inserts(
    plan: &Plan,
    inserts: &[MapInsert],
    environment: &BTreeMap<String, Value>,
    state: ChargedState<Db>,
) -> Result<ChargedState<Db>> {
    if inserts.is_empty() {
        return Ok(state);
    }
    let mut maps: BTreeMap<usize, ConstructorMap> = BTreeMap::new();
    for insert in inserts {
        let (slot, key, value) =
            evaluate_map_insert(plan, &insert.state, &insert.key, &insert.value, environment)?;
        let map = maps.entry(slot).or_insert_with(HashMap::new);
        *map = map.insert(key, StateValue::Cell(Sp::new(value)));
    }

    let StateValue::Array(slots) = state.get_ref() else {
        bail!("constructor Map state requires array storage")
    };
    let mut slots = slots.clone();
    for (slot, map) in maps {
        slots = slots
            .insert(slot, StateValue::Map(map))
            .ok_or_else(|| anyhow!("constructor Map slot is outside state"))?;
    }
    Ok(ChargedState::new(StateValue::Array(slots)))
}

fn flat_map_slot(plan: &Plan, name: &str) -> Result<(usize, ScalarType, ScalarType)> {
    let (slot, declaration) = plan
        .state
        .iter()
        .enumerate()
        .find(|(_, declaration)| declaration.name == name)
        .ok_or_else(|| anyhow!("unknown constructor Map state"))?;
    let (key_type, value_type) = flat_map_types(declaration)?
        .ok_or_else(|| anyhow!("constructor Map insert requires a flat scalar Map"))?;
    Ok((slot, key_type, value_type))
}

fn record_cell_slot(
    plan: &Plan,
    name: &str,
) -> Result<(usize, crate::CheckedRecordSchema)> {
    let (slot, declaration) = plan
        .state
        .iter()
        .enumerate()
        .find(|(_, declaration)| declaration.name == name)
        .ok_or_else(|| anyhow!("unknown constructor record Cell state"))?;
    ensure!(
        declaration
            .kind
            .as_object()
            .is_some_and(|kind| kind.len() == 1 && kind.contains_key("tree")),
        "constructor record Cell initializer requires a root record Cell"
    );
    let tree = declaration
        .kind
        .get("tree")
        .and_then(Json::as_object)
        .filter(|tree| tree.len() == 1)
        .ok_or_else(|| anyhow!("constructor record Cell initializer requires a root record Cell"))?;
    let schema = tree
        .get("composite")
        .ok_or_else(|| anyhow!("constructor record Cell initializer requires a root record Cell"))?;
    Ok((slot, crate::checked_cell_record_schema(schema)?))
}

fn record_map_slot(plan: &Plan, name: &str) -> Result<(usize, crate::CheckedRecordSchema)> {
    let (slot, declaration) = plan
        .state
        .iter()
        .enumerate()
        .find(|(_, declaration)| declaration.name == name)
        .ok_or_else(|| anyhow!("unknown constructor record Map state"))?;
    ensure!(
        declaration
            .kind
            .as_object()
            .is_some_and(|kind| kind.len() == 1 && kind.contains_key("tree")),
        "constructor record Map insert requires a root Bytes32 Map of records"
    );
    let tree = declaration
        .kind
        .get("tree")
        .and_then(Json::as_object)
        .filter(|tree| tree.len() == 1)
        .ok_or_else(|| {
            anyhow!("constructor record Map insert requires a root Bytes32 Map of records")
        })?;
    let map = tree
        .get("map")
        .and_then(Json::as_array)
        .filter(|map| map.len() == 2)
        .ok_or_else(|| {
            anyhow!("constructor record Map insert requires a root Bytes32 Map of records")
        })?;
    ensure!(
        crate::ledger_key_type(&map[0])? == ScalarType::Bytes32,
        "constructor record Map key must be Bytes32"
    );
    let record = map[1]
        .as_object()
        .filter(|value| value.len() == 1)
        .and_then(|value| value.get("composite"))
        .ok_or_else(|| anyhow!("constructor record Map value must be a record"))?;
    Ok((slot, crate::checked_typed_record_schema(record)?))
}

fn evaluate_map_insert(
    plan: &Plan,
    state: &str,
    key: &Expr,
    value: &Expr,
    environment: &BTreeMap<String, Value>,
) -> Result<(usize, AlignedValue, AlignedValue)> {
    let (slot, key_type, value_type) = flat_map_slot(plan, state)?;
    let key_value = evaluate(key, environment)?;
    ensure!(
        key_value.scalar_type() == key_type,
        "constructor Map key type mismatch"
    );
    crate::validate_ledger_key_value(&key_type, &key_value)?;
    let value = evaluate(value, environment)?;
    ensure!(
        value.scalar_type() == value_type,
        "constructor Map value type mismatch"
    );
    value.validate()?;
    Ok((
        slot,
        crate::aligned(&key_value, crate::key_alignment(&key_type))?,
        crate::aligned_storage_cell(&value)?,
    ))
}

fn validate_ordered_action_targets(
    plan: &Plan,
    actions: &[ConstructorAction],
    initialized: &mut BTreeSet<String>,
) -> Result<()> {
    for action in actions {
        match action {
            ConstructorAction::MapInsert { state, .. } => {
                flat_map_slot(plan, state)?;
            }
            ConstructorAction::CounterIncrement { state, .. } => {
                constructor_counter_slot(plan, state)?;
            }
            ConstructorAction::InitializeCellFromCounter { state, counter } => {
                constructor_counter_slot(plan, counter)?;
                constructor_counter_cell_slot(plan, state)?;
                ensure!(
                    initialized.insert(state.clone()),
                    "duplicate constructor initializer"
                );
            }
            ConstructorAction::InitializeRecordCell { state, .. } => {
                record_cell_slot(plan, state)?;
                ensure!(
                    initialized.insert(state.clone()),
                    "duplicate constructor initializer"
                );
            }
            ConstructorAction::InsertRecordMap { state, .. } => {
                record_map_slot(plan, state)?;
            }
            ConstructorAction::InitializeCellFromMapMember { state, map, .. } => {
                flat_map_slot(plan, map)?;
                let declaration = plan
                    .state
                    .iter()
                    .find(|declaration| declaration.name == *state)
                    .ok_or_else(|| anyhow!("unknown constructor state cell"))?;
                ensure!(
                    declaration.sealed
                        && declaration
                            .kind
                            .as_object()
                            .is_some_and(|kind| kind.len() == 1)
                        && declaration.kind.get("cell").and_then(Json::as_str) == Some("Bool"),
                    "constructor Map membership initializer requires a sealed Bool cell"
                );
                ensure!(
                    initialized.insert(state.clone()),
                    "duplicate constructor initializer"
                );
            }
        }
    }
    Ok(())
}

fn apply_ordered_actions(
    plan: &Plan,
    actions: &[ConstructorAction],
    environment: &BTreeMap<String, Value>,
    state: ChargedState<Db>,
) -> Result<ChargedState<Db>> {
    if actions.is_empty() {
        return Ok(state);
    }
    let StateValue::Array(root) = state.get_ref() else {
        bail!("constructor state requires array storage")
    };
    let mut slots = root.clone();
    for action in actions {
        match action {
            ConstructorAction::MapInsert {
                state: map_name,
                key,
                value,
                guard,
            } => {
                if let Some(guard) = guard {
                    let guard = evaluate(guard, environment)?;
                    ensure!(
                        guard.scalar_type() == ScalarType::Bool,
                        "constructor Map insert guard must be Bool"
                    );
                    let Value::Bool(guard) = guard else {
                        bail!("constructor Map insert guard must be Bool")
                    };
                    if !guard {
                        continue;
                    }
                }
                let (slot, key, value) =
                    evaluate_map_insert(plan, map_name, key, value, environment)?;
                let Some(StateValue::Map(map)) = slots.get(slot) else {
                    bail!("constructor Map state requires map storage")
                };
                let map = map.insert(key, StateValue::Cell(Sp::new(value)));
                slots = slots
                    .insert(slot, StateValue::Map(map))
                    .ok_or_else(|| anyhow!("constructor Map slot is outside state"))?;
            }
            ConstructorAction::CounterIncrement {
                state: counter_name,
                amount,
                guard,
            } => {
                if !counter_increment_enabled(guard.as_ref(), environment)? {
                    continue;
                }
                let amount = counter_increment_amount(amount, environment)?;

                let slot = constructor_counter_slot(plan, counter_name)?;
                let current = slots
                    .get(slot)
                    .ok_or_else(|| anyhow!("constructor Counter slot is outside state"))?;
                let current = constructor_counter_value(current)?;
                let total = current
                    .checked_add(amount)
                    .ok_or_else(|| anyhow!("constructor Counter sum exceeds UInt64"))?;
                slots = slots
                    .insert(slot, StateValue::Cell(Sp::new(AlignedValue::from(total))))
                    .ok_or_else(|| anyhow!("constructor Counter slot is outside state"))?;
            }
            ConstructorAction::InitializeCellFromCounter {
                state: cell_name,
                counter: counter_name,
            } => {
                let counter_slot = constructor_counter_slot(plan, counter_name)?;
                let counter = slots
                    .get(counter_slot)
                    .ok_or_else(|| anyhow!("constructor Counter slot is outside state"))?;
                let counter = constructor_counter_value(counter)?;
                let value = input_value(
                    "UIntRange<18446744073709551616>",
                    &json!(counter.to_string()),
                )?;
                let value = crate::aligned_storage_cell(&value)?;
                let cell_slot = constructor_counter_cell_slot(plan, cell_name)?;
                slots = slots
                    .insert(cell_slot, StateValue::Cell(Sp::new(value)))
                    .ok_or_else(|| anyhow!("constructor UInt64 Cell slot is outside state"))?;
            }
            ConstructorAction::InitializeRecordCell {
                state: cell_name,
                fields,
            } => {
                let (slot, schema) = record_cell_slot(plan, cell_name)?;
                let values = crate::record_values_from_expressions(&schema, fields, environment)?;
                let value = crate::aligned_record_value(&schema, &values)?;
                slots = slots
                    .insert(slot, StateValue::Cell(Sp::new(value)))
                    .ok_or_else(|| anyhow!("constructor record Cell slot is outside state"))?;
            }
            ConstructorAction::InsertRecordMap {
                state: map_name,
                key,
                fields,
            } => {
                let (slot, schema) = record_map_slot(plan, map_name)?;
                let key_value = evaluate(key, environment)?;
                ensure!(
                    key_value.scalar_type() == ScalarType::Bytes32,
                    "constructor record Map key type mismatch"
                );
                crate::validate_ledger_key_value(&ScalarType::Bytes32, &key_value)?;
                let key = crate::aligned(&key_value, "bytes32")?;
                let values = crate::record_values_from_expressions(&schema, fields, environment)?;
                let value = crate::aligned_record_value(&schema, &values)?;
                let Some(StateValue::Map(map)) = slots.get(slot) else {
                    bail!("constructor record Map state requires map storage")
                };
                let map = map.insert(key, StateValue::Cell(Sp::new(value)));
                slots = slots
                    .insert(slot, StateValue::Map(map))
                    .ok_or_else(|| anyhow!("constructor record Map slot is outside state"))?;
            }
            ConstructorAction::InitializeCellFromMapMember {
                state: cell_name,
                map,
                key,
            } => {
                let (map_slot, key_type, _) = flat_map_slot(plan, map)?;
                let key_value = evaluate(key, environment)?;
                ensure!(
                    key_value.scalar_type() == key_type,
                    "constructor Map key type mismatch"
                );
                crate::validate_ledger_key_value(&key_type, &key_value)?;
                let key = crate::aligned(&key_value, crate::key_alignment(&key_type))?;
                let Some(StateValue::Map(entries)) = slots.get(map_slot) else {
                    bail!("constructor Map state requires map storage")
                };
                let member = entries.get(&key).is_some();
                let value = crate::aligned_storage_cell(&Value::Bool(member))?;
                let cell_slot = plan
                    .state
                    .iter()
                    .position(|declaration| declaration.name == *cell_name)
                    .ok_or_else(|| anyhow!("unknown constructor state cell"))?;
                slots = slots
                    .insert(cell_slot, StateValue::Cell(Sp::new(value)))
                    .ok_or_else(|| anyhow!("constructor cell slot is outside state"))?;
            }
        }
    }
    Ok(ChargedState::new(StateValue::Array(slots)))
}

fn constructor_counter_value(value: &StateValue<Db>) -> Result<u64> {
    let StateValue::Cell(value) = value else {
        bail!("constructor Counter state requires cell storage")
    };
    let value = crate::decode_state_cell(
        value,
        "UIntRange<18446744073709551616>",
        "u64",
    )?;
    let Value::UInt { number, .. } = value else {
        bail!("constructor Counter state requires a UInt64 counter")
    };
    u64::try_from(number).map_err(|_| anyhow!("constructor Counter value exceeds UInt64"))
}

fn apply_set_inserts(
    plan: &Plan,
    inserts: &[SetInsert],
    environment: &BTreeMap<String, Value>,
    state: ChargedState<Db>,
) -> Result<ChargedState<Db>> {
    if inserts.is_empty() {
        return Ok(state);
    }
    let mut sets = BTreeMap::<usize, ConstructorMap>::new();
    for insert in inserts {
        let (slot, declaration) = plan
            .state
            .iter()
            .enumerate()
            .find(|(_, declaration)| declaration.name == insert.name)
            .ok_or_else(|| anyhow!("unknown constructor Set state"))?;
        let key_type = root_scalar_set_type(declaration)?
            .ok_or_else(|| anyhow!("constructor Set insert requires a root scalar Set"))?;

        if let Some(guard) = &insert.guard {
            let Value::Bool(guard) = evaluate(guard, environment)? else {
                bail!("constructor Set insert guard must be Bool")
            };
            if !guard {
                continue;
            }
        }

        let key_value = evaluate(&insert.key, environment)?;
        ensure!(
            key_value.scalar_type() == key_type,
            "constructor Set key type mismatch"
        );
        crate::validate_ledger_key_value(&key_type, &key_value)?;
        let key = crate::aligned(&key_value, crate::key_alignment(&key_type))?;
        let set = sets.entry(slot).or_insert_with(HashMap::new);
        *set = set.insert(key, StateValue::Null);
    }

    let StateValue::Array(slots) = state.get_ref() else {
        bail!("constructor Set state requires array storage")
    };
    let mut slots = slots.clone();
    for (slot, set) in sets {
        slots = slots
            .insert(slot, StateValue::Map(set))
            .ok_or_else(|| anyhow!("constructor Set slot is outside state"))?;
    }
    Ok(ChargedState::new(StateValue::Array(slots)))
}

fn apply_list_pushes(
    plan: &Plan,
    pushes: &[ListPush],
    environment: &BTreeMap<String, Value>,
    state: ChargedState<Db>,
) -> Result<ChargedState<Db>> {
    if pushes.is_empty() {
        return Ok(state);
    }
    let StateValue::Array(state_slots) = state.get_ref() else {
        bail!("constructor List state requires array storage")
    };
    let mut slots = state_slots.clone();
    let mut lengths = BTreeMap::<usize, u64>::new();
    for push in pushes {
        let (slot, declaration) = plan
            .state
            .iter()
            .enumerate()
            .find(|(_, declaration)| declaration.name == push.state)
            .ok_or_else(|| anyhow!("unknown constructor List state"))?;
        let element_type = flat_scalar_list_type(declaration)?
            .ok_or_else(|| anyhow!("constructor List push requires a flat scalar List"))?;
        if let Some(guard) = &push.guard {
            let guard = evaluate(guard, environment)?;
            ensure!(
                guard.scalar_type() == ScalarType::Bool,
                "constructor List push guard must be Bool"
            );
            let Value::Bool(guard) = guard else {
                bail!("constructor List push guard must be Bool")
            };
            if !guard {
                continue;
            }
        }
        let value = evaluate(&push.value, environment)?;
        ensure!(
            value.scalar_type() == element_type,
            "constructor List value type mismatch"
        );
        value.validate()?;
        let head = crate::aligned_storage_cell(&value)?;
        let length = lengths.entry(slot).or_default();
        *length = length
            .checked_add(1)
            .ok_or_else(|| anyhow!("constructor List length exceeds UInt64"))?;
        let previous = slots
            .get(slot)
            .ok_or_else(|| anyhow!("constructor List slot is outside state"))?
            .clone();
        let list = StateValue::Array(
            vec![
                StateValue::Cell(Sp::new(head)),
                previous,
                StateValue::Cell(Sp::new(AlignedValue::from(*length))),
            ]
            .into(),
        );
        slots = slots
            .insert(slot, list)
            .ok_or_else(|| anyhow!("constructor List slot is outside state"))?;
    }
    Ok(ChargedState::new(StateValue::Array(slots)))
}

/// Build fresh genesis from the artifact's public constructor arguments.
/// This evaluates source initialization off chain; the ledger has no constructor proof.
pub fn construct_state(
    plan: &Plan,
    arguments: &BTreeMap<String, Json>,
) -> Result<ChargedState<Db>> {
    let constructor = plan
        .constructor
        .as_ref()
        .ok_or_else(|| anyhow!("artifact has no constructor"))?;
    ensure!(plan.state.len() <= 16, "state array exceeds native limit");
    ensure!(
        constructor.parameters.len() <= 64,
        "too many constructor parameters"
    );
    ensure!(
        constructor.initializers.len() <= plan.state.len(),
        "too many constructor initializers"
    );
    let action_count = constructor
        .map_inserts
        .len()
        .checked_add(constructor.actions.len())
        .and_then(|count| count.checked_add(constructor.counter_increments.len()))
        .and_then(|count| count.checked_add(constructor.list_pushes.len()))
        .and_then(|count| count.checked_add(constructor.set_inserts.len()))
        .ok_or_else(|| anyhow!("too many constructor collection actions"))?;
    ensure!(
        action_count <= 64,
        "too many constructor collection actions"
    );
    ensure!(
        constructor.actions.is_empty() || constructor.map_inserts.is_empty(),
        "ordered constructor actions cannot be mixed with legacy Map inserts"
    );
    let ordered_counter_actions = constructor.actions.iter().any(|action| {
        matches!(
            action,
            ConstructorAction::CounterIncrement { .. }
                | ConstructorAction::InitializeCellFromCounter { .. }
        )
    });
    ensure!(
        constructor.counter_increments.is_empty() || !ordered_counter_actions,
        "ordered constructor Counter actions cannot be mixed with legacy Counter increments"
    );
    for declaration in &plan.state {
        if declaration.kind.get("map").is_some() {
            ensure!(
                flat_map_types(declaration)?.is_some(),
                "unsupported constructor Map schema"
            );
        }
    }
    let mut expected = BTreeSet::new();
    let mut scalars = BTreeMap::new();
    let mut strings = BTreeMap::new();
    let mut string_bytes = 0usize;
    for parameter in &constructor.parameters {
        ensure!(
            !parameter.name.is_empty() && expected.insert(parameter.name.as_str()),
            "invalid or duplicate constructor parameter"
        );
        let value = arguments
            .get(&parameter.name)
            .ok_or_else(|| anyhow!("missing constructor argument"))?;
        if parameter.ty == "OpaqueString" {
            let text = value
                .as_str()
                .ok_or_else(|| anyhow!("expected opaque UTF-8 string"))?;
            string_bytes = string_bytes
                .checked_add(text.len())
                .ok_or_else(|| anyhow!("constructor byte size overflow"))?;
            ensure!(
                string_bytes <= scalars::MAX_OPAQUE_STRING_LENGTH,
                "constructor string byte limit"
            );
            strings.insert(parameter.name.as_str(), value);
        } else {
            scalars.insert(parameter.name.clone(), input_value(&parameter.ty, value)?);
        }
    }
    ensure!(
        arguments.len() == expected.len()
            && arguments
                .keys()
                .all(|name| expected.contains(name.as_str())),
        "constructor argument schema mismatch"
    );
    let mut config = BTreeMap::new();
    for declaration in &plan.state {
        ensure!(
            !declaration.name.is_empty() && !config.contains_key(&declaration.name),
            "invalid or duplicate state name"
        );
        config.insert(declaration.name.clone(), default_value(declaration)?);
    }
    let mut initialized = BTreeSet::new();
    for initializer in &constructor.initializers {
        ensure!(
            initialized.insert(initializer.state.clone()),
            "duplicate constructor initializer"
        );
        let declaration = plan
            .state
            .iter()
            .find(|decl| decl.name == initializer.state)
            .ok_or_else(|| anyhow!("unknown constructor state cell"))?;
        ensure!(
            cell_type(declaration)? == initializer.ty,
            "constructor initializer type mismatch"
        );
        let value = match &initializer.value {
            InitialValue::ScalarExpression { expression } => {
                ensure!(
                    initializer.ty != "OpaqueString",
                    "opaque string requires typed initializer"
                );
                let value = evaluate(expression, &scalars)?;
                ensure!(
                    value.scalar_type() == ScalarType::parse(&initializer.ty)?,
                    "constructor scalar expression type mismatch"
                );
                value.validate()?;
                value.public_json()
            }
            InitialValue::OpaqueStringParameter { name } => {
                ensure!(
                    initializer.ty == "OpaqueString",
                    "string initializer type mismatch"
                );
                (*strings
                    .get(name.as_str())
                    .ok_or_else(|| anyhow!("unknown opaque string parameter"))?)
                .clone()
            }
            InitialValue::OpaqueStringLiteral { value } => {
                ensure!(
                    initializer.ty == "OpaqueString",
                    "string initializer type mismatch"
                );
                json!(value)
            }
        };
        config.insert(initializer.state.clone(), value);
    }
    validate_ordered_action_targets(plan, &constructor.actions, &mut initialized)?;
    for declaration in &plan.state {
        if declaration.sealed && declaration.kind.get("map").is_none() {
            let collection_default = constructor_counter(declaration)
                || flat_scalar_list_type(declaration)?.is_some()
                || root_scalar_set_type(declaration)?.is_some();
            if collection_default {
                continue;
            }
            if declaration
                .kind
                .get("tree")
                .and_then(|tree| tree.get("composite"))
                .is_some()
            {
                record_cell_slot(plan, &declaration.name)?;
            } else {
                cell_type(declaration)?;
            }
            ensure!(
                initialized.contains(declaration.name.as_str()),
                "sealed cell lacks constructor initialization"
            );
        }
    }
    let counter_totals = counter_totals(plan, &constructor.counter_increments, &scalars)?;
    for (state, total) in counter_totals {
        config.insert(state, json!(total.to_string()));
    }
    let state = create_state(plan, &config)?;
    let state = if constructor.actions.is_empty() {
        apply_map_inserts(plan, &constructor.map_inserts, &scalars, state)?
    } else {
        apply_ordered_actions(plan, &constructor.actions, &scalars, state)?
    };
    let state = apply_list_pushes(plan, &constructor.list_pushes, &scalars, state)?;
    apply_set_inserts(plan, &constructor.set_inserts, &scalars, state)
}

pub(crate) fn deployment_state(
    plan: &Plan,
    config: &BTreeMap<String, Json>,
) -> Result<ChargedState<Db>> {
    if plan.constructor.is_some() {
        construct_state(plan, config)
    } else {
        create_state(plan, config)
    }
}

pub(crate) fn check_sealed_state(
    plan: &Plan,
    before: &ChargedState<Db>,
    after: &ChargedState<Db>,
) -> Result<()> {
    if !plan.state.iter().any(|decl| decl.sealed) {
        return Ok(());
    }
    let (StateValue::Array(before), StateValue::Array(after)) = (before.get_ref(), after.get_ref())
    else {
        bail!("sealed state requires array storage")
    };
    for (slot, declaration) in plan.state.iter().enumerate() {
        if declaration.sealed {
            ensure!(
                before.get(slot).is_some() && before.get(slot) == after.get(slot),
                "entrypoint changed sealed state cell"
            );
        }
    }
    Ok(())
}
