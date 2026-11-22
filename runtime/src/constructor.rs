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
    #[serde(default, rename = "mapInserts")]
    pub map_inserts: Vec<MapInsert>,
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
#[serde(deny_unknown_fields)]
pub struct CounterIncrement {
    pub state: String,
    pub amount: Expr,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ListPush {
    pub state: String,
    pub value: Expr,
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

type ConstructorMap = HashMap<AlignedValue, StateValue<Db>, Db>;

fn constructor_counter(decl: &StateDecl) -> bool {
    decl.kind == json!({"tree":{"counter":true}})
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
    let amount_type = ScalarType::parse("UIntRange<4294967296>")?;
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
        let amount = evaluate(&increment.amount, environment)?;
        ensure!(
            amount.scalar_type() == amount_type,
            "constructor Counter increment amount must use the native UInt32 width"
        );
        amount.validate()?;
        let Value::UInt { number, .. } = amount else {
            bail!("constructor Counter increment amount must use the native UInt32 width")
        };
        let amount = u64::try_from(number)
            .map_err(|_| anyhow!("constructor Counter amount exceeds UInt64"))?;
        let total = totals.entry(increment.state.clone()).or_default();
        *total = total
            .checked_add(amount)
            .ok_or_else(|| anyhow!("constructor Counter sum exceeds UInt64"))?;
    }
    Ok(totals)
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
        let (slot, declaration) = plan
            .state
            .iter()
            .enumerate()
            .find(|(_, declaration)| declaration.name == insert.state)
            .ok_or_else(|| anyhow!("unknown constructor Map state"))?;
        let (key_type, value_type) = flat_map_types(declaration)?
            .ok_or_else(|| anyhow!("constructor Map insert requires a flat scalar Map"))?;
        let key_value = evaluate(&insert.key, environment)?;
        ensure!(
            key_value.scalar_type() == key_type,
            "constructor Map key type mismatch"
        );
        crate::validate_ledger_key_value(&key_type, &key_value)?;
        let value = evaluate(&insert.value, environment)?;
        ensure!(
            value.scalar_type() == value_type,
            "constructor Map value type mismatch"
        );
        value.validate()?;
        let key = crate::aligned(&key_value, crate::key_alignment(&key_type))?;
        let value = crate::aligned_storage_cell(&value)?;
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
        .checked_add(constructor.counter_increments.len())
        .and_then(|count| count.checked_add(constructor.list_pushes.len()))
        .ok_or_else(|| anyhow!("too many constructor collection actions"))?;
    ensure!(
        action_count <= 64,
        "too many constructor collection actions"
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
            initialized.insert(initializer.state.as_str()),
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
    for declaration in &plan.state {
        if declaration.sealed && declaration.kind.get("map").is_none() {
            let collection_default =
                constructor_counter(declaration) || flat_scalar_list_type(declaration)?.is_some();
            if collection_default {
                continue;
            }
            cell_type(declaration)?;
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
    let state = apply_map_inserts(plan, &constructor.map_inserts, &scalars, state)?;
    apply_list_pushes(plan, &constructor.list_pushes, &scalars, state)
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
