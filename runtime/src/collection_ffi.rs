//! Bounded native ABI for collection pages and paths in a pinned state snapshot.
use crate::{
    Db, ScalarType, StateDecl, Value,
    aggregates::Schema,
    artifacts,
    merkle::{
        MerkleTreeSnapshot, merkle_curve_leaf_hash, merkle_fab_leaf_hash, merkle_tree_at,
        merkle_tree_at_node, typed_state_path,
    },
    native_ffi::{self, INTERNAL, INVALID_ARGUMENT, LIMIT, MAX_BYTES, Work},
};
use base_crypto::fab::AlignedValue;
use onchain_runtime::state::{ContractState, StateValue};
use serde::Deserialize;
use serde_json::{Value as Json, json};
use serialize::{tagged_deserialize, tagged_serialize};
use storage::arena::Sp;
use transient_crypto::merkle_tree::{MerklePathEntry, leaf_hash};

const MAX_REQUEST_BYTES: usize = 65_536;
const MAX_KEYS: usize = 12;
const MAX_OFFSET: usize = 1_048_576;
const MAX_PAGE_SIZE: usize = 64;
const MAX_ROOT_WIDTH: usize = 16;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Request {
    abi_version: u32,
    plan_sha256: String,
    state_sha256: String,
    name: String,
    keys: Vec<Key>,
    #[serde(default, deserialize_with = "present")]
    offset: Option<usize>,
    #[serde(default, deserialize_with = "present")]
    limit: Option<usize>,
    #[serde(default, deserialize_with = "present")]
    merkle_path: Option<MerklePathRequest>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct MerklePathRequest {
    leaf: MerkleLeaf,
    #[serde(default, deserialize_with = "present")]
    index: Option<String>,
}

#[derive(Deserialize)]
#[serde(
    tag = "kind",
    rename_all = "camelCase",
    rename_all_fields = "camelCase",
    deny_unknown_fields
)]
enum MerkleLeaf {
    Field {
        value: String,
    },
    Structured {
        schema_json: String,
        value_json: String,
    },
    JubjubScalar {
        value: String,
    },
    JubjubPoint {
        x: String,
        y: String,
    },
    #[cfg(feature = "zkir-321")]
    Foreign {
        #[serde(rename = "type")]
        ty: String,
        bytes: Vec<u8>,
    },
    Fab {
        value: AlignedValue,
    },
    Prehashed {
        value: [u8; 32],
    },
}

fn present<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de>,
{
    T::deserialize(deserializer).map(Some)
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Key {
    #[serde(rename = "type")]
    ty: String,
    value: Json,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct CounterRequest {
    abi_version: u32,
    plan_sha256: String,
    state_sha256: String,
    name: String,
    keys: Vec<CounterKey>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CounterKey {
    #[serde(rename = "type")]
    ty: String,
    value: Json,
}

// A read needs only the state declarations, even if the plan uses newer execution opcodes.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct ReadPlan {
    schema_version: u32,
    target: Option<String>,
    target_profile: Option<Json>,
    state: Vec<StateDecl>,
}

fn valid_digest(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn decode_state(bytes: &[u8]) -> Result<ContractState<Db>, i32> {
    let state: ContractState<Db> = tagged_deserialize(bytes).map_err(|_| INVALID_ARGUMENT)?;
    let mut canonical = Vec::new();
    tagged_serialize(&state, &mut canonical).map_err(|_| INTERNAL)?;
    if canonical != bytes {
        return Err(INVALID_ARGUMENT);
    }
    Ok(state)
}

struct AdmittedSnapshot {
    plan: ReadPlan,
    state: ContractState<Db>,
    keys: Vec<Value>,
}

fn admit_snapshot<'a>(
    plan_bytes: &[u8],
    snapshot_bytes: &[u8],
    plan_sha256: &str,
    state_sha256: &str,
    keys: impl Iterator<Item = (&'a str, &'a Json)>,
) -> Result<AdmittedSnapshot, i32> {
    if artifacts::digest(plan_bytes) != plan_sha256
        || artifacts::digest(snapshot_bytes) != state_sha256
    {
        return Err(INVALID_ARGUMENT);
    }

    let plan: ReadPlan = serde_json::from_slice(plan_bytes).map_err(|_| INVALID_ARGUMENT)?;
    if plan.schema_version != 1
        || !crate::profile::validate_plan(plan.target.as_deref(), plan.target_profile.as_ref())
    {
        return Err(INVALID_ARGUMENT);
    }
    if plan.state.len() > MAX_ROOT_WIDTH {
        return Err(LIMIT);
    }

    let keys = keys
        .map(|(ty, value)| crate::input_value(ty, value).map_err(|_| INVALID_ARGUMENT))
        .collect::<Result<Vec<_>, _>>()?;
    let state = decode_state(snapshot_bytes)?;
    let StateValue::Array(root) = state.data.get_ref() else {
        return Err(INVALID_ARGUMENT);
    };
    if root.len() > MAX_ROOT_WIDTH {
        return Err(LIMIT);
    }
    if root.len() != plan.state.len() {
        return Err(INVALID_ARGUMENT);
    }

    Ok(AdmittedSnapshot { plan, state, keys })
}

fn counter_value(node: &StateValue<Db>) -> Result<u64, i32> {
    let StateValue::Cell(value) = node else {
        return Err(INVALID_ARGUMENT);
    };
    let Value::UInt { number, .. } =
        crate::decode_state_cell(value, "UIntRange<18446744073709551616>", "u64")
            .map_err(|_| INVALID_ARGUMENT)?
    else {
        return Err(INVALID_ARGUMENT);
    };
    u64::try_from(number).map_err(|_| INVALID_ARGUMENT)
}

fn canonical_index(value: &str) -> Result<u64, i32> {
    let index = value.parse::<u64>().map_err(|_| INVALID_ARGUMENT)?;
    if index.to_string() != value {
        return Err(INVALID_ARGUMENT);
    }
    Ok(index)
}

fn merkle_leaf_hash(leaf: &MerkleLeaf) -> Result<[u8; 32], i32> {
    match leaf {
        MerkleLeaf::Field { value } => {
            let field = crate::canonical_field(value).map_err(|_| INVALID_ARGUMENT)?;
            Ok(leaf_hash(&field).0)
        }
        MerkleLeaf::Structured {
            schema_json,
            value_json,
        } => {
            let schema = Schema::from_json(schema_json.as_bytes()).map_err(|_| INVALID_ARGUMENT)?;
            schema
                .merkle_leaf_hash(value_json.as_bytes())
                .map_err(|_| INVALID_ARGUMENT)
        }
        MerkleLeaf::JubjubScalar { value } => {
            let value = crate::jubjub::scalar(value).map_err(|_| INVALID_ARGUMENT)?;
            merkle_curve_leaf_hash(&crate::Value::JubjubScalar(value)).map_err(|_| INVALID_ARGUMENT)
        }
        MerkleLeaf::JubjubPoint { x, y } => {
            let x = crate::canonical_field(x).map_err(|_| INVALID_ARGUMENT)?;
            let y = crate::canonical_field(y).map_err(|_| INVALID_ARGUMENT)?;
            let value = crate::jubjub::point(x, y).map_err(|_| INVALID_ARGUMENT)?;
            merkle_curve_leaf_hash(&crate::Value::JubjubPoint(value)).map_err(|_| INVALID_ARGUMENT)
        }
        #[cfg(feature = "zkir-321")]
        MerkleLeaf::Foreign { ty, bytes } => {
            let ty =
                crate::foreign::ForeignType::parse_source_name(ty).map_err(|_| INVALID_ARGUMENT)?;
            let value = crate::foreign::ForeignValue::from_bytes(ty, bytes)
                .map_err(|_| INVALID_ARGUMENT)?;
            merkle_curve_leaf_hash(&crate::Value::Foreign(value)).map_err(|_| INVALID_ARGUMENT)
        }
        MerkleLeaf::Fab { value } => {
            merkle_fab_leaf_hash(value.clone()).map_err(|_| INVALID_ARGUMENT)
        }
        MerkleLeaf::Prehashed { value } => Ok(*value),
    }
}

fn path_steps(entries: &[MerklePathEntry]) -> Vec<Json> {
    entries
        .iter()
        .map(|entry| {
            serde_json::json!({
                "sibling": crate::field_decimal(entry.sibling.0),
                "goesLeft": entry.goes_left
            })
        })
        .collect()
}

fn merkle_path_result(
    snapshot: &MerkleTreeSnapshot,
    query: &MerklePathRequest,
) -> Result<Json, i32> {
    let view = snapshot.view().map_err(|_| INVALID_ARGUMENT)?;
    let hash = merkle_leaf_hash(&query.leaf)?;
    let (candidate_root, steps) = match query.index.as_deref() {
        Some(index) => {
            let path = snapshot
                .indexed_prehashed_path(canonical_index(index)?, hash)
                .map_err(|_| INVALID_ARGUMENT)?;
            (
                Some(crate::field_decimal(path.candidate_root)),
                Some(path_steps(&path.entries)),
            )
        }
        None => {
            let path = snapshot
                .find_prehashed_path(hash)
                .map_err(|_| INVALID_ARGUMENT)?;
            match path {
                Some(path) => (
                    Some(crate::field_decimal(path.root())),
                    Some(path_steps(path.entries())),
                ),
                None => (None, None),
            }
        }
    };
    Ok(serde_json::json!({
        "abiVersion": 1,
        "kind": "merklePath",
        "snapshotRoot": crate::field_decimal(view.root),
        "candidateRoot": candidate_root,
        "steps": steps
    }))
}

fn merkle_page(tree: &MerkleTreeSnapshot, offset: usize, limit: usize) -> Result<Json, i32> {
    let view = tree.view().map_err(|_| INVALID_ARGUMENT)?;
    let mut entries = Vec::new();
    let mut next_offset = None;
    let kind = if tree.is_historic() {
        let mut roots = tree.historic_roots().map_err(|_| INVALID_ARGUMENT)?;
        for _ in 0..offset {
            if roots
                .next()
                .transpose()
                .map_err(|_| INVALID_ARGUMENT)?
                .is_none()
            {
                break;
            }
        }
        for root in roots.by_ref().take(limit) {
            entries.push(crate::field_decimal(root.map_err(|_| INVALID_ARGUMENT)?));
        }
        if roots
            .next()
            .transpose()
            .map_err(|_| INVALID_ARGUMENT)?
            .is_some()
        {
            next_offset = Some(offset + entries.len());
        }
        "historicMerkleTree"
    } else {
        "merkleTree"
    };
    Ok(json!({
        "abiVersion": 1,
        "kind": kind,
        "root": crate::field_decimal(view.root),
        "firstFree": view.first_free.to_string(),
        "entries": entries,
        "nextOffset": next_offset
    }))
}

enum CollectionValueSchema {
    Scalar { ty: ScalarType, name: String },
    Record(crate::CheckedRecordSchema),
}

enum CollectionSchema {
    Map {
        key: CollectionValueSchema,
        value: CollectionValueSchema,
    },
    Set {
        key: CollectionValueSchema,
    },
    List {
        element: CollectionValueSchema,
    },
}

fn collection_schema(schema: &Json) -> Result<Option<CollectionSchema>, i32> {
    if let Some(set) = schema.get("set") {
        let key = if let Some(key_name) = set.as_str() {
            let key_name = key_name.to_owned();
            let ty = crate::ledger_key_type(&Json::String(key_name.clone()))
                .map_err(|_| INVALID_ARGUMENT)?;
            CollectionValueSchema::Scalar { ty, name: key_name }
        } else {
            let record = set
                .as_object()
                .filter(|fields| fields.len() == 1)
                .and_then(|fields| fields.get("composite"))
                .ok_or(INVALID_ARGUMENT)?;
            if !crate::is_shielded_coin_record_schema(record) {
                return Err(INVALID_ARGUMENT);
            }
            CollectionValueSchema::Record(
                crate::checked_record_schema(record).map_err(|_| INVALID_ARGUMENT)?,
            )
        };
        return Ok(Some(CollectionSchema::Set { key }));
    }
    if let Some(map) = schema.get("map") {
        let fields = map
            .as_array()
            .filter(|fields| fields.len() == 2)
            .ok_or(INVALID_ARGUMENT)?;
        let key = if let Some(key_name) = fields[0].as_str() {
            let key_name = key_name.to_owned();
            let ty = crate::ledger_key_type(&Json::String(key_name.clone()))
                .map_err(|_| INVALID_ARGUMENT)?;
            CollectionValueSchema::Scalar { ty, name: key_name }
        } else {
            let record = crate::ordinary_record_key_schema(&fields[0]).ok_or(INVALID_ARGUMENT)?;
            let schema =
                crate::checked_typed_record_schema(record).map_err(|_| INVALID_ARGUMENT)?;
            if schema
                .fields
                .iter()
                .any(|field| field.ty == ScalarType::JubjubPoint)
            {
                return Err(INVALID_ARGUMENT);
            }
            CollectionValueSchema::Record(schema)
        };
        let value = if let Some(name) = fields[1].as_str() {
            CollectionValueSchema::Scalar {
                ty: ScalarType::parse(name).map_err(|_| INVALID_ARGUMENT)?,
                name: name.to_owned(),
            }
        } else {
            let descriptor = fields[1]
                .as_object()
                .filter(|fields| fields.len() == 1)
                .ok_or(INVALID_ARGUMENT)?;
            if let Some(name) = descriptor.get("scalar").and_then(Json::as_str) {
                CollectionValueSchema::Scalar {
                    ty: crate::validate_tree_scalar_type(name).map_err(|_| INVALID_ARGUMENT)?,
                    name: name.to_owned(),
                }
            } else {
                let record = descriptor.get("composite").ok_or(INVALID_ARGUMENT)?;
                CollectionValueSchema::Record(
                    crate::checked_record_schema(record).map_err(|_| INVALID_ARGUMENT)?,
                )
            }
        };
        return Ok(Some(CollectionSchema::Map { key, value }));
    }
    if let Some(list) = schema.get("list") {
        let element = list
            .as_object()
            .filter(|fields| fields.len() == 1)
            .ok_or(INVALID_ARGUMENT)?;
        let element = if let Some(name) = element.get("scalar").and_then(Json::as_str) {
            CollectionValueSchema::Scalar {
                ty: crate::validate_tree_scalar_type(name).map_err(|_| INVALID_ARGUMENT)?,
                name: name.to_owned(),
            }
        } else {
            let record = element.get("composite").ok_or(INVALID_ARGUMENT)?;
            CollectionValueSchema::Record(
                crate::checked_record_schema(record).map_err(|_| INVALID_ARGUMENT)?,
            )
        };
        return Ok(Some(CollectionSchema::List { element }));
    }
    Ok(None)
}

fn validate_collection_value(
    value: &AlignedValue,
    schema: &CollectionValueSchema,
) -> Result<(), i32> {
    match schema {
        CollectionValueSchema::Scalar { ty, name } => {
            crate::decode_state_cell(value, name, &crate::scalar_storage_alignment(ty))
                .map(|_| ())
                .map_err(|_| INVALID_ARGUMENT)
        }
        CollectionValueSchema::Record(schema) => {
            let values = crate::decode_record_value(schema, value).map_err(|_| INVALID_ARGUMENT)?;
            if schema.aggregate.is_some() {
                record_values_json(schema, &values)?;
            }
            Ok(())
        }
    }
}

fn collection_value_json(
    value: &AlignedValue,
    schema: &CollectionValueSchema,
) -> Result<Json, i32> {
    match schema {
        CollectionValueSchema::Scalar { ty, name } => {
            crate::decode_state_cell(value, name, &crate::scalar_storage_alignment(ty))
                .map(|value| value.public_json())
                .map_err(|_| INVALID_ARGUMENT)
        }
        CollectionValueSchema::Record(record_schema) => {
            let values =
                crate::decode_record_value(record_schema, value).map_err(|_| INVALID_ARGUMENT)?;
            record_values_json(record_schema, &values)
        }
    }
}

fn record_values_json(schema: &crate::CheckedRecordSchema, values: &[Value]) -> Result<Json, i32> {
    if let Some(aggregate) = &schema.aggregate {
        let leaves = values
            .iter()
            .map(|value| match value {
                Value::Native(field) => Ok(Json::String(crate::field_decimal(*field))),
                _ => Err(INVALID_ARGUMENT),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let rendered = aggregate
            .from_native_leaves_json(&leaves)
            .map_err(|_| INVALID_ARGUMENT)?;
        return serde_json::from_slice(&rendered).map_err(|_| INVALID_ARGUMENT);
    }

    let fields = schema
        .fields
        .iter()
        .zip(values)
        .map(|(field, value)| {
            Ok((
                field.name.clone().ok_or(INVALID_ARGUMENT)?,
                value.public_json(),
            ))
        })
        .collect::<Result<serde_json::Map<_, _>, i32>>()?;
    Ok(Json::Object(fields))
}

fn key_order(value: &Value) -> Result<Vec<u8>, i32> {
    match value {
        Value::Native(field) => {
            let mut bytes = field.as_le_bytes().to_vec();
            bytes.reverse();
            Ok(bytes)
        }
        Value::Bool(value) => Ok(vec![u8::from(*value)]),
        Value::UInt { number, .. } => {
            let bytes = number.to_bytes_be();
            if bytes.len() > 32 {
                return Err(INVALID_ARGUMENT);
            }
            let mut padded = vec![0; 32 - bytes.len()];
            padded.extend(bytes);
            Ok(padded)
        }
        Value::Bytes(bytes) => Ok(bytes.clone()),
        #[cfg(feature = "zkir-321")]
        Value::Foreign(value) => value.to_bytes().map_err(|_| INVALID_ARGUMENT),
        Value::OpaqueBytes(_)
        | Value::OpaqueString(_)
        | Value::JubjubScalar(_)
        | Value::JubjubPoint(_) => Err(INVALID_ARGUMENT),
    }
}

fn qualified_coin_key_order(values: &[Value]) -> Result<Vec<u8>, i32> {
    let [
        Value::Bytes(nonce),
        Value::Bytes(color),
        Value::UInt { number, .. },
        Value::UInt {
            number: mt_index, ..
        },
    ] = values
    else {
        return Err(INVALID_ARGUMENT);
    };
    if nonce.len() != 32 || color.len() != 32 {
        return Err(INVALID_ARGUMENT);
    }
    let mut order = Vec::with_capacity(88);
    order.extend_from_slice(nonce);
    order.extend_from_slice(color);
    let number = u128::try_from(number.clone()).map_err(|_| INVALID_ARGUMENT)?;
    let mt_index = u64::try_from(mt_index.clone()).map_err(|_| INVALID_ARGUMENT)?;
    order.extend_from_slice(&number.to_be_bytes());
    order.extend_from_slice(&mt_index.to_be_bytes());
    Ok(order)
}

struct OrderedEntry {
    order: Vec<u8>,
    key: Json,
    value: Option<Sp<AlignedValue>>,
}

fn collection_page(
    state: &StateValue<Db>,
    schema: &CollectionSchema,
    offset: usize,
    limit: usize,
) -> Result<Json, i32> {
    let StateValue::Map(map) = state else {
        return Err(INVALID_ARGUMENT);
    };
    let map_size = usize::try_from(map.size()).map_err(|_| INVALID_ARGUMENT)?;
    let mut entries = Vec::with_capacity(map_size);
    for entry in map.iter() {
        let (key, value) = &*entry;
        let (order, key) = match schema {
            CollectionSchema::Map {
                key: CollectionValueSchema::Scalar { ty, name },
                ..
            }
            | CollectionSchema::Set {
                key: CollectionValueSchema::Scalar { ty, name },
            } => {
                let key = crate::decode_state_cell(key, name, crate::key_alignment(ty))
                    .map_err(|_| INVALID_ARGUMENT)?;
                let order = key_order(&key)?;
                (order, key.public_json())
            }
            CollectionSchema::Map {
                key: CollectionValueSchema::Record(record_schema),
                ..
            } => {
                let values =
                    crate::decode_record_value(record_schema, key).map_err(|_| INVALID_ARGUMENT)?;
                let mut order = Vec::new();
                for value in &values {
                    order.extend(key_order(value)?);
                }
                let key = record_values_json(record_schema, &values)?;
                (order, key)
            }
            CollectionSchema::Set {
                key: CollectionValueSchema::Record(record_schema),
            } => {
                let values =
                    crate::decode_record_value(record_schema, key).map_err(|_| INVALID_ARGUMENT)?;
                let order = qualified_coin_key_order(&values)?;
                let key = record_values_json(record_schema, &values)?;
                (order, key)
            }
            CollectionSchema::List { .. } => return Err(INVALID_ARGUMENT),
        };
        let value = match schema {
            CollectionSchema::Map { .. } => {
                let StateValue::Cell(value) = &**value else {
                    return Err(INVALID_ARGUMENT);
                };
                Some((*value).clone())
            }
            CollectionSchema::Set { .. } => {
                if !matches!(&**value, StateValue::Null) {
                    return Err(INVALID_ARGUMENT);
                }
                None
            }
            CollectionSchema::List { .. } => return Err(INVALID_ARGUMENT),
        };
        entries.push(OrderedEntry { order, key, value });
    }
    entries.sort_by(|left, right| left.order.cmp(&right.order));

    let end = offset.saturating_add(limit).min(entries.len());
    let mut page = Vec::with_capacity(end.saturating_sub(offset));
    for (index, entry) in entries.into_iter().enumerate() {
        let OrderedEntry { key, value, .. } = entry;
        let rendered = match (value, schema) {
            (
                Some(value),
                CollectionSchema::Map {
                    value: value_schema,
                    ..
                },
            ) => {
                json!({
                    "key": key,
                    "value": collection_value_json(&value, value_schema)?
                })
            }
            (None, CollectionSchema::Set { .. }) => key,
            _ => return Err(INVALID_ARGUMENT),
        };
        if index >= offset && index < end {
            page.push(rendered);
        }
    }
    let kind = match schema {
        CollectionSchema::Map { .. } => "map",
        CollectionSchema::Set { .. } => "set",
        CollectionSchema::List { .. } => return Err(INVALID_ARGUMENT),
    };
    Ok(json!({
        "abiVersion": 1,
        "kind": kind,
        "entries": page,
        "nextOffset": (end < map_size).then_some(end)
    }))
}

fn list_page(
    state: &StateValue<Db>,
    element_schema: &CollectionValueSchema,
    offset: usize,
    limit: usize,
) -> Result<Json, i32> {
    let mut cursor = state;
    let mut remaining = None;
    let mut length = 0usize;
    let end = offset.saturating_add(limit);
    let mut entries = Vec::with_capacity(limit);

    loop {
        let StateValue::Array(node) = cursor else {
            return Err(INVALID_ARGUMENT);
        };
        if node.len() != 3 {
            return Err(INVALID_ARGUMENT);
        }
        let StateValue::Cell(count) = node.get(2).ok_or(INVALID_ARGUMENT)? else {
            return Err(INVALID_ARGUMENT);
        };
        let Value::UInt { number, .. } =
            crate::decode_state_cell(count, "UIntRange<18446744073709551616>", "u64")
                .map_err(|_| INVALID_ARGUMENT)?
        else {
            return Err(INVALID_ARGUMENT);
        };
        let count = u64::try_from(number).map_err(|_| INVALID_ARGUMENT)?;
        let count = usize::try_from(count).map_err(|_| INVALID_ARGUMENT)?;
        if count > MAX_BYTES || remaining.is_some_and(|expected| count != expected) {
            return Err(INVALID_ARGUMENT);
        }

        if count == 0 {
            if !matches!(node.get(0), Some(StateValue::Null))
                || !matches!(node.get(1), Some(StateValue::Null))
            {
                return Err(INVALID_ARGUMENT);
            }
            break;
        }

        let StateValue::Cell(head) = node.get(0).ok_or(INVALID_ARGUMENT)? else {
            return Err(INVALID_ARGUMENT);
        };
        if length >= offset && length < end {
            entries.push(collection_value_json(head, element_schema)?);
        } else {
            validate_collection_value(head, element_schema)?;
        }
        length = length.checked_add(1).ok_or(INVALID_ARGUMENT)?;

        let tail = node.get(1).ok_or(INVALID_ARGUMENT)?;
        if !matches!(tail, StateValue::Array(_)) {
            return Err(INVALID_ARGUMENT);
        }
        cursor = tail;
        remaining = Some(count - 1);
    }

    Ok(json!({
        "abiVersion": 1,
        "kind": "list",
        "entries": entries,
        "nextOffset": (end < length).then_some(end)
    }))
}

/// # Safety
/// Each input pointer must reference readable bytes for its declared length.
/// `out_result` must point to writable storage for one `u64`.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_ledger_collection_page(
    request: *const u8,
    request_len: usize,
    plan: *const u8,
    plan_len: usize,
    snapshot: *const u8,
    snapshot_len: usize,
    out_result: *mut u64,
) -> i32 {
    native_ffi::guard(|| {
        unsafe { native_ffi::output(out_result)? };

        let request: Request = serde_json::from_slice(unsafe {
            native_ffi::input(request, request_len, MAX_REQUEST_BYTES)?
        })
        .map_err(|_| INVALID_ARGUMENT)?;
        if request.abi_version != 1
            || request.name.is_empty()
            || !valid_digest(&request.plan_sha256)
            || !valid_digest(&request.state_sha256)
        {
            return Err(INVALID_ARGUMENT);
        }
        if request.keys.len() > MAX_KEYS {
            return Err(LIMIT);
        }
        match (request.offset, request.limit, &request.merkle_path) {
            (Some(offset), Some(limit), None) => {
                if offset > MAX_OFFSET || limit > MAX_PAGE_SIZE {
                    return Err(LIMIT);
                }
                if limit == 0 {
                    return Err(INVALID_ARGUMENT);
                }
            }
            (None, None, Some(_)) => {}
            _ => return Err(INVALID_ARGUMENT),
        }

        let _work = Work::reserve()?;
        let plan_bytes = unsafe { native_ffi::input(plan, plan_len, MAX_BYTES)? };
        let snapshot_bytes = unsafe { native_ffi::input(snapshot, snapshot_len, MAX_BYTES)? };
        let AdmittedSnapshot { plan, state, keys } = admit_snapshot(
            plan_bytes,
            snapshot_bytes,
            &request.plan_sha256,
            &request.state_sha256,
            request.keys.iter().map(|key| (key.ty.as_str(), &key.value)),
        )?;

        let page = if request.merkle_path.is_none() {
            let (final_schema, selected) =
                typed_state_path(&plan.state, &state.data, &request.name, &keys)
                    .map_err(|_| INVALID_ARGUMENT)?;
            match collection_schema(final_schema)? {
                Some(schema) => {
                    let offset = request.offset.ok_or(INVALID_ARGUMENT)?;
                    let limit = request.limit.ok_or(INVALID_ARGUMENT)?;
                    match &schema {
                        CollectionSchema::List { element } => {
                            list_page(&selected, element, offset, limit)?
                        }
                        _ => collection_page(&selected, &schema, offset, limit)?,
                    }
                }
                None => {
                    let tree = merkle_tree_at_node(final_schema, &selected)
                        .map_err(|_| INVALID_ARGUMENT)?;
                    merkle_page(
                        &tree,
                        request.offset.ok_or(INVALID_ARGUMENT)?,
                        request.limit.ok_or(INVALID_ARGUMENT)?,
                    )?
                }
            }
        } else {
            let tree = merkle_tree_at(&plan.state, &state.data, &request.name, &keys)
                .map_err(|_| INVALID_ARGUMENT)?;
            if let Some(query) = &request.merkle_path {
                merkle_path_result(&tree, query)?
            } else {
                merkle_page(
                    &tree,
                    request.offset.ok_or(INVALID_ARGUMENT)?,
                    request.limit.ok_or(INVALID_ARGUMENT)?,
                )?
            }
        };
        let result =
            native_ffi::service_public_bytes(serde_json::to_vec(&page).map_err(|_| INTERNAL)?)?;
        unsafe { out_result.write(result) };
        Ok(())
    })
}

/// Read one UInt64 Counter from an authenticated, canonical state snapshot.
/// The request, plan, and snapshot pointers follow the same safety contract as
/// `noctium_ledger_collection_page`.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_ledger_counter_get(
    request: *const u8,
    request_len: usize,
    plan: *const u8,
    plan_len: usize,
    snapshot: *const u8,
    snapshot_len: usize,
    out_result: *mut u64,
) -> i32 {
    native_ffi::guard(|| {
        unsafe { native_ffi::output(out_result)? };

        let request: CounterRequest = serde_json::from_slice(unsafe {
            native_ffi::input(request, request_len, MAX_REQUEST_BYTES)?
        })
        .map_err(|_| INVALID_ARGUMENT)?;
        if request.abi_version != 1
            || request.name.is_empty()
            || !valid_digest(&request.plan_sha256)
            || !valid_digest(&request.state_sha256)
        {
            return Err(INVALID_ARGUMENT);
        }
        if request.keys.len() > MAX_KEYS {
            return Err(LIMIT);
        }

        let _work = Work::reserve()?;
        let plan_bytes = unsafe { native_ffi::input(plan, plan_len, MAX_BYTES)? };
        let snapshot_bytes = unsafe { native_ffi::input(snapshot, snapshot_len, MAX_BYTES)? };
        let AdmittedSnapshot { plan, state, keys } = admit_snapshot(
            plan_bytes,
            snapshot_bytes,
            &request.plan_sha256,
            &request.state_sha256,
            request.keys.iter().map(|key| (key.ty.as_str(), &key.value)),
        )?;

        let (schema, selected) = typed_state_path(&plan.state, &state.data, &request.name, &keys)
            .map_err(|_| INVALID_ARGUMENT)?;
        if schema != &json!({"counter": true}) {
            return Err(INVALID_ARGUMENT);
        }
        let value = counter_value(&selected)?;
        let result = native_ffi::service_public_bytes(
            serde_json::to_vec(&json!({
                "abiVersion": 1,
                "kind": "counter",
                "value": value.to_string(),
            }))
            .map_err(|_| INTERNAL)?,
        )?;
        unsafe { out_result.write(result) };
        Ok(())
    })
}
