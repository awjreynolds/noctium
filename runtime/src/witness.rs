//! Canonical value types shared by typed witness requests and fixed composites.
use crate::{ScalarType, aggregates, canonical_field, canonical_unsigned};
use anyhow::{Result, anyhow, bail, ensure};
use num_bigint::BigUint;
use serde_json::Value as Json;
use std::{collections::BTreeMap, ops::Range, sync::Arc};
use zeroize::{Zeroize, Zeroizing};

pub const MAX_SCHEMAS: usize = 256;
pub const MAX_TOTAL_SCHEMA_BYTES: usize = 1_048_576;
pub const MAX_ARGUMENTS: usize = 64;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Unit,
    Scalar(ScalarType),
    Aggregate(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Parameter {
    pub name: String,
    pub type_token: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessSignature {
    pub name: String,
    pub operation: String,
    pub capability: String,
    pub parameters: Vec<Parameter>,
    pub result_type: String,
    pub private_key: Option<String>,
}

#[derive(Clone, Debug)]
pub struct Projection {
    pub kind: String,
    pub index: Option<usize>,
    pub name: Option<String>,
    pub variant: Option<String>,
    pub type_token: String,
}

#[derive(Clone, Default)]
pub struct Registry {
    schemas: BTreeMap<String, Arc<aggregates::Schema>>,
    type_tokens: BTreeMap<String, String>,
    schema_json: BTreeMap<String, Vec<u8>>,
    schema_bytes: usize,
}

impl Type {
    pub fn parse(token: &str, registry: &Registry) -> Result<Self> {
        if token == "Unit" {
            return Ok(Self::Unit);
        }
        if let Some(name) = token.strip_prefix("Aggregate:") {
            ensure!(token.len() <= 64, "witness type token exceeds limit");
            ensure!(
                registry.schemas.contains_key(token),
                "unknown aggregate type token"
            );
            ensure!(valid_type_name(name), "invalid aggregate type token");
            return Ok(Self::Aggregate(token.to_owned()));
        }
        let ty = ScalarType::parse(token)?;
        Ok(Self::Scalar(ty))
    }

    pub fn token(&self) -> String {
        match self {
            Self::Unit => "Unit".to_owned(),
            Self::Scalar(ScalarType::Native) => "Native".to_owned(),
            Self::Scalar(ScalarType::Bool) => "Bool".to_owned(),
            Self::Scalar(ScalarType::Bytes32) => "Bytes<32>".to_owned(),
            Self::Scalar(ScalarType::Bytes(length)) => format!("Bytes<{length}>"),
            Self::Scalar(ScalarType::OpaqueBytes) => "OpaqueBytes".to_owned(),
            Self::Scalar(ScalarType::OpaqueString) => "OpaqueString".to_owned(),
            Self::Scalar(ScalarType::JubjubScalar) => "JubjubScalar".to_owned(),
            Self::Scalar(ScalarType::JubjubPoint) => "JubjubPoint".to_owned(),
            #[cfg(feature = "zkir-321")]
            Self::Scalar(ScalarType::Foreign(ty)) => ty.source_name().to_owned(),
            Self::Scalar(ScalarType::UInt(maximum)) => {
                format!("UIntRange<{}>", maximum + BigUint::from(1u8))
            }
            Self::Aggregate(token) => token.clone(),
        }
    }
}

fn valid_type_name(name: &str) -> bool {
    let Some(number) = name.strip_prefix('t') else {
        return false;
    };
    !number.is_empty()
        && number.bytes().all(|byte| byte.is_ascii_digit())
        && (number == "0" || !number.starts_with('0'))
}

fn scalar_type_key(ty: &ScalarType) -> String {
    match ty {
        ScalarType::Native => "sN".to_owned(),
        ScalarType::Bool => "sB".to_owned(),
        ScalarType::Bytes32 => "bytes32".to_owned(),
        ScalarType::Bytes(length) => format!("bytes{length}"),
        ScalarType::OpaqueBytes => "opaqueBytes".to_owned(),
        ScalarType::OpaqueString => "opaqueString".to_owned(),
        ScalarType::JubjubScalar => "jubjubScalar".to_owned(),
        ScalarType::JubjubPoint => "jubjubPoint".to_owned(),
        #[cfg(feature = "zkir-321")]
        ScalarType::Foreign(ty) => format!("foreign:{}", ty.source_name()),
        ScalarType::UInt(maximum) => format!("sU{};", maximum.to_str_radix(10)),
    }
}

fn type_key(token: &str, registry: &Registry) -> Result<String> {
    match Type::parse(token, registry)? {
        Type::Unit => Ok("u".to_owned()),
        Type::Scalar(ty) => Ok(scalar_type_key(&ty)),
        Type::Aggregate(token) => registry.schemas[&token].root_type_key(),
    }
}

fn validate_scalar(ty: &ScalarType, value: &Json) -> Result<()> {
    match ty {
        ScalarType::Native => {
            let text = value
                .as_str()
                .ok_or_else(|| anyhow!("expected canonical Native decimal"))?;
            canonical_field(text)?;
        }
        ScalarType::Bool => {
            ensure!(value.is_boolean(), "expected Boolean value");
        }
        ScalarType::UInt(maximum) => {
            let text = value
                .as_str()
                .ok_or_else(|| anyhow!("expected canonical unsigned decimal"))?;
            canonical_unsigned(text, maximum)?;
        }
        ScalarType::Bytes32
        | ScalarType::Bytes(_)
        | ScalarType::OpaqueBytes
        | ScalarType::OpaqueString
        | ScalarType::JubjubScalar
        | ScalarType::JubjubPoint => {
            let token = Type::Scalar(ty.clone()).token();
            crate::input_value(&token, value)?;
        }
        #[cfg(feature = "zkir-321")]
        ScalarType::Foreign(_) => {
            let token = Type::Scalar(ty.clone()).token();
            crate::input_value(&token, value)?;
        }
    }
    Ok(())
}

fn wipe_json(value: &mut Json) {
    match value {
        Json::String(text) => text.zeroize(),
        Json::Array(values) => values.iter_mut().for_each(wipe_json),
        Json::Object(values) => values.values_mut().for_each(wipe_json),
        _ => {}
    }
}

impl Registry {
    pub fn register_json(&mut self, token: &str, schema_json: &[u8]) -> Result<()> {
        ensure!(
            valid_type_name(token.strip_prefix("Aggregate:").unwrap_or("")),
            "invalid aggregate type token"
        );
        ensure!(token.len() <= 64, "aggregate type token exceeds limit");
        ensure!(
            schema_json.len() <= aggregates::MAX_TRANSPORT_BYTES,
            "aggregate schema exceeds transport limit"
        );
        ensure!(
            self.schema_bytes
                .checked_add(schema_json.len())
                .is_some_and(|size| size <= MAX_TOTAL_SCHEMA_BYTES),
            "aggregate schema registry exceeds byte limit"
        );
        ensure!(
            self.schemas.len() < MAX_SCHEMAS || self.schemas.contains_key(token),
            "aggregate schema count limit exceeded"
        );
        ensure!(
            !self.schemas.contains_key(token),
            "duplicate aggregate type token"
        );
        let schema = Arc::new(aggregates::Schema::from_json(schema_json)?);
        let key = schema.root_type_key()?;
        if let Some(existing) = self.type_tokens.get(&key) {
            ensure!(existing == token, "duplicate aggregate type identity");
        }
        let parsed: Json = serde_json::from_slice(schema_json)?;
        let canonical = serde_json::to_vec(&parsed)?;
        ensure!(
            self.schema_bytes
                .checked_add(canonical.len())
                .is_some_and(|size| size <= MAX_TOTAL_SCHEMA_BYTES),
            "aggregate schema registry exceeds byte limit"
        );
        self.schema_bytes += canonical.len();
        self.type_tokens.insert(key, token.to_owned());
        self.schemas.insert(token.to_owned(), schema);
        self.schema_json.insert(token.to_owned(), canonical);
        Ok(())
    }

    pub fn declarations(&self) -> Result<Vec<Json>> {
        self.schema_json
            .iter()
            .map(|(token, schema)| {
                Ok(serde_json::json!({
                    "id": token,
                    "schema": serde_json::from_slice::<Json>(schema)?
                }))
            })
            .collect()
    }

    pub fn contains(&self, token: &str) -> bool {
        token == "Unit" || ScalarType::parse(token).is_ok() || self.schemas.contains_key(token)
    }

    pub fn validate(&self, token: &str, value: &Json) -> Result<()> {
        match Type::parse(token, self)? {
            Type::Unit => ensure!(
                value == &serde_json::json!({"kind":"unit"}),
                "invalid Unit value"
            ),
            Type::Scalar(ty) => validate_scalar(&ty, value)?,
            Type::Aggregate(token) => {
                let bytes = Zeroizing::new(serde_json::to_vec(value)?);
                self.schemas[&token].validate_value_json(&bytes)?;
            }
        }
        Ok(())
    }

    pub fn leaf_types(&self, token: &str) -> Result<Vec<String>> {
        match Type::parse(token, self)? {
            Type::Unit => Ok(vec![]),
            Type::Scalar(ty) => Ok(vec![Type::Scalar(ty).token()]),
            Type::Aggregate(token) => self.schemas[&token].leaf_types(),
        }
    }

    pub fn flatten_leaves(&self, token: &str, value: &Json) -> Result<Vec<Json>> {
        self.validate(token, value)?;
        match Type::parse(token, self)? {
            Type::Unit => Ok(vec![]),
            Type::Scalar(_) => Ok(vec![value.clone()]),
            Type::Aggregate(token) => {
                let bytes = Zeroizing::new(serde_json::to_vec(value)?);
                self.schemas[&token].flatten_leaves_json(&bytes)
            }
        }
    }

    pub fn from_leaves(&self, token: &str, leaves: &[Json]) -> Result<Json> {
        let Type::Aggregate(token) = Type::parse(token, self)? else {
            bail!("aggregate leaves require an aggregate type")
        };
        let bytes = Zeroizing::new(self.schemas[&token].from_leaf_json(leaves)?);
        Ok(serde_json::from_slice(&bytes)?)
    }

    pub fn can_widen_aggregate(&self, source: &str, target: &str) -> Result<bool> {
        let Type::Aggregate(source) = Type::parse(source, self)? else {
            bail!("aggregate widening requires an aggregate source")
        };
        let Type::Aggregate(target) = Type::parse(target, self)? else {
            bail!("aggregate widening requires an aggregate target")
        };
        self.schemas[&source].can_widen_to(&self.schemas[&target])
    }

    pub fn widen_aggregate_value(&self, source: &str, target: &str, value: &Json) -> Result<Json> {
        ensure!(
            self.can_widen_aggregate(source, target)?,
            "incompatible aggregate widening"
        );
        let mut leaves = self.flatten_leaves(source, value)?;
        let widened = self.from_leaves(target, &leaves);
        leaves.iter_mut().for_each(wipe_json);
        widened
    }

    pub fn index_type(&self, token: &str) -> Result<String> {
        let Type::Aggregate(token) = Type::parse(token, self)? else {
            bail!("dynamic indexing requires an aggregate vector or bytes")
        };
        let schema = &self.schemas[&token];
        let key = schema.indexed_type_key()?;
        self.type_tokens
            .get(&key)
            .cloned()
            .or_else(|| scalar_token_from_key(&key))
            .ok_or_else(|| anyhow!("aggregate index type is absent from the checked registry"))
    }

    pub fn index(&self, token: &str, value: &Json, index: usize) -> Result<(String, Json)> {
        let (token, value, _) = self.index_with_range(token, value, index)?;
        Ok((token, value))
    }

    pub fn index_with_range(
        &self,
        token: &str,
        value: &Json,
        index: usize,
    ) -> Result<(String, Json, Range<usize>)> {
        let Type::Aggregate(token) = Type::parse(token, self)? else {
            bail!("dynamic indexing requires an aggregate vector or bytes")
        };
        let schema = &self.schemas[&token];
        let aggregate_projection = schema.index_projection(index)?;
        let (key, _) = schema.projection_type(&aggregate_projection)?;
        let type_token = self
            .type_tokens
            .get(&key)
            .cloned()
            .or_else(|| scalar_token_from_key(&key))
            .ok_or_else(|| anyhow!("aggregate index type is absent from the checked registry"))?;
        let projection = Projection {
            kind: aggregate_projection.kind,
            index: aggregate_projection.index,
            name: aggregate_projection.name,
            variant: aggregate_projection.variant,
            type_token,
        };
        self.project_with_range(&token, value, &projection)
    }

    pub fn projection_type(
        &self,
        token: &str,
        projection: &Projection,
    ) -> Result<(String, Range<usize>)> {
        let Type::Aggregate(token) = Type::parse(token, self)? else {
            bail!("projection requires an aggregate type")
        };
        let aggregate_projection = aggregates::Projection {
            kind: projection.kind.clone(),
            index: projection.index,
            name: projection.name.clone(),
            variant: projection.variant.clone(),
        };
        let (actual_key, range) = self.schemas[&token].projection_type(&aggregate_projection)?;
        let expected_key = type_key(&projection.type_token, self)?;
        ensure!(
            actual_key == expected_key,
            "aggregate projection type identity mismatch"
        );
        Ok((projection.type_token.clone(), range))
    }

    pub fn project(
        &self,
        token: &str,
        value: &Json,
        projection: &Projection,
    ) -> Result<(String, Json)> {
        let (token, value, _) = self.project_with_range(token, value, projection)?;
        Ok((token, value))
    }

    pub fn project_with_range(
        &self,
        token: &str,
        value: &Json,
        projection: &Projection,
    ) -> Result<(String, Json, Range<usize>)> {
        let Type::Aggregate(token) = Type::parse(token, self)? else {
            bail!("projection requires an aggregate value")
        };
        let source = &self.schemas[&token];
        let aggregate_projection = aggregates::Projection {
            kind: projection.kind.clone(),
            index: projection.index,
            name: projection.name.clone(),
            variant: projection.variant.clone(),
        };
        let (actual_key, range) = source.projection_type(&aggregate_projection)?;
        let expected_key = type_key(&projection.type_token, self)?;
        ensure!(
            actual_key == expected_key,
            "aggregate projection type identity mismatch"
        );
        let bytes = Zeroizing::new(serde_json::to_vec(value)?);
        let projected = source.project_value_json(&bytes, &aggregate_projection)?;
        let projected_value_bytes = Zeroizing::new(projected.value);
        let mut projected_value: Json = serde_json::from_slice(&projected_value_bytes)?;
        if let Type::Scalar(scalar) = Type::parse(&projection.type_token, self)? {
            let expected_kind = match &scalar {
                ScalarType::Native => "native",
                ScalarType::Bool => "bool",
                ScalarType::UInt(_) => "uint",
                ScalarType::Bytes32
                | ScalarType::Bytes(_)
                | ScalarType::OpaqueBytes
                | ScalarType::OpaqueString => {
                    bail!("byte projections require an aggregate schema")
                }
                ScalarType::JubjubScalar | ScalarType::JubjubPoint => {
                    bail!("Jubjub projections require a typed curve schema")
                }
                #[cfg(feature = "zkir-321")]
                ScalarType::Foreign(_) => {
                    bail!("foreign values require typed foreign projections")
                }
            };
            ensure!(
                projected_value.get("kind").and_then(Json::as_str) == Some(expected_kind),
                "aggregate projection scalar encoding mismatch"
            );
            if let ScalarType::UInt(maximum) = &scalar {
                let expected_maximum = maximum.to_str_radix(10);
                ensure!(
                    projected_value.get("maximum").and_then(Json::as_str)
                        == Some(expected_maximum.as_str()),
                    "aggregate projection unsigned bound mismatch"
                );
            }
            let canonical = match scalar {
                ScalarType::Native | ScalarType::UInt(_) => Json::String(
                    projected_value
                        .get("value")
                        .and_then(Json::as_str)
                        .ok_or_else(|| anyhow!("aggregate projection decimal value missing"))?
                        .to_owned(),
                ),
                ScalarType::Bool => Json::Bool(
                    projected_value
                        .get("value")
                        .and_then(Json::as_bool)
                        .ok_or_else(|| anyhow!("aggregate projection Boolean value missing"))?,
                ),
                ScalarType::Bytes32
                | ScalarType::Bytes(_)
                | ScalarType::OpaqueBytes
                | ScalarType::OpaqueString => {
                    bail!("byte projections require an aggregate schema")
                }
                ScalarType::JubjubScalar | ScalarType::JubjubPoint => {
                    bail!("Jubjub projections require a typed curve schema")
                }
                #[cfg(feature = "zkir-321")]
                ScalarType::Foreign(_) => {
                    bail!("foreign values require typed foreign projections")
                }
            };
            wipe_json(&mut projected_value);
            projected_value = canonical;
        }
        self.validate(&projection.type_token, &projected_value)?;
        Ok((projection.type_token.clone(), projected_value, range))
    }
}

fn scalar_token_from_key(key: &str) -> Option<String> {
    match key {
        "u" => Some("Unit".to_owned()),
        "sN" => Some("Native".to_owned()),
        "sB" => Some("Bool".to_owned()),
        "opaqueBytes" => Some("OpaqueBytes".to_owned()),
        "opaqueString" => Some("OpaqueString".to_owned()),
        _ => {
            let maximum = key.strip_prefix("sU")?.strip_suffix(';')?;
            let value = BigUint::parse_bytes(maximum.as_bytes(), 10)?;
            Some(format!("UIntRange<{}>", value + BigUint::from(1u8)))
        }
    }
}
