//! Explicit host capabilities and private journals. No ambient I/O or durable storage.
use crate::{
    ScalarType, input_value,
    lifecycle::{Effect, Event, Lifecycle, Phase},
    witness::{Registry, WitnessSignature},
};
use serde::{Deserialize, Serialize};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use zeroize::Zeroize;

pub const PROTOCOL_VERSION: u32 = 1;
pub const READ: &str = "private_state.read.v1";
/// A typed read uses its source signature's exact result schema.
pub const SOURCE_CELL_TYPE: &str = "SourceCellType";
pub const STAGE: &str = "private_state.stage.v1";
pub const CAS: &str = "private_state.compare_exchange.v1";
pub const CAS_SCHEMA: &str = "PrivateStateCasResult/v1";
pub const MAX_PRIVATE_BYTES: usize = 65_536;
const MAX_LEGACY_REQUESTS: usize = 257;
const MAX_TYPED_REQUESTS: usize = 1_201;
const MAX_RECOVERY_BYTES: usize = 1_200_000;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Descriptor,
    Denied,
    State,
    Response,
    Limit,
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Descriptor => "invalid host descriptor",
            Self::Denied => "host capability denied",
            Self::State => "invalid host lifecycle state",
            Self::Response => "invalid host response",
            Self::Limit => "host limit exceeded",
        })
    }
}
impl std::error::Error for Error {}
pub type Result<T> = std::result::Result<T, Error>;
fn require(value: bool, error: Error) -> Result<()> {
    if value { Ok(()) } else { Err(error) }
}
fn wipe(value: &mut Json) {
    match value {
        Json::String(v) => v.zeroize(),
        Json::Array(v) => v.iter_mut().for_each(wipe),
        Json::Object(v) => v.values_mut().for_each(wipe),
        _ => {}
    }
}
fn serialized_json_len(value: &Json, error: Error) -> Result<usize> {
    let mut bytes = serde_json::to_vec(value).map_err(|_| error)?;
    let length = bytes.len();
    bytes.zeroize();
    Ok(length)
}
fn identifier(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && value
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b"_-.:".contains(&b))
}
fn operation(value: &str) -> bool {
    identifier(value) && value.ends_with(".v1")
}
fn key(value: &str, prefix: bool) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && value
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b"_-/.:".contains(&b))
        && !value.starts_with('/')
        && (prefix || !value.ends_with('/'))
        && value
            .strip_suffix('/')
            .unwrap_or(value)
            .split('/')
            .all(|s| !s.is_empty() && s != "." && s != "..")
}
fn typed_token_valid(token: &str, registry: Option<&Registry>) -> bool {
    token == "Unit"
        || ScalarType::parse(token).is_ok()
        || registry.is_some_and(|value| value.contains(token))
}
fn validate_witness_argument(token: &str, value: &Json, registry: &Registry) -> Result<()> {
    if token == "Key" {
        let value = value.as_str().ok_or(Error::Response)?;
        require(key(value, false), Error::Response)?;
        return Ok(());
    }
    registry
        .validate(token, value)
        .map_err(|_| Error::Response.into())
}
#[derive(Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Context {
    pub protocol_version: u32,
    pub namespace: String,
    pub base_revision: String,
    pub attempt_id: String,
    pub capabilities: Vec<Capability>,
    pub operations: Vec<Operation>,
    pub providers: Vec<Provider>,
    pub commit_capability: String,
    #[serde(default)]
    pub limits: Limits,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RecoveryContext {
    recovery_version: u32,
    context: Context,
    typed: bool,
    typed_inputs: Vec<String>,
    typed_schemas: Vec<RecoverySchema>,
    target: String,
    entrypoint: String,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RecoverySchema {
    id: String,
    schema: Json,
}
#[derive(Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Capability {
    pub id: String,
    pub namespace: String,
    pub key_prefix: String,
    pub operations: Vec<String>,
}
#[derive(Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Operation {
    pub operation: String,
    pub argument_schema: BTreeMap<String, String>,
    pub result_schema: String,
}
#[derive(Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Provider {
    pub input: String,
    pub operation: String,
    pub capability: String,
    pub arguments: BTreeMap<String, Json>,
}
#[derive(Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Limits {
    pub requests: usize,
    pub writes: usize,
    pub private_bytes: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            requests: 64,
            writes: 64,
            private_bytes: MAX_PRIVATE_BYTES,
        }
    }
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Stage {
    pub abi_version: u32,
    pub operation: String,
    pub capability: String,
    pub key: String,
    #[serde(rename = "type")]
    pub ty: String,
    pub value: Json,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Notice {
    pub abi_version: u32,
    pub event: String,
    pub attempt_id: String,
    pub transaction_id: String,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct CasResponse {
    attempt_id: String,
    transaction_id: String,
    journal_digest: String,
    outcome: String,
    base_revision: String,
    revision: String,
}
struct Write {
    ty: String,
    value: Json,
}
impl Drop for Write {
    fn drop(&mut self) {
        wipe(&mut self.value);
    }
}
enum Pending {
    Provider {
        id: u64,
        input: String,
    },
    TypedProvider {
        id: u64,
        input: String,
        signature: WitnessSignature,
        arguments: Json,
    },
    Cas {
        id: u64,
    },
}
impl Drop for Pending {
    fn drop(&mut self) {
        if let Self::TypedProvider {
            arguments,
            signature,
            ..
        } = self
        {
            wipe(arguments);
            if let Some(key) = &mut signature.private_key {
                key.zeroize();
            }
        }
    }
}
pub struct Runtime {
    context: Context,
    lifecycle: Lifecycle,
    target: String,
    entrypoint: String,
    registry: Option<Registry>,
    typed_inputs: BTreeSet<String>,
    writes: BTreeMap<String, Write>,
    pending: Option<Pending>,
    requests: usize,
    retained_journal_digest: Option<String>,
    completed_cas: Option<(bool, String)>,
}
impl Runtime {
    pub fn new(
        context: Context,
        private_inputs: &BTreeMap<String, String>,
        target: String,
        entrypoint: String,
    ) -> Result<Self> {
        Self::new_inner(
            context,
            private_inputs,
            target,
            entrypoint,
            None,
            &BTreeSet::new(),
        )
    }

    pub fn new_typed(
        context: Context,
        private_inputs: &[String],
        target: String,
        entrypoint: String,
        registry: &Registry,
    ) -> Result<Self> {
        let typed_inputs: BTreeSet<String> = private_inputs.iter().cloned().collect();
        require(
            typed_inputs.len() == private_inputs.len(),
            Error::Descriptor,
        )?;
        let mut private_schemas = BTreeMap::new();
        for provider in &context.providers {
            let descriptor = context
                .operations
                .iter()
                .find(|descriptor| descriptor.operation == provider.operation)
                .ok_or(Error::Descriptor)?;
            private_schemas.insert(provider.input.clone(), descriptor.result_schema.clone());
        }
        Self::new_inner(
            context,
            &private_schemas,
            target,
            entrypoint,
            Some(registry),
            &typed_inputs,
        )
    }

    fn new_inner(
        context: Context,
        private_inputs: &BTreeMap<String, String>,
        target: String,
        entrypoint: String,
        registry: Option<&Registry>,
        typed_inputs: &BTreeSet<String>,
    ) -> Result<Self> {
        require(
            context.protocol_version == PROTOCOL_VERSION && identifier(&context.namespace),
            Error::Descriptor,
        )?;
        require(
            context.capabilities.len() <= 32
                && context.operations.len() <= 32
                && context.providers.len() <= 32,
            Error::Limit,
        )?;
        let max_requests = if registry.is_some() {
            MAX_TYPED_REQUESTS
        } else {
            MAX_LEGACY_REQUESTS
        };
        require(
            context.limits.requests > private_inputs.len()
                && context.limits.requests <= max_requests
                && context.limits.writes > 0
                && context.limits.writes <= 64
                && context.limits.private_bytes >= 1024
                && context.limits.private_bytes <= MAX_PRIVATE_BYTES,
            Error::Limit,
        )?;
        let lifecycle = Lifecycle::new(context.attempt_id.clone(), context.base_revision.clone())
            .map_err(|_| Error::Descriptor)?;
        let mut names = BTreeSet::new();
        for capability in &context.capabilities {
            require(
                identifier(&capability.id)
                    && names.insert(capability.id.clone())
                    && capability.namespace == context.namespace
                    && key(&capability.key_prefix, true)
                    && !capability.operations.is_empty()
                    && capability.operations.len() <= 32,
                Error::Descriptor,
            )?;
            let mut ops = BTreeSet::new();
            for name in &capability.operations {
                require(operation(name) && ops.insert(name), Error::Descriptor)?;
            }
        }
        names.clear();
        for descriptor in &context.operations {
            require(
                operation(&descriptor.operation)
                    && !matches!(descriptor.operation.as_str(), STAGE | CAS)
                    && names.insert(descriptor.operation.clone())
                    && descriptor.argument_schema.len() <= 8
                    && (typed_token_valid(&descriptor.result_schema, registry)
                        || (registry.is_some()
                            && descriptor.operation == READ
                            && descriptor.result_schema == SOURCE_CELL_TYPE)),
                Error::Descriptor,
            )?;
            for (name, ty) in &descriptor.argument_schema {
                require(
                    identifier(name) && (ty == "Key" || typed_token_valid(ty, registry)),
                    Error::Descriptor,
                )?;
            }
            if descriptor.operation == READ {
                require(
                    descriptor.argument_schema == BTreeMap::from([("key".into(), "Key".into())]),
                    Error::Descriptor,
                )?;
            }
        }
        names.clear();
        let runtime = Self {
            context,
            lifecycle,
            target,
            entrypoint,
            registry: registry.cloned(),
            typed_inputs: typed_inputs.clone(),
            writes: BTreeMap::new(),
            pending: None,
            requests: 0,
            retained_journal_digest: None,
            completed_cas: None,
        };
        runtime.grant(&runtime.context.commit_capability, CAS, None)?;
        for provider in &runtime.context.providers {
            let descriptor = runtime.descriptor(&provider.operation)?;
            let typed_read = typed_inputs.contains(&provider.input) && provider.operation == READ;
            let typed_provider_arguments_valid = if typed_read {
                descriptor.argument_schema == BTreeMap::from([("key".into(), "Key".into())])
                    && provider.arguments.len() == 1
                    && provider
                        .arguments
                        .get("key")
                        .and_then(Json::as_str)
                        .is_some_and(|value| key(value, false))
            } else if typed_inputs.contains(&provider.input) {
                provider.arguments.is_empty()
            } else {
                provider.arguments.len() == descriptor.argument_schema.len()
            };
            require(
                names.insert(provider.input.clone())
                    && private_inputs.contains_key(&provider.input)
                    && typed_provider_arguments_valid,
                Error::Descriptor,
            )?;
            require(
                private_inputs[&provider.input] == descriptor.result_schema
                    && (descriptor.result_schema != SOURCE_CELL_TYPE || typed_read)
                    && if typed_inputs.contains(&provider.input) {
                        typed_provider_arguments_valid
                    } else {
                        provider.arguments.len() == descriptor.argument_schema.len()
                    },
                Error::Descriptor,
            )?;
            runtime.grant(&provider.capability, &provider.operation, None)?;
            if typed_inputs.contains(&provider.input) {
                if typed_read {
                    let value = provider.arguments["key"]
                        .as_str()
                        .ok_or(Error::Descriptor)?;
                    runtime.grant(&provider.capability, &provider.operation, Some(value))?;
                }
                continue;
            }
            for (name, ty) in &descriptor.argument_schema {
                let value = provider.arguments.get(name).ok_or(Error::Descriptor)?;
                if ty == "Key" {
                    let value = value.as_str().ok_or(Error::Descriptor)?;
                    require(key(value, false), Error::Descriptor)?;
                    runtime.grant(&provider.capability, &provider.operation, Some(value))?;
                } else {
                    if let Some(registry) = registry {
                        registry
                            .validate(ty, value)
                            .map_err(|_| Error::Descriptor)?;
                    } else {
                        input_value(ty, value).map_err(|_| Error::Descriptor)?;
                    }
                }
            }
        }
        require(
            typed_inputs.iter().all(|input| names.contains(input)),
            Error::Descriptor,
        )?;
        // Bound the retained descriptor/argument envelope as well as later journal exports.
        require(
            runtime.private_size()? <= runtime.context.limits.private_bytes,
            Error::Limit,
        )?;
        Ok(runtime)
    }
    fn descriptor(&self, name: &str) -> Result<&Operation> {
        self.context
            .operations
            .iter()
            .find(|d| d.operation == name)
            .ok_or(Error::Descriptor)
    }
    fn provider(&self, input: &str) -> Option<&Provider> {
        self.context.providers.iter().find(|p| p.input == input)
    }
    fn grant(&self, id: &str, operation: &str, key: Option<&str>) -> Result<()> {
        let capability = self
            .context
            .capabilities
            .iter()
            .find(|c| c.id == id)
            .ok_or(Error::Denied)?;
        require(
            capability.namespace == self.context.namespace
                && capability.operations.iter().any(|op| op == operation),
            Error::Denied,
        )?;
        if let Some(key) = key {
            require(
                if capability.key_prefix.ends_with('/') {
                    key.starts_with(&capability.key_prefix)
                } else {
                    key == capability.key_prefix
                },
                Error::Denied,
            )?;
        }
        Ok(())
    }
    fn private_size(&self) -> Result<usize> {
        let writes: BTreeMap<_, _> = self
            .writes
            .iter()
            .map(|(k, w)| (k, json!({"type":w.ty,"value":w.value})))
            .collect();
        let args: Vec<_> = self
            .context
            .providers
            .iter()
            .map(|p| &p.arguments)
            .collect();
        let pending_arguments = match &self.pending {
            Some(Pending::TypedProvider { arguments, .. }) => Some(arguments),
            _ => None,
        };
        let transaction = self
            .lifecycle
            .transaction_id()
            .unwrap_or("0000000000000000000000000000000000000000000000000000000000000000");
        let mut envelope = json!({"journal":{"protocolVersion":1,"attemptId":self.lifecycle.attempt_id(),"transactionId":transaction,"namespace":self.context.namespace,"baseRevision":self.lifecycle.base_revision(),"contractAddress":self.target,"entrypoint":self.entrypoint,"writes":writes},"arguments":args});
        if let Some(arguments) = pending_arguments {
            envelope["pendingArguments"] = arguments.clone();
        }
        serde_json::to_vec(&envelope)
            .map(|mut v| {
                let length = v.len();
                v.zeroize();
                length + 128
            })
            .map_err(|_| Error::Descriptor)
    }
    fn count_request(&mut self) -> Result<()> {
        require(self.requests < self.context.limits.requests, Error::Limit)?;
        self.requests += 1;
        Ok(())
    }
    pub fn begin_input(&mut self, input: &str, id: u64) -> Result<Option<Json>> {
        require(
            self.lifecycle.phase() == Phase::Open && self.pending.is_none(),
            Error::State,
        )?;
        let provider = self.provider(input);
        if let Some(provider) = provider {
            require(
                self.descriptor(&provider.operation)?.result_schema != SOURCE_CELL_TYPE,
                Error::Descriptor,
            )?;
        }
        let has_provider = provider.is_some();
        self.count_request()?;
        if has_provider {
            self.pending = Some(Pending::Provider {
                id,
                input: input.to_owned(),
            });
            self.input_metadata()
        } else {
            Ok(None)
        }
    }
    pub fn input_metadata(&self) -> Result<Option<Json>> {
        let Some(Pending::Provider { id, input }) = &self.pending else {
            return Ok(None);
        };
        let provider = self.provider(input).ok_or(Error::State)?;
        let descriptor = self.descriptor(&provider.operation)?;
        Ok(Some(
            json!({"id":id,"operation":provider.operation,"capability":provider.capability,"schema":descriptor.result_schema,"name":input,"type":descriptor.result_schema,"visibility":"private","hasPrivateArguments":true,"protocolVersion":1}),
        ))
    }

    pub fn begin_typed_input(
        &mut self,
        input: &str,
        id: u64,
        signature: &WitnessSignature,
        arguments: &Json,
        registry: &Registry,
    ) -> Result<Option<Json>> {
        require(
            self.lifecycle.phase() == Phase::Open && self.pending.is_none(),
            Error::State,
        )?;
        require(
            signature.name == input
                && identifier(input)
                && signature.operation != STAGE
                && signature.operation != CAS,
            Error::Descriptor,
        )?;
        let provider = self.provider(input).ok_or(Error::Descriptor)?;
        let private_read = signature.operation == READ;
        if private_read {
            require(
                signature
                    .private_key
                    .as_deref()
                    .is_some_and(|value| key(value, false))
                    && signature.parameters.is_empty()
                    && provider.arguments.get("key").and_then(Json::as_str)
                        == signature.private_key.as_deref(),
                Error::Descriptor,
            )?;
        } else {
            require(
                signature.private_key.is_none() && provider.arguments.is_empty(),
                Error::Descriptor,
            )?;
        }
        require(
            provider.operation == signature.operation
                && provider.capability == signature.capability,
            Error::Descriptor,
        )?;
        let descriptor = self.descriptor(&signature.operation)?;
        require(
            descriptor.result_schema == signature.result_type
                || (private_read && descriptor.result_schema == SOURCE_CELL_TYPE),
            Error::Descriptor,
        )?;
        require(
            typed_token_valid(&signature.result_type, Some(registry)),
            Error::Descriptor,
        )?;
        require(signature.parameters.len() <= 8, Error::Limit)?;
        if private_read {
            require(
                descriptor.argument_schema == BTreeMap::from([("key".into(), "Key".into())]),
                Error::Descriptor,
            )?;
        }
        let mut names = BTreeSet::new();
        let expected_parameters = descriptor.argument_schema.len() - usize::from(private_read);
        require(
            signature.parameters.iter().all(|parameter| {
                identifier(&parameter.name)
                    && parameter.type_token != "Key"
                    && names.insert(parameter.name.as_str())
                    && descriptor.argument_schema.get(&parameter.name)
                        == Some(&parameter.type_token)
            }) && names.len() == expected_parameters,
            Error::Descriptor,
        )?;
        require(
            serialized_json_len(arguments, Error::Response)? <= self.context.limits.private_bytes,
            Error::Limit,
        )?;
        let object = arguments.as_object().ok_or(Error::Response)?;
        require(
            object.len() == signature.parameters.len()
                && object.keys().all(|name| names.contains(name.as_str())),
            Error::Response,
        )?;
        for parameter in &signature.parameters {
            let value = object.get(&parameter.name).ok_or(Error::Response)?;
            validate_witness_argument(&parameter.type_token, value, registry)?;
        }
        if let Some(key) = &signature.private_key {
            self.grant(&signature.capability, &signature.operation, Some(key))?;
        }
        self.grant(&signature.capability, &signature.operation, None)?;
        self.count_request()?;
        self.pending = Some(Pending::TypedProvider {
            id,
            input: input.to_owned(),
            signature: signature.clone(),
            arguments: arguments.clone(),
        });
        if self.private_size()? > self.context.limits.private_bytes {
            self.pending = None;
            return Err(Error::Limit.into());
        }
        let args = signature
            .parameters
            .iter()
            .map(|parameter| {
                json!({
                    "name": parameter.name,
                    "type": parameter.type_token,
                })
            })
            .collect::<Vec<_>>();
        Ok(Some(json!({
            "protocolVersion": 2,
            "requestId": id.to_string(),
            "attemptId": self.lifecycle.attempt_id(),
            "name": signature.name,
            "operation": signature.operation,
            "capability": signature.capability,
            "schema": signature.result_type,
            "arguments": args,
        })))
    }

    pub fn finish_typed_input(
        &mut self,
        input: &str,
        id: u64,
        attempt_id: Option<&str>,
        operation: Option<&str>,
        capability: Option<&str>,
        schema: Option<&str>,
        value: &Json,
        registry: &Registry,
    ) -> Result<Json> {
        let Some(Pending::TypedProvider {
            id: expected,
            input: pending_input,
            signature,
            ..
        }) = self.pending.as_ref()
        else {
            return Err(Error::State.into());
        };
        require(*expected == id && pending_input == input, Error::Response)?;
        require(
            attempt_id == Some(self.lifecycle.attempt_id()),
            Error::Response,
        )?;
        require(
            operation == Some(signature.operation.as_str())
                && capability == Some(signature.capability.as_str())
                && schema == Some(signature.result_type.as_str()),
            Error::Response,
        )?;
        require(
            serialized_json_len(value, Error::Response)? <= self.context.limits.private_bytes,
            Error::Limit,
        )?;
        registry
            .validate(&signature.result_type, value)
            .map_err(|_| Error::Response)?;
        if signature.operation == READ {
            let key = signature.private_key.as_ref().ok_or(Error::Descriptor)?;
            if let Some(write) = self.writes.get(key) {
                require(
                    write.ty == signature.result_type && write.value == *value,
                    Error::Response,
                )?;
            }
        }
        let result = value.clone();
        self.pending = None;
        Ok(result)
    }

    pub fn stage_typed(&mut self, stage: Stage, registry: &Registry) -> Result<()> {
        require(self.lifecycle.phase() == Phase::Open, Error::State)?;
        require(
            stage.abi_version == 2 && stage.operation == STAGE && key(&stage.key, false),
            Error::Descriptor,
        )?;
        self.grant(&stage.capability, STAGE, Some(&stage.key))?;
        self.grant(&self.context.commit_capability, CAS, Some(&stage.key))?;
        require(
            serialized_json_len(&stage.value, Error::Response)?
                <= self.context.limits.private_bytes,
            Error::Limit,
        )?;
        registry
            .validate(&stage.ty, &stage.value)
            .map_err(|_| Error::Response)?;
        require(
            self.writes.contains_key(&stage.key) || self.writes.len() < self.context.limits.writes,
            Error::Limit,
        )?;
        let old = self.writes.insert(
            stage.key.clone(),
            Write {
                ty: stage.ty,
                value: stage.value,
            },
        );
        if self.private_size()? > self.context.limits.private_bytes {
            self.writes.remove(&stage.key);
            if let Some(old) = old {
                self.writes.insert(stage.key, old);
            }
            return Err(Error::Limit.into());
        }
        if let Some(mut old) = old {
            wipe(&mut old.value);
        }
        Ok(())
    }

    pub(crate) fn has_target(&self, target: &str, entrypoint: &str) -> bool {
        self.target == target && self.entrypoint == entrypoint
    }

    pub fn finish_input(
        &mut self,
        input: &str,
        id: u64,
        operation: Option<&str>,
        capability: Option<&str>,
        schema: Option<&str>,
        value: &Json,
    ) -> Result<()> {
        if self.provider(input).is_none() {
            return require(
                operation.is_none() && capability.is_none() && schema.is_none(),
                Error::Response,
            );
        }
        let Some(Pending::Provider {
            id: expected,
            input: pending,
        }) = &self.pending
        else {
            return Err(Error::State);
        };
        require(*expected == id && pending == input, Error::Response)?;
        let provider = self.provider(input).ok_or(Error::State)?;
        let descriptor = self.descriptor(&provider.operation)?;
        require(
            operation == Some(provider.operation.as_str())
                && capability == Some(provider.capability.as_str())
                && schema == Some(descriptor.result_schema.as_str()),
            Error::Response,
        )?;
        input_value(&descriptor.result_schema, value).map_err(|_| Error::Response)?;
        self.pending = None;
        Ok(())
    }
    pub fn stage(&mut self, stage: Stage) -> Result<()> {
        require(self.lifecycle.phase() == Phase::Open, Error::State)?;
        require(
            stage.abi_version == 1 && stage.operation == STAGE && key(&stage.key, false),
            Error::Descriptor,
        )?;
        self.grant(&stage.capability, STAGE, Some(&stage.key))?;
        self.grant(&self.context.commit_capability, CAS, Some(&stage.key))?;
        input_value(&stage.ty, &stage.value).map_err(|_| Error::Response)?;
        require(
            self.writes.contains_key(&stage.key) || self.writes.len() < self.context.limits.writes,
            Error::Limit,
        )?;
        let old = self.writes.insert(
            stage.key.clone(),
            Write {
                ty: stage.ty,
                value: stage.value,
            },
        );
        if self.private_size()? > self.context.limits.private_bytes {
            self.writes.remove(&stage.key);
            if let Some(old) = old {
                self.writes.insert(stage.key, old);
            }
            return Err(Error::Limit);
        }
        Ok(())
    }
    fn effect(&mut self, effect: Effect) {
        if effect == Effect::DropJournal {
            self.clear_writes();
            self.pending = None;
        }
    }
    fn clear_writes(&mut self) {
        for (mut key, write) in std::mem::take(&mut self.writes) {
            key.zeroize();
            drop(write);
        }
    }
    pub fn execution_finished(&mut self, success: bool) -> Result<()> {
        let effect = self
            .lifecycle
            .apply(if success {
                Event::ExecutionSucceeded
            } else {
                Event::ExecutionFailed
            })
            .map_err(|_| Error::State)?;
        self.effect(effect);
        require(self.lifecycle.invariant(), Error::State)
    }
    pub fn cancel(&mut self) -> Result<()> {
        let effect = self
            .lifecycle
            .apply(Event::Cancel)
            .map_err(|_| Error::State)?;
        self.effect(effect);
        self.pending = None;
        Ok(())
    }
    pub fn notify(&mut self, notice: Notice) -> Result<bool> {
        require(notice.abi_version == 1, Error::Response)?;
        let binding = notice.event == "bind";
        let event = match notice.event.as_str() {
            "bind" => {
                require(
                    notice.attempt_id == self.lifecycle.attempt_id(),
                    Error::Response,
                )?;
                Event::Bind {
                    transaction_id: notice.transaction_id,
                }
            }
            "persisted" => Event::Persisted {
                transaction_id: notice.transaction_id,
                attempt_id: notice.attempt_id,
            },
            "submitted" => Event::Submitted {
                transaction_id: notice.transaction_id,
                attempt_id: notice.attempt_id,
            },
            "accepted" => Event::Accepted {
                transaction_id: notice.transaction_id,
                attempt_id: notice.attempt_id,
            },
            "partially_accepted" => Event::PartiallyAccepted {
                transaction_id: notice.transaction_id,
                attempt_id: notice.attempt_id,
            },
            "rejected" => Event::Rejected {
                transaction_id: notice.transaction_id,
                attempt_id: notice.attempt_id,
            },
            "uncertain" => Event::Uncertain {
                transaction_id: notice.transaction_id,
                attempt_id: notice.attempt_id,
            },
            _ => return Err(Error::Response),
        };
        let effect = self.lifecycle.apply(event).map_err(|_| Error::State)?;
        if binding {
            self.retained_journal_digest = Some(
                self.private_journal()?["journalDigest"]
                    .as_str()
                    .ok_or(Error::State)?
                    .to_owned(),
            );
        }
        let request = effect == Effect::RequestCas;
        self.effect(effect);
        require(self.lifecycle.invariant(), Error::State)?;
        Ok(request)
    }
    pub fn begin_cas(&mut self, id: u64) -> Result<()> {
        if matches!(self.pending, Some(Pending::Cas { .. })) {
            return Ok(());
        }
        require(
            self.lifecycle.phase() == Phase::AwaitingCas && self.pending.is_none(),
            Error::State,
        )?;
        self.count_request()?;
        self.pending = Some(Pending::Cas { id });
        Ok(())
    }
    pub fn cas_metadata(&self) -> Option<Json> {
        let Some(Pending::Cas { id }) = self.pending else {
            return None;
        };
        Some(
            json!({"id":id,"operation":CAS,"capability":self.context.commit_capability,"schema":CAS_SCHEMA,"hasPrivateArguments":true,"protocolVersion":1}),
        )
    }
    pub fn finish_cas(
        &mut self,
        id: u64,
        operation: Option<&str>,
        capability: Option<&str>,
        schema: Option<&str>,
        value: Json,
    ) -> Result<()> {
        let Some(Pending::Cas { id: expected }) = self.pending else {
            return Err(Error::State);
        };
        require(
            id == expected
                && operation == Some(CAS)
                && capability == Some(self.context.commit_capability.as_str())
                && schema == Some(CAS_SCHEMA),
            Error::Response,
        )?;
        let value: CasResponse = serde_json::from_value(value).map_err(|_| Error::Response)?;
        require(
            self.private_journal()?["journalDigest"].as_str()
                == Some(value.journal_digest.as_str()),
            Error::Response,
        )?;
        let transaction_id = value.transaction_id;
        let attempt_id = value.attempt_id;
        let completed = (value.outcome == "committed", value.revision.clone());
        let event = match value.outcome.as_str() {
            "committed" => Event::CasCommitted {
                transaction_id,
                attempt_id,
                base_revision: value.base_revision,
                revision: value.revision,
            },
            "conflict" => Event::CasConflict {
                transaction_id,
                attempt_id,
                base_revision: value.base_revision,
                revision: value.revision,
            },
            _ => return Err(Error::Response),
        };
        let effect = self.lifecycle.apply(event).map_err(|_| Error::Response)?;
        self.completed_cas = Some(completed);
        self.pending = None;
        self.effect(effect);
        require(self.lifecycle.invariant(), Error::State)
    }
    fn bounded(&self, value: Json) -> Result<Json> {
        require(
            serialized_json_len(&value, Error::Descriptor)? <= self.context.limits.private_bytes,
            Error::Limit,
        )?;
        Ok(value)
    }
    pub fn private_arguments(&self) -> Result<Json> {
        match &self.pending {
            Some(Pending::Provider { id, input }) => {
                let provider = self.provider(input).ok_or(Error::State)?;
                self.bounded(json!({"protocolVersion":1,"requestId":id,"namespace":self.context.namespace,"arguments":provider.arguments}))
            }
            Some(Pending::TypedProvider {
                id,
                signature,
                arguments,
                ..
            }) => {
                let mut private_arguments = arguments.clone();
                if let Some(key) = &signature.private_key {
                    private_arguments["key"] = Json::String(key.clone());
                }
                self.bounded(json!({
                    "protocolVersion":2,
                    "requestId":id.to_string(),
                    "attemptId":self.lifecycle.attempt_id(),
                    "namespace":self.context.namespace,
                    "name":signature.name,
                    "operation":signature.operation,
                    "capability":signature.capability,
                    "arguments":private_arguments
                }))
            }
            Some(Pending::Cas { id }) => self.bounded(
                json!({"protocolVersion":1,"requestId":id,"journal":self.private_journal()?}),
            ),
            None => Err(Error::State),
        }
    }
    pub fn private_journal(&self) -> Result<Json> {
        require(
            matches!(
                self.lifecycle.phase(),
                Phase::Prepared
                    | Phase::Submitted
                    | Phase::Uncertain
                    | Phase::AwaitingCas
                    | Phase::PartiallyAccepted
            ),
            Error::State,
        )?;
        let transaction = self.lifecycle.transaction_id().ok_or(Error::State)?;
        let writes: BTreeMap<_, _> = self
            .writes
            .iter()
            .map(|(key, write)| (key, json!({"type":write.ty,"value":write.value})))
            .collect();
        let mut journal = json!({"protocolVersion":1,"attemptId":self.lifecycle.attempt_id(),"transactionId":transaction,"namespace":self.context.namespace,"baseRevision":self.lifecycle.base_revision(),"contractAddress":self.target,"entrypoint":self.entrypoint,"writes":writes});
        // Root and write maps use lexical keys. Scalar write values have one canonical encoding.
        let canonical: BTreeMap<String, Json> =
            serde_json::from_value(journal.clone()).map_err(|_| Error::Descriptor)?;
        let mut bytes = serde_json::to_vec(&canonical).map_err(|_| Error::Descriptor)?;
        let mut hasher = Sha256::new();
        hasher.update(b"noctium.private-state-journal.v1\0");
        hasher.update(&bytes);
        journal["journalDigest"] = json!(hex::encode(hasher.finalize()));
        bytes.zeroize();
        self.bounded(journal)
    }
    pub fn public_status(&self) -> Json {
        let phase = match self.lifecycle.phase() {
            Phase::Open => "open",
            Phase::Prepared => "prepared",
            Phase::Submitted => "submitted",
            Phase::Uncertain => "uncertain",
            Phase::AwaitingCas => "awaiting_cas",
            Phase::PartiallyAccepted => "partially_accepted",
            Phase::Committed => "committed",
            Phase::Rejected => "rejected",
            Phase::Cancelled => "cancelled",
            Phase::Failed => "failed",
            Phase::Conflicted => "conflicted",
        };
        json!({"abiVersion":1,"status":"private_state","phase":phase,"acceptedHostEvidence":self.lifecycle.accepted_host_evidence(),"hostCasAcknowledged":self.lifecycle.phase()==Phase::Committed})
    }

    /// Export host-private constructor data for a durable typed execution handoff.
    /// The caller must keep this envelope with the private recovery record.
    pub fn recovery_context(&self) -> Result<Json> {
        require(
            self.lifecycle.phase() == Phase::Prepared && self.pending.is_none(),
            Error::State,
        )?;
        let context = serde_json::to_value(&self.context).map_err(|_| Error::Descriptor)?;
        let typed_schemas = match &self.registry {
            Some(registry) => registry.declarations().map_err(|_| Error::Descriptor)?,
            None => Vec::new(),
        };
        let value = json!({
            "recoveryVersion": 1,
            "context": context,
            "typed": self.registry.is_some(),
            "typedInputs": self.typed_inputs,
            "typedSchemas": typed_schemas,
            "target": self.target,
            "entrypoint": self.entrypoint,
        });
        let mut bytes = serde_json::to_vec(&value).map_err(|_| Error::Descriptor)?;
        let within_limit = bytes.len() <= MAX_RECOVERY_BYTES;
        bytes.zeroize();
        require(within_limit, Error::Limit)?;
        Ok(value)
    }

    pub fn typed_registry(&self) -> Option<&Registry> {
        self.registry.as_ref()
    }

    pub fn from_recovery_context(value: Json) -> Result<Self> {
        let mut bytes = serde_json::to_vec(&value).map_err(|_| Error::Descriptor)?;
        let within_limit = bytes.len() <= MAX_RECOVERY_BYTES;
        bytes.zeroize();
        require(within_limit, Error::Limit)?;
        let recovery: RecoveryContext =
            serde_json::from_value(value).map_err(|_| Error::Descriptor)?;
        require(recovery.recovery_version == 1, Error::Descriptor)?;
        if recovery.typed {
            let mut registry = Registry::default();
            require(
                recovery.typed_schemas.len() <= crate::witness::MAX_SCHEMAS,
                Error::Limit,
            )?;
            for declaration in recovery.typed_schemas {
                let schema =
                    serde_json::to_vec(&declaration.schema).map_err(|_| Error::Descriptor)?;
                registry
                    .register_json(&declaration.id, &schema)
                    .map_err(|_| Error::Descriptor)?;
            }
            Self::new_typed(
                recovery.context,
                &recovery.typed_inputs,
                recovery.target,
                recovery.entrypoint,
                &registry,
            )
        } else {
            require(
                recovery.typed_inputs.is_empty() && recovery.typed_schemas.is_empty(),
                Error::Descriptor,
            )?;
            let private_inputs = recovery
                .context
                .providers
                .iter()
                .map(|provider| {
                    let descriptor = recovery
                        .context
                        .operations
                        .iter()
                        .find(|operation| operation.operation == provider.operation)
                        .ok_or(Error::Descriptor)?;
                    Ok((provider.input.clone(), descriptor.result_schema.clone()))
                })
                .collect::<Result<BTreeMap<_, _>>>()?;
            Self::new(
                recovery.context,
                &private_inputs,
                recovery.target,
                recovery.entrypoint,
            )
        }
    }

    pub fn invariant(&self) -> bool {
        self.lifecycle.invariant()
    }
    pub(crate) fn matches_journal(
        &self,
        attempt: &str,
        transaction: &str,
        base: &str,
        target: &str,
        digest: &str,
    ) -> bool {
        self.lifecycle.attempt_id() == attempt
            && self.lifecycle.transaction_id() == Some(transaction)
            && self.lifecycle.base_revision() == base
            && self.target == target
            && self.retained_journal_digest.as_deref() == Some(digest)
    }
    pub(crate) fn matches_cas(&self, committed: bool, revision: &str) -> bool {
        self.completed_cas
            .as_ref()
            .is_some_and(|(outcome, actual)| *outcome == committed && actual == revision)
    }
}
impl Drop for Runtime {
    fn drop(&mut self) {
        self.clear_writes();
        for provider in &mut self.context.providers {
            provider.arguments.values_mut().for_each(wipe);
        }
    }
}
