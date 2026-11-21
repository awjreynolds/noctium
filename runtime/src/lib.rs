//! Native execution of the bounded Noctium plan schema. No process or JavaScript API.
use crate::aggregates::Schema;
use crate::zkir::IrSource;
use anyhow::{Context, Result, anyhow, bail, ensure};
use base_crypto::fab::{
    AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom, ValueSlice,
};
use base_crypto::hash::HashOutput;
use base_crypto::repr::BinaryHashRepr;
use coin_structure::coin::{
    Info as ShieldedCoinInfo, Nonce, PublicAddress, PublicKey, QualifiedInfo, ShieldedTokenType,
    TokenType, UnshieldedTokenType, UserAddress,
};
use coin_structure::contract::ContractAddress;
use coin_structure::transfer::{Recipient, SenderEvidence};
use ledger::{
    construct::{PreTranscript, partition_transcripts},
    structure::LedgerParameters,
};
use num_bigint::BigUint;
use onchain_runtime::result_mode::{GatherEvent, ResultModeGather};
use onchain_runtime::{
    context::QueryContext,
    ops::{Key, Op, VersionedLogItem},
    result_mode::ResultModeVerify,
    state::{ChargedState, StateValue},
    transcript::Transcript,
};
use serde::Deserialize;
use serde_json::Value as Json;
use sha2::{Digest, Sha256};
use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
};
use storage::{arena::Sp, db::InMemoryDB, storage::HashMap};
use transient_crypto::{
    curve::{EmbeddedFr, EmbeddedGroupAffine, Fr},
    fab::{AlignedValueExt, AlignmentExt, ValueReprAlignedValue},
    hash::transient_hash,
    merkle_tree::MerkleTree,
    proofs::{KeyLocation, ProofPreimage},
    repr::FieldRepr,
};

pub const LEDGER_REVISION: &str = "a2b30128ca4b660b73a068e29b56b48ede8c9a74";
pub const ZKIR_REVISION: &str = profile::REVISION;
pub const MAX_HASH_TO_CURVE_FIELDS: usize = 1024;
pub const MAX_TRANSIENT_HASH_FIELDS: usize = 1024;
pub const MODULUS: &str =
    "52435875175126190479447740508185965837690552500527637822603658699938581184513";
pub type Db = InMemoryDB;
pub type Program = Vec<Op<ResultModeVerify, Db>>;

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Native(Fr),
    Bool(bool),
    UInt {
        number: BigUint,
        maximum: BigUint,
    },
    Bytes(Vec<u8>),
    OpaqueBytes(Vec<u8>),
    JubjubScalar(EmbeddedFr),
    JubjubPoint(EmbeddedGroupAffine),
    #[cfg(feature = "zkir-321")]
    Foreign(foreign::ForeignValue),
}
impl Value {
    fn field(&self) -> Result<Fr> {
        match self {
            Self::Native(n) => Ok(*n),
            _ => bail!("expected Native value"),
        }
    }
    fn boolean(&self) -> Result<bool> {
        match self {
            Self::Bool(b) => Ok(*b),
            _ => bail!("expected Bool value"),
        }
    }
    fn jubjub_scalar(&self) -> Result<EmbeddedFr> {
        match self {
            Self::JubjubScalar(value) => Ok(*value),
            _ => bail!("expected JubjubScalar value"),
        }
    }
    fn jubjub_point(&self) -> Result<EmbeddedGroupAffine> {
        match self {
            Self::JubjubPoint(value) => Ok(*value),
            _ => bail!("expected JubjubPoint value"),
        }
    }
}
pub fn canonical_field(text: &str) -> Result<Fr> {
    ensure!(
        !text.is_empty()
            && text.len() <= MODULUS.len()
            && text.bytes().all(|b| b.is_ascii_digit())
            && (text == "0" || !text.starts_with('0')),
        "Native input must be a canonical decimal string"
    );
    let n =
        BigUint::parse_bytes(text.as_bytes(), 10).ok_or_else(|| anyhow!("invalid Native input"))?;
    ensure!(
        n < BigUint::parse_bytes(MODULUS.as_bytes(), 10).unwrap(),
        "Native input out of range"
    );
    Fr::from_le_bytes(&n.to_bytes_le()).ok_or_else(|| anyhow!("invalid Native encoding"))
}
pub fn field_decimal(n: Fr) -> String {
    BigUint::from_bytes_le(&n.as_le_bytes()).to_str_radix(10)
}
pub fn field_value(n: Fr) -> AlignedValue {
    AlignedValue {
        value: FabValue(vec![n.into()]),
        alignment: Alignment::singleton(AlignmentAtom::Field),
    }
}
fn aligned_bytes(value: &Value) -> Result<AlignedValue> {
    value.validate()?;
    let Value::Bytes(bytes) = value else {
        bail!("expected bytes value")
    };
    Ok(AlignedValue {
        value: FabValue(vec![ValueAtom::from(bytes.as_slice())]),
        alignment: Alignment::singleton(AlignmentAtom::Bytes {
            length: bytes.len() as u32,
        }),
    })
}

fn aligned_opaque_bytes(value: &Value) -> Result<AlignedValue> {
    value.validate()?;
    let Value::OpaqueBytes(bytes) = value else {
        bail!("expected opaque bytes value")
    };
    AlignedValue::new(
        FabValue(vec![ValueAtom(bytes.clone())]),
        Alignment::singleton(AlignmentAtom::Compress),
    )
    .ok_or_else(|| anyhow!("invalid opaque byte alignment"))
}

fn claim_hash_output(value: Value, label: &str) -> Result<HashOutput> {
    let Value::Bytes(bytes) = value else {
        bail!("{label} must be Bytes32")
    };
    ensure!(bytes.len() == 32, "{label} must be Bytes32");
    let bytes: [u8; 32] = bytes
        .try_into()
        .map_err(|_| anyhow!("{label} must be Bytes32"))?;
    Ok(HashOutput(bytes))
}

fn byte_alignment_length(alignment: &str) -> Result<Option<usize>> {
    if alignment == "bytes32" {
        return Ok(Some(32));
    }
    let Some(length) = alignment.strip_prefix("bytes:") else {
        return Ok(None);
    };
    ensure!(
        !length.is_empty()
            && length.bytes().all(|byte| byte.is_ascii_digit())
            && (length == "0" || !length.starts_with('0')),
        "noncanonical byte alignment length"
    );
    let length = length.parse::<usize>()?;
    ensure!(
        length <= scalars::MAX_BYTES_LENGTH && length != 32,
        "byte alignment length outside the source limit"
    );
    Ok(Some(length))
}

pub(crate) fn byte_projection_bindings(name: &str, length: usize) -> Result<Vec<(String, String)>> {
    ensure!(
        length <= scalars::MAX_BYTES_LENGTH,
        "byte length exceeds compiler limit"
    );
    let chunks = length.div_ceil(31);
    (0..chunks)
        .map(|index| {
            let remainder = length % 31;
            let width = if index == 0 && remainder != 0 {
                remainder
            } else {
                31
            };
            let exclusive = BigUint::from(1u8) << (width * 8);
            Ok((
                format!("_noctium_bytes_{name}_{index}"),
                format!("UIntRange<{}>", exclusive.to_str_radix(10)),
            ))
        })
        .collect()
}

fn evaluated_bytes(value: &Expr, length: usize, env: &Environment) -> Result<Vec<u8>> {
    ensure!(
        length <= scalars::MAX_BYTES_LENGTH,
        "byte length exceeds compiler limit"
    );
    let Value::Bytes(bytes) = evaluate(value, env)? else {
        bail!("expected bytes value")
    };
    ensure!(bytes.len() == length, "byte operand length mismatch");
    Ok(bytes)
}

fn aligned(value: &Value, alignment: &str) -> Result<AlignedValue> {
    if let Some(length) = byte_alignment_length(alignment)? {
        let Value::Bytes(bytes) = value else {
            bail!("expected bytes value")
        };
        ensure!(bytes.len() == length, "byte alignment length mismatch");
        return aligned_bytes(value);
    }
    match alignment {
        "compress" => aligned_opaque_bytes(value),
        "field" => match value {
            #[cfg(feature = "zkir-321")]
            Value::Foreign(value) => Ok(aligned_fields(&value.encode()?)),
            _ => Ok(field_value(value.field_encoding()?)),
        },
        "bit" => Ok(AlignedValue {
            value: FabValue(vec![ValueAtom(if value.boolean()? {
                vec![1]
            } else {
                vec![]
            })]),
            alignment: Alignment::singleton(AlignmentAtom::Bytes { length: 1 }),
        }),
        "u64" => {
            let Value::UInt { number, maximum } = value else {
                bail!("counter alignment requires UInt64")
            };
            ensure!(
                *maximum == BigUint::from(u64::MAX),
                "counter alignment requires UInt64"
            );
            let number =
                u64::try_from(number.clone()).map_err(|_| anyhow!("counter value exceeds u64"))?;
            Ok(number.into())
        }
        _ => bail!("unsupported alignment"),
    }
}
#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(tag = "tag", rename_all = "lowercase", deny_unknown_fields)]
pub enum Expr {
    Constant {
        value: String,
    },
    #[cfg(feature = "zkir-321")]
    #[serde(rename = "foreignConstant")]
    ForeignConstant {
        #[serde(rename = "type")]
        ty: String,
        encoding: Vec<String>,
    },
    #[cfg(feature = "zkir-321")]
    #[serde(rename = "foreignUnary")]
    ForeignUnary {
        operation: String,
        value: Box<Expr>,
    },
    #[cfg(feature = "zkir-321")]
    #[serde(rename = "foreignBinary")]
    ForeignBinary {
        operation: String,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    #[cfg(feature = "zkir-321")]
    #[serde(rename = "foreignToBytes")]
    ForeignToBytes {
        value: Box<Expr>,
    },
    #[cfg(feature = "zkir-321")]
    #[serde(rename = "foreignFromBytes")]
    ForeignFromBytes {
        #[serde(rename = "type")]
        ty: String,
        length: usize,
        value: Box<Expr>,
    },
    Bool {
        value: bool,
    },
    Uint {
        maximum: String,
        value: String,
    },
    Uadd {
        left: Box<Expr>,
        right: Box<Expr>,
        maximum: String,
    },
    Usub {
        left: Box<Expr>,
        right: Box<Expr>,
        maximum: String,
    },
    Umul {
        left: Box<Expr>,
        right: Box<Expr>,
        maximum: String,
    },
    Sub {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Inv {
        value: Box<Expr>,
    },
    #[serde(rename = "toBytes32")]
    ToBytes32 {
        value: Box<Expr>,
    },
    #[serde(rename = "reverseBytes32")]
    ReverseBytes32 {
        value: Box<Expr>,
    },
    #[serde(rename = "bytesLiteral")]
    BytesLiteral {
        length: usize,
        values: Vec<u8>,
    },
    #[serde(rename = "reverseBytes")]
    ReverseBytes {
        length: usize,
        value: Box<Expr>,
    },
    Sha256 {
        length: usize,
        value: Box<Expr>,
    },
    Sha512 {
        length: usize,
        value: Box<Expr>,
    },
    Keccak256 {
        length: usize,
        value: Box<Expr>,
    },
    #[serde(rename = "keccak256Secp256k1Point")]
    Keccak256Secp256k1Point {
        value: Box<Expr>,
    },
    #[serde(rename = "sliceBytes")]
    SliceBytes {
        length: usize,
        value: Box<Expr>,
        start: usize,
        end: usize,
    },
    #[serde(rename = "concatBytes")]
    ConcatBytes {
        #[serde(rename = "leftLength")]
        left_length: usize,
        #[serde(rename = "rightLength")]
        right_length: usize,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    #[serde(rename = "fromBytes32")]
    FromBytes32 {
        #[serde(rename = "type")]
        ty: String,
        value: Box<Expr>,
    },
    #[serde(rename = "fromBytes")]
    FromBytes {
        #[serde(rename = "type")]
        ty: String,
        length: usize,
        value: Box<Expr>,
    },
    Cast {
        #[serde(rename = "type")]
        ty: String,
        value: Box<Expr>,
    },
    Reference {
        name: String,
    },
    #[serde(rename = "byteAt")]
    ByteAt {
        value: Box<Expr>,
        index: usize,
    },
    #[serde(rename = "bytesField")]
    BytesField {
        value: Box<Expr>,
        index: usize,
    },
    #[cfg(feature = "zkir-321")]
    #[serde(rename = "foreignEncodedField")]
    ForeignEncodedField {
        value: Box<Expr>,
        index: usize,
    },
    #[serde(rename = "persistentHash32")]
    PersistentHash32 {
        value: Box<Expr>,
    },
    #[serde(rename = "bytes32Literal")]
    Bytes32Literal {
        values: Vec<u8>,
    },
    #[serde(rename = "persistentHashVector32")]
    PersistentHashVector32 {
        values: Vec<Expr>,
    },
    #[serde(rename = "persistentHashNative")]
    PersistentHashNative {
        value: Box<Expr>,
    },
    #[serde(rename = "persistentHashNativeVector")]
    PersistentHashNativeVector {
        values: Vec<Expr>,
    },
    #[serde(rename = "transientHash")]
    TransientHash {
        values: Vec<Expr>,
    },
    #[serde(rename = "hashToCurve")]
    HashToCurve {
        values: Vec<Expr>,
    },
    #[serde(rename = "jubjubScalarFromNative")]
    JubjubScalarFromNative {
        value: Box<Expr>,
    },
    #[serde(rename = "jubjubScalarToNative")]
    JubjubScalarToNative {
        value: Box<Expr>,
    },
    #[serde(rename = "jubjubMulGenerator")]
    JubjubMulGenerator {
        scalar: Box<Expr>,
    },
    #[serde(rename = "jubjubMul")]
    JubjubMul {
        point: Box<Expr>,
        scalar: Box<Expr>,
    },
    #[serde(rename = "jubjubAdd")]
    JubjubAdd {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    #[serde(rename = "jubjubNeg")]
    JubjubNeg {
        point: Box<Expr>,
    },
    #[serde(rename = "jubjubCoordinate")]
    JubjubCoordinate {
        point: Box<Expr>,
        index: usize,
    },
    #[serde(rename = "jubjubFromCoordinates")]
    JubjubFromCoordinates {
        x: Box<Expr>,
        y: Box<Expr>,
    },
    Let {
        name: String,
        value: Box<Expr>,
        body: Box<Expr>,
    },
    Lets {
        bindings: Vec<(String, Expr)>,
        body: Box<Expr>,
    },
    #[serde(rename = "assertThen")]
    AssertThen {
        condition: Box<Expr>,
        body: Box<Expr>,
    },
    Add {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Mul {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Eq {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    #[serde(rename = "boolAnd")]
    BoolAnd {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    #[serde(rename = "boolOr")]
    BoolOr {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    #[serde(rename = "boolXor")]
    BoolXor {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Select {
        condition: Box<Expr>,
        yes: Box<Expr>,
        no: Box<Expr>,
    },
    Poseidon2 {
        domain: String,
        left: Box<Expr>,
        right: Box<Expr>,
    },
}
pub type Environment = BTreeMap<String, Value>;

#[derive(Debug)]
struct UnboundReference(String);

impl std::fmt::Display for UnboundReference {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "unbound reference '{}'", self.0)
    }
}

impl std::error::Error for UnboundReference {}

fn unbound_reference(error: &anyhow::Error) -> Option<&str> {
    error
        .downcast_ref::<UnboundReference>()
        .map(|error| error.0.as_str())
}
fn persistent_hash(value: AlignedValue) -> Result<Value> {
    let mut fields = Vec::new();
    value.value_only_field_repr(&mut fields);
    let decoded = value
        .alignment
        .parse_field_repr(&fields)
        .ok_or_else(|| anyhow!("invalid persistent hash alignment"))?;
    let mut bytes = zeroize::Zeroizing::new(Vec::new());
    ValueReprAlignedValue(decoded).binary_repr(&mut *bytes);
    Ok(Value::Bytes(Sha256::digest(bytes.as_slice()).to_vec()))
}

pub fn evaluate(expr: &Expr, env: &Environment) -> Result<Value> {
    let result = match expr {
        Expr::Uint { maximum, value } => scalars::unsigned_literal(maximum, value)?,
        Expr::Uadd {
            left,
            right,
            maximum,
        } => scalars::unsigned_arithmetic(
            scalars::UnsignedOp::Add,
            evaluate(left, env)?,
            evaluate(right, env)?,
            maximum,
        )?,
        Expr::Usub {
            left,
            right,
            maximum,
        } => scalars::unsigned_arithmetic(
            scalars::UnsignedOp::Sub,
            evaluate(left, env)?,
            evaluate(right, env)?,
            maximum,
        )?,
        Expr::Umul {
            left,
            right,
            maximum,
        } => scalars::unsigned_arithmetic(
            scalars::UnsignedOp::Mul,
            evaluate(left, env)?,
            evaluate(right, env)?,
            maximum,
        )?,
        Expr::Let { name, value, body } => {
            let value = evaluate(value, env)?;
            let mut local = env.clone();
            local.insert(name.clone(), value);
            evaluate(body, &local)?
        }
        Expr::Lets { bindings, body } => {
            let mut local = env.clone();
            for (name, value) in bindings {
                let value = evaluate(value, &local)?;
                local.insert(name.clone(), value);
            }
            evaluate(body, &local)?
        }
        Expr::AssertThen { condition, body } => {
            ensure!(
                evaluate(condition, env)?.boolean()?,
                "helper assertion failed"
            );
            evaluate(body, env)?
        }
        Expr::Cast { ty, value } => evaluate(value, env)?.cast(&ScalarType::parse(ty)?)?,
        Expr::Sub { left, right } => {
            Value::Native(evaluate(left, env)?.field()? - evaluate(right, env)?.field()?)
        }
        Expr::Constant { value } => Value::Native(canonical_field(value)?),
        #[cfg(feature = "zkir-321")]
        Expr::ForeignConstant { ty, encoding } => {
            let ScalarType::Foreign(ty) = ScalarType::parse(ty)? else {
                bail!("foreign constant requires a foreign source type")
            };
            ensure!(
                encoding.len() == ty.native_type().encoded_len(),
                "wrong native field count for foreign constant"
            );
            let encoded = encoding
                .iter()
                .map(|field| canonical_field(field))
                .collect::<Result<Vec<_>>>()?;
            Value::Foreign(foreign::ForeignValue::decode(ty, &encoded)?)
        }
        #[cfg(feature = "zkir-321")]
        Expr::ForeignUnary { operation, value } => {
            let Value::Foreign(value) = evaluate(value, env)? else {
                bail!("foreign unary operation requires a foreign value")
            };
            Value::Foreign(value.unary(foreign::ForeignUnaryOp::parse(operation)?)?)
        }
        #[cfg(feature = "zkir-321")]
        Expr::ForeignBinary {
            operation,
            left,
            right,
        } => {
            let Value::Foreign(left) = evaluate(left, env)? else {
                bail!("foreign binary operation requires foreign operands")
            };
            let Value::Foreign(right) = evaluate(right, env)? else {
                bail!("foreign binary operation requires foreign operands")
            };
            Value::Foreign(left.binary(foreign::ForeignBinaryOp::parse(operation)?, &right)?)
        }
        #[cfg(feature = "zkir-321")]
        Expr::ForeignToBytes { value } => {
            let Value::Foreign(value) = evaluate(value, env)? else {
                bail!("foreign ToBytes requires a foreign value")
            };
            Value::Bytes(value.to_bytes()?)
        }
        #[cfg(feature = "zkir-321")]
        Expr::ForeignFromBytes { ty, length, value } => {
            ensure!(
                *length <= scalars::MAX_BYTES_LENGTH,
                "byte length exceeds compiler limit"
            );
            let ScalarType::Foreign(ty) = ScalarType::parse(ty)? else {
                bail!("foreign FromBytes requires a foreign source type")
            };
            let Value::Bytes(bytes) = evaluate(value, env)? else {
                bail!("foreign FromBytes requires bytes")
            };
            ensure!(
                bytes.len() == *length,
                "foreign byte operand length mismatch"
            );
            Value::Foreign(foreign::ForeignValue::from_bytes_reducing(ty, &bytes)?)
        }
        Expr::Bool { value } => Value::Bool(*value),
        Expr::Reference { name } => env
            .get(name)
            .cloned()
            .ok_or_else(|| anyhow::Error::new(UnboundReference(name.clone())))?,
        Expr::ByteAt { value, index } => {
            let Value::Bytes(bytes) = evaluate(value, env)? else {
                bail!("byte projection requires bytes")
            };
            let byte = bytes
                .get(*index)
                .ok_or_else(|| anyhow!("byte index out of range"))?;
            Value::UInt {
                number: BigUint::from(*byte),
                maximum: BigUint::from(255u16),
            }
        }
        Expr::BytesField { value, index } => {
            let value = aligned_bytes(&evaluate(value, env)?)?;
            let mut fields = Vec::new();
            value.value_only_field_repr(&mut fields);
            Value::Native(
                *fields
                    .get(*index)
                    .ok_or_else(|| anyhow!("byte field index out of range"))?,
            )
        }
        #[cfg(feature = "zkir-321")]
        Expr::ForeignEncodedField { value, index } => {
            let Value::Foreign(value) = evaluate(value, env)? else {
                bail!("foreign encoded field projection requires a foreign value")
            };
            let encoded = value.encode()?;
            Value::Native(
                *encoded
                    .get(*index)
                    .ok_or_else(|| anyhow!("foreign encoded field index out of range"))?,
            )
        }
        Expr::Bytes32Literal { values } => {
            ensure!(
                values.len() == 32,
                "Bytes32 literal must contain exactly 32 bytes"
            );
            Value::Bytes(values.clone())
        }
        Expr::BytesLiteral { length, values } => {
            ensure!(
                *length <= scalars::MAX_BYTES_LENGTH,
                "byte length exceeds compiler limit"
            );
            ensure!(values.len() == *length, "byte literal length mismatch");
            Value::Bytes(values.clone())
        }
        Expr::PersistentHash32 { value } => {
            persistent_hash(aligned(&evaluate(value, env)?, "bytes32")?)?
        }
        Expr::PersistentHashVector32 { values } => {
            ensure!(
                (1..=32).contains(&values.len()),
                "persistent hash vector must contain 1 to 32 Bytes32 values"
            );
            let parts = values
                .iter()
                .map(|value| aligned(&evaluate(value, env)?, "bytes32"))
                .collect::<Result<Vec<_>>>()?;
            persistent_hash(AlignedValue::concat(&parts))?
        }
        Expr::PersistentHashNative { value } => {
            persistent_hash(field_value(evaluate(value, env)?.field()?))?
        }
        Expr::PersistentHashNativeVector { values } => {
            ensure!(
                (1..=32).contains(&values.len()),
                "Native persistent hash vector must contain 1 to 32 fields"
            );
            let parts = values
                .iter()
                .map(|value| Ok(field_value(evaluate(value, env)?.field()?)))
                .collect::<Result<Vec<_>>>()?;
            persistent_hash(AlignedValue::concat(&parts))?
        }
        Expr::TransientHash { values } => {
            ensure!(
                values.len() <= MAX_TRANSIENT_HASH_FIELDS,
                "transient hash field vector exceeds compiler limit"
            );
            let fields = values
                .iter()
                .map(|value| evaluate(value, env)?.field())
                .collect::<Result<Vec<_>>>()?;
            Value::Native(transient_hash(&fields))
        }
        Expr::HashToCurve { values } => {
            ensure!(
                values.len() <= MAX_HASH_TO_CURVE_FIELDS,
                "hash-to-curve field vector exceeds compiler limit"
            );
            let fields = values
                .iter()
                .map(|value| evaluate(value, env)?.field())
                .collect::<Result<Vec<_>>>()?;
            Value::JubjubPoint(transient_crypto::hash::hash_to_curve(fields.as_slice()))
        }
        Expr::JubjubScalarFromNative { value } => {
            Value::JubjubScalar(jubjub::reduce_scalar(evaluate(value, env)?.field()?)?)
        }
        Expr::Inv { value } => match evaluate(value, env)? {
            Value::Native(value) => {
                ensure!(value != Fr::from(0u64), "cannot invert zero");
                Value::Native(Fr::from(1u64) / value)
            }
            Value::JubjubScalar(value) => {
                ensure!(value != EmbeddedFr::from(0u64), "cannot invert zero");
                Value::JubjubScalar(EmbeddedFr::from(1u64) / value)
            }
            _ => bail!("inverse requires Native or JubjubScalar"),
        },
        Expr::ToBytes32 { value } => Value::Bytes(match evaluate(value, env)? {
            Value::Native(value) => value.as_le_bytes(),
            Value::JubjubScalar(value) => value.as_le_bytes(),
            Value::JubjubPoint(value) => jubjub::to_bytes(value)?.to_vec(),
            _ => bail!("toBytes32 requires Native, JubjubScalar or JubjubPoint"),
        }),
        Expr::ReverseBytes32 { value } => {
            let Value::Bytes(mut bytes) = evaluate(value, env)? else {
                bail!("reverseBytes32 requires Bytes32")
            };
            ensure!(bytes.len() == 32, "reverseBytes32 requires 32 bytes");
            bytes.reverse();
            Value::Bytes(bytes)
        }
        Expr::ReverseBytes { length, value } => {
            let mut bytes = evaluated_bytes(value, *length, env)?;
            bytes.reverse();
            Value::Bytes(bytes)
        }
        Expr::Sha256 { length, value } => {
            let bytes = zeroize::Zeroizing::new(evaluated_bytes(value, *length, env)?);
            Value::Bytes(Sha256::digest(bytes.as_slice()).to_vec())
        }
        Expr::Sha512 { length, value } => {
            Value::Bytes(sha2::Sha512::digest(evaluated_bytes(value, *length, env)?).to_vec())
        }
        Expr::Keccak256 { length, value } => {
            Value::Bytes(sha3::Keccak256::digest(evaluated_bytes(value, *length, env)?).to_vec())
        }
        #[cfg(feature = "zkir-321")]
        Expr::Keccak256Secp256k1Point { value } => {
            let Value::Foreign(point) = evaluate(value, env)? else {
                bail!("keccak256Secp256k1Point requires a typed foreign point")
            };
            let expected = foreign::ForeignType::new(
                foreign::ForeignFamily::Secp256k1,
                foreign::ForeignRole::Point,
            );
            ensure!(
                point.foreign_type() == expected,
                "keccak256Secp256k1Point requires Secp256k1Point"
            );
            let encoded = point.encode()?;
            ensure!(
                encoded.len() == 5,
                "Secp256k1Point Encode must produce five fields"
            );
            let mut preimage = Vec::with_capacity(96);
            for (field, width) in encoded.iter().zip([24usize, 8, 24, 8, 32]) {
                let bytes = field.as_le_bytes();
                ensure!(
                    bytes[width..].iter().all(|byte| *byte == 0),
                    "Secp256k1Point Encode field exceeds its FAB alignment"
                );
                preimage.extend_from_slice(&bytes[..width]);
            }
            ensure!(
                preimage.len() == 96,
                "Secp256k1Point FAB preimage must be 96 bytes"
            );
            Value::Bytes(sha3::Keccak256::digest(preimage).to_vec())
        }
        #[cfg(not(feature = "zkir-321"))]
        Expr::Keccak256Secp256k1Point { .. } => {
            bail!("keccak256Secp256k1Point requires the ZKIR 3.2.1 runtime")
        }
        Expr::SliceBytes {
            length,
            value,
            start,
            end,
        } => {
            ensure!(
                start <= end && *end <= *length,
                "byte slice bounds are invalid"
            );
            let bytes = evaluated_bytes(value, *length, env)?;
            Value::Bytes(bytes[*start..*end].to_vec())
        }
        Expr::ConcatBytes {
            left_length,
            right_length,
            left,
            right,
        } => {
            ensure!(
                left_length
                    .checked_add(*right_length)
                    .is_some_and(|length| length <= scalars::MAX_BYTES_LENGTH),
                "concatenated byte length exceeds compiler limit"
            );
            let mut bytes = evaluated_bytes(left, *left_length, env)?;
            bytes.extend(evaluated_bytes(right, *right_length, env)?);
            Value::Bytes(bytes)
        }
        Expr::FromBytes32 { ty, value } => {
            let Value::Bytes(bytes) = evaluate(value, env)? else {
                bail!("fromBytes32 requires Bytes32")
            };
            ensure!(bytes.len() == 32, "fromBytes32 requires 32 bytes");
            match ScalarType::parse(ty)? {
                ScalarType::Native => {
                    let number = BigUint::from_bytes_le(&bytes)
                        % BigUint::parse_bytes(MODULUS.as_bytes(), 10).unwrap();
                    Value::Native(
                        Fr::from_le_bytes(&number.to_bytes_le())
                            .ok_or_else(|| anyhow!("invalid reduced Native encoding"))?,
                    )
                }
                ScalarType::JubjubScalar => Value::JubjubScalar(
                    EmbeddedFr::from_le_bytes_wide(&bytes)
                        .ok_or_else(|| anyhow!("invalid reduced Jubjub scalar encoding"))?,
                ),
                ScalarType::JubjubPoint => Value::JubjubPoint(jubjub::from_bytes(&bytes)?),
                _ => bail!("fromBytes32 requires Native, JubjubScalar or JubjubPoint"),
            }
        }
        Expr::FromBytes { ty, length, value } => {
            let value = evaluate(value, env)?;
            ensure!(
                *length <= scalars::MAX_BYTES_LENGTH,
                "byte length exceeds compiler limit"
            );
            let Value::Bytes(bytes) = value else {
                bail!("fromBytes requires bytes")
            };
            ensure!(bytes.len() == *length, "fromBytes operand length mismatch");
            match ScalarType::parse(ty)? {
                ScalarType::Native => {
                    let modulus = BigUint::parse_bytes(MODULUS.as_bytes(), 10).unwrap();
                    let number = BigUint::from_bytes_le(&bytes) % modulus;
                    Value::Native(canonical_field(&number.to_str_radix(10))?)
                }
                ScalarType::JubjubScalar => Value::JubjubScalar(jubjub::reduce_bytes(&bytes)?),
                _ => bail!("fromBytes requires Native or JubjubScalar"),
            }
        }
        Expr::JubjubScalarToNative { value } => Value::Native(jubjub::scalar_native(
            evaluate(value, env)?.jubjub_scalar()?,
        )?),
        Expr::JubjubMulGenerator { scalar } => Value::JubjubPoint(
            EmbeddedGroupAffine::generator() * evaluate(scalar, env)?.jubjub_scalar()?,
        ),
        Expr::JubjubMul { point, scalar } => Value::JubjubPoint(
            evaluate(point, env)?.jubjub_point()? * evaluate(scalar, env)?.jubjub_scalar()?,
        ),
        Expr::JubjubAdd { left, right } => Value::JubjubPoint(
            evaluate(left, env)?.jubjub_point()? + evaluate(right, env)?.jubjub_point()?,
        ),
        Expr::JubjubNeg { point } => Value::JubjubPoint(-evaluate(point, env)?.jubjub_point()?),
        Expr::JubjubCoordinate { point, index } => {
            let coordinates = jubjub::coordinates(evaluate(point, env)?.jubjub_point()?)?;
            Value::Native(
                *coordinates
                    .get(*index)
                    .ok_or_else(|| anyhow!("Jubjub coordinate index out of range"))?,
            )
        }
        Expr::JubjubFromCoordinates { x, y } => Value::JubjubPoint(jubjub::point(
            evaluate(x, env)?.field()?,
            evaluate(y, env)?.field()?,
        )?),
        Expr::Add { left, right } => {
            Value::Native(evaluate(left, env)?.field()? + evaluate(right, env)?.field()?)
        }
        Expr::Mul { left, right } => {
            Value::Native(evaluate(left, env)?.field()? * evaluate(right, env)?.field()?)
        }
        Expr::BoolAnd { left, right } => {
            let left = evaluate(left, env)?.boolean()?;
            let right = evaluate(right, env)?.boolean()?;
            Value::Bool(left && right)
        }
        Expr::BoolOr { left, right } => {
            let left = evaluate(left, env)?.boolean()?;
            let right = evaluate(right, env)?.boolean()?;
            Value::Bool(left || right)
        }
        Expr::BoolXor { left, right } => {
            let left = evaluate(left, env)?.boolean()?;
            let right = evaluate(right, env)?.boolean()?;
            Value::Bool(left ^ right)
        }
        Expr::Eq { left, right } => {
            let a = evaluate(left, env)?;
            let b = evaluate(right, env)?;
            ensure!(a.scalar_type() == b.scalar_type(), "equality type mismatch");
            Value::Bool(a == b)
        }
        Expr::Select { condition, yes, no } => {
            let c = evaluate(condition, env)?.boolean()?;
            let a = evaluate(yes, env)?;
            let b = evaluate(no, env)?;
            ensure!(
                a.scalar_type() == b.scalar_type(),
                "selection type mismatch"
            );
            if c { a } else { b }
        }
        Expr::Poseidon2 {
            domain,
            left,
            right,
        } => Value::Native(transient_hash(&[
            canonical_field(domain)?,
            evaluate(left, env)?.field()?,
            evaluate(right, env)?.field()?,
        ])),
    };
    result.validate()?;
    Ok(result)
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Plan {
    #[serde(default)]
    pub target: Option<String>,
    #[serde(default)]
    pub target_profile: Option<Json>,
    pub schema_version: u32,
    pub entrypoint: String,
    pub circuit: Circuit,
    pub state: Vec<StateDecl>,
    pub operations: Vec<Instruction>,
    pub reads: Vec<Read>,
    #[serde(default)]
    pub call_inputs: Vec<String>,
    #[serde(default)]
    pub returns: Vec<Output>,
    #[serde(default)]
    pub return_views: Vec<ReturnView>,
    #[serde(default)]
    pub constructor: Option<constructor::Constructor>,
}
#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ReturnView {
    pub name: String,
    pub schema: Json,
    pub fields: Vec<String>,
}
#[derive(Clone, Debug, Deserialize)]
pub struct Circuit {
    pub inputs: Vec<Input>,
    #[serde(default, rename = "sharedBindings")]
    pub shared_bindings: Vec<(String, Expr)>,
    pub outputs: Vec<Output>,
}
#[derive(Clone, Debug, Deserialize)]
pub struct Input {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    pub visibility: String,
}
#[derive(Clone, Debug, Deserialize)]
pub struct Output {
    pub visibility: String,
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    pub expression: Expr,
}
#[derive(Clone, Debug, Deserialize)]
pub struct StateDecl {
    pub name: String,
    pub kind: Json,
    #[serde(default)]
    pub sealed: bool,
}
#[derive(Clone, Debug, Deserialize)]
pub struct Read {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    #[serde(default)]
    pub guard: Option<Expr>,
    #[serde(default)]
    pub components: Vec<ReadComponent>,
    #[serde(default)]
    pub projections: Option<Vec<ReadComponent>>,
    #[serde(default)]
    pub schema: Option<Json>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum BalanceComparison {
    LessThan(Expr),
    GreaterThan(Expr),
}

impl BalanceComparison {
    fn limit(&self) -> &Expr {
        match self {
            Self::LessThan(limit) | Self::GreaterThan(limit) => limit,
        }
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReadComponent {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
}
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PathPart {
    pub alignment: String,
    pub expression: Expr,
}

/// A native counter immediate is either the historical numeric opcode
/// argument or a source-checked unsigned expression evaluated by the runtime.
#[derive(Clone, Debug, Deserialize)]
#[serde(untagged)]
pub enum ImmediateAmount {
    Literal(u32),
    Expression(Expr),
}

#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "op", rename_all = "lowercase", deny_unknown_fields)]
pub enum Instruction {
    Guarded {
        guard: Expr,
        operation: Box<Instruction>,
    },
    Dup,
    Checkpoint,
    Index {
        slot: u32,
        #[serde(rename = "pushPath")]
        push_path: bool,
        #[serde(default)]
        key: Option<Expr>,
    },
    #[serde(rename = "indexPath")]
    IndexPath {
        slot: u32,
        #[serde(rename = "pushPath")]
        push_path: bool,
        keys: Vec<PathPart>,
    },
    New,
    Push {
        storage: bool,
        expression: Expr,
        alignment: String,
    },
    #[serde(rename = "pushFields")]
    PushFields {
        storage: bool,
        expressions: Vec<Expr>,
        schema: Json,
    },
    Popeq {
        expression: Expr,
        alignment: String,
    },
    #[serde(rename = "popeqFields")]
    PopeqFields {
        expressions: Vec<Expr>,
        schema: Json,
    },
    Member,
    Insert {
        n: u8,
    },
    #[serde(rename = "listLength")]
    ListLength {
        slot: u32,
        keys: Vec<PathPart>,
        expression: Expr,
    },
    #[serde(rename = "mapSize")]
    MapSize {
        slot: u32,
        keys: Vec<PathPart>,
        expression: Expr,
    },
    #[serde(rename = "mapIsEmpty")]
    MapIsEmpty {
        slot: u32,
        keys: Vec<PathPart>,
        destination: String,
    },

    #[serde(rename = "merkleTreeIsFull")]
    MerkleTreeIsFull {
        slot: u32,
        #[serde(default)]
        keys: Vec<PathPart>,
        depth: u8,
        destination: String,
    },
    #[serde(rename = "merkleTreeCheckRoot")]
    MerkleTreeCheckRoot {
        slot: u32,
        #[serde(default)]
        keys: Vec<PathPart>,
        depth: u8,
        expected: Expr,
        destination: String,
    },
    #[serde(rename = "merkleTreeInsertHash")]
    MerkleTreeInsertHash {
        slot: u32,
        #[serde(default)]
        keys: Vec<PathPart>,
        depth: u8,
        hash: Expr,
    },
    #[serde(rename = "merkleTreeInsertHashIndex")]
    MerkleTreeInsertHashIndex {
        slot: u32,
        #[serde(default)]
        keys: Vec<PathPart>,
        depth: u8,
        hash: Expr,
        index: Expr,
    },
    #[serde(rename = "merkleTreeReset")]
    MerkleTreeReset {
        slot: u32,
        #[serde(default)]
        keys: Vec<PathPart>,
        depth: u8,
        #[serde(default, rename = "emptyHistory")]
        empty_history: bool,
    },
    #[serde(rename = "merkleTreeResetHistory")]
    MerkleTreeResetHistory {
        slot: u32,
        #[serde(default)]
        keys: Vec<PathPart>,
        depth: u8,
    },
    #[serde(rename = "listHead")]
    ListHead {
        slot: u32,
        keys: Vec<PathPart>,
        schema: Json,
        expressions: Vec<Expr>,
    },
    #[serde(rename = "listPushFront")]
    ListPushFront {
        slot: u32,
        keys: Vec<PathPart>,
        schema: Json,
        expressions: Vec<Expr>,
    },
    #[serde(rename = "listPopFront")]
    ListPopFront {
        slot: u32,
        keys: Vec<PathPart>,
    },
    #[serde(rename = "mapRemove")]
    MapRemove {
        slot: u32,
        keys: Vec<PathPart>,
    },
    #[serde(rename = "listReset")]
    ListReset {
        slot: u32,
        keys: Vec<PathPart>,
    },
    #[serde(rename = "addImmediate")]
    AddImmediate {
        amount: ImmediateAmount,
    },
    #[serde(rename = "subImmediate")]
    SubImmediate {
        amount: ImmediateAmount,
    },
    #[serde(rename = "claimcontractcall")]
    ClaimContractCall {
        address: Expr,
        #[serde(rename = "entryPointHash")]
        entry_point_hash: Expr,
        commitment: Expr,
    },
    #[serde(rename = "mintShielded")]
    MintShielded {
        domain: Expr,
        amount: Expr,
    },
    #[serde(rename = "mintUnshielded")]
    MintUnshielded {
        domain: Expr,
        amount: Expr,
    },
    #[serde(rename = "incUnshieldedOutputs", rename_all = "camelCase")]
    IncUnshieldedOutputs {
        color: Expr,
        amount: Expr,
        is_unshielded: Expr,
    },
    #[serde(rename = "incUnshieldedInputs", rename_all = "camelCase")]
    IncUnshieldedInputs {
        color: Expr,
        amount: Expr,
        is_unshielded: Expr,
    },
    #[serde(rename = "claimUnshieldedCoinSpend", rename_all = "camelCase")]
    ClaimUnshieldedCoinSpend {
        color: Expr,
        amount: Expr,
        is_unshielded: Expr,
        is_contract: Expr,
        recipient: Expr,
    },
    #[serde(rename = "receiveShieldedToMap", rename_all = "camelCase")]
    ReceiveShieldedToMap {
        slot: u32,
        nonce: Expr,
        color: Expr,
        amount: Expr,
        commitment: Expr,
    },
    #[serde(rename = "writeShieldedCoinCell", rename_all = "camelCase")]
    WriteShieldedCoinCell {
        slot: u32,
        nonce: Expr,
        color: Expr,
        amount: Expr,
        commitment: Expr,
    },
    #[serde(rename = "insertShieldedCoinSet", rename_all = "camelCase")]
    InsertShieldedCoinSet {
        slot: u32,
        nonce: Expr,
        color: Expr,
        amount: Expr,
        commitment: Expr,
    },
    #[serde(rename = "spendShieldedFromMap", rename_all = "camelCase")]
    SpendShieldedFromMap {
        nonce: Expr,
        color: Expr,
        amount: Expr,
        recipient: Expr,
        nullifier: Expr,
        #[serde(rename = "outputCommitment")]
        output_commitment: Expr,
    },
    #[serde(rename = "sendShieldedFromMap", rename_all = "camelCase")]
    SendShieldedFromMap {
        nonce: Expr,
        color: Expr,
        #[serde(rename = "inputAmount")]
        input_amount: Expr,
        #[serde(rename = "sendAmount")]
        send_amount: Expr,
        recipient: Expr,
        nullifier: Expr,
        #[serde(rename = "outputCommitment")]
        output_commitment: Expr,
        #[serde(rename = "changeCommitment")]
        change_commitment: Expr,
    },
    #[serde(rename = "relayShieldedImmediate", rename_all = "camelCase")]
    RelayShieldedImmediate {
        nonce: Expr,
        color: Expr,
        amount: Expr,
        recipient: Expr,
        #[serde(rename = "inputCommitment")]
        input_commitment: Expr,
        nullifier: Expr,
        #[serde(rename = "outputCommitment")]
        output_commitment: Expr,
    },
    #[serde(rename = "requireContractCaller")]
    RequireContractCaller {
        address: Expr,
    },
    #[serde(rename = "readCaller", rename_all = "camelCase")]
    ReadCaller {
        present: String,
        is_contract: String,
        contract_address: String,
        user_address: String,
    },
    #[serde(rename = "readContractAddress")]
    ReadContractAddress {
        destination: String,
    },
    #[serde(rename = "readTokenBalance", rename_all = "camelCase")]
    ReadTokenBalance {
        destination: String,
        color: Expr,
        is_unshielded: Expr,
        comparison: Option<BalanceComparison>,
    },
    #[serde(rename = "emitEvent")]
    EmitEvent {
        tag: u8,
        payload: Expr,
    },
    #[serde(rename = "blockTimeCompare")]
    BlockTimeCompare {
        destination: String,
        before: bool,
        deadline: Expr,
    },
    #[serde(rename = "counterLessThan")]
    CounterLessThan {
        slot: u32,
        keys: Vec<PathPart>,
        threshold: Expr,
        destination: String,
    },
}

fn evaluate_immediate_amount(amount: &ImmediateAmount, env: &Environment) -> Result<u32> {
    match amount {
        ImmediateAmount::Literal(amount) => Ok(*amount),
        ImmediateAmount::Expression(expression) => {
            let Value::UInt { number, maximum } = evaluate(expression, env)? else {
                bail!("counter adjustment amount must be unsigned")
            };
            ensure!(
                maximum <= BigUint::from(u32::MAX),
                "counter adjustment amount must be bounded by UInt32"
            );
            u32::try_from(number).map_err(|_| anyhow!("counter adjustment amount exceeds u32"))
        }
    }
}

fn event_payload_length(tag: u8) -> Result<usize> {
    match tag {
        0 => Ok(32),
        1 => Ok(578),
        2 => Ok(81),
        3 => Ok(49),
        4 | 5 => Ok(145),
        6 => Ok(80),
        7 => Ok(113),
        8 | 9 => Ok(0),
        10 => Ok(288),
        _ => bail!("unsupported native event tag"),
    }
}

fn path_field_count(plan: &Plan, slot: u32, keys: &[PathPart]) -> Result<usize> {
    let types = map_path_key_types(plan, slot, keys.len())?;
    let mut fields = 4;
    for (part, ty) in keys.iter().zip(types) {
        ensure!(
            part.alignment == key_alignment(&ty),
            "map path key alignment mismatch"
        );
        fields += ledger_key_aligned_field_count(&ty);
    }
    Ok(fields)
}

fn counter_path_field_count(plan: &Plan, slot: u32, keys: &[PathPart]) -> Result<usize> {
    let fields = path_field_count(plan, slot, keys)?;
    ensure!(
        tree_schema_at_path(plan, slot, keys.len())?.get("counter") == Some(&Json::Bool(true)),
        "counter comparison path schema mismatch"
    );
    Ok(fields)
}

fn validate_counter_adjustment_path<'a>(
    plan: &Plan,
    previous_index: Option<&'a (u32, Vec<AlignedValue>)>,
) -> Result<&'a (u32, Vec<AlignedValue>)> {
    let previous_index = previous_index
        .ok_or_else(|| anyhow!("counter adjustment requires a complete index path"))?;
    let (slot, keys) = previous_index;
    ensure!(
        tree_schema_at_path(plan, *slot, keys.len())?.get("counter") == Some(&Json::Bool(true)),
        "counter adjustment path schema mismatch"
    );
    Ok(previous_index)
}

pub(crate) fn ledger_key_type(value: &Json) -> Result<ScalarType> {
    let ty = ScalarType::parse(
        value
            .as_str()
            .ok_or_else(|| anyhow!("invalid ledger key schema"))?,
    )?;
    reject_jubjub_map_key(&ty)?;
    ensure!(
        !matches!(&ty, ScalarType::Bytes(_) | ScalarType::OpaqueBytes),
        "only fixed-width byte map keys are supported"
    );
    Ok(ty)
}

fn ledger_key_aligned_field_count(ty: &ScalarType) -> usize {
    match ty {
        ScalarType::Bytes32 => 4,
        #[cfg(feature = "zkir-321")]
        ScalarType::Foreign(ty) => 1 + 2 * ty.native_type().encoded_len(),
        _ => 3,
    }
}

fn validate_ledger_key_value(ty: &ScalarType, value: &Value) -> Result<()> {
    value.validate()?;
    #[cfg(feature = "zkir-321")]
    if matches!(ty, ScalarType::Foreign(_)) || matches!(value, Value::Foreign(_)) {
        ensure!(value.scalar_type() == *ty, "map key type mismatch");
    }
    let _ = ty;
    Ok(())
}

#[cfg(feature = "zkir-321")]
fn foreign_key_projection<'a>(expressions: &'a [Expr], ty: &ScalarType) -> Result<&'a Expr> {
    let ScalarType::Foreign(ty) = ty else {
        bail!("foreign key projections require a foreign type")
    };
    ensure!(
        expressions.len() == ty.native_type().encoded_len(),
        "typed foreign key field count mismatch"
    );
    let mut source = None;
    for (expected_index, expression) in expressions.iter().enumerate() {
        let Expr::ForeignEncodedField { value, index } = expression else {
            bail!("foreign key fields must use canonical foreign projections")
        };
        ensure!(
            *index == expected_index,
            "foreign key projections are not in canonical order"
        );
        if let Some(source) = source {
            ensure!(
                value.as_ref() == source,
                "foreign key projections use different source values"
            );
        } else {
            source = Some(value.as_ref());
        }
    }
    source.ok_or_else(|| anyhow!("foreign key requires encoded fields"))
}

#[cfg(feature = "zkir-321")]
fn validate_foreign_key_pushes(plan: &Plan) -> Result<()> {
    let mut previous_index = None;
    for operation in &plan.operations {
        let (instruction, guard) = match operation {
            Instruction::Guarded { guard, operation } => (operation.as_ref(), Some(guard)),
            operation => (operation, None),
        };
        match instruction {
            Instruction::Index {
                slot, key: None, ..
            } => previous_index = Some((*slot, 0, guard)),
            Instruction::IndexPath { slot, keys, .. } => {
                previous_index = Some((*slot, keys.len(), guard))
            }
            Instruction::PushFields {
                storage: false,
                expressions,
                schema,
                ..
            } => {
                if let Some(name) = typed_scalar_schema_token(schema) {
                    let ty = ScalarType::parse(name)?;
                    if matches!(&ty, ScalarType::Foreign(_)) {
                        foreign_key_projection(expressions, &ty)?;
                        let (slot, parents, index_guard) =
                            previous_index.take().ok_or_else(|| {
                                anyhow!("foreign map key push requires an indexed path")
                            })?;
                        ensure!(
                            index_guard == guard,
                            "foreign map key guard differs from its indexed path"
                        );
                        let expected = map_path_key_types(plan, slot, parents + 1)?
                            .pop()
                            .ok_or_else(|| anyhow!("invalid foreign map key schema"))?;
                        ensure!(
                            expected == ty,
                            "foreign map key type differs from state schema"
                        );
                    } else {
                        previous_index = None;
                    }
                } else {
                    previous_index = None;
                }
            }
            _ => previous_index = None,
        }
    }
    Ok(())
}

fn impact_field_counts(instruction: &Instruction, plan: &Plan) -> Result<Vec<usize>> {
    Ok(match instruction {
        Instruction::ListLength { slot, keys, .. } => {
            vec![1, path_field_count(plan, *slot, keys)?, 4, 4]
        }
        Instruction::MapSize { slot, keys, .. } => {
            validate_map_size_path(plan, *slot, keys.len())?;
            vec![1, path_field_count(plan, *slot, keys)?, 1, 4]
        }
        Instruction::MapIsEmpty { slot, keys, .. } => {
            validate_map_size_path(plan, *slot, keys.len())?;
            vec![1, path_field_count(plan, *slot, keys)?, 1, 5, 1, 4]
        }
        Instruction::ReceiveShieldedToMap { .. } => RECEIVE_SHIELDED_TO_MAP_FIELD_COUNTS.to_vec(),
        Instruction::WriteShieldedCoinCell { .. } => WRITE_SHIELDED_COIN_CELL_FIELD_COUNTS.to_vec(),
        Instruction::InsertShieldedCoinSet { slot, .. } => {
            validate_shielded_coin_set(plan, *slot)?;
            INSERT_SHIELDED_COIN_SET_FIELD_COUNTS.to_vec()
        }
        Instruction::SpendShieldedFromMap { .. } => SPEND_SHIELDED_FROM_MAP_FIELD_COUNTS.to_vec(),
        Instruction::SendShieldedFromMap { .. } => SEND_SHIELDED_FROM_MAP_FIELD_COUNTS.to_vec(),
        Instruction::RelayShieldedImmediate { .. } => {
            RELAY_SHIELDED_IMMEDIATE_FIELD_COUNTS.to_vec()
        }

        Instruction::MerkleTreeIsFull {
            slot, keys, depth, ..
        } => {
            ensure_merkle_tree_depth(plan, *slot, keys, *depth)?;
            vec![1, path_field_count(plan, *slot, keys)?, 4, 5, 1, 1, 4]
        }
        Instruction::MerkleTreeCheckRoot {
            slot, keys, depth, ..
        } => {
            let historic = ensure_merkle_tree_depth(plan, *slot, keys, *depth)?;
            let path = path_field_count(plan, *slot, keys)?;
            if historic {
                vec![1, path, 4, 5, 1, 4]
            } else {
                vec![1, path, 4, 1, 5, 1, 4]
            }
        }
        Instruction::MerkleTreeInsertHash {
            slot, keys, depth, ..
        } => {
            let historic = ensure_merkle_tree_depth(plan, *slot, keys, *depth)?;
            let path = path_field_count(plan, *slot, keys)?;
            let mut groups = vec![path, 4, 1, 4, 6, 1, 1, 4, 2, 1];
            if historic {
                groups.extend([4, 1, 4, 1, 2, 1, 1]);
            }
            groups
        }
        Instruction::MerkleTreeInsertHashIndex {
            slot, keys, depth, ..
        } => {
            let historic = ensure_merkle_tree_depth(plan, *slot, keys, *depth)?;
            let path = path_field_count(plan, *slot, keys)?;
            let mut groups = vec![path, 4, 5, 6, 1, 4, 5, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1];
            if historic {
                groups.extend([4, 1, 4, 1, 2, 1]);
            }
            groups.push(1);
            groups
        }
        Instruction::MerkleTreeReset {
            slot,
            keys,
            depth,
            empty_history,
        } => {
            let historic =
                ensure_merkle_tree_reset_mode(plan, *slot, keys, *depth, *empty_history)?;
            let default_fields =
                1 + merkle_tree_default_state(*depth, historic, *empty_history).field_size();
            if let Some((_, parents)) = keys.split_last() {
                let full = path_field_count(plan, *slot, keys)?;
                let parent = path_field_count(plan, *slot, parents)?;
                // The final key is a Push, with two more header fields than a path key.
                vec![parent, full - parent + 2, default_fields, 1]
            } else {
                vec![5, default_fields, 1]
            }
        }
        Instruction::MerkleTreeResetHistory { slot, keys, depth } => {
            ensure!(
                ensure_merkle_tree_depth(plan, *slot, keys, *depth)?,
                "resetHistory requires a historic MerkleTree"
            );
            vec![path_field_count(plan, *slot, keys)?, 5, 2, 1, 4, 1, 2, 1]
        }
        Instruction::ListHead {
            slot,
            keys,
            schema,
            expressions,
        }
        | Instruction::ListPushFront {
            slot,
            keys,
            schema,
            expressions,
        } => {
            let (popeq_width, push_width) =
                match list_operation_scalar_type(plan, *slot, keys, schema)? {
                    Some(ty) => {
                        ensure!(
                            expressions.len() == 1,
                            "scalar List operation requires one expression"
                        );
                        (
                            list_scalar_popeq_impact_width(&ty),
                            list_scalar_push_impact_width(&ty),
                        )
                    }
                    None => {
                        let parsed = checked_record_schema(schema)?;
                        ensure!(
                            expressions.len() == parsed.fields.len(),
                            "list record expression count mismatch"
                        );
                        (parsed.popeq_impact_width(), parsed.push_impact_width())
                    }
                };
            let path = path_field_count(plan, *slot, keys)?;
            if matches!(instruction, Instruction::ListHead { .. }) {
                vec![1, path, 4, popeq_width]
            } else {
                vec![path, 1, 4, 2, push_width + 3, 1, 5, 1, 1, 1, 5, 1, 1]
            }
        }
        Instruction::ListPopFront { slot, keys } => {
            vec![path_field_count(plan, *slot, keys)?, 1, 4, 2, 1, 4, 1]
        }
        Instruction::MapRemove { slot, keys } => {
            let (_, parents) = keys
                .split_last()
                .ok_or_else(|| anyhow!("map removal requires a key"))?;
            let full = path_field_count(plan, *slot, keys)?;
            let parent = path_field_count(plan, *slot, parents)?;
            vec![parent, 2 + full - parent, 1, 1]
        }
        Instruction::ListReset { slot, keys } => {
            if let Some((_, parents)) = keys.split_last() {
                let full = path_field_count(plan, *slot, keys)?;
                let parent = path_field_count(plan, *slot, parents)?;
                vec![parent, 2 + full - parent, 8, 1]
            } else {
                vec![5, 8, 1]
            }
        }
        Instruction::ClaimContractCall { .. } => vec![1, 4, 1, 1, 11, 2, 2, 1, 1],
        Instruction::MintShielded { .. } | Instruction::MintUnshielded { .. } => {
            MINT_FIELD_COUNTS.to_vec()
        }
        Instruction::IncUnshieldedOutputs { .. } | Instruction::IncUnshieldedInputs { .. } => {
            token_accumulation_fields(11).to_vec()
        }
        Instruction::ClaimUnshieldedCoinSpend { .. } => token_accumulation_fields(19).to_vec(),
        Instruction::RequireContractCaller { .. } => vec![1, 4, 10],
        Instruction::ReadCaller { .. } => vec![1, 4, 1, 1, 5, 1, 2, 5, 1, 2, 2, 1, 13, 12],
        Instruction::ReadContractAddress { .. } => vec![1, 4, 5],
        Instruction::ReadTokenBalance { comparison, .. } => {
            let mut counts = vec![1, 4, 1, 11, 1, 2, 1, 5, 2, 10];
            match comparison {
                None => counts.push(4),
                Some(BalanceComparison::LessThan(_)) => counts.extend([5, 1, 4]),
                Some(BalanceComparison::GreaterThan(_)) => {
                    counts.insert(0, 5);
                    counts.extend([1, 4]);
                }
            }
            counts
        }
        Instruction::EmitEvent { tag, .. } => {
            vec![13 + event_payload_length(*tag)?.div_ceil(31), 1]
        }
        Instruction::BlockTimeCompare { before, .. } => {
            if *before {
                vec![1, 4, 5, 1, 4]
            } else {
                vec![5, 1, 4, 1, 4]
            }
        }
        Instruction::CounterLessThan { slot, keys, .. } => {
            vec![1, counter_path_field_count(plan, *slot, keys)?, 5, 1, 4]
        }
        _ => vec![impact_field_count(instruction, plan)?],
    })
}

/// Number of transcript fields in one statically scheduled Impact group.
/// Inactive guarded writes use only this shape metadata, never their payloads.
fn impact_field_count(instruction: &Instruction, plan: &Plan) -> Result<usize> {
    let value_fields = |alignment: &str| -> Result<usize> {
        match alignment {
            "field" | "bit" | "u64" | "compress" => Ok(1),
            _ => match byte_alignment_length(alignment)? {
                Some(length) => Ok(length.div_ceil(31)),
                None => bail!("unsupported alignment"),
            },
        }
    };
    Ok(match instruction {
        Instruction::AddImmediate { .. } | Instruction::SubImmediate { .. } => 2,
        Instruction::ClaimContractCall { .. } => 24,
        Instruction::ReceiveShieldedToMap { .. } => {
            bail!("shielded receive must be unguarded")
        }
        Instruction::WriteShieldedCoinCell { .. } => {
            bail!("shielded coin Cell write must be unguarded")
        }
        Instruction::InsertShieldedCoinSet { .. } => {
            bail!("shielded coin Set insertion must be unguarded")
        }
        Instruction::SpendShieldedFromMap { .. } => {
            bail!("shielded spend must be unguarded")
        }
        Instruction::SendShieldedFromMap { .. } => {
            bail!("shielded send must be unguarded")
        }
        Instruction::RelayShieldedImmediate { .. } => {
            bail!("immediate shielded relay must be unguarded")
        }
        Instruction::MintShielded { .. } | Instruction::MintUnshielded { .. } => {
            impact_field_counts(instruction, plan)?.into_iter().sum()
        }
        Instruction::IncUnshieldedOutputs { .. }
        | Instruction::IncUnshieldedInputs { .. }
        | Instruction::ClaimUnshieldedCoinSpend { .. } => {
            impact_field_counts(instruction, plan)?.into_iter().sum()
        }
        Instruction::RequireContractCaller { .. } => 15,
        Instruction::ReadCaller { .. } => impact_field_counts(instruction, plan)?.into_iter().sum(),
        Instruction::ReadContractAddress { .. } => 10,
        Instruction::ReadTokenBalance { .. } => {
            impact_field_counts(instruction, plan)?.into_iter().sum()
        }
        Instruction::BlockTimeCompare { .. } => 15,
        Instruction::CounterLessThan { .. } => {
            impact_field_counts(instruction, plan)?.into_iter().sum()
        }
        Instruction::EmitEvent { .. } => impact_field_counts(instruction, plan)?.into_iter().sum(),
        Instruction::Dup
        | Instruction::Checkpoint
        | Instruction::Member
        | Instruction::Insert { .. }
        | Instruction::New => 1,
        Instruction::Index { key: None, .. } => 4,
        Instruction::Index {
            slot, key: Some(_), ..
        } => {
            let key_type = map_key_type(plan, *slot)?;
            4 + ledger_key_aligned_field_count(&key_type)
        }
        Instruction::IndexPath { slot, keys, .. } => path_field_count(plan, *slot, keys)?,
        Instruction::ListLength { .. }
        | Instruction::MapSize { .. }
        | Instruction::MapIsEmpty { .. }
        | Instruction::MerkleTreeIsFull { .. }
        | Instruction::MerkleTreeCheckRoot { .. }
        | Instruction::MerkleTreeInsertHash { .. }
        | Instruction::MerkleTreeInsertHashIndex { .. }
        | Instruction::MerkleTreeReset { .. }
        | Instruction::MerkleTreeResetHistory { .. }
        | Instruction::ListHead { .. }
        | Instruction::ListPushFront { .. }
        | Instruction::ListPopFront { .. }
        | Instruction::ListReset { .. }
        | Instruction::MapRemove { .. } => {
            impact_field_counts(instruction, plan)?.into_iter().sum()
        }
        Instruction::Push { alignment, .. } => 4 + value_fields(alignment)?,
        Instruction::Popeq { alignment, .. } => 3 + value_fields(alignment)?,
        Instruction::PushFields {
            expressions,
            schema,
            ..
        } => {
            if let Some(name) = typed_scalar_schema_token(schema) {
                let ty = ScalarType::parse(name)?;
                ensure!(
                    expressions.len() == typed_scalar_field_count(&ty)?,
                    "aligned value expression count mismatch"
                );
                3 + 2 * expressions.len()
            } else {
                let schema = checked_record_schema(schema)?;
                ensure!(
                    expressions.len() == schema.fields.len(),
                    "aligned value expression count mismatch"
                );
                schema.push_impact_width()
            }
        }
        Instruction::PopeqFields {
            expressions,
            schema,
        } => {
            if let Some(name) = typed_scalar_schema_token(schema) {
                let ty = ScalarType::parse(name)?;
                ensure!(
                    expressions.len() == typed_scalar_field_count(&ty)?,
                    "aligned value expression count mismatch"
                );
                2 + 2 * expressions.len()
            } else {
                let schema = checked_record_schema(schema)?;
                ensure!(
                    expressions.len() == schema.fields.len(),
                    "aligned value expression count mismatch"
                );
                schema.popeq_impact_width()
            }
        }
        Instruction::Guarded { .. } => bail!("nested guarded native operation is unsupported"),
    })
}

fn map_key_type(plan: &Plan, slot: u32) -> Result<ScalarType> {
    map_path_key_types(plan, slot, 1)?
        .pop()
        .ok_or_else(|| anyhow!("invalid map key schema"))
}

const MINT_FIELD_COUNTS: [usize; 16] = [1, 4, 6, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 1];
const RECEIVE_SHIELDED_TO_MAP_FIELD_COUNTS: [usize; 16] =
    [1, 4, 6, 2, 1, 1, 4, 6, 1, 6, 5, 11, 1, 2, 1, 1];
const WRITE_SHIELDED_COIN_CELL_FIELD_COUNTS: [usize; 8] = [5, 1, 6, 5, 11, 1, 2, 1];
const INSERT_SHIELDED_COIN_SET_FIELD_COUNTS: [usize; 10] = [4, 1, 6, 5, 11, 1, 2, 2, 1, 1];
const SPEND_SHIELDED_FROM_MAP_FIELD_COUNTS: [usize; 12] = [1, 4, 6, 2, 1, 1, 1, 4, 6, 2, 1, 1];
const SEND_SHIELDED_FROM_MAP_FIELD_COUNTS: [usize; 18] =
    [1, 4, 6, 2, 1, 1, 1, 4, 6, 2, 1, 1, 1, 4, 6, 2, 1, 1];
const RELAY_SHIELDED_IMMEDIATE_FIELD_COUNTS: [usize; 18] =
    [1, 4, 6, 2, 1, 1, 1, 4, 6, 2, 1, 1, 1, 4, 6, 2, 1, 1];

fn token_accumulation_fields(key_push: usize) -> [usize; 16] {
    [1, 4, key_push, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 1]
}

fn reject_unqualified_foreign_storage(ty: &ScalarType) -> Result<()> {
    #[cfg(feature = "zkir-321")]
    ensure!(
        !matches!(ty, ScalarType::Foreign(_)),
        "foreign ledger storage is unsupported"
    );
    #[cfg(not(feature = "zkir-321"))]
    let _ = ty;
    Ok(())
}

fn scalar_storage_type_at_path(plan: &Plan, slot: u32, depth: usize) -> Result<ScalarType> {
    let state = plan
        .state
        .get(slot as usize)
        .ok_or_else(|| anyhow!("state slot out of range"))?;
    let declared = if state.kind.get("tree").is_some() {
        tree_schema_at_path(plan, slot, depth)?
            .get("scalar")
            .and_then(Json::as_str)
            .ok_or_else(|| anyhow!("typed tree path does not select a scalar leaf"))?
    } else if let Some(ty) = state.kind.get("cell").and_then(Json::as_str) {
        ensure!(depth == 0, "typed cell path schema mismatch");
        ty
    } else if let Some(types) = state.kind.get("map").and_then(Json::as_array) {
        ensure!(
            depth == 1 && types.len() == 2,
            "typed map path schema mismatch"
        );
        types[1]
            .as_str()
            .ok_or_else(|| anyhow!("invalid map value schema"))?
    } else {
        bail!("typed ledger values require a scalar cell or map value")
    };
    ScalarType::parse(declared)
}

fn validate_scalar_storage_type(
    plan: &Plan,
    slot: u32,
    depth: usize,
    ty: &ScalarType,
) -> Result<()> {
    ensure!(
        scalar_storage_type_at_path(plan, slot, depth)? == *ty,
        "typed ledger type differs from state schema"
    );
    Ok(())
}

fn opaque_byte_storage_path(
    plan: &Plan,
    operation_index: usize,
    guard: Option<&Expr>,
) -> Result<(u32, usize)> {
    let key_operation = operation_index
        .checked_sub(1)
        .and_then(|index| plan.operations.get(index))
        .ok_or_else(|| anyhow!("opaque byte write has no indexed key push"))?;
    let (key_operation, key_guard) = unguarded_operation(key_operation);
    ensure!(
        key_guard == guard,
        "opaque byte key push guard differs from its write"
    );
    let Instruction::Push {
        storage: false,
        expression: _,
        alignment: key_alignment,
    } = key_operation
    else {
        bail!("opaque byte write requires an adjacent non-storage key push")
    };
    ensure!(
        key_alignment == "bytes32",
        "opaque byte map key push must use Bytes32 alignment"
    );

    let path_operation = operation_index
        .checked_sub(2)
        .and_then(|index| plan.operations.get(index))
        .ok_or_else(|| anyhow!("opaque byte write has no adjacent indexed path"))?;
    let (path_operation, path_guard) = unguarded_operation(path_operation);
    ensure!(
        path_guard == guard,
        "opaque byte indexed path guard differs from its write"
    );
    let Instruction::IndexPath {
        slot,
        push_path: true,
        keys,
    } = path_operation
    else {
        bail!("opaque byte write requires an adjacent indexed storage path")
    };
    ensure!(
        keys.is_empty(),
        "opaque byte write requires a direct Map root path"
    );
    let key_types = map_path_key_types(plan, *slot, 1)?;
    ensure!(
        key_types.len() == 1 && key_types[0] == ScalarType::Bytes32,
        "opaque byte Map key must be Bytes32"
    );
    let insert_operation = operation_index
        .checked_add(1)
        .and_then(|index| plan.operations.get(index))
        .ok_or_else(|| anyhow!("opaque byte write has no adjacent Map insertion"))?;
    let (insert_operation, insert_guard) = unguarded_operation(insert_operation);
    ensure!(
        insert_guard == guard
            && matches!(insert_operation, Instruction::Insert { n: 2 }),
        "opaque byte Map value push must be followed by Insert(2)"
    );
    Ok((*slot, 1))
}

fn reject_jubjub_map_key(ty: &ScalarType) -> Result<()> {
    ensure!(
        !matches!(ty, ScalarType::JubjubScalar | ScalarType::JubjubPoint),
        "Jubjub ledger values cannot be map keys"
    );
    Ok(())
}

fn map_path_key_types(plan: &Plan, slot: u32, count: usize) -> Result<Vec<ScalarType>> {
    ensure!(count < 16, "map path exceeds native index limit");
    let state = plan
        .state
        .get(slot as usize)
        .ok_or_else(|| anyhow!("state slot out of range"))?;
    if count == 0 {
        return Ok(Vec::new());
    }
    if let Some(mut schema) = state.kind.get("tree") {
        let mut types = Vec::with_capacity(count);
        for index in 0..count {
            if let Some(key) = schema.get("set") {
                ensure!(index + 1 == count, "a set key must end its path");
                types.push(ledger_key_type(key)?);
                break;
            }
            let parts = schema
                .get("map")
                .and_then(Json::as_array)
                .filter(|parts| parts.len() == 2)
                .ok_or_else(|| anyhow!("map path exceeds declared schema"))?;
            types.push(ledger_key_type(&parts[0])?);
            schema = &parts[1];
        }
        return Ok(types);
    }
    ensure!(count == 1, "scalar map has no nested path");
    let parts = state
        .kind
        .get("map")
        .and_then(Json::as_array)
        .filter(|parts| parts.len() == 2)
        .ok_or_else(|| anyhow!("invalid map key schema"))?;
    Ok(vec![ledger_key_type(&parts[0])?])
}

fn validate_tree_schema(schema: &Json, depth: usize) -> Result<()> {
    ensure!(depth <= 16, "state tree exceeds native path limit");
    let fields = schema
        .as_object()
        .ok_or_else(|| anyhow!("invalid state tree schema"))?;
    if fields.contains_key("merkleTree") {
        ensure!(
            (1..=12).contains(&depth),
            "invalid nested MerkleTree path depth"
        );
        checked_merkle_tree_schema(schema)?;
        return Ok(());
    }
    ensure!(fields.len() == 1, "invalid state tree schema");
    if fields.get("counter") == Some(&Json::Bool(true)) {
        return Ok(());
    }
    if let Some(element) = fields.get("list") {
        let parts = element
            .as_object()
            .ok_or_else(|| anyhow!("invalid list element schema"))?;
        ensure!(parts.len() == 1, "invalid list element schema");
        if let Some(ty) = parts.get("scalar").and_then(Json::as_str) {
            validate_tree_scalar_type(ty)?;
            return Ok(());
        }
        checked_record_schema(
            parts
                .get("composite")
                .ok_or_else(|| anyhow!("List requires a scalar or record element"))?,
        )?;
        return Ok(());
    }
    if let Some(ty) = fields.get("scalar").and_then(Json::as_str) {
        validate_tree_scalar_type(ty)?;
        return Ok(());
    }
    if let Some(schema) = fields.get("composite") {
        if is_shielded_coin_record_schema(schema) {
            return Ok(());
        }
        checked_record_schema(schema)?;
        return Ok(());
    }
    if let Some(key) = fields.get("set") {
        if let Some(record) = key
            .as_object()
            .filter(|object| object.len() == 1)
            .and_then(|object| object.get("composite"))
        {
            ensure!(
                is_shielded_coin_record_schema(record),
                "Set composite schema is unsupported"
            );
            checked_record_schema(record)?;
        } else {
            ledger_key_type(key)?;
        }
        return Ok(());
    }
    let parts = fields
        .get("map")
        .and_then(Json::as_array)
        .filter(|parts| parts.len() == 2)
        .ok_or_else(|| anyhow!("invalid state tree map schema"))?;
    ledger_key_type(&parts[0])?;
    validate_tree_schema(&parts[1], depth + 1)
}

fn is_shielded_coin_record_schema(schema: &Json) -> bool {
    let Some(object) = schema.as_object() else {
        return false;
    };
    if object.len() != 2 || !object.contains_key("id") || !object.contains_key("fields") {
        return false;
    }
    let Some(id) = object.get("id").and_then(Json::as_str) else {
        return false;
    };
    if !valid_record_identifier(id, true) {
        return false;
    }
    let Some(fields) = object.get("fields").and_then(Json::as_array) else {
        return false;
    };
    let expected = [
        ("nonce", "Bytes<32>"),
        ("color", "Bytes<32>"),
        (
            "value",
            "UIntRange<340282366920938463463374607431768211456>",
        ),
        ("mtIndex", "UIntRange<18446744073709551616>"),
    ];
    fields.len() == expected.len()
        && fields.iter().zip(expected).all(|(field, (name, ty))| {
            field.as_object().is_some_and(|field| {
                field.len() == 2
                    && field.get("name").and_then(Json::as_str) == Some(name)
                    && field.get("type").and_then(Json::as_str) == Some(ty)
            })
        })
}

fn validate_shielded_coin_map(plan: &Plan, slot: u32) -> Result<()> {
    ensure!(
        slot < 16,
        "shielded receive Map slot exceeds the native state limit"
    );
    let schema = tree_schema_at_path(plan, slot, 0)?;
    let object = schema
        .as_object()
        .ok_or_else(|| anyhow!("shielded receive requires a tree Map"))?;
    ensure!(
        object.len() == 1 && object.contains_key("map"),
        "shielded receive requires a root tree Map"
    );
    let parts = schema
        .get("map")
        .and_then(Json::as_array)
        .filter(|parts| parts.len() == 2)
        .ok_or_else(|| anyhow!("shielded receive requires a Bytes32-keyed Map"))?;
    ensure!(
        ledger_key_type(&parts[0])? == ScalarType::Bytes32,
        "shielded receive Map key must be Bytes32"
    );
    let value = parts[1]
        .as_object()
        .filter(|value| value.len() == 1)
        .and_then(|value| value.get("composite"))
        .ok_or_else(|| anyhow!("shielded receive Map value must be the coin record"))?;
    ensure!(
        is_shielded_coin_record_schema(value),
        "shielded receive Map must use the fixed coin record schema"
    );
    Ok(())
}

fn validate_shielded_coin_cell(plan: &Plan, slot: u32) -> Result<()> {
    let schema = tree_schema_at_path(plan, slot, 0)?;
    ensure!(
        !plan.state[slot as usize].sealed,
        "shielded coin Cell is sealed"
    );
    let record = schema
        .as_object()
        .filter(|object| object.len() == 1)
        .and_then(|object| object.get("composite"))
        .ok_or_else(|| anyhow!("shielded coin write requires a root composite Cell"))?;
    ensure!(
        is_shielded_coin_record_schema(record),
        "shielded coin Cell must use the fixed qualified coin record schema"
    );
    Ok(())
}

fn validate_shielded_coin_set(plan: &Plan, slot: u32) -> Result<()> {
    ensure!(
        plan.state.len() <= 16 && slot < 16,
        "shielded coin Set slot exceeds the native state limit"
    );
    let declaration = plan
        .state
        .get(slot as usize)
        .ok_or_else(|| anyhow!("shielded coin Set slot out of range"))?;
    ensure!(!declaration.sealed, "shielded coin Set is sealed");
    let schema = tree_schema_at_path(plan, slot, 0)?;
    let set = schema
        .as_object()
        .filter(|object| object.len() == 1)
        .and_then(|object| object.get("set"))
        .ok_or_else(|| anyhow!("shielded coin insertion requires a root Set"))?;
    let record = set
        .as_object()
        .filter(|object| object.len() == 1)
        .and_then(|object| object.get("composite"))
        .ok_or_else(|| anyhow!("shielded coin Set must store qualified coin records"))?;
    ensure!(
        is_shielded_coin_record_schema(record),
        "shielded coin Set must use the fixed qualified coin record schema"
    );
    Ok(())
}

fn validate_tree_scalar_type(ty: &str) -> Result<ScalarType> {
    let ty = ScalarType::parse(ty)?;
    #[cfg(feature = "zkir-321")]
    if !matches!(&ty, ScalarType::Foreign(_)) {
        reject_unqualified_foreign_storage(&ty)?;
    }
    #[cfg(not(feature = "zkir-321"))]
    reject_unqualified_foreign_storage(&ty)?;
    Ok(ty)
}

struct RecordField {
    name: Option<String>,
    ty: ScalarType,
}

struct CheckedRecordSchema {
    fields: Vec<RecordField>,
    aggregate: Option<aggregates::Schema>,
    shielded_coin: bool,
}

impl CheckedRecordSchema {
    fn alignment_atoms(&self) -> usize {
        self.fields
            .iter()
            .map(|field| {
                if field.ty == ScalarType::JubjubPoint {
                    2
                } else {
                    1
                }
            })
            .sum()
    }

    fn field_values(&self) -> usize {
        self.fields
            .iter()
            .map(|field| match &field.ty {
                ScalarType::Bytes32 | ScalarType::JubjubPoint => 2,
                _ => 1,
            })
            .sum()
    }

    fn push_impact_width(&self) -> usize {
        3 + self.alignment_atoms() + self.field_values()
    }

    fn popeq_impact_width(&self) -> usize {
        2 + self.alignment_atoms() + self.field_values()
    }
}

fn record_projection_bindings(name: &str, ty: &ScalarType) -> Result<Vec<(String, String)>> {
    Ok(match ty {
        ScalarType::Bytes32 => byte_projection_bindings(name, 32)?,
        ScalarType::JubjubPoint => (0..2)
            .map(|index| {
                (
                    format!("_noctium_jubjub_read_{name}_{index}"),
                    "Native".into(),
                )
            })
            .collect(),
        _ => Vec::new(),
    })
}

fn bind_record_values(
    read: &Read,
    schema: &CheckedRecordSchema,
    values: &[Value],
    env: &mut Environment,
) -> Result<Vec<String>> {
    ensure!(
        read.components.len() == schema.fields.len() && values.len() == schema.fields.len(),
        "record binding field count mismatch"
    );
    let mut produced = Vec::new();
    for ((component, field), value) in read.components.iter().zip(&schema.fields).zip(values) {
        ensure!(
            ScalarType::parse(&component.ty)? == field.ty && value.scalar_type() == field.ty,
            "record binding type mismatch"
        );
        ensure!(
            !env.contains_key(&component.name),
            "record component shadows an existing value"
        );
        env.insert(component.name.clone(), value.clone());
        produced.push(component.name.clone());

        let projections = record_projection_bindings(&component.name, &field.ty)?;
        if projections.is_empty() {
            continue;
        }
        let mut encoded = Vec::new();
        match value {
            Value::Bytes(_) => aligned_bytes(value)?.value_only_field_repr(&mut encoded),
            Value::JubjubPoint(point) => encoded.extend(jubjub::coordinates(*point)?),
            _ => bail!("record projection type mismatch"),
        }
        ensure!(
            projections.len() == encoded.len(),
            "record projection field count mismatch"
        );
        for ((name, ty), field_value) in projections.into_iter().zip(encoded) {
            ensure!(
                !env.contains_key(&name),
                "record projection shadows an existing value"
            );
            env.insert(
                name.clone(),
                input_value(&ty, &Json::String(field_decimal(field_value)))?,
            );
            produced.push(name);
        }
    }
    Ok(produced)
}

fn valid_record_identifier(value: &str, qualified: bool) -> bool {
    let segments = if qualified {
        value.split('.').collect::<Vec<_>>()
    } else {
        vec![value]
    };
    !segments.is_empty()
        && segments.iter().all(|segment| {
            let mut chars = segment.chars();
            chars
                .next()
                .is_some_and(|first| first == '_' || first.is_ascii_alphabetic())
                && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
        })
}

fn record_type_name(ty: &ScalarType) -> Result<&'static str> {
    Ok(match ty {
        ScalarType::Native => "Native",
        ScalarType::Bytes32 => "Bytes<32>",
        ScalarType::UInt(maximum) if maximum == &BigUint::from(u128::MAX) => {
            "UIntRange<340282366920938463463374607431768211456>"
        }
        ScalarType::UInt(maximum) if maximum == &BigUint::from(u64::MAX) => {
            "UIntRange<18446744073709551616>"
        }
        ScalarType::JubjubPoint => "JubjubPoint",
        _ => bail!("unsupported mixed record field type"),
    })
}

fn checked_record_schema(json: &Json) -> Result<CheckedRecordSchema> {
    if is_shielded_coin_record_schema(json) {
        let fields = [
            ("nonce", "Bytes<32>"),
            ("color", "Bytes<32>"),
            (
                "value",
                "UIntRange<340282366920938463463374607431768211456>",
            ),
            ("mtIndex", "UIntRange<18446744073709551616>"),
        ]
        .into_iter()
        .map(|(name, ty)| {
            Ok(RecordField {
                name: Some(name.to_owned()),
                ty: ScalarType::parse(ty)?,
            })
        })
        .collect::<Result<Vec<_>>>()?;
        return Ok(CheckedRecordSchema {
            fields,
            aggregate: None,
            shielded_coin: true,
        });
    }

    if json.get("schemaVersion").is_some() {
        let schema = aggregates::Schema::from_json(&serde_json::to_vec(json)?)?;
        ensure!(
            schema.counts().leaves > 0 && schema.native_field_only(),
            "record requires nonempty Native leaves"
        );
        return Ok(CheckedRecordSchema {
            fields: (0..schema.counts().leaves)
                .map(|_| RecordField {
                    name: None,
                    ty: ScalarType::Native,
                })
                .collect(),
            aggregate: Some(schema),
            shielded_coin: false,
        });
    }

    let object = json
        .as_object()
        .ok_or_else(|| anyhow!("invalid mixed record schema"))?;
    ensure!(
        object.len() == 2 && object.contains_key("id") && object.contains_key("fields"),
        "invalid mixed record schema"
    );
    let id = object
        .get("id")
        .and_then(Json::as_str)
        .ok_or_else(|| anyhow!("invalid mixed record identity"))?;
    ensure!(
        valid_record_identifier(id, true),
        "invalid mixed record identity"
    );
    let fields = object
        .get("fields")
        .and_then(Json::as_array)
        .filter(|fields| !fields.is_empty() && fields.len() <= aggregates::MAX_LEAVES)
        .ok_or_else(|| anyhow!("invalid mixed record fields"))?;
    let mut names = BTreeSet::new();
    let mut checked = Vec::with_capacity(fields.len());
    for field in fields {
        let field = field
            .as_object()
            .ok_or_else(|| anyhow!("invalid mixed record field"))?;
        ensure!(
            field.len() == 2 && field.contains_key("name") && field.contains_key("type"),
            "invalid mixed record field"
        );
        let name = field
            .get("name")
            .and_then(Json::as_str)
            .ok_or_else(|| anyhow!("invalid mixed record field name"))?;
        ensure!(
            valid_record_identifier(name, false) && names.insert(name.to_owned()),
            "invalid or duplicate mixed record field name"
        );
        let ty_name = field
            .get("type")
            .and_then(Json::as_str)
            .ok_or_else(|| anyhow!("invalid mixed record field type"))?;
        let ty = ScalarType::parse(ty_name)?;
        ensure!(
            matches!(
                &ty,
                ScalarType::Native | ScalarType::Bytes32 | ScalarType::JubjubPoint
            ) && record_type_name(&ty)? == ty_name,
            "unsupported or noncanonical mixed record field type"
        );
        checked.push(RecordField {
            name: Some(name.to_owned()),
            ty,
        });
    }
    Ok(CheckedRecordSchema {
        fields: checked,
        aggregate: None,
        shielded_coin: false,
    })
}

fn validate_record_values(schema: &CheckedRecordSchema, values: &[Value]) -> Result<()> {
    ensure!(
        values.len() == schema.fields.len(),
        "record field count mismatch"
    );
    for (field, value) in schema.fields.iter().zip(values) {
        ensure!(
            value.scalar_type() == field.ty,
            "record field type mismatch"
        );
        value.validate()?;
    }
    if let Some(aggregate) = &schema.aggregate {
        let fields = values
            .iter()
            .map(Value::field)
            .collect::<Result<Vec<_>>>()?;
        validate_record_fields(aggregate, &fields)?;
    }
    Ok(())
}

fn unguarded_operation(operation: &Instruction) -> (&Instruction, Option<&Expr>) {
    match operation {
        Instruction::Guarded { guard, operation } => (operation, Some(guard)),
        operation => (operation, None),
    }
}

fn mutates_contract_state(operation: &Instruction) -> bool {
    let (operation, _) = unguarded_operation(operation);
    matches!(
        operation,
        Instruction::Push { storage: true, .. }
            | Instruction::PushFields { storage: true, .. }
            | Instruction::Insert { .. }
            | Instruction::MapRemove { .. }
            | Instruction::ListPushFront { .. }
            | Instruction::ListPopFront { .. }
            | Instruction::ListReset { .. }
            | Instruction::MerkleTreeInsertHash { .. }
            | Instruction::MerkleTreeInsertHashIndex { .. }
            | Instruction::MerkleTreeReset { .. }
            | Instruction::MerkleTreeResetHistory { .. }
            | Instruction::ReceiveShieldedToMap { .. }
            | Instruction::WriteShieldedCoinCell { .. }
            | Instruction::InsertShieldedCoinSet { .. }
    )
}

fn is_shielded_send_read_only(operation: &Instruction) -> bool {
    let (operation, _) = unguarded_operation(operation);
    matches!(
        operation,
        Instruction::Dup
            | Instruction::Checkpoint
            | Instruction::Index {
                push_path: false,
                ..
            }
            | Instruction::IndexPath {
                push_path: false,
                ..
            }
            | Instruction::Push { storage: false, .. }
            | Instruction::Popeq { .. }
            | Instruction::PopeqFields { .. }
            | Instruction::Member
            | Instruction::ListLength { .. }
            | Instruction::MapSize { .. }
            | Instruction::MapIsEmpty { .. }
            | Instruction::ListHead { .. }
            | Instruction::MerkleTreeIsFull { .. }
            | Instruction::MerkleTreeCheckRoot { .. }
            | Instruction::ReadCaller { .. }
            | Instruction::ReadTokenBalance { .. }
            | Instruction::BlockTimeCompare { .. }
            | Instruction::CounterLessThan { .. }
    )
}

fn validate_shielded_spend_layout(
    plan: &Plan,
    operation_index: usize,
    nonce: &Expr,
    color: &Expr,
    amount: &Expr,
) -> Result<(u32, PathPart)> {
    let removal = plan
        .operations
        .get(operation_index + 1)
        .ok_or_else(|| anyhow!("shielded spend must be followed by Map removal"))?;
    let (removal, removal_guard) = unguarded_operation(removal);
    ensure!(
        removal_guard.is_none(),
        "shielded spend removal must be unguarded"
    );
    let Instruction::MapRemove { slot, keys } = removal else {
        bail!("shielded spend must be followed by Map removal")
    };
    ensure!(keys.len() == 1, "shielded spend requires one Map key");
    ensure!(
        keys[0].alignment == "bytes32",
        "shielded spend Map key must be Bytes32"
    );
    validate_shielded_coin_map(plan, *slot)?;

    let (record_index, record_read) = (0..operation_index)
        .rev()
        .find_map(|index| {
            let (candidate, guard) = unguarded_operation(&plan.operations[index]);
            match candidate {
                Instruction::PopeqFields { schema, .. }
                    if is_shielded_coin_record_schema(schema) =>
                {
                    Some((index, (candidate, guard)))
                }
                _ => None,
            }
        })
        .ok_or_else(|| anyhow!("shielded spend has no exact coin record read"))?;
    let (record_read, record_guard) = record_read;
    ensure!(
        record_guard.is_none(),
        "shielded coin read must be unguarded"
    );
    let Instruction::PopeqFields {
        expressions,
        schema,
    } = record_read
    else {
        unreachable!("the selected operation is a record read")
    };
    ensure!(
        expressions.len() == 4
            && expressions[0] == *nonce
            && expressions[1] == *color
            && expressions[2] == *amount,
        "shielded spend operands differ from the coin record read"
    );

    let path_operation = record_index
        .checked_sub(1)
        .and_then(|index| plan.operations.get(index))
        .ok_or_else(|| anyhow!("shielded coin read has no indexed Map path"))?;
    let (path_operation, path_guard) = unguarded_operation(path_operation);
    ensure!(path_guard.is_none(), "shielded coin path must be unguarded");
    let Instruction::IndexPath {
        slot: read_slot,
        push_path: false,
        keys: read_keys,
    } = path_operation
    else {
        bail!("shielded coin read has no indexed Map path")
    };
    ensure!(
        *read_slot == *slot
            && read_keys.len() == 1
            && read_keys[0].alignment == "bytes32"
            && read_keys[0].expression == keys[0].expression,
        "shielded spend removal differs from the coin read path"
    );
    ensure!(
        tree_schema_at_path(plan, *read_slot, read_keys.len())?.get("composite") == Some(schema),
        "shielded spend read differs from the coin Map schema"
    );
    ensure!(
        plan.operations[record_index + 1..operation_index]
            .iter()
            .any(|operation| {
                let (operation, guard) = unguarded_operation(operation);
                guard.is_none()
                    && matches!(operation, Instruction::ReadContractAddress { .. })
            }),
        "shielded spend requires a current contract address read"
    );
    ensure!(
        !plan.operations[record_index + 1..operation_index]
            .iter()
            .any(mutates_contract_state),
        "shielded coin row changes between read and spend"
    );
    Ok((*slot, read_keys[0].clone()))
}

fn validate_shielded_send_layout(
    plan: &Plan,
    operation_index: usize,
    nonce: &Expr,
    color: &Expr,
    input_amount: &Expr,
    change_commitment: &Expr,
) -> Result<(u32, PathPart, usize)> {
    let (slot, read_key) =
        validate_shielded_spend_layout(plan, operation_index, nonce, color, input_amount)?;
    let removal_index = operation_index + 1;
    let mut receive_index = None;
    for index in removal_index + 1..plan.operations.len() {
        let operation = &plan.operations[index];
        let (candidate, guard) = unguarded_operation(operation);
        if matches!(candidate, Instruction::ReceiveShieldedToMap { .. }) {
            ensure!(guard.is_none(), "shielded change receive must be unguarded");
            receive_index = Some(index);
            break;
        }
        ensure!(
            !mutates_contract_state(operation) && is_shielded_send_read_only(operation),
            "shielded change receive must be the next state mutation after removal"
        );
    }
    let receive_index =
        receive_index.ok_or_else(|| anyhow!("shielded send must be followed by change receive"))?;
    let receive_operation = &plan.operations[receive_index];
    let (receive_operation, receive_guard) = unguarded_operation(receive_operation);
    ensure!(
        receive_guard.is_none(),
        "shielded change receive must be unguarded"
    );
    let Instruction::ReceiveShieldedToMap {
        slot: receive_slot,
        color: receive_color,
        commitment: receive_commitment,
        ..
    } = receive_operation
    else {
        bail!("shielded send must be followed by change receive")
    };
    ensure!(
        *receive_slot == slot,
        "shielded change receive uses a different Map"
    );
    validate_shielded_coin_map(plan, *receive_slot)?;
    ensure!(
        receive_color == color && receive_commitment == change_commitment,
        "shielded change receive differs from the send output"
    );
    Ok((slot, read_key, receive_index))
}

fn validate_relay_shielded_immediate_layout(
    plan: &Plan,
    operation_index: usize,
    recipient: &Expr,
) -> Result<()> {
    let address_read_index = operation_index
        .checked_sub(1)
        .ok_or_else(|| anyhow!("immediate shielded relay requires a current address read"))?;
    let address_read = &plan.operations[address_read_index];
    let (address_read, address_guard) = unguarded_operation(address_read);
    ensure!(
        address_guard.is_none()
            && matches!(address_read, Instruction::ReadContractAddress { .. }),
        "immediate shielded relay requires an unguarded current address read"
    );

    let call_index = operation_index
        .checked_add(1)
        .ok_or_else(|| anyhow!("immediate shielded relay has no recipient call"))?;
    let call = plan
        .operations
        .get(call_index)
        .ok_or_else(|| anyhow!("immediate shielded relay has no recipient call"))?;
    let (call, guard) = unguarded_operation(call);
    ensure!(
        guard.is_none(),
        "immediate shielded recipient call must be unguarded"
    );
    let Instruction::ClaimContractCall { address, .. } = call else {
        bail!("immediate shielded relay must be followed by its recipient call")
    };
    ensure!(
        address == recipient,
        "immediate shielded recipient call differs from the output owner"
    );
    Ok(())
}

fn is_record_schema(schema: &Json) -> bool {
    schema.get("schemaVersion").is_some()
        || schema
            .as_object()
            .is_some_and(|object| object.contains_key("id") && object.contains_key("fields"))
}

fn validate_record_operation_schemas(plan: &Plan) -> Result<()> {
    for (index, operation) in plan.operations.iter().enumerate() {
        let (operation, guard) = unguarded_operation(operation);
        match operation {
            Instruction::PushFields {
                storage: true,
                schema,
                ..
            } if is_record_schema(schema) => {
                checked_record_schema(schema)?;
                let key_operation = index
                    .checked_sub(1)
                    .and_then(|index| plan.operations.get(index))
                    .ok_or_else(|| anyhow!("record write has no final map key"))?;
                let path_operation = index
                    .checked_sub(2)
                    .and_then(|index| plan.operations.get(index))
                    .ok_or_else(|| anyhow!("record write has no indexed map path"))?;
                let (key_operation, key_guard) = unguarded_operation(key_operation);
                let (path_operation, path_guard) = unguarded_operation(path_operation);
                ensure!(
                    key_guard == guard && path_guard == guard,
                    "record write guard differs from its indexed path"
                );
                ensure!(
                    matches!(
                        key_operation,
                        Instruction::Push { storage: false, .. }
                            | Instruction::PushFields { storage: false, .. }
                    ),
                    "record write has an invalid final map key"
                );
                let Instruction::IndexPath {
                    slot,
                    keys,
                    push_path: true,
                } = path_operation
                else {
                    bail!("record write has no indexed map path")
                };
                ensure!(
                    tree_schema_at_path(plan, *slot, keys.len() + 1)?.get("composite")
                        == Some(schema),
                    "record write differs from state schema"
                );
            }
            Instruction::PopeqFields { schema, .. } if is_record_schema(schema) => {
                checked_record_schema(schema)?;
                let path_operation = index
                    .checked_sub(1)
                    .and_then(|index| plan.operations.get(index))
                    .ok_or_else(|| anyhow!("record read has no indexed path"))?;
                let (path_operation, path_guard) = unguarded_operation(path_operation);
                ensure!(
                    path_guard == guard,
                    "record read guard differs from its indexed path"
                );
                let Instruction::IndexPath {
                    slot,
                    keys,
                    push_path: false,
                } = path_operation
                else {
                    bail!("record read has no indexed path")
                };
                ensure!(
                    tree_schema_at_path(plan, *slot, keys.len())?.get("composite") == Some(schema),
                    "record read differs from state schema"
                );
            }
            Instruction::SpendShieldedFromMap {
                nonce,
                color,
                amount,
                ..
            } => {
                ensure!(guard.is_none(), "shielded spend must be unguarded");
                validate_shielded_spend_layout(plan, index, nonce, color, amount)?;
            }
            Instruction::SendShieldedFromMap {
                nonce,
                color,
                input_amount,
                change_commitment,
                ..
            } => {
                ensure!(guard.is_none(), "shielded send must be unguarded");
                validate_shielded_send_layout(
                    plan,
                    index,
                    nonce,
                    color,
                    input_amount,
                    change_commitment,
                )?;
            }
            Instruction::RelayShieldedImmediate { recipient, .. } => {
                ensure!(guard.is_none(), "immediate shielded relay must be unguarded");
                validate_relay_shielded_immediate_layout(plan, index, recipient)?;
            }
            Instruction::ListHead {
                slot,
                keys,
                schema,
                expressions,
            }
            | Instruction::ListPushFront {
                slot,
                keys,
                schema,
                expressions,
            } => {
                if list_operation_scalar_type(plan, *slot, keys, schema)?.is_some() {
                    ensure!(
                        expressions.len() == 1,
                        "scalar List operation requires one expression"
                    );
                } else {
                    checked_record_schema(schema)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn record_values_from_json(schema: &CheckedRecordSchema, json: &Json) -> Result<Vec<Value>> {
    let values = if let Some(aggregate) = &schema.aggregate {
        let leaves = aggregate.flatten_leaves_json(&serde_json::to_vec(json)?)?;
        leaves
            .iter()
            .map(|leaf| input_value("Native", leaf))
            .collect::<Result<Vec<_>>>()?
    } else {
        let object = json
            .as_object()
            .ok_or_else(|| anyhow!("mixed record value must be an object"))?;
        ensure!(
            object.len() == schema.fields.len(),
            "mixed record value field count mismatch"
        );
        schema
            .fields
            .iter()
            .map(|field| {
                let name = field
                    .name
                    .as_deref()
                    .ok_or_else(|| anyhow!("mixed record field lacks a name"))?;
                let value = object
                    .get(name)
                    .ok_or_else(|| anyhow!("mixed record value is missing a field"))?;
                input_value(record_type_name(&field.ty)?, value)
            })
            .collect::<Result<Vec<_>>>()?
    };
    validate_record_values(schema, &values)?;
    Ok(values)
}

fn record_values_from_expressions(
    schema: &CheckedRecordSchema,
    expressions: &[Expr],
    env: &Environment,
) -> Result<Vec<Value>> {
    ensure!(
        expressions.len() == schema.fields.len(),
        "record expression count mismatch"
    );
    let values = expressions
        .iter()
        .map(|expression| evaluate(expression, env))
        .collect::<Result<Vec<_>>>()?;
    validate_record_values(schema, &values)?;
    Ok(values)
}

fn shielded_qualified_coin(values: &[Value]) -> Result<QualifiedInfo> {
    ensure!(values.len() == 4, "qualified coin record field count mismatch");
    let Value::UInt {
        number: amount,
        maximum: amount_maximum,
    } = &values[2]
    else {
        bail!("qualified coin amount must be UInt128")
    };
    let Value::UInt {
        number: mt_index,
        maximum: mt_index_maximum,
    } = &values[3]
    else {
        bail!("qualified coin index must be UInt64")
    };
    ensure!(
        *amount_maximum == u128::MAX.into() && *mt_index_maximum == u64::MAX.into(),
        "qualified coin integer widths differ from the ledger"
    );
    Ok(QualifiedInfo {
        nonce: Nonce(claim_hash_output(values[0].clone(), "qualified coin nonce")?),
        type_: ShieldedTokenType(claim_hash_output(
            values[1].clone(),
            "qualified coin color",
        )?),
        value: u128::try_from(amount.clone())?,
        mt_index: u64::try_from(mt_index.clone())?,
    })
}

fn aligned_record_value(schema: &CheckedRecordSchema, values: &[Value]) -> Result<AlignedValue> {
    validate_record_values(schema, values)?;
    if schema.shielded_coin {
        return Ok(AlignedValue::from(shielded_qualified_coin(values)?));
    }
    let parts = values
        .iter()
        .map(aligned_storage_cell)
        .collect::<Result<Vec<_>>>()?;
    Ok(AlignedValue::concat(parts.iter()))
}

fn decode_record_value(schema: &CheckedRecordSchema, value: &AlignedValue) -> Result<Vec<Value>> {
    if schema.shielded_coin {
        let empty = AlignedValue::from(QualifiedInfo::default());
        ensure!(
            value.alignment == empty.alignment && value.alignment.fits(&value.value),
            "qualified coin record alignment mismatch"
        );
        let value_slice: &ValueSlice = &value.value;
        let qualified = QualifiedInfo::try_from(value_slice)
            .map_err(|_| anyhow!("qualified coin record encoding mismatch"))?;
        ensure!(
            AlignedValue::from(qualified) == *value,
            "qualified coin record is not canonically encoded"
        );
        let values = vec![
            Value::Bytes(qualified.nonce.0.0.to_vec()),
            Value::Bytes(qualified.type_.0.0.to_vec()),
            Value::UInt {
                number: qualified.value.into(),
                maximum: u128::MAX.into(),
            },
            Value::UInt {
                number: qualified.mt_index.into(),
                maximum: u64::MAX.into(),
            },
        ];
        validate_record_values(schema, &values)?;
        return Ok(values);
    }

    let defaults = schema
        .fields
        .iter()
        .map(|field| inactive_read_value(record_type_name(&field.ty)?))
        .collect::<Result<Vec<_>>>()?;
    let templates = defaults
        .iter()
        .map(aligned_storage_cell)
        .collect::<Result<Vec<_>>>()?;
    let expected = AlignedValue::concat(templates.iter());
    ensure!(
        value.alignment == expected.alignment && value.value.0.len() == expected.value.0.len(),
        "record cell alignment mismatch"
    );
    ensure!(
        value.alignment.fits(&value.value),
        "record cell encoding mismatch"
    );
    let mut offset: usize = 0;
    let mut values = Vec::with_capacity(schema.fields.len());
    for (field, template) in schema.fields.iter().zip(templates) {
        let end = offset
            .checked_add(template.value.0.len())
            .ok_or_else(|| anyhow!("record atom count overflow"))?;
        let part = AlignedValue {
            value: FabValue(value.value.0[offset..end].to_vec()),
            alignment: template.alignment,
        };
        offset = end;
        let alignment = if field.ty == ScalarType::Bytes32 {
            "bytes32"
        } else {
            "field"
        };
        values.push(decode_state_cell(
            &part,
            record_type_name(&field.ty)?,
            alignment,
        )?);
    }
    ensure!(
        offset == value.value.0.len(),
        "record cell atom count mismatch"
    );
    validate_record_values(schema, &values)?;
    Ok(values)
}

pub(crate) fn default_record_value(schema: &Json) -> Result<Json> {
    let schema = checked_record_schema(schema)?;
    if let Some(aggregate) = schema.aggregate {
        return Ok(serde_json::from_slice(&aggregate.from_leaf_json(
            &vec![Json::String("0".into()); aggregate.counts().leaves],
        )?)?);
    }
    let fields = schema
        .fields
        .into_iter()
        .map(|field| {
            let name = field
                .name
                .ok_or_else(|| anyhow!("mixed record field lacks a name"))?;
            let value = inactive_read_value(record_type_name(&field.ty)?)?.public_json();
            Ok((name, value))
        })
        .collect::<Result<serde_json::Map<_, _>>>()?;
    Ok(Json::Object(fields))
}

fn typed_scalar_schema_token(schema: &Json) -> Option<&str> {
    let name = schema.as_str()?;
    is_typed_scalar(&ScalarType::parse(name).ok()?).then_some(name)
}

fn is_typed_scalar(ty: &ScalarType) -> bool {
    match ty {
        ScalarType::JubjubScalar | ScalarType::JubjubPoint => true,
        #[cfg(feature = "zkir-321")]
        ScalarType::Foreign(_) => true,
        _ => false,
    }
}

fn typed_scalar_field_count(ty: &ScalarType) -> Result<usize> {
    Ok(match ty {
        ScalarType::JubjubScalar => 1,
        ScalarType::JubjubPoint => 2,
        #[cfg(feature = "zkir-321")]
        ScalarType::Foreign(ty) => ty.native_type().encoded_len(),
        _ => bail!("unsupported typed storage scalar"),
    })
}

fn typed_scalar_fields(value: &Value) -> Result<Vec<Fr>> {
    Ok(match value {
        Value::JubjubScalar(value) => vec![jubjub::scalar_native(*value)?],
        Value::JubjubPoint(value) => jubjub::coordinates(*value)?.to_vec(),
        #[cfg(feature = "zkir-321")]
        Value::Foreign(value) => value.encode()?,
        _ => bail!("expected typed storage scalar"),
    })
}

fn decode_typed_scalar(ty: &ScalarType, fields: &[Fr]) -> Result<Value> {
    Ok(match ty {
        ScalarType::JubjubScalar => {
            ensure!(fields.len() == 1, "JubjubScalar storage requires one field");
            Value::JubjubScalar(jubjub::scalar(&field_decimal(fields[0]))?)
        }
        ScalarType::JubjubPoint => {
            ensure!(fields.len() == 2, "JubjubPoint storage requires two fields");
            Value::JubjubPoint(jubjub::point(fields[0], fields[1])?)
        }
        #[cfg(feature = "zkir-321")]
        ScalarType::Foreign(ty) => Value::Foreign(foreign::ForeignValue::decode(*ty, fields)?),
        _ => bail!("unsupported typed storage scalar"),
    })
}

fn aligned_storage_cell(value: &Value) -> Result<AlignedValue> {
    match value {
        Value::Bytes(_) => aligned_bytes(value),
        Value::OpaqueBytes(_) => aligned_opaque_bytes(value),
        Value::JubjubScalar(_) | Value::JubjubPoint(_) => {
            Ok(aligned_fields(&typed_scalar_fields(value)?))
        }
        #[cfg(feature = "zkir-321")]
        Value::Foreign(_) => Ok(aligned_fields(&typed_scalar_fields(value)?)),
        _ => aligned(value, "field"),
    }
}

fn aligned_fields(fields: &[Fr]) -> AlignedValue {
    let fields: Vec<_> = fields.iter().copied().map(field_value).collect();
    AlignedValue::concat(fields.iter())
}

fn aligned_call_inputs(plan: &Plan, env: &Environment) -> Result<AlignedValue> {
    let values = plan
        .call_inputs
        .iter()
        .map(|name| {
            env.get(name)
                .ok_or_else(|| anyhow!("native call input is missing"))
        })
        .collect::<Result<Vec<_>>>()?;
    aligned_call_values(values.into_iter())
}

fn validate_record_fields(schema: &aggregates::Schema, fields: &[Fr]) -> Result<()> {
    let json: Vec<_> = fields
        .iter()
        .map(|field| Json::String(field_decimal(*field)))
        .collect();
    schema.from_leaf_json(&json)?;
    Ok(())
}

fn record_component_names(read: &Read, expressions: &[Expr], schema: &Json) -> Result<()> {
    let checked = checked_record_schema(schema)?;
    ensure!(
        read.ty == "Composite"
            && read.schema.as_ref() == Some(schema)
            && read.components.len() == checked.fields.len()
            && expressions.len() == read.components.len()
            && read.projections.is_none(),
        "record read schema mismatch"
    );
    let mut names = BTreeSet::new();
    for ((component, field), expression) in
        read.components.iter().zip(&checked.fields).zip(expressions)
    {
        let component_type = ScalarType::parse(&component.ty)?;
        ensure!(
            component_type == field.ty
                && component.ty == record_type_name(&field.ty)?
                && names.insert(component.name.as_str()),
            "invalid record read component"
        );
        ensure!(
            matches!(expression, Expr::Reference { name } if name == &component.name),
            "record read expression differs from source component"
        );
    }
    Ok(())
}

fn validate_byte_read_projections(read: &Read, ty: &ScalarType) -> Result<()> {
    let length = ty
        .bytes_length()
        .ok_or_else(|| anyhow!("byte read requires a byte scalar"))?;
    ensure!(
        read.schema.is_none() && read.components.is_empty(),
        "byte read has record projections"
    );
    let expected = byte_projection_bindings(&read.name, length)?;
    let projections = read
        .projections
        .as_ref()
        .ok_or_else(|| anyhow!("byte read is missing its projections"))?;
    ensure!(
        projections.len() == expected.len()
            && projections
                .iter()
                .zip(expected)
                .all(|(actual, (name, ty))| actual.name == name && actual.ty == ty),
        "byte read projections differ from its declared length"
    );
    Ok(())
}

fn validate_jubjub_point_read_projections(read: &Read) -> Result<()> {
    ensure!(
        read.schema.is_none() && read.components.is_empty(),
        "JubjubPoint read has record metadata"
    );
    let projections = read
        .projections
        .as_ref()
        .ok_or_else(|| anyhow!("JubjubPoint read is missing its projections"))?;
    ensure!(
        projections.len() == 2
            && projections.iter().enumerate().all(|(index, projection)| {
                projection.name == format!("_noctium_jubjub_read_{}_{}", read.name, index)
                    && projection.ty == "Native"
            }),
        "JubjubPoint read projections differ from its coordinates"
    );
    Ok(())
}

fn bind_list_scalar_read(
    read: &Read,
    expression: &Expr,
    ty_name: &str,
    guard: Option<&Expr>,
    active: bool,
    value: Value,
    env: &mut Environment,
) -> Result<PreparationRead> {
    let ty = ScalarType::parse(ty_name)?;
    ensure!(
        matches!(expression, Expr::Reference { name } if name == &read.name)
            && read.ty == ty_name
            && read.guard.as_ref() == guard
            && read.components.is_empty()
            && read.schema.is_none()
            && value.scalar_type() == ty,
        "scalar List read schema mismatch"
    );
    value.validate()?;
    ensure!(
        !env.contains_key(&read.name),
        "scalar List read shadows an existing value"
    );
    env.insert(read.name.clone(), value.clone());
    let mut produced = vec![read.name.clone()];

    let projections = if ty.bytes_length().is_some() {
        validate_byte_read_projections(read, &ty)?;
        byte_projection_bindings(&read.name, ty.bytes_length().unwrap())?
    } else if ty == ScalarType::JubjubPoint {
        validate_jubjub_point_read_projections(read)?;
        (0..2)
            .map(|index| {
                (
                    format!("_noctium_jubjub_read_{}_{}", read.name, index),
                    "Native".to_owned(),
                )
            })
            .collect()
    } else {
        ensure!(
            read.projections.is_none(),
            "scalar List read has unexpected projections"
        );
        Vec::new()
    };

    if !projections.is_empty() {
        let encoded = match &value {
            Value::Bytes(_) => {
                let mut fields = Vec::new();
                aligned_bytes(&value)?.value_only_field_repr(&mut fields);
                fields
            }
            Value::JubjubPoint(point) => jubjub::coordinates(*point)?.to_vec(),
            _ => bail!("scalar List projection type mismatch"),
        };
        ensure!(
            projections.len() == encoded.len(),
            "scalar List projection field count mismatch"
        );
        for ((name, projection_ty), field) in projections.into_iter().zip(encoded) {
            ensure!(
                !env.contains_key(&name),
                "scalar List projection shadows an existing value"
            );
            env.insert(
                name.clone(),
                input_value(&projection_ty, &Json::String(field_decimal(field)))?,
            );
            produced.push(name);
        }
    }

    Ok(read_event(read, active, env, produced))
}

fn key_alignment(ty: &ScalarType) -> &'static str {
    if *ty == ScalarType::Bytes32 {
        "bytes32"
    } else {
        "field"
    }
}
fn inactive_read_value(ty: &str) -> Result<Value> {
    Ok(match ScalarType::parse(ty)? {
        ScalarType::Native => Value::Native(Fr::from(0u64)),
        ScalarType::Bool => Value::Bool(false),
        ScalarType::UInt(maximum) => Value::UInt {
            number: BigUint::from(0u8),
            maximum,
        },
        ScalarType::Bytes32 => Value::Bytes(vec![0; 32]),
        ScalarType::Bytes(length) => Value::Bytes(vec![0; length]),
        ScalarType::OpaqueBytes => Value::OpaqueBytes(Vec::new()),
        ScalarType::JubjubScalar => Value::JubjubScalar(jubjub::scalar("0")?),
        ScalarType::JubjubPoint => {
            Value::JubjubPoint(jubjub::point(Fr::from(0u64), Fr::from(1u64))?)
        }
        #[cfg(feature = "zkir-321")]
        ScalarType::Foreign(ty) => Value::Foreign(foreign::ForeignValue::zero(ty)?),
    })
}
#[derive(Clone, Deserialize)]
pub struct Config {
    pub inputs: BTreeMap<String, Json>,
    pub state: BTreeMap<String, Json>,
    #[serde(rename = "negativeCases", default)]
    pub negative_cases: Vec<NegativeCase>,
}
/// Private decoding errors retain locations, never parser messages or values.
pub fn parse_private_config(bytes: &[u8]) -> Result<Config> {
    serde_json::from_slice(bytes).map_err(|error| {
        anyhow!(
            "invalid private configuration (line {}, column {})",
            error.line(),
            error.column()
        )
    })
}
#[derive(Clone, Deserialize)]
pub struct NegativeCase {
    pub name: String,
    pub inputs: BTreeMap<String, Json>,
}
fn input_value(ty: &str, json: &Json) -> Result<Value> {
    match ScalarType::parse(ty)? {
        ScalarType::Native => Ok(Value::Native(canonical_field(
            json.as_str()
                .ok_or_else(|| anyhow!("Native input requires decimal string"))?,
        )?)),
        ScalarType::Bool => Ok(Value::Bool(
            json.as_bool()
                .ok_or_else(|| anyhow!("Bool input requires boolean"))?,
        )),
        ScalarType::UInt(maximum) => Ok(Value::UInt {
            number: canonical_unsigned(
                json.as_str()
                    .ok_or_else(|| anyhow!("unsigned input requires decimal string"))?,
                &maximum,
            )?,
            maximum,
        }),
        bytes_type @ (ScalarType::Bytes32 | ScalarType::Bytes(_)) => {
            let object = json
                .as_object()
                .ok_or_else(|| anyhow!("expected bytes object"))?;
            ensure!(
                object.len() == 2 && object.get("kind").and_then(Json::as_str) == Some("bytes"),
                "invalid bytes object"
            );
            let values = object
                .get("values")
                .and_then(Json::as_array)
                .ok_or_else(|| anyhow!("expected bytes array"))?;
            ensure!(
                values.len() == bytes_type.bytes_length().unwrap(),
                "byte input length mismatch"
            );
            let bytes = values
                .iter()
                .map(|value| {
                    value
                        .as_u64()
                        .and_then(|value| u8::try_from(value).ok())
                        .ok_or_else(|| anyhow!("expected canonical byte integer"))
                })
                .collect::<Result<Vec<_>>>()?;
            Ok(Value::Bytes(bytes))
        }
        ScalarType::OpaqueBytes => {
            let object = json
                .as_object()
                .ok_or_else(|| anyhow!("expected opaque byte object"))?;
            ensure!(
                object.len() == 2
                    && object.get("kind").and_then(Json::as_str) == Some("opaqueBytes"),
                "invalid opaque byte object"
            );
            let values = object
                .get("values")
                .and_then(Json::as_array)
                .ok_or_else(|| anyhow!("expected opaque byte array"))?;
            ensure!(
                values.len() <= scalars::MAX_OPAQUE_BYTES_LENGTH,
                "opaque byte value exceeds native limit"
            );
            let bytes = values
                .iter()
                .map(|value| {
                    value
                        .as_u64()
                        .and_then(|value| u8::try_from(value).ok())
                        .ok_or_else(|| anyhow!("expected canonical opaque byte integer"))
                })
                .collect::<Result<Vec<_>>>()?;
            let value = Value::OpaqueBytes(bytes);
            value.validate()?;
            Ok(value)
        }
        ScalarType::JubjubScalar => {
            let object = json
                .as_object()
                .ok_or_else(|| anyhow!("expected JubjubScalar object"))?;
            ensure!(
                object.len() == 2
                    && object.get("kind").and_then(Json::as_str) == Some("jubjubScalar"),
                "invalid JubjubScalar object"
            );
            let value = object
                .get("value")
                .and_then(Json::as_str)
                .ok_or_else(|| anyhow!("JubjubScalar requires canonical decimal value"))?;
            Ok(Value::JubjubScalar(jubjub::scalar(value)?))
        }
        ScalarType::JubjubPoint => {
            let object = json
                .as_object()
                .ok_or_else(|| anyhow!("expected JubjubPoint object"))?;
            ensure!(
                object.len() == 3
                    && object.get("kind").and_then(Json::as_str) == Some("jubjubPoint"),
                "invalid JubjubPoint object"
            );
            let x = canonical_field(
                object
                    .get("x")
                    .and_then(Json::as_str)
                    .ok_or_else(|| anyhow!("JubjubPoint requires canonical x coordinate"))?,
            )?;
            let y = canonical_field(
                object
                    .get("y")
                    .and_then(Json::as_str)
                    .ok_or_else(|| anyhow!("JubjubPoint requires canonical y coordinate"))?,
            )?;
            Ok(Value::JubjubPoint(jubjub::point(x, y)?))
        }
        #[cfg(feature = "zkir-321")]
        ScalarType::Foreign(ty) => {
            let object = json
                .as_object()
                .ok_or_else(|| anyhow!("expected foreign value object"))?;
            ensure!(
                object.len() == 3
                    && object.get("kind").and_then(Json::as_str) == Some("foreign")
                    && object.get("type").and_then(Json::as_str) == Some(ty.source_name()),
                "invalid foreign value object"
            );
            let values = object
                .get("bytes")
                .and_then(Json::as_array)
                .ok_or_else(|| anyhow!("expected foreign byte array"))?;
            ensure!(
                values.len() == ty.byte_len(),
                "foreign byte length mismatch"
            );
            let bytes = values
                .iter()
                .map(|value| {
                    value
                        .as_u64()
                        .and_then(|value| u8::try_from(value).ok())
                        .ok_or_else(|| anyhow!("expected canonical foreign byte"))
                })
                .collect::<Result<Vec<_>>>()?;
            Ok(Value::Foreign(foreign::ForeignValue::from_bytes(
                ty, &bytes,
            )?))
        }
    }
}
fn validate_environment_schema(plan: &Plan) -> Result<()> {
    let expected_schema = if plan.circuit.shared_bindings.is_empty() { 1 } else { 2 };
    ensure!(plan.schema_version == expected_schema, "unsupported plan schema");
    ensure!(
        profile::validate_plan(plan.target.as_deref(), plan.target_profile.as_ref()),
        "plan target differs from linked native profile"
    );
    ensure!(!plan.entrypoint.is_empty(), "missing entrypoint");
    let names: BTreeSet<_> = plan
        .circuit
        .inputs
        .iter()
        .map(|input| input.name.as_str())
        .collect();
    ensure!(
        names.len() == plan.circuit.inputs.len(),
        "duplicate input name"
    );
    call_input_header(&plan.circuit.inputs, &plan.call_inputs)?;
    validate_record_operation_schemas(plan)?;
    #[cfg(feature = "zkir-321")]
    validate_foreign_key_pushes(plan)?;
    let mut output_names = BTreeSet::new();
    for output in &plan.circuit.outputs {
        ensure!(
            output.visibility == "public",
            "unsupported output visibility"
        );
        ensure!(
            !output.name.is_empty()
                && !names.contains(output.name.as_str())
                && output_names.insert(output.name.as_str()),
            "output shadows an existing name"
        );
        ScalarType::parse(&output.ty)?;
    }
    let mut shared_names = BTreeSet::new();
    for (name, _) in &plan.circuit.shared_bindings {
        ensure!(
            !name.is_empty()
                && !names.contains(name.as_str())
                && !output_names.contains(name.as_str())
                && shared_names.insert(name.as_str()),
            "shared binding shadows an existing name"
        );
    }
    ensure!(plan.returns.len() <= 256, "too many call returns");
    validate_return_views_specs(
        &plan.return_views,
        plan.returns.iter().map(|output| {
            (
                output.name.as_str(),
                output.ty.as_str(),
                output.visibility.as_str(),
            )
        }),
    )?;
    Ok(())
}

fn call_byte_input_fields(name: &str, length: usize) -> impl Iterator<Item = (String, u64)> + '_ {
    let chunks = length.div_ceil(31);
    (0..chunks).map(move |index| {
        let width = (length - (chunks - 1 - index) * 31).min(31);
        (format!("{name}_call_chunk_{index}"), (width * 8) as u64)
    })
}

fn call_input_header(inputs: &[Input], call_inputs: &[String]) -> Result<Vec<(String, Json)>> {
    ensure!(call_inputs.len() <= 256, "too many native call inputs");
    let native = Json::String("Scalar<BLS12-381>".into());
    let mut names = BTreeSet::new();
    let mut header = Vec::new();
    let mut field_count = 0;
    for name in call_inputs {
        ensure!(
            !name.is_empty() && names.insert(name.as_str()),
            "invalid native call input list"
        );
        let input = inputs
            .iter()
            .find(|input| input.name == *name)
            .ok_or_else(|| anyhow!("native call input is not declared by the circuit"))?;
        ensure!(
            input.visibility == "private",
            "native call inputs must name private circuit inputs"
        );
        let ty = ScalarType::parse(&input.ty)?;
        field_count += ty.call_return_fields();
        ensure!(field_count <= 256, "too many native call argument fields");
        if let Some(length) = ty.bytes_length() {
            header.extend(
                call_byte_input_fields(name, length)
                    .map(|(field, _)| (format!("%input_{field}"), native.clone())),
            );
        } else {
            match ty {
                ScalarType::JubjubPoint => {
                    for axis in ["x", "y"] {
                        header.push((format!("%input_{name}_{axis}"), native.clone()));
                    }
                }
                #[cfg(feature = "zkir-321")]
                ScalarType::Foreign(ty) => {
                    header.push((
                        format!("%input_{name}"),
                        serde_json::to_value(ty.native_type())?,
                    ));
                }
                _ => header.push((format!("%input_{name}"), native.clone())),
            }
        }
    }
    ensure!(
        header
            .iter()
            .map(|(name, _)| name)
            .collect::<BTreeSet<_>>()
            .len()
            == header.len(),
        "native call argument projections collide"
    );
    Ok(header)
}

fn validate_call_input_header_json(expected: &[(String, Json)], circuit: &Json) -> Result<()> {
    let inputs = match circuit.get("inputs") {
        Some(Json::Array(inputs)) => inputs.as_slice(),
        None if expected.is_empty() => &[],
        _ => bail!("invalid native circuit input header"),
    };
    ensure!(
        inputs.len() == expected.len(),
        "native circuit input header mismatch"
    );
    for (header, (name, ty)) in inputs.iter().zip(expected) {
        let object = header
            .as_object()
            .ok_or_else(|| anyhow!("invalid native circuit input header"))?;
        ensure!(
            object.len() == 2
                && object.get("name").and_then(Json::as_str) == Some(name.as_str())
                && object.get("type") == Some(ty),
            "native circuit inputs do not match declared call inputs"
        );
    }
    Ok(())
}

fn call_input_names(metadata: &Json) -> Result<Vec<String>> {
    match metadata.get("callInputs") {
        None => Ok(Vec::new()),
        Some(Json::Array(inputs)) if inputs.len() <= 256 => inputs
            .iter()
            .map(|input| {
                input
                    .as_str()
                    .map(str::to_owned)
                    .ok_or_else(|| anyhow!("native call input name must be a string"))
            })
            .collect(),
        _ => bail!("invalid native call input list"),
    }
}

pub(crate) fn validate_call_inputs_json(plan: &Json, circuit: &Json) -> Result<()> {
    let call_inputs = call_input_names(plan)?;
    let inputs = plan
        .get("circuit")
        .and_then(|value| value.get("inputs"))
        .and_then(Json::as_array)
        .ok_or_else(|| anyhow!("invalid plan circuit inputs"))?
        .iter()
        .map(|input| {
            Ok(Input {
                name: input
                    .get("name")
                    .and_then(Json::as_str)
                    .ok_or_else(|| anyhow!("invalid plan input name"))?
                    .to_owned(),
                ty: input
                    .get("type")
                    .and_then(Json::as_str)
                    .ok_or_else(|| anyhow!("invalid plan input type"))?
                    .to_owned(),
                visibility: input
                    .get("visibility")
                    .and_then(Json::as_str)
                    .ok_or_else(|| anyhow!("invalid plan input visibility"))?
                    .to_owned(),
            })
        })
        .collect::<Result<Vec<_>>>()?;
    validate_call_input_header_json(&call_input_header(&inputs, &call_inputs)?, circuit)
}

fn validate_return_views_specs<'a>(
    views: &[ReturnView],
    returns: impl IntoIterator<Item = (&'a str, &'a str, &'a str)>,
) -> Result<BTreeSet<String>> {
    ensure!(views.len() <= 256, "too many composite return views");
    let mut physical = BTreeMap::new();
    let mut logical_names = BTreeSet::new();
    let mut total_fields = 0usize;
    for (index, (name, ty, visibility)) in returns.into_iter().enumerate() {
        ensure!(
            visibility == "public" && !name.is_empty() && logical_names.insert(name),
            "invalid call return declaration"
        );
        let scalar = ScalarType::parse(ty)?;
        total_fields = total_fields
            .checked_add(scalar.call_return_fields())
            .ok_or_else(|| anyhow!("too many native call return fields"))?;
        ensure!(total_fields <= 256, "too many native call return fields");
        physical.insert(name, (index, ty));
    }

    let mut grouped = BTreeSet::new();
    for view in views {
        ensure!(
            !view.name.is_empty()
                && view.name.len() <= 4096
                && logical_names.insert(view.name.as_str())
                && view.fields.len() <= 256,
            "invalid or colliding composite return view"
        );
        let schema_bytes = serde_json::to_vec(&view.schema)?;
        let schema = Schema::from_json(&schema_bytes)?;
        ensure!(
            schema.counts().leaves == view.fields.len(),
            "composite return field count differs from its schema"
        );
        let mut previous_index = None;
        for field in &view.fields {
            let (index, ty) = physical
                .get(field.as_str())
                .ok_or_else(|| anyhow!("composite return references an unknown field"))?;
            ensure!(
                *ty == "Native" && grouped.insert(field.clone()),
                "composite return fields must be unique Native outputs"
            );
            ensure!(
                previous_index.is_none_or(|previous| previous < *index),
                "composite return fields are out of order"
            );
            previous_index = Some(*index);
        }
    }
    Ok(grouped)
}

pub(crate) fn validate_return_views_json(plan: &Json) -> Result<()> {
    let views = match plan.get("returnViews") {
        None => Vec::new(),
        Some(value) => serde_json::from_value::<Vec<ReturnView>>(value.clone())?,
    };
    let returns = match plan.get("returns") {
        None => &[][..],
        Some(Json::Array(values)) => values.as_slice(),
        _ => bail!("invalid call return schema"),
    };
    let returns = returns
        .iter()
        .map(|output| {
            Ok((
                output["name"]
                    .as_str()
                    .ok_or_else(|| anyhow!("invalid call return name"))?,
                output["type"]
                    .as_str()
                    .ok_or_else(|| anyhow!("invalid call return type"))?,
                output["visibility"]
                    .as_str()
                    .ok_or_else(|| anyhow!("invalid call return visibility"))?,
            ))
        })
        .collect::<Result<Vec<_>>>()?;
    validate_return_views_specs(&views, returns)?;
    Ok(())
}

fn parse_input_environment(
    plan: &Plan,
    inputs: &BTreeMap<String, Json>,
    allow_missing_private: bool,
) -> Result<Environment> {
    validate_environment_schema(plan)?;
    let names: BTreeSet<_> = plan
        .circuit
        .inputs
        .iter()
        .map(|input| input.name.as_str())
        .collect();
    ensure!(
        inputs.keys().all(|name| names.contains(name.as_str())),
        "input schema mismatch (missing or unknown input)"
    );
    let mut env = BTreeMap::new();
    for input in &plan.circuit.inputs {
        ensure!(
            matches!(input.visibility.as_str(), "public" | "private"),
            "unsupported input visibility"
        );
        ScalarType::parse(&input.ty)?;
        if let Some(value) = inputs.get(&input.name) {
            env.insert(
                input.name.clone(),
                input_value(&input.ty, value)
                    .with_context(|| format!("invalid input '{}'", input.name))?,
            );
        } else {
            ensure!(
                allow_missing_private && input.visibility == "private",
                "input schema mismatch (missing or unknown input)"
            );
        }
    }
    Ok(env)
}

fn evaluate_circuit_outputs(plan: &Plan, env: &mut Environment) -> Result<()> {
    validate_shared_binding_environment(plan, env)?;
    let shared_bindings =
        if plan.circuit.outputs.is_empty() || plan.circuit.shared_bindings.is_empty() {
            Vec::new()
        } else {
            evaluate_shared_bindings(plan, env)?
        };
    let mut local = if shared_bindings.is_empty() {
        None
    } else {
        Some(circuit_output_environment(env, &shared_bindings)?)
    };
    for o in &plan.circuit.outputs {
        let v = evaluate(&o.expression, local.as_ref().unwrap_or(env))?;
        ensure!(
            v.scalar_type() == ScalarType::parse(&o.ty)?,
            "output type mismatch"
        );
        env.insert(o.name.clone(), v.clone());
        if let Some(local) = &mut local {
            local.insert(o.name.clone(), v);
        }
    }
    Ok(())
}

pub fn environment(plan: &Plan, inputs: &BTreeMap<String, Json>) -> Result<Environment> {
    let mut env = parse_input_environment(plan, inputs, false)?;
    evaluate_circuit_outputs(plan, &mut env)?;
    Ok(env)
}
pub fn create_state(plan: &Plan, config: &BTreeMap<String, Json>) -> Result<ChargedState<Db>> {
    ensure!(plan.state.len() <= 16, "state array exceeds native limit");
    ensure!(
        config.len() == plan.state.len(),
        "initial state schema mismatch"
    );
    let mut values = Vec::new();
    for d in &plan.state {
        let value = config
            .get(&d.name)
            .ok_or_else(|| anyhow!("missing initial state cell"))?;
        if d.kind.get("merkleTree").is_some() {
            let (depth, historic) = checked_merkle_tree_schema(&d.kind)?;
            ensure!(
                value.as_array().is_some_and(Vec::is_empty),
                "initial MerkleTree must be explicitly empty"
            );
            values.push(merkle_tree_default_state(depth, historic, false));
        } else if d.kind.get("opaqueString") == Some(&Json::Bool(true)) {
            values.push(StateValue::Cell(Sp::new(constructor::opaque_string(
                value,
            )?)));
        } else if let Some(ty) = d.kind.get("cell").and_then(Json::as_str) {
            values.push(StateValue::Cell(Sp::new(aligned_storage_cell(
                &input_value(ty, value)?,
            )?)));
        } else if let Some(types) = d.kind.get("map").and_then(Json::as_array) {
            ensure!(
                types.len() == 2
                    && types
                        .iter()
                        .all(|t| t.as_str().is_some_and(|t| ScalarType::parse(t).is_ok())),
                "unsupported map schema"
            );
            ledger_key_type(&types[0])?;
            ensure!(
                value.as_array().is_some_and(|a| a.is_empty()),
                "initial map must be explicitly empty"
            );
            values.push(StateValue::Map(Default::default()));
        } else if let Some(schema) = d.kind.get("tree") {
            validate_tree_schema(schema, 0)?;
            if schema.get("list").is_some() {
                ensure!(
                    value.as_array().is_some_and(Vec::is_empty),
                    "initial list must be empty"
                );
                values.push(empty_native_list());
            } else if schema.get("counter") == Some(&Json::Bool(true)) {
                values.push(StateValue::Cell(Sp::new(aligned(
                    &input_value("UIntRange<18446744073709551616>", value)?,
                    "u64",
                )?)));
            } else if let Some(ty) = schema.get("scalar").and_then(Json::as_str) {
                values.push(StateValue::Cell(Sp::new(aligned_storage_cell(
                    &input_value(ty, value)?,
                )?)));
            } else if let Some(schema) = schema.get("composite") {
                let schema = checked_record_schema(schema)?;
                let fields = record_values_from_json(&schema, value)?;
                values.push(StateValue::Cell(Sp::new(aligned_record_value(
                    &schema, &fields,
                )?)));
            } else {
                ensure!(
                    value.as_array().is_some_and(|items| items.is_empty()),
                    "initial map tree must be explicitly empty"
                );
                values.push(StateValue::Map(Default::default()));
            }
        } else {
            bail!("unsupported state kind");
        }
    }
    Ok(ChargedState::new(StateValue::Array(
        values.into_iter().collect(),
    )))
}

fn checked_merkle_tree_schema(schema: &Json) -> Result<(u8, bool)> {
    let fields = schema
        .as_object()
        .ok_or_else(|| anyhow!("invalid MerkleTree schema"))?;
    let historic = match fields.get("historic") {
        None if fields.len() == 1 => false,
        Some(Json::Bool(historic)) if fields.len() == 2 => *historic,
        _ => bail!("invalid MerkleTree schema"),
    };
    let depth = fields
        .get("merkleTree")
        .and_then(Json::as_u64)
        .ok_or_else(|| anyhow!("invalid MerkleTree schema"))?;
    ensure!(
        (2..=32).contains(&depth),
        "MerkleTree depth must be between 2 and 32"
    );
    Ok((depth.try_into()?, historic))
}

fn ensure_merkle_tree_depth(plan: &Plan, slot: u32, keys: &[PathPart], depth: u8) -> Result<bool> {
    ensure!(keys.len() <= 12, "MerkleTree path exceeds 12 keys");
    let schema = if keys.is_empty() {
        &plan
            .state
            .get(slot as usize)
            .ok_or_else(|| anyhow!("state slot out of range"))?
            .kind
    } else {
        tree_schema_at_path(plan, slot, keys.len())?
    };
    let (declared_depth, historic) = checked_merkle_tree_schema(schema)?;
    ensure!(
        declared_depth == depth,
        "MerkleTree operation depth differs from state schema"
    );
    Ok(historic)
}

fn ensure_merkle_tree_reset_mode(
    plan: &Plan,
    slot: u32,
    keys: &[PathPart],
    depth: u8,
    empty_history: bool,
) -> Result<bool> {
    let historic = ensure_merkle_tree_depth(plan, slot, keys, depth)?;
    ensure!(
        !empty_history || (!keys.is_empty() && historic),
        "emptyHistory requires a nested historic MerkleTree"
    );
    Ok(historic)
}

fn merkle_tree_default_state(depth: u8, historic: bool, empty_history: bool) -> StateValue<Db> {
    let mut values = vec![
        StateValue::BoundedMerkleTree(MerkleTree::<(), Db>::blank(depth)),
        StateValue::Cell(Sp::new(0u64.into())),
    ];
    if historic {
        let history = if empty_history {
            HashMap::default()
        } else {
            [(field_value(Fr::from(0u64)), StateValue::Null)]
                .into_iter()
                .collect()
        };
        values.push(StateValue::Map(history));
    }
    StateValue::Array(values.into())
}

type HistoricRoots = HashMap<AlignedValue, StateValue<Db>, Db>;

fn merkle_tree_parts(
    state: &StateValue<Db>,
    depth: u8,
    historic: bool,
) -> Result<(&MerkleTree<(), Db>, u64, Option<&HistoricRoots>)> {
    let StateValue::Array(node) = state else {
        bail!("MerkleTree state must be an array");
    };
    ensure!(
        node.len() == 2 + usize::from(historic),
        "MerkleTree state has an invalid shape"
    );
    let Some(StateValue::BoundedMerkleTree(tree)) = node.get(0) else {
        bail!("MerkleTree state is missing its bounded tree");
    };
    ensure!(
        tree.height() == depth,
        "MerkleTree height differs from state schema"
    );
    let Some(StateValue::Cell(count)) = node.get(1) else {
        bail!("MerkleTree state is missing its insertion count");
    };
    let Value::UInt { number, .. } =
        decode_state_cell(count, "UIntRange<18446744073709551616>", "u64")?
    else {
        bail!("MerkleTree count must be UInt64");
    };
    let count: u64 = number.try_into()?;
    ensure!(
        count <= 1u64 << depth,
        "MerkleTree count exceeds its capacity"
    );
    let history = if historic {
        let Some(StateValue::Map(history)) = node.get(2) else {
            bail!("historic MerkleTree state is missing its root map");
        };
        let current = tree
            .root()
            .context("MerkleTree state has an unrehashed root")?
            .0;
        let has_current_root = history
            .get(&field_value(current))
            .is_some_and(|entry| matches!(*entry, StateValue::Null));
        ensure!(
            has_current_root
                || (history.is_empty() && count == 0 && current == Fr::from(0u64)),
            "historic MerkleTree root map is missing its current root"
        );
        Some(history)
    } else {
        None
    };
    Ok((tree, count, history))
}

fn read_state_value(
    context: &QueryContext<Db>,
    slot: u32,
    keys: &[AlignedValue],
) -> Result<StateValue<Db>> {
    let StateValue::Array(array) = context.state.get_ref() else {
        bail!("expected array state")
    };
    let mut cell = Sp::new(
        array
            .get(slot as usize)
            .ok_or_else(|| anyhow!("state slot out of range"))?
            .clone(),
    );
    for key in keys {
        cell = match &*cell {
            StateValue::Map(map) => map
                .get(key)
                .ok_or_else(|| anyhow!("missing map path key"))?,
            _ => bail!("state path does not address a map"),
        };
    }
    Ok((*cell).clone())
}

fn read_state_aligned(
    context: &QueryContext<Db>,
    slot: u32,
    keys: &[AlignedValue],
) -> Result<AlignedValue> {
    let StateValue::Cell(ref value) = read_state_value(context, slot, keys)? else {
        bail!("expected state cell")
    };
    Ok((**value).clone())
}

fn read_state_cell(
    context: &QueryContext<Db>,
    slot: u32,
    keys: &[AlignedValue],
    ty: &str,
    alignment: &str,
) -> Result<Value> {
    decode_state_cell(&read_state_aligned(context, slot, keys)?, ty, alignment)
}

fn decode_state_cell(value: &AlignedValue, ty: &str, alignment: &str) -> Result<Value> {
    ensure!(
        value.alignment.fits(&value.value),
        "state cell encoding mismatch"
    );
    let parsed = ScalarType::parse(ty)?;
    let decoded = if parsed == ScalarType::OpaqueBytes {
        ensure!(
            alignment == "compress",
            "opaque byte read requires Compress alignment"
        );
        ensure!(
            value.alignment == Alignment::singleton(AlignmentAtom::Compress),
            "opaque byte state cell alignment mismatch"
        );
        ensure!(value.value.0.len() == 1, "invalid opaque byte atom count");
        let decoded = Value::OpaqueBytes(value.value.0[0].0.clone());
        decoded.validate()?;
        decoded
    } else if let Some(length) = parsed.bytes_length() {
        ensure!(
            byte_alignment_length(alignment)? == Some(length),
            "byte state read alignment mismatch"
        );
        ensure!(
            value.alignment
                == Alignment::singleton(AlignmentAtom::Bytes {
                    length: length as u32,
                }),
            "byte state cell alignment mismatch"
        );
        ensure!(value.value.0.len() == 1, "invalid byte state atom count");
        let atom = value.value.0.first().expect("one atom checked");
        ensure!(atom.0.len() <= length, "byte state cell length mismatch");
        let mut bytes = atom.0.clone();
        bytes.resize(length, 0);
        Value::Bytes(bytes)
    } else {
        let mut fields = Vec::new();
        value.value_only_field_repr(&mut fields);
        match &parsed {
            ScalarType::Native => {
                ensure!(fields.len() == 1, "expected scalar state cell");
                Value::Native(fields[0])
            }
            ScalarType::Bool => {
                ensure!(fields.len() == 1, "expected scalar state cell");
                Value::Bool(
                    bool::try_from(fields[0]).map_err(|_| anyhow!("noncanonical state bool"))?,
                )
            }
            ScalarType::UInt(_) => {
                ensure!(fields.len() == 1, "expected scalar state cell");
                input_value(ty, &Json::String(field_decimal(fields[0])))?
            }
            ScalarType::Bytes32 | ScalarType::Bytes(_) | ScalarType::OpaqueBytes => {
                unreachable!("decoded above")
            }
            ScalarType::JubjubScalar | ScalarType::JubjubPoint => {
                decode_typed_scalar(&parsed, &fields)?
            }
            #[cfg(feature = "zkir-321")]
            ScalarType::Foreign(_) => decode_typed_scalar(&parsed, &fields)?,
        }
    };
    let typed_scalar = match &parsed {
        ScalarType::JubjubScalar | ScalarType::JubjubPoint => true,
        #[cfg(feature = "zkir-321")]
        ScalarType::Foreign(_) => true,
        _ => false,
    };
    let encoded = if parsed == ScalarType::OpaqueBytes {
        aligned_opaque_bytes(&decoded)?
    } else if parsed.bytes_length().is_some() {
        aligned_bytes(&decoded)?
    } else if typed_scalar {
        aligned_storage_cell(&decoded)?
    } else {
        aligned(&decoded, alignment)?
    };
    ensure!(
        *value == encoded,
        "state cell alignment or encoding mismatch"
    );
    Ok(decoded)
}

fn tree_schema_at_path(plan: &Plan, slot: u32, depth: usize) -> Result<&Json> {
    let mut schema = plan
        .state
        .get(slot as usize)
        .and_then(|state| state.kind.get("tree"))
        .ok_or_else(|| anyhow!("record path requires tree state"))?;
    ensure!(depth < 16, "record path exceeds native index limit");
    for _ in 0..depth {
        schema = schema
            .get("map")
            .and_then(Json::as_array)
            .filter(|parts| parts.len() == 2)
            .and_then(|parts| parts.get(1))
            .ok_or_else(|| anyhow!("record path exceeds declared schema"))?;
    }
    Ok(schema)
}

fn list_element_schema_at_path(plan: &Plan, slot: u32, depth: usize) -> Result<&Json> {
    ensure!(depth <= 13, "list path exceeds native insertion depth");
    tree_schema_at_path(plan, slot, depth)?
        .get("list")
        .ok_or_else(|| anyhow!("path does not select a List"))
}

/// Validate an operation's canonical scalar token or existing record schema against state.
/// `None` denotes the record wire form, `Some` denotes a scalar element.
fn list_operation_scalar_type(
    plan: &Plan,
    slot: u32,
    keys: &[PathPart],
    operation_schema: &Json,
) -> Result<Option<ScalarType>> {
    let element = list_element_schema_at_path(plan, slot, keys.len())?;
    if let Some(ty_name) = element.get("scalar").and_then(Json::as_str) {
        ensure!(
            operation_schema.as_str() == Some(ty_name),
            "List scalar operation differs from state schema"
        );
        return Ok(Some(validate_tree_scalar_type(ty_name)?));
    }
    let record = element
        .get("composite")
        .ok_or_else(|| anyhow!("List state requires a scalar or record element"))?;
    ensure!(
        operation_schema == record,
        "List record operation differs from state schema"
    );
    Ok(None)
}

fn list_scalar_storage_alignment(ty: &ScalarType) -> String {
    match ty {
        ScalarType::Bytes32 => "bytes32".to_owned(),
        ScalarType::Bytes(length) => format!("bytes:{length}"),
        ScalarType::OpaqueBytes => "compress".to_owned(),
        _ => "field".to_owned(),
    }
}

fn list_scalar_atom_count(ty: &ScalarType) -> usize {
    match ty {
        ScalarType::JubjubPoint => 2,
        #[cfg(feature = "zkir-321")]
        ScalarType::Foreign(ty) => ty.native_type().encoded_len(),
        _ => 1,
    }
}

fn list_scalar_payload_field_count(ty: &ScalarType) -> usize {
    match ty {
        ScalarType::Bytes32 => 2,
        ScalarType::Bytes(length) => length.div_ceil(31),
        ScalarType::JubjubPoint => 2,
        #[cfg(feature = "zkir-321")]
        ScalarType::Foreign(ty) => ty.native_type().encoded_len(),
        _ => 1,
    }
}

fn list_scalar_popeq_impact_width(ty: &ScalarType) -> usize {
    2 + list_scalar_atom_count(ty) + list_scalar_payload_field_count(ty)
}

fn list_scalar_push_impact_width(ty: &ScalarType) -> usize {
    3 + list_scalar_atom_count(ty) + list_scalar_payload_field_count(ty)
}

fn validate_map_size_path(plan: &Plan, slot: u32, depth: usize) -> Result<()> {
    let kind = &plan
        .state
        .get(slot as usize)
        .ok_or_else(|| anyhow!("state slot out of range"))?
        .kind;
    let schema = match kind.get("tree") {
        Some(_) => tree_schema_at_path(plan, slot, depth)?,
        None => {
            ensure!(depth == 0, "scalar map size does not take a key");
            kind
        }
    };
    if let Some(key) = schema.get("set") {
        ledger_key_type(key)?;
        return Ok(());
    }
    ensure!(
        schema
            .get("map")
            .and_then(Json::as_array)
            .is_some_and(|parts| parts.len() == 2),
        "size path must select a Map"
    );
    Ok(())
}

fn empty_native_list() -> StateValue<Db> {
    StateValue::Array(
        vec![
            StateValue::Null,
            StateValue::Null,
            StateValue::Cell(Sp::new(0u64.into())),
        ]
        .into(),
    )
}

fn native_list_value(
    context: &QueryContext<Db>,
    slot: u32,
    keys: &[AlignedValue],
    schema: &Json,
) -> Result<(u64, Option<AlignedValue>)> {
    let StateValue::Array(ref node) = read_state_value(context, slot, keys)? else {
        bail!("expected native List array")
    };
    ensure!(node.len() == 3, "invalid native List node width");
    let StateValue::Cell(length) = node.get(2).unwrap() else {
        bail!("invalid List length cell")
    };
    let Value::UInt { number, .. } =
        decode_state_cell(length, "UIntRange<18446744073709551616>", "u64")?
    else {
        unreachable!()
    };
    let length = u64::try_from(number).map_err(|_| anyhow!("invalid List length"))?;
    if length == 0 {
        ensure!(
            matches!(node.get(0), Some(StateValue::Null))
                && matches!(node.get(1), Some(StateValue::Null)),
            "invalid empty List sentinel"
        );
        return Ok((0, None));
    }
    ensure!(
        matches!(node.get(1), Some(StateValue::Array(_))),
        "invalid List tail"
    );
    let StateValue::Cell(head) = node.get(0).unwrap() else {
        bail!("invalid List head cell")
    };
    if let Some(ty_name) = schema.get("scalar").and_then(Json::as_str) {
        let ty = validate_tree_scalar_type(ty_name)?;
        decode_state_cell(head, ty_name, &list_scalar_storage_alignment(&ty))?;
    } else {
        let checked = checked_record_schema(
            schema
                .get("composite")
                .ok_or_else(|| anyhow!("List state requires a scalar or record element"))?,
        )?;
        decode_record_value(&checked, head)?;
    }
    Ok((length, Some((**head).clone())))
}

fn list_index(index: u8) -> Op<ResultModeVerify, Db> {
    Op::Idx {
        cached: false,
        push_path: false,
        path: vec![Key::Value(
            AlignedValue::from(index).try_into().expect("u8 index"),
        )]
        .try_into()
        .expect("one index"),
    }
}

fn merkle_tree_index(index: u8, push_path: bool) -> Op<ResultModeVerify, Db> {
    Op::Idx {
        cached: false,
        push_path,
        path: vec![Key::Value(
            AlignedValue::from(index)
                .try_into()
                .expect("u8 MerkleTree index"),
        )]
        .try_into()
        .expect("one MerkleTree index"),
    }
}

fn append_historic_merkle_root(program: &mut Program) -> Result<()> {
    program.extend([
        merkle_tree_index(2, true),
        Op::Dup { n: 2 },
        merkle_tree_index(0, false),
        Op::Root,
        push_native_state(StateValue::Null, true)?,
        Op::Ins {
            cached: false,
            n: 1,
        },
    ]);
    Ok(())
}

fn push_native_state(value: StateValue<Db>, storage: bool) -> Result<Op<ResultModeVerify, Db>> {
    Ok(Op::Push {
        storage,
        value: value
            .try_into_checked()
            .map_err(|_| anyhow!("invalid native state value for Push"))?,
    })
}

fn mint_amount(amount: &Expr, env: &Environment) -> Result<u64> {
    let Value::UInt { number, maximum } = evaluate(amount, env)? else {
        bail!("mint amount must be UInt64");
    };
    ensure!(maximum == u64::MAX.into(), "mint amount must be UInt64");
    Ok(number.try_into()?)
}

fn unshielded_amount(amount: &Expr, env: &Environment) -> Result<u128> {
    let Value::UInt { number, maximum } = evaluate(amount, env)? else {
        bail!("unshielded amount must be UInt128");
    };
    ensure!(
        maximum == u128::MAX.into(),
        "unshielded amount must be UInt128"
    );
    Ok(number.try_into()?)
}

fn append_unshielded_spend_claim(
    program: &mut Program,
    token: TokenType,
    amount: u128,
    is_contract: bool,
    recipient: HashOutput,
) -> Result<Op<ResultModeVerify, Db>> {
    let address = if is_contract {
        PublicAddress::Contract(ContractAddress(recipient))
    } else {
        PublicAddress::User(UserAddress(recipient))
    };
    let key = onchain_runtime::context::ClaimedUnshieldedSpendsKey(token, address);
    append_token_accumulation(program, 8, key.into(), amount.into())
}

fn append_token_accumulation(
    program: &mut Program,
    slot: u8,
    key: AlignedValue,
    amount: AlignedValue,
) -> Result<Op<ResultModeVerify, Db>> {
    program.extend([
        Op::Swap { n: 0 },
        Op::Idx {
            cached: true,
            push_path: true,
            path: vec![Key::Value(
                AlignedValue::from(slot).try_into().expect("u8 index"),
            )]
            .try_into()?,
        },
        push_native_state(StateValue::Cell(Sp::new(key)), false)?,
        Op::Dup { n: 1 },
        Op::Dup { n: 1 },
        Op::Member,
        push_native_state(StateValue::Cell(Sp::new(amount)), false)?,
        Op::Swap { n: 0 },
        Op::Neg,
        Op::Branch { skip: 4 },
        Op::Dup { n: 2 },
        Op::Dup { n: 2 },
        Op::Idx {
            cached: true,
            push_path: false,
            path: vec![Key::Stack].try_into()?,
        },
        Op::Add,
        Op::Ins { cached: true, n: 2 },
    ]);
    Ok(Op::Swap { n: 0 })
}

fn record_schema_at_path(plan: &Plan, slot: u32, depth: usize) -> Result<&Json> {
    tree_schema_at_path(plan, slot, depth)?
        .get("composite")
        .ok_or_else(|| anyhow!("path does not select a record"))
}
fn native_index(
    plan: &Plan,
    slot: u32,
    keys: &[PathPart],
    push_path: bool,
    env: &Environment,
) -> Result<(Op<ResultModeVerify, Db>, Vec<AlignedValue>)> {
    let types = map_path_key_types(plan, slot, keys.len())?;
    let mut path = vec![Key::Value(
        field_value(Fr::from(slot as u64))
            .try_into()
            .map_err(|_| anyhow!("invalid native index key"))?,
    )];
    let mut values = Vec::with_capacity(keys.len());
    for (part, ty) in keys.iter().zip(types) {
        ensure!(
            part.alignment == key_alignment(&ty),
            "map path key alignment mismatch"
        );
        let key = evaluate(&part.expression, env)?;
        validate_ledger_key_value(&ty, &key)?;
        let value = aligned(&key, &part.alignment)?;
        path.push(Key::Value(
            value
                .clone()
                .try_into()
                .map_err(|_| anyhow!("invalid native map key"))?,
        ));
        values.push(value);
    }
    Ok((
        Op::Idx {
            cached: false,
            push_path,
            path: path.into_iter().collect(),
        },
        values,
    ))
}
fn advance_native_state_prefix(
    context: &mut QueryContext<Db>,
    program: &[Op<ResultModeVerify, Db>],
    materialized: &mut usize,
    boundary: usize,
    cost: &onchain_runtime::cost_model::CostModel,
) -> Result<()> {
    ensure!(
        *materialized <= boundary && boundary <= program.len(),
        "invalid native state prefix boundary"
    );
    if *materialized == boundary {
        return Ok(());
    }
    *context = context
        .query(&program[*materialized..boundary], None, cost)
        .map_err(|_| anyhow!("native state prefix rejected"))?
        .context;
    *materialized = boundary;
    Ok(())
}

/// Gather the native VM's actual Bool result for a Member opcode. The gather
/// query replays only the current ordered prefix against the state after prior
/// writes, then appends a read to expose Member's result.
fn native_member_result(
    context: &QueryContext<Db>,
    program: &[Op<ResultModeVerify, Db>],
    cost: &onchain_runtime::cost_model::CostModel,
) -> Result<bool> {
    ensure!(
        matches!(program.last(), Some(Op::Member)),
        "membership read lacks a native Member opcode"
    );
    let mut gather_program: Vec<Op<ResultModeGather, Db>> = program
        .iter()
        .cloned()
        .map(|operation| operation.translate::<ResultModeGather, _>(|_| ()))
        .collect();
    gather_program.push(Op::Popeq {
        cached: false,
        result: (),
    });
    let result = context
        .query(&gather_program, None, cost)
        .map_err(|_| anyhow!("native map membership query rejected"))?
        .events
        .into_iter()
        .rev()
        .find_map(|event| match event {
            GatherEvent::Read(value) => Some(value),
            GatherEvent::Log(_) => None,
        })
        .ok_or_else(|| anyhow!("native map membership query returned no Bool"))?;
    let absent = aligned(&Value::Bool(false), "bit")?;
    let present = aligned(&Value::Bool(true), "bit")?;
    if result == absent {
        Ok(false)
    } else if result == present {
        Ok(true)
    } else {
        bail!("native Member returned a noncanonical Bool")
    }
}

fn aligned_call_returns(values: &[(String, Value)]) -> Result<AlignedValue> {
    aligned_call_values(values.iter().map(|(_, value)| value))
}

fn aligned_call_values<'a>(values: impl Iterator<Item = &'a Value>) -> Result<AlignedValue> {
    let mut fields = Vec::new();
    for value in values {
        value.validate()?;
        match value {
            Value::Bytes(_) => aligned_bytes(value)?.value_only_field_repr(&mut fields),
            Value::OpaqueBytes(_) => {
                aligned_opaque_bytes(value)?.value_only_field_repr(&mut fields)
            }
            Value::JubjubScalar(value) => fields.push(jubjub::scalar_native(*value)?),
            Value::JubjubPoint(value) => fields.extend(jubjub::coordinates(*value)?),
            #[cfg(feature = "zkir-321")]
            Value::Foreign(value) => fields.extend(value.encode()?),
            _ => fields.push(value.field_encoding()?),
        }
    }
    ensure!(fields.len() <= 256, "too many native call payload fields");
    Ok(aligned_fields(&fields))
}

fn reconstruct_return_views(
    views: &[ReturnView],
    return_values: &[(String, Value)],
) -> Result<Vec<(String, Json)>> {
    let values: BTreeMap<_, _> = return_values
        .iter()
        .map(|(name, value)| (name.as_str(), value))
        .collect();
    views
        .iter()
        .map(|view| {
            let schema_bytes = serde_json::to_vec(&view.schema)?;
            let schema = Schema::from_json(&schema_bytes)?;
            let leaves = view
                .fields
                .iter()
                .map(|field| match values.get(field.as_str()).copied() {
                    Some(Value::Native(value)) => Ok(Json::String(field_decimal(*value))),
                    Some(_) => bail!("composite return field is not Native"),
                    None => bail!("composite return field is missing"),
                })
                .collect::<Result<Vec<_>>>()?;
            let encoded = schema.from_native_leaves_json(&leaves)?;
            Ok((view.name.clone(), serde_json::from_slice(&encoded)?))
        })
        .collect()
}

pub struct Execution {
    pub program: Program,
    /// Exact source schedule returned by the checked native Impact groups.
    pub activity_schedule: Vec<Option<usize>>,
    pub after: QueryContext<Db>,
    /// Public logs produced during local simulation, in execution order.
    pub logs: Vec<VersionedLogItem<Db>>,
    pub guaranteed: Option<Transcript<Db>>,
    pub fallible: Option<Transcript<Db>>,
    pub preimage: ProofPreimage,
    call_input: AlignedValue,
    call_input_header: Vec<(String, Json)>,
    return_values: Vec<(String, Value)>,
    logical_return_views: Vec<(String, Json)>,
    grouped_return_fields: BTreeSet<String>,
}
impl Execution {
    /// Typed source-declared results. Call `check` before treating them as checked.
    pub fn returns(&self) -> &[(String, Value)] {
        &self.return_values
    }
    pub fn returns_json(&self) -> BTreeMap<String, Json> {
        let mut values: BTreeMap<_, _> = self
            .return_values
            .iter()
            .filter(|(name, _)| !self.grouped_return_fields.contains(name))
            .map(|(name, value)| (name.clone(), value.public_json()))
            .collect();
        values.extend(self.logical_return_views.iter().cloned());
        values
    }
    pub(crate) fn call_output(&self) -> Result<AlignedValue> {
        aligned_call_returns(&self.return_values)
    }
    pub(crate) fn call_input(&self) -> Result<AlignedValue> {
        Ok(self.call_input.clone())
    }
}

#[derive(Clone, Debug)]
pub struct PreparationRead {
    pub name: String,
    pub active: bool,
    /// Only bindings declared by this read and currently produced by native preparation.
    pub values: BTreeMap<String, Value>,
}

#[derive(Clone, Debug)]
pub enum PreparationStep {
    PendingInputs(Vec<Input>),
    Operation {
        index: usize,
        read: Option<PreparationRead>,
    },
    Complete,
}

/// Incremental owner of the same native preparation state used by `prepare`.
///
/// A cursor freezes its plan, parameters, address, and starting state. Missing private inputs
/// pause the next operation before its native state preparation starts.
pub struct PreparationCursor {
    plan: Plan,
    env: Environment,
    supplied_inputs: BTreeSet<String>,
    deferred_outputs: BTreeMap<String, Vec<Input>>,
    context: QueryContext<Db>,
    has_block_time: bool,
    params: LedgerParameters,
    prefix_context: QueryContext<Db>,
    materialized_prefix: usize,
    mutation_boundary: usize,
    program: Program,
    read_index: usize,
    previous_index: Option<(u32, Vec<AlignedValue>)>,
    member_result_pending: bool,
    has_written: bool,
    activity_schedule: Vec<Option<usize>>,
    next_operation: usize,
    poisoned: bool,
    completed: bool,
}

fn refresh_circuit_outputs(
    plan: &Plan,
    env: &mut Environment,
) -> Result<BTreeMap<String, Vec<Input>>> {
    validate_shared_binding_environment(plan, env)?;
    let mut deferred = BTreeMap::new();
    let remaining: Vec<_> = plan
        .circuit
        .outputs
        .iter()
        .filter(|output| !env.contains_key(&output.name))
        .collect();
    let shared_bindings = if remaining.is_empty() || plan.circuit.shared_bindings.is_empty() {
        Vec::new()
    } else {
        match evaluate_shared_bindings(plan, env) {
            Ok(values) => values,
            Err(error) => {
                let Some(missing) = unbound_reference(&error) else {
                    return Err(error);
                };
                let Some(input) = plan
                    .circuit
                    .inputs
                    .iter()
                    .find(|input| input.name == missing)
                else {
                    return Err(error);
                };
                ensure!(
                    input.visibility == "private" && !env.contains_key(missing),
                    "{}",
                    error
                );
                return Ok(remaining
                    .into_iter()
                    .map(|output| (output.name.clone(), vec![input.clone()]))
                    .collect());
            }
        }
    };
    let mut local = if shared_bindings.is_empty() {
        None
    } else {
        Some(circuit_output_environment(env, &shared_bindings)?)
    };
    for output in &plan.circuit.outputs {
        if env.contains_key(&output.name) {
            continue;
        }
        match evaluate(&output.expression, local.as_ref().unwrap_or(env)) {
            Ok(value) => {
                ensure!(
                    value.scalar_type() == ScalarType::parse(&output.ty)?,
                    "output type mismatch"
                );
                env.insert(output.name.clone(), value.clone());
                if let Some(local) = &mut local {
                    local.insert(output.name.clone(), value);
                }
            }
            Err(error) => {
                let Some(missing) = unbound_reference(&error) else {
                    return Err(error);
                };
                if let Some(input) = plan
                    .circuit
                    .inputs
                    .iter()
                    .find(|input| input.name == missing)
                {
                    ensure!(
                        input.visibility == "private" && !env.contains_key(missing),
                        "{}",
                        error
                    );
                    deferred.insert(output.name.clone(), vec![input.clone()]);
                } else if let Some(dependencies) = deferred.get(missing) {
                    deferred.insert(output.name.clone(), dependencies.clone());
                } else {
                    return Err(error);
                }
            }
        }
    }
    Ok(deferred)
}

fn validate_shared_binding_environment(plan: &Plan, env: &Environment) -> Result<()> {
    ensure!(
        plan.circuit
            .shared_bindings
            .iter()
            .all(|(name, _)| !env.contains_key(name)),
        "shared binding shadows an existing environment name"
    );
    Ok(())
}

fn circuit_output_environment(
    env: &Environment,
    shared_bindings: &[(String, Value)],
) -> Result<Environment> {
    let mut local = env.clone();
    for (name, value) in shared_bindings {
        ensure!(
            !local.contains_key(name),
            "shared binding shadows an existing environment name"
        );
        local.insert(name.clone(), value.clone());
    }
    Ok(local)
}

fn evaluate_shared_bindings(plan: &Plan, env: &Environment) -> Result<Vec<(String, Value)>> {
    let input_names: BTreeSet<_> = plan
        .circuit
        .inputs
        .iter()
        .map(|input| input.name.as_str())
        .collect();
    let output_names: BTreeSet<_> = plan
        .circuit
        .outputs
        .iter()
        .map(|output| output.name.as_str())
        .collect();
    let shared_names: BTreeSet<_> = plan
        .circuit
        .shared_bindings
        .iter()
        .map(|(name, _)| name.as_str())
        .collect();
    let mut local: Environment = env
        .iter()
        .filter(|(name, _)| input_names.contains(name.as_str()))
        .map(|(name, value)| (name.clone(), value.clone()))
        .collect();
    let mut values = Vec::with_capacity(plan.circuit.shared_bindings.len());

    for (name, expression) in &plan.circuit.shared_bindings {
        let value = match evaluate(expression, &local) {
            Ok(value) => value,
            Err(error)
                if unbound_reference(&error)
                    .is_some_and(|missing| shared_names.contains(missing)) =>
            {
                bail!("shared binding has an unsupported forward dependency")
            }
            Err(error)
                if unbound_reference(&error)
                    .is_some_and(|missing| output_names.contains(missing)) =>
            {
                bail!("shared binding depends on a circuit output")
            }
            Err(error) => return Err(error),
        };
        local.insert(name.clone(), value.clone());
        values.push((name.clone(), value));
    }
    Ok(values)
}

fn required_missing_input(
    error: anyhow::Error,
    plan: &Plan,
    env: &Environment,
    deferred_outputs: &BTreeMap<String, Vec<Input>>,
) -> Result<Input> {
    let Some(name) = unbound_reference(&error) else {
        return Err(error);
    };
    if let Some(input) = plan.circuit.inputs.iter().find(|input| input.name == name) {
        ensure!(
            input.visibility == "private" && !env.contains_key(name),
            "{}",
            error
        );
        return Ok(input.clone());
    }
    if let Some(dependencies) = deferred_outputs.get(name) {
        return dependencies
            .first()
            .cloned()
            .ok_or_else(|| anyhow!("deferred output has no missing private input"));
    }
    Err(error)
}

fn probe_expression(
    expression: &Expr,
    plan: &Plan,
    env: &Environment,
    deferred_outputs: &BTreeMap<String, Vec<Input>>,
) -> Result<Option<Input>> {
    match evaluate(expression, env) {
        Ok(_) => Ok(None),
        Err(error) => required_missing_input(error, plan, env, deferred_outputs).map(Some),
    }
}

fn probe_expressions<'a>(
    expressions: impl IntoIterator<Item = &'a Expr>,
    plan: &Plan,
    env: &Environment,
    deferred_outputs: &BTreeMap<String, Vec<Input>>,
) -> Result<Option<Input>> {
    for expression in expressions {
        if let Some(input) = probe_expression(expression, plan, env, deferred_outputs)? {
            return Ok(Some(input));
        }
    }
    Ok(None)
}

fn probe_paths<'a>(
    keys: impl IntoIterator<Item = &'a PathPart>,
    plan: &Plan,
    env: &Environment,
    deferred_outputs: &BTreeMap<String, Vec<Input>>,
) -> Result<Option<Input>> {
    probe_expressions(
        keys.into_iter().map(|part| &part.expression),
        plan,
        env,
        deferred_outputs,
    )
}

fn probe_instruction(
    instruction: &Instruction,
    plan: &Plan,
    env: &Environment,
    deferred_outputs: &BTreeMap<String, Vec<Input>>,
    previous_index: Option<&(u32, Vec<AlignedValue>)>,
) -> Result<Option<Input>> {
    match instruction {
        Instruction::Guarded { .. } => bail!("nested guarded native operation is unsupported"),
        Instruction::Index { key, .. } => key
            .as_ref()
            .map(|key| probe_expression(key, plan, env, deferred_outputs))
            .transpose()
            .map(Option::flatten),
        Instruction::IndexPath { keys, .. }
        | Instruction::ListPopFront { keys, .. }
        | Instruction::MapRemove { keys, .. }
        | Instruction::ListReset { keys, .. } => probe_paths(keys, plan, env, deferred_outputs),
        Instruction::ListLength { keys, .. } | Instruction::ListHead { keys, .. } => {
            probe_paths(keys, plan, env, deferred_outputs)
        }
        Instruction::MapSize { keys, .. } | Instruction::MapIsEmpty { keys, .. } => {
            probe_paths(keys, plan, env, deferred_outputs)
        }
        Instruction::MerkleTreeIsFull { keys, .. }
        | Instruction::MerkleTreeReset { keys, .. }
        | Instruction::MerkleTreeResetHistory { keys, .. } => {
            probe_paths(keys, plan, env, deferred_outputs)
        }
        Instruction::MerkleTreeInsertHash { keys, hash, .. }
        | Instruction::MerkleTreeCheckRoot {
            keys,
            expected: hash,
            ..
        } => probe_expressions(
            keys.iter().map(|part| &part.expression).chain([hash]),
            plan,
            env,
            deferred_outputs,
        ),
        Instruction::MerkleTreeInsertHashIndex {
            keys, hash, index, ..
        } => probe_expressions(
            keys.iter()
                .map(|part| &part.expression)
                .chain([hash, index]),
            plan,
            env,
            deferred_outputs,
        ),
        Instruction::ListPushFront {
            keys, expressions, ..
        } => {
            if let Some(input) = probe_paths(keys, plan, env, deferred_outputs)? {
                Ok(Some(input))
            } else {
                probe_expressions(expressions, plan, env, deferred_outputs)
            }
        }
        Instruction::Push { expression, .. } => {
            probe_expression(expression, plan, env, deferred_outputs)
        }
        Instruction::PushFields { expressions, .. } => {
            probe_expressions(expressions, plan, env, deferred_outputs)
        }
        Instruction::ClaimContractCall {
            address,
            entry_point_hash,
            commitment,
        } => probe_expressions(
            [address, entry_point_hash, commitment],
            plan,
            env,
            deferred_outputs,
        ),
        Instruction::MintShielded { domain, amount }
        | Instruction::MintUnshielded { domain, amount } => {
            probe_expressions([domain, amount], plan, env, deferred_outputs)
        }
        Instruction::IncUnshieldedOutputs {
            color,
            amount,
            is_unshielded,
        }
        | Instruction::IncUnshieldedInputs {
            color,
            amount,
            is_unshielded,
        } => probe_expressions([color, amount, is_unshielded], plan, env, deferred_outputs),
        Instruction::ClaimUnshieldedCoinSpend {
            color,
            amount,
            is_unshielded,
            is_contract,
            recipient,
        } => probe_expressions(
            [color, amount, is_unshielded, is_contract, recipient],
            plan,
            env,
            deferred_outputs,
        ),
        Instruction::ReceiveShieldedToMap {
            nonce,
            color,
            amount,
            commitment,
            ..
        }
        | Instruction::WriteShieldedCoinCell {
            nonce,
            color,
            amount,
            commitment,
            ..
        }
        | Instruction::InsertShieldedCoinSet {
            nonce,
            color,
            amount,
            commitment,
            ..
        } => probe_expressions(
            [nonce, color, amount, commitment],
            plan,
            env,
            deferred_outputs,
        ),
        Instruction::SpendShieldedFromMap {
            nonce,
            color,
            amount,
            recipient,
            nullifier,
            output_commitment,
        } => probe_expressions(
            [
                nonce,
                color,
                amount,
                recipient,
                nullifier,
                output_commitment,
            ],
            plan,
            env,
            deferred_outputs,
        ),
        Instruction::SendShieldedFromMap {
            nonce,
            color,
            input_amount,
            send_amount,
            recipient,
            nullifier,
            output_commitment,
            change_commitment,
        } => probe_expressions(
            [
                nonce,
                color,
                input_amount,
                send_amount,
                recipient,
                nullifier,
                output_commitment,
                change_commitment,
            ],
            plan,
            env,
            deferred_outputs,
        ),
        Instruction::RelayShieldedImmediate {
            nonce,
            color,
            amount,
            recipient,
            input_commitment,
            nullifier,
            output_commitment,
        } => probe_expressions(
            [
                nonce,
                color,
                amount,
                recipient,
                input_commitment,
                nullifier,
                output_commitment,
            ],
            plan,
            env,
            deferred_outputs,
        ),
        Instruction::RequireContractCaller { address } => {
            probe_expression(address, plan, env, deferred_outputs)
        }
        Instruction::ReadCaller { .. } => Ok(None),
        Instruction::ReadContractAddress { .. } => Ok(None),
        Instruction::ReadTokenBalance {
            color,
            is_unshielded,
            comparison,
            ..
        } => probe_expressions(
            std::iter::once(color)
                .chain(std::iter::once(is_unshielded))
                .chain(comparison.iter().map(BalanceComparison::limit)),
            plan,
            env,
            deferred_outputs,
        ),
        Instruction::EmitEvent { tag, payload } => {
            event_payload_length(*tag)?;
            probe_expression(payload, plan, env, deferred_outputs)
        }
        Instruction::BlockTimeCompare { deadline, .. } => {
            probe_expression(deadline, plan, env, deferred_outputs)
        }
        Instruction::CounterLessThan {
            keys, threshold, ..
        } => probe_expressions(
            keys.iter().map(|part| &part.expression).chain([threshold]),
            plan,
            env,
            deferred_outputs,
        ),
        Instruction::AddImmediate { amount } | Instruction::SubImmediate { amount } => match amount
        {
            ImmediateAmount::Literal(_) => Ok(None),
            ImmediateAmount::Expression(expression) => {
                validate_counter_adjustment_path(plan, previous_index)?;
                probe_expression(expression, plan, env, deferred_outputs)
            }
        },
        // Read expressions bind values produced by the state read itself.
        Instruction::Popeq { .. }
        | Instruction::PopeqFields { .. }
        | Instruction::Dup
        | Instruction::Checkpoint
        | Instruction::New
        | Instruction::Member
        | Instruction::Insert { .. } => Ok(None),
    }
}

fn consume_contract_caller_reads(
    plan: &Plan,
    index: &mut usize,
    guard: Option<&Expr>,
) -> Result<()> {
    let start = *index;
    for field in 0..5 {
        let read = plan
            .reads
            .get(start + field)
            .ok_or_else(|| anyhow!("missing contract caller transcript field"))?;
        ensure!(
            read.name == format!("_noctium_contract_caller_{start}_{field}")
                && read.ty == "Native"
                && read.guard.as_ref() == guard
                && read.components.is_empty()
                && read.projections.is_none()
                && read.schema.is_none(),
            "invalid contract caller transcript field"
        );
    }
    *index += 5;
    Ok(())
}

fn bind_caller_reads(
    plan: &Plan,
    index: &mut usize,
    guard: Option<&Expr>,
    destinations: [&str; 4],
    active: bool,
    caller: Option<PublicAddress>,
    env: &mut Environment,
) -> Result<PreparationRead> {
    let zero = [0; 32];
    let (contract, user) = match caller {
        Some(PublicAddress::Contract(address)) => (address.0.0, zero),
        Some(PublicAddress::User(address)) => (zero, address.0.0),
        None => (zero, zero),
    };
    let returned = [
        Value::Bool(caller.is_some()),
        Value::Bool(matches!(caller, Some(PublicAddress::Contract(_)))),
        Value::Bytes(contract.to_vec()),
        Value::Bytes(user.to_vec()),
    ];
    let mut values = BTreeMap::new();
    for (destination, value) in destinations.into_iter().zip(returned) {
        let read = plan
            .reads
            .get(*index)
            .ok_or_else(|| anyhow!("missing caller read"))?;
        ensure!(
            read.name == destination
                && ScalarType::parse(&read.ty)? == value.scalar_type()
                && read.guard.as_ref() == guard
                && !env.contains_key(destination),
            "caller read schema mismatch"
        );
        if matches!(value, Value::Bytes(_)) {
            validate_byte_read_projections(read, &ScalarType::Bytes32)?;
        } else {
            ensure!(
                read.schema.is_none() && read.components.is_empty() && read.projections.is_none(),
                "caller flag has unexpected read projections"
            );
        }
        env.insert(destination.to_owned(), value.clone());
        values.insert(destination.to_owned(), value);
        *index += 1;
    }
    Ok(PreparationRead {
        name: destinations[0].to_owned(),
        active,
        values,
    })
}

fn append_caller_read(
    program: &mut Program,
    caller: Option<PublicAddress>,
) -> Result<Op<ResultModeVerify, Db>> {
    let absent = AlignedValue::concat([
        &false.into(),
        &PublicAddress::User(UserAddress(HashOutput([0; 32]))).into(),
    ]);
    let result = match caller {
        Some(address) => AlignedValue::concat([&true.into(), &address.into()]),
        None => absent.clone(),
    };
    let push_one = push_native_state(StateValue::Cell(Sp::new(1u8.into())), false)?;
    program.extend([
        Op::Dup { n: 2 },
        list_index(6),
        Op::Dup { n: 0 },
        Op::Type,
        push_one.clone(),
        Op::Eq,
        Op::Branch { skip: 4 },
        push_one,
        Op::Swap { n: 0 },
        Op::Concat {
            cached: false,
            n: 66,
        },
        Op::Jmp { skip: 2 },
        Op::Pop,
        push_native_state(StateValue::Cell(Sp::new(absent)), false)?,
    ]);
    Ok(Op::Popeq {
        cached: false,
        result,
    })
}

fn bind_contract_address(
    read: Option<&Read>,
    guard: Option<&Expr>,
    destination: &str,
    address: Option<ContractAddress>,
    env: &mut Environment,
) -> Result<PreparationRead> {
    let read = read.ok_or_else(|| anyhow!("missing contract address read"))?;
    ensure!(
        read.name == destination
            && ScalarType::parse(&read.ty)? == ScalarType::Bytes32
            && read.guard.as_ref() == guard,
        "contract address read schema mismatch"
    );
    validate_byte_read_projections(read, &ScalarType::Bytes32)?;
    ensure!(
        !env.contains_key(destination),
        "contract address read shadows an existing value"
    );
    let value = Value::Bytes(address.map_or_else(|| vec![0; 32], |address| address.0.0.to_vec()));
    env.insert(destination.to_owned(), value);
    Ok(read_event(
        read,
        address.is_some(),
        env,
        vec![destination.to_owned()],
    ))
}

fn read_event(
    read: &Read,
    active: bool,
    env: &Environment,
    produced: Vec<String>,
) -> PreparationRead {
    let mut declared = BTreeSet::from([read.name.clone()]);
    declared.extend(
        read.components
            .iter()
            .map(|component| component.name.clone()),
    );
    declared.extend(
        read.projections
            .iter()
            .flatten()
            .map(|projection| projection.name.clone()),
    );
    for component in &read.components {
        match component.ty.as_str() {
            "Bytes<32>" => declared
                .extend((0..2).map(|index| format!("_noctium_bytes_{}_{}", component.name, index))),
            "JubjubPoint" => declared.extend(
                (0..2).map(|index| format!("_noctium_jubjub_read_{}_{}", component.name, index)),
            ),
            _ => {}
        }
    }
    let values = produced
        .into_iter()
        .filter(|name| declared.contains(name))
        .filter_map(|name| env.get(&name).cloned().map(|value| (name, value)))
        .collect();
    PreparationRead {
        name: read.name.clone(),
        active,
        values,
    }
}

fn bind_context_scalar(
    read: Option<&Read>,
    guard: Option<&Expr>,
    destination: &str,
    active: bool,
    value: Value,
    env: &mut Environment,
) -> Result<PreparationRead> {
    let read = read.ok_or_else(|| anyhow!("missing context scalar read"))?;
    ensure!(
        read.name == destination
            && ScalarType::parse(&read.ty)? == value.scalar_type()
            && read.guard.as_ref() == guard
            && read.components.is_empty()
            && read.projections.is_none()
            && read.schema.is_none()
            && !env.contains_key(destination),
        "context scalar read schema mismatch"
    );
    env.insert(destination.to_owned(), value);
    Ok(read_event(read, active, env, vec![destination.to_owned()]))
}

fn balance_amount(value: u128) -> Value {
    Value::UInt {
        number: value.into(),
        maximum: u128::MAX.into(),
    }
}

fn token_type(color: HashOutput, is_unshielded: bool) -> TokenType {
    if is_unshielded {
        TokenType::Unshielded(UnshieldedTokenType(color))
    } else {
        TokenType::Shielded(ShieldedTokenType(color))
    }
}

fn balance_limit(expression: &Expr, env: &Environment) -> Result<u128> {
    let Value::UInt { number, maximum } = evaluate(expression, env)? else {
        bail!("token balance comparison limit must be UInt128");
    };
    ensure!(
        maximum == u128::MAX.into(),
        "token balance comparison limit must be UInt128"
    );
    Ok(number.try_into()?)
}

fn push_amount(value: u128) -> Result<Op<ResultModeVerify, Db>> {
    push_native_state(StateValue::Cell(Sp::new(value.into())), false)
}

fn append_balance_read(
    program: &mut Program,
    token: TokenType,
    comparison: Option<(bool, u128)>,
) -> Result<()> {
    let token: AlignedValue = token.into();
    let key = Key::Value(
        token
            .clone()
            .try_into()
            .map_err(|_| anyhow!("invalid balance token key"))?,
    );
    let reverse = comparison.is_some_and(|(less, _)| !less);
    if let Some((false, limit)) = comparison {
        program.push(push_amount(limit)?);
    }
    program.extend([
        Op::Dup {
            n: if reverse { 3 } else { 2 },
        },
        list_index(5),
        Op::Dup { n: 0 },
        push_native_state(StateValue::Cell(Sp::new(token)), false)?,
        Op::Member,
        Op::Branch { skip: 3 },
        Op::Pop,
        push_amount(0)?,
        Op::Jmp { skip: 1 },
        Op::Idx {
            cached: false,
            push_path: false,
            path: vec![key].try_into()?,
        },
    ]);
    if let Some((less, limit)) = comparison {
        if less {
            program.push(push_amount(limit)?);
        }
        program.push(Op::Lt);
    }
    Ok(())
}
fn validate_guarded_shape(operation: &Instruction) -> Result<()> {
    ensure!(
        matches!(
            operation,
            Instruction::Dup
                | Instruction::Checkpoint
                | Instruction::Index {
                    push_path: false,
                    ..
                }
                | Instruction::Push { storage: false, .. }
                | Instruction::Popeq { .. }
                | Instruction::Member
                | Instruction::Index {
                    push_path: true,
                    ..
                }
                | Instruction::Push { .. }
                | Instruction::Insert { .. }
                | Instruction::IndexPath { .. }
                | Instruction::New
                | Instruction::PushFields { .. }
                | Instruction::PopeqFields { .. }
                | Instruction::AddImmediate { .. }
                | Instruction::SubImmediate { .. }
                | Instruction::ListLength { .. }
                | Instruction::MapSize { .. }
                | Instruction::MapIsEmpty { .. }
                | Instruction::ListHead { .. }
                | Instruction::ListPushFront { .. }
                | Instruction::ListPopFront { .. }
                | Instruction::ListReset { .. }
                | Instruction::MapRemove { .. }
                | Instruction::MerkleTreeIsFull { .. }
                | Instruction::MerkleTreeCheckRoot { .. }
                | Instruction::MerkleTreeInsertHash { .. }
                | Instruction::MerkleTreeInsertHashIndex { .. }
                | Instruction::MerkleTreeReset { .. }
                | Instruction::MerkleTreeResetHistory { .. }
                | Instruction::ClaimContractCall { .. }
                | Instruction::MintShielded { .. }
                | Instruction::MintUnshielded { .. }
                | Instruction::IncUnshieldedOutputs { .. }
                | Instruction::IncUnshieldedInputs { .. }
                | Instruction::ClaimUnshieldedCoinSpend { .. }
                | Instruction::RequireContractCaller { .. }
                | Instruction::ReadCaller { .. }
                | Instruction::ReadContractAddress { .. }
                | Instruction::ReadTokenBalance { .. }
                | Instruction::EmitEvent { .. }
                | Instruction::BlockTimeCompare { .. }
                | Instruction::CounterLessThan { .. }
        ),
        "guarded native operation has an unsupported shape"
    );
    Ok(())
}

impl PreparationCursor {
    pub fn new(
        plan: &Plan,
        inputs: &BTreeMap<String, Json>,
        state: &ChargedState<Db>,
        params: &LedgerParameters,
        address: ContractAddress,
    ) -> Result<Self> {
        Self::from_context(
            plan,
            inputs,
            QueryContext::new(state.clone(), address),
            params,
            false,
        )
    }

    pub(crate) fn from_context(
        plan: &Plan,
        inputs: &BTreeMap<String, Json>,
        context: QueryContext<Db>,
        params: &LedgerParameters,
        has_block_time: bool,
    ) -> Result<Self> {
        let env = parse_input_environment(plan, inputs, true)?;
        let supplied_inputs = inputs.keys().cloned().collect();
        let prefix_context = context.clone();
        let mut cursor = Self {
            plan: plan.clone(),
            deferred_outputs: BTreeMap::new(),
            env,
            supplied_inputs,
            context,
            has_block_time,
            params: params.clone(),
            prefix_context,
            materialized_prefix: 0,
            mutation_boundary: 0,
            program: Vec::new(),
            read_index: 0,
            previous_index: None,
            member_result_pending: false,
            has_written: false,
            activity_schedule: Vec::with_capacity(plan.operations.len()),
            next_operation: 0,
            poisoned: false,
            completed: false,
        };
        cursor.deferred_outputs = refresh_circuit_outputs(&cursor.plan, &mut cursor.env)?;
        Ok(cursor)
    }

    pub fn supply_inputs(&mut self, inputs: &BTreeMap<String, Json>) -> Result<()> {
        ensure!(!self.poisoned, "preparation cursor is poisoned");
        ensure!(!self.completed, "preparation cursor is complete");
        let mut additions = Vec::with_capacity(inputs.len());
        for (name, json) in inputs {
            let input = self
                .plan
                .circuit
                .inputs
                .iter()
                .find(|input| input.name == *name)
                .ok_or_else(|| anyhow!("input schema mismatch (missing or unknown input)"))?;
            ensure!(
                !self.supplied_inputs.contains(name) && !self.env.contains_key(name),
                "input '{}' was already supplied",
                name
            );
            ensure!(
                input.visibility == "private",
                "public inputs are required initially"
            );
            additions.push((
                name.clone(),
                input_value(&input.ty, json)
                    .with_context(|| format!("invalid input '{}'", input.name))?,
            ));
        }

        let mut next_env = self.env.clone();
        let mut next_supplied = self.supplied_inputs.clone();
        for (name, value) in additions {
            next_env.insert(name.clone(), value);
            next_supplied.insert(name);
        }
        let next_deferred = refresh_circuit_outputs(&self.plan, &mut next_env)?;
        self.env = next_env;
        self.supplied_inputs = next_supplied;
        self.deferred_outputs = next_deferred;
        Ok(())
    }

    pub fn step(&mut self) -> Result<PreparationStep> {
        ensure!(!self.poisoned, "preparation cursor is poisoned");
        if self.completed {
            return Ok(PreparationStep::Complete);
        }
        let result = self.step_inner();
        if result.is_err() {
            self.poisoned = true;
        }
        result
    }

    fn step_inner(&mut self) -> Result<PreparationStep> {
        if self.next_operation == self.plan.operations.len() {
            let missing = self
                .plan
                .circuit
                .inputs
                .iter()
                .filter(|input| !self.supplied_inputs.contains(&input.name))
                .cloned()
                .collect::<Vec<_>>();
            if !missing.is_empty() {
                return Ok(PreparationStep::PendingInputs(missing));
            }
            ensure!(
                self.deferred_outputs.is_empty(),
                "circuit outputs are incomplete"
            );
            validate_return_environment(&self.plan, &self.env)?;
            ensure!(
                self.read_index == self.plan.reads.len(),
                "read schema mismatch"
            );
            ensure!(
                self.activity_schedule
                    .iter()
                    .filter(|entry| entry.is_none())
                    .count()
                    == self.program.len(),
                "native activity schedule does not match emitted operations"
            );
            self.completed = true;
            return Ok(PreparationStep::Complete);
        }

        // Complete-input callers need no speculative operand evaluation.
        if self.supplied_inputs.len() == self.plan.circuit.inputs.len() {
            return self.execute_next();
        }

        let instruction = &self.plan.operations[self.next_operation];
        let operation = if let Instruction::Guarded { guard, operation } = instruction {
            validate_guarded_shape(operation)?;
            if let Some(input) =
                probe_expression(guard, &self.plan, &self.env, &self.deferred_outputs)?
            {
                return Ok(PreparationStep::PendingInputs(vec![input]));
            }
            if !evaluate(guard, &self.env)?.boolean()? {
                None
            } else {
                Some(operation.as_ref())
            }
        } else {
            Some(instruction)
        };
        if let Some(operation) = operation {
            if let Some(input) = probe_instruction(
                operation,
                &self.plan,
                &self.env,
                &self.deferred_outputs,
                self.previous_index.as_ref(),
            )? {
                return Ok(PreparationStep::PendingInputs(vec![input]));
            }
        }
        self.execute_next()
    }
}

fn validate_return_environment(plan: &Plan, env: &Environment) -> Result<()> {
    validate_return_views_specs(
        &plan.return_views,
        plan.returns.iter().map(|output| {
            (
                output.name.as_str(),
                output.ty.as_str(),
                output.visibility.as_str(),
            )
        }),
    )?;
    let mut names = BTreeSet::new();
    let mut return_values = Vec::with_capacity(plan.returns.len());
    for output in &plan.returns {
        ensure!(
            output.visibility == "public"
                && !output.name.is_empty()
                && names.insert(output.name.as_str()),
            "invalid call return declaration"
        );
        let ty = ScalarType::parse(&output.ty)?;
        let value = evaluate(&output.expression, env)?;
        ensure!(value.scalar_type() == ty, "call return type mismatch");
        value.validate()?;
        return_values.push((output.name.clone(), value));
    }
    reconstruct_return_views(&plan.return_views, &return_values)?;
    Ok(())
}

pub fn prepare(
    plan: &Plan,
    inputs: &BTreeMap<String, Json>,
    state: &ChargedState<Db>,
    params: &LedgerParameters,
    address: ContractAddress,
) -> Result<Execution> {
    finish_preparation(PreparationCursor::from_context(
        plan,
        inputs,
        QueryContext::new(state.clone(), address),
        params,
        false,
    )?)
}

/// Prepare a call using its prospective ledger query context. Composition assembly
/// checks the supplied contract parent against the call forest before returning an intent.
pub fn prepare_with_context(
    plan: &Plan,
    inputs: &BTreeMap<String, Json>,
    context: QueryContext<Db>,
    params: &LedgerParameters,
) -> Result<Execution> {
    prepare_with_context_and_block_time(plan, inputs, context, params, true)
}

pub(crate) fn prepare_with_context_and_block_time(
    plan: &Plan,
    inputs: &BTreeMap<String, Json>,
    context: QueryContext<Db>,
    params: &LedgerParameters,
    has_block_time: bool,
) -> Result<Execution> {
    finish_preparation(PreparationCursor::from_context(
        plan,
        inputs,
        context,
        params,
        has_block_time,
    )?)
}

fn finish_preparation(mut cursor: PreparationCursor) -> Result<Execution> {
    loop {
        match cursor.step()? {
            PreparationStep::PendingInputs(missing) => bail!(
                "complete preparation is missing circuit inputs: {}",
                missing
                    .iter()
                    .map(|input| input.name.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            PreparationStep::Operation { .. } => {}
            PreparationStep::Complete => break,
        }
    }
    cursor.finish()
}

impl PreparationCursor {
    fn execute_next(&mut self) -> Result<PreparationStep> {
        let PreparationCursor {
            plan,
            env,
            context,
            has_block_time,
            params,
            prefix_context,
            materialized_prefix: stored_materialized_prefix,
            mutation_boundary: stored_mutation_boundary,
            program,
            read_index: stored_read_index,
            previous_index: stored_previous_index,
            member_result_pending: stored_member_result_pending,
            has_written: stored_has_written,
            activity_schedule,
            next_operation: stored_next_operation,
            ..
        } = self;
        let index = *stored_next_operation;
        let i = &plan.operations[index];
        let cost = &params.cost_model.runtime_cost_model;
        let mut materialized_prefix = *stored_materialized_prefix;
        let mut mutation_boundary = *stored_mutation_boundary;
        let mut read_index = *stored_read_index;
        let mut previous_index = stored_previous_index.take();
        let mut member_result_pending = *stored_member_result_pending;
        let mut has_written = *stored_has_written;
        let mut event = None;
        let operation_start = program.len();
        let mut instruction_guard = None;
        let instruction = match i {
            Instruction::Guarded { guard, operation } => {
                validate_guarded_shape(operation)?;
                let active = evaluate(guard, &env)?.boolean()?;
                if !active {
                    activity_schedule.extend(
                        impact_field_counts(operation.as_ref(), plan)?
                            .into_iter()
                            .map(Some),
                    );
                    if matches!(
                        operation.as_ref(),
                        Instruction::RequireContractCaller { .. }
                    ) {
                        consume_contract_caller_reads(plan, &mut read_index, Some(guard))?;
                    }
                    if let Instruction::ReadCaller {
                        present,
                        is_contract,
                        contract_address,
                        user_address,
                    } = operation.as_ref()
                    {
                        event = Some(bind_caller_reads(
                            plan,
                            &mut read_index,
                            Some(guard),
                            [present, is_contract, contract_address, user_address],
                            false,
                            None,
                            env,
                        )?);
                    }
                    if let Instruction::ReadContractAddress { destination } = operation.as_ref() {
                        event = Some(bind_contract_address(
                            plan.reads.get(read_index),
                            Some(guard),
                            destination,
                            None,
                            env,
                        )?);
                        read_index += 1;
                    }
                    if let Instruction::ReadTokenBalance {
                        destination,
                        comparison,
                        ..
                    } = operation.as_ref()
                    {
                        let result = if comparison.is_some() {
                            Value::Bool(false)
                        } else {
                            balance_amount(0)
                        };
                        event = Some(bind_context_scalar(
                            plan.reads.get(read_index),
                            Some(guard),
                            destination,
                            false,
                            result,
                            env,
                        )?);
                        read_index += 1;
                    }
                    if let Instruction::BlockTimeCompare { destination, .. }
                    | Instruction::CounterLessThan { destination, .. } = operation.as_ref()
                    {
                        event = Some(bind_context_scalar(
                            plan.reads.get(read_index),
                            Some(guard),
                            destination,
                            false,
                            Value::Bool(false),
                            env,
                        )?);
                        read_index += 1;
                    }
                    if let Instruction::Popeq {
                        expression,
                        alignment,
                    } = operation.as_ref()
                    {
                        let read = plan
                            .reads
                            .get(read_index)
                            .ok_or_else(|| anyhow!("missing read schema for inactive read"))?;
                        ensure!(
                            read.guard.as_ref() == Some(guard),
                            "inactive read guard differs from the source read schema"
                        );
                        let read_reference = match expression {
                            Expr::Reference { name } => Some(name),
                            Expr::Cast { ty, value } if ty == "Native" => match value.as_ref() {
                                Expr::Reference { name } => Some(name),
                                _ => None,
                            },
                            _ => None,
                        };
                        ensure!(
                            read_reference == Some(&read.name),
                            "inactive read result differs from the source read schema"
                        );
                        let read_type = ScalarType::parse(&read.ty)?;
                        if let Some(length) = byte_alignment_length(alignment)? {
                            ensure!(
                                read_type.bytes_length() == Some(length),
                                "inactive byte read alignment mismatch"
                            );
                            validate_byte_read_projections(read, &read_type)?;
                        } else if alignment == "compress" {
                            ensure!(
                                read_type == ScalarType::OpaqueBytes,
                                "inactive opaque byte read alignment mismatch"
                            );
                        } else {
                            ensure!(
                                matches!(alignment.as_str(), "field" | "bit" | "u64"),
                                "unsupported inactive read alignment"
                            );
                        }
                        read_index += 1;
                        env.insert(read.name.clone(), inactive_read_value(&read.ty)?);
                        event = Some(read_event(read, false, env, vec![read.name.clone()]));
                    }
                    if let Instruction::PopeqFields {
                        expressions,
                        schema,
                    } = operation.as_ref()
                    {
                        let read = plan
                            .reads
                            .get(read_index)
                            .ok_or_else(|| anyhow!("missing inactive record read schema"))?;
                        ensure!(
                            read.guard.as_ref() == Some(guard),
                            "inactive record read guard mismatch"
                        );
                        if let Some(name) = typed_scalar_schema_token(schema) {
                            let ty = ScalarType::parse(name)?;
                            ensure!(
                                read.ty == name
                                    && read.schema.is_none()
                                    && read.components.is_empty()
                                    && expressions.len() == typed_scalar_field_count(&ty)?,
                                "inactive typed read schema mismatch"
                            );
                            ensure!(
                                !env.contains_key(&read.name),
                                "typed read shadows an existing value"
                            );
                            let value = inactive_read_value(&read.ty)?;
                            let encoded = typed_scalar_fields(&value)?;
                            env.insert(read.name.clone(), value);
                            let projected = expressions
                                .iter()
                                .map(|expression| evaluate(expression, &env)?.field())
                                .collect::<Result<Vec<_>>>()?;
                            ensure!(
                                projected == encoded,
                                "inactive typed read projections mismatch"
                            );
                            event = Some(read_event(read, false, env, vec![read.name.clone()]));
                        } else {
                            record_component_names(read, expressions, schema)?;
                            let checked = checked_record_schema(schema)?;
                            let defaults = checked
                                .fields
                                .iter()
                                .map(|field| inactive_read_value(record_type_name(&field.ty)?))
                                .collect::<Result<Vec<_>>>()?;
                            let produced = bind_record_values(read, &checked, &defaults, env)?;
                            event = Some(read_event(read, false, env, produced));
                        }
                        read_index += 1;
                    }
                    if let Instruction::MapIsEmpty { destination, .. } = operation.as_ref() {
                        let read = plan
                            .reads
                            .get(read_index)
                            .ok_or_else(|| anyhow!("missing inactive map emptiness read"))?;
                        ensure!(
                            read.name == destination.as_str()
                                && read.ty == "Bool"
                                && read.guard.as_ref() == Some(guard)
                                && read.components.is_empty()
                                && read.projections.is_none()
                                && read.schema.is_none()
                                && !env.contains_key(destination),
                            "inactive map emptiness read schema mismatch"
                        );
                        env.insert(destination.clone(), Value::Bool(false));
                        event = Some(read_event(read, false, env, vec![destination.clone()]));
                        read_index += 1;
                    }
                    match operation.as_ref() {
                        Instruction::ListLength { expression, .. }
                        | Instruction::MapSize { expression, .. } => {
                            let read = plan
                                .reads
                                .get(read_index)
                                .ok_or_else(|| anyhow!("missing inactive cardinality read"))?;
                            ensure!(
                                read.guard.as_ref() == Some(guard)
                                    && read.ty == "UIntRange<18446744073709551616>",
                                "inactive cardinality read schema mismatch"
                            );
                            ensure!(
                                matches!(expression, Expr::Reference { name } if name == &read.name),
                                "List length must bind its declared read"
                            );
                            ensure!(
                                !env.contains_key(&read.name),
                                "cardinality shadows an existing value"
                            );
                            env.insert(read.name.clone(), inactive_read_value(&read.ty)?);
                            event = Some(read_event(read, false, env, vec![read.name.clone()]));
                            read_index += 1;
                        }
                        Instruction::ListHead {
                            slot,
                            keys,
                            schema,
                            expressions,
                            ..
                        } => {
                            let read = plan
                                .reads
                                .get(read_index)
                                .ok_or_else(|| anyhow!("missing inactive List head read"))?;
                            ensure!(
                                read.guard.as_ref() == Some(guard),
                                "inactive List head guard mismatch"
                            );
                            if let Some(ty) = list_operation_scalar_type(plan, *slot, keys, schema)?
                            {
                                ensure!(
                                    expressions.len() == 1,
                                    "scalar List head requires one expression"
                                );
                                let ty_name = schema
                                    .as_str()
                                    .ok_or_else(|| anyhow!("invalid scalar List schema"))?;
                                let value = inactive_read_value(ty_name)?;
                                ensure!(
                                    value.scalar_type() == ty,
                                    "inactive scalar List default type mismatch"
                                );
                                event = Some(bind_list_scalar_read(
                                    read,
                                    &expressions[0],
                                    ty_name,
                                    Some(guard),
                                    false,
                                    value,
                                    env,
                                )?);
                            } else {
                                record_component_names(read, expressions, schema)?;
                                let checked = checked_record_schema(schema)?;
                                let defaults = checked
                                    .fields
                                    .iter()
                                    .map(|field| inactive_read_value(record_type_name(&field.ty)?))
                                    .collect::<Result<Vec<_>>>()?;
                                let produced = bind_record_values(read, &checked, &defaults, env)?;
                                event = Some(read_event(read, false, env, produced));
                            }
                            read_index += 1;
                        }
                        Instruction::MerkleTreeIsFull { destination, .. }
                        | Instruction::MerkleTreeCheckRoot { destination, .. } => {
                            event = Some(bind_context_scalar(
                                plan.reads.get(read_index),
                                Some(guard),
                                destination,
                                false,
                                Value::Bool(false),
                                env,
                            )?);
                            read_index += 1;
                        }
                        _ => {}
                    }
                    *stored_next_operation += 1;
                    *stored_read_index = read_index;
                    *stored_materialized_prefix = materialized_prefix;
                    *stored_mutation_boundary = mutation_boundary;
                    *stored_member_result_pending = member_result_pending;
                    *stored_has_written = has_written;
                    *stored_previous_index = previous_index;
                    return Ok(PreparationStep::Operation { index, read: event });
                }
                instruction_guard = Some(guard);
                operation.as_ref()
            }
            _ => i,
        };
        if has_written
            && matches!(
                instruction,
                Instruction::ListLength { .. }
                    | Instruction::MapSize { .. }
                    | Instruction::MapIsEmpty { .. }
                    | Instruction::ListHead { .. }
                    | Instruction::ListPushFront { .. }
                    | Instruction::ListPopFront { .. }
                    | Instruction::ListReset { .. }
                    | Instruction::MerkleTreeIsFull { .. }
                    | Instruction::MerkleTreeCheckRoot { .. }
                    | Instruction::MerkleTreeInsertHash { .. }
                    | Instruction::MerkleTreeInsertHashIndex { .. }
                    | Instruction::MerkleTreeResetHistory { .. }
            )
        {
            advance_native_state_prefix(
                prefix_context,
                &program,
                &mut materialized_prefix,
                mutation_boundary,
                cost,
            )?;
        }
        let mut current_index = None;
        let op = match instruction {
            Instruction::Guarded { .. } => {
                bail!("nested guarded native operation is unsupported")
            }
            Instruction::Dup => Op::Dup { n: 0 },
            Instruction::Checkpoint => Op::Ckpt,
            Instruction::Index {
                slot,
                push_path,
                key,
            } => {
                let map_key = key
                    .as_ref()
                    .map(|key| {
                        let key_type = map_key_type(plan, *slot)?;
                        let value = evaluate(key, &env)?;
                        validate_ledger_key_value(&key_type, &value)?;
                        aligned(&value, key_alignment(&key_type))
                    })
                    .transpose()?;
                let mut path = vec![Key::Value(
                    field_value(Fr::from(*slot as u64))
                        .try_into()
                        .map_err(|_| anyhow!("invalid native index key"))?,
                )];
                if let Some(key) = map_key.as_ref() {
                    path.push(Key::Value(
                        key.clone()
                            .try_into()
                            .map_err(|_| anyhow!("invalid native map key"))?,
                    ));
                }
                current_index = Some((*slot, map_key.into_iter().collect::<Vec<_>>()));
                Op::Idx {
                    cached: false,
                    push_path: *push_path,
                    path: path.into_iter().collect(),
                }
            }
            Instruction::IndexPath {
                slot,
                push_path,
                keys,
            } => {
                let (op, values) = native_index(plan, *slot, keys, *push_path, &env)?;
                current_index = Some((*slot, values));
                op
            }
            Instruction::New => Op::New,
            Instruction::Push {
                storage,
                expression,
                alignment,
            } => {
                let value = evaluate(expression, &env)?;
                if *storage && matches!(&value, Value::OpaqueBytes(_)) {
                    let (slot, depth) = opaque_byte_storage_path(plan, index, instruction_guard)?;
                    validate_scalar_storage_type(
                        plan,
                        slot,
                        depth,
                        &ScalarType::OpaqueBytes,
                    )?;
                }
                #[cfg(feature = "zkir-321")]
                ensure!(
                    !matches!(&value, Value::Foreign(_)),
                    "foreign pushes require a typed field schema"
                );
                Op::Push {
                    storage: *storage,
                    value: StateValue::Cell(Sp::new(aligned(&value, alignment)?))
                        .try_into_checked()
                        .map_err(|_| anyhow!("invalid native pushed value"))?,
                }
            }
            Instruction::PushFields {
                storage,
                expressions,
                schema,
            } => {
                if let Some(name) = typed_scalar_schema_token(schema) {
                    let ty = ScalarType::parse(name)?;
                    ensure!(
                        expressions.len() == typed_scalar_field_count(&ty)?,
                        "typed storage field count mismatch"
                    );
                    let value = {
                        #[cfg(feature = "zkir-321")]
                        if !*storage && matches!(&ty, ScalarType::Foreign(_)) {
                            let value = evaluate(foreign_key_projection(expressions, &ty)?, &env)?;
                            validate_ledger_key_value(&ty, &value)?;
                            value
                        } else {
                            let fields = expressions
                                .iter()
                                .map(|expression| evaluate(expression, &env)?.field())
                                .collect::<Result<Vec<_>>>()?;
                            decode_typed_scalar(&ty, &fields)?
                        }
                        #[cfg(not(feature = "zkir-321"))]
                        {
                            let fields = expressions
                                .iter()
                                .map(|expression| evaluate(expression, &env)?.field())
                                .collect::<Result<Vec<_>>>()?;
                            decode_typed_scalar(&ty, &fields)?
                        }
                    };
                    Op::Push {
                        storage: *storage,
                        value: StateValue::Cell(Sp::new(aligned_storage_cell(&value)?))
                            .try_into_checked()
                            .map_err(|_| anyhow!("invalid typed storage value"))?,
                    }
                } else {
                    let schema = checked_record_schema(schema)?;
                    let fields = record_values_from_expressions(&schema, expressions, &env)?;
                    Op::Push {
                        storage: *storage,
                        value: StateValue::Cell(Sp::new(aligned_record_value(&schema, &fields)?))
                            .try_into_checked()
                            .map_err(|_| anyhow!("invalid record value"))?,
                    }
                }
            }
            Instruction::Popeq {
                expression,
                alignment,
            } => {
                let read = plan
                    .reads
                    .get(read_index)
                    .ok_or_else(|| anyhow!("missing read schema"))?;
                ensure!(
                    read.guard.as_ref() == instruction_guard,
                    "active read guard differs from the source read schema"
                );
                read_index += 1;
                let read_reference = match expression {
                    Expr::Reference { name } => Some(name),
                    Expr::Cast { ty, value } if ty == "Native" => match value.as_ref() {
                        Expr::Reference { name } => Some(name),
                        _ => None,
                    },
                    _ => None,
                };
                let mut produced = Vec::new();
                if let Some(name) = read_reference {
                    if !env.contains_key(name) {
                        let member_read = member_result_pending
                            && read.ty == "Bool"
                            && alignment == "bit"
                            && name == &read.name;
                        if has_written {
                            advance_native_state_prefix(
                                prefix_context,
                                &program,
                                &mut materialized_prefix,
                                mutation_boundary,
                                cost,
                            )?;
                        }
                        let read_context = if has_written {
                            &prefix_context
                        } else {
                            &context
                        };
                        let value = if member_read {
                            Value::Bool(native_member_result(
                                read_context,
                                &program[materialized_prefix..],
                                cost,
                            )?)
                        } else {
                            let (slot, keys) = previous_index
                                .as_ref()
                                .ok_or_else(|| anyhow!("unsupported state-read shape"))?;
                            if alignment == "u64" {
                                ensure!(
                                    tree_schema_at_path(plan, *slot, keys.len())?.get("counter")
                                        == Some(&Json::Bool(true)),
                                    "counter read path schema mismatch"
                                );
                            }
                            let read_type = ScalarType::parse(&read.ty)?;
                            if read_type.bytes_length().is_some() {
                                validate_byte_read_projections(read, &read_type)?;
                            }
                            if is_typed_scalar(&read_type)
                                || read_type.bytes_length().is_some()
                                || read_type == ScalarType::OpaqueBytes
                            {
                                validate_scalar_storage_type(plan, *slot, keys.len(), &read_type)?;
                            }
                            read_state_cell(read_context, *slot, keys, &read.ty, alignment)?
                        };
                        env.insert(name.clone(), value);
                        produced.push(name.clone());
                    }
                }
                let value = evaluate(expression, &env)?;
                #[cfg(feature = "zkir-321")]
                ensure!(
                    !matches!(&value, Value::Foreign(_)),
                    "foreign comparisons require a typed field schema"
                );
                if !env.contains_key(&read.name) {
                    env.insert(read.name.clone(), value.clone());
                    produced.push(read.name.clone());
                }
                event = Some(read_event(read, true, env, produced));
                Op::Popeq {
                    cached: false,
                    result: aligned(&value, alignment)?,
                }
            }
            Instruction::PopeqFields {
                expressions,
                schema,
            } => {
                let read = plan
                    .reads
                    .get(read_index)
                    .ok_or_else(|| anyhow!("missing record read schema"))?;
                ensure!(
                    read.guard.as_ref() == instruction_guard,
                    "active record read guard mismatch"
                );
                if let Some(name) = typed_scalar_schema_token(schema) {
                    let ty = ScalarType::parse(name)?;
                    ensure!(
                        read.ty == name && read.schema.is_none() && read.components.is_empty(),
                        "typed read schema mismatch"
                    );
                    ensure!(
                        expressions.len() == typed_scalar_field_count(&ty)?,
                        "typed read field count mismatch"
                    );
                    let (slot, keys) = previous_index
                        .as_ref()
                        .ok_or_else(|| anyhow!("typed read lacks a state index"))?;
                    validate_scalar_storage_type(plan, *slot, keys.len(), &ty)?;
                    if has_written {
                        advance_native_state_prefix(
                            prefix_context,
                            &program,
                            &mut materialized_prefix,
                            mutation_boundary,
                            cost,
                        )?;
                    }
                    let read_context = if has_written {
                        &prefix_context
                    } else {
                        &context
                    };
                    let value = read_state_aligned(read_context, *slot, keys)?;
                    let decoded = decode_state_cell(&value, &read.ty, "field")?;
                    let fields = typed_scalar_fields(&decoded)?;
                    ensure!(
                        !env.contains_key(&read.name),
                        "typed read shadows an existing value"
                    );
                    env.insert(read.name.clone(), decoded);
                    let produced = vec![read.name.clone()];
                    let projected = expressions
                        .iter()
                        .map(|expression| evaluate(expression, &env)?.field())
                        .collect::<Result<Vec<_>>>()?;
                    ensure!(projected == fields, "typed read projections mismatch");
                    event = Some(read_event(read, true, env, produced));
                    read_index += 1;
                    Op::Popeq {
                        cached: false,
                        result: value,
                    }
                } else {
                    record_component_names(read, expressions, schema)?;
                    let (slot, keys) = previous_index
                        .as_ref()
                        .ok_or_else(|| anyhow!("record read lacks a native index"))?;
                    ensure!(
                        record_schema_at_path(plan, *slot, keys.len())? == schema,
                        "record read differs from state schema"
                    );
                    if has_written {
                        advance_native_state_prefix(
                            prefix_context,
                            &program,
                            &mut materialized_prefix,
                            mutation_boundary,
                            cost,
                        )?;
                    }
                    let read_context = if has_written {
                        &prefix_context
                    } else {
                        &context
                    };
                    let value = read_state_aligned(read_context, *slot, keys)?;
                    let checked = checked_record_schema(schema)?;
                    let values = decode_record_value(&checked, &value)?;
                    let produced = bind_record_values(read, &checked, &values, env)?;
                    event = Some(read_event(read, true, env, produced));
                    read_index += 1;
                    Op::Popeq {
                        cached: false,
                        result: value,
                    }
                }
            }
            Instruction::ListLength {
                slot,
                keys,
                expression,
            } => {
                let schema = list_element_schema_at_path(plan, *slot, keys.len())?;
                let (index, values) = native_index(plan, *slot, keys, false, &env)?;
                let read = plan
                    .reads
                    .get(read_index)
                    .ok_or_else(|| anyhow!("missing List length read"))?;
                ensure!(
                    read.guard.as_ref() == instruction_guard
                        && read.ty == "UIntRange<18446744073709551616>",
                    "List length read schema mismatch"
                );
                ensure!(
                    matches!(expression, Expr::Reference { name } if name == &read.name),
                    "List length must bind its declared read"
                );
                let (length, _) = native_list_value(
                    if has_written {
                        &prefix_context
                    } else {
                        &context
                    },
                    *slot,
                    &values,
                    schema,
                )?;
                ensure!(
                    !env.contains_key(&read.name),
                    "List length shadows an existing value"
                );
                env.insert(
                    read.name.clone(),
                    Value::UInt {
                        number: length.into(),
                        maximum: u64::MAX.into(),
                    },
                );
                event = Some(read_event(read, true, env, vec![read.name.clone()]));
                read_index += 1;
                program.extend([Op::Dup { n: 0 }, index, list_index(2)]);
                Op::Popeq {
                    cached: false,
                    result: length.into(),
                }
            }
            Instruction::MapSize {
                slot,
                keys,
                expression,
            } => {
                validate_map_size_path(plan, *slot, keys.len())?;
                let (index, values) = native_index(plan, *slot, keys, false, &env)?;
                let read = plan
                    .reads
                    .get(read_index)
                    .ok_or_else(|| anyhow!("missing map size read"))?;
                ensure!(
                    read.guard.as_ref() == instruction_guard
                        && read.ty == "UIntRange<18446744073709551616>",
                    "map size read schema mismatch"
                );
                ensure!(
                    matches!(expression, Expr::Reference { name } if name == &read.name),
                    "map size must bind its declared read"
                );
                let read_context = if has_written {
                    &prefix_context
                } else {
                    &context
                };
                let StateValue::Map(ref map) = read_state_value(read_context, *slot, &values)?
                else {
                    bail!("size path does not address a map")
                };
                let size = u64::try_from(map.size())?;
                ensure!(
                    !env.contains_key(&read.name),
                    "map size shadows an existing value"
                );
                env.insert(
                    read.name.clone(),
                    Value::UInt {
                        number: size.into(),
                        maximum: u64::MAX.into(),
                    },
                );
                event = Some(read_event(read, true, env, vec![read.name.clone()]));
                read_index += 1;
                program.extend([Op::Dup { n: 0 }, index, Op::Size]);
                Op::Popeq {
                    cached: false,
                    result: size.into(),
                }
            }
            Instruction::MapIsEmpty {
                slot,
                keys,
                destination,
            } => {
                validate_map_size_path(plan, *slot, keys.len())?;
                let (index, values) = native_index(plan, *slot, keys, false, &env)?;
                let read_context = if has_written {
                    &prefix_context
                } else {
                    &context
                };
                let StateValue::Map(ref map) = read_state_value(read_context, *slot, &values)?
                else {
                    bail!("isEmpty path does not address a map")
                };
                let result = map.is_empty();
                let read = plan
                    .reads
                    .get(read_index)
                    .ok_or_else(|| anyhow!("missing map emptiness read"))?;
                ensure!(
                    read.name == destination.as_str()
                        && read.ty == "Bool"
                        && read.guard.as_ref() == instruction_guard
                        && read.components.is_empty()
                        && read.projections.is_none()
                        && read.schema.is_none()
                        && !env.contains_key(destination),
                    "map emptiness read schema mismatch"
                );
                env.insert(destination.clone(), Value::Bool(result));
                event = Some(read_event(read, true, env, vec![destination.clone()]));
                read_index += 1;
                program.extend([
                    Op::Dup { n: 0 },
                    index,
                    Op::Size,
                    push_native_state(StateValue::Cell(Sp::new(AlignedValue::from(0u64))), false)?,
                    Op::Eq,
                ]);
                Op::Popeq {
                    cached: true,
                    result: result.into(),
                }
            }
            Instruction::MerkleTreeIsFull {
                slot,
                keys,
                depth,
                destination,
            } => {
                let historic = ensure_merkle_tree_depth(plan, *slot, keys, *depth)?;
                let (index, values) = native_index(plan, *slot, keys, false, &env)?;
                let tree_state = read_state_value(
                    if has_written {
                        &prefix_context
                    } else {
                        &context
                    },
                    *slot,
                    &values,
                )?;
                let (_, count, _) = merkle_tree_parts(&tree_state, *depth, historic)?;
                let capacity = 1u64 << depth;
                let result = count == capacity;
                event = Some(bind_context_scalar(
                    plan.reads.get(read_index),
                    instruction_guard,
                    destination,
                    true,
                    Value::Bool(result),
                    env,
                )?);
                read_index += 1;
                program.extend([
                    Op::Dup { n: 0 },
                    index,
                    list_index(1),
                    push_native_state(StateValue::Cell(Sp::new(capacity.into())), false)?,
                    Op::Lt,
                    Op::Neg,
                ]);
                Op::Popeq {
                    cached: true,
                    result: result.into(),
                }
            }
            Instruction::MerkleTreeCheckRoot {
                slot,
                keys,
                depth,
                expected,
                destination,
            } => {
                let historic = ensure_merkle_tree_depth(plan, *slot, keys, *depth)?;
                let (index, values) = native_index(plan, *slot, keys, false, &env)?;
                let read_context = if has_written {
                    &prefix_context
                } else {
                    &context
                };
                let tree_state = read_state_value(read_context, *slot, &values)?;
                let (tree, _, history) = merkle_tree_parts(&tree_state, *depth, historic)?;
                let expected_root = evaluate(expected, &env)?.field()?;
                let expected_key = field_value(expected_root);
                let result = if let Some(history) = history {
                    if let Some(entry) = history.get(&expected_key) {
                        ensure!(
                            matches!(*entry, StateValue::Null),
                            "historic MerkleTree root value must be Null"
                        );
                        true
                    } else {
                        false
                    }
                } else {
                    tree.root()
                        .context("MerkleTree state has an unrehashed root")?
                        .0
                        == expected_root
                };
                event = Some(bind_context_scalar(
                    plan.reads.get(read_index),
                    instruction_guard,
                    destination,
                    true,
                    Value::Bool(result),
                    env,
                )?);
                read_index += 1;
                program.extend([
                    Op::Dup { n: 0 },
                    index,
                    merkle_tree_index(if historic { 2 } else { 0 }, false),
                ]);
                if !historic {
                    program.push(Op::Root);
                }
                program.extend([
                    push_native_state(StateValue::Cell(Sp::new(expected_key)), false)?,
                    if historic { Op::Member } else { Op::Eq },
                ]);
                Op::Popeq {
                    cached: true,
                    result: result.into(),
                }
            }
            Instruction::MerkleTreeInsertHash {
                slot,
                keys,
                depth,
                hash,
            } => {
                let historic = ensure_merkle_tree_depth(plan, *slot, keys, *depth)?;
                let (root_index, values) = native_index(plan, *slot, keys, true, &env)?;
                let tree_state = read_state_value(
                    if has_written {
                        &prefix_context
                    } else {
                        &context
                    },
                    *slot,
                    &values,
                )?;
                let (_, count, _) = merkle_tree_parts(&tree_state, *depth, historic)?;
                let capacity = 1u64 << depth;
                ensure!(count < capacity, "MerkleTree is full");
                let hash = evaluate(hash, &env)?;
                let Value::Bytes(bytes) = &hash else {
                    bail!("MerkleTree inserted hash must be Bytes32")
                };
                ensure!(
                    bytes.len() == 32,
                    "MerkleTree inserted hash must be Bytes32"
                );
                let aligned_hash = aligned_bytes(&hash)?;
                program.extend([
                    root_index,
                    merkle_tree_index(0, true),
                    Op::Dup { n: 2 },
                    merkle_tree_index(1, false),
                    push_native_state(StateValue::Cell(Sp::new(aligned_hash)), true)?,
                    Op::Ins {
                        cached: false,
                        n: 1,
                    },
                    Op::Ins { cached: true, n: 1 },
                    merkle_tree_index(1, true),
                    Op::Addi { immediate: 1 },
                ]);
                if historic {
                    program.push(Op::Ins { cached: true, n: 1 });
                    append_historic_merkle_root(program)?;
                }
                has_written = true;
                Op::Ins {
                    cached: true,
                    n: (keys.len() + 2).try_into()?,
                }
            }
            Instruction::MerkleTreeInsertHashIndex {
                slot,
                keys,
                depth,
                hash,
                index,
            } => {
                let historic = ensure_merkle_tree_depth(plan, *slot, keys, *depth)?;
                let (root_index, values) = native_index(plan, *slot, keys, true, &env)?;
                let read_context = if has_written {
                    &prefix_context
                } else {
                    &context
                };
                let tree_state = read_state_value(read_context, *slot, &values)?;
                merkle_tree_parts(&tree_state, *depth, historic)?;
                let capacity = 1u64 << depth;

                let index_value = evaluate(index, &env)?;
                let Value::UInt { number, maximum } = &index_value else {
                    bail!("MerkleTree insertion index must be UInt64")
                };
                ensure!(
                    *maximum == u64::MAX.into(),
                    "MerkleTree insertion index must be UInt64"
                );
                let index_value_u64: u64 = number.clone().try_into()?;
                ensure!(
                    index_value_u64 < capacity,
                    "MerkleTree insertion index exceeds its capacity"
                );
                let index_value = aligned(&index_value, "u64")?;

                let hash = evaluate(hash, &env)?;
                let Value::Bytes(ref bytes) = hash else {
                    bail!("MerkleTree inserted hash must be Bytes32")
                };
                ensure!(
                    bytes.len() == 32,
                    "MerkleTree inserted hash must be Bytes32"
                );
                let aligned_hash = aligned_bytes(&hash)?;
                program.extend([
                    root_index,
                    merkle_tree_index(0, true),
                    push_native_state(StateValue::Cell(Sp::new(index_value.clone())), false)?,
                    push_native_state(StateValue::Cell(Sp::new(aligned_hash)), true)?,
                    Op::Ins {
                        cached: false,
                        n: 2,
                    },
                    merkle_tree_index(1, true),
                    push_native_state(StateValue::Cell(Sp::new(index_value)), false)?,
                    Op::Addi { immediate: 1 },
                    Op::Dup { n: 1 },
                    Op::Dup { n: 1 },
                    Op::Lt,
                    Op::Branch { skip: 2 },
                    Op::Pop,
                    Op::Jmp { skip: 2 },
                    Op::Swap { n: 0 },
                    Op::Pop,
                    Op::Ins {
                        cached: false,
                        n: 1,
                    },
                ]);
                if historic {
                    append_historic_merkle_root(program)?;
                }
                has_written = true;
                Op::Ins {
                    cached: true,
                    n: (keys.len() + 1 + usize::from(historic)).try_into()?,
                }
            }
            Instruction::ListHead {
                slot,
                keys,
                schema,
                expressions,
            } => {
                let scalar_type = list_operation_scalar_type(plan, *slot, keys, schema)?;
                let (index, values) = native_index(plan, *slot, keys, false, &env)?;
                let read = plan
                    .reads
                    .get(read_index)
                    .ok_or_else(|| anyhow!("missing List head read"))?;
                ensure!(
                    read.guard.as_ref() == instruction_guard,
                    "List head guard mismatch"
                );
                let (_, head) = native_list_value(
                    if has_written {
                        &prefix_context
                    } else {
                        &context
                    },
                    *slot,
                    &values,
                    list_element_schema_at_path(plan, *slot, keys.len())?,
                )?;
                let head = head.ok_or_else(|| anyhow!("head of empty List"))?;
                if let Some(ty) = scalar_type {
                    ensure!(
                        expressions.len() == 1,
                        "scalar List head requires one expression"
                    );
                    let ty_name = schema
                        .as_str()
                        .ok_or_else(|| anyhow!("invalid scalar List schema"))?;
                    let value =
                        decode_state_cell(&head, ty_name, &list_scalar_storage_alignment(&ty))?;
                    event = Some(bind_list_scalar_read(
                        read,
                        &expressions[0],
                        ty_name,
                        instruction_guard,
                        true,
                        value,
                        env,
                    )?);
                } else {
                    record_component_names(read, expressions, schema)?;
                    let checked = checked_record_schema(schema)?;
                    let values = decode_record_value(&checked, &head)?;
                    let produced = bind_record_values(read, &checked, &values, env)?;
                    event = Some(read_event(read, true, env, produced));
                }
                read_index += 1;
                program.extend([Op::Dup { n: 0 }, index, list_index(0)]);
                Op::Popeq {
                    cached: false,
                    result: head,
                }
            }
            Instruction::ListPushFront {
                slot,
                keys,
                schema,
                expressions,
            } => {
                let scalar_type = list_operation_scalar_type(plan, *slot, keys, schema)?;
                let (index, values) = native_index(plan, *slot, keys, true, &env)?;
                native_list_value(
                    if has_written {
                        &prefix_context
                    } else {
                        &context
                    },
                    *slot,
                    &values,
                    list_element_schema_at_path(plan, *slot, keys.len())?,
                )?;
                let aligned_head = if let Some(ty) = scalar_type {
                    ensure!(
                        expressions.len() == 1,
                        "scalar List push requires one expression"
                    );
                    let value = evaluate(&expressions[0], &env)?;
                    ensure!(
                        value.scalar_type() == ty,
                        "scalar List push expression type mismatch"
                    );
                    value.validate()?;
                    aligned_storage_cell(&value)?
                } else {
                    let checked = checked_record_schema(schema)?;
                    let fields = record_values_from_expressions(&checked, expressions, &env)?;
                    aligned_record_value(&checked, &fields)?
                };
                let node = StateValue::Array(
                    vec![
                        StateValue::Cell(Sp::new(aligned_head)),
                        StateValue::Null,
                        StateValue::Null,
                    ]
                    .into(),
                );
                program.extend([
                    index,
                    Op::Dup { n: 0 },
                    list_index(2),
                    Op::Addi { immediate: 1 },
                    push_native_state(node, true)?,
                    Op::Swap { n: 0 },
                    push_native_state(StateValue::Cell(Sp::new(2u8.into())), false)?,
                    Op::Swap { n: 0 },
                    Op::Ins {
                        cached: false,
                        n: 1,
                    },
                    Op::Swap { n: 0 },
                    push_native_state(StateValue::Cell(Sp::new(1u8.into())), false)?,
                    Op::Swap { n: 0 },
                ]);
                has_written = true;
                Op::Ins {
                    cached: false,
                    n: (keys.len() + 2).try_into()?,
                }
            }
            Instruction::ListPopFront { slot, keys } => {
                let schema = list_element_schema_at_path(plan, *slot, keys.len())?;
                let (index, values) = native_index(plan, *slot, keys, true, &env)?;
                let (length, _) = native_list_value(
                    if has_written {
                        &prefix_context
                    } else {
                        &context
                    },
                    *slot,
                    &values,
                    schema,
                )?;
                ensure!(length > 0, "pop of empty List");
                // Subi enforces nonempty in the ledger VM as well as host preparation.
                program.extend([
                    index,
                    Op::Dup { n: 0 },
                    list_index(2),
                    Op::Subi { immediate: 1 },
                    Op::Pop,
                    list_index(1),
                ]);
                has_written = true;
                Op::Ins {
                    cached: false,
                    n: (keys.len() + 1).try_into()?,
                }
            }
            Instruction::MapRemove { slot, keys } => {
                let (_, parents) = keys
                    .split_last()
                    .ok_or_else(|| anyhow!("map removal requires a key"))?;
                let (_, values) = native_index(plan, *slot, keys, false, &env)?;
                let (index, _) = native_index(plan, *slot, parents, true, &env)?;
                program.extend([
                    index,
                    push_native_state(
                        StateValue::Cell(Sp::new(values.last().expect("nonempty path").clone())),
                        false,
                    )?,
                    Op::Rem { cached: false },
                ]);
                has_written = true;
                Op::Ins {
                    cached: false,
                    n: keys.len().try_into()?,
                }
            }
            Instruction::ListReset { slot, keys } => {
                list_element_schema_at_path(plan, *slot, keys.len())?;
                let (_, values) = native_index(plan, *slot, keys, false, &env)?;
                if let Some((_, parents)) = keys.split_last() {
                    let (index, _) = native_index(plan, *slot, parents, true, &env)?;
                    program.push(index);
                    program.push(push_native_state(
                        StateValue::Cell(Sp::new(values.last().expect("nonempty path").clone())),
                        false,
                    )?);
                } else {
                    program.push(push_native_state(
                        StateValue::Cell(Sp::new(field_value(Fr::from(*slot as u64)))),
                        false,
                    )?);
                }
                program.push(push_native_state(empty_native_list(), true)?);
                has_written = true;
                Op::Ins {
                    cached: false,
                    n: (keys.len() + 1).try_into()?,
                }
            }
            Instruction::MerkleTreeReset {
                slot,
                keys,
                depth,
                empty_history,
            } => {
                let historic =
                    ensure_merkle_tree_reset_mode(plan, *slot, keys, *depth, *empty_history)?;
                let key = if let Some((_, parents)) = keys.split_last() {
                    let (_, mut values) = native_index(plan, *slot, keys, false, &env)?;
                    let (parent, _) = native_index(plan, *slot, parents, true, &env)?;
                    program.push(parent);
                    values.pop().expect("nonempty MerkleTree path")
                } else {
                    field_value(Fr::from(*slot as u64))
                };
                program.extend([
                    push_native_state(StateValue::Cell(Sp::new(key)), false)?,
                    push_native_state(
                        merkle_tree_default_state(*depth, historic, *empty_history),
                        true,
                    )?,
                ]);
                has_written = true;
                Op::Ins {
                    cached: false,
                    n: (keys.len() + 1).try_into()?,
                }
            }
            Instruction::MerkleTreeResetHistory { slot, keys, depth } => {
                ensure!(
                    ensure_merkle_tree_depth(plan, *slot, keys, *depth)?,
                    "resetHistory requires a historic MerkleTree"
                );
                let (root_index, values) = native_index(plan, *slot, keys, true, &env)?;
                let read_context = if has_written {
                    &prefix_context
                } else {
                    &context
                };
                let tree_state = read_state_value(read_context, *slot, &values)?;
                merkle_tree_parts(&tree_state, *depth, true)?;
                program.extend([
                    root_index,
                    push_native_state(StateValue::Cell(Sp::new(AlignedValue::from(2u8))), false)?,
                    push_native_state(StateValue::Map(Default::default()), true)?,
                    Op::Dup { n: 2 },
                    merkle_tree_index(0, false),
                    Op::Root,
                    push_native_state(StateValue::Null, true)?,
                ]);
                has_written = true;
                Op::Ins {
                    cached: true,
                    n: (keys.len() + 3).try_into()?,
                }
            }
            Instruction::ClaimContractCall {
                address,
                entry_point_hash,
                commitment,
            } => {
                let address = claim_hash_output(evaluate(address, &env)?, "contract address")?;
                let entry_point_hash =
                    claim_hash_output(evaluate(entry_point_hash, &env)?, "entrypoint hash")?;
                let commitment = evaluate(commitment, &env)?.field()?;
                let claim_ops = onchain_runtime::program_fragments::kernel_claim_contract_call!(
                    (),
                    (),
                    AlignedValue::from(address),
                    AlignedValue::from(entry_point_hash),
                    field_value(commitment)
                );
                program.extend(claim_ops[..8].iter().cloned());
                claim_ops[8].clone()
            }
            Instruction::MintShielded { domain, amount } => {
                let domain = claim_hash_output(evaluate(domain, &env)?, "shielded mint domain")?;
                let amount = mint_amount(amount, &env)?;
                append_token_accumulation(program, 4, domain.into(), amount.into())?
            }
            Instruction::MintUnshielded { domain, amount } => {
                let domain = claim_hash_output(evaluate(domain, &env)?, "unshielded mint domain")?;
                let amount = mint_amount(amount, &env)?;
                append_token_accumulation(program, 5, domain.into(), amount.into())?
            }
            Instruction::IncUnshieldedOutputs {
                color,
                amount,
                is_unshielded,
            } => {
                let color = claim_hash_output(evaluate(color, &env)?, "unshielded output color")?;
                let amount = unshielded_amount(amount, &env)?;
                let is_unshielded = evaluate(is_unshielded, &env)?.boolean()?;
                append_token_accumulation(
                    program,
                    7,
                    token_type(color, is_unshielded).into(),
                    amount.into(),
                )?
            }
            Instruction::IncUnshieldedInputs {
                color,
                amount,
                is_unshielded,
            } => {
                let color = claim_hash_output(evaluate(color, &env)?, "unshielded input color")?;
                let amount = unshielded_amount(amount, &env)?;
                let is_unshielded = evaluate(is_unshielded, &env)?.boolean()?;
                append_token_accumulation(
                    program,
                    6,
                    token_type(color, is_unshielded).into(),
                    amount.into(),
                )?
            }
            Instruction::ClaimUnshieldedCoinSpend {
                color,
                amount,
                is_unshielded,
                is_contract,
                recipient,
            } => {
                let color = claim_hash_output(evaluate(color, &env)?, "unshielded spend color")?;
                let amount = unshielded_amount(amount, &env)?;
                let is_unshielded = evaluate(is_unshielded, &env)?.boolean()?;
                let is_contract = evaluate(is_contract, &env)?.boolean()?;
                let recipient =
                    claim_hash_output(evaluate(recipient, &env)?, "unshielded recipient")?;
                append_unshielded_spend_claim(
                    program,
                    token_type(color, is_unshielded),
                    amount,
                    is_contract,
                    recipient,
                )?
            }
            Instruction::ReceiveShieldedToMap {
                slot,
                nonce,
                color,
                amount,
                commitment,
            } => {
                validate_shielded_coin_map(plan, *slot)?;
                let coin = ShieldedCoinInfo {
                    nonce: Nonce(claim_hash_output(
                        evaluate(nonce, &env)?,
                        "shielded coin nonce",
                    )?),
                    type_: ShieldedTokenType(claim_hash_output(
                        evaluate(color, &env)?,
                        "shielded coin color",
                    )?),
                    value: unshielded_amount(amount, &env)?,
                };
                let recipient = Recipient::Contract(context.address);
                let source_commitment =
                    claim_hash_output(evaluate(commitment, &env)?, "shielded receive commitment")?;
                let coin_commitment = coin.commitment(&recipient);
                ensure!(
                    coin_commitment.0 == source_commitment,
                    "shielded receive commitment mismatch"
                );
                context
                    .qualify(&coin)
                    .ok_or_else(|| anyhow!("shielded receive commitment is absent from context"))?;

                if has_written {
                    advance_native_state_prefix(
                        prefix_context,
                        &program,
                        &mut materialized_prefix,
                        mutation_boundary,
                        cost,
                    )?;
                }
                let read_context = if has_written {
                    &prefix_context
                } else {
                    &context
                };
                let coin_state = read_state_value(read_context, *slot, &[])?;
                let StateValue::Map(coins) = &coin_state else {
                    bail!("shielded receive state is not a Map")
                };
                let key = AlignedValue::from(coin.nonce);
                ensure!(
                    coins.get(&key).is_none(),
                    "shielded receive nonce already exists"
                );

                let path = vec![Key::Value(
                    AlignedValue::from(u8::try_from(*slot)?)
                        .try_into()
                        .map_err(|_| anyhow!("invalid shielded receive Map slot"))?,
                )];
                let mut map_ops = onchain_runtime::program_fragments::Map_insert_coin!(
                    path,
                    false,
                    AlignedValue,
                    ShieldedCoinInfo,
                    key,
                    coin,
                    recipient
                );
                map_ops[2] = Op::Dup { n: 5 };
                let insert_final = map_ops[9].clone();
                program.extend(
                    onchain_runtime::program_fragments::kernel_claim_zswap_coin_receive!(
                        (),
                        (),
                        coin_commitment
                    ),
                );
                program.extend(map_ops.into_iter().take(9));
                has_written = true;
                insert_final
            }
            Instruction::WriteShieldedCoinCell {
                slot,
                nonce,
                color,
                amount,
                commitment,
            } => {
                validate_shielded_coin_cell(plan, *slot)?;
                let coin = ShieldedCoinInfo {
                    nonce: Nonce(claim_hash_output(
                        evaluate(nonce, &env)?,
                        "shielded coin nonce",
                    )?),
                    type_: ShieldedTokenType(claim_hash_output(
                        evaluate(color, &env)?,
                        "shielded coin color",
                    )?),
                    value: unshielded_amount(amount, &env)?,
                };
                let recipient = Recipient::Contract(context.address);
                let expected_commitment =
                    claim_hash_output(evaluate(commitment, &env)?, "shielded coin commitment")?;
                ensure!(
                    coin.commitment(&recipient).0 == expected_commitment,
                    "shielded coin Cell commitment mismatch"
                );
                context.qualify(&coin).ok_or_else(|| {
                    anyhow!("shielded coin Cell commitment is absent from the current transaction")
                })?;

                if has_written {
                    advance_native_state_prefix(
                        prefix_context,
                        &program,
                        &mut materialized_prefix,
                        mutation_boundary,
                        cost,
                    )?;
                }
                let current = if has_written {
                    &prefix_context
                } else {
                    &context
                };
                ensure!(
                    matches!(read_state_value(current, *slot, &[])?, StateValue::Cell(_)),
                    "shielded coin destination is not a Cell"
                );
                let path = vec![Key::Value(
                    AlignedValue::from(u8::try_from(*slot)?)
                        .try_into()
                        .map_err(|_| anyhow!("invalid shielded coin Cell slot"))?,
                )];
                let [
                    _,
                    slot_push,
                    duplicate,
                    commitment_push,
                    lookup,
                    coin_push,
                    swap,
                    concatenate,
                    insert,
                    _,
                ] = onchain_runtime::program_fragments::Cell_write_coin!(
                    path,
                    false,
                    QualifiedInfo,
                    coin,
                    recipient
                );
                program.extend([
                    slot_push,
                    duplicate,
                    commitment_push,
                    lookup,
                    coin_push,
                    swap,
                    concatenate,
                ]);
                has_written = true;
                insert
            }
            Instruction::InsertShieldedCoinSet {
                slot,
                nonce,
                color,
                amount,
                commitment,
            } => {
                validate_shielded_coin_set(plan, *slot)?;
                let coin = ShieldedCoinInfo {
                    nonce: Nonce(claim_hash_output(
                        evaluate(nonce, &env)?,
                        "shielded Set coin nonce",
                    )?),
                    type_: ShieldedTokenType(claim_hash_output(
                        evaluate(color, &env)?,
                        "shielded Set coin color",
                    )?),
                    value: unshielded_amount(amount, &env)?,
                };
                let recipient = Recipient::Contract(context.address);
                let expected_commitment = claim_hash_output(
                    evaluate(commitment, &env)?,
                    "shielded Set coin commitment",
                )?;
                let coin_commitment = coin.commitment(&recipient);
                ensure!(
                    coin_commitment.0 == expected_commitment,
                    "shielded coin Set commitment mismatch"
                );
                let qualified = context.qualify(&coin).ok_or_else(|| {
                    anyhow!(
                        "shielded coin Set commitment is absent from the current transaction"
                    )
                })?;
                let qualified_key = AlignedValue::from(qualified);
                ensure!(
                    qualified_key.alignment.fits(&qualified_key.value),
                    "shielded coin Set record alignment mismatch"
                );

                if has_written {
                    advance_native_state_prefix(
                        prefix_context,
                        &program,
                        &mut materialized_prefix,
                        mutation_boundary,
                        cost,
                    )?;
                }
                let current = if has_written {
                    &prefix_context
                } else {
                    &context
                };
                let set_state = read_state_value(current, *slot, &[])?;
                let StateValue::Map(members) = &set_state else {
                    bail!("shielded coin Set state is not a Map")
                };
                if let Some(marker) = members.get(&qualified_key) {
                    ensure!(
                        matches!(*marker, StateValue::Null),
                        "shielded coin Set member marker is invalid"
                    );
                }

                let path = vec![Key::Value(
                    AlignedValue::from(u8::try_from(*slot)?)
                        .try_into()
                        .map_err(|_| anyhow!("invalid shielded coin Set slot"))?,
                )];
                let set_ops = onchain_runtime::program_fragments::Set_insert_coin!(
                    path,
                    false,
                    QualifiedInfo,
                    coin,
                    recipient
                );
                program.extend([
                    set_ops[0].clone(),
                    set_ops[1].clone(),
                    set_ops[2].clone(),
                    set_ops[3].clone(),
                    set_ops[5].clone(),
                    set_ops[6].clone(),
                    set_ops[4].clone(),
                    set_ops[7].clone(),
                    set_ops[8].clone(),
                ]);
                has_written = true;
                set_ops[9].clone()
            }
            Instruction::SpendShieldedFromMap {
                nonce,
                color,
                amount,
                recipient,
                nullifier,
                output_commitment,
            } => {
                let (_, read_key) =
                    validate_shielded_spend_layout(plan, index, nonce, color, amount)?;
                let coin = ShieldedCoinInfo {
                    nonce: Nonce(claim_hash_output(
                        evaluate(nonce, &env)?,
                        "shielded spend coin nonce",
                    )?),
                    type_: ShieldedTokenType(claim_hash_output(
                        evaluate(color, &env)?,
                        "shielded spend coin color",
                    )?),
                    value: unshielded_amount(amount, &env)?,
                };
                let key = claim_hash_output(
                    evaluate(&read_key.expression, &env)?,
                    "shielded spend Map key",
                )?;
                ensure!(
                    coin.nonce.0 == key,
                    "shielded spend coin nonce differs from its Map key"
                );

                let coin_nullifier = coin.nullifier(&SenderEvidence::Contract(context.address));
                let source_nullifier =
                    claim_hash_output(evaluate(nullifier, &env)?, "shielded spend nullifier")?;
                ensure!(
                    coin_nullifier.0 == source_nullifier,
                    "shielded spend nullifier mismatch"
                );

                let recipient =
                    claim_hash_output(evaluate(recipient, &env)?, "shielded spend recipient")?;
                let output_coin =
                    coin.evolve_from(b"midnight:kernel:nonce_evolve", coin.value, coin.type_);
                let coin_commitment =
                    output_coin.commitment(&Recipient::User(PublicKey(recipient)));
                let source_commitment = claim_hash_output(
                    evaluate(output_commitment, &env)?,
                    "shielded spend output commitment",
                )?;
                ensure!(
                    coin_commitment.0 == source_commitment,
                    "shielded spend output commitment mismatch"
                );

                let nullifier_ops = onchain_runtime::program_fragments::kernel_claim_zswap_nullifier!(
                    (),
                    (),
                    coin_nullifier
                );
                let spend_ops = onchain_runtime::program_fragments::kernel_claim_zswap_coin_spend!(
                    (),
                    (),
                    coin_commitment
                );
                program.extend(nullifier_ops);
                program.extend(spend_ops[..5].iter().cloned());
                spend_ops[5].clone()
            }
            Instruction::SendShieldedFromMap {
                nonce,
                color,
                input_amount,
                send_amount,
                recipient,
                nullifier,
                output_commitment,
                change_commitment,
            } => {
                let (_, read_key, receive_index) = validate_shielded_send_layout(
                    plan,
                    index,
                    nonce,
                    color,
                    input_amount,
                    change_commitment,
                )?;
                let coin = ShieldedCoinInfo {
                    nonce: Nonce(claim_hash_output(
                        evaluate(nonce, &env)?,
                        "shielded send coin nonce",
                    )?),
                    type_: ShieldedTokenType(claim_hash_output(
                        evaluate(color, &env)?,
                        "shielded send coin color",
                    )?),
                    value: unshielded_amount(input_amount, &env)?,
                };
                let key = claim_hash_output(
                    evaluate(&read_key.expression, &env)?,
                    "shielded send Map key",
                )?;
                ensure!(
                    coin.nonce.0 == key,
                    "shielded send coin nonce differs from its Map key"
                );
                let send_amount = unshielded_amount(send_amount, &env)?;
                ensure!(
                    send_amount > 0 && send_amount < coin.value,
                    "shielded send amount must leave positive contract change"
                );

                let coin_nullifier = coin.nullifier(&SenderEvidence::Contract(context.address));
                let source_nullifier =
                    claim_hash_output(evaluate(nullifier, &env)?, "shielded send nullifier")?;
                ensure!(
                    coin_nullifier.0 == source_nullifier,
                    "shielded send nullifier mismatch"
                );

                let recipient =
                    claim_hash_output(evaluate(recipient, &env)?, "shielded send recipient")?;
                let send_coin =
                    coin.evolve_from(b"midnight:kernel:nonce_evolve", send_amount, coin.type_);
                let send_commitment = send_coin.commitment(&Recipient::User(PublicKey(recipient)));
                let source_commitment = claim_hash_output(
                    evaluate(output_commitment, &env)?,
                    "shielded send output commitment",
                )?;
                ensure!(
                    send_commitment.0 == source_commitment,
                    "shielded send output commitment mismatch"
                );

                let change_amount = coin.value - send_amount;
                let change_coin =
                    coin.evolve_from(b"midnight:kernel:nonce_evolve/2", change_amount, coin.type_);
                let source_change_commitment = claim_hash_output(
                    evaluate(change_commitment, &env)?,
                    "shielded change output commitment",
                )?;
                let change_commitment =
                    change_coin.commitment(&Recipient::Contract(context.address));
                ensure!(
                    change_commitment.0 == source_change_commitment,
                    "shielded change output commitment mismatch"
                );

                let receive = plan
                    .operations
                    .get(receive_index)
                    .ok_or_else(|| anyhow!("shielded send change receive is missing"))?;
                let (receive, receive_guard) = unguarded_operation(receive);
                ensure!(
                    receive_guard.is_none(),
                    "shielded change receive must be unguarded"
                );
                let Instruction::ReceiveShieldedToMap {
                    nonce,
                    color,
                    amount,
                    commitment,
                    ..
                } = receive
                else {
                    bail!("shielded send change receive is missing")
                };
                ensure!(
                    claim_hash_output(evaluate(nonce, &env)?, "shielded change nonce")?
                        == change_coin.nonce.0
                        && claim_hash_output(evaluate(color, &env)?, "shielded change color")?
                            == change_coin.type_.0
                        && unshielded_amount(amount, &env)? == change_amount
                        && claim_hash_output(
                            evaluate(commitment, &env)?,
                            "shielded change receive commitment",
                        )? == source_change_commitment,
                    "shielded change receive differs from the derived change coin"
                );

                let nullifier_ops = onchain_runtime::program_fragments::kernel_claim_zswap_nullifier!(
                    (),
                    (),
                    coin_nullifier
                );
                let send_ops = onchain_runtime::program_fragments::kernel_claim_zswap_coin_spend!(
                    (),
                    (),
                    send_commitment
                );
                let change_ops = onchain_runtime::program_fragments::kernel_claim_zswap_coin_spend!(
                    (),
                    (),
                    change_commitment
                );
                program.extend(nullifier_ops);
                program.extend(send_ops);
                program.extend(change_ops[..5].iter().cloned());
                change_ops[5].clone()
            }
            Instruction::RelayShieldedImmediate {
                nonce,
                color,
                amount,
                recipient,
                input_commitment,
                nullifier,
                output_commitment,
            } => {
                let coin = ShieldedCoinInfo {
                    nonce: Nonce(claim_hash_output(
                        evaluate(nonce, &env)?,
                        "immediate relay coin nonce",
                    )?),
                    type_: ShieldedTokenType(claim_hash_output(
                        evaluate(color, &env)?,
                        "immediate relay coin color",
                    )?),
                    value: unshielded_amount(amount, &env)?,
                };
                ensure!(
                    coin.value > 0,
                    "immediate shielded relay amount must be positive"
                );

                let source_commitment = claim_hash_output(
                    evaluate(input_commitment, &env)?,
                    "immediate relay input commitment",
                )?;
                let coin_commitment = coin.commitment(&Recipient::Contract(context.address));
                ensure!(
                    coin_commitment.0 == source_commitment,
                    "immediate relay input commitment mismatch"
                );
                let qualified_coin = context
                    .qualify(&coin)
                    .ok_or_else(|| anyhow!("immediate relay transient is absent from context"))?;
                ensure!(
                    context.call_context.com_indices.get(&coin_commitment)
                        == Some(&qualified_coin.mt_index),
                    "immediate relay transient index mismatch"
                );

                let coin_nullifier = coin.nullifier(&SenderEvidence::Contract(context.address));
                let source_nullifier =
                    claim_hash_output(evaluate(nullifier, &env)?, "immediate relay nullifier")?;
                ensure!(
                    coin_nullifier.0 == source_nullifier,
                    "immediate relay nullifier mismatch"
                );

                let target = ContractAddress(claim_hash_output(
                    evaluate(recipient, &env)?,
                    "immediate relay recipient contract",
                )?);
                let output_coin = coin.evolve_from(
                    b"midnight:kernel:nonce_evolve",
                    coin.value,
                    coin.type_,
                );
                let destination = output_coin.commitment(&Recipient::Contract(target));
                let source_output_commitment = claim_hash_output(
                    evaluate(output_commitment, &env)?,
                    "immediate relay output commitment",
                )?;
                ensure!(
                    destination.0 == source_output_commitment,
                    "immediate relay output commitment mismatch"
                );
                ensure!(
                    context.call_context.com_indices.contains_key(&destination),
                    "immediate relay output commitment is absent from context"
                );

                let receive_ops =
                    onchain_runtime::program_fragments::kernel_claim_zswap_coin_receive!(
                        (),
                        (),
                        coin_commitment
                    );
                let nullifier_ops =
                    onchain_runtime::program_fragments::kernel_claim_zswap_nullifier!(
                        (),
                        (),
                        coin_nullifier
                    );
                let spend_ops =
                    onchain_runtime::program_fragments::kernel_claim_zswap_coin_spend!(
                        (),
                        (),
                        destination
                    );
                program.extend(receive_ops);
                program.extend(nullifier_ops);
                program.extend(spend_ops[..5].iter().cloned());
                spend_ops[5].clone()
            }
            Instruction::ReadTokenBalance {
                destination,
                color,
                is_unshielded,
                comparison,
            } => {
                let color = claim_hash_output(evaluate(color, &env)?, "balance token color")?;
                let token = token_type(color, evaluate(is_unshielded, &env)?.boolean()?);
                let amount = context
                    .call_context
                    .balance
                    .get(&token)
                    .map(|value| *value)
                    .unwrap_or(0);
                let (comparison, result, expected) = match comparison {
                    None => (None, balance_amount(amount), AlignedValue::from(amount)),
                    Some(comparison) => {
                        let limit = balance_limit(comparison.limit(), &env)?;
                        ensure!(
                            amount <= u128::from(u64::MAX) && limit <= u128::from(u64::MAX),
                            "native balance comparisons require UInt64 operands"
                        );
                        let less = matches!(comparison, BalanceComparison::LessThan(_));
                        let answer = if less { amount < limit } else { amount > limit };
                        (Some((less, limit)), Value::Bool(answer), answer.into())
                    }
                };
                append_balance_read(program, token, comparison)?;
                event = Some(bind_context_scalar(
                    plan.reads.get(read_index),
                    instruction_guard,
                    destination,
                    true,
                    result,
                    env,
                )?);
                read_index += 1;
                Op::Popeq {
                    cached: false,
                    result: expected,
                }
            }
            Instruction::RequireContractCaller { address } => {
                consume_contract_caller_reads(plan, &mut read_index, instruction_guard)?;
                let expected = PublicAddress::Contract(ContractAddress(claim_hash_output(
                    evaluate(address, &env)?,
                    "contract caller",
                )?));
                ensure!(
                    context.call_context.caller == Some(expected),
                    "required contract caller mismatch"
                );
                program.extend([Op::Dup { n: 2 }, list_index(6)]);
                Op::Popeq {
                    cached: false,
                    result: AlignedValue::from(expected),
                }
            }
            Instruction::ReadCaller {
                present,
                is_contract,
                contract_address,
                user_address,
            } => {
                let caller = context.call_context.caller;
                event = Some(bind_caller_reads(
                    plan,
                    &mut read_index,
                    instruction_guard,
                    [present, is_contract, contract_address, user_address],
                    true,
                    caller,
                    env,
                )?);
                append_caller_read(program, caller)?
            }
            Instruction::ReadContractAddress { destination } => {
                let address = context.address;
                event = Some(bind_contract_address(
                    plan.reads.get(read_index),
                    instruction_guard,
                    destination,
                    Some(address),
                    env,
                )?);
                read_index += 1;
                program.extend([Op::Dup { n: 2 }, list_index(0)]);
                Op::Popeq {
                    cached: false,
                    result: AlignedValue::from(address),
                }
            }
            Instruction::EmitEvent { tag, payload } => {
                let bytes = evaluated_bytes(payload, event_payload_length(*tag)?, &env)?;
                let value = StateValue::Array(
                    vec![
                        StateValue::Cell(Sp::new(1u32.into())),
                        StateValue::Cell(Sp::new((*tag).into())),
                        StateValue::Cell(Sp::new(aligned_bytes(&Value::Bytes(bytes))?)),
                    ]
                    .into(),
                );
                program.push(push_native_state(value, false)?);
                Op::Log
            }
            Instruction::BlockTimeCompare {
                destination,
                before,
                deadline,
            } => {
                ensure!(
                    *has_block_time,
                    "active time comparison requires explicit block context"
                );
                let Value::UInt { number, maximum } = evaluate(deadline, &env)? else {
                    bail!("block-time comparison requires a UInt64 deadline")
                };
                ensure!(
                    maximum == u64::MAX.into(),
                    "block-time deadline must be UInt64"
                );
                let seconds: u64 = number.try_into()?;
                let current = context.call_context.tblock.to_secs();
                let threshold =
                    push_native_state(StateValue::Cell(Sp::new(seconds.into())), false)?;
                let result = if *before {
                    program.extend([Op::Dup { n: 2 }, list_index(2), threshold]);
                    current < seconds
                } else {
                    program.extend([threshold, Op::Dup { n: 3 }, list_index(2)]);
                    seconds < current
                };
                program.push(Op::Lt);
                event = Some(bind_context_scalar(
                    plan.reads.get(read_index),
                    instruction_guard,
                    destination,
                    true,
                    Value::Bool(result),
                    env,
                )?);
                read_index += 1;
                Op::Popeq {
                    cached: false,
                    result: result.into(),
                }
            }
            Instruction::CounterLessThan {
                slot,
                keys,
                threshold,
                destination,
            } => {
                counter_path_field_count(plan, *slot, keys)?;
                let (index, values) = native_index(plan, *slot, keys, false, &env)?;
                let Value::UInt {
                    number: threshold_number,
                    maximum: threshold_maximum,
                } = evaluate(threshold, &env)?
                else {
                    bail!("counter comparison threshold must be UInt64")
                };
                ensure!(
                    threshold_maximum == u64::MAX.into(),
                    "counter comparison threshold must be UInt64"
                );
                let threshold_number = u64::try_from(threshold_number)
                    .map_err(|_| anyhow!("counter comparison threshold exceeds u64"))?;

                if has_written {
                    advance_native_state_prefix(
                        prefix_context,
                        &program,
                        &mut materialized_prefix,
                        mutation_boundary,
                        cost,
                    )?;
                }
                let read_context = if has_written {
                    &prefix_context
                } else {
                    &context
                };
                let Value::UInt {
                    number: counter_number,
                    ..
                } = read_state_cell(
                    read_context,
                    *slot,
                    &values,
                    "UIntRange<18446744073709551616>",
                    "u64",
                )?
                else {
                    bail!("counter comparison requires a UInt64 Counter")
                };
                let counter_number = u64::try_from(counter_number)
                    .map_err(|_| anyhow!("counter value exceeds u64"))?;
                let result = counter_number < threshold_number;
                program.extend([
                    Op::Dup { n: 0 },
                    index,
                    push_native_state(StateValue::Cell(Sp::new(threshold_number.into())), false)?,
                    Op::Lt,
                ]);
                event = Some(bind_context_scalar(
                    plan.reads.get(read_index),
                    instruction_guard,
                    destination,
                    true,
                    Value::Bool(result),
                    env,
                )?);
                read_index += 1;
                Op::Popeq {
                    cached: false,
                    result: result.into(),
                }
            }
            Instruction::Member => Op::Member,
            Instruction::AddImmediate { amount } | Instruction::SubImmediate { amount } => {
                let (slot, keys) = validate_counter_adjustment_path(plan, previous_index.as_ref())?;
                let amount = evaluate_immediate_amount(amount, &env)?;
                if has_written {
                    advance_native_state_prefix(
                        prefix_context,
                        &program,
                        &mut materialized_prefix,
                        mutation_boundary,
                        cost,
                    )?;
                }
                let read_context = if has_written {
                    &prefix_context
                } else {
                    &context
                };
                read_state_cell(
                    read_context,
                    *slot,
                    keys,
                    "UIntRange<18446744073709551616>",
                    "u64",
                )?;
                if matches!(instruction, Instruction::AddImmediate { .. }) {
                    Op::Addi { immediate: amount }
                } else {
                    Op::Subi { immediate: amount }
                }
            }
            Instruction::Insert { n } => {
                has_written = true;
                ensure!(*n > 0 && *n < 16, "unsupported insertion depth");
                Op::Ins {
                    cached: false,
                    n: *n,
                }
            }
        };
        previous_index = current_index;
        program.push(op);
        activity_schedule.extend(std::iter::repeat_n(None, program.len() - operation_start));
        member_result_pending = matches!(instruction, Instruction::Member);
        if matches!(
            instruction,
            Instruction::Insert { .. }
                | Instruction::MerkleTreeInsertHash { .. }
                | Instruction::MerkleTreeInsertHashIndex { .. }
                | Instruction::MerkleTreeReset { .. }
                | Instruction::MerkleTreeResetHistory { .. }
                | Instruction::ListPushFront { .. }
                | Instruction::ListPopFront { .. }
                | Instruction::ListReset { .. }
                | Instruction::MapRemove { .. }
                | Instruction::ReceiveShieldedToMap { .. }
                | Instruction::WriteShieldedCoinCell { .. }
                | Instruction::InsertShieldedCoinSet { .. }
        ) {
            mutation_boundary = program.len();
        }
        *stored_next_operation += 1;
        *stored_read_index = read_index;
        *stored_materialized_prefix = materialized_prefix;
        *stored_mutation_boundary = mutation_boundary;
        *stored_member_result_pending = member_result_pending;
        *stored_has_written = has_written;
        *stored_previous_index = previous_index;
        Ok(PreparationStep::Operation { index, read: event })
    }

    pub fn finish(self) -> Result<Execution> {
        ensure!(!self.poisoned, "preparation cursor is poisoned");
        ensure!(self.completed, "preparation cursor is not complete");
        let PreparationCursor {
            plan,
            env,
            context,
            params,
            program,
            activity_schedule,
            read_index,
            ..
        } = self;
        let cost = &params.cost_model.runtime_cost_model;
        ensure!(
            activity_schedule
                .iter()
                .filter(|entry| entry.is_none())
                .count()
                == program.len(),
            "native activity schedule does not match emitted operations"
        );
        ensure!(read_index == plan.reads.len(), "read schema mismatch");
        let queried = context.query(&program, None, cost).map_err(|_| {
            anyhow!("native state transcript rejected (spent nullifier or state mismatch)")
        })?;
        constructor::check_sealed_state(&plan, &context.state, &queried.context.state)?;
        ensure!(plan.returns.len() <= 256, "too many call returns");
        let mut return_values = Vec::with_capacity(plan.returns.len());
        let mut return_names = BTreeSet::new();
        for output in &plan.returns {
            ensure!(
                output.visibility == "public"
                    && !output.name.is_empty()
                    && return_names.insert(output.name.as_str()),
                "invalid call return declaration"
            );
            let ty = ScalarType::parse(&output.ty)?;
            let value = evaluate(&output.expression, &env)?;
            ensure!(value.scalar_type() == ty, "call return type mismatch");
            value.validate()?;
            return_values.push((output.name.clone(), value));
        }
        let grouped_return_fields = validate_return_views_specs(
            &plan.return_views,
            plan.returns.iter().map(|output| {
                (
                    output.name.as_str(),
                    output.ty.as_str(),
                    output.visibility.as_str(),
                )
            }),
        )?;
        let logical_return_views = reconstruct_return_views(&plan.return_views, &return_values)?;
        let output = aligned_call_returns(&return_values)?;
        let randomness = Fr::from(0u64); // Diagnostic checker context. Final transactions need fresh randomness.
        let call_input = aligned_call_inputs(&plan, &env)?;
        let comm =
            onchain_runtime::communication_commitment(call_input.clone(), output, randomness);
        let partition = partition_transcripts(
            &[PreTranscript {
                context: context.clone(),
                program: program.clone(),
                comm_comm: Some(comm),
            }],
            &params,
        )
        .map_err(|_| anyhow!("native transcript partitioning failed"))?;
        let (guaranteed, fallible) = partition
            .into_iter()
            .next()
            .ok_or_else(|| anyhow!("missing transcript partition"))?;
        let mut after = context;
        if let Some(t) = &guaranteed {
            after = after
                .run_transcript(t, cost)
                .map_err(|_| anyhow!("guaranteed transcript failed"))?
                .context;
        }
        if let Some(t) = &fallible {
            after = after
                .run_transcript(t, cost)
                .map_err(|_| anyhow!("fallible transcript failed"))?
                .context;
        }
        let mut public_transcript_inputs = Vec::new();
        let mut public_transcript_outputs = Vec::new();
        for op in guaranteed
            .iter()
            .chain(fallible.iter())
            .flat_map(|t| t.program.iter_deref())
        {
            op.field_repr(&mut public_transcript_inputs);
            if let Op::Popeq { result, .. } = op {
                result.value_only_field_repr(&mut public_transcript_outputs);
            }
        }
        let mut private_transcript = Vec::new();
        let call_input_names: BTreeSet<_> = plan.call_inputs.iter().map(String::as_str).collect();
        for input in
            plan.circuit.inputs.iter().filter(|i| {
                i.visibility == "private" && !call_input_names.contains(i.name.as_str())
            })
        {
            match &env[&input.name] {
                Value::Bytes(bytes) => {
                    private_transcript.extend(bytes.iter().map(|byte| Fr::from(*byte as u64)))
                }
                Value::OpaqueBytes(_) => aligned_opaque_bytes(&env[&input.name])?
                    .value_only_field_repr(&mut private_transcript),
                Value::JubjubScalar(value) => {
                    private_transcript.push(jubjub::scalar_native(*value)?)
                }
                Value::JubjubPoint(value) => {
                    private_transcript.extend(jubjub::coordinates(*value)?)
                }
                #[cfg(feature = "zkir-321")]
                Value::Foreign(value) => private_transcript.extend(value.encode()?),
                value => aligned(value, "field")?.value_only_field_repr(&mut private_transcript),
            }
        }
        let preimage = ProofPreimage {
            inputs: ValueReprAlignedValue(call_input.clone()).field_vec(),
            private_transcript,
            public_transcript_inputs,
            public_transcript_outputs,
            binding_input: Fr::from(0u64),
            communications_commitment: Some((comm, randomness)),
            key_location: KeyLocation(Cow::Owned(plan.entrypoint.clone())),
        };
        Ok(Execution {
            program,
            activity_schedule,
            after,
            logs: queried.events,
            guaranteed,
            fallible,
            preimage,
            call_input,
            call_input_header: call_input_header(&plan.circuit.inputs, &plan.call_inputs)?,
            return_values,
            logical_return_views,
            grouped_return_fields,
        })
    }
}
pub fn check(execution: &Execution, circuit: &IrSource) -> Result<Vec<Option<usize>>> {
    let (commitment, randomness) = execution
        .preimage
        .communications_commitment
        .ok_or_else(|| anyhow!("missing call output commitment"))?;
    let circuit_json = serde_json::to_value(circuit)?;
    validate_call_input_header_json(&execution.call_input_header, &circuit_json)?;
    ensure!(
        onchain_runtime::communication_commitment(
            execution.call_input()?,
            execution.call_output()?,
            randomness
        ) == commitment,
        "call arguments or returns differ from the committed communication"
    );
    let active = execution
        .preimage
        .check(circuit)
        .map_err(|_| anyhow!("native circuit assertion or preimage check failed"))?;
    ensure!(
        active == execution.activity_schedule,
        "activity metadata does not match source operation guards"
    );
    ensure!(
        active.iter().filter(|skip| skip.is_none()).count() == execution.program.len(),
        "active activity groups do not match native operations"
    );
    Ok(active)
}

/// Versioned C ABI over the bounded provider/session runtime.
pub mod ffi;

mod jubjub;
mod scalars;
pub use scalars::{MAX_UINT_BITS, ScalarType, canonical_unsigned, max_uint};

#[cfg(feature = "zkir-321")]
pub mod foreign;

/// Versioned portable artifact manifests.
pub mod artifacts;
pub use artifacts::ContractBundleSet;

/// Native private transaction artifact assembly.
pub mod assembly;
mod composition_wire;
/// Bounded replies for an explicit browser transaction host.
pub mod browser_transport;

/// Scoped host providers and private journal transport.
pub mod host;
/// Pure private-state lifecycle model.
pub mod lifecycle;
pub mod witness;
/// Owned source witness execution, native proof and client handoff.
pub mod witness_execution;

#[cfg(all(feature = "zkir-320", feature = "zkir-321"))]
compile_error!("select exactly one native profile: zkir-320 or zkir-321");
#[cfg(not(any(feature = "zkir-320", feature = "zkir-321")))]
compile_error!("select exactly one native profile: zkir-320 or zkir-321");
#[cfg(feature = "zkir-320")]
pub use zkir_320 as zkir;
#[cfg(all(feature = "zkir-321", not(feature = "zkir-320")))]
pub use zkir_321 as zkir;
pub mod aggregates;
pub mod collection_ffi;
pub mod merkle;
pub mod native_ffi;
pub mod profile;
pub mod proof;
// Reply constructors live in explicitly selected native host adapters.
pub mod client;
pub mod control;
pub mod control_ffi;
#[cfg(all(feature = "localnet", feature = "zkir-321"))]
pub mod deployment_audit;
pub mod funding;
#[cfg(feature = "localnet")]
pub mod localnet;
#[cfg(feature = "localnet")]
pub mod localnet_ffi;
#[cfg_attr(not(feature = "localnet"), allow(dead_code))]
mod native_client;

pub mod constructor;
pub use constructor::construct_state;

#[cfg(test)]
mod shared_binding_tests {
    use super::*;
    use serde_json::json;

    fn mk_plan(circuit: Json) -> Plan {
        let mut plan: Plan = serde_json::from_value(json!({
            "schemaVersion": 2,
            "entrypoint": "sharedBindings",
            "circuit": circuit,
            "state": [],
            "operations": [],
            "reads": []
        }))
        .unwrap();
        plan.target = Some(profile::NAME.into());
        plan.target_profile = Some(profile::target_json());
        plan
    }

    fn reference(name: &str) -> Json {
        json!({"tag":"reference", "name":name})
    }

    fn native(env: &Environment, name: &str) -> Fr {
        let Value::Native(value) = env.get(name).unwrap() else {
            panic!("expected Native circuit value")
        };
        *value
    }

    #[test]
    fn shared_prefix_runs_in_order_and_stays_local() {
        let plan = mk_plan(json!({
            "inputs": [{"name":"x", "type":"Native", "visibility":"public"}],
            "sharedBindings": [
                ["_noctium_shared_0", {"tag":"add", "left":reference("x"), "right":{"tag":"constant", "value":"1"}}],
                ["_noctium_shared_1", {"tag":"add", "left":reference("_noctium_shared_0"), "right":{"tag":"constant", "value":"1"}}]
            ],
            "outputs": [
                {"name":"first", "visibility":"public", "type":"Native", "expression":reference("_noctium_shared_1")},
                {"name":"second", "visibility":"public", "type":"Native", "expression":{"tag":"add", "left":reference("first"), "right":reference("_noctium_shared_0")}}
            ]
        }));
        let env = environment(&plan, &BTreeMap::from([("x".into(), json!("2"))])).unwrap();
        assert_eq!(field_decimal(native(&env, "first")), "4");
        assert_eq!(field_decimal(native(&env, "second")), "7");
        assert!(!env.contains_key("_noctium_shared_0"));
        assert!(!env.contains_key("_noctium_shared_1"));

        let mut wrong_schema = plan;
        wrong_schema.schema_version = 1;
        assert!(validate_environment_schema(&wrong_schema).is_err());
        wrong_schema.schema_version = 2;
        wrong_schema.circuit.shared_bindings.clear();
        assert!(validate_environment_schema(&wrong_schema).is_err());
    }

    #[test]
    fn shared_prefix_defers_private_inputs_and_rejects_unsafe_shapes() {
        let plan = mk_plan(json!({
            "inputs": [
                {"name":"x", "type":"Native", "visibility":"public"},
                {"name":"later", "type":"Native", "visibility":"private"}
            ],
            "sharedBindings": [["_noctium_shared_0", {"tag":"add", "left":reference("x"), "right":reference("later")}]],
            "outputs": [
                {"name":"throughShared", "visibility":"public", "type":"Native", "expression":reference("_noctium_shared_0")},
                {"name":"direct", "visibility":"public", "type":"Native", "expression":{"tag":"constant", "value":"9"}}
            ]
        }));
        let mut env =
            parse_input_environment(&plan, &BTreeMap::from([("x".into(), json!("2"))]), true)
                .unwrap();
        let deferred = refresh_circuit_outputs(&plan, &mut env).unwrap();
        assert_eq!(deferred.len(), 2);
        assert_eq!(deferred["throughShared"][0].name, "later");
        assert_eq!(deferred["direct"][0].name, "later");
        assert!(!env.contains_key("direct"));
        assert!(!env.contains_key("_noctium_shared_0"));

        env.insert("later".into(), Value::Native(canonical_field("3").unwrap()));
        assert!(refresh_circuit_outputs(&plan, &mut env).unwrap().is_empty());
        assert_eq!(field_decimal(native(&env, "throughShared")), "5");
        assert!(!env.contains_key("_noctium_shared_0"));

        assert!(
            serde_json::from_value::<Circuit>(json!({
                "inputs": [], "outputs": [], "sharedBindings": [["_bad"]]
            }))
            .is_err()
        );

        let output_dependency = mk_plan(json!({
            "inputs": [],
            "sharedBindings": [["_noctium_shared_0", reference("base")]],
            "outputs": [
                {"name":"base", "visibility":"public", "type":"Native", "expression":{"tag":"constant", "value":"1"}},
                {"name":"derived", "visibility":"public", "type":"Native", "expression":reference("_noctium_shared_0")}
            ]
        }));
        assert!(environment(&output_dependency, &BTreeMap::new()).is_err());

        let collision = mk_plan(json!({
            "inputs": [{"name":"x", "type":"Native", "visibility":"public"}],
            "sharedBindings": [["x", {"tag":"constant", "value":"1"}]],
            "outputs": []
        }));
        assert!(environment(&collision, &BTreeMap::from([("x".into(), json!("2"))])).is_err());
    }
}

#[cfg(test)]
mod shielded_spend_tests {
    use super::*;
    use coin_structure::coin::{Commitment, Nullifier};
    use serde_json::json;

    const NONCE: [u8; 32] = [2; 32];
    const COLOR: [u8; 32] = [1; 32];
    const RECIPIENT: [u8; 32] = [3; 32];
    const ADDRESS: [u8; 32] = [0; 32];
    const RELAY_TARGET: [u8; 32] = [4; 32];
    const ENTRY_POINT: [u8; 32] = [5; 32];

    fn hash_from_hex(value: &str) -> [u8; 32] {
        assert_eq!(value.len(), 64);
        let mut bytes = [0; 32];
        for (index, byte) in bytes.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16).unwrap();
        }
        bytes
    }

    fn bytes_json(value: &[u8; 32]) -> Json {
        json!({"kind":"bytes", "values":value.iter().copied().map(u64::from).collect::<Vec<_>>()})
    }

    fn reference(name: &str) -> Json {
        json!({"tag":"reference", "name":name})
    }

    fn coin_schema() -> Json {
        json!({
            "id":"ShieldedSpend.Coin",
            "fields":[
                {"name":"nonce", "type":"Bytes<32>"},
                {"name":"color", "type":"Bytes<32>"},
                {"name":"value", "type":"UIntRange<340282366920938463463374607431768211456>"},
                {"name":"mtIndex", "type":"UIntRange<18446744073709551616>"}
            ]
        })
    }

    fn spend_plan_json() -> Json {
        let schema = coin_schema();
        let address_projections = byte_projection_bindings("selfAddress", 32)
            .unwrap()
            .into_iter()
            .map(|(name, ty)| json!({"name":name, "type":ty}))
            .collect::<Vec<_>>();
        json!({
            "schemaVersion":1,
            "entrypoint":"spend",
            "circuit":{
                "inputs":[
                    {"name":"nonce", "type":"Bytes<32>", "visibility":"private"},
                    {"name":"recipient", "type":"Bytes<32>", "visibility":"private"},
                    {"name":"sourceNullifier", "type":"Bytes<32>", "visibility":"private"},
                    {"name":"sourceCommitment", "type":"Bytes<32>", "visibility":"private"}
                ],
                "outputs":[]
            },
            "state":[{
                "name":"pot",
                "kind":{"tree":{"map":["Bytes<32>", {"composite":schema}]}}
            }],
            "operations":[
                {"op":"dup"},
                {"op":"indexPath", "slot":0, "pushPath":false,
                    "keys":[{"alignment":"bytes32", "expression":reference("nonce")}]},
                {"op":"popeqFields", "schema":schema, "expressions":[
                    reference("coin_nonce"), reference("coin_color"),
                    reference("coin_value"), reference("coin_mtIndex")
                ]},
                {"op":"readContractAddress", "destination":"selfAddress"},
                {"op":"spendShieldedFromMap",
                    "nonce":reference("coin_nonce"),
                    "color":reference("coin_color"),
                    "amount":reference("coin_value"),
                    "recipient":reference("recipient"),
                    "nullifier":reference("sourceNullifier"),
                    "outputCommitment":reference("sourceCommitment")
                },
                {"op":"mapRemove", "slot":0,
                    "keys":[{"alignment":"bytes32", "expression":reference("nonce")}]}
            ],
            "reads":[
                {"name":"coin", "type":"Composite", "schema":schema,
                    "components":[
                        {"name":"coin_nonce", "type":"Bytes<32>"},
                        {"name":"coin_color", "type":"Bytes<32>"},
                        {"name":"coin_value", "type":"UIntRange<340282366920938463463374607431768211456>"},
                        {"name":"coin_mtIndex", "type":"UIntRange<18446744073709551616>"}
                    ]},
                {"name":"selfAddress", "type":"Bytes<32>", "projections":address_projections}
            ]
        })
    }

    fn spend_plan() -> Plan {
        let mut plan: Plan = serde_json::from_value(spend_plan_json()).unwrap();
        plan.target = Some(profile::NAME.into());
        plan.target_profile = Some(profile::target_json());
        plan
    }

    fn send_plan() -> Plan {
        let mut value = spend_plan_json();
        value["entrypoint"] = json!("send");
        value["circuit"]["inputs"]
            .as_array_mut()
            .unwrap()
            .extend([
                json!({"name":"sendAmount", "type":"UIntRange<340282366920938463463374607431768211456>", "visibility":"private"}),
                json!({"name":"changeNonce", "type":"Bytes<32>", "visibility":"private"}),
                json!({"name":"changeAmount", "type":"UIntRange<340282366920938463463374607431768211456>", "visibility":"private"}),
                json!({"name":"changeCommitment", "type":"Bytes<32>", "visibility":"private"})
            ]);
        value["operations"][4] = json!({
            "op":"sendShieldedFromMap",
            "nonce":reference("coin_nonce"),
            "color":reference("coin_color"),
            "inputAmount":reference("coin_value"),
            "sendAmount":reference("sendAmount"),
            "recipient":reference("recipient"),
            "nullifier":reference("sourceNullifier"),
            "outputCommitment":reference("sourceCommitment"),
            "changeCommitment":reference("changeCommitment")
        });
        value["operations"].as_array_mut().unwrap().push(json!({
            "op":"receiveShieldedToMap",
            "slot":0,
            "nonce":reference("changeNonce"),
            "color":reference("coin_color"),
            "amount":reference("changeAmount"),
            "commitment":reference("changeCommitment")
        }));
        value["operations"]
            .as_array_mut()
            .unwrap()
            .insert(6, json!({"op":"checkpoint"}));
        let mut plan: Plan = serde_json::from_value(value).unwrap();
        plan.target = Some(profile::NAME.into());
        plan.target_profile = Some(profile::target_json());
        plan
    }

    fn relay_plan_json() -> Json {
        let mut value = spend_plan_json();
        value["entrypoint"] = json!("relayShieldedImmediate");
        value["circuit"]["inputs"] = json!([
            {"name":"nonce", "type":"Bytes<32>", "visibility":"private"},
            {"name":"color", "type":"Bytes<32>", "visibility":"private"},
            {"name":"amount", "type":"UIntRange<340282366920938463463374607431768211456>", "visibility":"private"},
            {"name":"recipient", "type":"Bytes<32>", "visibility":"private"},
            {"name":"inputCommitment", "type":"Bytes<32>", "visibility":"private"},
            {"name":"nullifier", "type":"Bytes<32>", "visibility":"private"},
            {"name":"outputCommitment", "type":"Bytes<32>", "visibility":"private"},
            {"name":"entryPoint", "type":"Bytes<32>", "visibility":"private"},
            {"name":"callCommitment", "type":"Native", "visibility":"private"}
        ]);
        value["operations"] = json!([
            {"op":"readContractAddress", "destination":"selfAddress"},
            {
                "op":"relayShieldedImmediate",
                "nonce":reference("nonce"),
                "color":reference("color"),
                "amount":reference("amount"),
                "recipient":reference("recipient"),
                "inputCommitment":reference("inputCommitment"),
                "nullifier":reference("nullifier"),
                "outputCommitment":reference("outputCommitment")
            },
            {
                "op":"claimcontractcall",
                "address":reference("recipient"),
                "entryPointHash":reference("entryPoint"),
                "commitment":reference("callCommitment")
            }
        ]);
        value["reads"] = json!([{
            "name":"selfAddress",
            "type":"Bytes<32>",
            "projections":byte_projection_bindings("selfAddress", 32)
                .unwrap()
                .into_iter()
                .map(|(name, ty)| json!({"name":name, "type":ty}))
                .collect::<Vec<_>>()
        }]);
        value
    }

    fn relay_plan() -> Plan {
        let mut plan: Plan = serde_json::from_value(relay_plan_json()).unwrap();
        plan.target = Some(profile::NAME.into());
        plan.target_profile = Some(profile::target_json());
        plan
    }

    fn relay_inputs(
        input_commitment: [u8; 32],
        nullifier: [u8; 32],
        output_commitment: [u8; 32],
    ) -> BTreeMap<String, Json> {
        BTreeMap::from([
            ("nonce".into(), bytes_json(&NONCE)),
            ("color".into(), bytes_json(&COLOR)),
            ("amount".into(), json!("5")),
            ("recipient".into(), bytes_json(&RELAY_TARGET)),
            ("inputCommitment".into(), bytes_json(&input_commitment)),
            ("nullifier".into(), bytes_json(&nullifier)),
            ("outputCommitment".into(), bytes_json(&output_commitment)),
            ("entryPoint".into(), bytes_json(&ENTRY_POINT)),
            ("callCommitment".into(), json!("17")),
        ])
    }

    fn spend_inputs(nullifier: [u8; 32], commitment: [u8; 32]) -> BTreeMap<String, Json> {
        BTreeMap::from([
            ("nonce".into(), bytes_json(&NONCE)),
            ("recipient".into(), bytes_json(&RECIPIENT)),
            ("sourceNullifier".into(), bytes_json(&nullifier)),
            ("sourceCommitment".into(), bytes_json(&commitment)),
        ])
    }

    fn send_inputs(
        nullifier: [u8; 32],
        send_commitment: [u8; 32],
        send_amount: u128,
        change_nonce: [u8; 32],
        change_amount: u128,
        change_commitment: [u8; 32],
    ) -> BTreeMap<String, Json> {
        let mut inputs = spend_inputs(nullifier, send_commitment);
        inputs.insert("sendAmount".into(), json!(send_amount.to_string()));
        inputs.insert("changeNonce".into(), bytes_json(&change_nonce));
        inputs.insert("changeAmount".into(), json!(change_amount.to_string()));
        inputs.insert("changeCommitment".into(), bytes_json(&change_commitment));
        inputs
    }

    fn context(key_nonce: [u8; 32], record_nonce: [u8; 32]) -> QueryContext<Db> {
        context_with_amount(key_nonce, record_nonce, 5)
    }

    fn context_with_amount(
        key_nonce: [u8; 32],
        record_nonce: [u8; 32],
        amount: u128,
    ) -> QueryContext<Db> {
        context_with_schema(&coin_schema(), key_nonce, record_nonce, amount)
    }

    fn context_with_schema(
        schema: &Json,
        key_nonce: [u8; 32],
        record_nonce: [u8; 32],
        amount: u128,
    ) -> QueryContext<Db> {
        let coin_schema = checked_record_schema(schema).unwrap();
        let record = aligned_record_value(
            &coin_schema,
            &[
                Value::Bytes(record_nonce.to_vec()),
                Value::Bytes(COLOR.to_vec()),
                Value::UInt {
                    number: amount.into(),
                    maximum: u128::MAX.into(),
                },
                Value::UInt {
                    number: 7u8.into(),
                    maximum: u64::MAX.into(),
                },
            ],
        )
        .unwrap();
        let mut coins: HashMap<AlignedValue, StateValue<Db>, Db> = HashMap::default();
        coins = coins.insert(
            AlignedValue::from(Nonce(HashOutput(key_nonce))),
            StateValue::Cell(Sp::new(record)),
        );
        let state = ChargedState::new(StateValue::Array(
            vec![StateValue::Map(coins)].into(),
        ));
        QueryContext::new(state, ContractAddress(HashOutput(ADDRESS)))
    }

    fn context_with_send_outputs(
        key_nonce: [u8; 32],
        record_nonce: [u8; 32],
        amount: u128,
        send_commitment: Commitment,
        send_index: u64,
        change_commitment: Commitment,
        change_index: u64,
    ) -> QueryContext<Db> {
        context_with_schema_send_outputs(
            &coin_schema(),
            key_nonce,
            record_nonce,
            amount,
            send_commitment,
            send_index,
            change_commitment,
            change_index,
        )
    }

    fn context_with_relay_bookings(
        input_commitment: Commitment,
        input_index: u64,
        output_commitment: Commitment,
        output_index: u64,
    ) -> QueryContext<Db> {
        let mut context = context(NONCE, NONCE);
        context.call_context.com_indices = context
            .call_context
            .com_indices
            .insert(input_commitment, input_index)
            .insert(output_commitment, output_index);
        context
    }

    fn context_with_schema_send_outputs(
        schema: &Json,
        key_nonce: [u8; 32],
        record_nonce: [u8; 32],
        amount: u128,
        send_commitment: Commitment,
        send_index: u64,
        change_commitment: Commitment,
        change_index: u64,
    ) -> QueryContext<Db> {
        let mut context = context_with_schema(schema, key_nonce, record_nonce, amount);
        context.call_context.com_indices =
            context
                .call_context
                .com_indices
                .insert(send_commitment, send_index)
                .insert(change_commitment, change_index);
        context
    }

    fn expected_relay_effects() -> (Commitment, Nullifier, Commitment) {
        let coin = ShieldedCoinInfo {
            nonce: Nonce(HashOutput(NONCE)),
            type_: ShieldedTokenType(HashOutput(COLOR)),
            value: 5,
        };
        let input_commitment = coin.commitment(&Recipient::Contract(ContractAddress(HashOutput(
            ADDRESS,
        ))));
        let nullifier = coin.nullifier(&SenderEvidence::Contract(ContractAddress(HashOutput(
            ADDRESS,
        ))));
        let output_coin = coin.evolve_from(
            b"midnight:kernel:nonce_evolve",
            coin.value,
            coin.type_,
        );
        let output_commitment = output_coin
            .commitment(&Recipient::Contract(ContractAddress(HashOutput(RELAY_TARGET))));
        assert_eq!(
            input_commitment.0,
            HashOutput(hash_from_hex(
                "84a93c4d7971bb71252e9b01a8cc75f4daffdcac90c25c3d3ea484a1b6eae3a0"
            ))
        );
        assert_eq!(
            nullifier.0,
            HashOutput(hash_from_hex(
                "d119520f9cd70fb3b835e7421773629b1991e38d642ff9b6b69eb9ed1bf86c24"
            ))
        );
        assert_eq!(
            output_commitment.0,
            HashOutput(hash_from_hex(
                "142498ccc64b0b945dbabf4804b879f555b3e1eefe9251b9d6e4abaad1ca5a0b"
            ))
        );
        (input_commitment, nullifier, output_commitment)
    }

    fn expected_coin_effects() -> (Nullifier, Commitment) {
        let coin = ShieldedCoinInfo {
            nonce: Nonce(HashOutput(NONCE)),
            type_: ShieldedTokenType(HashOutput(COLOR)),
            value: 5,
        };
        let nullifier = coin.nullifier(&SenderEvidence::Contract(ContractAddress(HashOutput(ADDRESS))));
        let evolved = coin.evolve_from(
            b"midnight:kernel:nonce_evolve",
            coin.value,
            coin.type_,
        );
        let output = evolved.commitment(&Recipient::User(PublicKey(HashOutput(RECIPIENT))));
        assert_eq!(
            nullifier.0,
            HashOutput(hash_from_hex(
                "d119520f9cd70fb3b835e7421773629b1991e38d642ff9b6b69eb9ed1bf86c24"
            ))
        );
        assert_eq!(
            output.0,
            HashOutput(hash_from_hex(
                "800f1c60e2b9e9da8e987cc2d31713904daa9920005e1490aeab9366f24eb149"
            ))
        );
        (nullifier, output)
    }

    fn expected_split_effects() -> (
        Nullifier,
        ShieldedCoinInfo,
        Commitment,
        ShieldedCoinInfo,
        Commitment,
    ) {
        let coin = ShieldedCoinInfo {
            nonce: Nonce(HashOutput(NONCE)),
            type_: ShieldedTokenType(HashOutput(COLOR)),
            value: 5,
        };
        let nullifier = coin.nullifier(&SenderEvidence::Contract(ContractAddress(HashOutput(
            ADDRESS,
        ))));
        let send_coin = coin.evolve_from(b"midnight:kernel:nonce_evolve", 2, coin.type_);
        let send_commitment =
            send_coin.commitment(&Recipient::User(PublicKey(HashOutput(RECIPIENT))));
        let change_coin = coin.evolve_from(b"midnight:kernel:nonce_evolve/2", 3, coin.type_);
        let change_commitment =
            change_coin.commitment(&Recipient::Contract(ContractAddress(HashOutput(ADDRESS))));
        assert_eq!(
            nullifier.0,
            HashOutput(hash_from_hex(
                "d119520f9cd70fb3b835e7421773629b1991e38d642ff9b6b69eb9ed1bf86c24"
            ))
        );
        assert_eq!(
            send_commitment.0,
            HashOutput(hash_from_hex(
                "ed1aadafa7d1883bc63e45853fc4b51f21fb99c6ae68c8de9a256cbc3ac299c7"
            ))
        );
        assert_eq!(
            change_commitment.0,
            HashOutput(hash_from_hex(
                "ac1f3bb1ec93068af7810556a541cd2fbd3eb3e8e1c4336a7e5a72ee403405c2"
            ))
        );
        assert_eq!(
            change_coin.nonce.0,
            HashOutput(hash_from_hex(
                "0283a70d7732a940d63ebf3957495f2549236d165e604aa67a59d7eb746f4b00"
            ))
        );

        let equal_send = coin.evolve_from(b"midnight:kernel:nonce_evolve", 2, coin.type_);
        let equal_change = coin.evolve_from(b"midnight:kernel:nonce_evolve/2", 2, coin.type_);
        assert_ne!(equal_send.nonce, equal_change.nonce);

        (
            nullifier,
            send_coin,
            send_commitment,
            change_coin,
            change_commitment,
        )
    }

    #[test]
    fn shielded_spend_claims_the_compact_coin_and_removes_its_exact_row() {
        let (nullifier, commitment) = expected_coin_effects();
        let plan = spend_plan();
        let inputs = spend_inputs(nullifier.0.0, commitment.0.0);
        let execution = prepare_with_context(
            &plan,
            &inputs,
            context(NONCE, NONCE),
            &ledger::structure::INITIAL_PARAMETERS,
        )
        .unwrap();

        assert!(execution.after.effects.claimed_nullifiers.member(&nullifier));
        assert!(execution
            .after
            .effects
            .claimed_shielded_spends
            .member(&commitment));
        let key = aligned_bytes(&Value::Bytes(NONCE.to_vec())).unwrap();
        assert!(read_state_value(&execution.after, 0, &[key]).is_err());

        // A repeated spend sees no row after the first call's atomic removal.
        assert!(prepare_with_context(
            &plan,
            &inputs,
            execution.after.clone(),
            &ledger::structure::INITIAL_PARAMETERS,
        )
        .is_err());

        if std::env::var_os("NOCTIUM_CHECK_SHIELDED_SPEND_ARTIFACT").is_some() {
            let artifact_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../build/experiments/210/lean-spend");
            let compiled_plan: Plan = serde_json::from_slice(
                &std::fs::read(artifact_dir.join("ShieldedSpend.spend.impact.json")).unwrap(),
            )
            .unwrap();
            let circuit_bytes =
                std::fs::read(artifact_dir.join("ShieldedSpend.spend.zkir")).unwrap();
            let circuit = IrSource::load(circuit_bytes.as_slice()).unwrap();
            let compiled_inputs = BTreeMap::from([
                ("nonce".into(), bytes_json(&NONCE)),
                ("recipient".into(), bytes_json(&RECIPIENT)),
            ]);
            let compiled_execution = prepare_with_context(
                &compiled_plan,
                &compiled_inputs,
                context(NONCE, NONCE),
                &ledger::structure::INITIAL_PARAMETERS,
            )
            .unwrap();
            let checked_schedule = compiled_execution
                .preimage
                .check(&circuit)
                .unwrap_or_else(|error| panic!("compiled preimage check failed: {error:#}"));
            assert_eq!(checked_schedule, compiled_execution.activity_schedule);
            super::check(&compiled_execution, &circuit).unwrap();
        }
    }

    #[test]
    fn shielded_spend_rejects_missing_mismatched_and_unclaimed_coins() {
        let (nullifier, commitment) = expected_coin_effects();
        let plan = spend_plan();
        let inputs = spend_inputs(nullifier.0.0, commitment.0.0);
        let parameters = &ledger::structure::INITIAL_PARAMETERS;

        assert!(prepare_with_context(
            &plan,
            &inputs,
            context([8; 32], [8; 32]),
            parameters,
        )
        .is_err());
        assert!(prepare_with_context(
            &plan,
            &inputs,
            context(NONCE, [9; 32]),
            parameters,
        )
        .is_err());

        let mut wrong_nullifier = inputs.clone();
        wrong_nullifier.insert("sourceNullifier".into(), bytes_json(&[0; 32]));
        assert!(prepare_with_context(
            &plan,
            &wrong_nullifier,
            context(NONCE, NONCE),
            parameters,
        )
        .is_err());

        let mut wrong_commitment = inputs;
        wrong_commitment.insert("sourceCommitment".into(), bytes_json(&[0; 32]));
        assert!(prepare_with_context(
            &plan,
            &wrong_commitment,
            context(NONCE, NONCE),
            parameters,
        )
        .is_err());
    }

    #[test]
    fn shielded_send_matches_compact_split_claims_and_replaces_the_exact_row_with_change() {
        let (nullifier, send_coin, send_commitment, change_coin, change_commitment) =
            expected_split_effects();
        let plan = send_plan();
        let inputs = send_inputs(
            nullifier.0.0,
            send_commitment.0.0,
            2,
            change_coin.nonce.0.0,
            3,
            change_commitment.0.0,
        );
        let execution = prepare_with_context(
            &plan,
            &inputs,
            context_with_send_outputs(
                NONCE,
                NONCE,
                5,
                send_commitment,
                7,
                change_commitment,
                8,
            ),
            &ledger::structure::INITIAL_PARAMETERS,
        )
        .unwrap();

        let nullifier_ops =
            onchain_runtime::program_fragments::kernel_claim_zswap_nullifier!((), (), nullifier);
        let send_ops = onchain_runtime::program_fragments::kernel_claim_zswap_coin_spend!(
            (),
            (),
            send_commitment
        );
        let change_ops = onchain_runtime::program_fragments::kernel_claim_zswap_coin_spend!(
            (),
            (),
            change_commitment
        );
        let mut expected_program: Program = nullifier_ops.into();
        expected_program.extend(send_ops);
        expected_program.extend(change_ops);
        assert!(
            execution
                .program
                .windows(expected_program.len())
                .any(|operations| operations == expected_program)
        );
        assert_eq!(execution.after.effects.claimed_nullifiers.size(), 1);
        assert!(
            execution
                .after
                .effects
                .claimed_nullifiers
                .member(&nullifier)
        );
        assert_eq!(execution.after.effects.claimed_shielded_spends.size(), 2);
        assert!(
            execution
                .after
                .effects
                .claimed_shielded_spends
                .member(&send_commitment)
        );
        assert!(
            execution
                .after
                .effects
                .claimed_shielded_spends
                .member(&change_commitment)
        );
        assert!(
            execution
                .after
                .effects
                .claimed_shielded_receives
                .iter()
                .any(|entry| **entry == change_commitment)
        );

        let spent_key = aligned_bytes(&Value::Bytes(NONCE.to_vec())).unwrap();
        assert!(read_state_value(&execution.after, 0, &[spent_key]).is_err());
        let change_key = AlignedValue::from(change_coin.nonce);
        let StateValue::Array(slots) = execution.after.state.get_ref() else {
            panic!("expected native state array")
        };
        let StateValue::Map(coins) = slots.get(0).unwrap() else {
            panic!("expected shielded coin Map")
        };
        assert_eq!(
            coins.get(&change_key).as_deref(),
            Some(&StateValue::Cell(Sp::new(AlignedValue::from(
                change_coin.qualify(8)
            ))))
        );
        assert_eq!(send_coin.value, 2);
        assert_eq!(change_coin.value, 3);

        if std::env::var_os("NOCTIUM_CHECK_SHIELDED_SEND_ARTIFACT").is_some() {
            let artifact_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../build/experiments/214/lean-partial-spend-shared-address");
            let compiled_plan: Plan = serde_json::from_slice(
                &std::fs::read(artifact_dir.join("ShieldedMapPartialSpend.spend.impact.json"))
                    .unwrap(),
            )
            .unwrap();
            let circuit_bytes =
                std::fs::read(artifact_dir.join("ShieldedMapPartialSpend.spend.zkir")).unwrap();
            let circuit = IrSource::load(circuit_bytes.as_slice()).unwrap();
            let compiled_inputs = BTreeMap::from([
                ("nonce".into(), bytes_json(&NONCE)),
                ("sendAmount".into(), json!("2")),
                ("recipient".into(), bytes_json(&RECIPIENT)),
            ]);
            let mut schema = coin_schema();
            schema["id"] = json!("ShieldedMapPartialSpend.Coin");
            let compiled_execution = prepare_with_context(
                &compiled_plan,
                &compiled_inputs,
                context_with_schema_send_outputs(
                    &schema,
                    NONCE,
                    NONCE,
                    5,
                    send_commitment,
                    7,
                    change_commitment,
                    8,
                ),
                &ledger::structure::INITIAL_PARAMETERS,
            )
            .unwrap();
            let checked_schedule = compiled_execution
                .preimage
                .check(&circuit)
                .unwrap_or_else(|error| panic!("compiled send preimage check failed: {error:#}"));
            assert_eq!(checked_schedule, compiled_execution.activity_schedule);
            super::check(&compiled_execution, &circuit).unwrap();
        }

        assert!(
            prepare_with_context(
                &plan,
                &inputs,
                execution.after,
                &ledger::structure::INITIAL_PARAMETERS,
            )
            .is_err()
        );
    }

    #[test]
    fn shielded_send_rejects_changed_claims_amounts_and_receive_booking() {
        let (nullifier, _, send_commitment, change_coin, change_commitment) =
            expected_split_effects();
        let plan = send_plan();
        let inputs = send_inputs(
            nullifier.0.0,
            send_commitment.0.0,
            2,
            change_coin.nonce.0.0,
            3,
            change_commitment.0.0,
        );
        let parameters = &ledger::structure::INITIAL_PARAMETERS;

        for name in ["sourceNullifier", "sourceCommitment", "changeCommitment"] {
            let mut wrong = inputs.clone();
            wrong.insert(name.into(), bytes_json(&[0; 32]));
            assert!(
                prepare_with_context(
                    &plan,
                    &wrong,
                    context_with_send_outputs(
                        NONCE,
                        NONCE,
                        5,
                        send_commitment,
                        7,
                        change_commitment,
                        8,
                    ),
                    parameters,
                )
                .is_err()
            );
        }

        for amount in [0, 5, 6] {
            let mut wrong = inputs.clone();
            wrong.insert("sendAmount".into(), json!(amount.to_string()));
            assert!(
                prepare_with_context(
                    &plan,
                    &wrong,
                    context_with_send_outputs(
                        NONCE,
                        NONCE,
                        5,
                        send_commitment,
                        7,
                        change_commitment,
                        8,
                    ),
                    parameters,
                )
                .is_err()
            );
        }

        let mut wrong_nonce = inputs.clone();
        wrong_nonce.insert("changeNonce".into(), bytes_json(&[9; 32]));
        assert!(
            prepare_with_context(
                &plan,
                &wrong_nonce,
                context_with_send_outputs(
                    NONCE,
                    NONCE,
                    5,
                    send_commitment,
                    7,
                    change_commitment,
                    8,
                ),
                parameters,
            )
            .is_err()
        );
        assert!(prepare_with_context(&plan, &inputs, context(NONCE, NONCE), parameters,).is_err());
    }

    #[test]
    fn shielded_immediate_relay_matches_compact_claims_and_requires_booked_coins() {
        let (input_commitment, nullifier, output_commitment) = expected_relay_effects();
        let plan = relay_plan();
        let inputs = relay_inputs(
            input_commitment.0.0,
            nullifier.0.0,
            output_commitment.0.0,
        );
        let execution = prepare_with_context(
            &plan,
            &inputs,
            context_with_relay_bookings(input_commitment, 7, output_commitment, 9),
            &ledger::structure::INITIAL_PARAMETERS,
        )
        .unwrap();

        let receive_ops = onchain_runtime::program_fragments::kernel_claim_zswap_coin_receive!(
            (),
            (),
            input_commitment
        );
        let nullifier_ops = onchain_runtime::program_fragments::kernel_claim_zswap_nullifier!(
            (),
            (),
            nullifier
        );
        let spend_ops = onchain_runtime::program_fragments::kernel_claim_zswap_coin_spend!(
            (),
            (),
            output_commitment
        );
        let mut expected_program: Program = receive_ops.into();
        expected_program.extend(nullifier_ops);
        expected_program.extend(spend_ops);
        assert!(execution
            .program
            .windows(expected_program.len())
            .any(|operations| operations == expected_program));
        assert_eq!(execution.after.effects.claimed_nullifiers.size(), 1);
        assert!(execution
            .after
            .effects
            .claimed_nullifiers
            .member(&nullifier));
        assert_eq!(execution.after.effects.claimed_shielded_receives.size(), 1);
        assert!(execution
            .after
            .effects
            .claimed_shielded_receives
            .iter()
            .any(|entry| **entry == input_commitment));
        assert_eq!(execution.after.effects.claimed_shielded_spends.size(), 1);
        assert!(execution
            .after
            .effects
            .claimed_shielded_spends
            .member(&output_commitment));

        let parameters = &ledger::structure::INITIAL_PARAMETERS;
        for (name, wrong) in [
            ("inputCommitment", [0; 32]),
            ("nullifier", [0; 32]),
            ("outputCommitment", [0; 32]),
        ] {
            let mut changed = inputs.clone();
            changed.insert(name.into(), bytes_json(&wrong));
            assert!(prepare_with_context(
                &plan,
                &changed,
                context_with_relay_bookings(input_commitment, 7, output_commitment, 9),
                parameters,
            )
            .is_err());
        }

        assert!(prepare_with_context(
            &plan,
            &inputs,
            context_with_relay_bookings(input_commitment, 7, Commitment(HashOutput([8; 32])), 9),
            parameters,
        )
        .is_err());
        assert!(prepare_with_context(
            &plan,
            &inputs,
            context_with_relay_bookings(Commitment(HashOutput([8; 32])), 7, output_commitment, 9),
            parameters,
        )
        .is_err());

        let mut wrong_call_target = plan.clone();
        let Instruction::ClaimContractCall { address, .. } = &mut wrong_call_target.operations[2]
        else {
            unreachable!("relay plan ends with its child call")
        };
        *address = serde_json::from_value(reference("entryPoint")).unwrap();
        assert!(prepare_with_context(
            &wrong_call_target,
            &inputs,
            context_with_relay_bookings(input_commitment, 7, output_commitment, 9),
            parameters,
        )
        .is_err());
    }

    #[test]
    fn shielded_send_layout_allows_the_compiled_change_membership_reads() {
        let mut plan = send_plan();
        let read_only = [
            json!({"op":"indexPath", "slot":0, "pushPath":false, "keys":[]}),
            json!({
                "op":"push", "storage":false, "alignment":"bytes32",
                "expression":reference("changeNonce")
            }),
            json!({"op":"member"}),
            json!({
                "op":"popeq", "alignment":"bit", "expression":reference("changeMember")
            }),
        ]
        .into_iter()
        .map(serde_json::from_value::<Instruction>)
        .collect::<std::result::Result<Vec<Instruction>, _>>()
        .unwrap();
        plan.operations.splice(6..7, read_only);
        let Instruction::SendShieldedFromMap {
            nonce,
            color,
            input_amount,
            change_commitment,
            ..
        } = &plan.operations[4]
        else {
            unreachable!("send plan has a shielded send operation")
        };

        let (_, _, receive_index) = validate_shielded_send_layout(
            &plan,
            4,
            nonce,
            color,
            input_amount,
            change_commitment,
        )
        .unwrap();
        assert_eq!(receive_index, 10);
    }
}
