//! Version 1 plans use host policy. Version 2 plans bind typed source execution to retained artifacts.
//! This interpreter enforces source disclosure and control checks. Native proof verification remains in the proof module.
use crate::{ScalarType, Value, canonical_field, host, input_value, max_uint, scalars, witness};
use anyhow::{Result, anyhow, bail, ensure};
use serde::Deserialize;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    ops::{Deref, DerefMut},
    sync::Arc,
    sync::atomic::{AtomicU64, AtomicUsize, Ordering},
};
use zeroize::Zeroize;

pub const MAX_BYTES: usize = 1_048_576;
pub const MAX_STEPS: usize = 131_072;
const MAX_NODES: usize = 16_384;
const MAX_DEPTH: usize = 128;
const MAX_FUNCTIONS: usize = 256;
const MAX_ARGUMENTS: usize = 64;
const MAX_WITNESSES: usize = 32;
const MAX_AGGREGATE_JSON_NODES: usize = 65_536;
const MAX_AGGREGATE_VALUE_BYTES: usize = 2 * MAX_BYTES;
const MAX_SESSION_AGGREGATE_BYTES: usize = 4 * MAX_BYTES;
const MAX_COMPLETED_INPUT_BYTES: usize = MAX_BYTES;
const AGGREGATE_MATERIALIZATION_ENTRY_OVERHEAD: usize = 256;
static NEXT_TYPED_REQUEST_ID: AtomicU64 = AtomicU64::new(1);

#[derive(Clone, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct InvocationTarget {
    pub contract_address: String,
    pub entrypoint: String,
}
pub(crate) struct AuthenticatedNativeTarget {
    pub context_id: u64,
    pub contract_address: String,
    pub entrypoint: String,
    pub control_plan: Json,
    pub control_plan_bytes: Vec<u8>,
    pub binding_bytes: Vec<u8>,
    pub relation: Json,
}
impl InvocationTarget {
    fn validate(&self) -> Result<()> {
        ensure!(
            self.contract_address.len() == 64
                && self
                    .contract_address
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
            "invalid invocation contract address"
        );
        ensure!(
            host_identifier(&self.entrypoint),
            "invalid invocation entrypoint"
        );
        Ok(())
    }
}

type Type = witness::Type;

fn supported_ledger_read_type(ty: &ScalarType) -> bool {
    match ty {
        ScalarType::Native | ScalarType::Bool | ScalarType::UInt(_) | ScalarType::JubjubScalar => {
            true
        }
        #[cfg(feature = "zkir-321")]
        ScalarType::Foreign(_) => true,
        _ => false,
    }
}

fn supported_ledger_field_type(ty: &ScalarType) -> bool {
    matches!(
        ty,
        ScalarType::Native | ScalarType::Bool | ScalarType::UInt(_)
    )
}

fn parse_type(text: &str, registry: &witness::Registry) -> Result<Type> {
    if text == "Unit" {
        Ok(Type::Unit)
    } else if text.starts_with("Aggregate:") {
        ensure!(registry.contains(text), "unknown control aggregate type");
        Ok(Type::Aggregate(text.to_owned()))
    } else {
        Ok(Type::Scalar(ScalarType::parse(text)?))
    }
}

impl Type {
    fn coerce(&self, mut value: Tracked) -> Result<Tracked> {
        match self {
            Self::Unit => {
                ensure!(
                    value.value.is_none() && value.aggregate.is_none(),
                    "control value type mismatch"
                );
                value.known = Some(None);
            }
            Self::Scalar(ty) => {
                ensure!(value.aggregate.is_none(), "control value type mismatch");
                value.value = Some(
                    value
                        .value
                        .take()
                        .ok_or_else(|| anyhow!("control scalar required"))?
                        .cast(ty)?,
                );
                value.known = known_cast(self, value.known.take());
            }
            Self::Aggregate(token) => {
                ensure!(value.value.is_none(), "control value type mismatch");
                let aggregate = value
                    .aggregate
                    .as_mut()
                    .ok_or_else(|| anyhow!("control aggregate required"))?;
                ensure!(&aggregate.token == token, "control aggregate type mismatch");
                value.known = None;
            }
        }
        Ok(value)
    }
}
fn subtype(a: &Type, b: &Type) -> bool {
    a == b
        || matches!(
            (a, b),
            (
                Type::Scalar(ScalarType::UInt(_)),
                Type::Scalar(ScalarType::Native)
            )
        )
        || matches!((a,b), (Type::Scalar(ScalarType::UInt(m)),Type::Scalar(ScalarType::UInt(n))) if m<=n)
}
fn join(a: &Type, b: &Type) -> Result<Type> {
    if subtype(a, b) {
        Ok(b.clone())
    } else if subtype(b, a) {
        Ok(a.clone())
    } else {
        bail!("control branch type mismatch")
    }
}
fn scalar_type(ty: &Type) -> Result<&ScalarType> {
    match ty {
        Type::Scalar(t) => Ok(t),
        _ => bail!("control scalar required"),
    }
}

fn boolean_operation(operation: BooleanOperation) -> (Vec<ScalarType>, ScalarType, crate::Expr) {
    let argument = |index: usize| {
        Box::new(crate::Expr::Reference {
            name: index.to_string(),
        })
    };
    let left = argument(0);
    let right = argument(1);
    let expression = match operation {
        BooleanOperation::And => crate::Expr::BoolAnd { left, right },
        BooleanOperation::Or => crate::Expr::BoolOr { left, right },
        BooleanOperation::Xor => crate::Expr::BoolXor { left, right },
    };
    (
        vec![ScalarType::Bool, ScalarType::Bool],
        ScalarType::Bool,
        expression,
    )
}

fn curve_operation(operation: &str) -> Result<(Vec<ScalarType>, ScalarType, crate::Expr)> {
    use ScalarType::{JubjubPoint, JubjubScalar, Native};
    let argument = |index: usize| {
        Box::new(crate::Expr::Reference {
            name: index.to_string(),
        })
    };
    #[cfg(feature = "zkir-321")]
    if operation.starts_with("foreignUnary:") || operation.starts_with("foreignBinary:") {
        let count = if operation.starts_with("foreignUnary:") {
            1
        } else {
            2
        };
        return foreign_curve_operation(operation, count);
    }
    if let Some(encoded_arity) = operation.strip_prefix("transientHashNativeVector:") {
        let arity = canonical_transient_hash_arity(encoded_arity)?;
        return Ok((
            vec![Native; arity],
            Native,
            crate::Expr::TransientHash {
                values: (0..arity)
                    .map(|index| crate::TransientHashOperand::Expression(*argument(index)))
                    .collect(),
            },
        ));
    }
    if let Some(encoded_arity) = operation.strip_prefix("hashToCurve:") {
        let arity = canonical_hash_to_curve_arity(encoded_arity)?;
        return Ok((
            vec![Native; arity],
            JubjubPoint,
            crate::Expr::HashToCurve {
                values: (0..arity).map(|index| *argument(index)).collect(),
            },
        ));
    }
    Ok(match operation {
        "jubjubScalarFromNative" => (
            vec![Native],
            JubjubScalar,
            crate::Expr::JubjubScalarFromNative { value: argument(0) },
        ),
        "jubjubScalarToNative" => (
            vec![JubjubScalar],
            Native,
            crate::Expr::JubjubScalarToNative { value: argument(0) },
        ),
        "jubjubMulGenerator" => (
            vec![JubjubScalar],
            JubjubPoint,
            crate::Expr::JubjubMulGenerator {
                scalar: argument(0),
            },
        ),
        "jubjubMul" => (
            vec![JubjubPoint, JubjubScalar],
            JubjubPoint,
            crate::Expr::JubjubMul {
                point: argument(0),
                scalar: argument(1),
            },
        ),
        "jubjubAdd" => (
            vec![JubjubPoint, JubjubPoint],
            JubjubPoint,
            crate::Expr::JubjubAdd {
                left: argument(0),
                right: argument(1),
            },
        ),
        "jubjubNeg" => (
            vec![JubjubPoint],
            JubjubPoint,
            crate::Expr::JubjubNeg { point: argument(0) },
        ),
        "jubjubX" | "jubjubY" => (
            vec![JubjubPoint],
            Native,
            crate::Expr::JubjubCoordinate {
                point: argument(0),
                index: usize::from(operation == "jubjubY"),
            },
        ),
        "jubjubFromCoordinates" => (
            vec![Native, Native],
            JubjubPoint,
            crate::Expr::JubjubFromCoordinates {
                x: argument(0),
                y: argument(1),
            },
        ),
        _ => bail!("unsupported control curve operation"),
    })
}

#[cfg(feature = "zkir-321")]
fn foreign_curve_operation(
    operation: &str,
    count: usize,
) -> Result<(Vec<ScalarType>, ScalarType, crate::Expr)> {
    use crate::foreign::{ForeignBinaryOp, ForeignType, ForeignUnaryOp};
    let argument = |index: usize| {
        Box::new(crate::Expr::Reference {
            name: index.to_string(),
        })
    };
    if let Some(encoded) = operation.strip_prefix("foreignUnary:") {
        let fields = encoded.split(':').collect::<Vec<_>>();
        ensure!(
            fields.len() == 2 && count == 1,
            "foreign unary operation encoding"
        );
        let op = ForeignUnaryOp::parse(fields[0])?;
        let input = ForeignType::parse_source_name(fields[1])?;
        ensure!(
            operation == format!("foreignUnary:{}:{}", fields[0], input.source_name()),
            "noncanonical foreign unary operation"
        );
        let output = input.unary_result(op)?;
        return Ok((
            vec![ScalarType::Foreign(input)],
            ScalarType::Foreign(output),
            crate::Expr::ForeignUnary {
                operation: fields[0].to_owned(),
                value: argument(0),
            },
        ));
    }
    if let Some(encoded) = operation.strip_prefix("foreignBinary:") {
        let fields = encoded.split(':').collect::<Vec<_>>();
        ensure!(
            fields.len() == 3 && count == 2,
            "foreign binary operation encoding"
        );
        let op = ForeignBinaryOp::parse(fields[0])?;
        let left = ForeignType::parse_source_name(fields[1])?;
        let right = ForeignType::parse_source_name(fields[2])?;
        ensure!(
            operation
                == format!(
                    "foreignBinary:{}:{}:{}",
                    fields[0],
                    left.source_name(),
                    right.source_name()
                ),
            "noncanonical foreign binary operation"
        );
        let output = left.binary_result(op, right)?;
        return Ok((
            vec![ScalarType::Foreign(left), ScalarType::Foreign(right)],
            ScalarType::Foreign(output),
            crate::Expr::ForeignBinary {
                operation: fields[0].to_owned(),
                left: argument(0),
                right: argument(1),
            },
        ));
    }
    bail!("unsupported control foreign curve operation")
}

fn canonical_hash_to_curve_arity(text: &str) -> Result<usize> {
    ensure!(
        !text.is_empty()
            && text.bytes().all(|byte| byte.is_ascii_digit())
            && (text == "0" || !text.starts_with('0')),
        "noncanonical control hashToCurve arity"
    );
    let arity = text
        .parse::<usize>()
        .map_err(|_| anyhow!("control hashToCurve arity"))?;
    ensure!(
        arity <= crate::MAX_HASH_TO_CURVE_FIELDS,
        "control hashToCurve field limit"
    );
    Ok(arity)
}

fn canonical_transient_hash_arity(text: &str) -> Result<usize> {
    ensure!(
        !text.is_empty()
            && text.bytes().all(|byte| byte.is_ascii_digit())
            && (text == "0" || !text.starts_with('0')),
        "noncanonical control transientHashNativeVector arity"
    );
    let arity = text
        .parse::<usize>()
        .map_err(|_| anyhow!("control transientHashNativeVector arity"))?;
    ensure!(
        arity <= crate::MAX_TRANSIENT_HASH_FIELDS,
        "control transientHashNativeVector field limit"
    );
    Ok(arity)
}

fn byte_scalar_type(length: usize) -> ScalarType {
    if length == 32 {
        ScalarType::Bytes32
    } else {
        ScalarType::Bytes(length)
    }
}

fn fab_digest_scalar_type(field: &crate::aggregates::FabHashField) -> ScalarType {
    use crate::aggregates::FabHashField;
    match field {
        FabHashField::Bytes(length) => byte_scalar_type(*length),
        FabHashField::Bool => ScalarType::Bool,
        FabHashField::UInt(maximum) | FabHashField::EnumTag { maximum, .. } => {
            ScalarType::UInt(maximum.clone())
        }
        FabHashField::Native => ScalarType::Native,
        FabHashField::Curve(ty) => ty.clone(),
    }
}

#[derive(Clone)]
enum FabDigestArgumentKind {
    Scalar,
    AggregateBytes { token: String, length: usize },
}

fn aggregate_bytes_value(value: &Json, length: usize) -> Result<Value> {
    ensure!(
        text(value, "kind")? == "bytes",
        "control aggregate byte value"
    );
    let raw_bytes = list(value, "values")?;
    ensure!(raw_bytes.len() == length, "control aggregate byte length");
    let bytes = raw_bytes
        .iter()
        .map(|value| {
            value
                .as_u64()
                .filter(|byte| *byte <= u8::MAX as u64)
                .map(|byte| byte as u8)
                .ok_or_else(|| anyhow!("control aggregate byte out of range"))
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(Value::Bytes(bytes))
}

fn fab_curve_source_name(ty: &ScalarType) -> Result<String> {
    match ty {
        ScalarType::JubjubScalar => Ok("JubjubScalar".to_owned()),
        ScalarType::JubjubPoint => Ok("JubjubPoint".to_owned()),
        #[cfg(feature = "zkir-321")]
        ScalarType::Foreign(ty) => Ok(ty.source_name().to_owned()),
        _ => bail!("unsupported FAB curve field type"),
    }
}

fn fab_digest_input(
    field: &crate::aggregates::FabHashField,
    index: usize,
) -> Result<crate::FabHashInput> {
    use crate::aggregates::FabHashField;
    let value = || {
        Box::new(crate::Expr::Reference {
            name: index.to_string(),
        })
    };
    Ok(match field {
        FabHashField::Bytes(length) => crate::FabHashInput::Bytes {
            length: *length,
            value: value(),
        },
        FabHashField::Bool => crate::FabHashInput::Bool { value: value() },
        FabHashField::UInt(maximum) => crate::FabHashInput::Uint {
            maximum: maximum.to_str_radix(10),
            value: value(),
        },
        FabHashField::EnumTag { id, maximum } => crate::FabHashInput::EnumTag {
            id: id.clone(),
            maximum: maximum.to_str_radix(10),
            value: value(),
        },
        FabHashField::Native => crate::FabHashInput::Native { value: value() },
        FabHashField::Curve(ty) => crate::FabHashInput::Curve {
            ty: fab_curve_source_name(ty)?,
            value: value(),
        },
    })
}

fn fab_digest_operation(
    operation: &str,
    schema: Json,
    fields: &[crate::aggregates::FabHashField],
) -> Result<(Vec<ScalarType>, ScalarType, crate::Expr)> {
    let parameters = fields
        .iter()
        .map(fab_digest_scalar_type)
        .collect::<Vec<_>>();
    let values = fields
        .iter()
        .enumerate()
        .map(|(index, field)| fab_digest_input(field, index))
        .collect::<Result<Vec<_>>>()?;
    match operation {
        "persistentHash" => Ok((
            parameters,
            ScalarType::Bytes32,
            crate::Expr::PersistentHashFab { schema, values },
        )),
        "sha512" => Ok((
            parameters,
            ScalarType::Bytes(64),
            crate::Expr::Sha512Fab { schema, values },
        )),
        "keccak256" => Ok((
            parameters,
            ScalarType::Bytes32,
            crate::Expr::Keccak256Fab { schema, values },
        )),
        _ => bail!("unsupported control FAB digest operation"),
    }
}

fn canonical_byte_length(text: &str) -> Result<usize> {
    ensure!(
        !text.is_empty()
            && text.bytes().all(|byte| byte.is_ascii_digit())
            && (text == "0" || !text.starts_with('0')),
        "noncanonical control byte length"
    );
    let length = text
        .parse::<usize>()
        .map_err(|_| anyhow!("control byte length"))?;
    ensure!(
        length <= scalars::MAX_BYTES_LENGTH,
        "control byte length exceeds the source limit"
    );
    Ok(length)
}

fn scalar_wire_operation(
    encode: bool,
    encoded: &str,
    count: usize,
) -> Result<(Vec<ScalarType>, ScalarType, crate::Expr)> {
    use crate::Expr;
    use ScalarType::*;
    let (token, length) = encoded
        .split_once(':')
        .ok_or_else(|| anyhow!("wire codec requires a type and byte length"))?;
    ensure!(count == 1, "wire codec requires one argument");
    let ty = ScalarType::parse(token)?;
    let length = canonical_byte_length(length)?;
    let width = match &ty {
        Native | JubjubScalar => 32,
        Bool => 1,
        UInt(maximum) => maximum.bits().div_ceil(8) as usize,
        Bytes32 => 32,
        Bytes(length) => *length,
        #[cfg(feature = "zkir-321")]
        Foreign(kind) if kind.role() != crate::foreign::ForeignRole::Point => 32,
        _ => bail!("wire codec requires a scalar or fixed bytes"),
    };
    ensure!(width <= length, "wire codec frame is too short");
    let reference = |name: &str| Box::new(Expr::Reference { name: name.into() });
    let arg = reference("0");
    let slice = |value, length, end| {
        Box::new(Expr::SliceBytes {
            value,
            length,
            start: 0,
            end,
        })
    };
    let literal = |length, values| Box::new(Expr::BytesLiteral { length, values });
    let cast = |ty: &str, value| {
        Box::new(Expr::Cast {
            ty: ty.into(),
            value,
        })
    };
    if encode {
        let bytes = match ty {
            Native | JubjubScalar => Box::new(Expr::ToBytes32 { value: arg }),
            Bool => Box::new(Expr::Select {
                condition: arg,
                yes: literal(1, vec![1]),
                no: literal(1, vec![0]),
            }),
            UInt(_) => slice(
                Box::new(Expr::ToBytes32 {
                    value: cast("Native", arg),
                }),
                32,
                width,
            ),
            Bytes32 | Bytes(_) => arg,
            #[cfg(feature = "zkir-321")]
            Foreign(_) => Box::new(Expr::ForeignToBytes { value: arg }),
            _ => bail!("unsupported wire encoding kind"),
        };
        let result = if width == length {
            *bytes
        } else {
            Expr::ConcatBytes {
                left_length: width,
                right_length: length - width,
                left: bytes,
                right: literal(length - width, vec![0; length - width]),
            }
        };
        return Ok((vec![ty], byte_scalar_type(length), result));
    }
    let frame = if length == width {
        arg.clone()
    } else {
        slice(arg.clone(), length, width)
    };
    let result = match ty {
        Bytes32 | Bytes(_) => *frame,
        Bool => Expr::Eq {
            left: cast(
                "UIntRange<2>",
                Box::new(Expr::ByteAt {
                    value: arg,
                    index: 0,
                }),
            ),
            right: Box::new(Expr::Uint {
                maximum: "1".into(),
                value: "1".into(),
            }),
        },
        UInt(_) => *cast(
            token,
            Box::new(Expr::FromBytes {
                ty: "Native".into(),
                length: width,
                value: frame,
            }),
        ),
        Native => Expr::Lets {
            bindings: vec![
                ("frame".into(), *frame),
                (
                    "decoded".into(),
                    Expr::FromBytes32 {
                        ty: token.into(),
                        value: reference("frame"),
                    },
                ),
            ],
            body: Box::new(Expr::AssertThen {
                condition: Box::new(Expr::Eq {
                    left: Box::new(Expr::ToBytes32 {
                        value: reference("decoded"),
                    }),
                    right: reference("frame"),
                }),
                body: reference("decoded"),
            }),
        },
        JubjubScalar => Expr::FromBytes32 {
            ty: token.into(),
            value: frame,
        },
        #[cfg(feature = "zkir-321")]
        Foreign(_) => Expr::ForeignFromBytes {
            ty: token.into(),
            length: width,
            value: frame,
        },
        _ => bail!("unsupported wire decoding kind"),
    };
    Ok((vec![byte_scalar_type(length)], ty, result))
}

fn bytes_operation(
    operation: &str,
    count: usize,
) -> Result<(Vec<ScalarType>, ScalarType, crate::Expr)> {
    if let Some(encoded) = operation.strip_prefix("serialize:") {
        return scalar_wire_operation(true, encoded, count);
    }
    if let Some(encoded) = operation.strip_prefix("deserialize:") {
        return scalar_wire_operation(false, encoded, count);
    }
    use ScalarType::{Bytes32, JubjubPoint, JubjubScalar, Native};
    let argument = |index: usize| {
        Box::new(crate::Expr::Reference {
            name: index.to_string(),
        })
    };
    if let Some(encoded) = operation.strip_prefix("fromBytes:") {
        let fields = encoded.split(':').collect::<Vec<_>>();
        ensure!(
            fields.len() == 2 && count == 1,
            "fromBytes operation encoding"
        );
        let (ty, type_name) = match fields[0] {
            "Native" => (Native, "Native"),
            "JubjubScalar" => (JubjubScalar, "JubjubScalar"),
            _ => bail!("fromBytes requires Native or JubjubScalar"),
        };
        let length = canonical_byte_length(fields[1])?;
        ensure!(
            operation == format!("fromBytes:{type_name}:{length}"),
            "noncanonical fromBytes operation"
        );
        return Ok((
            vec![byte_scalar_type(length)],
            ty,
            crate::Expr::FromBytes {
                ty: type_name.to_owned(),
                length,
                value: argument(0),
            },
        ));
    }
    #[cfg(feature = "zkir-321")]
    if let Some(encoded_type) = operation.strip_prefix("foreignToBytes:") {
        use crate::foreign::ForeignType;
        ensure!(count == 1, "foreignToBytes argument count");
        let ty = ForeignType::parse_source_name(encoded_type)?;
        ensure!(
            operation == format!("foreignToBytes:{}", ty.source_name()),
            "noncanonical foreignToBytes operation"
        );
        return Ok((
            vec![ScalarType::Foreign(ty)],
            byte_scalar_type(ty.byte_len()),
            crate::Expr::ForeignToBytes { value: argument(0) },
        ));
    }
    #[cfg(feature = "zkir-321")]
    if let Some(encoded) = operation.strip_prefix("foreignFromBytes:") {
        use crate::foreign::ForeignType;
        let fields = encoded.split(':').collect::<Vec<_>>();
        ensure!(
            fields.len() == 2 && count == 1,
            "foreignFromBytes operation encoding"
        );
        let ty = ForeignType::parse_source_name(fields[0])?;
        let length = canonical_byte_length(fields[1])?;
        ensure!(
            operation == format!("foreignFromBytes:{}:{length}", ty.source_name()),
            "noncanonical foreignFromBytes operation"
        );
        if ty.role() == crate::foreign::ForeignRole::Point {
            ensure!(
                length == ty.byte_len(),
                "foreign point decoding requires exactly {} bytes",
                ty.byte_len()
            );
        }
        return Ok((
            vec![byte_scalar_type(length)],
            ScalarType::Foreign(ty),
            crate::Expr::ForeignFromBytes {
                ty: ty.source_name().to_owned(),
                length,
                value: argument(0),
            },
        ));
    }
    if let Some(encoded) = operation.strip_prefix("__byteAt:") {
        let (length, index) = match encoded.split_once(':') {
            Some((length, index)) => (
                canonical_byte_length(length)?,
                canonical_byte_length(index)?,
            ),
            None => (32, canonical_byte_length(encoded)?),
        };
        ensure!(count == 1 && index < length, "control byte index");
        return Ok((
            vec![byte_scalar_type(length)],
            ScalarType::parse("UIntRange<256>")?,
            crate::Expr::ByteAt {
                value: argument(0),
                index,
            },
        ));
    }
    if let Some(encoded_length) = operation.strip_prefix("reverseBytes:") {
        let length = canonical_byte_length(encoded_length)?;
        ensure!(count == 1, "reverseBytes argument count");
        let ty = byte_scalar_type(length);
        return Ok((
            vec![ty.clone()],
            ty,
            crate::Expr::ReverseBytes {
                length,
                value: argument(0),
            },
        ));
    }
    if let Some(encoded_length) = operation.strip_prefix("sha256:") {
        let length = canonical_byte_length(encoded_length)?;
        ensure!(count == 1, "sha256 argument count");
        return Ok((
            vec![byte_scalar_type(length)],
            Bytes32,
            crate::Expr::Sha256 {
                length,
                value: argument(0),
            },
        ));
    }
    if let Some(encoded_length) = operation.strip_prefix("sha512:") {
        let length = canonical_byte_length(encoded_length)?;
        ensure!(count == 1, "sha512 argument count");
        return Ok((
            vec![byte_scalar_type(length)],
            byte_scalar_type(64),
            crate::Expr::Sha512 {
                length,
                value: argument(0),
            },
        ));
    }
    #[cfg(feature = "zkir-321")]
    if operation == "keccak256:Secp256k1Point" {
        ensure!(count == 1, "typed Keccak point argument count");
        let point = crate::foreign::ForeignType::parse_source_name("Secp256k1Point")?;
        return Ok((
            vec![ScalarType::Foreign(point)],
            Bytes32,
            crate::Expr::Keccak256Secp256k1Point { value: argument(0) },
        ));
    }
    if let Some(encoded_length) = operation.strip_prefix("keccak256:") {
        let length = canonical_byte_length(encoded_length)?;
        ensure!(count == 1, "keccak256 argument count");
        return Ok((
            vec![byte_scalar_type(length)],
            byte_scalar_type(32),
            crate::Expr::Keccak256 {
                length,
                value: argument(0),
            },
        ));
    }
    if let Some(encoded_bounds) = operation.strip_prefix("sliceBytes:") {
        let fields = encoded_bounds.split(':').collect::<Vec<_>>();
        ensure!(fields.len() == 3, "sliceBytes operation encoding");
        let length = canonical_byte_length(fields[0])?;
        let start = canonical_byte_length(fields[1])?;
        let end = canonical_byte_length(fields[2])?;
        ensure!(
            count == 1 && start <= end && end <= length,
            "sliceBytes bounds"
        );
        return Ok((
            vec![byte_scalar_type(length)],
            byte_scalar_type(end - start),
            crate::Expr::SliceBytes {
                length,
                value: argument(0),
                start,
                end,
            },
        ));
    }
    if let Some(encoded_lengths) = operation.strip_prefix("concatBytes:") {
        let fields = encoded_lengths.split(':').collect::<Vec<_>>();
        ensure!(fields.len() == 2, "concatBytes operation encoding");
        let left_length = canonical_byte_length(fields[0])?;
        let right_length = canonical_byte_length(fields[1])?;
        let length = left_length
            .checked_add(right_length)
            .filter(|length| *length <= scalars::MAX_BYTES_LENGTH)
            .ok_or_else(|| anyhow!("concatBytes result exceeds the source byte limit"))?;
        ensure!(count == 2, "concatBytes argument count");
        return Ok((
            vec![
                byte_scalar_type(left_length),
                byte_scalar_type(right_length),
            ],
            byte_scalar_type(length),
            crate::Expr::ConcatBytes {
                left_length,
                right_length,
                left: argument(0),
                right: argument(1),
            },
        ));
    }
    Ok(match operation {
        "persistentHash32" => (
            vec![Bytes32],
            Bytes32,
            crate::Expr::PersistentHash32 { value: argument(0) },
        ),
        "persistentHashVector32" => {
            ensure!((1..=32).contains(&count), "control byte hash vector size");
            (
                vec![Bytes32; count],
                Bytes32,
                crate::Expr::PersistentHashVector32 {
                    values: (0..count).map(|index| *argument(index)).collect(),
                },
            )
        }
        "persistentHashNative" => (
            vec![Native],
            Bytes32,
            crate::Expr::PersistentHashNative { value: argument(0) },
        ),
        "persistentHashNativeVector" => {
            ensure!((1..=32).contains(&count), "control field hash vector size");
            (
                vec![Native; count],
                Bytes32,
                crate::Expr::PersistentHashNativeVector {
                    values: (0..count).map(|index| *argument(index)).collect(),
                },
            )
        }
        "transientHashNativeVector" => {
            return curve_operation(&format!("transientHashNativeVector:{count}"));
        }
        "persistentHashPoint" => (
            vec![JubjubPoint],
            Bytes32,
            crate::Expr::PersistentHashNativeVector {
                values: vec![
                    crate::Expr::JubjubCoordinate {
                        point: argument(0),
                        index: 0,
                    },
                    crate::Expr::JubjubCoordinate {
                        point: argument(0),
                        index: 1,
                    },
                ],
            },
        ),
        "reverseBytes32" => (
            vec![Bytes32],
            Bytes32,
            crate::Expr::ReverseBytes32 { value: argument(0) },
        ),
        "nativeToBytes32" | "jubjubScalarToBytes32" | "jubjubPointToBytes32" => (
            vec![match operation {
                "nativeToBytes32" => Native,
                "jubjubScalarToBytes32" => ScalarType::JubjubScalar,
                _ => JubjubPoint,
            }],
            Bytes32,
            crate::Expr::ToBytes32 { value: argument(0) },
        ),
        "degradeToNative" => (
            vec![Bytes32],
            Native,
            crate::Expr::BytesField {
                value: argument(0),
                index: 1,
            },
        ),
        _ => bail!("unsupported control byte operation '{operation}'"),
    })
}

fn evaluate_operation(
    (parameters, result, expression): (Vec<ScalarType>, ScalarType, crate::Expr),
    values: Vec<Value>,
) -> Result<Value> {
    ensure!(
        values.len() == parameters.len(),
        "control operation argument count"
    );
    if let crate::Expr::TransientHash {
        values: expressions,
    } = &expression
    {
        ensure!(
            result == ScalarType::Native
                && parameters == vec![ScalarType::Native; values.len()]
                && expressions.len() == values.len()
                && values.len() <= crate::MAX_TRANSIENT_HASH_FIELDS,
            "control transientHashNativeVector type"
        );
        let fields = values
            .iter()
            .map(crate::Value::field)
            .collect::<Result<Vec<_>>>()?;
        return Ok(Value::Native(transient_crypto::hash::transient_hash(
            &fields,
        )));
    }
    let env = values
        .into_iter()
        .zip(parameters)
        .enumerate()
        .map(|(index, (value, ty))| Ok((index.to_string(), value.cast(&ty)?)))
        .collect::<Result<BTreeMap<_, _>>>()?;
    let value = crate::evaluate(&expression, &env)?;
    ensure!(
        value.scalar_type() == result,
        "control operation result type"
    );
    Ok(value)
}
fn text<'a>(v: &'a Json, key: &str) -> Result<&'a str> {
    v.get(key)
        .and_then(Json::as_str)
        .ok_or_else(|| anyhow!("invalid control descriptor"))
}
fn field<'a>(v: &'a Json, key: &str) -> Result<&'a Json> {
    v.get(key)
        .ok_or_else(|| anyhow!("invalid control descriptor"))
}
fn list<'a>(v: &'a Json, key: &str) -> Result<&'a Vec<Json>> {
    field(v, key)?
        .as_array()
        .ok_or_else(|| anyhow!("invalid control descriptor"))
}
fn shape(v: &Json, required: &[&str], span: bool) -> Result<()> {
    let object = v
        .as_object()
        .ok_or_else(|| anyhow!("invalid control descriptor"))?;
    ensure!(
        required.iter().all(|k| object.contains_key(*k))
            && object
                .keys()
                .all(|k| required.contains(&k.as_str()) || (span && k == "span")),
        "invalid control fields"
    );
    if let Some(s) = object.get("span") {
        ensure!(s.is_object(), "invalid control span");
    }
    Ok(())
}
fn assertion_shape(v: &Json) -> Result<Option<String>> {
    let object = v
        .as_object()
        .ok_or_else(|| anyhow!("invalid control descriptor"))?;
    ensure!(
        ["tag", "condition"].iter().all(|key| object.contains_key(*key))
            && object
                .keys()
                .all(|key| ["tag", "condition", "message", "span"].contains(&key.as_str())),
        "invalid control fields"
    );
    if let Some(span) = object.get("span") {
        ensure!(span.is_object(), "invalid control span");
    }
    object
        .get("message")
        .map(|message| {
            message
                .as_str()
                .map(str::to_owned)
                .ok_or_else(|| anyhow!("invalid control assertion message"))
        })
        .transpose()
}
fn name(value: &str) -> Result<String> {
    ensure!(
        !value.is_empty() && value.len() <= 1024 && !value.chars().any(char::is_control),
        "invalid control identifier"
    );
    Ok(value.into())
}
fn host_identifier(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && value
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b"_-.:".contains(&b))
}
fn host_key(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && value
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b"_-/.:".contains(&b))
        && !value.starts_with('/')
        && !value.ends_with('/')
        && value
            .split('/')
            .all(|s| !s.is_empty() && s != "." && s != "..")
}

#[derive(Clone)]
struct Expr {
    ty: Type,
    kind: ExprKind,
}
#[derive(Clone, Copy)]
enum BooleanOperation {
    And,
    Or,
    Xor,
}
#[derive(Clone)]
enum ExprKind {
    Unit,
    Literal(Value),
    Ref(String),
    Binary(String, Arc<Expr>, Arc<Expr>),
    BoolAnd(Arc<Expr>, Arc<Expr>),
    BoolOr(Arc<Expr>, Arc<Expr>),
    BoolXor(Arc<Expr>, Arc<Expr>),
    Eq(Type, Arc<Expr>, Arc<Expr>),
    Cast(Arc<Expr>),
    Disclose(Arc<Expr>),
    Select(Arc<Expr>, Arc<Expr>, Arc<Expr>),
    If(Arc<Expr>, Arc<Expr>, Arc<Expr>),
    And(Arc<Expr>, Arc<Expr>),
    Or(Arc<Expr>, Arc<Expr>),
    Hash(String, Arc<Expr>, Arc<Expr>),
    Curve(String, Vec<Arc<Expr>>),
    #[cfg(feature = "zkir-321")]
    ForeignEncodedField(Arc<Expr>, usize),
    Bytes(String, Vec<Arc<Expr>>),
    FabDigest {
        parameters: Vec<ScalarType>,
        result: ScalarType,
        expression: crate::Expr,
        argument_kinds: Vec<FabDigestArgumentKind>,
        arguments: Vec<Arc<Expr>>,
    },
    Call(String, Vec<Arc<Expr>>),
    Witness(String),
    WitnessCall {
        name: String,
        site: String,
        arguments: Vec<Arc<Expr>>,
    },
    Composite {
        token: String,
        leaves: Vec<Arc<Expr>>,
    },
    Project {
        value: Arc<Expr>,
        projection: witness::Projection,
    },
    Index {
        value: Arc<Expr>,
        index: Arc<Expr>,
    },
}
#[derive(Clone)]
enum Stmt {
    Bind(String, Type, Arc<Expr>),
    Evaluate(Arc<Expr>),
    Assert(Arc<Expr>, Option<String>),
    Return(Option<Arc<Expr>>),
    If(Arc<Expr>, Arc<Block>, Arc<Block>),
    Stage(String, String, String, Arc<Expr>),
}
#[derive(Clone, Default)]
struct Block {
    statements: Vec<Stmt>,
    must_return: bool,
    may_return: bool,
}
#[derive(Clone)]
struct Signature {
    parameters: Vec<(String, Type)>,
    result: Type,
}
struct Function {
    signature: Signature,
    body: Arc<Block>,
    calls: Vec<String>,
    witness_sites: BTreeSet<String>,
    nodes: usize,
    depth: usize,
}
struct Plan {
    schema_version: u32,
    mode: Option<String>,
    functions: BTreeMap<String, Arc<Function>>,
    inputs: Vec<(String, String, bool)>,
    witnesses: BTreeMap<String, String>,
    signatures: BTreeMap<String, witness::WitnessSignature>,
    registry: witness::Registry,
    binding: Option<Json>,
    native_relation: Option<Json>,
    bound_calls: Vec<Json>,
    ledger_calls: BTreeMap<usize, LedgerCall>,
    native_input_types: BTreeMap<String, String>,
    entry: String,
    name: String,
    max_steps: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LedgerCall {
    pub ordinal: usize,
    pub operation_end: usize,
    pub read: Option<String>,
}
struct Parser<'a> {
    signatures: &'a BTreeMap<String, Signature>,
    witnesses: &'a BTreeMap<String, String>,
    typed_witnesses: &'a BTreeMap<String, witness::WitnessSignature>,
    registry: &'a witness::Registry,
    registered_schemas: &'a BTreeMap<String, Json>,
    fab_digest_layouts: BTreeMap<String, (Json, Vec<crate::aggregates::FabHashField>)>,
    aggregate_bytes_lengths: BTreeMap<String, Option<usize>>,
    schema_version: u32,
    nodes: usize,
    deepest: usize,
    calls: Vec<String>,
    witness_sites: BTreeSet<String>,
}
impl Parser<'_> {
    fn tick(&mut self, depth: usize) -> Result<()> {
        self.nodes += 1;
        self.deepest = self.deepest.max(depth);
        ensure!(
            self.nodes <= MAX_NODES && depth <= MAX_DEPTH,
            "control source resource limit"
        );
        Ok(())
    }

    fn fab_digest_layout(
        &mut self,
        token: &str,
    ) -> Result<(Json, Vec<crate::aggregates::FabHashField>)> {
        if let Some(layout) = self.fab_digest_layouts.get(token) {
            return Ok(layout.clone());
        }
        let schema_json = self
            .registered_schemas
            .get(token)
            .cloned()
            .ok_or_else(|| anyhow!("unknown control aggregate type"))?;
        let schema_bytes = serde_json::to_vec(&schema_json)?;
        let schema = crate::aggregates::Schema::from_json(&schema_bytes)?;
        let fields = schema.fab_hash_nested_fields(crate::aggregates::MAX_FAB_OPERANDS)?;
        let layout = (schema_json, fields);
        self.fab_digest_layouts
            .insert(token.to_owned(), layout.clone());
        Ok(layout)
    }

    fn aggregate_bytes_length(&mut self, token: &str) -> Result<Option<usize>> {
        if let Some(length) = self.aggregate_bytes_lengths.get(token) {
            return Ok(*length);
        }
        let schema_json = self
            .registered_schemas
            .get(token)
            .ok_or_else(|| anyhow!("unknown control aggregate type"))?;
        let schema_bytes = serde_json::to_vec(schema_json)?;
        let length = crate::aggregates::Schema::from_json(&schema_bytes)?.root_bytes_length();
        self.aggregate_bytes_lengths
            .insert(token.to_owned(), length);
        Ok(length)
    }

    fn expr(&mut self, v: &Json, env: &BTreeMap<String, Type>, depth: usize) -> Result<Arc<Expr>> {
        self.tick(depth)?;
        let tag = text(v, "tag")?;
        let (ty, kind) = match tag {
            "unit" => {
                shape(v, &["tag"], true)?;
                (Type::Unit, ExprKind::Unit)
            }
            "constant" => {
                shape(v, &["tag", "value"], true)?;
                let x = Value::Native(canonical_field(text(v, "value")?)?);
                (Type::Scalar(x.scalar_type()), ExprKind::Literal(x))
            }
            #[cfg(feature = "zkir-321")]
            "foreignConstant" => {
                ensure!(self.schema_version == 2, "foreign values require v2 plan");
                shape(v, &["tag", "type", "encoding"], true)?;
                let token = text(v, "type")?;
                let ScalarType::Foreign(foreign_type) = ScalarType::parse(token)? else {
                    bail!("foreign constant requires a foreign source type")
                };
                let encoding = list(v, "encoding")?;
                ensure!(
                    encoding.len() == foreign_type.native_type().encoded_len(),
                    "wrong native field count for foreign constant"
                );
                let encoding = encoding
                    .iter()
                    .map(|field| {
                        field.as_str().map(str::to_owned).ok_or_else(|| {
                            anyhow!("foreign encoding fields must be decimal strings")
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;
                let value = crate::evaluate(
                    &crate::Expr::ForeignConstant {
                        ty: token.to_owned(),
                        encoding,
                    },
                    &crate::Environment::new(),
                )?;
                ensure!(
                    value.scalar_type() == ScalarType::Foreign(foreign_type),
                    "foreign constant result type mismatch"
                );
                (
                    Type::Scalar(ScalarType::Foreign(foreign_type)),
                    ExprKind::Literal(value),
                )
            }
            #[cfg(feature = "zkir-321")]
            "foreignEncodedField" => {
                ensure!(self.schema_version == 2, "foreign values require v2 plan");
                shape(v, &["tag", "value", "index"], true)?;
                let value = self.expr(field(v, "value")?, env, depth + 1)?;
                let Type::Scalar(ScalarType::Foreign(foreign_type)) = &value.ty else {
                    bail!("foreign encoded field projection requires a foreign value")
                };
                let index = field(v, "index")?
                    .as_u64()
                    .and_then(|index| usize::try_from(index).ok())
                    .ok_or_else(|| anyhow!("invalid foreign encoded field index"))?;
                ensure!(
                    index < foreign_type.native_type().encoded_len(),
                    "foreign encoded field index out of range"
                );
                (
                    Type::Scalar(ScalarType::Native),
                    ExprKind::ForeignEncodedField(value, index),
                )
            }
            #[cfg(feature = "zkir-321")]
            "foreignUnary" => {
                ensure!(
                    self.schema_version == 2,
                    "foreign operations require v2 plan"
                );
                shape(v, &["tag", "operation", "value"], true)?;
                let operation_name = text(v, "operation")?;
                let operation = crate::foreign::ForeignUnaryOp::parse(operation_name)?;
                let value = self.expr(field(v, "value")?, env, depth + 1)?;
                let Type::Scalar(ScalarType::Foreign(input_type)) = &value.ty else {
                    bail!("foreign unary operation requires a foreign value")
                };
                let input_type = *input_type;
                let output_type = input_type.unary_result(operation)?;
                let canonical = format!(
                    "foreignUnary:{}:{}",
                    operation_name,
                    input_type.source_name()
                );
                let (parameters, result, _) = curve_operation(&canonical)?;
                ensure!(
                    parameters == [ScalarType::Foreign(input_type)]
                        && result == ScalarType::Foreign(output_type),
                    "foreign unary result type mismatch"
                );
                (
                    Type::Scalar(result),
                    ExprKind::Curve(canonical, vec![value]),
                )
            }
            #[cfg(feature = "zkir-321")]
            "foreignBinary" => {
                ensure!(
                    self.schema_version == 2,
                    "foreign operations require v2 plan"
                );
                shape(v, &["tag", "operation", "left", "right"], true)?;
                let operation_name = text(v, "operation")?;
                let operation = crate::foreign::ForeignBinaryOp::parse(operation_name)?;
                let left = self.expr(field(v, "left")?, env, depth + 1)?;
                let right = self.expr(field(v, "right")?, env, depth + 1)?;
                let Type::Scalar(ScalarType::Foreign(left_type)) = &left.ty else {
                    bail!("foreign binary operation requires foreign operands")
                };
                let Type::Scalar(ScalarType::Foreign(right_type)) = &right.ty else {
                    bail!("foreign binary operation requires foreign operands")
                };
                let left_type = *left_type;
                let right_type = *right_type;
                let output_type = left_type.binary_result(operation, right_type)?;
                let canonical = format!(
                    "foreignBinary:{}:{}:{}",
                    operation_name,
                    left_type.source_name(),
                    right_type.source_name()
                );
                let (parameters, result, _) = curve_operation(&canonical)?;
                ensure!(
                    parameters
                        == [
                            ScalarType::Foreign(left_type),
                            ScalarType::Foreign(right_type)
                        ]
                        && result == ScalarType::Foreign(output_type),
                    "foreign binary result type mismatch"
                );
                (
                    Type::Scalar(result),
                    ExprKind::Curve(canonical, vec![left, right]),
                )
            }
            #[cfg(feature = "zkir-321")]
            "foreignToBytes" => {
                ensure!(
                    self.schema_version == 2,
                    "foreign byte conversions require v2 plan"
                );
                shape(v, &["tag", "value"], true)?;
                let value = self.expr(field(v, "value")?, env, depth + 1)?;
                let Type::Scalar(ScalarType::Foreign(foreign_type)) = &value.ty else {
                    bail!("foreignToBytes requires a foreign value")
                };
                let foreign_type = *foreign_type;
                let canonical = format!("foreignToBytes:{}", foreign_type.source_name());
                let (parameters, result, _) = bytes_operation(&canonical, 1)?;
                ensure!(
                    parameters == [ScalarType::Foreign(foreign_type)]
                        && result == byte_scalar_type(foreign_type.byte_len()),
                    "foreignToBytes result type mismatch"
                );
                (
                    Type::Scalar(result),
                    ExprKind::Bytes(canonical, vec![value]),
                )
            }
            "fromBytes" => {
                ensure!(self.schema_version == 2, "byte operations require v2 plan");
                shape(v, &["tag", "type", "length", "value"], true)?;
                let token = text(v, "type")?;
                let length = field(v, "length")?
                    .as_u64()
                    .and_then(|length| usize::try_from(length).ok())
                    .filter(|length| *length <= scalars::MAX_BYTES_LENGTH)
                    .ok_or_else(|| anyhow!("fromBytes byte length"))?;
                let canonical = format!("fromBytes:{token}:{length}");
                let (parameters, result, _) = bytes_operation(&canonical, 1)?;
                let value = self.expr(field(v, "value")?, env, depth + 1)?;
                ensure!(
                    parameters == [byte_scalar_type(length)]
                        && value.ty == Type::Scalar(byte_scalar_type(length)),
                    "fromBytes operand length mismatch"
                );
                (
                    Type::Scalar(result),
                    ExprKind::Bytes(canonical, vec![value]),
                )
            }
            #[cfg(feature = "zkir-321")]
            "foreignFromBytes" => {
                ensure!(
                    self.schema_version == 2,
                    "foreign byte conversions require v2 plan"
                );
                shape(v, &["tag", "type", "length", "value"], true)?;
                let token = text(v, "type")?;
                let ScalarType::Foreign(foreign_type) = ScalarType::parse(token)? else {
                    bail!("foreignFromBytes requires a foreign target type")
                };
                let length = field(v, "length")?
                    .as_u64()
                    .and_then(|length| usize::try_from(length).ok())
                    .filter(|length| *length <= scalars::MAX_BYTES_LENGTH)
                    .ok_or_else(|| anyhow!("foreignFromBytes byte length"))?;
                if foreign_type.role() == crate::foreign::ForeignRole::Point {
                    ensure!(
                        length == foreign_type.byte_len(),
                        "foreign point decoding requires exactly {} bytes",
                        foreign_type.byte_len()
                    );
                }
                let value = self.expr(field(v, "value")?, env, depth + 1)?;
                ensure!(
                    value.ty == Type::Scalar(byte_scalar_type(length)),
                    "foreignFromBytes operand length mismatch"
                );
                let canonical = format!("foreignFromBytes:{}:{length}", foreign_type.source_name());
                let (parameters, result, _) = bytes_operation(&canonical, 1)?;
                ensure!(
                    parameters == [byte_scalar_type(length)]
                        && result == ScalarType::Foreign(foreign_type),
                    "foreignFromBytes result type mismatch"
                );
                (
                    Type::Scalar(result),
                    ExprKind::Bytes(canonical, vec![value]),
                )
            }
            "bool" => {
                shape(v, &["tag", "value"], true)?;
                let x = Value::Bool(
                    field(v, "value")?
                        .as_bool()
                        .ok_or_else(|| anyhow!("invalid control Boolean"))?,
                );
                (Type::Scalar(ScalarType::Bool), ExprKind::Literal(x))
            }
            "uint" => {
                shape(v, &["tag", "maximum", "value"], true)?;
                let x = scalars::unsigned_literal(text(v, "maximum")?, text(v, "value")?)?;
                (Type::Scalar(x.scalar_type()), ExprKind::Literal(x))
            }
            "reference" => {
                shape(v, &["tag", "name"], true)?;
                let n = name(text(v, "name")?)?;
                (
                    env.get(&n)
                        .ok_or_else(|| anyhow!("unbound control reference"))?
                        .clone(),
                    ExprKind::Ref(n),
                )
            }
            "cast" => {
                shape(v, &["tag", "type", "value"], true)?;
                let target = parse_type(text(v, "type")?, self.registry)?;
                let x = self.expr(field(v, "value")?, env, depth + 1)?;
                match (&x.ty, &target) {
                    (Type::Scalar(_), Type::Scalar(_)) => {}
                    (Type::Aggregate(source), Type::Aggregate(destination)) => ensure!(
                        self.registry.can_widen_aggregate(source, destination)?,
                        "unsafe aggregate cast"
                    ),
                    _ => bail!("control cast cannot mix aggregate and scalar types"),
                }
                (target, ExprKind::Cast(x))
            }
            "disclose" => {
                shape(v, &["tag", "value"], true)?;
                let x = self.expr(field(v, "value")?, env, depth + 1)?;
                (x.ty.clone(), ExprKind::Disclose(x))
            }
            "boolAnd" | "boolOr" | "boolXor" => {
                shape(v, &["tag", "left", "right"], true)?;
                let left = self.expr(field(v, "left")?, env, depth + 1)?;
                let right = self.expr(field(v, "right")?, env, depth + 1)?;
                ensure!(
                    left.ty == Type::Scalar(ScalarType::Bool)
                        && right.ty == Type::Scalar(ScalarType::Bool),
                    "control eager Boolean operands require Bool"
                );
                let kind = match tag {
                    "boolAnd" => ExprKind::BoolAnd(left, right),
                    "boolOr" => ExprKind::BoolOr(left, right),
                    _ => ExprKind::BoolXor(left, right),
                };
                (Type::Scalar(ScalarType::Bool), kind)
            }
            "binary" | "eq" | "and" | "or" => {
                if tag == "binary" {
                    shape(v, &["tag", "operation", "left", "right"], true)?;
                } else {
                    shape(v, &["tag", "left", "right"], true)?;
                }
                let a = self.expr(field(v, "left")?, env, depth + 1)?;
                let b = self.expr(field(v, "right")?, env, depth + 1)?;
                match tag {
                    "eq" => {
                        let t = match (&a.ty, &b.ty) {
                            (Type::Scalar(_), Type::Scalar(_)) => join(&a.ty, &b.ty)?,
                            (Type::Aggregate(left), Type::Aggregate(right)) => {
                                ensure!(
                                    left == right,
                                    "control equality requires identical checked aggregate types"
                                );
                                Type::parse(left, &self.registry)?
                            }
                            _ => bail!(
                                "control equality requires scalar or matching aggregate operands"
                            ),
                        };
                        (Type::Scalar(ScalarType::Bool), ExprKind::Eq(t, a, b))
                    }
                    "and" | "or" => {
                        ensure!(
                            a.ty == Type::Scalar(ScalarType::Bool) && b.ty == a.ty,
                            "control Boolean required"
                        );
                        (
                            a.ty.clone(),
                            if tag == "and" {
                                ExprKind::And(a, b)
                            } else {
                                ExprKind::Or(a, b)
                            },
                        )
                    }
                    _ => {
                        let op = text(v, "operation")?;
                        ensure!(
                            ["add", "sub", "mul"].contains(&op),
                            "invalid control arithmetic"
                        );
                        let lt = scalar_type(&a.ty)?;
                        let rt = scalar_type(&b.ty)?;
                        let t = match (lt, rt) {
                            (ScalarType::JubjubScalar | ScalarType::JubjubPoint, _)
                            | (_, ScalarType::JubjubScalar | ScalarType::JubjubPoint) => {
                                bail!("control arithmetic requires numeric scalar operands")
                            }
                            (
                                ScalarType::Bytes32
                                | ScalarType::Bytes(_)
                                | ScalarType::OpaqueBytes
                                | ScalarType::OpaqueString,
                                _,
                            )
                            | (
                                _,
                                ScalarType::Bytes32
                                | ScalarType::Bytes(_)
                                | ScalarType::OpaqueBytes
                                | ScalarType::OpaqueString,
                            ) => {
                                bail!("control byte arithmetic")
                            }
                            #[cfg(feature = "zkir-321")]
                            (ScalarType::Foreign(_), _) | (_, ScalarType::Foreign(_)) => {
                                bail!("control foreign values do not support scalar arithmetic")
                            }
                            (ScalarType::Bool, _) | (_, ScalarType::Bool) => {
                                bail!("control Boolean arithmetic")
                            }
                            (ScalarType::Native, _) | (_, ScalarType::Native) => ScalarType::Native,
                            (ScalarType::UInt(m), ScalarType::UInt(n)) => {
                                let maximum = match op {
                                    "add" => m + n,
                                    "sub" => m.clone(),
                                    _ => m * n,
                                };
                                ensure!(maximum <= max_uint(), "control unsigned bound");
                                ScalarType::UInt(maximum)
                            }
                        };
                        (Type::Scalar(t), ExprKind::Binary(op.into(), a, b))
                    }
                }
            }
            "if" | "select" => {
                shape(v, &["tag", "condition", "yes", "no"], true)?;
                let c = self.expr(field(v, "condition")?, env, depth + 1)?;
                ensure!(
                    c.ty == Type::Scalar(ScalarType::Bool),
                    "control Boolean required"
                );
                let a = self.expr(field(v, "yes")?, env, depth + 1)?;
                let b = self.expr(field(v, "no")?, env, depth + 1)?;
                let t = join(&a.ty, &b.ty)?;
                if tag == "select" {
                    scalar_type(&t)?;
                }
                (
                    t,
                    if tag == "if" {
                        ExprKind::If(c, a, b)
                    } else {
                        ExprKind::Select(c, a, b)
                    },
                )
            }
            "poseidon2" => {
                shape(v, &["tag", "domain", "left", "right"], true)?;
                let d = text(v, "domain")?.to_owned();
                canonical_field(&d)?;
                let a = self.expr(field(v, "left")?, env, depth + 1)?;
                let b = self.expr(field(v, "right")?, env, depth + 1)?;
                ensure!(
                    subtype(&a.ty, &Type::Scalar(ScalarType::Native))
                        && subtype(&b.ty, &Type::Scalar(ScalarType::Native)),
                    "control hash scalar types"
                );
                (Type::Scalar(ScalarType::Native), ExprKind::Hash(d, a, b))
            }
            "transientHash" => {
                shape(v, &["tag", "values"], true)?;
                let values = list(v, "values")?;
                ensure!(
                    values.len() <= crate::MAX_TRANSIENT_HASH_FIELDS,
                    "control transientHashNativeVector field limit"
                );
                let arguments = values
                    .iter()
                    .map(|value| {
                        let value = self.expr(value, env, depth + 1)?;
                        ensure!(
                            value.ty == Type::Scalar(ScalarType::Native),
                            "control transientHashNativeVector argument type"
                        );
                        Ok(value)
                    })
                    .collect::<Result<Vec<_>>>()?;
                (
                    Type::Scalar(ScalarType::Native),
                    ExprKind::Curve(
                        format!("transientHashNativeVector:{}", arguments.len()),
                        arguments,
                    ),
                )
            }
            "curve" => {
                ensure!(self.schema_version == 2, "curve operations require v2 plan");
                shape(v, &["tag", "operation", "arguments"], true)?;
                let operation = text(v, "operation")?;
                let (parameters, result, _) = curve_operation(operation)?;
                let arguments = list(v, "arguments")?;
                ensure!(
                    arguments.len() == parameters.len(),
                    "control curve argument count"
                );
                let arguments = arguments
                    .iter()
                    .zip(parameters)
                    .map(|(argument, expected)| {
                        let argument = self.expr(argument, env, depth + 1)?;
                        ensure!(
                            argument.ty == Type::Scalar(expected),
                            "control curve argument type"
                        );
                        Ok(argument)
                    })
                    .collect::<Result<Vec<_>>>()?;
                (
                    Type::Scalar(result),
                    ExprKind::Curve(operation.to_owned(), arguments),
                )
            }
            "bytes32" => {
                ensure!(self.schema_version == 2, "byte literals require v2 plan");
                shape(v, &["tag", "values"], true)?;
                let bytes = list(v, "values")?;
                ensure!(bytes.len() == 32, "control byte literal length");
                let bytes = bytes
                    .iter()
                    .map(|value| {
                        value
                            .as_u64()
                            .and_then(|value| u8::try_from(value).ok())
                            .ok_or_else(|| anyhow!("control byte literal must contain octets"))
                    })
                    .collect::<Result<Vec<_>>>()?;
                (
                    Type::Scalar(ScalarType::Bytes32),
                    ExprKind::Literal(Value::Bytes(bytes)),
                )
            }
            "bytesLiteral" => {
                ensure!(self.schema_version == 2, "byte literals require v2 plan");
                shape(v, &["tag", "length", "values"], true)?;
                let length = field(v, "length")?
                    .as_u64()
                    .and_then(|length| usize::try_from(length).ok())
                    .filter(|length| *length <= scalars::MAX_BYTES_LENGTH)
                    .ok_or_else(|| anyhow!("control byte literal length"))?;
                let values = list(v, "values")?;
                ensure!(values.len() == length, "control byte literal length");
                let bytes = values
                    .iter()
                    .map(|value| {
                        value
                            .as_u64()
                            .and_then(|value| u8::try_from(value).ok())
                            .ok_or_else(|| anyhow!("control byte literal must contain octets"))
                    })
                    .collect::<Result<Vec<_>>>()?;
                (
                    Type::Scalar(byte_scalar_type(length)),
                    ExprKind::Literal(Value::Bytes(bytes)),
                )
            }
            "byteAt" => {
                ensure!(self.schema_version == 2, "byte projections require v2 plan");
                shape(v, &["tag", "value", "index"], true)?;
                let index = field(v, "index")?
                    .as_u64()
                    .and_then(|index| usize::try_from(index).ok())
                    .ok_or_else(|| anyhow!("control byte index"))?;
                let value = self.expr(field(v, "value")?, env, depth + 1)?;
                let length = scalar_type(&value.ty)?.bytes_length().ok_or_else(|| {
                    anyhow!("control byte projection requires a fixed byte string")
                })?;
                ensure!(
                    index < length,
                    "control byte projection index is outside the byte string"
                );
                let operation = if length == 32 {
                    format!("__byteAt:{index}")
                } else {
                    format!("__byteAt:{length}:{index}")
                };
                (
                    Type::Scalar(ScalarType::parse("UIntRange<256>")?),
                    ExprKind::Bytes(operation, vec![value]),
                )
            }
            "reverseBytes" => {
                ensure!(self.schema_version == 2, "byte operations require v2 plan");
                shape(v, &["tag", "length", "value"], true)?;
                let length = field(v, "length")?
                    .as_u64()
                    .and_then(|length| usize::try_from(length).ok())
                    .filter(|length| *length <= scalars::MAX_BYTES_LENGTH)
                    .ok_or_else(|| anyhow!("control byte length"))?;
                let value = self.expr(field(v, "value")?, env, depth + 1)?;
                ensure!(
                    value.ty == Type::Scalar(byte_scalar_type(length)),
                    "reverseBytes operand length mismatch"
                );
                (
                    Type::Scalar(byte_scalar_type(length)),
                    ExprKind::Bytes(format!("reverseBytes:{length}"), vec![value]),
                )
            }
            "sliceBytes" => {
                ensure!(self.schema_version == 2, "byte operations require v2 plan");
                shape(v, &["tag", "length", "value", "start", "end"], true)?;
                let length = field(v, "length")?
                    .as_u64()
                    .and_then(|length| usize::try_from(length).ok())
                    .filter(|length| *length <= scalars::MAX_BYTES_LENGTH)
                    .ok_or_else(|| anyhow!("control byte length"))?;
                let start = field(v, "start")?
                    .as_u64()
                    .and_then(|start| usize::try_from(start).ok())
                    .ok_or_else(|| anyhow!("control byte slice start"))?;
                let end = field(v, "end")?
                    .as_u64()
                    .and_then(|end| usize::try_from(end).ok())
                    .ok_or_else(|| anyhow!("control byte slice end"))?;
                ensure!(start <= end && end <= length, "control byte slice bounds");
                let value = self.expr(field(v, "value")?, env, depth + 1)?;
                ensure!(
                    value.ty == Type::Scalar(byte_scalar_type(length)),
                    "sliceBytes operand length mismatch"
                );
                (
                    Type::Scalar(byte_scalar_type(end - start)),
                    ExprKind::Bytes(format!("sliceBytes:{length}:{start}:{end}"), vec![value]),
                )
            }
            "concatBytes" => {
                ensure!(self.schema_version == 2, "byte operations require v2 plan");
                shape(
                    v,
                    &["tag", "leftLength", "rightLength", "left", "right"],
                    true,
                )?;
                let left_length = field(v, "leftLength")?
                    .as_u64()
                    .and_then(|length| usize::try_from(length).ok())
                    .filter(|length| *length <= scalars::MAX_BYTES_LENGTH)
                    .ok_or_else(|| anyhow!("control left byte length"))?;
                let right_length = field(v, "rightLength")?
                    .as_u64()
                    .and_then(|length| usize::try_from(length).ok())
                    .filter(|length| *length <= scalars::MAX_BYTES_LENGTH)
                    .ok_or_else(|| anyhow!("control right byte length"))?;
                let length = left_length
                    .checked_add(right_length)
                    .filter(|length| *length <= scalars::MAX_BYTES_LENGTH)
                    .ok_or_else(|| anyhow!("control concatenated byte length"))?;
                let left = self.expr(field(v, "left")?, env, depth + 1)?;
                let right = self.expr(field(v, "right")?, env, depth + 1)?;
                ensure!(
                    left.ty == Type::Scalar(byte_scalar_type(left_length))
                        && right.ty == Type::Scalar(byte_scalar_type(right_length)),
                    "concatBytes operand length mismatch"
                );
                (
                    Type::Scalar(byte_scalar_type(length)),
                    ExprKind::Bytes(
                        format!("concatBytes:{left_length}:{right_length}"),
                        vec![left, right],
                    ),
                )
            }
            "fabDigest" => {
                ensure!(self.schema_version == 2, "FAB digests require v2 plan");
                shape(v, &["tag", "operation", "type", "arguments"], true)?;
                let operation = text(v, "operation")?.to_owned();
                ensure!(
                    matches!(
                        operation.as_str(),
                        "persistentHash" | "sha512" | "keccak256"
                    ),
                    "unsupported control FAB digest operation"
                );
                let token = text(v, "type")?.to_owned();
                ensure!(
                    matches!(parse_type(&token, self.registry)?, Type::Aggregate(_)),
                    "FAB digest requires an aggregate type"
                );
                let (schema, fields) = self.fab_digest_layout(&token)?;
                let raw_arguments = list(v, "arguments")?;
                ensure!(
                    raw_arguments.len() == fields.len(),
                    "control FAB digest argument count"
                );
                let mut arguments = Vec::with_capacity(raw_arguments.len());
                let mut argument_kinds = Vec::with_capacity(raw_arguments.len());
                for (raw, field) in raw_arguments.iter().zip(&fields) {
                    let argument = self.expr(raw, env, depth + 1)?;
                    let argument_kind = match (&argument.ty, field) {
                        (Type::Scalar(actual), _) if *actual == fab_digest_scalar_type(field) => {
                            FabDigestArgumentKind::Scalar
                        }
                        (
                            Type::Aggregate(token),
                            crate::aggregates::FabHashField::Bytes(length),
                        ) => {
                            ensure!(
                                self.aggregate_bytes_length(token)? == Some(*length),
                                "control FAB digest aggregate byte argument type"
                            );
                            FabDigestArgumentKind::AggregateBytes {
                                token: token.clone(),
                                length: *length,
                            }
                        }
                        _ => bail!("control FAB digest argument type"),
                    };
                    argument_kinds.push(argument_kind);
                    arguments.push(argument);
                }
                let (parameters, result, expression) =
                    fab_digest_operation(&operation, schema, &fields)?;
                ensure!(
                    parameters.len() == arguments.len(),
                    "control FAB digest argument count"
                );
                (
                    Type::Scalar(result.clone()),
                    ExprKind::FabDigest {
                        parameters,
                        result,
                        expression,
                        argument_kinds,
                        arguments,
                    },
                )
            }
            "bytes" => {
                ensure!(self.schema_version == 2, "byte operations require v2 plan");
                shape(v, &["tag", "operation", "arguments"], true)?;
                let operation = text(v, "operation")?;
                let arguments = list(v, "arguments")?;
                let (parameters, result, _) = bytes_operation(operation, arguments.len())?;
                ensure!(
                    arguments.len() == parameters.len(),
                    "control byte argument count"
                );
                let arguments = arguments
                    .iter()
                    .zip(parameters)
                    .map(|(argument, expected)| {
                        let argument = self.expr(argument, env, depth + 1)?;
                        ensure!(
                            argument.ty == Type::Scalar(expected),
                            "control byte argument type"
                        );
                        Ok(argument)
                    })
                    .collect::<Result<Vec<_>>>()?;
                (
                    Type::Scalar(result),
                    ExprKind::Bytes(operation.to_owned(), arguments),
                )
            }
            "call" => {
                shape(v, &["tag", "function", "arguments"], true)?;
                let id = text(v, "function")?.to_owned();
                let sig = self
                    .signatures
                    .get(&id)
                    .ok_or_else(|| anyhow!("unknown control function"))?
                    .clone();
                let args = list(v, "arguments")?;
                ensure!(args.len() == sig.parameters.len(), "control call arity");
                let args = args
                    .iter()
                    .map(|x| self.expr(x, env, depth + 1))
                    .collect::<Result<Vec<_>>>()?;
                for (a, (_, t)) in args.iter().zip(&sig.parameters) {
                    ensure!(subtype(&a.ty, t), "control call argument type");
                }
                self.calls.push(id.clone());
                (sig.result, ExprKind::Call(id, args))
            }
            "witness" => {
                ensure!(
                    self.schema_version == 1,
                    "legacy witness expression in v2 plan"
                );
                shape(v, &["tag", "name", "type"], true)?;
                let n = name(text(v, "name")?)?;
                ensure!(host_identifier(&n), "invalid control witness identifier");
                let t = text(v, "type")?;
                ensure!(
                    self.witnesses.get(&n).map(String::as_str) == Some(t),
                    "control witness schema mismatch"
                );
                (Type::Scalar(ScalarType::parse(t)?), ExprKind::Witness(n))
            }
            "witnessCall" => {
                ensure!(
                    self.schema_version == 2,
                    "typed witness call requires v2 plan"
                );
                shape(v, &["tag", "name", "site", "arguments"], true)?;
                let witness_name = text(v, "name")?.to_owned();
                let site = name(text(v, "site")?)?;
                ensure!(host_identifier(&site), "invalid control witness call site");
                ensure!(
                    self.witness_sites.insert(site.clone()),
                    "duplicate control witness site"
                );
                let signature = self
                    .typed_witnesses
                    .get(&witness_name)
                    .ok_or_else(|| anyhow!("unknown typed witness signature"))?
                    .clone();
                let raw = list(v, "arguments")?;
                ensure!(
                    raw.len() == signature.parameters.len(),
                    "control witness arity"
                );
                let arguments = raw
                    .iter()
                    .map(|argument| self.expr(argument, env, depth + 1))
                    .collect::<Result<Vec<_>>>()?;
                for (argument, parameter) in arguments.iter().zip(&signature.parameters) {
                    let expected = parse_type(&parameter.type_token, self.registry)?;
                    ensure!(
                        subtype(&argument.ty, &expected),
                        "control witness argument type"
                    );
                }
                let result = parse_type(&signature.result_type, self.registry)?;
                (
                    result,
                    ExprKind::WitnessCall {
                        name: witness_name,
                        site,
                        arguments,
                    },
                )
            }
            "composite" => {
                ensure!(
                    self.schema_version == 2,
                    "composite expression requires v2 plan"
                );
                shape(v, &["tag", "type", "leaves"], true)?;
                let ty = parse_type(text(v, "type")?, self.registry)?;
                let Type::Aggregate(token) = ty else {
                    bail!("composite expression requires aggregate type")
                };
                let raw = list(v, "leaves")?;
                let leaf_types = self.registry.source_leaf_types(&token)?;
                ensure!(
                    raw.len() == leaf_types.len(),
                    "control aggregate leaf count"
                );
                let leaves = raw
                    .iter()
                    .map(|leaf| self.expr(leaf, env, depth + 1))
                    .collect::<Result<Vec<_>>>()?;
                for (leaf, expected) in leaves.iter().zip(leaf_types) {
                    ensure!(
                        leaf.ty == parse_type(&expected, self.registry)?,
                        "control aggregate leaf type"
                    );
                }
                (
                    Type::Aggregate(token.clone()),
                    ExprKind::Composite { token, leaves },
                )
            }
            "project" => {
                ensure!(
                    self.schema_version == 2,
                    "aggregate projection requires v2 plan"
                );
                shape(v, &["tag", "value", "projection", "type"], true)?;
                let value = self.expr(field(v, "value")?, env, depth + 1)?;
                let Type::Aggregate(token) = &value.ty else {
                    bail!("aggregate projection requires aggregate value")
                };
                let projected = text(v, "type")?.to_owned();
                let projected_type = parse_type(&projected, self.registry)?;
                let raw = field(v, "projection")?;
                let kind = text(raw, "kind")?.to_owned();
                let (index, field_name, variant) = match kind.as_str() {
                    "tupleIndex" | "vectorIndex" | "byteIndex" => {
                        shape(raw, &["kind", "index"], false)?;
                        (Some(canonical_index(text(raw, "index")?)?), None, None)
                    }
                    "field" => {
                        shape(raw, &["kind", "name"], false)?;
                        (None, Some(name(text(raw, "name")?)?), None)
                    }
                    "enumField" => {
                        shape(raw, &["kind", "variant", "name"], false)?;
                        (
                            None,
                            Some(name(text(raw, "name")?)?),
                            Some(name(text(raw, "variant")?)?),
                        )
                    }
                    "enumTag" => {
                        shape(raw, &["kind"], false)?;
                        (None, None, None)
                    }
                    _ => bail!("unsupported aggregate projection"),
                };
                let projection = witness::Projection {
                    kind,
                    index,
                    name: field_name,
                    variant,
                    type_token: projected.clone(),
                };
                let (actual, _) = self.registry.projection_type(token, &projection)?;
                ensure!(actual == projected, "control projection result type");
                (projected_type, ExprKind::Project { value, projection })
            }
            "index" => {
                ensure!(self.schema_version == 2, "aggregate index requires v2 plan");
                shape(v, &["tag", "value", "index", "type"], true)?;
                let value = self.expr(field(v, "value")?, env, depth + 1)?;
                let Type::Aggregate(token) = &value.ty else {
                    bail!("aggregate index requires aggregate value")
                };
                let index = self.expr(field(v, "index")?, env, depth + 1)?;
                ensure!(
                    matches!(
                        scalar_type(&index.ty)?,
                        ScalarType::Native | ScalarType::UInt(_)
                    ),
                    "aggregate index requires Native or UInt"
                );
                let projected = text(v, "type")?.to_owned();
                let projected_type = parse_type(&projected, self.registry)?;
                let actual = self.registry.index_type(token)?;
                ensure!(actual == projected, "control index result type");
                (projected_type, ExprKind::Index { value, index })
            }
            _ => bail!("unsupported control expression"),
        };
        Ok(Arc::new(Expr { ty, kind }))
    }
    fn block(
        &mut self,
        values: &[Json],
        initial: &BTreeMap<String, Type>,
        result: &Type,
        depth: usize,
    ) -> Result<Arc<Block>> {
        let mut env = initial.clone();
        let mut block = Block::default();
        for value in values {
            self.tick(depth)?;
            let tag = text(value, "tag")?;
            let stmt = match tag {
                "bind" => {
                    shape(value, &["tag", "name", "type", "value"], true)?;
                    let n = name(text(value, "name")?)?;
                    ensure!(!env.contains_key(&n), "duplicate control local");
                    let t = parse_type(text(value, "type")?, self.registry)?;
                    let x = self.expr(field(value, "value")?, &env, depth + 1)?;
                    ensure!(subtype(&x.ty, &t), "control binding type");
                    env.insert(n.clone(), t.clone());
                    Stmt::Bind(n, t, x)
                }
                "evaluate" => {
                    shape(value, &["tag", "value"], true)?;
                    Stmt::Evaluate(self.expr(field(value, "value")?, &env, depth + 1)?)
                }
                "assert" => {
                    let message = assertion_shape(value)?;
                    let x = self.expr(field(value, "condition")?, &env, depth + 1)?;
                    ensure!(
                        x.ty == Type::Scalar(ScalarType::Bool),
                        "control assertion requires Boolean"
                    );
                    Stmt::Assert(x, message)
                }
                "return" => {
                    shape(value, &["tag", "value"], true)?;
                    let x = if field(value, "value")?.is_null() {
                        None
                    } else {
                        Some(self.expr(field(value, "value")?, &env, depth + 1)?)
                    };
                    ensure!(
                        subtype(
                            &x.as_ref().map(|x| x.ty.clone()).unwrap_or(Type::Unit),
                            result
                        ),
                        "control return type"
                    );
                    block.must_return = true;
                    block.may_return = true;
                    Stmt::Return(x)
                }
                "if" => {
                    shape(value, &["tag", "condition", "yes", "no"], true)?;
                    let c = self.expr(field(value, "condition")?, &env, depth + 1)?;
                    ensure!(
                        c.ty == Type::Scalar(ScalarType::Bool),
                        "control Boolean required"
                    );
                    let yes = self.block(list(value, "yes")?, &env, result, depth + 1)?;
                    let no = self.block(list(value, "no")?, &env, result, depth + 1)?;
                    block.must_return |= yes.must_return && no.must_return;
                    block.may_return |= yes.may_return || no.may_return;
                    Stmt::If(c, yes, no)
                }
                "stage" => {
                    shape(value, &["tag", "capability", "key", "type", "value"], true)?;
                    let t = text(value, "type")?.to_owned();
                    let target = parse_type(&t, self.registry)?;
                    let x = self.expr(field(value, "value")?, &env, depth + 1)?;
                    ensure!(subtype(&x.ty, &target), "control private stage type");
                    {
                        let cap = text(value, "capability")?;
                        let key = text(value, "key")?;
                        ensure!(
                            host_identifier(cap) && host_key(key),
                            "invalid control stage descriptor"
                        );
                        Stmt::Stage(cap.into(), key.into(), t, x)
                    }
                }
                _ => bail!("unsupported control statement"),
            };
            block.statements.push(stmt);
        }
        Ok(Arc::new(block))
    }
}
fn parse_parameters(v: &Json, registry: &witness::Registry) -> Result<Vec<(String, Type)>> {
    let values = list(v, "parameters")?;
    ensure!(values.len() <= MAX_ARGUMENTS, "control parameter limit");
    let mut names = BTreeSet::new();
    values
        .iter()
        .map(|v| {
            shape(v, &["name", "type"], false)?;
            let n = name(text(v, "name")?)?;
            ensure!(names.insert(n.clone()), "duplicate control parameter");
            let t = parse_type(text(v, "type")?, registry)?;
            Ok((n, t))
        })
        .collect()
}
fn canonical_index(text: &str) -> Result<usize> {
    ensure!(
        !text.is_empty()
            && text.bytes().all(|byte| byte.is_ascii_digit())
            && (text == "0" || !text.starts_with('0')),
        "noncanonical control index"
    );
    text.parse::<usize>()
        .map_err(|_| anyhow!("control index out of range"))
}
fn canonical_u64(text: &str) -> Result<u64> {
    ensure!(
        !text.is_empty()
            && text.bytes().all(|byte| byte.is_ascii_digit())
            && (text == "0" || !text.starts_with('0')),
        "noncanonical control request id"
    );
    text.parse::<u64>()
        .map_err(|_| anyhow!("control request id out of range"))
}
fn witness_signature(v: &Json, registry: &witness::Registry) -> Result<witness::WitnessSignature> {
    shape(
        v,
        &[
            "name",
            "operation",
            "capability",
            "privateKey",
            "parameters",
            "resultType",
        ],
        false,
    )?;
    let signature_name = name(text(v, "name")?)?;
    let operation = text(v, "operation")?.to_owned();
    let capability = text(v, "capability")?.to_owned();
    let private_key = if field(v, "privateKey")?.is_null() {
        None
    } else {
        let key = text(v, "privateKey")?.to_owned();
        ensure!(host_key(&key), "invalid typed witness private key");
        Some(key)
    };
    ensure!(
        host_identifier(&signature_name) && host_identifier(&capability),
        "invalid typed witness identity"
    );
    ensure!(
        host_identifier(&operation) && operation.ends_with(".v1"),
        "invalid typed witness operation"
    );
    ensure!(
        operation != host::STAGE && operation != host::CAS,
        "private state journal operations are reserved for source effects"
    );
    let mut parameter_names = BTreeSet::new();
    let mut parameters = Vec::new();
    for parameter in list(v, "parameters")? {
        shape(parameter, &["name", "type"], false)?;
        let parameter_name = name(text(parameter, "name")?)?;
        ensure!(
            host_identifier(&parameter_name) && parameter_names.insert(parameter_name.clone()),
            "invalid or duplicate typed witness parameter"
        );
        let type_token = text(parameter, "type")?.to_owned();
        parse_type(&type_token, registry)?;
        parameters.push(witness::Parameter {
            name: parameter_name,
            type_token,
        });
    }
    ensure!(
        parameters.len() <= MAX_ARGUMENTS,
        "typed witness parameter limit"
    );
    if operation == host::READ {
        ensure!(
            private_key.is_some() && parameters.is_empty(),
            "private state witness requires a fixed source key"
        );
    } else {
        ensure!(
            private_key.is_none(),
            "private key is restricted to private state reads"
        );
    }
    let result_type = text(v, "resultType")?.to_owned();
    parse_type(&result_type, registry)?;
    Ok(witness::WitnessSignature {
        name: signature_name,
        operation,
        capability,
        private_key,
        parameters,
        result_type,
    })
}
fn raw_preflight(value: &Json) -> Result<()> {
    let mut work = vec![(value, 0usize)];
    let mut nodes = 0usize;
    let mut string_bytes = 0usize;
    while let Some((value, depth)) = work.pop() {
        nodes += 1;
        ensure!(
            nodes <= 131072 && depth <= 256,
            "control JSON resource limit"
        );
        match value {
            Json::Array(values) => {
                ensure!(
                    work.len() + values.len() <= 131072,
                    "control JSON resource limit"
                );
                work.extend(values.iter().map(|v| (v, depth + 1)));
            }
            Json::Object(values) => {
                ensure!(
                    work.len() + values.len() <= 131072,
                    "control JSON resource limit"
                );
                for (key, value) in values {
                    string_bytes = string_bytes.saturating_add(key.len());
                    work.push((value, depth + 1));
                }
            }
            Json::String(s) => string_bytes = string_bytes.saturating_add(s.len()),
            _ => {}
        }
        ensure!(string_bytes <= MAX_BYTES, "control JSON byte limit");
    }
    Ok(())
}

fn matching_native_input_type(declared: &str, semantic: &str) -> bool {
    declared == semantic
        || (declared == "Native"
            && matches!(
                ScalarType::parse(semantic),
                Ok(ScalarType::Bool | ScalarType::UInt(_))
            ))
}

fn native_relation_input_type(semantic: &str) -> Result<Json> {
    #[cfg(feature = "zkir-321")]
    if let ScalarType::Foreign(foreign) = ScalarType::parse(semantic)? {
        return Ok(serde_json::to_value(foreign.native_type())?);
    }
    #[cfg(not(feature = "zkir-321"))]
    let _ = ScalarType::parse(semantic)?;
    Ok(json!("Scalar<BLS12-381>"))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PublicBytesAbi {
    LegacyBytes,
    PackedFields,
}

fn byte_relation_fields(name: &str, length: usize, abi: PublicBytesAbi) -> Vec<(String, u64)> {
    match abi {
        PublicBytesAbi::LegacyBytes => (0..length)
            .map(|index| (format!("{name}_byte_{index}"), 8))
            .collect(),
        PublicBytesAbi::PackedFields if length == 32 => vec![
            (format!("_noctium_bytes32_{name}_high"), 8),
            (format!("_noctium_bytes32_{name}_low31"), 248),
        ],
        PublicBytesAbi::PackedFields => {
            let chunks = length.div_ceil(31);
            (0..chunks)
                .map(|index| {
                    let width = (length - (chunks - 1 - index) * 31).min(31);
                    (format!("_noctium_bytes_{name}_{index}"), (width * 8) as u64)
                })
                .collect()
        }
    }
}

fn public_byte_relation_fields(
    name: &str,
    length: usize,
    relation_names: &BTreeSet<String>,
) -> Result<(PublicBytesAbi, Vec<(String, u64)>)> {
    let packed = byte_relation_fields(name, length, PublicBytesAbi::PackedFields);
    let legacy = byte_relation_fields(name, length, PublicBytesAbi::LegacyBytes);
    let present = |fields: &[(String, u64)]| {
        fields
            .iter()
            .all(|(field, _)| relation_names.contains(field))
    };
    ensure!(
        present(&packed) ^ present(&legacy),
        "native public byte input has an unsupported field shape"
    );
    if present(&packed) {
        Ok((PublicBytesAbi::PackedFields, packed))
    } else {
        Ok((PublicBytesAbi::LegacyBytes, legacy))
    }
}

fn native_relation_input_names(instructions: &[Json]) -> Result<BTreeSet<String>> {
    let mut names = BTreeSet::new();
    for instruction in instructions {
        if matches!(text(instruction, "op")?, "public_input" | "private_input") {
            let input = text(instruction, "output")?
                .strip_prefix("%input_")
                .ok_or_else(|| anyhow!("invalid native input operation"))?;
            ensure!(
                names.insert(input.to_owned()),
                "duplicate native relation input"
            );
        }
    }
    Ok(names)
}

fn public_byte_relation_abis(
    binding: &Json,
    relation: &Json,
) -> Result<BTreeMap<String, PublicBytesAbi>> {
    let relation_names = native_relation_input_names(list(relation, "instructions")?)?;
    let mut abis = BTreeMap::new();
    for input in list(binding, "circuitInputs")? {
        if text(input, "visibility")? != "public" {
            continue;
        }
        let scalar = ScalarType::parse(text(input, "type")?)?;
        if let Some(length) = scalar.bytes_length().filter(|length| *length > 0) {
            let name = text(input, "name")?;
            let (abi, _) = public_byte_relation_fields(name, length, &relation_names)?;
            abis.insert(name.to_owned(), abi);
        }
    }
    Ok(abis)
}

fn validate_relation_inputs(
    relation: &Json,
    circuit_inputs: &BTreeMap<String, (String, String)>,
    input_order: &[(String, String)],
    call_inputs: &[String],
) -> Result<()> {
    let version = field(relation, "version")?;
    ensure!(
        field(version, "major")?.as_u64() == Some(3)
            && field(version, "minor")?.as_u64() == Some(2),
        "invalid native relation version"
    );
    let instructions = list(relation, "instructions")?;
    let relation_input_names = native_relation_input_names(instructions)?;
    let header = if call_inputs.is_empty() {
        Vec::new()
    } else {
        let inputs: Vec<_> = circuit_inputs
            .iter()
            .map(|(name, (ty, visibility))| crate::Input {
                name: name.clone(),
                ty: ty.clone(),
                visibility: visibility.clone(),
            })
            .collect();
        crate::call_input_header(&inputs, call_inputs)?
    };
    crate::validate_call_input_header_json(&header, relation)?;
    ensure!(
        header.iter().all(|(name, _)| {
            name.strip_prefix("%input_")
                .is_some_and(|field| !relation_input_names.contains(field))
        }),
        "native call input collides with a transcript input"
    );
    let mut physical_inputs = BTreeMap::new();
    let mut physical_order = Vec::new();
    let mut byte_constraints = Vec::new();
    for (name, visibility) in input_order {
        let (token, _) = circuit_inputs
            .get(name)
            .ok_or_else(|| anyhow!("unknown native circuit input"))?;
        let scalar = ScalarType::parse(token)?;
        if call_inputs.contains(name) {
            if let Some(length) = scalar.bytes_length() {
                byte_constraints.extend(crate::call_byte_input_fields(name, length));
            }
            continue;
        }
        let names = if scalar == ScalarType::JubjubPoint {
            vec![format!("{name}_x"), format!("{name}_y")]
        } else if let Some(length) = scalar.bytes_length() {
            let fields = if visibility == "public" && length > 0 {
                public_byte_relation_fields(name, length, &relation_input_names)?.1
            } else {
                byte_relation_fields(name, length, PublicBytesAbi::LegacyBytes)
            };
            let names = fields.iter().map(|(field, _)| field.clone()).collect();
            byte_constraints.extend(fields);
            names
        } else {
            vec![name.clone()]
        };
        let native_type = native_relation_input_type(token)?;
        for name in names {
            ensure!(
                physical_inputs
                    .insert(name.clone(), (visibility.clone(), native_type.clone()))
                    .is_none(),
                "colliding native input coordinates"
            );
            physical_order.push((name, visibility.clone()));
        }
    }
    ensure!(physical_inputs.len() <= 4096, "native relation input limit");
    let mut declared = BTreeMap::new();
    let mut declared_order = Vec::new();
    let mut bit_constraints = BTreeMap::<String, Vec<u64>>::new();
    let mut zero_constraints = BTreeSet::new();
    let mut aliases = BTreeMap::<String, String>::new();
    let mut pending_constraints = Vec::new();
    for instruction in instructions {
        let operation = text(instruction, "op")?;
        if matches!(operation, "public_input" | "private_input") {
            let output = text(instruction, "output")?;
            let input_name = output
                .strip_prefix("%input_")
                .ok_or_else(|| anyhow!("invalid native input operation"))?;
            let expected = physical_inputs
                .get(input_name)
                .ok_or_else(|| anyhow!("unknown native relation input"))?;
            let actual_type = field(instruction, "type")?.clone();
            ensure!(
                actual_type == expected.1,
                "native relation input type differs from its typed source"
            );
            let visibility = if operation == "public_input" {
                "public"
            } else {
                "private"
            };
            ensure!(
                declared
                    .insert(input_name.to_owned(), (visibility.to_owned(), actual_type))
                    .is_none(),
                "duplicate native relation input"
            );
            declared_order.push((input_name.to_owned(), visibility.to_owned()));
        } else if operation == "constrain_to_boolean" {
            pending_constraints.push((text(instruction, "val")?.to_owned(), 1));
        } else if operation == "constrain_bits" {
            if let (Some(input), Some(bits)) = (
                instruction.get("val").and_then(Json::as_str),
                instruction.get("bits").and_then(Json::as_u64),
            ) {
                pending_constraints.push((input.to_owned(), bits));
            }
        } else if operation == "constrain_eq" {
            let zero_operand = match (text(instruction, "a")?, text(instruction, "b")?) {
                ("0x00", value) | (value, "0x00") => value,
                _ => continue,
            };
            if let Some(input) = zero_operand.strip_prefix("%input_") {
                zero_constraints.insert(input);
            }
        } else if operation == "cond_select" {
            let selected = match instruction.get("bit").and_then(Json::as_str) {
                Some("0x01") => instruction.get("a").and_then(Json::as_str),
                Some("0x00") => instruction.get("b").and_then(Json::as_str),
                _ => None,
            };
            if let (Some(output), Some(selected)) =
                (instruction.get("output").and_then(Json::as_str), selected)
            {
                aliases.insert(output.to_owned(), selected.to_owned());
            }
        }
    }
    for (mut value, bits) in pending_constraints {
        let mut steps = 0usize;
        while let Some(next) = aliases.get(&value) {
            value = next.clone();
            steps += 1;
            ensure!(steps <= instructions.len(), "cyclic native input alias");
        }
        if let Some(input) = value.strip_prefix("%input_") {
            bit_constraints
                .entry(input.to_owned())
                .or_default()
                .push(bits);
        }
    }
    ensure!(
        declared == physical_inputs,
        "native relation input map differs from witness binding"
    );
    ensure!(
        declared_order == physical_order,
        "native relation input order differs from witness binding"
    );
    for (name, bits) in byte_constraints {
        ensure!(
            bit_constraints
                .get(&name)
                .is_some_and(|values| values.contains(&bits)),
            "native byte input lacks its exact chunk range constraint"
        );
    }
    for (name, (type_token, _)) in circuit_inputs {
        let required_bits = match ScalarType::parse(type_token)? {
            ScalarType::Native => None,
            ScalarType::Bool => Some(1),
            ScalarType::UInt(maximum) if maximum.bits() == 0 => {
                ensure!(
                    zero_constraints.contains(name.as_str()),
                    "native zero-bound input lacks equality to zero"
                );
                None
            }
            ScalarType::UInt(maximum) => Some(maximum.bits()),
            ScalarType::Bytes32
            | ScalarType::Bytes(_)
            | ScalarType::OpaqueBytes
            | ScalarType::OpaqueString => None,
            ScalarType::JubjubScalar | ScalarType::JubjubPoint => None,
            #[cfg(feature = "zkir-321")]
            ScalarType::Foreign(_) => None,
        };
        if let Some(bits) = required_bits {
            ensure!(
                bit_constraints
                    .get(name)
                    .is_some_and(|values| values.contains(&bits)),
                "native relation does not constrain the declared witness input width"
            );
        }
        if matches!(type_token.as_str(), "JubjubScalar" | "JubjubPoint") {
            validate_curve_input_bridge(instructions, name, type_token)?;
        }
    }
    Ok(())
}

fn validate_curve_input_bridge(instructions: &[Json], name: &str, token: &str) -> Result<()> {
    let equal = |a: &str, b: &str| {
        instructions.iter().any(|instruction| {
            instruction["op"] == "constrain_eq"
                && ((instruction["a"] == a && instruction["b"] == b)
                    || (instruction["a"] == b && instruction["b"] == a))
        })
    };
    let input = format!("%input_{name}");
    let valid = if token == "JubjubScalar" {
        instructions.iter().any(|conversion| {
            conversion["op"] == "jubjub_scalar_from_native"
                && conversion["native"] == input
                && conversion["output"].as_str().is_some_and(|scalar| {
                    instructions.iter().any(|encoding| {
                        encoding["op"] == "encode"
                            && encoding["input"] == scalar
                            && encoding["outputs"].as_array().is_some_and(|outputs| {
                                outputs.len() == 1
                                    && outputs[0]
                                        .as_str()
                                        .is_some_and(|value| equal(&input, value))
                            })
                    })
                })
        })
    } else {
        let x = format!("{input}_x");
        let y = format!("{input}_y");
        instructions.iter().any(|conversion| {
            conversion["op"] == "from_coordinates"
                && conversion["inputs"] == json!([x, y])
                && conversion["output"].as_str().is_some_and(|point| {
                    instructions.iter().any(|projection| {
                        projection["op"] == "into_coordinates"
                            && projection["point"] == point
                            && projection["outputs"].as_array().is_some_and(|outputs| {
                                outputs.len() == 2
                                    && outputs[0].as_str().is_some_and(|value| equal(&x, value))
                                    && outputs[1].as_str().is_some_and(|value| equal(&y, value))
                            })
                    })
                })
        })
    };
    ensure!(valid, "native curve input lacks canonical roundtrip bridge");
    Ok(())
}

fn native_binding_version(binding: &Json) -> Result<u32> {
    field(binding, "schemaVersion")?
        .as_u64()
        .and_then(|version| u32::try_from(version).ok())
        .ok_or_else(|| anyhow!("invalid native witness binding version"))
}

fn guard_references(
    value: &Json,
    scope: &mut Vec<String>,
    references: &mut BTreeSet<String>,
) -> Result<()> {
    match value {
        Json::Object(object) if object.get("tag").and_then(Json::as_str) == Some("reference") => {
            let reference = text(value, "name")?.to_owned();
            if !scope.iter().rev().any(|name| name == &reference) {
                references.insert(reference);
            }
        }
        Json::Object(object) if object.get("tag").and_then(Json::as_str) == Some("let") => {
            guard_references(field(value, "value")?, scope, references)?;
            scope.push(text(value, "name")?.to_owned());
            guard_references(field(value, "body")?, scope, references)?;
            scope.pop();
        }
        Json::Object(object) if object.get("tag").and_then(Json::as_str) == Some("lets") => {
            let outer = scope.len();
            for binding in list(value, "bindings")? {
                let Some([name, initializer]) = binding.as_array().map(Vec::as_slice) else {
                    bail!("invalid native witness guard binding");
                };
                guard_references(initializer, scope, references)?;
                let name = name
                    .as_str()
                    .ok_or_else(|| anyhow!("invalid native witness guard binding name"))?;
                scope.push(name.to_owned());
            }
            let result = guard_references(field(value, "body")?, scope, references);
            scope.truncate(outer);
            result?;
        }
        Json::Object(object) => {
            for child in object.values() {
                guard_references(child, scope, references)?;
            }
        }
        Json::Array(values) => {
            for child in values {
                guard_references(child, scope, references)?;
            }
        }
        Json::Null | Json::Bool(_) | Json::Number(_) | Json::String(_) => {}
    }
    Ok(())
}

#[cfg(test)]
#[test]
fn grouped_guard_bindings_only_scope_later_expressions() -> Result<()> {
    let reference = |name: &str| json!({"tag": "reference", "name": name});
    let guard = json!({
        "tag": "lets",
        "bindings": [
            ["first", reference("input")],
            ["second", reference("first")],
            ["third", reference("later")],
            ["later", reference("second")]
        ],
        "body": reference("third")
    });
    let mut references = BTreeSet::new();
    guard_references(&guard, &mut Vec::new(), &mut references)?;
    assert_eq!(references, BTreeSet::from(["input".into(), "later".into()]));
    Ok(())
}

fn guard_is_bool(
    expression: &crate::Expr,
    input_types: &BTreeMap<String, String>,
    locals: &mut Vec<(String, bool)>,
) -> Result<bool> {
    use crate::Expr;
    Ok(match expression {
        Expr::Bool { .. } => true,
        Expr::Reference { name } => locals
            .iter()
            .rev()
            .find(|(local, _)| local == name)
            .map(|(_, is_bool)| *is_bool)
            .or_else(|| {
                input_types
                    .get(name)
                    .map(|ty| ScalarType::parse(ty).is_ok_and(|ty| ty == ScalarType::Bool))
            })
            .unwrap_or(false),
        Expr::Eq { .. } => true,
        Expr::BoolAnd { left, right }
        | Expr::BoolOr { left, right }
        | Expr::BoolXor { left, right } => {
            guard_is_bool(left, input_types, locals)? && guard_is_bool(right, input_types, locals)?
        }
        Expr::Cast { ty, .. } => ScalarType::parse(ty)? == ScalarType::Bool,
        Expr::Let { name, value, body } => {
            let is_bool = guard_is_bool(value, input_types, locals)?;
            locals.push((name.clone(), is_bool));
            let result = guard_is_bool(body, input_types, locals)?;
            locals.pop();
            result
        }
        Expr::Lets { bindings, body } => {
            let old_len = locals.len();
            for (name, value) in bindings {
                let is_bool = guard_is_bool(value, input_types, locals)?;
                locals.push((name.clone(), is_bool));
            }
            let result = guard_is_bool(body, input_types, locals)?;
            locals.truncate(old_len);
            result
        }
        Expr::AssertThen { condition, body } => {
            guard_is_bool(condition, input_types, locals)?
                && guard_is_bool(body, input_types, locals)?
        }
        Expr::Select { condition, yes, no } => {
            guard_is_bool(condition, input_types, locals)?
                && guard_is_bool(yes, input_types, locals)?
                && guard_is_bool(no, input_types, locals)?
        }
        _ => false,
    })
}

fn native_leaf(input_types: &BTreeMap<String, String>, name: &str, value: Json) -> Result<Json> {
    let input_type = input_types
        .get(name)
        .ok_or_else(|| anyhow!("unknown native circuit input"))?;
    if input_type == "Native" {
        match value {
            Json::Bool(value) => Ok(Json::String(if value { "1" } else { "0" }.into())),
            Json::String(_) => Ok(value),
            _ => bail!("native circuit input is not a canonical field value"),
        }
    } else {
        Ok(value)
    }
}

fn evaluate_native_guard(
    call: &Json,
    input_types: &BTreeMap<String, String>,
    circuit_values: &BTreeMap<String, Json>,
) -> Result<bool> {
    let guard = field(call, "guard")?;
    let expression: crate::Expr = serde_json::from_value(guard.clone())
        .map_err(|_| anyhow!("invalid native witness guard"))?;
    let mut references = BTreeSet::new();
    guard_references(guard, &mut Vec::new(), &mut references)?;
    let environment = references
        .into_iter()
        .map(|name| {
            let value = circuit_values
                .get(&name)
                .ok_or_else(|| anyhow!("native witness guard input is unavailable"))?;
            let ty = input_types
                .get(&name)
                .ok_or_else(|| anyhow!("unknown native witness guard input"))?;
            Ok((name, input_value(ty, value)?))
        })
        .collect::<Result<crate::Environment>>()?;
    crate::evaluate(&expression, &environment)?.boolean()
}

fn validate_native_binding(
    binding: &Json,
    plan_name: &str,
    entry: &str,
    signatures: &BTreeMap<String, witness::WitnessSignature>,
    signature_jsons: &[Json],
    type_declarations: &[Json],
    source_inputs: &[(String, String, bool)],
    functions: &BTreeMap<String, Arc<Function>>,
    registry: &witness::Registry,
) -> Result<Vec<Json>> {
    let has_ledger_inputs = binding.get("ledgerInputs").is_some();
    let has_ledger_calls = binding.get("ledgerCalls").is_some();
    let call_inputs = crate::call_input_names(binding)?;
    let binding_version = native_binding_version(binding)?;
    ensure!(
        binding_version == 1 || binding_version == 2,
        "unsupported native witness binding version"
    );
    let mut fields = vec![
        "schemaVersion",
        "kind",
        "circuitName",
        "sourceExport",
        "target",
        "types",
        "inputBindings",
        "nativeRelation",
        "circuitInputs",
        "circuitOutputs",
        "signatures",
        "calls",
    ];
    if has_ledger_inputs {
        fields.push("ledgerInputs");
    }
    if has_ledger_calls {
        fields.push("ledgerCalls");
    }
    if binding.get("callInputs").is_some() {
        fields.push("callInputs");
    }
    shape(binding, &fields, false)?;
    ensure!(
        text(binding, "kind")? == "typed-witness-bindings"
            && text(binding, "sourceExport")? == plan_name,
        "invalid native witness binding identity"
    );
    name(text(binding, "circuitName")?)?;
    ensure!(
        field(binding, "nativeRelation")?.is_object(),
        "invalid native relation binding"
    );
    ensure!(
        field(binding, "signatures")? == &Json::Array(signature_jsons.to_vec()),
        "native witness signature mismatch"
    );
    ensure!(
        field(binding, "types")? == &Json::Array(type_declarations.to_vec()),
        "native witness aggregate type mismatch"
    );
    let target_kind = text(field(binding, "target")?, "kind")?;
    match target_kind {
        "standalone" => shape(field(binding, "target")?, &["kind"], false)?,
        "entrypoint" => {
            let target = field(binding, "target")?;
            shape(
                target,
                &[
                    "kind",
                    "contractName",
                    "entrypoint",
                    "nativeCircuitFile",
                    "targetProfile",
                ],
                false,
            )?;
            for key in [
                "contractName",
                "entrypoint",
                "nativeCircuitFile",
                "targetProfile",
            ] {
                ensure!(
                    host_identifier(text(target, key)?),
                    "invalid native target identity"
                );
            }
        }
        _ => bail!("invalid native target identity"),
    }
    ensure!(
        target_kind != "standalone" || !has_ledger_inputs,
        "standalone native witness binding cannot declare ledger inputs"
    );
    ensure!(
        target_kind == "entrypoint" || call_inputs.is_empty(),
        "standalone native witness binding cannot declare call inputs"
    );

    let mut circuit_inputs = BTreeMap::new();
    let mut relation_input_order = Vec::new();
    for input in list(binding, "circuitInputs")? {
        shape(input, &["name", "type", "visibility"], false)?;
        let input_name = name(text(input, "name")?)?;
        let input_type = text(input, "type")?.to_owned();
        scalar_type(&parse_type(&input_type, registry)?)?;
        let visibility = text(input, "visibility")?;
        ensure!(
            ["public", "private"].contains(&visibility)
                && circuit_inputs
                    .insert(input_name.clone(), (input_type, visibility.to_owned()))
                    .is_none(),
            "invalid or duplicate native circuit input"
        );
        relation_input_order.push((input_name, visibility.to_owned()));
    }
    ensure!(circuit_inputs.len() <= 4096, "native circuit input limit");
    let ledger_input_descriptors: &[Json] = match binding.get("ledgerInputs") {
        Some(value) => value
            .as_array()
            .map(Vec::as_slice)
            .ok_or_else(|| anyhow!("invalid native ledger input list"))?,
        None => &[],
    };
    ensure!(
        circuit_inputs
            .len()
            .checked_add(ledger_input_descriptors.len())
            .is_some_and(|count| count <= 4096),
        "native relation input limit"
    );
    let mut ledger_inputs = BTreeMap::<String, (String, String)>::new();
    for input in ledger_input_descriptors {
        shape(input, &["name", "type", "visibility"], false)?;
        let input_name = name(text(input, "name")?)?;
        let input_type = text(input, "type")?.to_owned();
        let scalar = ScalarType::parse(&input_type)?;
        ensure!(
            supported_ledger_read_type(&scalar),
            "unsupported native ledger input type"
        );
        let visibility = text(input, "visibility")?;
        ensure!(
            visibility == "public",
            "native ledger inputs must be public"
        );
        ensure!(
            ledger_inputs
                .insert(input_name.clone(), (input_type, visibility.to_owned()))
                .is_none(),
            "duplicate native ledger input"
        );
        relation_input_order.push((input_name, visibility.to_owned()));
    }
    ensure!(
        circuit_inputs
            .len()
            .checked_add(ledger_inputs.len())
            .is_some_and(|count| count <= 4096),
        "native relation input limit"
    );
    let mut output_names = BTreeSet::new();
    for output in list(binding, "circuitOutputs")? {
        shape(output, &["name", "type"], false)?;
        let output_name = name(text(output, "name")?)?;
        scalar_type(&parse_type(text(output, "type")?, registry)?)?;
        ensure!(
            output_names.insert(output_name),
            "duplicate native circuit output"
        );
    }

    let calls = list(binding, "calls")?;
    ensure!(
        calls.len() <= MAX_NODES,
        "native witness call binding limit"
    );
    let mut expected_inputs = BTreeMap::<String, (String, String)>::new();
    let guard_input_types = circuit_inputs
        .iter()
        .map(|(name, (ty, _))| (name.clone(), ty.clone()))
        .collect::<BTreeMap<_, _>>();
    let mut source_input_names = BTreeSet::new();
    let mut private_parameters = BTreeSet::new();
    let input_bindings = list(binding, "inputBindings")?;
    ensure!(
        input_bindings.len() == source_inputs.len(),
        "native source input binding count"
    );
    for ((source_name, source_type, is_private), input_binding) in
        source_inputs.iter().zip(input_bindings)
    {
        shape(input_binding, &["name", "type", "inputs"], false)?;
        ensure!(
            text(input_binding, "name")? == source_name
                && text(input_binding, "type")? == source_type,
            "native source input binding mismatch"
        );
        let expected_leaf_types = registry.leaf_types(source_type)?;
        let bound_names = list(input_binding, "inputs")?;
        ensure!(
            bound_names.len() == expected_leaf_types.len(),
            "native source input leaf count"
        );
        for (input_name, leaf_type) in bound_names.iter().zip(expected_leaf_types) {
            let input_name = input_name
                .as_str()
                .ok_or_else(|| anyhow!("invalid native source input binding"))?;
            let visibility = if *is_private { "private" } else { "public" };
            ensure!(
                expected_inputs
                    .insert(
                        input_name.to_owned(),
                        (leaf_type.clone(), visibility.to_owned())
                    )
                    .is_none(),
                "duplicate native source input leaf"
            );
            source_input_names.insert(input_name.to_owned());
            let Some((actual_type, visibility)) = circuit_inputs.get(input_name) else {
                bail!("unknown native source circuit input")
            };
            ensure!(
                matching_native_input_type(actual_type, &leaf_type)
                    && visibility == if *is_private { "private" } else { "public" },
                "native source leaf does not match its circuit input"
            );
        }
        if !call_inputs.is_empty() && *is_private {
            if ScalarType::parse(source_type).is_ok()
                && bound_names.len() == 1
                && bound_names[0].as_str() == Some(source_name)
            {
                private_parameters.insert(source_name.as_str());
            } else if matches!(parse_type(source_type, registry)?, Type::Aggregate(_)) {
                let members: Vec<_> = bound_names.iter().filter_map(Json::as_str).collect();
                if call_inputs
                    .iter()
                    .any(|input| members.contains(&input.as_str()))
                {
                    let start = call_inputs
                        .iter()
                        .position(|input| Some(input.as_str()) == members.first().copied());
                    ensure!(
                        start
                            .and_then(|start| call_inputs.get(start..start + members.len()))
                            .is_some_and(|fields| {
                                fields
                                    .iter()
                                    .map(String::as_str)
                                    .eq(members.iter().copied())
                            }),
                        "native aggregate call input must commit all leaves in layout order"
                    );
                    private_parameters.extend(members);
                }
            }
        }
    }
    ensure!(
        call_inputs
            .iter()
            .all(|name| private_parameters.contains(name.as_str())),
        "native call inputs must come from private source parameters"
    );
    let mut witness_slot_ordinals = BTreeMap::new();
    for (ordinal, call) in calls.iter().enumerate() {
        if binding_version == 2 {
            shape(
                call,
                &[
                    "ordinal",
                    "site",
                    "path",
                    "name",
                    "resultType",
                    "inputs",
                    "guard",
                ],
                false,
            )?;
        } else {
            shape(
                call,
                &["ordinal", "site", "path", "name", "resultType", "inputs"],
                false,
            )?;
        }
        ensure!(
            canonical_index(text(call, "ordinal")?)? == ordinal,
            "native witness call ordinal mismatch"
        );
        let site = text(call, "site")?;
        let call_name = text(call, "name")?;
        let signature = signatures
            .get(call_name)
            .ok_or_else(|| anyhow!("unknown bound witness signature"))?;
        ensure!(
            host_identifier(site) && text(call, "resultType")? == signature.result_type,
            "native witness call signature mismatch"
        );
        let path = list(call, "path")?;
        ensure!(
            !path.is_empty() && path.len() <= 64,
            "invalid native witness call path"
        );
        let path = path
            .iter()
            .map(Json::as_str)
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| anyhow!("invalid native witness call path"))?;
        ensure!(
            path.first() == Some(&entry),
            "native witness path entry mismatch"
        );
        for id in &path {
            ensure!(
                functions.contains_key(*id),
                "unknown native witness path function"
            );
        }
        for pair in path.windows(2) {
            ensure!(
                functions[pair[0]]
                    .calls
                    .iter()
                    .any(|child| child == pair[1]),
                "invalid native witness call path"
            );
        }
        ensure!(
            functions[*path.last().unwrap()]
                .witness_sites
                .contains(site),
            "native witness call site mismatch"
        );
        let result_type = parse_type(&signature.result_type, registry)?;
        let leaf_types = match result_type {
            Type::Unit => vec![],
            Type::Scalar(_) => vec![signature.result_type.clone()],
            Type::Aggregate(ref token) => registry.leaf_types(token)?,
        };
        let inputs = list(call, "inputs")?;
        ensure!(
            inputs.len() == leaf_types.len(),
            "native witness input binding arity"
        );
        for (input, leaf_type) in inputs.iter().zip(leaf_types) {
            let input = input
                .as_str()
                .ok_or_else(|| anyhow!("invalid native witness input binding"))?;
            ensure!(
                expected_inputs
                    .insert(input.to_owned(), (leaf_type.clone(), "private".into()))
                    .is_none(),
                "duplicate native witness leaf binding"
            );
            witness_slot_ordinals.insert(input.to_owned(), ordinal);
            let Some((actual_type, visibility)) = circuit_inputs.get(input) else {
                bail!("unknown native witness circuit input")
            };
            ensure!(
                matching_native_input_type(actual_type, &leaf_type) && visibility == "private",
                "native witness leaf is not a matching private circuit input"
            );
        }
        if binding_version == 2 {
            let guard = field(call, "guard")?;
            ensure!(guard.is_object(), "invalid native witness guard");
            let expression: crate::Expr = serde_json::from_value(guard.clone())
                .map_err(|_| anyhow!("invalid native witness guard"))?;
            let mut references = BTreeSet::new();
            guard_references(guard, &mut Vec::new(), &mut references)?;
            for reference in &references {
                ensure!(
                    source_input_names.contains(reference)
                        || witness_slot_ordinals
                            .get(reference)
                            .is_some_and(|slot_ordinal| *slot_ordinal < ordinal),
                    "native witness guard references an unavailable input"
                );
            }
            ensure!(
                guard_is_bool(&expression, &guard_input_types, &mut Vec::new())?,
                "native witness guard must be Bool"
            );
        }
    }
    for (id, function) in functions {
        for site in &function.witness_sites {
            ensure!(
                calls.iter().any(|call| {
                    text(call, "site").ok() == Some(site.as_str())
                        && list(call, "path")
                            .ok()
                            .and_then(|path| path.last())
                            .and_then(Json::as_str)
                            == Some(id.as_str())
                }),
                "unbound native witness call site"
            );
        }
    }
    ensure!(
        expected_inputs.len() == circuit_inputs.len()
            && expected_inputs
                .iter()
                .all(|(name, (semantic_type, visibility))| {
                    circuit_inputs
                        .get(name)
                        .is_some_and(|(declared_type, declared_visibility)| {
                            matching_native_input_type(declared_type, semantic_type)
                                && declared_visibility == visibility
                        })
                }),
        "unbound native circuit input"
    );
    let mut relation_inputs = expected_inputs;
    for (input_name, (input_type, visibility)) in ledger_inputs {
        ensure!(
            !source_inputs
                .iter()
                .any(|(source_name, _, _)| source_name == &input_name)
                && relation_inputs
                    .insert(input_name, (input_type, visibility))
                    .is_none(),
            "native ledger input collides with source or witness input"
        );
    }
    validate_relation_inputs(
        field(binding, "nativeRelation")?,
        &relation_inputs,
        &relation_input_order,
        &call_inputs,
    )?;
    Ok(calls.to_vec())
}

fn validate_native_ledger_calls(
    binding: &Json,
    target_kind: &str,
    signatures: &BTreeMap<String, witness::WitnessSignature>,
    calls: &[Json],
    registry: &witness::Registry,
) -> Result<BTreeMap<usize, LedgerCall>> {
    let Some(rows) = binding.get("ledgerCalls") else {
        ensure!(
            calls.iter().all(|call| {
                text(call, "name")
                    .ok()
                    .and_then(|name| signatures.get(name))
                    .is_none_or(|signature| signature.capability != "noctium.ledger")
            }),
            "native ledger witness call has no ledger binding"
        );
        return Ok(BTreeMap::new());
    };
    ensure!(
        native_binding_version(binding)? == 2 && target_kind == "entrypoint",
        "native ledger calls require a bound entrypoint"
    );
    let rows = rows
        .as_array()
        .ok_or_else(|| anyhow!("invalid native ledger call list"))?;
    ensure!(rows.len() <= MAX_WITNESSES, "native ledger call limit");
    let mut result = BTreeMap::new();
    let mut previous_ordinal = None;
    let mut previous_end = 0usize;
    for row in rows {
        shape(row, &["ordinal", "operationEnd", "read"], false)?;
        let ordinal = canonical_index(text(row, "ordinal")?)?;
        let operation_end = field(row, "operationEnd")?
            .as_u64()
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| anyhow!("invalid native ledger operation boundary"))?;
        let read = match field(row, "read")? {
            Json::Null => None,
            Json::String(value) => Some(name(value)?),
            _ => bail!("invalid native ledger read name"),
        };
        ensure!(
            previous_ordinal.is_none_or(|previous| previous < ordinal)
                && operation_end > previous_end
                && ordinal < calls.len()
                && operation_end > 0,
            "native ledger call order or boundary mismatch"
        );
        previous_ordinal = Some(ordinal);
        previous_end = operation_end;
        let call = &calls[ordinal];
        let signature = signatures
            .get(text(call, "name")?)
            .ok_or_else(|| anyhow!("unknown native ledger witness signature"))?;
        ensure!(
            signature.capability == "noctium.ledger" && signature.private_key.is_none(),
            "invalid native ledger witness authority"
        );
        let output_slots = list(call, "inputs")?;
        match (signature.operation.as_str(), read.as_ref()) {
            ("noctium.ledger.read.v1", Some(_)) => {
                let ty = parse_type(&signature.result_type, registry)?;
                ensure!(
                    matches!(ty, Type::Scalar(_))
                        && output_slots.len() == 1
                        && signature.parameters.len() <= 1,
                    "invalid native ledger read binding"
                );
            }
            ("noctium.ledger.write.v1", None) => ensure!(
                signature.result_type == "Unit"
                    && output_slots.is_empty()
                    && (1..=2).contains(&signature.parameters.len()),
                "invalid native ledger write binding"
            ),
            _ => bail!("native ledger call kind does not match its binding"),
        }
        ensure!(
            result
                .insert(
                    ordinal,
                    LedgerCall {
                        ordinal,
                        operation_end,
                        read,
                    },
                )
                .is_none(),
            "duplicate native ledger call ordinal"
        );
    }
    for (ordinal, call) in calls.iter().enumerate() {
        let signature = signatures
            .get(text(call, "name")?)
            .ok_or_else(|| anyhow!("unknown native witness signature"))?;
        ensure!(
            (signature.capability == "noctium.ledger") == result.contains_key(&ordinal),
            "native ledger call binding is incomplete"
        );
    }
    Ok(result)
}

fn expression_references(value: &Json, expected: &str) -> bool {
    match value {
        Json::Array(values) => values
            .iter()
            .any(|value| expression_references(value, expected)),
        Json::Object(values) => {
            (values.get("tag").and_then(Json::as_str) == Some("reference")
                && values.get("name").and_then(Json::as_str) == Some(expected))
                || values
                    .values()
                    .any(|value| expression_references(value, expected))
        }
        _ => false,
    }
}

fn unwrap_guarded_operation(mut operation: &Json) -> &Json {
    while operation.get("op").and_then(Json::as_str) == Some("guarded") {
        let Some(inner) = operation.get("operation") else {
            break;
        };
        operation = inner;
    }
    operation
}

fn typed_scalar_field_count(ty: &ScalarType) -> Option<usize> {
    match ty {
        ScalarType::JubjubScalar => Some(1),
        ScalarType::JubjubPoint => Some(2),
        #[cfg(feature = "zkir-321")]
        ScalarType::Foreign(ty) => Some(ty.native_type().encoded_len()),
        _ => None,
    }
}

fn expected_point_projection_bindings(name: &str) -> Vec<(String, String)> {
    (0..2)
        .map(|index| {
            (
                format!("_noctium_jubjub_read_{name}_{index}"),
                "Native".to_owned(),
            )
        })
        .collect()
}

fn checked_impact_projections(read: &Json, expected: &[(String, String)]) -> Result<Vec<Json>> {
    let object = read
        .as_object()
        .ok_or_else(|| anyhow!("invalid Impact projected read"))?;
    ensure!(
        object.contains_key("name")
            && object.contains_key("type")
            && object.contains_key("projections")
            && !object.contains_key("components")
            && !object.contains_key("schema")
            && object
                .keys()
                .all(|key| { ["name", "type", "guard", "projections"].contains(&key.as_str()) }),
        "invalid Impact projected read"
    );
    let projections = read
        .get("projections")
        .and_then(Json::as_array)
        .ok_or_else(|| anyhow!("invalid Impact read projections"))?;
    ensure!(
        projections.len() == expected.len(),
        "Impact read projection count mismatch"
    );
    let mut result = Vec::with_capacity(expected.len());
    for (projection, (expected_name, expected_type)) in projections.iter().zip(expected) {
        shape(projection, &["name", "type"], false)?;
        ensure!(
            text(projection, "name")? == expected_name
                && text(projection, "type")? == expected_type,
            "Impact read projection order or type mismatch"
        );
        result.push(json!({
            "name": expected_name,
            "type": expected_type,
            "visibility": "public"
        }));
    }
    Ok(result)
}

fn impact_ledger_read_inputs(read: &Json) -> Result<Vec<Json>> {
    let read_name = name(text(read, "name")?)?;
    let read_type = text(read, "type")?;
    match ScalarType::parse(read_type)? {
        scalar @ (ScalarType::Bytes32 | ScalarType::Bytes(_)) => {
            let length = scalar
                .bytes_length()
                .expect("byte scalar type has a checked length");
            let expected = crate::byte_projection_bindings(&read_name, length)?;
            checked_impact_projections(read, &expected)
        }
        ScalarType::JubjubPoint => {
            let expected = expected_point_projection_bindings(&read_name);
            checked_impact_projections(read, &expected)
        }
        _ => {
            ensure!(
                read.get("projections").is_none()
                    && read.get("components").is_none()
                    && read.get("schema").is_none(),
                "native scalar ledger read has unexpected projections"
            );
            let mut names = BTreeSet::new();
            let mut expected = Vec::new();
            append_impact_ledger_input(read, true, 0, &mut names, &mut expected)?;
            Ok(expected)
        }
    }
}

fn public_source_read_prologue_len(impact_plan: &Json) -> Result<usize> {
    let inputs = list(field(impact_plan, "circuit")?, "inputs")?;
    let reads = list(impact_plan, "reads")?;
    let mut count = 0usize;
    for input in inputs {
        shape(input, &["name", "type", "visibility"], false)?;
        if text(input, "visibility")? != "public" {
            continue;
        }
        let input_name = text(input, "name")?;
        let input_type = text(input, "type")?;
        let scalar = ScalarType::parse(input_type)?;
        let width = match scalar {
            ScalarType::Bytes32 => {
                let first = reads
                    .get(count)
                    .ok_or_else(|| anyhow!("Impact plan is missing its public input prologue"))?;
                let packed = matches_public_input_prologue(
                    std::slice::from_ref(first),
                    &[(input_name.to_owned(), input_type.to_owned())],
                );
                let legacy = matches_public_input_prologue(
                    std::slice::from_ref(first),
                    &[(
                        format!("_noctium_bytes_{input_name}_0"),
                        "UIntRange<256>".to_owned(),
                    )],
                );
                ensure!(
                    packed ^ legacy,
                    "Impact plan public input prologue mismatch"
                );
                if packed { 1 } else { 32 }
            }
            ScalarType::Bytes(length) => length,
            ScalarType::JubjubScalar => 1,
            ScalarType::JubjubPoint => 2,
            #[cfg(feature = "zkir-321")]
            ScalarType::Foreign(ty) => ty.native_type().encoded_len(),
            _ => 1,
        };
        count = count
            .checked_add(width)
            .ok_or_else(|| anyhow!("Impact public input prologue overflow"))?;
        ensure!(
            count <= reads.len(),
            "Impact plan is missing its public input prologue"
        );
    }
    Ok(count)
}

fn validate_native_ledger_boundaries(binding: &Json, impact_plan: &Json) -> Result<()> {
    let Some(rows) = binding.get("ledgerCalls") else {
        return Ok(());
    };
    let operations = list(impact_plan, "operations")?;
    let reads = list(impact_plan, "reads")?;
    let source_input_names = list(field(impact_plan, "circuit")?, "inputs")?
        .iter()
        .map(|input| Ok(text(input, "name")?.to_owned()))
        .collect::<Result<BTreeSet<_>>>()?;
    let ledger_inputs = match binding.get("ledgerInputs") {
        Some(value) => value
            .as_array()
            .map(Vec::as_slice)
            .ok_or_else(|| anyhow!("invalid native ledger input list"))?,
        None => &[],
    };
    for row in rows
        .as_array()
        .ok_or_else(|| anyhow!("invalid native ledger call list"))?
    {
        let end = field(row, "operationEnd")?
            .as_u64()
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| anyhow!("invalid native ledger operation boundary"))?;
        ensure!(
            end <= operations.len(),
            "native ledger operation boundary exceeds plan"
        );
        let operation = unwrap_guarded_operation(
            operations
                .get(end - 1)
                .ok_or_else(|| anyhow!("native ledger operation boundary is empty"))?,
        );
        match field(row, "read")? {
            Json::String(read) => {
                let read_matches = reads
                    .iter()
                    .enumerate()
                    .filter(|(_, descriptor)| {
                        descriptor.get("name").and_then(Json::as_str) == Some(read.as_str())
                    })
                    .collect::<Vec<_>>();
                ensure!(
                    read_matches.len() == 1,
                    "native ledger read is absent or duplicated in selected plan"
                );
                let (read_index, read_descriptor) = read_matches[0];
                let ordinal = canonical_index(text(row, "ordinal")?)?;
                let call = list(binding, "calls")?
                    .get(ordinal)
                    .ok_or_else(|| anyhow!("native ledger call ordinal is unknown"))?;
                let signature_name = text(call, "name")?;
                let signature = list(binding, "signatures")?
                    .iter()
                    .find(|signature| {
                        signature.get("name").and_then(Json::as_str) == Some(signature_name)
                    })
                    .ok_or_else(|| anyhow!("native ledger signature is absent"))?;
                let signature_result = text(signature, "resultType")?;
                let result_scalar = ScalarType::parse(signature_result)?;
                let operation_kind = operation.get("op").and_then(Json::as_str);
                let operation_reads_root = match (&result_scalar, operation_kind) {
                    (ScalarType::JubjubScalar | ScalarType::JubjubPoint, Some("popeqFields")) => {
                        field(operation, "schema")?.as_str() == Some(signature_result)
                            && typed_scalar_field_count(&result_scalar).is_some_and(|count| {
                                operation
                                    .get("expressions")
                                    .and_then(Json::as_array)
                                    .is_some_and(|expressions| {
                                        expressions.len() == count
                                            && expressions.iter().all(|expression| {
                                                expression_references(expression, read)
                                            })
                                    })
                            })
                    }
                    #[cfg(feature = "zkir-321")]
                    (ScalarType::Foreign(_), Some("popeqFields")) => {
                        field(operation, "schema")?.as_str() == Some(signature_result)
                            && typed_scalar_field_count(&result_scalar).is_some_and(|count| {
                                operation
                                    .get("expressions")
                                    .and_then(Json::as_array)
                                    .is_some_and(|expressions| {
                                        expressions.len() == count
                                            && expressions.iter().all(|expression| {
                                                expression_references(expression, read)
                                            })
                                    })
                            })
                    }
                    (ScalarType::JubjubScalar | ScalarType::JubjubPoint, Some("popeq")) => false,
                    #[cfg(feature = "zkir-321")]
                    (ScalarType::Foreign(_), Some("popeq")) => false,
                    (_, Some("popeq")) => operation
                        .get("expression")
                        .is_some_and(|expression| expression_references(expression, read)),
                    _ => false,
                };
                let ledger_read_inputs = impact_ledger_read_inputs(read_descriptor)?;
                ensure!(
                    !source_input_names.contains(read)
                        && read_index >= public_source_read_prologue_len(impact_plan)?
                        && read_descriptor.get("components").is_none()
                        && read_descriptor.get("schema").is_none()
                        && read_descriptor.get("type") == signature.get("resultType")
                        && operation_reads_root
                        && ledger_read_inputs.iter().all(|expected| {
                            ledger_inputs.iter().any(|actual| actual == expected)
                        }),
                    "native ledger read does not match its selected typed state read"
                );
            }
            Json::Null => ensure!(
                operation.get("op").and_then(Json::as_str) == Some("insert"),
                "native ledger write boundary does not end at a write"
            ),
            _ => bail!("invalid native ledger read name"),
        }
    }
    Ok(())
}

impl Plan {
    fn parse(v: &Json, expected_binding_sha256: Option<&str>) -> Result<Self> {
        raw_preflight(v)?;
        ensure!(
            serde_json::to_vec(v)?.len() <= MAX_BYTES,
            "control plan byte limit"
        );
        let schema_version = field(v, "schemaVersion")?
            .as_u64()
            .and_then(|value| u32::try_from(value).ok())
            .ok_or_else(|| anyhow!("invalid control schema version"))?;
        match schema_version {
            1 => {
                shape(
                    v,
                    &[
                        "schemaVersion",
                        "kind",
                        "name",
                        "inputs",
                        "witnesses",
                        "functions",
                        "entry",
                        "limits",
                    ],
                    false,
                )?;
                ensure!(
                    expected_binding_sha256.is_none(),
                    "unexpected witness binding digest"
                );
            }
            2 => shape(
                v,
                &[
                    "schemaVersion",
                    "kind",
                    "name",
                    "types",
                    "mode",
                    "binding",
                    "inputs",
                    "witnesses",
                    "functions",
                    "entry",
                    "limits",
                ],
                false,
            )?,
            _ => bail!("unsupported control schema"),
        }
        ensure!(
            text(v, "kind")? == "host-control",
            "unsupported control schema"
        );

        let mut registry = witness::Registry::default();
        let type_declarations = if schema_version == 2 {
            list(v, "types")?.clone()
        } else {
            Vec::new()
        };
        if schema_version == 2 {
            ensure!(
                type_declarations.len() <= 256,
                "control aggregate type limit"
            );
            let mut type_names = BTreeSet::new();
            for declaration in &type_declarations {
                shape(declaration, &["id", "schema"], false)?;
                let id = name(text(declaration, "id")?)?;
                ensure!(
                    host_identifier(&id) && type_names.insert(id.clone()),
                    "invalid or duplicate aggregate type token"
                );
                let bytes = serde_json::to_vec(field(declaration, "schema")?)?;
                registry.register_json(&format!("Aggregate:{id}"), &bytes)?;
            }
        }
        let registered_schemas = registry
            .declarations()?
            .into_iter()
            .map(|declaration| {
                Ok((
                    text(&declaration, "id")?.to_owned(),
                    field(&declaration, "schema")?.clone(),
                ))
            })
            .collect::<Result<BTreeMap<_, _>>>()?;
        shape(field(v, "limits")?, &["maxSteps"], false)?;
        let max_steps = field(field(v, "limits")?, "maxSteps")?
            .as_u64()
            .ok_or_else(|| anyhow!("invalid control fuel"))?;
        ensure!(
            max_steps > 0 && max_steps <= MAX_STEPS as u64,
            "control execution policy limit"
        );
        let mut inputs = Vec::new();
        let mut names = BTreeSet::new();
        ensure!(
            list(v, "inputs")?.len() <= MAX_ARGUMENTS,
            "control input limit"
        );
        for input in list(v, "inputs")? {
            shape(input, &["name", "type", "visibility"], true)?;
            let n = name(text(input, "name")?)?;
            ensure!(names.insert(n.clone()), "duplicate control input");
            let t = text(input, "type")?.to_owned();
            parse_type(&t, &registry)?;
            let visibility = text(input, "visibility")?;
            ensure!(
                ["public", "private"].contains(&visibility),
                "invalid control visibility"
            );
            inputs.push((n, t, visibility == "private"));
        }
        let mut witnesses = BTreeMap::new();
        let mut typed_witnesses = BTreeMap::new();
        let mut signature_jsons = Vec::new();
        ensure!(
            list(v, "witnesses")?.len() <= MAX_WITNESSES,
            "control witness limit"
        );
        if schema_version == 1 {
            for witness in list(v, "witnesses")? {
                shape(witness, &["name", "type"], true)?;
                let n = name(text(witness, "name")?)?;
                ensure!(host_identifier(&n), "invalid control witness identifier");
                let t = text(witness, "type")?.to_owned();
                ScalarType::parse(&t)?;
                ensure!(
                    witnesses.insert(n, t).is_none(),
                    "duplicate control witness"
                );
            }
        } else {
            for signature_json in list(v, "witnesses")? {
                let signature = witness_signature(signature_json, &registry)?;
                ensure!(
                    typed_witnesses
                        .insert(signature.name.clone(), signature)
                        .is_none(),
                    "duplicate typed witness signature"
                );
                signature_jsons.push(signature_json.clone());
            }
        }
        let raw = list(v, "functions")?;
        ensure!(
            !raw.is_empty() && raw.len() <= MAX_FUNCTIONS,
            "control function limit"
        );
        let mut signatures = BTreeMap::new();
        for f in raw {
            shape(f, &["id", "name", "parameters", "resultType", "body"], true)?;
            let id = name(text(f, "id")?)?;
            name(text(f, "name")?)?;
            let signature = Signature {
                parameters: parse_parameters(f, &registry)?,
                result: parse_type(text(f, "resultType")?, &registry)?,
            };
            ensure!(
                signatures.insert(id, signature).is_none(),
                "duplicate control function"
            );
        }
        let entry = text(v, "entry")?.to_owned();
        let sig = signatures
            .get(&entry)
            .ok_or_else(|| anyhow!("unknown control entry"))?;
        ensure!(sig.parameters.len() == inputs.len(), "control entry arity");
        for ((_, t, _), (_, expected)) in inputs.iter().zip(&sig.parameters) {
            ensure!(
                subtype(&parse_type(t, &registry)?, expected),
                "control entry type"
            );
        }
        let mut functions = BTreeMap::new();
        let mut total = 0;
        for f in raw {
            let id = text(f, "id")?.to_owned();
            let signature = signatures[&id].clone();
            let env = signature.parameters.iter().cloned().collect();
            let mut parser = Parser {
                signatures: &signatures,
                witnesses: &witnesses,
                typed_witnesses: &typed_witnesses,
                registry: &registry,
                registered_schemas: &registered_schemas,
                fab_digest_layouts: BTreeMap::new(),
                aggregate_bytes_lengths: BTreeMap::new(),
                schema_version,
                nodes: 0,
                deepest: 0,
                calls: vec![],
                witness_sites: BTreeSet::new(),
            };
            let body = parser.block(list(f, "body")?, &env, &signature.result, 1)?;
            ensure!(
                signature.result == Type::Unit || body.must_return,
                "control fall-through returns unit"
            );
            total += parser.nodes;
            ensure!(total <= MAX_NODES, "control source node limit");
            let calls = parser.calls;
            let witness_sites = parser.witness_sites;
            let nodes = parser.nodes;
            let deepest = parser.deepest;
            functions.insert(
                id,
                Arc::new(Function {
                    nodes: 3 * (nodes + signature.parameters.len() + 2),
                    depth: 3 * (body.statements.len() + deepest + signature.parameters.len() + 2),
                    signature,
                    body,
                    calls,
                    witness_sites,
                }),
            );
        }
        fn graph(
            id: &str,
            functions: &BTreeMap<String, Arc<Function>>,
            stack: &mut BTreeSet<String>,
            cache: &mut BTreeMap<String, (usize, usize, usize)>,
            visits: &mut usize,
        ) -> Result<(usize, usize, usize)> {
            *visits += 1;
            ensure!(*visits <= 65536, "control call analysis limit");
            ensure!(!stack.contains(id), "recursive control call");
            if let Some(c) = cache.get(id) {
                ensure!(stack.len() + c.2 <= 64, "control call depth limit");
                return Ok(*c);
            };
            ensure!(stack.len() < 64, "control call depth limit");
            stack.insert(id.into());
            let f = &functions[id];
            let mut nodes = f.nodes;
            let mut depth = 0;
            let mut calls = 0;
            for child in &f.calls {
                let (n, d, c) = graph(child, functions, stack, cache, visits)?;
                nodes = nodes.saturating_add(n).min(65537);
                depth = depth.max(d);
                calls = calls.max(c);
                ensure!(nodes <= 65536, "control expanded node limit");
            }
            stack.remove(id);
            depth = f.depth.saturating_add(depth).min(257);
            ensure!(depth <= 256 && calls < 64, "control expanded depth limit");
            let answer = (nodes, depth, calls + 1);
            cache.insert(id.into(), answer);
            Ok(answer)
        }
        graph(
            &entry,
            &functions,
            &mut BTreeSet::new(),
            &mut BTreeMap::new(),
            &mut 0,
        )?;
        let mode = if schema_version == 2 {
            Some(text(v, "mode")?.to_owned())
        } else {
            None
        };
        let (binding, native_relation, bound_calls, ledger_calls, native_input_types) =
            match (schema_version, mode.as_deref()) {
                (1, None) => (None, None, vec![], BTreeMap::new(), BTreeMap::new()),
                (2, Some("host")) => {
                    ensure!(
                        field(v, "binding")?.is_null() && expected_binding_sha256.is_none(),
                        "host control plan must not carry native bindings"
                    );
                    (None, None, vec![], BTreeMap::new(), BTreeMap::new())
                }
                (2, Some("native")) => {
                    let raw_binding = field(v, "binding")?
                        .as_str()
                        .ok_or_else(|| anyhow!("native control plan requires witness binding"))?;
                    let expected = expected_binding_sha256
                        .ok_or_else(|| anyhow!("trusted witness binding digest required"))?;
                    ensure!(
                        expected.len() == 64
                            && expected
                                .bytes()
                                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
                        "invalid trusted witness binding digest"
                    );
                    let actual = hex::encode(Sha256::digest(raw_binding.as_bytes()));
                    ensure!(actual == expected, "witness binding digest mismatch");
                    let parsed: Json = serde_json::from_str(raw_binding)
                        .map_err(|_| anyhow!("invalid native witness binding"))?;
                    raw_preflight(&parsed)?;
                    ensure!(
                        serde_json::to_vec(&parsed)?.len() <= MAX_BYTES,
                        "native witness binding byte limit"
                    );
                    let bound_calls = validate_native_binding(
                        &parsed,
                        text(v, "name")?,
                        &entry,
                        &typed_witnesses,
                        &signature_jsons,
                        &type_declarations,
                        &inputs,
                        &functions,
                        &registry,
                    )?;
                    let target_kind = text(field(&parsed, "target")?, "kind")?;
                    let ledger_calls = validate_native_ledger_calls(
                        &parsed,
                        target_kind,
                        &typed_witnesses,
                        &bound_calls,
                        &registry,
                    )?;
                    let native_input_types = list(&parsed, "circuitInputs")?
                        .iter()
                        .map(|input| {
                            Ok((
                                text(input, "name")?.to_owned(),
                                text(input, "type")?.to_owned(),
                            ))
                        })
                        .collect::<Result<BTreeMap<_, _>>>()?;
                    let native_relation = field(&parsed, "nativeRelation")?.clone();
                    (
                        Some(parsed),
                        Some(native_relation),
                        bound_calls,
                        ledger_calls,
                        native_input_types,
                    )
                }
                _ => bail!("invalid control execution mode"),
            };
        Ok(Self {
            schema_version,
            mode,
            functions,
            inputs,
            witnesses,
            signatures: typed_witnesses,
            registry,
            binding,
            native_relation,
            bound_calls,
            ledger_calls,
            native_input_types,
            entry,
            name: name(text(v, "name")?)?,
            max_steps: max_steps as usize,
        })
    }
}

fn append_impact_ledger_input(
    input: &Json,
    impact_read: bool,
    source_input_count: usize,
    names: &mut BTreeSet<String>,
    expected: &mut Vec<Json>,
) -> Result<()> {
    if impact_read {
        let object = input
            .as_object()
            .ok_or_else(|| anyhow!("invalid Impact ledger read"))?;
        ensure!(
            object.contains_key("name")
                && object.contains_key("type")
                && !object.contains_key("schema")
                && object.keys().all(|key| {
                    ["name", "type", "guard", "components", "projections"].contains(&key.as_str())
                }),
            "invalid Impact ledger read"
        );
    } else {
        shape(input, &["name", "type"], false)?;
    }
    let input_name = name(text(input, "name")?)?;
    let input_type = text(input, "type")?;
    let scalar = ScalarType::parse(input_type)?;
    let permitted_type = if impact_read {
        supported_ledger_read_type(&scalar)
    } else {
        supported_ledger_field_type(&scalar)
    };
    ensure!(permitted_type, "unsupported Impact ledger input type");
    ensure!(
        names.insert(input_name.clone()),
        "duplicate Impact ledger input"
    );
    ensure!(
        source_input_count
            .checked_add(expected.len())
            .is_some_and(|count| count < 4096),
        "native relation input limit"
    );
    expected.push(json!({
        "name": input_name,
        "type": input_type,
        "visibility": "public"
    }));
    Ok(())
}

fn matches_public_input_prologue(reads: &[Json], expected: &[(String, String)]) -> bool {
    expected.len() <= reads.len()
        && expected.iter().zip(reads).all(|((name, ty), read)| {
            read.get("components").is_none()
                && read.get("projections").is_none()
                && read.get("guard").is_none()
                && read.get("schema").is_none()
                && read.get("name").and_then(Json::as_str) == Some(name)
                && read.get("type").and_then(Json::as_str) == Some(ty)
        })
}

fn expected_ledger_inputs(
    impact_plan: &Json,
) -> Result<(Vec<Json>, BTreeMap<String, PublicBytesAbi>)> {
    let source_inputs = list(field(impact_plan, "circuit")?, "inputs")?;
    let reads = list(impact_plan, "reads")?;
    let mut public_source_inputs = Vec::new();
    let mut public_byte_abis = BTreeMap::new();
    for input in source_inputs {
        shape(input, &["name", "type", "visibility"], false)?;
        match text(input, "visibility")? {
            "public" => {
                let input_name = text(input, "name")?;
                let input_type = text(input, "type")?;
                match ScalarType::parse(input_type)? {
                    ScalarType::Bytes(0) => {}
                    byte_type @ (ScalarType::Bytes32 | ScalarType::Bytes(_)) => {
                        let length = byte_type.bytes_length().expect("matched a byte type");
                        let first_read =
                            reads.get(public_source_inputs.len()).ok_or_else(|| {
                                anyhow!("Impact plan is missing its public input prologue")
                            })?;
                        let packed = matches_public_input_prologue(
                            std::slice::from_ref(first_read),
                            &[(input_name.to_owned(), input_type.to_owned())],
                        );
                        let abi = if packed {
                            public_source_inputs
                                .push((input_name.to_owned(), input_type.to_owned()));
                            PublicBytesAbi::PackedFields
                        } else {
                            for index in 0..length {
                                public_source_inputs.push((
                                    format!("_noctium_bytes_{input_name}_{index}"),
                                    "UIntRange<256>".to_owned(),
                                ));
                            }
                            PublicBytesAbi::LegacyBytes
                        };
                        public_byte_abis.insert(input_name.to_owned(), abi);
                    }
                    ScalarType::JubjubScalar => {
                        public_source_inputs.push((
                            format!("_noctium_jubjub_scalar_{input_name}"),
                            "Native".to_owned(),
                        ));
                    }
                    ScalarType::JubjubPoint => {
                        for index in 0..2 {
                            public_source_inputs.push((
                                format!("_noctium_jubjub_point_{input_name}_{index}"),
                                "Native".to_owned(),
                            ));
                        }
                    }
                    #[cfg(feature = "zkir-321")]
                    ScalarType::Foreign(foreign_type) => {
                        for index in 0..foreign_type.native_type().encoded_len() {
                            public_source_inputs.push((
                                format!("_noctium_foreign_{input_name}_{index}"),
                                "Native".to_owned(),
                            ));
                        }
                    }
                    _ => public_source_inputs.push((input_name.to_owned(), input_type.to_owned())),
                }
            }
            "private" => {}
            _ => bail!("invalid Impact source input visibility"),
        }
    }

    ensure!(
        matches_public_input_prologue(reads, &public_source_inputs),
        "Impact plan public input prologue mismatch"
    );

    let mut expected = Vec::new();
    let mut names = BTreeSet::new();
    for read in reads.iter().skip(public_source_inputs.len()) {
        let read_type = text(read, "type")?;
        let byte_length = match ScalarType::parse(read_type) {
            Ok(ScalarType::Bytes32) => Some(32),
            Ok(ScalarType::Bytes(length)) => Some(length),
            _ => None,
        };
        if let Some(length) = byte_length {
            let projection_bindings = crate::byte_projection_bindings(text(read, "name")?, length)?;
            checked_impact_projections(read, &projection_bindings)?;
            for (expected_name, expected_type) in projection_bindings {
                append_impact_ledger_input(
                    &json!({"name": expected_name, "type": expected_type}),
                    false,
                    source_inputs.len(),
                    &mut names,
                    &mut expected,
                )?;
            }
            continue;
        }
        if matches!(ScalarType::parse(read_type), Ok(ScalarType::JubjubPoint)) {
            let projection_bindings = expected_point_projection_bindings(text(read, "name")?);
            checked_impact_projections(read, &projection_bindings)?;
            for (expected_name, expected_type) in projection_bindings {
                append_impact_ledger_input(
                    &json!({"name": expected_name, "type": expected_type}),
                    false,
                    source_inputs.len(),
                    &mut names,
                    &mut expected,
                )?;
            }
            continue;
        }
        ensure!(
            read.get("projections").is_none(),
            "non-byte Impact read has byte projections"
        );
        if let Some(components) = read.get("components") {
            let components = components
                .as_array()
                .ok_or_else(|| anyhow!("invalid Impact ledger read components"))?;
            if components.is_empty() {
                append_impact_ledger_input(
                    read,
                    true,
                    source_inputs.len(),
                    &mut names,
                    &mut expected,
                )?;
                continue;
            }
            for component in components {
                shape(component, &["name", "type"], false)?;
                let name = name(text(component, "name")?)?;
                let projections = match ScalarType::parse(text(component, "type")?)? {
                    ScalarType::Bytes32 => crate::byte_projection_bindings(&name, 32)?,
                    ScalarType::Bytes(length) => crate::byte_projection_bindings(&name, length)?,
                    ScalarType::JubjubPoint => expected_point_projection_bindings(&name),
                    _ => {
                        append_impact_ledger_input(
                            component,
                            false,
                            source_inputs.len(),
                            &mut names,
                            &mut expected,
                        )?;
                        continue;
                    }
                };
                for (name, ty) in projections {
                    append_impact_ledger_input(
                        &json!({"name": name, "type": ty}),
                        false,
                        source_inputs.len(),
                        &mut names,
                        &mut expected,
                    )?;
                }
            }
        } else {
            append_impact_ledger_input(read, true, source_inputs.len(), &mut names, &mut expected)?;
        }
    }
    Ok((expected, public_byte_abis))
}

pub(crate) fn validate_witness_artifacts(
    control_plan: &Json,
    binding_bytes: &[u8],
    relation: &Json,
    impact_plan: &Json,
    contract: &str,
    entrypoint: &str,
    circuit_file: &str,
    profile: &str,
) -> Result<()> {
    ensure!(
        binding_bytes.len() <= 524_288,
        "typed witness binding byte limit"
    );
    let binding_text = std::str::from_utf8(binding_bytes)
        .map_err(|_| anyhow!("typed witness binding is not UTF-8"))?;
    ensure!(
        field(control_plan, "binding")?.as_str() == Some(binding_text),
        "typed witness binding bytes differ from control plan"
    );
    let digest = hex::encode(Sha256::digest(binding_bytes));
    let parsed = Plan::parse(control_plan, Some(&digest))?;
    ensure!(
        parsed.schema_version == 2
            && parsed.mode.as_deref() == Some("native")
            && parsed.native_relation.as_ref() == Some(relation),
        "typed witness relation mismatch"
    );
    let binding = parsed
        .binding
        .as_ref()
        .ok_or_else(|| anyhow!("missing typed witness binding"))?;
    ensure!(
        text(impact_plan, "contractName")? == contract
            && text(impact_plan, "entrypoint")? == entrypoint
            && text(impact_plan, "nativeCircuitFile")? == circuit_file
            && impact_plan
                .get("target")
                .is_none_or(|target| target.as_str() == Some(profile)),
        "selected Impact plan identity mismatch"
    );
    ensure!(
        field(binding, "circuitInputs")? == field(field(impact_plan, "circuit")?, "inputs")?,
        "selected Impact plan source input mismatch"
    );
    ensure!(
        crate::call_input_names(binding)? == crate::call_input_names(impact_plan)?,
        "selected Impact plan call input order mismatch"
    );
    let actual_ledger_inputs: &[Json] = match binding.get("ledgerInputs") {
        Some(value) => value
            .as_array()
            .map(Vec::as_slice)
            .ok_or_else(|| anyhow!("invalid native ledger input list"))?,
        None => &[],
    };
    let (expected_ledger_descriptors, public_byte_abis) = expected_ledger_inputs(impact_plan)?;
    ensure!(
        actual_ledger_inputs == expected_ledger_descriptors.as_slice(),
        "selected Impact plan ledger input mismatch"
    );
    validate_native_ledger_boundaries(binding, impact_plan)?;
    ensure!(
        public_byte_relation_abis(binding, relation)? == public_byte_abis,
        "selected Impact plan and native relation public byte input shapes differ"
    );
    ensure!(
        field(binding, "nativeRelation")? == relation,
        "typed witness relation mismatch"
    );
    let target = field(binding, "target")?;
    ensure!(
        text(target, "kind")? == "entrypoint"
            && text(target, "contractName")? == contract
            && text(target, "entrypoint")? == entrypoint
            && text(target, "nativeCircuitFile")? == circuit_file
            && text(target, "targetProfile")? == profile,
        "typed witness native target mismatch"
    );
    Ok(())
}

// Unknown is distinct from known unit. Constants never invoke host effects.
type Known = Option<Option<Value>>;
type Constants = BTreeMap<String, Known>;
fn known_bool(value: &Known) -> Option<bool> {
    match value {
        Some(Some(Value::Bool(v))) => Some(*v),
        _ => None,
    }
}
fn known_cast(ty: &Type, value: Known) -> Known {
    match (ty, value) {
        (_, None) => None,
        (Type::Unit, Some(None)) => Some(None),
        (Type::Scalar(ty), Some(Some(value))) => value.cast(ty).ok().map(Some),
        _ => None,
    }
}
fn known_merge(values: Vec<Known>) -> Known {
    let mut it = values.into_iter();
    let first = it.next()?;
    if it.all(|v| v == first) { first } else { None }
}
fn known_environment(env: &Env) -> Constants {
    env.iter()
        .map(|(n, v)| (n.clone(), v.known.clone()))
        .collect()
}
fn arithmetic(op: &str, ty: &Type, a: Value, b: Value) -> Result<Value> {
    match scalar_type(ty)? {
        ScalarType::Native => {
            let a = a.cast(&ScalarType::Native)?.field_encoding()?;
            let b = b.cast(&ScalarType::Native)?.field_encoding()?;
            Ok(Value::Native(match op {
                "add" => a + b,
                "sub" => a - b,
                _ => a * b,
            }))
        }
        ScalarType::UInt(m) => scalars::unsigned_arithmetic(
            match op {
                "add" => scalars::UnsignedOp::Add,
                "sub" => scalars::UnsignedOp::Sub,
                _ => scalars::UnsignedOp::Mul,
            },
            a,
            b,
            &m.to_str_radix(10),
        ),
        _ => bail!("control arithmetic type"),
    }
}
struct AbstractFlow {
    returns: Vec<Known>,
    falls: bool,
}
struct Abstractor<'a> {
    functions: &'a BTreeMap<String, Arc<Function>>,
    fuel: &'a mut usize,
}
impl Abstractor<'_> {
    fn tick(&mut self) -> Result<()> {
        ensure!(*self.fuel > 0, "control abstract analysis fuel");
        *self.fuel -= 1;
        Ok(())
    }
    fn expression(&mut self, expr: &Expr, env: &Constants) -> Result<Known> {
        self.tick()?;
        Ok(match &expr.kind {
            ExprKind::Unit => Some(None),
            ExprKind::Literal(v) => Some(Some(v.clone())),
            ExprKind::Ref(n) => env.get(n).cloned().unwrap_or(None),
            ExprKind::Cast(x) => known_cast(&expr.ty, self.expression(x, env)?),
            ExprKind::Disclose(x) => self.expression(x, env)?,
            ExprKind::Binary(op, a, b) => {
                let a = self.expression(a, env)?;
                let b = self.expression(b, env)?;
                match (a, b) {
                    (Some(Some(a)), Some(Some(b))) => arithmetic(op, &expr.ty, a, b).ok().map(Some),
                    _ => None,
                }
            }
            ExprKind::BoolAnd(a, b) | ExprKind::BoolOr(a, b) | ExprKind::BoolXor(a, b) => {
                let a = self.expression(a, env)?;
                let b = self.expression(b, env)?;
                match (known_bool(&a), known_bool(&b)) {
                    (Some(a), Some(b)) => Some(Some(Value::Bool(match &expr.kind {
                        ExprKind::BoolAnd(_, _) => a && b,
                        ExprKind::BoolOr(_, _) => a || b,
                        ExprKind::BoolXor(_, _) => a != b,
                        _ => false,
                    }))),
                    _ => None,
                }
            }
            ExprKind::Eq(ty, a, b) => {
                let a = known_cast(ty, self.expression(a, env)?);
                let b = known_cast(ty, self.expression(b, env)?);
                match (a, b) {
                    (Some(a), Some(b)) => Some(Some(Value::Bool(a == b))),
                    _ => None,
                }
            }
            ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                let or = matches!(expr.kind, ExprKind::Or(_, _));
                let a = self.expression(a, env)?;
                match known_bool(&a) {
                    Some(v) if v == or => Some(Some(Value::Bool(or))),
                    Some(_) => self.expression(b, env)?,
                    None => {
                        let b = self.expression(b, env)?;
                        if known_bool(&b) == Some(or) {
                            Some(Some(Value::Bool(or)))
                        } else {
                            None
                        }
                    }
                }
            }
            ExprKind::If(c, a, b) | ExprKind::Select(c, a, b) => {
                let c = self.expression(c, env)?;
                match known_bool(&c) {
                    Some(v) => known_cast(&expr.ty, self.expression(if v { a } else { b }, env)?),
                    None => known_merge(vec![
                        known_cast(&expr.ty, self.expression(a, env)?),
                        known_cast(&expr.ty, self.expression(b, env)?),
                    ]),
                }
            }
            ExprKind::Call(id, args) => {
                let f = self.functions[id].clone();
                let mut local = BTreeMap::new();
                for ((n, t), a) in f.signature.parameters.iter().zip(args) {
                    local.insert(n.clone(), known_cast(t, self.expression(a, env)?));
                }
                let mut flow = self.body(&f.body, &local, &f.signature.result)?;
                if flow.falls {
                    flow.returns.push(Some(None));
                }
                known_merge(flow.returns)
            }
            ExprKind::Witness(_)
            | ExprKind::WitnessCall { .. }
            | ExprKind::Composite { .. }
            | ExprKind::Project { .. }
            | ExprKind::Index { .. }
            | ExprKind::Hash(_, _, _)
            | ExprKind::Curve(_, _)
            | ExprKind::Bytes(_, _)
            | ExprKind::FabDigest { .. } => None,
            #[cfg(feature = "zkir-321")]
            ExprKind::ForeignEncodedField(value, _) => {
                let _ = self.expression(value, env)?;
                None
            }
        })
    }
    fn body(&mut self, body: &Block, initial: &Constants, result: &Type) -> Result<AbstractFlow> {
        let mut env = initial.clone();
        let mut flow = AbstractFlow {
            returns: vec![],
            falls: true,
        };
        for stmt in &body.statements {
            if !flow.falls {
                break;
            }
            self.tick()?;
            match stmt {
                Stmt::Bind(n, t, x) => {
                    let value = known_cast(t, self.expression(x, &env)?);
                    env.insert(n.clone(), value);
                }
                Stmt::Return(x) => {
                    let value = match x {
                        Some(x) => self.expression(x, &env)?,
                        None => Some(None),
                    };
                    flow.returns.push(known_cast(result, value));
                    flow.falls = false;
                }
                Stmt::If(c, yes, no) => {
                    let condition = self.expression(c, &env)?;
                    let branches = match known_bool(&condition) {
                        Some(true) => vec![yes],
                        Some(false) => vec![no],
                        None => vec![yes, no],
                    };
                    let mut falls = false;
                    for branch in branches {
                        let inner = self.body(branch, &env, result)?;
                        falls |= inner.falls;
                        flow.returns.extend(inner.returns);
                    }
                    flow.falls = falls;
                }
                Stmt::Evaluate(_) | Stmt::Assert(_, _) | Stmt::Stage(_, _, _, _) => {}
            }
        }
        Ok(flow)
    }
}

#[derive(Clone)]
struct Tracked {
    value: Option<Value>,
    aggregate: Option<AggregateValue>,
    taint: bool,
    control_taint: bool,
    leaf_taints: Arc<Vec<bool>>,
    known: Known,
}
#[derive(Clone)]
struct AggregateValue {
    token: String,
    payload: Arc<AggregatePayload>,
}
struct AggregatePayload {
    value: Json,
    budget: Arc<AggregateBudget>,
    charge: usize,
}
struct AggregateBudget {
    used: AtomicUsize,
    limit: usize,
    per_value_limit: usize,
    node_limit: usize,
}
impl AggregateBudget {
    fn new(limit: usize) -> Arc<Self> {
        Self::with_limits(limit, MAX_AGGREGATE_VALUE_BYTES, MAX_AGGREGATE_JSON_NODES)
    }
    fn with_limits(limit: usize, per_value_limit: usize, node_limit: usize) -> Arc<Self> {
        Arc::new(Self {
            used: AtomicUsize::new(0),
            limit,
            per_value_limit,
            node_limit,
        })
    }
    fn reserve(&self, amount: usize) -> Result<()> {
        self.used
            .try_update(Ordering::AcqRel, Ordering::Acquire, |used| {
                used.checked_add(amount)
                    .filter(|total| *total <= self.limit)
            })
            .map(|_| ())
            .map_err(|_| anyhow!("control aggregate value budget exceeded"))
    }
    fn release(&self, amount: usize) {
        let previous = self.used.fetch_sub(amount, Ordering::AcqRel);
        debug_assert!(previous >= amount);
    }
}
pub(crate) struct AggregateReservation {
    budget: Arc<AggregateBudget>,
    charge: usize,
}
impl AggregateReservation {
    fn new(budget: &Arc<AggregateBudget>, charge: usize) -> Result<Self> {
        budget.reserve(charge)?;
        Ok(Self {
            budget: Arc::clone(budget),
            charge,
        })
    }
}
impl Drop for AggregateReservation {
    fn drop(&mut self) {
        self.budget.release(self.charge);
    }
}
/// JSON output that keeps its aggregate materialization charge until the value is dropped.
pub struct AccountedJson {
    value: Json,
    reservations: Vec<AggregateReservation>,
}
impl std::fmt::Debug for AccountedJson {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_tuple("AccountedJson")
            .field(&"[redacted]")
            .finish()
    }
}
impl AccountedJson {
    pub(crate) fn new(value: Json, reservations: Vec<AggregateReservation>) -> Self {
        Self {
            value,
            reservations,
        }
    }
    pub fn as_json(&self) -> &Json {
        &self.value
    }
    pub(crate) fn into_parts(mut self) -> (Json, Vec<AggregateReservation>) {
        let value = std::mem::replace(&mut self.value, Json::Null);
        let reservations = std::mem::take(&mut self.reservations);
        (value, reservations)
    }
}
impl Deref for AccountedJson {
    type Target = Json;
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}
impl PartialEq for AccountedJson {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}
impl Drop for AccountedJson {
    fn drop(&mut self) {
        wipe_json(&mut self.value);
    }
}
pub(crate) struct CompletedInputMap {
    pub values: BTreeMap<String, Json>,
    reservation: AggregateReservation,
}
impl CompletedInputMap {
    pub(crate) fn try_clone_accounted(&self) -> Result<Self> {
        let reservation =
            AggregateReservation::new(&self.reservation.budget, self.reservation.charge)?;
        Ok(Self {
            values: self.values.clone(),
            reservation,
        })
    }
}
impl Deref for CompletedInputMap {
    type Target = BTreeMap<String, Json>;
    fn deref(&self) -> &Self::Target {
        &self.values
    }
}
impl DerefMut for CompletedInputMap {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.values
    }
}
impl PartialEq for CompletedInputMap {
    fn eq(&self, other: &Self) -> bool {
        self.values == other.values
    }
}
impl Drop for CompletedInputMap {
    fn drop(&mut self) {
        for value in self.values.values_mut() {
            wipe_json(value);
        }
    }
}
impl AggregatePayload {
    fn from_borrowed(value: &Json, budget: &Arc<AggregateBudget>) -> Result<Arc<Self>> {
        let charge = aggregate_json_charge(value, budget.node_limit, budget.per_value_limit)?;
        budget.reserve(charge)?;
        Ok(Arc::new(Self {
            value: value.clone(),
            budget: Arc::clone(budget),
            charge,
        }))
    }
    fn from_owned(mut value: Json, budget: &Arc<AggregateBudget>) -> Result<Arc<Self>> {
        let charge = match aggregate_json_charge(&value, budget.node_limit, budget.per_value_limit)
        {
            Ok(charge) => charge,
            Err(error) => {
                wipe_json(&mut value);
                return Err(error);
            }
        };
        if charge > budget.per_value_limit {
            wipe_json(&mut value);
            bail!("control aggregate value limit exceeded");
        }
        if let Err(error) = budget.reserve(charge) {
            wipe_json(&mut value);
            return Err(error);
        }
        Ok(Arc::new(Self {
            value,
            budget: Arc::clone(budget),
            charge,
        }))
    }
}
impl Drop for AggregatePayload {
    fn drop(&mut self) {
        wipe_json(&mut self.value);
        self.budget.release(self.charge);
    }
}
fn aggregate_json_charge(value: &Json, node_limit: usize, byte_limit: usize) -> Result<usize> {
    // Charge a conservative retained-storage estimate before cloning borrowed trees.
    // Arc keeps later source references and environment copies from duplicating the payload.
    let mut pending = vec![value];
    let mut nodes = 0usize;
    let mut charge = 0usize;
    while let Some(value) = pending.pop() {
        nodes = nodes
            .checked_add(1)
            .ok_or_else(|| anyhow!("control aggregate node count overflow"))?;
        ensure!(
            nodes <= node_limit,
            "control aggregate JSON node limit exceeded"
        );
        charge = charge
            .checked_add(std::mem::size_of::<Json>() + 32)
            .ok_or_else(|| anyhow!("control aggregate size overflow"))?;
        match value {
            Json::String(text) => {
                charge = charge
                    .checked_add(
                        text.len()
                            .checked_mul(2)
                            .ok_or_else(|| anyhow!("control aggregate size overflow"))?,
                    )
                    .ok_or_else(|| anyhow!("control aggregate size overflow"))?;
            }
            Json::Array(values) => {
                ensure!(
                    pending
                        .len()
                        .checked_add(values.len())
                        .is_some_and(|count| count <= node_limit - nodes),
                    "control aggregate JSON node limit exceeded"
                );
                pending.extend(values);
            }
            Json::Object(values) => {
                ensure!(
                    pending
                        .len()
                        .checked_add(values.len())
                        .is_some_and(|count| count <= node_limit - nodes),
                    "control aggregate JSON node limit exceeded"
                );
                for (key, child) in values {
                    let key_charge = key
                        .len()
                        .checked_mul(2)
                        .and_then(|bytes| bytes.checked_add(48))
                        .ok_or_else(|| anyhow!("control aggregate size overflow"))?;
                    charge = charge
                        .checked_add(key_charge)
                        .ok_or_else(|| anyhow!("control aggregate size overflow"))?;
                    pending.push(child);
                }
            }
            Json::Null | Json::Bool(_) | Json::Number(_) => {}
        }
        ensure!(
            charge <= byte_limit,
            "control aggregate value limit exceeded"
        );
    }
    Ok(charge.max(1))
}
fn json_map_materialization_charge(values: &BTreeMap<String, Json>) -> Result<usize> {
    let mut charge = 0usize;
    for (key, value) in values {
        let key_charge = key
            .len()
            .checked_mul(2)
            .and_then(|bytes| bytes.checked_add(AGGREGATE_MATERIALIZATION_ENTRY_OVERHEAD))
            .ok_or_else(|| anyhow!("control materialization size overflow"))?;
        let value_charge = aggregate_json_charge(value, MAX_AGGREGATE_JSON_NODES, MAX_BYTES)?;
        charge = charge
            .checked_add(key_charge)
            .and_then(|total| total.checked_add(value_charge))
            .ok_or_else(|| anyhow!("control materialization size overflow"))?;
        ensure!(
            charge <= MAX_BYTES,
            "control materialization limit exceeded"
        );
    }
    Ok(charge.max(1))
}
impl Tracked {
    fn unit() -> Self {
        Self {
            value: None,
            aggregate: None,
            taint: false,
            control_taint: false,
            leaf_taints: Arc::new(vec![]),
            known: Some(None),
        }
    }
    fn scalar(value: Value, taint: bool) -> Self {
        let known = if taint {
            None
        } else {
            Some(Some(value.clone()))
        };
        Self {
            value: Some(value),
            aggregate: None,
            taint,
            control_taint: false,
            leaf_taints: Arc::new(vec![]),
            known,
        }
    }
    fn aggregate(
        token: String,
        payload: Arc<AggregatePayload>,
        leaf_taints: Vec<bool>,
        control_taint: bool,
    ) -> Self {
        Self {
            value: None,
            aggregate: Some(AggregateValue { token, payload }),
            taint: false,
            control_taint,
            leaf_taints: Arc::new(leaf_taints),
            known: None,
        }
    }
    fn is_tainted(&self) -> bool {
        self.taint || self.control_taint || self.leaf_taints.iter().any(|taint| *taint)
    }
    fn add_control_taint(&mut self, taint: bool) {
        self.control_taint |= taint;
        if taint {
            self.known = None;
        }
    }
    fn disclose(&mut self) {
        self.taint = false;
        self.control_taint = false;
        Arc::make_mut(&mut self.leaf_taints).fill(false);
        self.known = if self.aggregate.is_some() {
            None
        } else {
            Some(self.value.clone())
        };
    }
    fn public_json(&self) -> Json {
        self.value
            .as_ref()
            .map(Value::public_json)
            .or_else(|| {
                self.aggregate
                    .as_ref()
                    .map(|value| value.payload.value.clone())
            })
            .unwrap_or(Json::Null)
    }
    fn canonical_json(&self, ty: &Type) -> Result<Json> {
        match ty {
            Type::Unit => Ok(json!({"kind":"unit"})),
            Type::Scalar(_) => self
                .value
                .as_ref()
                .map(Value::public_json)
                .ok_or_else(|| anyhow!("control scalar required")),
            Type::Aggregate(token) => {
                let aggregate = self
                    .aggregate
                    .as_ref()
                    .ok_or_else(|| anyhow!("control aggregate required"))?;
                ensure!(&aggregate.token == token, "control aggregate type mismatch");
                Ok(aggregate.payload.value.clone())
            }
        }
    }
    fn materialization_charge(&self, key_bytes: usize) -> Result<usize> {
        let value_charge = self
            .aggregate
            .as_ref()
            .map(|value| value.payload.charge)
            .unwrap_or(0);
        value_charge
            .checked_add(
                key_bytes
                    .checked_mul(2)
                    .ok_or_else(|| anyhow!("control materialization size overflow"))?,
            )
            .and_then(|charge| charge.checked_add(AGGREGATE_MATERIALIZATION_ENTRY_OVERHEAD))
            .ok_or_else(|| anyhow!("control materialization size overflow"))
    }
    fn boolean(&self) -> Result<bool> {
        match self.value {
            Some(Value::Bool(b)) => Ok(b),
            _ => bail!("control Boolean required"),
        }
    }
}
fn reserve_witness_arguments(
    budget: &Arc<AggregateBudget>,
    values: &[Tracked],
    parameters: &[witness::Parameter],
) -> Result<AggregateReservation> {
    ensure!(
        values.len() == parameters.len(),
        "typed witness argument count"
    );
    let mut charge = 0usize;
    for (value, parameter) in values.iter().zip(parameters) {
        charge = charge
            .checked_add(value.materialization_charge(parameter.name.len())?)
            .ok_or_else(|| anyhow!("typed witness argument size overflow"))?;
        ensure!(
            charge <= MAX_BYTES,
            "typed witness argument materialization limit exceeded"
        );
    }
    AggregateReservation::new(budget, charge)
}
fn tracked_from_json(
    registry: &witness::Registry,
    token: &str,
    value: &Json,
    private: bool,
    aggregate_budget: &Arc<AggregateBudget>,
) -> Result<Tracked> {
    match parse_type(token, registry)? {
        Type::Unit => {
            registry.validate(token, value)?;
            let mut tracked = Tracked::unit();
            tracked.control_taint = private;
            Ok(tracked)
        }
        Type::Scalar(_) => {
            registry.validate(token, value)?;
            Ok(Tracked::scalar(input_value(token, value)?, private))
        }
        Type::Aggregate(aggregate_token) => {
            let payload = AggregatePayload::from_borrowed(value, aggregate_budget)?;
            let leaves = registry.flatten_leaves(token, &payload.value)?;
            Ok(Tracked::aggregate(
                aggregate_token,
                payload,
                vec![private; leaves.len()],
                private && leaves.is_empty(),
            ))
        }
    }
}
type Env = Arc<BTreeMap<String, Tracked>>;
enum Task {
    Eval(Arc<Expr>, Env),
    Unary(Type, bool),
    Merge(Type, bool),
    Binary(String, Type),
    Boolean(BooleanOperation),
    Eq(Type),
    Hash(String),
    Curve(String, usize),
    #[cfg(feature = "zkir-321")]
    ForeignEncodedField(usize),
    Bytes(String, usize),
    FabDigest(
        Vec<ScalarType>,
        ScalarType,
        crate::Expr,
        Vec<FabDigestArgumentKind>,
    ),
    EagerSelect(Type),
    Choose(Arc<Expr>, Arc<Expr>, Type, Env, Arc<Expr>),
    Short(bool, Arc<Expr>, Env),
    Args(String, Vec<Arc<Expr>>, usize, Vec<Tracked>, Env),
    ArgValue(String, Vec<Arc<Expr>>, usize, Vec<Tracked>, Env),
    Body(Arc<Block>, usize, Env, bool, Type),
    Bind(String, Type, Arc<Block>, usize, Env, bool, Type, Arc<Expr>),
    Discard,
    Assert(Option<String>),
    Return(Type, bool),
    Boundary(Type, bool, Option<String>),
    Finish,
    Branch(
        Arc<Block>,
        Arc<Block>,
        Arc<Block>,
        usize,
        Env,
        bool,
        Type,
        Arc<Expr>,
    ),
    Stage(String, String, String),
    WitnessArgs(String, String, Vec<Arc<Expr>>, usize, Vec<Tracked>, Env),
    WitnessArgValue(String, String, Vec<Arc<Expr>>, usize, Vec<Tracked>, Env),
    Composite(String, Vec<Arc<Expr>>, usize, Vec<Tracked>, Env),
    CompositeValue(String, Vec<Arc<Expr>>, usize, Vec<Tracked>, Env),
    Project(witness::Projection, String),
    Index(String),
}
pub(crate) fn wipe_json(value: &mut Json) {
    match value {
        Json::String(s) => s.zeroize(),
        Json::Array(v) => v.iter_mut().for_each(wipe_json),
        Json::Object(v) => v.values_mut().for_each(wipe_json),
        _ => {}
    }
}

#[derive(Clone, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Response {
    pub abi_version: u32,
    pub request_id: u64,
    pub operation: String,
    pub capability: String,
    pub schema: String,
    pub value: Json,
}
impl Drop for Response {
    fn drop(&mut self) {
        wipe_json(&mut self.value);
    }
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct TypedResponse {
    pub protocol_version: u32,
    pub request_id: String,
    pub attempt_id: String,
    pub outcome: String,
    pub operation: String,
    pub capability: String,
    pub schema: String,
    #[serde(default, deserialize_with = "present_json")]
    pub value: Option<Json>,
    pub error: Option<TypedProviderError>,
}
fn present_json<'de, D>(deserializer: D) -> std::result::Result<Option<Json>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    Json::deserialize(deserializer).map(Some)
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TypedProviderError {
    pub code: String,
}
impl Drop for TypedResponse {
    fn drop(&mut self) {
        if let Some(value) = &mut self.value {
            wipe_json(value);
        }
    }
}
struct Pending {
    id: u64,
    name: String,
    ty: String,
    request: Json,
    typed: Option<TypedInvocation>,
}
#[derive(Clone)]
struct TypedInvocation {
    ordinal: usize,
    name: String,
    site: String,
    path: Vec<String>,
    argument_charge: usize,
}
enum WitnessValue {
    PublicScalarOrUnit(Json),
    Aggregate(Arc<AggregatePayload>),
}
impl WitnessValue {
    fn as_json(&self) -> &Json {
        match self {
            Self::PublicScalarOrUnit(value) => value,
            Self::Aggregate(payload) => &payload.value,
        }
    }
}
impl Drop for WitnessValue {
    fn drop(&mut self) {
        if let Self::PublicScalarOrUnit(value) = self {
            wipe_json(value);
        }
    }
}
struct WitnessRecord {
    invocation: TypedInvocation,
    result_type: String,
    value: WitnessValue,
}
struct SecretInputs(BTreeMap<String, Json>, Arc<AggregateBudget>, usize);
impl Drop for SecretInputs {
    fn drop(&mut self) {
        for value in self.0.values_mut() {
            wipe_json(value);
        }
        self.1.release(self.2);
    }
}
enum Phase {
    Ready,
    Waiting,
    Complete(Json),
    Failed(Option<String>),
    Cancelled,
}
#[derive(Debug)]
struct AuthoredAssertionFailure(String);
impl std::fmt::Display for AuthoredAssertionFailure {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.0)
    }
}
impl std::error::Error for AuthoredAssertionFailure {}
/// A source-only invocation. No acceptance/commit notices or native proof API is exposed.
pub struct Session {
    plan: Plan,
    source_plan: Json,
    invocation_target: Option<InvocationTarget>,
    native_target_context_id: Option<u64>,
    host: Option<host::Runtime>,
    tasks: Vec<Task>,
    values: Vec<Tracked>,
    pending: Option<Pending>,
    phase: Phase,
    next_id: u64,
    remaining: usize,
    trace: Vec<String>,
    invocation_writes: BTreeMap<String, Json>,
    completed_phase_reservation: Option<AggregateReservation>,
    continuation_taint: bool,
    function_path: Vec<String>,
    witness_records: Vec<WitnessRecord>,
    bound_call_cursor: usize,
    native_guard_values: Option<BTreeMap<String, Json>>,
    native_guard_reservations: Vec<AggregateReservation>,
    source_inputs: SecretInputs,
    aggregate_budget: Arc<AggregateBudget>,
    invocation_write_reservations: BTreeMap<String, AggregateReservation>,
    completed_result_charge: Option<usize>,
    runtime_consumed: bool,
}
pub(crate) struct CompletedInvocation {
    pub context_id: u64,
    pub inputs: CompletedInputMap,
    pub runtime: host::Runtime,
}
impl Session {
    pub fn from_json(
        plan: Json,
        inputs: BTreeMap<String, Json>,
        context: host::Context,
    ) -> Result<Self> {
        Self::from_json_with_binding_sha256(plan, inputs, context, None)
    }
    pub fn from_json_with_binding_sha256(
        plan: Json,
        inputs: BTreeMap<String, Json>,
        context: host::Context,
        expected_binding_sha256: Option<&str>,
    ) -> Result<Self> {
        Self::from_json_with_invocation_target(plan, inputs, context, expected_binding_sha256, None)
    }
    pub fn from_json_with_invocation_target(
        plan: Json,
        inputs: BTreeMap<String, Json>,
        context: host::Context,
        expected_binding_sha256: Option<&str>,
        invocation_target: Option<InvocationTarget>,
    ) -> Result<Self> {
        raw_preflight(&plan)?;
        ensure!(
            serde_json::to_vec(&plan)?.len() <= MAX_BYTES,
            "control plan byte limit"
        );
        let source_plan = plan.clone();
        let plan = Plan::parse(&plan, expected_binding_sha256)?;
        let host_target = if plan.schema_version == 2 && plan.mode.as_deref() == Some("native") {
            let target = invocation_target
                .as_ref()
                .ok_or_else(|| anyhow!("native witness invocation target required"))?;
            target.validate()?;
            let binding_target = field(
                plan.binding
                    .as_ref()
                    .ok_or_else(|| anyhow!("missing native witness binding"))?,
                "target",
            )?;
            if text(binding_target, "kind")? == "entrypoint" {
                ensure!(
                    text(binding_target, "entrypoint")? == target.entrypoint,
                    "native witness invocation entrypoint mismatch"
                );
            } else {
                ensure!(
                    text(binding_target, "kind")? == "standalone",
                    "invalid native witness target"
                );
                ensure!(
                    target.entrypoint == plan.name,
                    "standalone witness source identity mismatch"
                );
            }
            (target.contract_address.clone(), target.entrypoint.clone())
        } else {
            ensure!(
                invocation_target.is_none(),
                "invocation target is restricted to native witness plans"
            );
            (plan.name.clone(), plan.entry.clone())
        };
        let aggregate_budget = AggregateBudget::new(MAX_SESSION_AGGREGATE_BYTES);
        let mut source_inputs = SecretInputs(inputs, Arc::clone(&aggregate_budget), 0);
        let source_input_charge = plan
            .inputs
            .iter()
            .try_fold(0usize, |total, (name, ty, _)| {
                let Type::Aggregate(_) = parse_type(ty, &plan.registry)? else {
                    return Ok(total);
                };
                let value = source_inputs
                    .0
                    .get(name)
                    .ok_or_else(|| anyhow!("missing control input"))?;
                let charge = aggregate_json_charge(
                    value,
                    aggregate_budget.node_limit,
                    aggregate_budget.per_value_limit,
                )?;
                total
                    .checked_add(charge)
                    .ok_or_else(|| anyhow!("control aggregate input size overflow"))
            })?;
        aggregate_budget.reserve(source_input_charge)?;
        source_inputs.2 = source_input_charge;
        ensure!(
            source_inputs.0.len() == plan.inputs.len(),
            "control input schema mismatch"
        );
        let host = if plan.schema_version == 1 {
            ensure!(
                plan.witnesses
                    .keys()
                    .all(|n| context.providers.iter().any(|p| &p.input == n)),
                "control witness requires registered provider"
            );
            host::Runtime::new(
                context,
                &plan.witnesses,
                plan.name.clone(),
                plan.entry.clone(),
            )?
        } else {
            let ledger_witnesses = plan
                .ledger_calls
                .keys()
                .map(|ordinal| {
                    plan.bound_calls
                        .get(*ordinal)
                        .and_then(|call| call.get("name"))
                        .and_then(Json::as_str)
                        .map(str::to_owned)
                        .ok_or_else(|| anyhow!("missing bound native ledger witness"))
                })
                .collect::<Result<BTreeSet<_>>>()?;
            let private_inputs = plan
                .signatures
                .keys()
                .filter(|name| !ledger_witnesses.contains(*name))
                .cloned()
                .collect::<Vec<_>>();
            let mut context = context;
            // Ledger witness slots come from the authenticated native cursor, never a host provider.
            context
                .providers
                .retain(|provider| !ledger_witnesses.contains(&provider.input));
            host::Runtime::new_typed(
                context,
                &private_inputs,
                host_target.0.clone(),
                host_target.1.clone(),
                &plan.registry,
            )?
        };
        let signature = &plan.functions[&plan.entry].signature;
        let mut env = BTreeMap::new();
        for ((input, ty, private), (parameter, target)) in
            plan.inputs.iter().zip(&signature.parameters)
        {
            let raw = source_inputs
                .0
                .get(input)
                .ok_or_else(|| anyhow!("missing control input"))?;
            let parsed = parse_type(ty, &plan.registry)?;
            let value = match parsed {
                Type::Unit => {
                    plan.registry.validate(ty, raw)?;
                    let mut value = Tracked::unit();
                    value.control_taint = *private;
                    value
                }
                Type::Scalar(_) => Tracked::scalar(input_value(ty, raw)?, *private),
                Type::Aggregate(token) => {
                    plan.registry.validate(ty, raw)?;
                    let leaf_values = plan.registry.flatten_leaves(ty, raw)?;
                    Tracked::aggregate(
                        token,
                        AggregatePayload::from_borrowed(raw, &aggregate_budget)?,
                        vec![*private; leaf_values.len()],
                        *private && leaf_values.is_empty(),
                    )
                }
            };
            env.insert(parameter.clone(), target.coerce(value)?);
        }
        let function = &plan.functions[&plan.entry];
        let function_path = vec![plan.entry.clone()];
        let tasks = vec![
            Task::Finish,
            Task::Boundary(signature.result.clone(), false, None),
            Task::Body(
                function.body.clone(),
                0,
                Arc::new(env),
                false,
                signature.result.clone(),
            ),
        ];
        let remaining = plan.max_steps;
        Ok(Self {
            plan,
            source_plan,
            invocation_target,
            native_target_context_id: None,
            host: Some(host),
            tasks,
            values: vec![],
            pending: None,
            phase: Phase::Ready,
            next_id: 0,
            remaining,
            trace: vec![],
            invocation_writes: BTreeMap::new(),
            completed_phase_reservation: None,
            continuation_taint: false,
            function_path,
            witness_records: Vec::new(),
            bound_call_cursor: 0,
            native_guard_values: None,
            native_guard_reservations: Vec::new(),
            source_inputs,
            aggregate_budget,
            invocation_write_reservations: BTreeMap::new(),
            completed_result_charge: None,
            runtime_consumed: false,
        })
    }
    pub(crate) fn from_authenticated_native_target(
        control_plan_bytes: &[u8],
        inputs: BTreeMap<String, Json>,
        context: host::Context,
        target: AuthenticatedNativeTarget,
    ) -> Result<Self> {
        ensure!(target.context_id != 0, "invalid native target context id");
        ensure!(
            control_plan_bytes == target.control_plan_bytes,
            "control plan bytes differ from authenticated bundle"
        );
        let control_plan: Json = serde_json::from_slice(control_plan_bytes)?;
        ensure!(
            control_plan == target.control_plan,
            "control plan differs from authenticated bundle"
        );
        let binding_sha256 = hex::encode(Sha256::digest(&target.binding_bytes));
        let invocation_target = InvocationTarget {
            contract_address: target.contract_address,
            entrypoint: target.entrypoint,
        };
        let mut session = Self::from_json_with_invocation_target(
            control_plan,
            inputs,
            context,
            Some(&binding_sha256),
            Some(invocation_target),
        )?;
        session.validate_public_witness_artifacts(
            &target.control_plan,
            &target.binding_bytes,
            &target.relation,
        )?;
        session.native_target_context_id = Some(target.context_id);
        Ok(session)
    }
    pub(crate) fn validate_public_witness_artifacts(
        &self,
        control_plan: &Json,
        binding_bytes: &[u8],
        actual_relation: &Json,
    ) -> Result<()> {
        ensure!(
            self.plan.schema_version == 2 && self.plan.mode.as_deref() == Some("native"),
            "native witness handoff requires a bound v2 plan"
        );
        ensure!(
            self.source_plan == *control_plan,
            "control plan differs from authenticated bundle"
        );
        let embedded_binding = self.source_plan["binding"]
            .as_str()
            .ok_or_else(|| anyhow!("missing native witness binding"))?;
        ensure!(
            embedded_binding.as_bytes() == binding_bytes,
            "witness binding bytes differ from authenticated bundle"
        );
        ensure!(
            self.plan.native_relation.as_ref() == Some(actual_relation),
            "native witness relation mismatch"
        );
        let invocation_target = self
            .invocation_target
            .as_ref()
            .ok_or_else(|| anyhow!("missing frozen native invocation target"))?;
        let binding_target = field(
            self.plan
                .binding
                .as_ref()
                .ok_or_else(|| anyhow!("missing native witness binding"))?,
            "target",
        )?;
        if text(binding_target, "kind")? == "entrypoint" {
            ensure!(
                text(binding_target, "entrypoint")? == invocation_target.entrypoint,
                "frozen invocation entrypoint differs from source binding"
            );
        }
        Ok(())
    }
    pub(crate) fn has_ledger_calls(&self) -> bool {
        !self.plan.ledger_calls.is_empty()
    }
    pub(crate) fn pending_ledger_call(&self) -> Result<Option<LedgerCall>> {
        if !matches!(self.phase, Phase::Waiting) {
            return Ok(None);
        }
        let pending = self
            .pending
            .as_ref()
            .ok_or_else(|| anyhow!("invalid control pending state"))?;
        let Some(invocation) = pending.typed.as_ref() else {
            return Ok(None);
        };
        let Some(call) = self.plan.ledger_calls.get(&invocation.ordinal) else {
            return Ok(None);
        };
        ensure!(
            self.native_target_context_id.is_some()
                && pending.name == invocation.name
                && self
                    .plan
                    .bound_calls
                    .get(invocation.ordinal)
                    .is_some_and(|bound| {
                        text(bound, "name").ok() == Some(invocation.name.as_str())
                            && text(bound, "site").ok() == Some(invocation.site.as_str())
                    }),
            "native ledger callback lacks its authenticated source binding"
        );
        Ok(Some(call.clone()))
    }
    pub(crate) fn peek_completed_invocation(
        &self,
        context_id: u64,
        target: &str,
        entrypoint: &str,
        control_plan: &Json,
        binding_bytes: &[u8],
        actual_relation: &Json,
    ) -> Result<CompletedInputMap> {
        self.validate_frozen_target(context_id, target, entrypoint)?;
        self.validate_public_witness_artifacts(control_plan, binding_bytes, actual_relation)?;
        self.completed_native_inputs(actual_relation)
    }
    pub(crate) fn take_completed_invocation(
        &mut self,
        context_id: u64,
        control_plan: &Json,
        binding_bytes: &[u8],
        actual_relation: &Json,
        expected_inputs: &CompletedInputMap,
        target: &str,
        entrypoint: &str,
    ) -> Result<CompletedInvocation> {
        self.validate_frozen_target(context_id, target, entrypoint)?;
        self.validate_public_witness_artifacts(control_plan, binding_bytes, actual_relation)?;
        let inputs = self.completed_native_inputs(actual_relation)?;
        ensure!(
            inputs.values == expected_inputs.values,
            "native witness input map changed after proof preparation"
        );
        let runtime = self.take_completed_host_runtime(actual_relation, target, entrypoint)?;
        Ok(CompletedInvocation {
            context_id,
            inputs,
            runtime,
        })
    }
    fn validate_frozen_target(
        &self,
        context_id: u64,
        target: &str,
        entrypoint: &str,
    ) -> Result<()> {
        ensure!(
            self.native_target_context_id == Some(context_id),
            "native target context mismatch"
        );
        let frozen = self
            .invocation_target
            .as_ref()
            .ok_or_else(|| anyhow!("missing frozen native invocation target"))?;
        ensure!(
            target == frozen.contract_address && entrypoint == frozen.entrypoint,
            "native witness invocation target changed"
        );
        Ok(())
    }
    fn pop(&mut self) -> Result<Tracked> {
        self.values
            .pop()
            .ok_or_else(|| anyhow!("invalid control machine state"))
    }
    fn clear_writes(&mut self) {
        for (mut key, mut value) in std::mem::take(&mut self.invocation_writes) {
            key.zeroize();
            wipe_json(&mut value);
        }
        self.invocation_write_reservations.clear();
    }
    fn guarded_native_binding(&self) -> bool {
        self.plan
            .binding
            .as_ref()
            .is_some_and(|binding| native_binding_version(binding).ok() == Some(2))
    }
    fn ensure_native_guard_values(&mut self) -> Result<()> {
        if self.native_guard_values.is_some() {
            return Ok(());
        }
        let binding = self
            .plan
            .binding
            .as_ref()
            .ok_or_else(|| anyhow!("missing native witness binding"))?;
        let mut circuit_values = BTreeMap::new();
        for input_binding in list(binding, "inputBindings")? {
            let source_name = text(input_binding, "name")?;
            let source_type = text(input_binding, "type")?;
            let source_value = self
                .source_inputs
                .0
                .get(source_name)
                .ok_or_else(|| anyhow!("missing native source input"))?;
            let leaves = self
                .plan
                .registry
                .flatten_leaves(source_type, source_value)?;
            let output_names = list(input_binding, "inputs")?;
            ensure!(
                leaves.len() == output_names.len(),
                "native source input binding mismatch"
            );
            for (name, value) in output_names.iter().zip(leaves) {
                let name = name
                    .as_str()
                    .ok_or_else(|| anyhow!("invalid native source input name"))?;
                ensure!(
                    circuit_values
                        .insert(
                            name.to_owned(),
                            native_leaf(&self.plan.native_input_types, name, value)?,
                        )
                        .is_none(),
                    "duplicate native circuit input value"
                );
            }
        }
        let reservation = AggregateReservation::new(
            &self.aggregate_budget,
            json_map_materialization_charge(&circuit_values)?,
        )?;
        self.native_guard_reservations.push(reservation);
        self.native_guard_values = Some(circuit_values);
        Ok(())
    }
    pub(crate) fn partial_native_inputs(&mut self) -> Result<CompletedInputMap> {
        ensure!(
            self.native_target_context_id.is_some()
                && self.has_ledger_calls()
                && self.guarded_native_binding()
                && !matches!(self.phase, Phase::Failed(_) | Phase::Cancelled),
            "partial native inputs require an authenticated ledger witness invocation"
        );
        self.ensure_native_guard_values()?;
        let values = self
            .native_guard_values
            .as_ref()
            .ok_or_else(|| anyhow!("missing partial native input prefix"))?;
        let reservation = AggregateReservation::new(
            &self.aggregate_budget,
            json_map_materialization_charge(&values)?,
        )?;
        Ok(CompletedInputMap {
            values: values.clone(),
            reservation,
        })
    }
    fn native_call_values(
        &self,
        ordinal: usize,
        value: Option<&Json>,
    ) -> Result<BTreeMap<String, Json>> {
        let call = self
            .plan
            .bound_calls
            .get(ordinal)
            .ok_or_else(|| anyhow!("missing native witness call binding"))?;
        let result_type = text(call, "resultType")?;
        let ty = parse_type(result_type, &self.plan.registry)?;
        let leaf_types = match &ty {
            Type::Unit => Vec::new(),
            Type::Scalar(_) => vec![result_type.to_owned()],
            Type::Aggregate(token) => self.plan.registry.leaf_types(token)?,
        };
        let leaves = match value {
            Some(value) => self.plan.registry.flatten_leaves(result_type, value)?,
            None => leaf_types
                .iter()
                .map(|ty| crate::inactive_read_value(ty).map(|value| value.public_json()))
                .collect::<Result<Vec<_>>>()?,
        };
        let output_names = list(call, "inputs")?;
        ensure!(
            leaves.len() == output_names.len() && leaves.len() == leaf_types.len(),
            "native witness result binding mismatch"
        );
        output_names
            .iter()
            .zip(leaves)
            .map(|(name, value)| {
                let name = name
                    .as_str()
                    .ok_or_else(|| anyhow!("invalid native witness input name"))?;
                Ok((
                    name.to_owned(),
                    native_leaf(&self.plan.native_input_types, name, value)?,
                ))
            })
            .collect()
    }
    fn prepare_native_guard_additions(
        &self,
        ordinal: usize,
        value: Option<&Json>,
    ) -> Result<(BTreeMap<String, Json>, Option<AggregateReservation>)> {
        let additions = self.native_call_values(ordinal, value)?;
        let current = self
            .native_guard_values
            .as_ref()
            .ok_or_else(|| anyhow!("missing native guard input prefix"))?;
        ensure!(
            additions.keys().all(|name| !current.contains_key(name)),
            "duplicate native circuit input value"
        );
        let reservation = if additions.is_empty() {
            None
        } else {
            Some(AggregateReservation::new(
                &self.aggregate_budget,
                json_map_materialization_charge(&additions)?,
            )?)
        };
        Ok((additions, reservation))
    }
    fn commit_native_guard_additions(
        &mut self,
        additions: BTreeMap<String, Json>,
        reservation: Option<AggregateReservation>,
    ) {
        if !additions.is_empty() {
            self.native_guard_values
                .as_mut()
                .expect("native guard prefix initialized")
                .extend(additions);
            self.native_guard_reservations
                .push(reservation.expect("native guard additions are charged"));
        }
    }
    fn next_native_active_call(&mut self) -> Result<Option<usize>> {
        if !self.guarded_native_binding() {
            return Ok((self.bound_call_cursor < self.plan.bound_calls.len())
                .then_some(self.bound_call_cursor));
        }
        self.ensure_native_guard_values()?;
        while self.bound_call_cursor < self.plan.bound_calls.len() {
            let ordinal = self.bound_call_cursor;
            let call = &self.plan.bound_calls[ordinal];
            let active = evaluate_native_guard(
                call,
                &self.plan.native_input_types,
                self.native_guard_values.as_ref().unwrap(),
            )?;
            if active {
                return Ok(Some(ordinal));
            }
            let (additions, reservation) = self.prepare_native_guard_additions(ordinal, None)?;
            self.commit_native_guard_additions(additions, reservation);
            self.bound_call_cursor += 1;
        }
        Ok(None)
    }
    fn consume_trailing_inactive_native_calls(&mut self) -> Result<()> {
        while self.next_native_active_call()?.is_some() {
            bail!("required native witness call was not executed");
        }
        Ok(())
    }
    fn clear_native_guard_values(&mut self) {
        if let Some(values) = &mut self.native_guard_values {
            for value in values.values_mut() {
                wipe_json(value);
            }
        }
        self.native_guard_values = None;
        self.native_guard_reservations.clear();
    }
    fn reject(&mut self) {
        self.reject_with_message(None);
    }
    fn reject_with_message(&mut self, message: Option<String>) {
        self.clear_writes();
        self.clear_native_guard_values();
        self.tasks.clear();
        self.values.clear();
        self.pending = None;
        for value in self.source_inputs.0.values_mut() {
            wipe_json(value);
        }
        self.witness_records.clear();
        if let Some(mut host) = self.host.take() {
            let _ = host.cancel();
        }
        self.phase = Phase::Failed(message);
    }
    pub fn private_trace(&self) -> Json {
        json!({"protocolVersion":1,"events":self.trace})
    }
    pub(crate) fn completed_native_inputs(
        &self,
        actual_relation: &Json,
    ) -> Result<CompletedInputMap> {
        ensure!(
            matches!(self.phase, Phase::Complete(_))
                && self.plan.schema_version == 2
                && self.plan.mode.as_deref() == Some("native")
                && !self.runtime_consumed,
            "native witness inputs require a completed bound execution"
        );
        ensure!(
            self.plan.native_relation.as_ref() == Some(actual_relation),
            "native witness relation mismatch"
        );
        ensure!(
            self.bound_call_cursor == self.plan.bound_calls.len()
                && (self.guarded_native_binding()
                    || self.witness_records.len() == self.plan.bound_calls.len()),
            "native witness call sequence is incomplete"
        );
        let binding = self
            .plan
            .binding
            .as_ref()
            .ok_or_else(|| anyhow!("missing native witness binding"))?;
        let input_descriptors = list(binding, "circuitInputs")?;
        let mut output_bytes = 0usize;
        for input in input_descriptors {
            let name = text(input, "name")?;
            let ty = text(input, "type")?;
            let input_charge = name
                .len()
                .checked_mul(2)
                .and_then(|bytes| bytes.checked_add(ty.len()))
                .and_then(|bytes| bytes.checked_add(256))
                .ok_or_else(|| anyhow!("native witness input map size overflow"))?;
            output_bytes = output_bytes
                .checked_add(input_charge)
                .ok_or_else(|| anyhow!("native witness input map size overflow"))?;
            ensure!(
                output_bytes <= MAX_COMPLETED_INPUT_BYTES,
                "native witness input map size limit exceeded"
            );
        }
        let transient_charge = output_bytes
            .checked_mul(2)
            .ok_or_else(|| anyhow!("native witness input map size overflow"))?;
        let transient_reservation =
            AggregateReservation::new(&self.aggregate_budget, transient_charge)?;
        let retained_reservation = AggregateReservation::new(&self.aggregate_budget, output_bytes)?;
        let circuit_input_types = &self.plan.native_input_types;
        let mut circuit_values = BTreeMap::new();
        for input_binding in list(binding, "inputBindings")? {
            let source_name = text(input_binding, "name")?;
            let source_type = text(input_binding, "type")?;
            let source_value = self
                .source_inputs
                .0
                .get(source_name)
                .ok_or_else(|| anyhow!("missing native source input"))?;
            let leaves = self
                .plan
                .registry
                .flatten_leaves(source_type, source_value)?;
            let output_names = list(input_binding, "inputs")?;
            ensure!(
                leaves.len() == output_names.len(),
                "native source input binding mismatch"
            );
            for (name, value) in output_names.iter().zip(leaves) {
                let name = name
                    .as_str()
                    .ok_or_else(|| anyhow!("invalid native source input name"))?;
                ensure!(
                    circuit_values
                        .insert(
                            name.to_owned(),
                            native_leaf(circuit_input_types, name, value)?,
                        )
                        .is_none(),
                    "duplicate native circuit input value"
                );
            }
        }
        let guarded_binding = self.guarded_native_binding();
        let mut previous_record_ordinal = None;
        for record in &self.witness_records {
            ensure!(
                record.invocation.ordinal < self.plan.bound_calls.len()
                    && previous_record_ordinal
                        .map_or(true, |previous| previous < record.invocation.ordinal),
                "native witness records are duplicated or reordered"
            );
            previous_record_ordinal = Some(record.invocation.ordinal);
        }
        let mut record_index = 0;
        for (index, call) in self.plan.bound_calls.iter().enumerate() {
            let record = self.witness_records.get(record_index);
            let active = if guarded_binding {
                evaluate_native_guard(call, circuit_input_types, &circuit_values)?
            } else {
                true
            };
            if !active {
                ensure!(
                    !record.is_some_and(|record| record.invocation.ordinal == index),
                    "native witness record exists for an inactive call"
                );
                for (name, value) in self.native_call_values(index, None)? {
                    ensure!(
                        circuit_values.insert(name, value).is_none(),
                        "duplicate native circuit input value"
                    );
                }
                continue;
            }
            let record = record.ok_or_else(|| anyhow!("required native witness record missing"))?;
            ensure!(
                record.invocation.ordinal == index
                    && text(call, "ordinal")? == index.to_string()
                    && text(call, "site")? == record.invocation.site
                    && text(call, "name")? == record.invocation.name
                    && list(call, "path")?
                        == &record
                            .invocation
                            .path
                            .iter()
                            .cloned()
                            .map(Json::String)
                            .collect::<Vec<_>>()
                    && text(call, "resultType")? == record.result_type,
                "native witness call binding mismatch"
            );
            for (name, value) in self.native_call_values(index, Some(record.value.as_json()))? {
                ensure!(
                    circuit_values.insert(name, value).is_none(),
                    "duplicate native circuit input value"
                );
            }
            record_index += 1;
        }
        ensure!(
            record_index == self.witness_records.len(),
            "native witness record ordinal is unknown"
        );
        let circuit_names = list(binding, "circuitInputs")?
            .iter()
            .map(|input| text(input, "name").map(str::to_owned))
            .collect::<Result<BTreeSet<_>>>()?;
        ensure!(
            circuit_values.len() == circuit_names.len()
                && circuit_values
                    .keys()
                    .all(|name| circuit_names.contains(name)),
            "native circuit input map is incomplete"
        );
        drop(transient_reservation);
        Ok(CompletedInputMap {
            values: circuit_values,
            reservation: retained_reservation,
        })
    }
    /// Private host handoff data. The caller must treat the returned circuit inputs and writes as secret.
    /// Compatibility API for callers that own the returned snapshot outside the session budget.
    /// Use `private_completion_accounted` when the caller needs the materialization charge to live
    /// with the returned private value.
    pub fn private_completion(&mut self, actual_relation: &Json) -> Result<Json> {
        Ok(self
            .private_completion_accounted(actual_relation)?
            .into_parts()
            .0)
    }
    /// Returns private completion data with both copy charges held until drop.
    pub fn private_completion_accounted(
        &mut self,
        actual_relation: &Json,
    ) -> Result<AccountedJson> {
        let inputs = self.completed_native_inputs(actual_relation)?;
        let input_reservation =
            AggregateReservation::new(&self.aggregate_budget, inputs.reservation.charge)?;
        let write_charge = json_map_materialization_charge(&self.invocation_writes)?;
        let write_reservation = AggregateReservation::new(&self.aggregate_budget, write_charge)?;
        let completion = json!({
            "protocolVersion": 2,
            "kind": "typed-witness-inputs",
            "circuitName": field(self.plan.binding.as_ref().unwrap(), "circuitName")?,
            "target": field(self.plan.binding.as_ref().unwrap(), "target")?,
            "inputs": inputs.values,
            "hostWrites": self.invocation_writes,
        });
        Ok(AccountedJson::new(
            completion,
            vec![input_reservation, write_reservation],
        ))
    }
    pub(crate) fn take_completed_host_runtime(
        &mut self,
        actual_relation: &Json,
        target: &str,
        entrypoint: &str,
    ) -> Result<host::Runtime> {
        ensure!(
            self.plan.native_relation.as_ref() == Some(actual_relation),
            "native witness relation mismatch"
        );
        let binding = self
            .plan
            .binding
            .as_ref()
            .ok_or_else(|| anyhow!("missing native witness binding"))?;
        let frozen = self
            .invocation_target
            .as_ref()
            .ok_or_else(|| anyhow!("missing frozen native invocation target"))?;
        ensure!(
            target == frozen.contract_address && entrypoint == frozen.entrypoint,
            "native witness invocation target changed"
        );
        ensure!(
            text(field(binding, "target")?, "kind")? == "entrypoint"
                && text(field(binding, "target")?, "entrypoint")? == entrypoint,
            "native witness entrypoint mismatch"
        );
        let runtime = self
            .host
            .as_mut()
            .ok_or_else(|| anyhow!("native witness runtime already consumed"))?;
        ensure!(
            runtime.has_target(target, entrypoint),
            "native witness runtime target changed"
        );
        runtime.execution_finished(true)?;
        let runtime = self
            .host
            .take()
            .ok_or_else(|| anyhow!("native witness runtime already consumed"))?;
        self.runtime_consumed = true;
        for value in self.source_inputs.0.values_mut() {
            wipe_json(value);
        }
        self.witness_records.clear();
        self.clear_native_guard_values();
        Ok(runtime)
    }
    /// Compatibility API for callers that own the returned snapshot outside the session budget.
    /// Use `private_request_accounted` when the caller needs the charge to live with the result.
    pub fn private_request(&mut self) -> Result<Json> {
        Ok(self.private_request_accounted()?.into_parts().0)
    }
    /// Returns a private request whose materialization charge follows the value until drop.
    pub fn private_request_accounted(&mut self) -> Result<AccountedJson> {
        ensure!(
            matches!(self.phase, Phase::Waiting),
            "invalid control lifecycle state"
        );
        let write_charge = json_map_materialization_charge(&self.invocation_writes)?;
        let argument_charge = self
            .pending
            .as_ref()
            .and_then(|pending| pending.typed.as_ref())
            .map(|invocation| invocation.argument_charge)
            .unwrap_or(0);
        let charge = write_charge
            .checked_add(argument_charge)
            .and_then(|total| total.checked_add(AGGREGATE_MATERIALIZATION_ENTRY_OVERHEAD * 2))
            .ok_or_else(|| anyhow!("control private request size overflow"))?;
        ensure!(
            charge <= MAX_BYTES,
            "control private request materialization limit exceeded"
        );
        let reservation = AggregateReservation::new(&self.aggregate_budget, charge)?;
        let mut request = self
            .host
            .as_ref()
            .ok_or_else(|| anyhow!("invalid control lifecycle state"))?
            .private_arguments()?;
        request["invocationWrites"] = json!(self.invocation_writes);
        Ok(AccountedJson::new(request, vec![reservation]))
    }
    pub fn stage(&mut self, stage: host::Stage) -> Result<()> {
        ensure!(
            self.plan.schema_version == 1,
            "manual writes are disabled for source-bound v2 plans"
        );
        self.stage_from_source(stage, None)
    }
    fn stage_from_source(
        &mut self,
        stage: host::Stage,
        reservation: Option<AggregateReservation>,
    ) -> Result<()> {
        ensure!(
            matches!(self.phase, Phase::Ready | Phase::Waiting),
            "invalid control lifecycle state"
        );
        let key = stage.key.clone();
        let reservation_key = key.clone();
        let mut value = json!({"type":stage.ty,"value":stage.value});
        let staged = if self.plan.schema_version == 1 {
            self.host
                .as_mut()
                .ok_or_else(|| anyhow!("invalid control lifecycle state"))?
                .stage(stage)
        } else {
            self.host
                .as_mut()
                .ok_or_else(|| anyhow!("invalid control lifecycle state"))?
                .stage_typed(stage, &self.plan.registry)
        };
        if let Err(error) = staged {
            wipe_json(&mut value);
            return Err(error.into());
        }
        if let Some(mut old) = self.invocation_writes.insert(key, value) {
            wipe_json(&mut old);
        }
        if let Some(reservation) = reservation {
            self.invocation_write_reservations
                .insert(reservation_key, reservation);
        }
        self.trace.push("stage".into());
        Ok(())
    }
    pub fn cancel(&mut self) -> Result<Json> {
        if !matches!(self.phase, Phase::Cancelled) {
            self.clear_writes();
            self.tasks.clear();
            self.values.clear();
            self.pending = None;
            if let Some(mut host) = self.host.take() {
                host.cancel()?;
            }
            for value in self.source_inputs.0.values_mut() {
                wipe_json(value);
            }
            self.witness_records.clear();
            self.clear_native_guard_values();
            self.phase = Phase::Cancelled;
        }
        Ok(json!({"abiVersion":1,"status":"cancelled"}))
    }
    pub fn resume(&mut self, response: Response) -> Result<Json> {
        ensure!(
            matches!(self.phase, Phase::Waiting),
            "invalid control lifecycle state"
        );
        let pending = self
            .pending
            .as_ref()
            .ok_or_else(|| anyhow!("invalid control lifecycle state"))?;
        ensure!(
            response.abi_version == 1 && response.request_id == pending.id,
            "invalid control host response"
        );
        let value = input_value(&pending.ty, &response.value)?;
        self.host
            .as_mut()
            .ok_or_else(|| anyhow!("invalid control lifecycle state"))?
            .finish_input(
                &pending.name,
                pending.id,
                Some(&response.operation),
                Some(&response.capability),
                Some(&response.schema),
                &response.value,
            )?;
        self.values.push(Tracked::scalar(value, true));
        self.pending = None;
        self.phase = Phase::Ready;
        Ok(json!({"abiVersion":1,"status":"ready"}))
    }
    pub fn resume_typed(&mut self, response: TypedResponse) -> Result<Json> {
        ensure!(
            matches!(self.phase, Phase::Waiting),
            "invalid control lifecycle state"
        );
        ensure!(
            self.pending_ledger_call()?.is_none(),
            "native ledger callback cannot be resumed by a host provider"
        );
        let (pending_id, invocation, expected_attempt) = {
            let pending = self
                .pending
                .as_ref()
                .ok_or_else(|| anyhow!("invalid control lifecycle state"))?;
            let invocation = pending
                .typed
                .as_ref()
                .ok_or_else(|| anyhow!("typed response for legacy control request"))?;
            (
                pending.id,
                invocation.clone(),
                text(&pending.request, "attemptId")?.to_owned(),
            )
        };
        let signature = self
            .plan
            .signatures
            .get(&invocation.name)
            .cloned()
            .ok_or_else(|| anyhow!("unknown pending typed witness"))?;
        let request_id = canonical_u64(&response.request_id)?;
        ensure!(
            request_id.to_string() == response.request_id
                && response.protocol_version == 2
                && request_id == pending_id
                && response.attempt_id == expected_attempt
                && response.operation == signature.operation
                && response.capability == signature.capability
                && response.schema == signature.result_type,
            "invalid typed control host response"
        );
        match response.outcome.as_str() {
            "error" => {
                ensure!(response.value.is_none(), "invalid typed provider failure");
                let error = response
                    .error
                    .as_ref()
                    .ok_or_else(|| anyhow!("missing typed provider error"))?;
                ensure!(
                    error.code == "provider_failed",
                    "invalid typed provider error"
                );
                self.reject();
                Ok(self.advance()?)
            }
            "value" => {
                ensure!(response.error.is_none(), "invalid typed provider result");
                let raw = response
                    .value
                    .as_ref()
                    .ok_or_else(|| anyhow!("missing typed provider value"))?;
                self.resume_typed_value(invocation, pending_id, raw, Some(&response))
            }
            _ => bail!("invalid typed control host outcome"),
        }
    }
    pub(crate) fn resume_ledger(&mut self, value: Json) -> Result<Json> {
        let call = self
            .pending_ledger_call()?
            .ok_or_else(|| anyhow!("no authenticated native ledger callback is pending"))?;
        let pending = self
            .pending
            .as_ref()
            .ok_or_else(|| anyhow!("invalid control pending state"))?;
        let invocation = pending
            .typed
            .as_ref()
            .ok_or_else(|| anyhow!("invalid native ledger callback state"))?
            .clone();
        ensure!(
            call.ordinal == invocation.ordinal,
            "native ledger callback order mismatch"
        );
        let pending_id = pending.id;
        let mut value = value;
        let result = self.resume_typed_value(invocation, pending_id, &value, None);
        wipe_json(&mut value);
        result
    }
    fn resume_typed_value(
        &mut self,
        invocation: TypedInvocation,
        pending_id: u64,
        raw: &Json,
        host_response: Option<&TypedResponse>,
    ) -> Result<Json> {
        if host_response.is_none() {
            let ledger_call = self
                .pending_ledger_call()?
                .ok_or_else(|| anyhow!("native ledger callback binding mismatch"))?;
            ensure!(
                ledger_call.ordinal == invocation.ordinal,
                "native ledger callback order mismatch"
            );
        }
        let signature = self
            .plan
            .signatures
            .get(&invocation.name)
            .cloned()
            .ok_or_else(|| anyhow!("unknown pending typed witness"))?;
        let result = tracked_from_json(
            &self.plan.registry,
            &signature.result_type,
            raw,
            true,
            &self.aggregate_budget,
        )?;
        if self.plan.mode.as_deref() == Some("native") {
            let bound = self
                .plan
                .bound_calls
                .get(invocation.ordinal)
                .ok_or_else(|| anyhow!("missing native witness call binding"))?;
            let leaf_values = self
                .plan
                .registry
                .flatten_leaves(&signature.result_type, raw)?;
            ensure!(
                list(bound, "inputs")?.len() == leaf_values.len(),
                "native witness response shape mismatch"
            );
        }
        let record_value = match parse_type(&signature.result_type, &self.plan.registry)? {
            Type::Aggregate(_) => WitnessValue::Aggregate(AggregatePayload::from_borrowed(
                raw,
                &self.aggregate_budget,
            )?),
            Type::Unit | Type::Scalar(_) => WitnessValue::PublicScalarOrUnit(raw.clone()),
        };
        let native_guard_additions = if self.guarded_native_binding() {
            Some(self.prepare_native_guard_additions(invocation.ordinal, Some(raw))?)
        } else {
            None
        };
        if let Some(response) = host_response {
            let completed = self
                .host
                .as_mut()
                .ok_or_else(|| anyhow!("invalid control host state"))?
                .finish_typed_input(
                    &invocation.name,
                    pending_id,
                    Some(&response.attempt_id),
                    Some(&response.operation),
                    Some(&response.capability),
                    Some(&response.schema),
                    raw,
                    &self.plan.registry,
                )?;
            let mut completed = completed;
            ensure!(
                completed == *raw,
                "typed host returned a different canonical witness value"
            );
            wipe_json(&mut completed);
        }
        self.witness_records.push(WitnessRecord {
            invocation,
            result_type: signature.result_type,
            value: record_value,
        });
        if let Some((additions, reservation)) = native_guard_additions {
            self.commit_native_guard_additions(additions, reservation);
        }
        self.values.push(result);
        self.pending = None;
        self.phase = Phase::Ready;
        Ok(json!({"abiVersion":2,"status":"ready"}))
    }
    /// Compatibility API for callers that own the returned snapshot outside the session budget.
    /// Use `advance_accounted` for bounded source-execution and C ABI paths.
    pub fn advance(&mut self) -> Result<Json> {
        Ok(self.advance_accounted()?.into_parts().0)
    }
    /// Returns the next control result with aggregate materialization charged until drop.
    pub fn advance_accounted(&mut self) -> Result<AccountedJson> {
        match &self.phase {
            Phase::Waiting => {
                if self.pending_ledger_call()?.is_some() {
                    return Ok(AccountedJson::new(
                        json!({"abiVersion":1,"status":"need_ledger"}),
                        Vec::new(),
                    ));
                }
                return Ok(AccountedJson::new(
                    json!({"abiVersion":1,"status":"need_host","request":self.pending.as_ref().ok_or_else(||anyhow!("invalid control pending state"))?.request}),
                    Vec::new(),
                ));
            }
            Phase::Complete(v) => {
                let reservations = self
                    .completed_result_charge
                    .map(|charge| AggregateReservation::new(&self.aggregate_budget, charge))
                    .transpose()?
                    .into_iter()
                    .collect();
                return Ok(AccountedJson::new(v.clone(), reservations));
            }
            Phase::Failed(message) => {
                let mut error = json!({"code":"execution_rejected"});
                if let Some(message) = message {
                    error["message"] = json!(message);
                }
                return Ok(AccountedJson::new(
                    json!({"abiVersion":1,"status":"failed","error":error}),
                    Vec::new(),
                ));
            }
            Phase::Cancelled => {
                return Ok(AccountedJson::new(
                    json!({"abiVersion":1,"status":"cancelled"}),
                    Vec::new(),
                ));
            }
            Phase::Ready => {}
        }
        while let Some(task) = self.tasks.pop() {
            if self.remaining == 0 {
                self.reject();
                return self.advance_accounted();
            }
            self.remaining -= 1;
            if let Err(error) = self.step(task) {
                let message = error
                    .downcast_ref::<AuthoredAssertionFailure>()
                    .map(|failure| failure.0.clone());
                self.reject_with_message(message);
                return self.advance_accounted();
            }
            if !matches!(self.phase, Phase::Ready) {
                return self.advance_accounted();
            }
        }
        self.reject();
        self.advance_accounted()
    }
    fn known_expression(&mut self, expression: &Expr, env: &Env) -> Result<Known> {
        Abstractor {
            functions: &self.plan.functions,
            fuel: &mut self.remaining,
        }
        .expression(expression, &known_environment(env))
    }
    fn coerce_aggregate_cast(&self, target: &str, value: Tracked) -> Result<Tracked> {
        ensure!(
            value.value.is_none(),
            "control aggregate cast requires aggregate"
        );
        let source = value
            .aggregate
            .as_ref()
            .ok_or_else(|| anyhow!("control aggregate cast requires aggregate"))?;
        if source.token == target {
            return Type::Aggregate(target.to_owned()).coerce(value);
        }
        let widened = self.plan.registry.widen_aggregate_value(
            &source.token,
            target,
            &source.payload.value,
        )?;
        ensure!(
            value.leaf_taints.len() == self.plan.registry.leaf_types(target)?.len(),
            "aggregate widening changed leaf taint shape"
        );
        let payload = AggregatePayload::from_owned(widened, &self.aggregate_budget)?;
        Ok(Tracked::aggregate(
            target.to_owned(),
            payload,
            value.leaf_taints.as_ref().clone(),
            value.control_taint,
        ))
    }
    fn step(&mut self, task: Task) -> Result<()> {
        match task {
            Task::Eval(expr, env) => match &expr.kind {
                ExprKind::Unit => self.values.push(Tracked::unit()),
                ExprKind::Literal(v) => self.values.push(Tracked::scalar(v.clone(), false)),
                ExprKind::Ref(n) => self.values.push(
                    env.get(n)
                        .ok_or_else(|| anyhow!("unbound control value"))?
                        .clone(),
                ),
                ExprKind::Cast(x) | ExprKind::Disclose(x) => {
                    self.tasks.push(Task::Unary(
                        expr.ty.clone(),
                        matches!(expr.kind, ExprKind::Disclose(_)),
                    ));
                    self.tasks.push(Task::Eval(x.clone(), env));
                }
                ExprKind::Binary(op, a, b) => {
                    self.tasks.push(Task::Binary(op.clone(), expr.ty.clone()));
                    self.tasks.push(Task::Eval(b.clone(), env.clone()));
                    self.tasks.push(Task::Eval(a.clone(), env));
                }
                ExprKind::BoolAnd(a, b) | ExprKind::BoolOr(a, b) | ExprKind::BoolXor(a, b) => {
                    let operation = match &expr.kind {
                        ExprKind::BoolAnd(_, _) => BooleanOperation::And,
                        ExprKind::BoolOr(_, _) => BooleanOperation::Or,
                        ExprKind::BoolXor(_, _) => BooleanOperation::Xor,
                        _ => return Err(anyhow!("invalid eager Boolean operation")),
                    };
                    self.tasks.push(Task::Boolean(operation));
                    self.tasks.push(Task::Eval(b.clone(), env.clone()));
                    self.tasks.push(Task::Eval(a.clone(), env));
                }
                ExprKind::Eq(t, a, b) => {
                    self.tasks.push(Task::Eq(t.clone()));
                    self.tasks.push(Task::Eval(b.clone(), env.clone()));
                    self.tasks.push(Task::Eval(a.clone(), env));
                }
                ExprKind::Hash(d, a, b) => {
                    self.tasks.push(Task::Hash(d.clone()));
                    self.tasks.push(Task::Eval(b.clone(), env.clone()));
                    self.tasks.push(Task::Eval(a.clone(), env));
                }
                ExprKind::Curve(operation, arguments) => {
                    self.tasks
                        .push(Task::Curve(operation.clone(), arguments.len()));
                    for argument in arguments.iter().rev() {
                        self.tasks.push(Task::Eval(argument.clone(), env.clone()));
                    }
                }
                #[cfg(feature = "zkir-321")]
                ExprKind::ForeignEncodedField(value, index) => {
                    self.tasks.push(Task::ForeignEncodedField(*index));
                    self.tasks.push(Task::Eval(value.clone(), env));
                }
                ExprKind::Bytes(operation, arguments) => {
                    self.tasks
                        .push(Task::Bytes(operation.clone(), arguments.len()));
                    for argument in arguments.iter().rev() {
                        self.tasks.push(Task::Eval(argument.clone(), env.clone()));
                    }
                }
                ExprKind::FabDigest {
                    parameters,
                    result,
                    expression,
                    argument_kinds,
                    arguments,
                } => {
                    self.tasks.push(Task::FabDigest(
                        parameters.clone(),
                        result.clone(),
                        expression.clone(),
                        argument_kinds.clone(),
                    ));
                    for argument in arguments.iter().rev() {
                        self.tasks.push(Task::Eval(argument.clone(), env.clone()));
                    }
                }
                ExprKind::Select(c, a, b) => {
                    self.tasks.push(Task::EagerSelect(expr.ty.clone()));
                    self.tasks.push(Task::Eval(b.clone(), env.clone()));
                    self.tasks.push(Task::Eval(a.clone(), env.clone()));
                    self.tasks.push(Task::Eval(c.clone(), env));
                }
                ExprKind::If(c, a, b) => {
                    self.tasks.push(Task::Choose(
                        a.clone(),
                        b.clone(),
                        expr.ty.clone(),
                        env.clone(),
                        c.clone(),
                    ));
                    self.tasks.push(Task::Eval(c.clone(), env));
                }
                ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                    self.tasks.push(Task::Short(
                        matches!(expr.kind, ExprKind::Or(_, _)),
                        b.clone(),
                        env.clone(),
                    ));
                    self.tasks.push(Task::Eval(a.clone(), env));
                }
                ExprKind::Call(id, args) => {
                    self.tasks
                        .push(Task::Args(id.clone(), args.clone(), 0, vec![], env))
                }
                ExprKind::Witness(n) => {
                    self.next_id = self
                        .next_id
                        .checked_add(1)
                        .ok_or_else(|| anyhow!("control request limit"))?;
                    let request = self
                        .host
                        .as_mut()
                        .ok_or_else(|| anyhow!("invalid control host state"))?
                        .begin_input(n, self.next_id)?
                        .ok_or_else(|| anyhow!("control witness requires provider"))?;
                    self.pending = Some(Pending {
                        id: self.next_id,
                        name: n.clone(),
                        ty: self.plan.witnesses[n].clone(),
                        request,
                        typed: None,
                    });
                    self.trace.push(format!("witness:{n}"));
                    self.phase = Phase::Waiting;
                }
                ExprKind::WitnessCall {
                    name,
                    site,
                    arguments,
                } => {
                    self.tasks.push(Task::WitnessArgs(
                        name.clone(),
                        site.clone(),
                        arguments.clone(),
                        0,
                        vec![],
                        env,
                    ));
                }
                ExprKind::Composite { token, leaves } => {
                    self.tasks.push(Task::Composite(
                        token.clone(),
                        leaves.clone(),
                        0,
                        vec![],
                        env,
                    ));
                }
                ExprKind::Project { value, projection } => {
                    self.tasks
                        .push(Task::Project(projection.clone(), expr.ty.token()));
                    self.tasks.push(Task::Eval(value.clone(), env));
                }
                ExprKind::Index { value, index } => {
                    self.tasks.push(Task::Index(expr.ty.token()));
                    self.tasks.push(Task::Eval(index.clone(), env.clone()));
                    self.tasks.push(Task::Eval(value.clone(), env));
                }
            },
            Task::Unary(ty, disclose) => {
                let value = self.pop()?;
                let mut value = match &ty {
                    Type::Aggregate(target) => self.coerce_aggregate_cast(target, value)?,
                    _ => ty.coerce(value)?,
                };
                if disclose {
                    value.disclose();
                }
                self.values.push(value);
            }
            Task::Merge(ty, taint) => {
                let value = self.pop()?;
                let mut value = ty.coerce(value)?;
                value.add_control_taint(taint);
                self.values.push(value);
            }
            Task::Boolean(operation) => {
                let right = self.pop()?;
                let left = self.pop()?;
                let taint = left.is_tainted() || right.is_tainted();
                let values = vec![Value::Bool(left.boolean()?), Value::Bool(right.boolean()?)];
                self.values.push(Tracked::scalar(
                    evaluate_operation(boolean_operation(operation), values)?,
                    taint,
                ));
            }
            Task::Binary(op, ty) => {
                let b = self.pop()?;
                let a = self.pop()?;
                let taint = a.is_tainted() || b.is_tainted();
                let a = a
                    .value
                    .clone()
                    .ok_or_else(|| anyhow!("control scalar required"))?;
                let b = b
                    .value
                    .clone()
                    .ok_or_else(|| anyhow!("control scalar required"))?;
                let value = match scalar_type(&ty)? {
                    ScalarType::Native => {
                        let a = a.cast(&ScalarType::Native)?.field_encoding()?;
                        let b = b.cast(&ScalarType::Native)?.field_encoding()?;
                        Value::Native(match op.as_str() {
                            "add" => a + b,
                            "sub" => a - b,
                            _ => a * b,
                        })
                    }
                    ScalarType::UInt(m) => scalars::unsigned_arithmetic(
                        match op.as_str() {
                            "add" => scalars::UnsignedOp::Add,
                            "sub" => scalars::UnsignedOp::Sub,
                            _ => scalars::UnsignedOp::Mul,
                        },
                        a,
                        b,
                        &m.to_str_radix(10),
                    )?,
                    _ => bail!("control arithmetic type"),
                };
                self.values.push(Tracked::scalar(value, taint));
            }
            Task::Eq(ty) => {
                let b = self.pop()?;
                let a = self.pop()?;
                let taint = a.is_tainted() || b.is_tainted();
                let a = ty.coerce(a)?;
                let b = ty.coerce(b)?;
                let equal = match &ty {
                    Type::Scalar(_) => a.value == b.value,
                    Type::Aggregate(token) => {
                        let left = &a
                            .aggregate
                            .as_ref()
                            .ok_or_else(|| anyhow!("control aggregate required"))?
                            .payload
                            .value;
                        let right = &b
                            .aggregate
                            .as_ref()
                            .ok_or_else(|| anyhow!("control aggregate required"))?
                            .payload
                            .value;
                        self.plan.registry.validate(token, left)?;
                        self.plan.registry.validate(token, right)?;
                        left == right
                    }
                    Type::Unit => bail!("control equality requires scalar or flat record operands"),
                };
                self.values.push(Tracked::scalar(Value::Bool(equal), taint));
            }
            Task::Curve(operation, count) => {
                ensure!(self.values.len() >= count, "control curve argument stack");
                let arguments = self.values.split_off(self.values.len() - count);
                let taint = arguments.iter().any(Tracked::is_tainted);
                let values = arguments
                    .into_iter()
                    .map(|argument| {
                        argument
                            .value
                            .ok_or_else(|| anyhow!("control curve scalar required"))
                    })
                    .collect::<Result<Vec<_>>>()?;
                self.values.push(Tracked::scalar(
                    evaluate_operation(curve_operation(&operation)?, values)?,
                    taint,
                ));
            }
            #[cfg(feature = "zkir-321")]
            Task::ForeignEncodedField(index) => {
                let value = self.pop()?;
                let taint = value.is_tainted();
                let Some(Value::Foreign(value)) = value.value else {
                    bail!("foreign encoded field projection requires a foreign value")
                };
                let encoding = value.encode()?;
                let field = encoding
                    .get(index)
                    .copied()
                    .ok_or_else(|| anyhow!("foreign encoded field index out of range"))?;
                self.values
                    .push(Tracked::scalar(Value::Native(field), taint));
            }
            Task::Bytes(operation, count) => {
                ensure!(self.values.len() >= count, "control byte argument stack");
                let arguments = self.values.split_off(self.values.len() - count);
                let taint = arguments.iter().any(Tracked::is_tainted);
                let values = arguments
                    .into_iter()
                    .map(|argument| {
                        argument
                            .value
                            .ok_or_else(|| anyhow!("control byte scalar required"))
                    })
                    .collect::<Result<Vec<_>>>()?;
                self.values.push(Tracked::scalar(
                    evaluate_operation(bytes_operation(&operation, count)?, values)?,
                    taint,
                ));
            }
            Task::FabDigest(parameters, result, expression, argument_kinds) => {
                let count = argument_kinds.len();
                ensure!(
                    self.values.len() >= count,
                    "control FAB digest argument stack"
                );
                let arguments = self.values.split_off(self.values.len() - count);
                let mut taint = false;
                let values = arguments
                    .into_iter()
                    .zip(argument_kinds)
                    .map(|(argument, kind)| {
                        taint |= argument.is_tainted();
                        match kind {
                            FabDigestArgumentKind::Scalar => argument
                                .value
                                .ok_or_else(|| anyhow!("control FAB digest scalar required")),
                            FabDigestArgumentKind::AggregateBytes { token, length } => {
                                let aggregate = argument.aggregate.as_ref().ok_or_else(|| {
                                    anyhow!("control FAB digest aggregate required")
                                })?;
                                ensure!(
                                    aggregate.token == token,
                                    "control FAB digest aggregate type mismatch"
                                );
                                aggregate_bytes_value(&aggregate.payload.value, length)
                            }
                        }
                    })
                    .collect::<Result<Vec<_>>>()?;
                let value = evaluate_operation((parameters, result, expression), values)?;
                self.values.push(Tracked::scalar(value, taint));
            }
            Task::Hash(domain) => {
                let b = self.pop()?;
                let a = self.pop()?;
                let taint = a.is_tainted() || b.is_tainted();
                let a = a
                    .value
                    .clone()
                    .ok_or_else(|| anyhow!("control hash scalar"))?
                    .field_encoding()?;
                let b = b
                    .value
                    .clone()
                    .ok_or_else(|| anyhow!("control hash scalar"))?
                    .field_encoding()?;
                let value =
                    transient_crypto::hash::transient_hash(&[canonical_field(&domain)?, a, b]);
                self.values
                    .push(Tracked::scalar(Value::Native(value), taint));
            }
            Task::EagerSelect(ty) => {
                let no = self.pop()?;
                let yes = self.pop()?;
                let c = self.pop()?;
                let bit = c.boolean()?;
                let taint = c.is_tainted() || yes.is_tainted() || no.is_tainted();
                let mut value = ty.coerce(if bit { yes } else { no })?;
                value.add_control_taint(taint);
                self.values.push(value);
            }
            Task::Choose(yes, no, ty, env, condition) => {
                let c = self.pop()?;
                let known = self.known_expression(&condition, &env)?;
                self.tasks.push(Task::Merge(
                    ty,
                    c.is_tainted() && known_bool(&known).is_none(),
                ));
                self.tasks
                    .push(Task::Eval(if c.boolean()? { yes } else { no }, env));
            }
            Task::Short(or, right, env) => {
                let left = self.pop()?;
                if left.boolean()? == or {
                    self.values.push(left);
                } else {
                    self.tasks.push(Task::Merge(
                        Type::Scalar(ScalarType::Bool),
                        left.is_tainted(),
                    ));
                    self.tasks.push(Task::Eval(right, env));
                }
            }
            Task::Args(id, args, index, values, env) => {
                if index < args.len() {
                    self.tasks
                        .push(Task::ArgValue(id, args.clone(), index, values, env.clone()));
                    self.tasks.push(Task::Eval(args[index].clone(), env));
                } else {
                    let function = self
                        .plan
                        .functions
                        .get(&id)
                        .ok_or_else(|| anyhow!("unknown control function"))?;
                    let mut local = BTreeMap::new();
                    for ((n, t), v) in function.signature.parameters.iter().zip(values) {
                        local.insert(n.clone(), t.coerce(v)?);
                    }
                    self.function_path.push(id.clone());
                    self.tasks.push(Task::Boundary(
                        function.signature.result.clone(),
                        self.continuation_taint,
                        Some(id.clone()),
                    ));
                    self.continuation_taint = false;
                    self.tasks.push(Task::Body(
                        function.body.clone(),
                        0,
                        Arc::new(local),
                        false,
                        function.signature.result.clone(),
                    ));
                }
            }
            Task::ArgValue(id, args, index, mut values, env) => {
                let mut value = self.pop()?;
                value.known = self.known_expression(&args[index], &env)?;
                values.push(value);
                self.tasks
                    .push(Task::Args(id, args, index + 1, values, env));
            }
            Task::WitnessArgs(name, site, arguments, index, values, env) => {
                if index < arguments.len() {
                    self.tasks.push(Task::WitnessArgValue(
                        name,
                        site,
                        arguments.clone(),
                        index,
                        values,
                        env.clone(),
                    ));
                    self.tasks.push(Task::Eval(arguments[index].clone(), env));
                } else {
                    let ordinal = if self.plan.mode.as_deref() == Some("native") {
                        self.next_native_active_call()?
                            .ok_or_else(|| anyhow!("unexpected native witness call"))?
                    } else {
                        self.bound_call_cursor
                    };
                    let signature = self
                        .plan
                        .signatures
                        .get(&name)
                        .ok_or_else(|| anyhow!("unknown typed witness signature"))?;
                    ensure!(
                        values.len() == signature.parameters.len(),
                        "typed witness argument count"
                    );
                    let _argument_reservation = reserve_witness_arguments(
                        &self.aggregate_budget,
                        &values,
                        &signature.parameters,
                    )?;
                    let mut arguments_json = serde_json::Map::new();
                    for (value, parameter) in values.iter().zip(&signature.parameters) {
                        let expected = parse_type(&parameter.type_token, &self.plan.registry)?;
                        let value = expected.coerce(value.clone())?;
                        arguments_json
                            .insert(parameter.name.clone(), value.canonical_json(&expected)?);
                    }
                    let path = self.function_path.clone();
                    let invocation = TypedInvocation {
                        ordinal,
                        name: name.clone(),
                        site: site.clone(),
                        path: path.clone(),
                        argument_charge: _argument_reservation.charge,
                    };
                    if self.plan.mode.as_deref() == Some("native") {
                        let expected = self
                            .plan
                            .bound_calls
                            .get(ordinal)
                            .ok_or_else(|| anyhow!("unexpected native witness call"))?;
                        ensure!(
                            text(expected, "ordinal")? == ordinal.to_string()
                                && text(expected, "site")? == site
                                && text(expected, "name")? == name
                                && list(expected, "path")?
                                    == &path.iter().cloned().map(Json::String).collect::<Vec<_>>()
                                && text(expected, "resultType")? == signature.result_type,
                            "native witness call order or source path mismatch"
                        );
                    }
                    let request_id = NEXT_TYPED_REQUEST_ID
                        .try_update(Ordering::Relaxed, Ordering::Relaxed, |current| {
                            current.checked_add(1)
                        })
                        .map_err(|_| anyhow!("control request id exhausted"))?;
                    let mut arguments_value = Json::Object(arguments_json);
                    let request = if self.plan.ledger_calls.contains_key(&ordinal) {
                        ensure!(
                            self.native_target_context_id.is_some(),
                            "native ledger callback requires an authenticated contract target"
                        );
                        Json::Null
                    } else {
                        let request_result = self
                            .host
                            .as_mut()
                            .ok_or_else(|| anyhow!("invalid control host state"))?
                            .begin_typed_input(
                                &name,
                                request_id,
                                signature,
                                &arguments_value,
                                &self.plan.registry,
                            );
                        request_result?.ok_or_else(|| anyhow!("typed witness requires provider"))?
                    };
                    wipe_json(&mut arguments_value);
                    self.bound_call_cursor += 1;
                    self.pending = Some(Pending {
                        id: request_id,
                        name: name.clone(),
                        ty: signature.result_type.clone(),
                        request,
                        typed: Some(invocation),
                    });
                    self.trace.push(format!("witness:{name}"));
                    self.phase = Phase::Waiting;
                }
            }
            Task::WitnessArgValue(name, site, arguments, index, mut values, env) => {
                let value = self.pop()?;
                values.push(value);
                self.tasks.push(Task::WitnessArgs(
                    name,
                    site,
                    arguments,
                    index + 1,
                    values,
                    env,
                ));
            }
            Task::Composite(token, leaves, index, values, env) => {
                if index < leaves.len() {
                    self.tasks.push(Task::CompositeValue(
                        token,
                        leaves.clone(),
                        index,
                        values,
                        env.clone(),
                    ));
                    self.tasks.push(Task::Eval(leaves[index].clone(), env));
                } else {
                    let leaf_types = self.plan.registry.source_leaf_types(&token)?;
                    let leaf_json = values
                        .iter()
                        .zip(&leaf_types)
                        .map(|(value, expected)| {
                            ensure!(
                                value.aggregate.is_none(),
                                "nested aggregate leaf unsupported by control composite"
                            );
                            let ty = parse_type(expected, &self.plan.registry)?;
                            value.canonical_json(&ty)
                        })
                        .collect::<Result<Vec<_>>>()?;
                    let value = self.plan.registry.from_source_leaves(&token, &leaf_json)?;
                    let widths = self.plan.registry.source_leaf_widths(&token)?;
                    ensure!(
                        widths.len() == values.len(),
                        "control aggregate source leaf width mismatch"
                    );
                    let taints = values
                        .iter()
                        .zip(widths)
                        .flat_map(|(value, width)| std::iter::repeat_n(value.is_tainted(), width))
                        .collect::<Vec<_>>();
                    let control_taint = values.is_empty() && self.continuation_taint;
                    let payload = AggregatePayload::from_owned(value, &self.aggregate_budget)?;
                    self.values
                        .push(Tracked::aggregate(token, payload, taints, control_taint));
                }
            }
            Task::CompositeValue(token, leaves, index, mut values, env) => {
                values.push(self.pop()?);
                self.tasks
                    .push(Task::Composite(token, leaves, index + 1, values, env));
            }
            Task::Project(projection, expected_type) => {
                let aggregate = self.pop()?;
                let source = aggregate
                    .aggregate
                    .as_ref()
                    .ok_or_else(|| anyhow!("control projection aggregate required"))?;
                let (actual_type, value, range) = self.plan.registry.project_with_range(
                    &source.token,
                    &source.payload.value,
                    &projection,
                )?;
                ensure!(
                    actual_type == expected_type,
                    "control projection type changed"
                );
                let projected = parse_type(&actual_type, &self.plan.registry)?;
                let enum_taint = projection.kind == "enumField"
                    && aggregate.leaf_taints.first().copied().unwrap_or(false);
                match projected {
                    Type::Unit => {
                        let mut result = tracked_from_json(
                            &self.plan.registry,
                            &actual_type,
                            &value,
                            false,
                            &self.aggregate_budget,
                        )?;
                        result.control_taint = aggregate.control_taint || enum_taint;
                        self.values.push(result);
                    }
                    Type::Scalar(_) => {
                        let mut result = tracked_from_json(
                            &self.plan.registry,
                            &actual_type,
                            &value,
                            false,
                            &self.aggregate_budget,
                        )?;
                        result.taint = aggregate
                            .leaf_taints
                            .get(range.start)
                            .copied()
                            .unwrap_or(false);
                        result.control_taint = aggregate.control_taint || enum_taint;
                        if result.is_tainted() {
                            result.known = None;
                        }
                        self.values.push(result);
                    }
                    Type::Aggregate(token) => {
                        let leaf_taints = aggregate
                            .leaf_taints
                            .get(range)
                            .ok_or_else(|| anyhow!("invalid aggregate projection range"))?
                            .to_vec();
                        let payload = AggregatePayload::from_owned(value, &self.aggregate_budget)?;
                        self.values.push(Tracked::aggregate(
                            token,
                            payload,
                            leaf_taints,
                            aggregate.control_taint || enum_taint,
                        ));
                    }
                }
            }
            Task::Index(expected_type) => {
                let index_value = self.pop()?;
                let index_taint = index_value.is_tainted();
                let aggregate = self.pop()?;
                let source = aggregate
                    .aggregate
                    .as_ref()
                    .ok_or_else(|| anyhow!("control index aggregate required"))?;
                let index = match index_value.value.as_ref() {
                    Some(Value::Native(value)) => crate::field_decimal(*value),
                    Some(Value::UInt { number, .. }) => number.to_string(),
                    _ => bail!("control index requires Native or UInt"),
                };
                let index = index
                    .parse::<usize>()
                    .map_err(|_| anyhow!("control index out of range"))?;
                let (actual_type, value, range) = self.plan.registry.index_with_range(
                    &source.token,
                    &source.payload.value,
                    index,
                )?;
                ensure!(actual_type == expected_type, "control index type changed");
                let projected = parse_type(&actual_type, &self.plan.registry)?;
                match projected {
                    Type::Unit => {
                        let mut result = tracked_from_json(
                            &self.plan.registry,
                            &actual_type,
                            &value,
                            false,
                            &self.aggregate_budget,
                        )?;
                        result.control_taint = aggregate.control_taint || index_taint;
                        self.values.push(result);
                    }
                    Type::Scalar(_) => {
                        let mut result = tracked_from_json(
                            &self.plan.registry,
                            &actual_type,
                            &value,
                            false,
                            &self.aggregate_budget,
                        )?;
                        result.taint = aggregate
                            .leaf_taints
                            .get(range.start)
                            .copied()
                            .unwrap_or(false);
                        result.control_taint = aggregate.control_taint || index_taint;
                        if result.is_tainted() {
                            result.known = None;
                        }
                        self.values.push(result);
                    }
                    Type::Aggregate(token) => {
                        let leaf_taints = aggregate
                            .leaf_taints
                            .get(range)
                            .ok_or_else(|| anyhow!("invalid aggregate index range"))?
                            .to_vec();
                        let payload = AggregatePayload::from_owned(value, &self.aggregate_budget)?;
                        self.values.push(Tracked::aggregate(
                            token,
                            payload,
                            leaf_taints,
                            aggregate.control_taint || index_taint,
                        ));
                    }
                }
            }
            Task::Body(body, index, env, control, result) => {
                if let Some(stmt) = body.statements.get(index) {
                    match stmt {
                        Stmt::Bind(n, t, x) => {
                            self.tasks.push(Task::Bind(
                                n.clone(),
                                t.clone(),
                                body.clone(),
                                index + 1,
                                env.clone(),
                                control,
                                result,
                                x.clone(),
                            ));
                            self.tasks.push(Task::Eval(x.clone(), env));
                        }
                        Stmt::Evaluate(x) => {
                            self.tasks.push(Task::Body(
                                body.clone(),
                                index + 1,
                                env.clone(),
                                control,
                                result,
                            ));
                            self.tasks.push(Task::Discard);
                            self.tasks.push(Task::Eval(x.clone(), env));
                        }
                        Stmt::Assert(x, message) => {
                            self.tasks.push(Task::Body(
                                body.clone(),
                                index + 1,
                                env.clone(),
                                control,
                                result,
                            ));
                            self.tasks.push(Task::Assert(message.clone()));
                            self.tasks.push(Task::Eval(x.clone(), env));
                        }
                        Stmt::Return(x) => {
                            self.tasks.push(Task::Return(result, control));
                            if let Some(x) = x {
                                self.tasks.push(Task::Eval(x.clone(), env));
                            } else {
                                self.values.push(Tracked::unit());
                            }
                        }
                        Stmt::If(c, yes, no) => {
                            self.tasks.push(Task::Branch(
                                yes.clone(),
                                no.clone(),
                                body.clone(),
                                index + 1,
                                env.clone(),
                                control,
                                result,
                                c.clone(),
                            ));
                            self.tasks.push(Task::Eval(c.clone(), env));
                        }
                        Stmt::Stage(cap, key, ty, x) => {
                            self.tasks.push(Task::Body(
                                body.clone(),
                                index + 1,
                                env.clone(),
                                control,
                                result,
                            ));
                            self.tasks
                                .push(Task::Stage(cap.clone(), key.clone(), ty.clone()));
                            self.tasks.push(Task::Eval(x.clone(), env));
                        }
                    }
                }
            }
            Task::Bind(n, ty, body, index, env, control, result, expression) => {
                let mut value = self.pop()?;
                value.known = self.known_expression(&expression, &env)?;
                let value = ty.coerce(value)?;
                let mut local = (*env).clone();
                local.insert(n, value);
                self.tasks
                    .push(Task::Body(body, index, Arc::new(local), control, result));
            }
            Task::Discard => {
                self.pop()?;
            }
            Task::Assert(message) => {
                if !self.pop()?.boolean()? {
                    if let Some(message) = message {
                        return Err(anyhow::Error::new(AuthoredAssertionFailure(message)));
                    }
                    bail!("control assertion failed");
                }
            }
            Task::Return(ty, control) => {
                let mut value = ty.coerce(self.pop()?)?;
                value.add_control_taint(control || self.continuation_taint);
                while let Some(task) = self.tasks.pop() {
                    if let Task::Boundary(_, outer_taint, function_id) = task {
                        if let Some(function_id) = function_id {
                            ensure!(
                                self.function_path.pop().as_deref() == Some(function_id.as_str()),
                                "invalid control call path"
                            );
                        }
                        self.continuation_taint = outer_taint;
                        self.values.push(value);
                        return Ok(());
                    }
                }
                bail!("invalid control return boundary")
            }
            Task::Boundary(ty, outer_taint, function_id) => {
                if let Some(function_id) = function_id {
                    ensure!(
                        self.function_path.pop().as_deref() == Some(function_id.as_str()),
                        "invalid control call path"
                    );
                }
                let mut value = Tracked::unit();
                value.add_control_taint(self.continuation_taint);
                self.continuation_taint = outer_taint;
                self.values.push(ty.coerce(value)?);
            }
            Task::Finish => {
                let value = self.pop()?;
                if self.plan.mode.as_deref() == Some("native") {
                    if self.guarded_native_binding() {
                        self.consume_trailing_inactive_native_calls()?;
                        ensure!(
                            self.bound_call_cursor == self.plan.bound_calls.len(),
                            "native witness call sequence is incomplete"
                        );
                        self.clear_native_guard_values();
                    } else {
                        ensure!(
                            self.bound_call_cursor == self.plan.bound_calls.len()
                                && self.witness_records.len() == self.plan.bound_calls.len(),
                            "native witness call sequence is incomplete"
                        );
                    }
                }
                let legacy_unit_result = self.plan.schema_version == 1
                    && self.plan.functions[&self.plan.entry].signature.result == Type::Unit
                    && value.value.is_none()
                    && value.aggregate.is_none();
                ensure!(
                    legacy_unit_result || !value.is_tainted(),
                    "undisclosed control output"
                );
                let actual = match (&value.value, &value.aggregate) {
                    (Some(value), None) => Type::Scalar(value.scalar_type()),
                    (None, Some(aggregate)) => Type::Aggregate(aggregate.token.clone()),
                    (None, None) => Type::Unit,
                    _ => bail!("invalid control result value"),
                };
                ensure!(
                    actual == self.plan.functions[&self.plan.entry].signature.result,
                    "control exported value type mismatch"
                );
                let result_charge = if value.aggregate.is_some() {
                    let charge = value.materialization_charge(0)?;
                    ensure!(
                        charge <= MAX_BYTES,
                        "control public result materialization limit exceeded"
                    );
                    Some(charge)
                } else {
                    None
                };
                let result_reservation = result_charge
                    .map(|charge| AggregateReservation::new(&self.aggregate_budget, charge))
                    .transpose()?;
                let result = value.public_json();
                self.phase =
                    Phase::Complete(json!({"abiVersion":1,"status":"completed","result":result}));
                self.completed_result_charge = result_charge;
                self.completed_phase_reservation = result_reservation;
                self.tasks.clear();
                self.values.clear();
            }
            Task::Branch(yes, no, rest, index, env, control, result, condition) => {
                let c = self.pop()?;
                let constants = known_environment(&env);
                let mut abstractor = Abstractor {
                    functions: &self.plan.functions,
                    fuel: &mut self.remaining,
                };
                let known = abstractor.expression(&condition, &constants)?;
                let guard = c.is_tainted() && known_bool(&known).is_none();
                let may_return = !abstractor
                    .body(&yes, &constants, &result)?
                    .returns
                    .is_empty()
                    || !abstractor
                        .body(&no, &constants, &result)?
                        .returns
                        .is_empty();
                let continuation = control || (guard && may_return);
                self.continuation_taint |= guard && may_return;
                self.tasks.push(Task::Body(
                    rest,
                    index,
                    env.clone(),
                    continuation,
                    result.clone(),
                ));
                self.tasks.push(Task::Body(
                    if c.boolean()? { yes } else { no },
                    0,
                    env,
                    control || guard,
                    result,
                ));
            }
            Task::Stage(capability, key, ty) => {
                let value = self.pop()?;
                let stage_type = parse_type(&ty, &self.plan.registry)?;
                let value = stage_type.coerce(value)?;
                let reservation = if self.plan.schema_version == 2 {
                    let charge = value
                        .materialization_charge(key.len())?
                        .checked_mul(2)
                        .ok_or_else(|| anyhow!("control stage size overflow"))?;
                    ensure!(
                        charge <= MAX_BYTES,
                        "control stage materialization limit exceeded"
                    );
                    Some(AggregateReservation::new(&self.aggregate_budget, charge)?)
                } else {
                    None
                };
                let value = value.canonical_json(&stage_type)?;
                self.stage_from_source(
                    host::Stage {
                        abi_version: if self.plan.schema_version == 1 { 1 } else { 2 },
                        operation: host::STAGE.into(),
                        capability,
                        key,
                        ty,
                        value,
                    },
                    reservation,
                )?;
            }
        }
        ensure!(
            self.tasks.len() <= 65536 && self.values.len() <= 16384,
            "control continuation limit"
        );
        Ok(())
    }
}

impl Drop for Session {
    fn drop(&mut self) {
        self.clear_writes();
        self.clear_native_guard_values();
    }
}

#[cfg(test)]
mod aggregate_budget_tests {
    use super::{AggregateBudget, AggregatePayload, Tracked, reserve_witness_arguments};
    use serde_json::json;
    use std::sync::Arc;

    #[test]
    fn aggregate_aliases_share_one_retained_payload_charge() {
        let budget = AggregateBudget::with_limits(512, 512, 16);
        let value = json!({"kind":"struct","fields":{"secret":"987654321"}});
        let payload = AggregatePayload::from_borrowed(&value, &budget).unwrap();
        let charged = budget.used.load(std::sync::atomic::Ordering::Acquire);
        assert!(charged > 0);
        let alias = Arc::clone(&payload);
        drop(payload);
        assert_eq!(
            budget.used.load(std::sync::atomic::Ordering::Acquire),
            charged
        );
        drop(alias);
        assert_eq!(budget.used.load(std::sync::atomic::Ordering::Acquire), 0);
    }

    #[test]
    fn aggregate_node_and_storage_caps_reject_before_retaining_values() {
        let node_budget = AggregateBudget::with_limits(4096, 4096, 2);
        let too_many_nodes = json!([{"value":0}]);
        assert!(AggregatePayload::from_borrowed(&too_many_nodes, &node_budget).is_err());
        assert_eq!(
            node_budget.used.load(std::sync::atomic::Ordering::Acquire),
            0
        );

        let storage_budget = AggregateBudget::with_limits(4096, 96, 16);
        let too_large = json!({"value":"a string larger than the configured test storage bound"});
        assert!(AggregatePayload::from_borrowed(&too_large, &storage_budget).is_err());
        assert_eq!(
            storage_budget
                .used
                .load(std::sync::atomic::Ordering::Acquire),
            0
        );
    }

    #[test]
    fn aliased_witness_arguments_reserve_total_copy_charge_before_materialization() {
        let budget = AggregateBudget::with_limits(512, 512, 16);
        let value = json!({"kind":"struct","fields":{"secret":"123456789"}});
        let payload = AggregatePayload::from_borrowed(&value, &budget).unwrap();
        let tracked = Tracked::aggregate("Aggregate:Claim".into(), payload, vec![false], false);
        let values = vec![tracked.clone(), tracked];
        let parameters = vec![
            crate::witness::Parameter {
                name: "left".into(),
                type_token: "Aggregate:Claim".into(),
            },
            crate::witness::Parameter {
                name: "right".into(),
                type_token: "Aggregate:Claim".into(),
            },
        ];
        let before = budget.used.load(std::sync::atomic::Ordering::Acquire);
        assert!(reserve_witness_arguments(&budget, &values, &parameters).is_err());
        assert_eq!(
            budget.used.load(std::sync::atomic::Ordering::Acquire),
            before
        );
    }
}

#[cfg(test)]
mod completed_invocation_tests {
    #[test]
    fn typed_record_ledger_inputs_follow_fab_field_order() {
        let plan = serde_json::json!({
            "circuit": {"inputs": []},
            "reads": [{
                "name": "memo", "type": "Composite",
                "components": [
                    {"name": "memo_amount", "type": "Native"},
                    {"name": "memo_payload", "type": "Bytes<32>"},
                    {"name": "memo_recipient", "type": "JubjubPoint"}
                ]
            }]
        });
        let (inputs, _) = super::expected_ledger_inputs(&plan).unwrap();
        let names: Vec<_> = inputs
            .iter()
            .map(|input| input["name"].as_str().unwrap())
            .collect();
        assert_eq!(
            names,
            [
                "memo_amount",
                "_noctium_bytes_memo_payload_0",
                "_noctium_bytes_memo_payload_1",
                "_noctium_jubjub_read_memo_recipient_0",
                "_noctium_jubjub_read_memo_recipient_1"
            ]
        );
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    fn typed_public_prologue_uses_all_byte_and_curve_projection_reads() {
        let mut plan: serde_json::Value = serde_json::from_str(include_str!(
            "../tests/fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.registerWithKey.impact.json"
        )).unwrap();
        let control: serde_json::Value = serde_json::from_str(include_str!(
            "../tests/fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.registerWithKey.witness.control.json"
        )).unwrap();
        let binding: serde_json::Value =
            serde_json::from_str(control["binding"].as_str().unwrap()).unwrap();
        let (expected, bytes32_abi) = super::expected_ledger_inputs(&plan).unwrap();
        assert_eq!(
            bytes32_abi,
            [("accountId".into(), super::PublicBytesAbi::LegacyBytes)].into()
        );
        assert_eq!(
            expected,
            binding["ledgerInputs"].as_array().unwrap().clone()
        );
        assert_eq!(
            super::public_byte_relation_abis(&binding, &binding["nativeRelation"]).unwrap(),
            bytes32_abi
        );
        plan["reads"][31]["name"] = serde_json::json!("changed_high_byte_projection");
        assert!(super::expected_ledger_inputs(&plan).is_err());
    }

    #[test]
    fn typed_public_bytes_prologue_uses_bounded_native_chunks() {
        for (length, high, low, high_bits) in [
            (
                32,
                "_noctium_bytes32_probe_high",
                "_noctium_bytes32_probe_low31",
                8,
            ),
            (33, "_noctium_bytes_probe_0", "_noctium_bytes_probe_1", 16),
        ] {
            let source_type = format!("Bytes<{length}>");
            let circuit_inputs = json!([
                {"name":"empty","type":"Bytes<0>","visibility":"public"},
                {"name":"probe","type":source_type,"visibility":"public"}
            ]);
            let plan = json!({
                "circuit":{"inputs":circuit_inputs},
                "reads":[{"name":"probe","type":source_type}]
            });
            let (ledger_inputs, abi) = super::expected_ledger_inputs(&plan).unwrap();
            assert!(ledger_inputs.is_empty());
            assert_eq!(
                abi,
                [("probe".into(), super::PublicBytesAbi::PackedFields)].into()
            );

            let high = format!("%input_{high}");
            let low = format!("%input_{low}");
            let mut relation = json!({
                "version":{"major":3,"minor":2},
                "instructions":[
                    {"op":"public_input","output":high,"type":"Scalar<BLS12-381>"},
                    {"op":"constrain_bits","val":high,"bits":high_bits},
                    {"op":"public_input","output":low,"type":"Scalar<BLS12-381>"},
                    {"op":"constrain_bits","val":low,"bits":248}
                ]
            });
            let binding = json!({"circuitInputs":circuit_inputs});
            let inputs = std::collections::BTreeMap::from([
                (
                    "empty".to_owned(),
                    ("Bytes<0>".to_owned(), "public".to_owned()),
                ),
                ("probe".to_owned(), (source_type, "public".to_owned())),
            ]);
            let order = vec![
                ("empty".to_owned(), "public".to_owned()),
                ("probe".to_owned(), "public".to_owned()),
            ];
            super::validate_relation_inputs(&relation, &inputs, &order, &[]).unwrap();
            assert_eq!(
                super::public_byte_relation_abis(&binding, &relation).unwrap(),
                abi
            );

            relation["instructions"][1]["bits"] = json!(high_bits + 1);
            assert!(super::validate_relation_inputs(&relation, &inputs, &order, &[]).is_err());
        }
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    fn byte_storage_reads_bind_ordered_bounded_chunks_and_empty_defaults() {
        let impact: Json = serde_json::from_str(include_str!(
            "../tests/fixtures/byte-storage/321/BytesStorage.update.impact.json"
        ))
        .unwrap();
        let reads = impact["reads"].as_array().unwrap();
        let (expected, bytes32_abi) = super::expected_ledger_inputs(&impact).unwrap();
        assert_eq!(
            bytes32_abi,
            [("domain".into(), super::PublicBytesAbi::PackedFields)].into()
        );
        let byte_reads: Vec<_> = reads
            .iter()
            .filter(|read| read.get("projections").is_some())
            .collect();
        assert!(byte_reads.iter().any(|read| {
            read["type"] == "Bytes<0>" && read["projections"].as_array().unwrap().is_empty()
        }));
        for read in byte_reads.iter().filter(|read| read["type"] == "Bytes<0>") {
            let prefix = format!("_noctium_bytes_{}_", read["name"].as_str().unwrap());
            assert!(expected.iter().all(|input| {
                !input["name"]
                    .as_str()
                    .is_some_and(|name| name.starts_with(&prefix))
            }));
        }
        let expected_byte_bindings: Vec<_> = byte_reads
            .iter()
            .flat_map(|read| read["projections"].as_array().unwrap())
            .map(|input| {
                json!({
                    "name":input["name"],
                    "type":input["type"],
                    "visibility":"public"
                })
            })
            .collect();
        let actual_byte_bindings: Vec<_> = expected
            .iter()
            .filter(|input| {
                input["name"]
                    .as_str()
                    .is_some_and(|name| name.starts_with("_noctium_bytes_"))
            })
            .cloned()
            .collect();
        assert_eq!(actual_byte_bindings, expected_byte_bindings);

        let mut relation_inputs = BTreeMap::new();
        let mut input_order = Vec::new();
        let mut instructions = Vec::new();
        for input in &expected {
            let name = input["name"].as_str().unwrap().to_owned();
            let ty = input["type"].as_str().unwrap().to_owned();
            let visibility = input["visibility"].as_str().unwrap().to_owned();
            relation_inputs.insert(name.clone(), (ty.clone(), visibility.clone()));
            input_order.push((name.clone(), visibility));
            instructions.push(json!({
                "op":"public_input",
                "output":format!("%input_{name}"),
                "type":"Scalar<BLS12-381>"
            }));
            match ScalarType::parse(&ty).unwrap() {
                ScalarType::UInt(maximum) => instructions.push(json!({
                    "op":"constrain_bits",
                    "val":format!("%input_{name}"),
                    "bits":maximum.bits().max(1)
                })),
                ScalarType::Bool => instructions.push(json!({
                    "op":"constrain_to_boolean",
                    "val":format!("%input_{name}")
                })),
                _ => {}
            }
        }
        let relation = json!({
            "version":{"major":3,"minor":2},
            "instructions":instructions
        });
        super::validate_relation_inputs(&relation, &relation_inputs, &input_order, &[]).unwrap();

        let wrong_width = input_order
            .iter()
            .find_map(|(name, _)| {
                let ty = &relation_inputs[name].0;
                let ScalarType::UInt(maximum) = ScalarType::parse(ty).ok()? else {
                    return None;
                };
                Some((name, maximum.bits().max(1)))
            })
            .unwrap();
        let mut bad_relation = relation.clone();
        for instruction in bad_relation["instructions"].as_array_mut().unwrap() {
            if instruction["op"] == "constrain_bits"
                && instruction["val"] == format!("%input_{}", wrong_width.0)
            {
                instruction["bits"] = json!(wrong_width.1 - 1);
                break;
            }
        }
        assert!(
            super::validate_relation_inputs(&bad_relation, &relation_inputs, &input_order, &[])
                .is_err()
        );

        let read_index = reads
            .iter()
            .position(|read| {
                read["type"] == "Bytes<33>"
                    && read["projections"]
                        .as_array()
                        .is_some_and(|items| items.len() == 2)
            })
            .unwrap();
        let mut wrong_order = impact.clone();
        wrong_order["reads"][read_index]["projections"]
            .as_array_mut()
            .unwrap()
            .swap(0, 1);
        assert!(super::expected_ledger_inputs(&wrong_order).is_err());

        let mut wrong_range = impact.clone();
        let first_type = wrong_range["reads"][read_index]["projections"][0]["type"]
            .as_str()
            .unwrap()
            .to_owned();
        wrong_range["reads"][read_index]["projections"][0]["type"] =
            json!(if first_type == "UIntRange<65536>" {
                "UIntRange<256>"
            } else {
                "UIntRange<65536>"
            });
        assert!(super::expected_ledger_inputs(&wrong_range).is_err());

        let mut wrong_length = impact;
        wrong_length["reads"][read_index]["type"] = json!("Bytes<0>");
        assert!(super::expected_ledger_inputs(&wrong_length).is_err());
    }

    use super::{AuthenticatedNativeTarget, InvocationTarget, ScalarType, Session, TypedResponse};
    use crate::{control::Plan, host};
    use serde_json::{Value as Json, json};
    use sha2::{Digest, Sha256};
    use std::collections::{BTreeMap, BTreeSet};
    use std::sync::atomic::Ordering;

    #[cfg(feature = "zkir-320")]
    const SOURCE_PLAN: &str = include_str!(
        "../tests/fixtures/witness/320/TypedWitness.ScalarWitness.claim.witness.control.json"
    );
    #[cfg(feature = "zkir-321")]
    const SOURCE_PLAN: &str = include_str!(
        "../tests/fixtures/witness/321/TypedWitness.ScalarWitness.claim.witness.control.json"
    );
    #[cfg(feature = "zkir-320")]
    const PAIR_PLAN: &str = include_str!(
        "../tests/fixtures/witness/320/TypedWitness.PairWitness.claim.witness.control.json"
    );
    #[cfg(feature = "zkir-321")]
    const PAIR_PLAN: &str = include_str!(
        "../tests/fixtures/witness/321/TypedWitness.PairWitness.claim.witness.control.json"
    );

    fn source_context(plan: &Plan, attempt_id: &str) -> host::Context {
        let mut operations = BTreeMap::<String, host::Operation>::new();
        let mut providers = Vec::new();
        let mut capability_map = BTreeMap::<String, (String, BTreeSet<String>)>::new();
        for signature in plan.signatures.values() {
            let mut argument_schema = signature
                .parameters
                .iter()
                .map(|parameter| (parameter.name.clone(), parameter.type_token.clone()))
                .collect::<BTreeMap<_, _>>();
            if signature.operation == host::READ {
                argument_schema.insert("key".into(), "Key".into());
            }
            operations.insert(
                signature.operation.clone(),
                host::Operation {
                    operation: signature.operation.clone(),
                    argument_schema,
                    result_schema: signature.result_type.clone(),
                },
            );
            let prefix = signature
                .private_key
                .as_deref()
                .map(|key| {
                    format!(
                        "{}/",
                        key.rsplit_once('/').map(|(root, _)| root).unwrap_or(key)
                    )
                })
                .unwrap_or_else(|| "lookup/".into());
            let entry = capability_map
                .entry(signature.capability.clone())
                .or_insert_with(|| (prefix.clone(), BTreeSet::new()));
            assert_eq!(entry.0, prefix);
            entry.1.insert(signature.operation.clone());
            if signature.private_key.is_some() {
                entry.1.insert(host::STAGE.into());
            }
            providers.push(host::Provider {
                input: signature.name.clone(),
                operation: signature.operation.clone(),
                capability: signature.capability.clone(),
                arguments: signature
                    .private_key
                    .as_ref()
                    .map(|key| BTreeMap::from([("key".into(), json!(key))]))
                    .unwrap_or_default(),
            });
        }
        capability_map
            .entry("commit".into())
            .or_insert_with(|| ("cache/".into(), BTreeSet::new()))
            .1
            .insert(host::CAS.into());
        capability_map
            .entry("private".into())
            .or_insert_with(|| ("cache/".into(), BTreeSet::new()))
            .1
            .insert(host::STAGE.into());
        let capabilities = capability_map
            .into_iter()
            .map(|(id, (key_prefix, operations))| host::Capability {
                id,
                namespace: "noctium".into(),
                key_prefix,
                operations: operations.into_iter().collect(),
            })
            .collect();
        host::Context {
            protocol_version: 1,
            namespace: "noctium".into(),
            base_revision: "fixture-r0".into(),
            attempt_id: attempt_id.into(),
            capabilities,
            operations: operations.into_values().collect(),
            providers,
            commit_capability: "commit".into(),
            limits: host::Limits::default(),
        }
    }

    fn complete_source(session: &mut Session, attempt_id: &str) {
        for _ in 0..64 {
            let status = session.advance().unwrap();
            if status["status"] == "completed" {
                return;
            }
            assert_eq!(status["status"], "need_host");
            let request = &status["request"];
            let value = match request["name"].as_str().unwrap() {
                "cache" => {
                    session.private_request().unwrap()["invocationWrites"]["cache/last"]["value"]
                        .clone()
                }
                "lookup" => json!("14"),
                other => panic!("unexpected provider {other}"),
            };
            let response: TypedResponse = serde_json::from_value(json!({
                "protocolVersion":2,
                "requestId":request["requestId"],
                "attemptId":attempt_id,
                "outcome":"value",
                "operation":request["operation"],
                "capability":request["capability"],
                "schema":request["schema"],
                "value":value,
            }))
            .unwrap();
            session.resume_typed(response).unwrap();
        }
        panic!("control source call sequence exceeded test bound");
    }

    fn host_plan(result_type: &str, value: Json) -> Json {
        json!({
            "schemaVersion": 2,
            "kind": "host-control",
            "name": "genericSourceControlTest",
            "types": [],
            "mode": "host",
            "binding": null,
            "inputs": [],
            "witnesses": [],
            "functions": [{
                "id": "main",
                "name": "main",
                "parameters": [],
                "resultType": result_type,
                "body": [{"tag": "return", "value": value}]
            }],
            "entry": "main",
            "limits": {"maxSteps": 256}
        })
    }

    fn run_host_plan(plan: Json) -> Json {
        let parsed = Plan::parse(&plan, None).unwrap();
        let context = source_context(&parsed, &"d".repeat(64));
        let mut session = Session::from_json(plan, BTreeMap::new(), context).unwrap();
        session.advance().unwrap()
    }

    #[test]
    fn generic_fixed_bytes_execute_operations_and_reject_bad_bounds() {
        let source = json!({"tag":"bytesLiteral","length":4,"values":[1,2,3,4]});
        let reverse = json!({
            "tag":"bytes",
            "operation":"reverseBytes:4",
            "arguments":[source]
        });
        let slice = json!({
            "tag":"bytes",
            "operation":"sliceBytes:4:1:3",
            "arguments":[reverse]
        });
        let joined = json!({
            "tag":"bytes",
            "operation":"concatBytes:2:0",
            "arguments":[slice,{"tag":"bytesLiteral","length":0,"values":[]}]
        });
        let nonempty_plan = host_plan("Bytes<2>", joined);
        let completed = run_host_plan(nonempty_plan.clone());
        assert_eq!(completed["status"], "completed");
        assert_eq!(completed["result"], json!({"kind":"bytes","values":[3,2]}));

        let mut out_of_bounds = nonempty_plan;
        out_of_bounds["functions"][0]["body"][0]["value"]["arguments"][0]["operation"] =
            json!("sliceBytes:4:1:5");
        assert!(Plan::parse(&out_of_bounds, None).is_err());

        let empty = json!({
            "tag":"bytes",
            "operation":"sliceBytes:4:2:2",
            "arguments":[{"tag":"bytesLiteral","length":4,"values":[9,8,7,6]}]
        });
        let completed = run_host_plan(host_plan("Bytes<0>", empty));
        assert_eq!(completed["status"], "completed");
        assert_eq!(completed["result"], json!({"kind":"bytes","values":[]}));
    }

    #[test]
    fn generic_scalar_from_bytes_reduces_directly_and_checks_control_routes() {
        const JUBJUB_ORDER: &str =
            "6554484396890773809930967563523245729705921265872317281365359162392183254199";
        let native_modulus =
            num_bigint::BigUint::parse_bytes(crate::MODULUS.as_bytes(), 10).unwrap();
        let jubjub_order = num_bigint::BigUint::parse_bytes(JUBJUB_ORDER.as_bytes(), 10).unwrap();
        let raw_value = &native_modulus + &jubjub_order;
        let mut raw_bytes = raw_value.to_bytes_le();
        raw_bytes.resize(64, 0);
        let literal =
            |values: Vec<u8>| json!({"tag":"bytesLiteral","length":values.len(),"values":values});
        let direct = |ty: &str, length: usize, value: Json| json!({"tag":"fromBytes","type":ty,"length":length,"value":value});

        let native = run_host_plan(host_plan(
            "Native",
            direct("Native", raw_bytes.len(), literal(raw_bytes.clone())),
        ));
        assert_eq!(native["status"], "completed");
        assert_eq!(native["result"], json!(jubjub_order.to_str_radix(10)));

        let jubjub = run_host_plan(host_plan(
            "JubjubScalar",
            direct("JubjubScalar", raw_bytes.len(), literal(raw_bytes.clone())),
        ));
        assert_eq!(jubjub["status"], "completed");
        assert_eq!(
            jubjub["result"],
            json!({"kind":"jubjubScalar","value":(&native_modulus % &jubjub_order).to_str_radix(10)})
        );

        let helper_route = json!({
            "tag":"bytes",
            "operation":"fromBytes:JubjubScalar:64",
            "arguments":[literal(raw_bytes)]
        });
        let helper = run_host_plan(host_plan("JubjubScalar", helper_route));
        assert_eq!(helper["status"], "completed");
        assert_eq!(helper["result"], jubjub["result"]);

        for enabled in [true, false] {
            let mut plan = host_plan("Native", direct("Native", 0, literal(Vec::new())));
            plan["functions"][0]["body"] = json!([
                {"tag":"assert","condition":{"tag":"bool","value":enabled}},
                {"tag":"return","value":direct("Native", 0, literal(Vec::new()))}
            ]);
            let result = run_host_plan(plan);
            assert_eq!(
                result["status"],
                if enabled { "completed" } else { "failed" }
            );
            if enabled {
                assert_eq!(result["result"], json!("0"));
            }
        }
        let empty_scalar = run_host_plan(host_plan(
            "JubjubScalar",
            direct("JubjubScalar", 0, literal(Vec::new())),
        ));
        assert_eq!(empty_scalar["status"], "completed");
        assert_eq!(
            empty_scalar["result"],
            json!({"kind":"jubjubScalar","value":"0"})
        );

        for malformed in [
            direct("JubjubPoint", 0, literal(Vec::new())),
            direct("Native", 1, literal(Vec::new())),
        ] {
            assert!(Plan::parse(&host_plan("Native", malformed), None).is_err());
        }
        assert!(super::bytes_operation("fromBytes:Native:1025", 1).is_err());
    }

    #[test]
    fn generic_bytes_hashes_match_sha256_sha512_and_keccak256_vectors() {
        fn run_hash(
            operation: &str,
            input_length: usize,
            values: Vec<u8>,
            result_type: &str,
        ) -> Json {
            let plan = host_plan(
                result_type,
                json!({
                        "tag":"bytes",
                        "operation":operation,
                        "arguments":[{"tag":"bytesLiteral","length":input_length,"values":values}]
                }),
            );
            run_host_plan(plan)
        }

        let abc = b"abc".to_vec();
        let sha256_abc = run_hash("sha256:3", 3, abc.clone(), "Bytes<32>");
        assert_eq!(sha256_abc["status"], "completed");
        assert_eq!(
            sha256_abc["result"]["values"],
            json!(
                hex::decode("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
                    .unwrap()
            )
        );

        let sha512_abc = run_hash("sha512:3", 3, abc.clone(), "Bytes<64>");
        assert_eq!(sha512_abc["status"], "completed");
        assert_eq!(
            sha512_abc["result"]["values"],
            json!(hex::decode(
                "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
            ).unwrap())
        );

        let keccak_abc = run_hash("keccak256:3", 3, abc, "Bytes<32>");
        assert_eq!(keccak_abc["status"], "completed");
        assert_eq!(
            keccak_abc["result"]["values"],
            json!(
                hex::decode("4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45")
                    .unwrap()
            )
        );

        let sha512_empty = run_hash("sha512:0", 0, Vec::new(), "Bytes<64>");
        assert_eq!(sha512_empty["status"], "completed");
        assert_eq!(
            sha512_empty["result"]["values"],
            json!(hex::decode(
                "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
            ).unwrap())
        );

        let keccak_empty = run_hash("keccak256:0", 0, Vec::new(), "Bytes<32>");
        assert_eq!(keccak_empty["status"], "completed");
        assert_eq!(
            keccak_empty["result"]["values"],
            json!(
                hex::decode("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")
                    .unwrap()
            )
        );

        assert!(super::bytes_operation("sha256:03", 1).is_err());
        assert!(super::bytes_operation("sha512:3", 0).is_err());
        assert!(super::bytes_operation("sha512:1025", 1).is_err());
        assert!(super::bytes_operation("keccak256:03", 1).is_err());
        assert!(super::bytes_operation("keccak256:0", 2).is_err());
    }

    #[test]
    fn hash_to_curve_control_session_preserves_order_and_checks_arity() {
        use transient_crypto::curve::{EmbeddedFr, EmbeddedGroupAffine, Fr};
        use transient_crypto::hash::hash_to_curve;

        fn native(value: u64) -> Json {
            json!({"tag":"constant","value":value.to_string()})
        }

        fn hash(operation: &str, arguments: Vec<Json>) -> Json {
            run_host_plan(host_plan(
                "JubjubPoint",
                json!({"tag":"curve","operation":operation,"arguments":arguments}),
            ))
        }

        let empty = hash("hashToCurve:0", vec![]);
        assert_eq!(empty["status"], "completed");
        assert_eq!(
            empty["result"],
            crate::Value::JubjubPoint(hash_to_curve(&[] as &[Fr])).public_json()
        );

        let one = hash("hashToCurve:1", vec![native(3)]);
        assert_eq!(one["status"], "completed");
        assert_eq!(
            one["result"],
            crate::Value::JubjubPoint(hash_to_curve(&[Fr::from(3u64)][..])).public_json()
        );

        let left = 3u64;
        let right = 5u64;
        let fields = vec![native(left), native(right)];
        let multiple = hash("hashToCurve:2", fields.clone());
        assert_eq!(multiple["status"], "completed");
        let point = hash_to_curve(&[Fr::from(left), Fr::from(right)][..]);
        assert_eq!(
            multiple["result"],
            crate::Value::JubjubPoint(point).public_json()
        );

        let composed = run_host_plan(host_plan(
            "JubjubPoint",
            json!({
                "tag":"curve",
                "operation":"jubjubAdd",
                "arguments":[
                    {"tag":"curve","operation":"hashToCurve:2","arguments":fields},
                    {"tag":"curve","operation":"jubjubMulGenerator","arguments":[
                        {"tag":"curve","operation":"jubjubScalarFromNative","arguments":[native(right)]}
                    ]}
                ]
            }),
        ));
        let expected = point + EmbeddedGroupAffine::generator() * EmbeddedFr::from(right);
        assert_eq!(composed["status"], "completed");
        assert_eq!(
            composed["result"],
            crate::Value::JubjubPoint(expected).public_json()
        );

        for (operation, arguments) in [
            ("hashToCurve:01", vec![native(3)]),
            ("hashToCurve:1025", vec![]),
            ("hashToCurve:2", vec![native(3)]),
            ("hashToCurve:1", vec![json!({"tag":"bool","value":true})]),
        ] {
            let plan = host_plan(
                "JubjubPoint",
                json!({"tag":"curve","operation":operation,"arguments":arguments}),
            );
            assert!(Plan::parse(&plan, None).is_err(), "accepted {operation}");
        }
    }

    #[test]
    fn transient_hash_native_vectors_preserve_native_order_and_bounds() {
        use transient_crypto::curve::Fr;
        use transient_crypto::hash::transient_hash;

        fn native(value: usize) -> Json {
            json!({"tag":"constant","value":value.to_string()})
        }
        fn run(value: Json, max_steps: usize) -> Json {
            let mut plan = host_plan("Native", value);
            plan["limits"]["maxSteps"] = json!(max_steps);
            run_host_plan(plan)
        }

        for count in [0usize, 1, 3, 1024] {
            let fields = (0..count)
                .map(|value| Fr::from(value as u64))
                .collect::<Vec<_>>();
            let expected = json!(crate::field_decimal(transient_hash(&fields)));
            let values = (0..count).map(native).collect::<Vec<_>>();
            let direct = run(json!({"tag":"transientHash","values":values}), 4096);
            let typed = run(
                json!({
                    "tag":"curve",
                    "operation":format!("transientHashNativeVector:{count}"),
                    "arguments":(0..count).map(native).collect::<Vec<_>>()
                }),
                4096,
            );
            assert_eq!(direct["status"], "completed");
            assert_eq!(direct["result"], expected);
            assert_eq!(typed["status"], "completed");
            assert_eq!(typed["result"], expected);
            let bytes_operation = run(
                json!({
                    "tag":"bytes",
                    "operation":"transientHashNativeVector",
                    "arguments":(0..count).map(native).collect::<Vec<_>>()
                }),
                4096,
            );
            assert_eq!(bytes_operation["status"], "completed");
            assert_eq!(bytes_operation["result"], expected);
            if count == 0 {
                assert_eq!(direct["result"], "0");
            }
        }

        let direct = run(
            json!({
                "tag":"transientHash",
                "values":[native(3),native(5),native(8)]
            }),
            256,
        );
        let typed = run(
            json!({
                "tag":"curve",
                "operation":"transientHashNativeVector:3",
                "arguments":[native(3),native(5),native(8)]
            }),
            256,
        );
        let legacy = run(
            json!({
                "tag":"poseidon2",
                "domain":"3",
                "left":native(5),
                "right":native(8)
            }),
            256,
        );
        assert_eq!(direct["result"], legacy["result"]);
        assert_eq!(typed["result"], legacy["result"]);

        for value in [
            json!({"tag":"bool","value":true}),
            json!({"tag":"uint","maximum":"1","value":"1"}),
            json!({
                "tag":"curve",
                "operation":"jubjubScalarFromNative",
                "arguments":[native(1)]
            }),
        ] {
            assert!(
                Plan::parse(
                    &host_plan(
                        "Native",
                        json!({"tag":"transientHash","values":[value.clone()]})
                    ),
                    None
                )
                .is_err()
            );
            assert!(
                Plan::parse(
                    &host_plan(
                        "Native",
                        json!({
                            "tag":"curve",
                            "operation":"transientHashNativeVector:1",
                            "arguments":[value]
                        })
                    ),
                    None
                )
                .is_err()
            );
        }

        let oversized_values = (0..=crate::MAX_TRANSIENT_HASH_FIELDS)
            .map(native)
            .collect::<Vec<_>>();
        assert!(
            Plan::parse(
                &host_plan(
                    "Native",
                    json!({"tag":"transientHash","values":oversized_values})
                ),
                None
            )
            .is_err()
        );
        assert!(
            super::curve_operation(&format!(
                "transientHashNativeVector:{}",
                crate::MAX_TRANSIENT_HASH_FIELDS + 1
            ))
            .is_err()
        );
        assert!(super::curve_operation("transientHashNativeVector:01").is_err());
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    fn typed_foreign_values_preserve_type_through_inputs_equality_and_select() {
        use crate::foreign::{ForeignFamily, ForeignRole, ForeignType, ForeignValue};

        let foreign_type = ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Base);
        let zero = ForeignValue::from_bytes(foreign_type, &[0; 32]).unwrap();
        let one = ForeignValue::from_bytes(
            foreign_type,
            &[
                1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0,
            ],
        )
        .unwrap();
        let encoded = |value: &ForeignValue| {
            value
                .encode()
                .unwrap()
                .iter()
                .map(|field| crate::field_decimal(*field))
                .collect::<Vec<_>>()
        };
        let literal = |value: &ForeignValue| {
            json!({
                "tag":"foreignConstant",
                "type":foreign_type.source_name(),
                "encoding":encoded(value)
            })
        };
        let zero_literal = literal(&zero);
        let one_literal = literal(&one);
        let expression = json!({
            "tag":"select",
            "condition":{
                "tag":"eq",
                "left":{"tag":"reference","name":"candidate"},
                "right":zero_literal
            },
            "yes":one_literal,
            "no":literal(&zero)
        });
        let mut plan = host_plan(foreign_type.source_name(), expression);
        plan["inputs"] = json!([{
            "name":"candidate",
            "type":foreign_type.source_name(),
            "visibility":"public"
        }]);
        plan["functions"][0]["parameters"] = json!([{
            "name":"candidate",
            "type":foreign_type.source_name()
        }]);

        let parsed = Plan::parse(&plan, None).unwrap();
        let context = source_context(&parsed, &"d".repeat(64));
        let inputs = BTreeMap::from([(
            "candidate".to_owned(),
            crate::Value::Foreign(zero).public_json(),
        )]);
        let mut session = Session::from_json(plan, inputs, context).unwrap();
        let completed = session.advance().unwrap();
        assert_eq!(completed["status"], "completed");
        assert_eq!(
            completed["result"],
            crate::Value::Foreign(one.clone()).public_json()
        );

        let projected = run_host_plan(host_plan(
            "Native",
            json!({"tag":"foreignEncodedField","value":literal(&one),"index":0}),
        ));
        let expected_native = crate::Value::Native(one.encode().unwrap()[0]).public_json();
        assert_eq!(projected["status"], "completed");
        assert_eq!(projected["result"], expected_native);

        for malformed in [
            json!({"tag":"foreignConstant","type":"Native","encoding":["0"]}),
            json!({"tag":"foreignConstant","type":foreign_type.source_name(),"encoding":["0"]}),
            json!({"tag":"foreignConstant","type":foreign_type.source_name(),"encoding":["00","0"]}),
        ] {
            assert!(Plan::parse(&host_plan(foreign_type.source_name(), malformed), None).is_err());
        }
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    fn foreign_curve_and_byte_operations_execute_through_control_session() {
        use crate::foreign::{ForeignFamily, ForeignRole, ForeignType, ForeignValue};

        let base_type = ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Base);
        let point_type = ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Point);
        let other_family = ForeignType::new(ForeignFamily::Secp256r1, ForeignRole::Base);
        let base = |value: u8| ForeignValue::from_bytes_reducing(base_type, &[value]).unwrap();
        let literal = |value: &ForeignValue| {
            json!({
                "tag":"foreignConstant",
                "type":value.foreign_type().source_name(),
                "encoding":value.encode().unwrap().iter().map(|field| crate::field_decimal(*field)).collect::<Vec<_>>()
            })
        };
        let three = base(3);
        let five = base(5);
        let eight = base(8);

        // The direct expression tags carry their own types. The nested byte
        // decoder accepts a short little-endian input and the outer encoder
        // returns the typed canonical result.
        let direct = json!({
            "tag":"foreignToBytes",
            "value":{
                "tag":"foreignBinary",
                "operation":"add",
                "left":literal(&three),
                "right":{
                    "tag":"foreignFromBytes",
                    "type":base_type.source_name(),
                    "length":1,
                    "value":{"tag":"bytesLiteral","length":1,"values":[5]}
                }
            }
        });
        let completed = run_host_plan(host_plan("Bytes<32>", direct));
        assert_eq!(completed["status"], "completed");
        assert_eq!(
            completed["result"],
            json!({"kind":"bytes","values":eight.to_bytes().unwrap()})
        );

        // The helper operation-name route must share the same checked SDK
        // evaluator as the direct source expression tags.
        let helper_route = json!({
            "tag":"bytes",
            "operation":format!("foreignToBytes:{}", base_type.source_name()),
            "arguments":[{
                "tag":"curve",
                "operation":format!(
                    "foreignBinary:add:{}:{}",
                    base_type.source_name(),
                    base_type.source_name()
                ),
                "arguments":[literal(&three), literal(&five)]
            }]
        });
        let completed = run_host_plan(host_plan("Bytes<32>", helper_route));
        assert_eq!(completed["status"], "completed");
        assert_eq!(
            completed["result"],
            json!({"kind":"bytes","values":eight.to_bytes().unwrap()})
        );

        let identity = ForeignValue::from_bytes_reducing(point_type, &[0; 33]).unwrap();
        let identity_bytes = json!({
            "tag":"bytes",
            "operation":format!("foreignToBytes:{}", point_type.source_name()),
            "arguments":[literal(&identity)]
        });
        let point_roundtrip = json!({
            "tag":"foreignFromBytes",
            "type":point_type.source_name(),
            "length":33,
            "value":identity_bytes
        });
        let completed = run_host_plan(host_plan(point_type.source_name(), point_roundtrip));
        assert_eq!(completed["status"], "completed");
        assert_eq!(
            completed["result"],
            crate::Value::Foreign(identity).public_json()
        );

        let scalar_type = ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Scalar);
        let one_scalar = ForeignValue::from_bytes_reducing(scalar_type, &[1]).unwrap();
        let generator = ForeignValue::from_bytes(
            point_type,
            &hex::decode("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")
                .unwrap(),
        )
        .unwrap();
        let generated_point = json!({
            "tag":"curve",
            "operation":format!("foreignUnary:mulGenerator:{}", scalar_type.source_name()),
            "arguments":[literal(&one_scalar)]
        });
        let completed = run_host_plan(host_plan(point_type.source_name(), generated_point));
        assert_eq!(completed["status"], "completed");
        assert_eq!(
            completed["result"],
            crate::Value::Foreign(generator.clone()).public_json()
        );
        let extracted_x = json!({
            "tag":"foreignUnary",
            "operation":"x",
            "value":literal(&generator)
        });
        let completed = run_host_plan(host_plan(base_type.source_name(), extracted_x));
        assert_eq!(completed["status"], "completed");
        assert_eq!(
            completed["result"],
            crate::Value::Foreign(generator.unary(crate::foreign::ForeignUnaryOp::X).unwrap())
                .public_json()
        );

        let empty_decode = json!({
            "tag":"foreignFromBytes",
            "type":base_type.source_name(),
            "length":0,
            "value":{"tag":"bytesLiteral","length":0,"values":[]}
        });
        let completed = run_host_plan(host_plan(base_type.source_name(), empty_decode));
        assert_eq!(completed["status"], "completed");
        assert_eq!(
            completed["result"],
            crate::Value::Foreign(base(0)).public_json()
        );

        let zero_inverse = json!({
            "tag":"foreignUnary",
            "operation":"inv",
            "value":literal(&base(0))
        });
        assert_eq!(
            run_host_plan(host_plan(base_type.source_name(), zero_inverse))["status"],
            "failed"
        );

        let mismatched_curve = json!({
            "tag":"foreignBinary",
            "operation":"add",
            "left":literal(&three),
            "right":literal(&ForeignValue::from_bytes_reducing(other_family, &[5]).unwrap())
        });
        assert!(Plan::parse(&host_plan(base_type.source_name(), mismatched_curve), None).is_err());
        let wrong_point_length = json!({
            "tag":"foreignFromBytes",
            "type":point_type.source_name(),
            "length":32,
            "value":{"tag":"bytesLiteral","length":32,"values":vec![0;32]}
        });
        assert!(
            Plan::parse(
                &host_plan(point_type.source_name(), wrong_point_length),
                None
            )
            .is_err()
        );
        assert!(
            super::curve_operation(&format!("foreignUnary:inv:{}", point_type.source_name()))
                .is_err()
        );
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    fn curve25519_field_point_and_byte_operations_execute_through_control_session() {
        use crate::foreign::{ForeignFamily, ForeignRole, ForeignType, ForeignValue};

        let base_type = ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Base);
        let scalar_type = ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Scalar);
        let point_type = ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Point);
        let base = |value: u8| ForeignValue::from_bytes_reducing(base_type, &[value]).unwrap();
        let scalar = |value: u8| ForeignValue::from_bytes_reducing(scalar_type, &[value]).unwrap();
        let literal = |value: &ForeignValue| {
            json!({
                "tag":"foreignConstant",
                "type":value.foreign_type().source_name(),
                "encoding":value.encode().unwrap().iter().map(|field| crate::field_decimal(*field)).collect::<Vec<_>>()
            })
        };

        let base_sum = json!({
            "tag":"bytes",
            "operation":format!("foreignToBytes:{}", base_type.source_name()),
            "arguments":[{
                "tag":"curve",
                "operation":format!("foreignBinary:add:{}:{}", base_type.source_name(), base_type.source_name()),
                "arguments":[literal(&base(3)), literal(&base(5))]
            }]
        });
        let completed = run_host_plan(host_plan("Bytes<32>", base_sum));
        assert_eq!(completed["status"], "completed");
        assert_eq!(
            completed["result"],
            json!({"kind":"bytes","values":base(8).to_bytes().unwrap()})
        );

        let scalar_product = json!({
            "tag":"bytes",
            "operation":format!("foreignToBytes:{}", scalar_type.source_name()),
            "arguments":[{
                "tag":"curve",
                "operation":format!("foreignBinary:mul:{}:{}", scalar_type.source_name(), scalar_type.source_name()),
                "arguments":[literal(&scalar(2)), literal(&scalar(3))]
            }]
        });
        let completed = run_host_plan(host_plan("Bytes<32>", scalar_product));
        assert_eq!(completed["status"], "completed");
        assert_eq!(
            completed["result"],
            json!({"kind":"bytes","values":scalar(6).to_bytes().unwrap()})
        );

        let identity_coordinates = json!({
            "tag":"curve",
            "operation":format!("foreignBinary:fromCoordinates:{}:{}", base_type.source_name(), base_type.source_name()),
            "arguments":[literal(&base(0)), literal(&base(1))]
        });
        let coordinates = ["x", "y"].map(|coordinate| {
            json!({
                "tag":"bytes",
                "operation":format!("foreignToBytes:{}", base_type.source_name()),
                "arguments":[{
                    "tag":"curve",
                    "operation":format!("foreignUnary:{}:{}", coordinate, point_type.source_name()),
                    "arguments":[identity_coordinates.clone()]
                }]
            })
        });
        let identity_coordinate_bytes = json!({
            "tag":"bytes",
            "operation":"concatBytes:32:32",
            "arguments":coordinates
        });
        let mut identity_coordinates_bytes = base(0).to_bytes().unwrap();
        identity_coordinates_bytes.extend(base(1).to_bytes().unwrap());
        let completed = run_host_plan(host_plan("Bytes<64>", identity_coordinate_bytes));
        assert_eq!(completed["status"], "completed");
        assert_eq!(
            completed["result"],
            json!({"kind":"bytes","values":identity_coordinates_bytes})
        );

        let identity_roundtrip = json!({
            "tag":"bytes",
            "operation":format!("foreignFromBytes:{}:32", point_type.source_name()),
            "arguments":[{
                "tag":"bytes",
                "operation":format!("foreignToBytes:{}", point_type.source_name()),
                "arguments":[identity_coordinates]
            }]
        });
        let completed = run_host_plan(host_plan(point_type.source_name(), identity_roundtrip));
        assert_eq!(completed["status"], "completed");
        assert_eq!(
            completed["result"],
            crate::Value::Foreign(ForeignValue::zero(point_type).unwrap()).public_json()
        );

        let generator_mul = json!({
            "tag":"bytes",
            "operation":format!("foreignToBytes:{}", point_type.source_name()),
            "arguments":[{
                "tag":"curve",
                "operation":format!("foreignUnary:mulGenerator:{}", scalar_type.source_name()),
                "arguments":[literal(&scalar(1))]
            }]
        });
        let completed = run_host_plan(host_plan("Bytes<32>", generator_mul));
        let mut generator_bytes = [0x66; 32];
        generator_bytes[0] = 0x58;
        assert_eq!(completed["status"], "completed");
        assert_eq!(
            completed["result"],
            json!({"kind":"bytes","values":generator_bytes})
        );

        let invalid_subgroup_bytes = {
            let mut bytes = vec![0xff; 32];
            bytes[0] = 0xec;
            bytes[31] = 0x7f;
            bytes
        };
        let invalid_subgroup = json!({
            "tag":"bytes",
            "operation":format!("foreignFromBytes:{}:32", point_type.source_name()),
            "arguments":[{"tag":"bytesLiteral","length":32,"values":invalid_subgroup_bytes}]
        });
        assert_eq!(
            run_host_plan(host_plan(point_type.source_name(), invalid_subgroup))["status"],
            "failed"
        );

        let wrong_point_length = host_plan(
            point_type.source_name(),
            json!({
                "tag":"foreignFromBytes",
                "type":point_type.source_name(),
                "length":31,
                "value":{"tag":"bytesLiteral","length":31,"values":vec![0;31]}
            }),
        );
        assert!(Plan::parse(&wrong_point_length, None).is_err());

        let wrong_helper_point_length = host_plan(
            point_type.source_name(),
            json!({
                "tag":"bytes",
                "operation":format!("foreignFromBytes:{}:31", point_type.source_name()),
                "arguments":[{"tag":"bytesLiteral","length":31,"values":vec![0;31]}]
            }),
        );
        assert!(Plan::parse(&wrong_helper_point_length, None).is_err());
    }

    #[test]
    fn eager_boolean_gates_match_truth_tables_and_evaluate_both_operands() {
        fn boolean(value: bool) -> Json {
            json!({"tag":"bool","value":value})
        }

        fn gate(tag: &str, left: Json, right: Json) -> Json {
            json!({"tag":tag,"left":left,"right":right})
        }

        let cases = [
            ("boolAnd", true, true, true),
            ("boolAnd", true, false, false),
            ("boolAnd", false, true, false),
            ("boolAnd", false, false, false),
            ("boolOr", true, true, true),
            ("boolOr", true, false, true),
            ("boolOr", false, true, true),
            ("boolOr", false, false, false),
            ("boolXor", true, true, false),
            ("boolXor", true, false, true),
            ("boolXor", false, true, true),
            ("boolXor", false, false, false),
        ];
        let mut checks = cases
            .into_iter()
            .map(|(operator, left, right, expected)| {
                json!({
                    "tag":"eq",
                    "left":gate(operator, boolean(left), boolean(right)),
                    "right":boolean(expected)
                })
            })
            .collect::<Vec<_>>();
        let chained_xor = gate(
            "boolXor",
            gate(
                "boolXor",
                gate("boolXor", boolean(true), boolean(false)),
                boolean(true),
            ),
            boolean(false),
        );
        checks.push(json!({
            "tag":"eq",
            "left":chained_xor,
            "right":boolean(false)
        }));
        let all = checks
            .into_iter()
            .reduce(|left, right| gate("boolAnd", left, right))
            .unwrap();
        let completed = run_host_plan(host_plan("Bool", all));
        assert_eq!(completed["status"], "completed");
        assert_eq!(completed["result"], json!(true));

        let failing_bool = json!({
            "tag":"eq",
            "left":{
                "tag":"cast",
                "type":"UIntRange<256>",
                "value":{"tag":"constant","value":"300"}
            },
            "right":{"tag":"uint","maximum":"255","value":"0"}
        });
        let failed_and = run_host_plan(host_plan(
            "Bool",
            gate("boolAnd", boolean(false), failing_bool.clone()),
        ));
        assert_eq!(failed_and["status"], "failed");
        let failed_or = run_host_plan(host_plan(
            "Bool",
            gate("boolOr", boolean(true), failing_bool),
        ));
        assert_eq!(failed_or["status"], "failed");

        let invalid_type = host_plan(
            "Bool",
            gate(
                "boolAnd",
                boolean(true),
                json!({"tag":"constant","value":"1"}),
            ),
        );
        assert!(Plan::parse(&invalid_type, None).is_err());
        let invalid_arity = host_plan(
            "Bool",
            json!({"tag":"boolXor","left":{"tag":"bool","value":true}}),
        );
        assert!(Plan::parse(&invalid_arity, None).is_err());
    }

    #[test]
    fn completed_handoff_rejects_changed_map_and_target_without_consuming_runtime() {
        let control_plan: Json = serde_json::from_str(SOURCE_PLAN).unwrap();
        let plan_bytes = serde_json::to_vec(&control_plan).unwrap();
        let binding_text = control_plan["binding"].as_str().unwrap();
        let binding_bytes = binding_text.as_bytes().to_vec();
        let binding: Json = serde_json::from_str(binding_text).unwrap();
        let relation = binding["nativeRelation"].clone();
        let digest = hex::encode(Sha256::digest(binding_bytes.as_slice()));
        let parsed = Plan::parse(&control_plan, Some(&digest)).unwrap();
        let attempt = "b".repeat(64);
        let address = "a".repeat(64);
        let context_id = 17;
        let target = AuthenticatedNativeTarget {
            context_id,
            contract_address: address.clone(),
            entrypoint: "claim".into(),
            control_plan,
            control_plan_bytes: plan_bytes.clone(),
            binding_bytes: binding_bytes.clone(),
            relation: relation.clone(),
        };
        let mut session = Session::from_authenticated_native_target(
            &plan_bytes,
            BTreeMap::from([
                ("expected".into(), json!("14")),
                ("seed".into(), json!("7")),
            ]),
            source_context(&parsed, &attempt),
            target,
        )
        .unwrap();
        let waiting = session.advance().unwrap();
        assert_eq!(waiting["status"], "need_host");
        let waiting_budget = session.aggregate_budget.used.load(Ordering::Acquire);
        for _ in 0..4 {
            let private = session.private_request_accounted().unwrap();
            assert_eq!(private.as_json()["arguments"]["key"], "cache/last");
            assert!(session.aggregate_budget.used.load(Ordering::Acquire) > waiting_budget);
            drop(private);
            assert_eq!(
                session.aggregate_budget.used.load(Ordering::Acquire),
                waiting_budget
            );
        }
        complete_source(&mut session, &attempt);
        let complete_budget = session.aggregate_budget.used.load(Ordering::Acquire);
        for _ in 0..3 {
            let private = session.private_completion_accounted(&relation).unwrap();
            assert_eq!(private.as_json()["kind"], "typed-witness-inputs");
            assert!(session.aggregate_budget.used.load(Ordering::Acquire) > complete_budget);
            drop(private);
            assert_eq!(
                session.aggregate_budget.used.load(Ordering::Acquire),
                complete_budget
            );
        }
        let budget_after_execution = session
            .aggregate_budget
            .used
            .load(std::sync::atomic::Ordering::Acquire);
        for _ in 0..3 {
            drop(
                session
                    .peek_completed_invocation(
                        context_id,
                        &address,
                        "claim",
                        &session.source_plan,
                        &binding_bytes,
                        &relation,
                    )
                    .unwrap(),
            );
        }
        assert_eq!(
            session
                .aggregate_budget
                .used
                .load(std::sync::atomic::Ordering::Acquire),
            budget_after_execution
        );
        let expected = session
            .peek_completed_invocation(
                context_id,
                &address,
                "claim",
                &session.source_plan,
                &binding_bytes,
                &relation,
            )
            .unwrap();
        let source_plan = session.source_plan.clone();

        let mut changed = expected.try_clone_accounted().unwrap();
        *changed.values_mut().next().unwrap() = json!("13");
        assert!(
            session
                .take_completed_invocation(
                    context_id,
                    &source_plan,
                    &binding_bytes,
                    &relation,
                    &changed,
                    &address,
                    "claim",
                )
                .is_err()
        );
        assert!(
            session
                .take_completed_invocation(
                    context_id + 1,
                    &source_plan,
                    &binding_bytes,
                    &relation,
                    &expected,
                    &address,
                    "claim",
                )
                .is_err()
        );
        assert!(
            session
                .take_completed_invocation(
                    context_id,
                    &source_plan,
                    &binding_bytes,
                    &relation,
                    &expected,
                    &"c".repeat(64),
                    "claim",
                )
                .is_err()
        );
        assert!(
            session
                .take_completed_invocation(
                    context_id,
                    &source_plan,
                    &binding_bytes,
                    &relation,
                    &expected,
                    &address,
                    "other",
                )
                .is_err()
        );
        let retried = session
            .peek_completed_invocation(
                context_id,
                &address,
                "claim",
                &session.source_plan,
                &binding_bytes,
                &relation,
            )
            .unwrap();
        assert_eq!(&retried.values, &expected.values);

        let completed = session
            .take_completed_invocation(
                context_id,
                &source_plan,
                &binding_bytes,
                &relation,
                &expected,
                &address,
                "claim",
            )
            .unwrap();
        assert!(completed.runtime.has_target(&address, "claim"));
        assert!(
            session
                .take_completed_invocation(
                    context_id,
                    &source_plan,
                    &binding_bytes,
                    &relation,
                    &expected,
                    &address,
                    "claim",
                )
                .is_err()
        );
    }

    #[test]
    fn aggregate_advance_results_hold_their_reservation_until_drop() {
        let plan: Json = serde_json::from_str(PAIR_PLAN).unwrap();
        let binding_text = plan["binding"].as_str().unwrap();
        let binding: Json = serde_json::from_str(binding_text).unwrap();
        let digest = hex::encode(Sha256::digest(binding_text.as_bytes()));
        let attempt = "c".repeat(64);
        let target = InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: "claim".into(),
        };
        let mut session = Session::from_json_with_invocation_target(
            plan.clone(),
            BTreeMap::from([
                ("expected".into(), json!("14")),
                (
                    "request".into(),
                    json!({
                        "kind":"struct",
                        "id":"TypedWitness.Pair",
                        "fields":[
                            {"name":"amount","value":{"kind":"uint","maximum":"255","value":"7"}},
                            {"name":"okay","value":{"kind":"bool","value":true}}
                        ]
                    }),
                ),
            ]),
            source_context(&Plan::parse(&plan, Some(&digest)).unwrap(), &attempt),
            Some(&digest),
            Some(target),
        )
        .unwrap();

        let pending = session.advance().unwrap();
        let response: TypedResponse = serde_json::from_value(json!({
            "protocolVersion":2,
            "requestId":pending["request"]["requestId"],
            "attemptId":attempt,
            "outcome":"value",
            "operation":pending["request"]["operation"],
            "capability":pending["request"]["capability"],
            "schema":pending["request"]["schema"],
            "value":{
                "kind":"struct",
                "id":"TypedWitness.Pair",
                "fields":[
                    {"name":"amount","value":{"kind":"uint","maximum":"255","value":"14"}},
                    {"name":"okay","value":{"kind":"bool","value":true}}
                ]
            }
        }))
        .unwrap();
        session.resume_typed(response).unwrap();

        let output = session.advance_accounted().unwrap();
        assert_eq!(output["status"], "completed");
        assert_eq!(output["result"]["kind"], "struct");
        let charge = session.completed_result_charge.unwrap();
        let baseline = session.aggregate_budget.used.load(Ordering::Acquire) - charge;
        assert_eq!(
            session.aggregate_budget.used.load(Ordering::Acquire),
            baseline + charge
        );
        drop(output);
        assert_eq!(
            session.aggregate_budget.used.load(Ordering::Acquire),
            baseline
        );

        for _ in 0..3 {
            let output = session.advance_accounted().unwrap();
            assert_eq!(output["result"]["kind"], "struct");
            assert_eq!(
                session.aggregate_budget.used.load(Ordering::Acquire),
                baseline + charge
            );
            drop(output);
            assert_eq!(
                session.aggregate_budget.used.load(Ordering::Acquire),
                baseline
            );
        }
        let relation = binding["nativeRelation"].clone();
        let completion = session.private_completion(&relation).unwrap();
        assert_eq!(completion["inputs"]["$helper7"], "14");
    }
}
