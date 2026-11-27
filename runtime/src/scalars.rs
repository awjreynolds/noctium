//! ScalarPolicy.lean-compatible unsigned bounds and checked conversions.
#[cfg(feature = "zkir-321")]
use crate::foreign::ForeignType;
use crate::{MODULUS, Value, canonical_field};
use anyhow::{Result, anyhow, bail, ensure};
use base_crypto::fab::ValueAtom;
use num_bigint::BigUint;

pub const MAX_UINT_BITS: usize = 248;
// Fixed byte transport uses high-first FAB limbs and remains bounded by the
// aggregate leaf limit. Byte indexing and legacy private/bytewise inputs keep
// their earlier cap.
pub const MAX_BYTES_LENGTH: usize = 4096;
pub const MAX_LEGACY_BYTE_INPUT_LENGTH: usize = 34 * 31;
pub const MAX_BYTE_INDEX_LENGTH: usize = MAX_LEGACY_BYTE_INPUT_LENGTH;
pub(super) const MAX_BYTE_LITERAL_LENGTH: usize = MAX_LEGACY_BYTE_INPUT_LENGTH;
pub const MAX_BYTE_OPERATION_LENGTH: usize = 1024;
pub(super) const MAX_OPAQUE_BYTES_LENGTH: usize = 1_048_576;
pub(crate) const MAX_OPAQUE_STRING_LENGTH: usize = 1_048_576;

pub(crate) fn opaque_string_atom(text: &str) -> Result<ValueAtom> {
    ensure!(
        text.len() <= MAX_OPAQUE_STRING_LENGTH,
        "opaque string exceeds byte limit"
    );
    let atom = ValueAtom(text.as_bytes().to_vec());
    ensure!(
        atom.is_in_normal_form(),
        "opaque string has trailing zero bytes"
    );
    Ok(atom)
}

pub(crate) fn validate_opaque_string_atom(atom: &ValueAtom) -> Result<()> {
    ensure!(
        atom.0.len() <= MAX_OPAQUE_STRING_LENGTH,
        "opaque string exceeds byte limit"
    );
    ensure!(
        atom.is_in_normal_form(),
        "opaque string has trailing zero bytes"
    );
    Ok(())
}
pub fn max_uint() -> BigUint {
    (BigUint::from(1u8) << MAX_UINT_BITS) - 1u8
}

fn decimal(text: &str) -> Result<BigUint> {
    ensure!(
        !text.is_empty()
            && text.len() <= MODULUS.len()
            && text.bytes().all(|b| b.is_ascii_digit())
            && (text == "0" || !text.starts_with('0')),
        "expected canonical unsigned decimal string"
    );
    BigUint::parse_bytes(text.as_bytes(), 10).ok_or_else(|| anyhow!("invalid unsigned decimal"))
}
pub fn canonical_unsigned(text: &str, maximum: &BigUint) -> Result<BigUint> {
    ensure!(
        *maximum <= max_uint(),
        "unsigned type exceeds target maximum"
    );
    let value = decimal(text)?;
    ensure!(value <= *maximum, "unsigned value outside declared type");
    Ok(value)
}
fn maximum(text: &str) -> Result<BigUint> {
    let value = decimal(text)?;
    ensure!(value <= max_uint(), "unsigned type exceeds target maximum");
    Ok(value)
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScalarType {
    Native,
    Bool,
    UInt(BigUint),
    Bytes32,
    Bytes(usize),
    OpaqueBytes,
    OpaqueString,
    JubjubScalar,
    JubjubPoint,
    #[cfg(feature = "zkir-321")]
    Foreign(ForeignType),
}
impl ScalarType {
    pub fn bytes_length(&self) -> Option<usize> {
        match self {
            Self::Bytes32 => Some(32),
            Self::Bytes(length) => Some(*length),
            _ => None,
        }
    }
    pub(crate) fn call_return_fields(&self) -> usize {
        match self {
            Self::Bytes32 | Self::JubjubPoint => 2,
            Self::Bytes(length) => length.div_ceil(31),
            #[cfg(feature = "zkir-321")]
            Self::Foreign(ty) => ty.native_type().encoded_len(),
            _ => 1,
        }
    }
    pub fn parse(text: &str) -> Result<Self> {
        #[cfg(feature = "zkir-321")]
        if let Ok(ty) = ForeignType::parse_source_name(text) {
            return Ok(Self::Foreign(ty));
        }
        match text {
            "Native" => Ok(Self::Native),
            "Bool" => Ok(Self::Bool),
            "Bytes<32>" => Ok(Self::Bytes32),
            "OpaqueBytes" => Ok(Self::OpaqueBytes),
            "OpaqueString" => Ok(Self::OpaqueString),
            "JubjubScalar" => Ok(Self::JubjubScalar),
            "JubjubPoint" => Ok(Self::JubjubPoint),
            _ => {
                if let Some(length) = text
                    .strip_prefix("Bytes<")
                    .and_then(|s| s.strip_suffix('>'))
                {
                    ensure!(
                        !length.is_empty()
                            && length.len() <= 4
                            && length.bytes().all(|byte| byte.is_ascii_digit())
                            && (length == "0" || !length.starts_with('0')),
                        "expected canonical byte length"
                    );
                    let length: usize = length.parse()?;
                    ensure!(
                        length <= MAX_BYTES_LENGTH,
                        "byte length exceeds compiler limit"
                    );
                    return Ok(Self::Bytes(length));
                }
                let bound = text
                    .strip_prefix("UIntRange<")
                    .and_then(|s| s.strip_suffix('>'))
                    .ok_or_else(|| anyhow!("unsupported scalar type"))?;
                let exclusive = decimal(bound)?;
                ensure!(
                    exclusive > BigUint::from(0u8) && exclusive <= max_uint() + 1u8,
                    "unsigned exclusive bound outside target range"
                );
                Ok(Self::UInt(exclusive - 1u8))
            }
        }
    }
    fn validate(&self) -> Result<()> {
        if let Self::Bytes(length) = self {
            ensure!(
                *length <= MAX_BYTES_LENGTH,
                "byte length exceeds compiler limit"
            );
            ensure!(*length != 32, "use the canonical Bytes32 type for 32 bytes");
        }
        if let Self::UInt(maximum) = self {
            ensure!(
                *maximum <= max_uint(),
                "unsigned type exceeds target maximum"
            );
        }
        Ok(())
    }
}
impl Value {
    pub fn scalar_type(&self) -> ScalarType {
        match self {
            Self::Native(_) => ScalarType::Native,
            Self::Bool(_) => ScalarType::Bool,
            Self::UInt { maximum, .. } => ScalarType::UInt(maximum.clone()),
            Self::Bytes(bytes) if bytes.len() == 32 => ScalarType::Bytes32,
            Self::Bytes(bytes) => ScalarType::Bytes(bytes.len()),
            Self::OpaqueBytes(_) => ScalarType::OpaqueBytes,
            Self::OpaqueString(_) => ScalarType::OpaqueString,
            Self::JubjubScalar(_) => ScalarType::JubjubScalar,
            Self::JubjubPoint(_) => ScalarType::JubjubPoint,
            #[cfg(feature = "zkir-321")]
            Self::Foreign(value) => ScalarType::Foreign(value.foreign_type()),
        }
    }
    pub fn validate(&self) -> Result<()> {
        self.scalar_type().validate()?;
        if let Self::UInt { number, maximum } = self {
            ensure!(number <= maximum, "unsigned value outside declared type");
        }
        if let Self::OpaqueBytes(bytes) = self {
            ensure!(
                bytes.len() <= MAX_OPAQUE_BYTES_LENGTH,
                "opaque byte value exceeds native limit"
            );
            ensure!(
                bytes.is_empty() || bytes.last() != Some(&0),
                "opaque byte value has trailing zero bytes"
            );
        }
        if let Self::OpaqueString(text) = self {
            let _ = opaque_string_atom(text)?;
        }
        Ok(())
    }
    fn number(&self) -> Result<BigUint> {
        Ok(match self {
            Self::Native(n) => BigUint::from_bytes_le(&n.as_le_bytes()),
            Self::Bool(b) => BigUint::from(u8::from(*b)),
            Self::UInt { number, .. } => number.clone(),
            Self::Bytes(_) | Self::OpaqueBytes(_) | Self::OpaqueString(_) => {
                bail!("bytes have no numeric scalar encoding")
            }
            Self::JubjubScalar(_) | Self::JubjubPoint(_) => {
                bail!("Jubjub values require explicit typed conversions")
            }
            #[cfg(feature = "zkir-321")]
            Self::Foreign(_) => bail!("foreign values require explicit typed conversions"),
        })
    }
    pub fn cast(&self, target: &ScalarType) -> Result<Self> {
        self.validate()?;
        target.validate()?;
        let opaque = match self {
            Self::Bytes(_)
            | Self::OpaqueBytes(_)
            | Self::OpaqueString(_)
            | Self::JubjubScalar(_)
            | Self::JubjubPoint(_) => true,
            #[cfg(feature = "zkir-321")]
            Self::Foreign(_) => true,
            _ => false,
        };
        if opaque {
            ensure!(
                *target == self.scalar_type(),
                "opaque values require an explicit typed conversion"
            );
            return Ok(self.clone());
        }
        let number = self.number()?;
        let result = match target {
            ScalarType::Native => Self::Native(canonical_field(&number.to_str_radix(10))?),
            ScalarType::Bool => Self::Bool(number != BigUint::from(0u8)),
            ScalarType::UInt(maximum) => Self::UInt {
                number,
                maximum: maximum.clone(),
            },
            ScalarType::Bytes32
            | ScalarType::Bytes(_)
            | ScalarType::OpaqueBytes
            | ScalarType::OpaqueString => {
                bail!("scalars cannot be cast to bytes")
            }
            ScalarType::JubjubScalar | ScalarType::JubjubPoint => {
                bail!("scalars cannot be cast to Jubjub values")
            }
            #[cfg(feature = "zkir-321")]
            ScalarType::Foreign(_) => bail!("scalars cannot be cast to foreign values"),
        };
        result.validate()?;
        Ok(result)
    }
    pub(crate) fn field_encoding(&self) -> Result<transient_crypto::curve::Fr> {
        self.validate()?;
        canonical_field(&self.number()?.to_str_radix(10))
    }
    pub fn public_json(&self) -> serde_json::Value {
        match self {
            Self::Native(n) => serde_json::Value::String(crate::field_decimal(*n)),
            Self::Bool(b) => serde_json::Value::Bool(*b),
            Self::UInt { number, .. } => serde_json::Value::String(number.to_str_radix(10)),
            Self::Bytes(bytes) => serde_json::json!({"kind":"bytes","values":bytes}),
            Self::OpaqueBytes(bytes) => {
                serde_json::json!({"kind":"opaqueBytes","values":bytes})
            }
            Self::OpaqueString(text) => {
                serde_json::json!({"kind":"opaqueString","value":text})
            }
            Self::JubjubScalar(value) => serde_json::json!({
                "kind":"jubjubScalar",
                "value":BigUint::from_bytes_le(&value.as_le_bytes()).to_str_radix(10)
            }),
            Self::JubjubPoint(value) => {
                let [x, y] = crate::jubjub::coordinates(*value)
                    .expect("validated Jubjub point has affine coordinates");
                serde_json::json!({
                    "kind":"jubjubPoint", "x":crate::field_decimal(x), "y":crate::field_decimal(y)
                })
            }
            #[cfg(feature = "zkir-321")]
            Self::Foreign(value) => serde_json::json!({
                "kind":"foreign",
                "type":value.foreign_type().source_name(),
                "bytes":value.to_bytes().expect("checked foreign value serializes canonically")
            }),
        }
    }
}
pub(crate) fn unsigned_literal(bound: &str, value: &str) -> Result<Value> {
    let maximum = maximum(bound)?;
    let number = canonical_unsigned(value, &maximum)?;
    Ok(Value::UInt { number, maximum })
}
pub(crate) enum UnsignedOp {
    Add,
    Sub,
    Mul,
}
pub(crate) fn unsigned_arithmetic(
    op: UnsignedOp,
    left: Value,
    right: Value,
    bound: &str,
) -> Result<Value> {
    left.validate()?;
    right.validate()?;
    let (
        Value::UInt {
            number: a,
            maximum: m,
        },
        Value::UInt {
            number: b,
            maximum: n,
        },
    ) = (left, right)
    else {
        bail!("unsigned arithmetic requires unsigned operands")
    };
    let inferred = match op {
        UnsignedOp::Add => &m + &n,
        UnsignedOp::Sub => m,
        UnsignedOp::Mul => &m * &n,
    };
    ensure!(
        inferred <= max_uint(),
        "unsigned result type exceeds target maximum"
    );
    ensure!(
        maximum(bound)? == inferred,
        "unsigned result bound mismatch"
    );
    let number = match op {
        UnsignedOp::Add => a + b,
        UnsignedOp::Mul => a * b,
        UnsignedOp::Sub => {
            ensure!(a >= b, "unsigned subtraction underflow");
            a - b
        }
    };
    let result = Value::UInt {
        number,
        maximum: inferred,
    };
    result.validate()?;
    Ok(result)
}
