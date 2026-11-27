//! Checked native codecs for the supported foreign curve values.

use crate::zkir::{
    ir_instructions::{
        add::add_offcircuit,
        ec_mul::ec_mul_offcircuit,
        encode::{decode_offcircuit, encode_offcircuit},
        from_bytes::from_bytes_offcircuit,
        from_coordinates::from_coordinates_offcircuit,
        into_coordinates::into_coordinates_offcircuit,
        inv::inv_offcircuit,
        mul::mul_offcircuit,
        neg::neg_offcircuit,
        to_bytes::to_bytes_offcircuit,
    },
    ir_types::{IrType, IrValue},
};
use anyhow::{Result, bail, ensure};
use transient_crypto::curve::Fr;

const SECP256K1_GENERATOR: &[u8; 33] = &[
    0x02, 0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac, 0x55, 0xa0, 0x62, 0x95, 0xce, 0x87, 0x0b,
    0x07, 0x02, 0x9b, 0xfc, 0xdb, 0x2d, 0xce, 0x28, 0xd9, 0x59, 0xf2, 0x81, 0x5b, 0x16, 0xf8, 0x17,
    0x98,
];
const SECP256R1_GENERATOR: &[u8; 33] = &[
    0x03, 0x6b, 0x17, 0xd1, 0xf2, 0xe1, 0x2c, 0x42, 0x47, 0xf8, 0xbc, 0xe6, 0xe5, 0x63, 0xa4, 0x40,
    0xf2, 0x77, 0x03, 0x7d, 0x81, 0x2d, 0xeb, 0x33, 0xa0, 0xf4, 0xa1, 0x39, 0x45, 0xd8, 0x98, 0xc2,
    0x96,
];
const CURVE25519_GENERATOR: &[u8; 32] = &[
    0x58, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
    0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
];
const CURVE25519_IDENTITY: &[u8; 32] = &[
    0x01, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0,
];

/// A supported foreign curve family.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ForeignFamily {
    Secp256k1,
    Secp256r1,
    Curve25519,
}

/// A role within a foreign curve family.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ForeignRole {
    Base,
    Scalar,
    Point,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ForeignUnaryOp {
    Neg,
    Inv,
    MulGenerator,
    X,
    Y,
}

impl ForeignUnaryOp {
    pub fn parse(operation: &str) -> Result<Self> {
        match operation {
            "neg" => Ok(Self::Neg),
            "inv" => Ok(Self::Inv),
            "mulGenerator" => Ok(Self::MulGenerator),
            "x" => Ok(Self::X),
            "y" => Ok(Self::Y),
            _ => bail!("unsupported foreign unary operation"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ForeignBinaryOp {
    Add,
    Sub,
    Mul,
    EcMul,
    FromCoordinates,
}

impl ForeignBinaryOp {
    pub fn parse(operation: &str) -> Result<Self> {
        match operation {
            "add" => Ok(Self::Add),
            "sub" => Ok(Self::Sub),
            "mul" => Ok(Self::Mul),
            "ecMul" => Ok(Self::EcMul),
            "fromCoordinates" => Ok(Self::FromCoordinates),
            _ => bail!("unsupported foreign binary operation"),
        }
    }
}

/// A closed foreign family and role pair.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ForeignType {
    family: ForeignFamily,
    role: ForeignRole,
}

impl ForeignType {
    pub const fn new(family: ForeignFamily, role: ForeignRole) -> Self {
        Self { family, role }
    }

    pub const fn family(self) -> ForeignFamily {
        self.family
    }

    pub const fn role(self) -> ForeignRole {
        self.role
    }

    pub fn parse_source_name(name: &str) -> Result<Self> {
        match name {
            "Secp256k1Base" => Ok(Self::new(ForeignFamily::Secp256k1, ForeignRole::Base)),
            "Secp256k1Scalar" => Ok(Self::new(ForeignFamily::Secp256k1, ForeignRole::Scalar)),
            "Secp256k1Point" => Ok(Self::new(ForeignFamily::Secp256k1, ForeignRole::Point)),
            "Secp256r1Base" => Ok(Self::new(ForeignFamily::Secp256r1, ForeignRole::Base)),
            "Secp256r1Scalar" => Ok(Self::new(ForeignFamily::Secp256r1, ForeignRole::Scalar)),
            "Secp256r1Point" => Ok(Self::new(ForeignFamily::Secp256r1, ForeignRole::Point)),
            "Curve25519Base" => Ok(Self::new(ForeignFamily::Curve25519, ForeignRole::Base)),
            "Curve25519Scalar" => Ok(Self::new(ForeignFamily::Curve25519, ForeignRole::Scalar)),
            "Curve25519Point" => Ok(Self::new(ForeignFamily::Curve25519, ForeignRole::Point)),
            _ => bail!("unsupported foreign type"),
        }
    }

    pub const fn source_name(self) -> &'static str {
        match (self.family, self.role) {
            (ForeignFamily::Secp256k1, ForeignRole::Base) => "Secp256k1Base",
            (ForeignFamily::Secp256k1, ForeignRole::Scalar) => "Secp256k1Scalar",
            (ForeignFamily::Secp256k1, ForeignRole::Point) => "Secp256k1Point",
            (ForeignFamily::Secp256r1, ForeignRole::Base) => "Secp256r1Base",
            (ForeignFamily::Secp256r1, ForeignRole::Scalar) => "Secp256r1Scalar",
            (ForeignFamily::Secp256r1, ForeignRole::Point) => "Secp256r1Point",
            (ForeignFamily::Curve25519, ForeignRole::Base) => "Curve25519Base",
            (ForeignFamily::Curve25519, ForeignRole::Scalar) => "Curve25519Scalar",
            (ForeignFamily::Curve25519, ForeignRole::Point) => "Curve25519Point",
        }
    }

    pub const fn byte_len(self) -> usize {
        match (self.family, self.role) {
            (ForeignFamily::Curve25519, ForeignRole::Point)
            | (_, ForeignRole::Base | ForeignRole::Scalar) => 32,
            (_, ForeignRole::Point) => 33,
        }
    }

    pub fn unary_result(self, operation: ForeignUnaryOp) -> Result<Self> {
        match operation {
            ForeignUnaryOp::Neg => Ok(self),
            ForeignUnaryOp::Inv => {
                ensure!(
                    self.role != ForeignRole::Point,
                    "cannot invert a foreign point"
                );
                Ok(self)
            }
            ForeignUnaryOp::MulGenerator => {
                ensure!(
                    self.role == ForeignRole::Scalar,
                    "generator multiplication requires a scalar"
                );
                Ok(Self::new(self.family, ForeignRole::Point))
            }
            ForeignUnaryOp::X | ForeignUnaryOp::Y => {
                ensure!(
                    self.role == ForeignRole::Point,
                    "coordinate extraction requires a point"
                );
                Ok(Self::new(self.family, ForeignRole::Base))
            }
        }
    }

    pub fn binary_result(self, operation: ForeignBinaryOp, right: Self) -> Result<Self> {
        ensure!(self.family == right.family, "foreign curve family mismatch");
        match operation {
            ForeignBinaryOp::Add | ForeignBinaryOp::Sub => {
                ensure!(self.role == right.role, "foreign operand role mismatch");
                Ok(self)
            }
            ForeignBinaryOp::Mul => {
                ensure!(self.role == right.role, "foreign operand role mismatch");
                ensure!(
                    self.role != ForeignRole::Point,
                    "point multiplication requires a scalar"
                );
                Ok(self)
            }
            ForeignBinaryOp::EcMul => {
                ensure!(
                    self.role == ForeignRole::Point && right.role == ForeignRole::Scalar,
                    "point multiplication requires a matching scalar"
                );
                Ok(self)
            }
            ForeignBinaryOp::FromCoordinates => {
                ensure!(
                    self.role == ForeignRole::Base && right.role == ForeignRole::Base,
                    "coordinate construction requires two base values"
                );
                Ok(Self::new(self.family, ForeignRole::Point))
            }
        }
    }

    pub fn native_type(self) -> IrType {
        match (self.family, self.role) {
            (ForeignFamily::Secp256k1, ForeignRole::Base) => IrType::Secp256k1Base,
            (ForeignFamily::Secp256k1, ForeignRole::Scalar) => IrType::Secp256k1Scalar,
            (ForeignFamily::Secp256k1, ForeignRole::Point) => IrType::Secp256k1Point,
            (ForeignFamily::Secp256r1, ForeignRole::Base) => IrType::Secp256r1Base,
            (ForeignFamily::Secp256r1, ForeignRole::Scalar) => IrType::Secp256r1Scalar,
            (ForeignFamily::Secp256r1, ForeignRole::Point) => IrType::Secp256r1Point,
            (ForeignFamily::Curve25519, ForeignRole::Base) => IrType::Curve25519Base,
            (ForeignFamily::Curve25519, ForeignRole::Scalar) => IrType::Curve25519Scalar,
            (ForeignFamily::Curve25519, ForeignRole::Point) => IrType::Curve25519Point,
        }
    }
}

/// A native value whose foreign type and canonical transport have been checked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForeignValue {
    ty: ForeignType,
    value: IrValue,
}

impl ForeignValue {
    /// Construct the field zero or group identity for this foreign type.
    pub fn zero(ty: ForeignType) -> Result<Self> {
        if ty.family == ForeignFamily::Curve25519 && ty.role == ForeignRole::Point {
            return Self::from_bytes(ty, CURVE25519_IDENTITY);
        }
        Self::from_bytes(ty, &vec![0; ty.byte_len()])
    }

    /// Decode the exact canonical native-field encoding for `ty`.
    pub fn decode(ty: ForeignType, encoded: &[Fr]) -> Result<Self> {
        let native_type = ty.native_type();
        ensure!(
            encoded.len() == native_type.encoded_len(),
            "wrong native field count for {native_type:?}"
        );
        let value = decode_offcircuit(encoded, &native_type)?;
        ensure!(
            value_matches_type(&value, ty),
            "native decoder returned the wrong foreign type"
        );
        Ok(Self { ty, value })
    }

    /// Construct from canonical little-endian bytes, rejecting modulo aliases.
    pub fn from_bytes(ty: ForeignType, bytes: &[u8]) -> Result<Self> {
        ensure!(bytes.len() == ty.byte_len(), "wrong foreign byte length");
        let value = from_bytes_offcircuit(&ty.native_type(), bytes)?;
        let value = Self::checked_native(ty, value)?;
        ensure!(
            value.to_bytes()?.as_slice() == bytes,
            "foreign bytes are not canonical"
        );
        Ok(value)
    }

    /// Construct from source Bytes using the pinned reducing field decoder.
    pub fn from_bytes_reducing(ty: ForeignType, bytes: &[u8]) -> Result<Self> {
        if ty.role == ForeignRole::Point {
            return Self::from_bytes(ty, bytes);
        }
        ensure!(
            bytes.len() <= crate::scalars::MAX_BYTE_OPERATION_LENGTH,
            "foreign Bytes input exceeds compiler limit"
        );
        let value = from_bytes_offcircuit(&ty.native_type(), bytes)?;
        Self::checked_native(ty, value)
    }

    pub const fn foreign_type(&self) -> ForeignType {
        self.ty
    }

    pub fn native_type(&self) -> IrType {
        self.ty.native_type()
    }

    /// Encode with the pinned native codec, preserving its canonical limb rules.
    pub fn encode(&self) -> Result<Vec<Fr>> {
        encode_native(self.ty, &self.value)
    }

    /// Serialize to canonical field bytes or the native compressed point form.
    pub fn to_bytes(&self) -> Result<Vec<u8>> {
        ensure!(
            value_matches_type(&self.value, self.ty),
            "foreign value does not match its declared type"
        );
        match to_bytes_offcircuit(&self.value)? {
            IrValue::Bytes(bytes) => {
                ensure!(
                    bytes.len() == self.ty.byte_len(),
                    "native encoder returned wrong byte count"
                );
                Ok(bytes)
            }
            _ => bail!("native byte encoder returned a non-byte value"),
        }
    }

    pub fn unary(&self, operation: ForeignUnaryOp) -> Result<Self> {
        let result_type = self.ty.unary_result(operation)?;
        let result = match operation {
            ForeignUnaryOp::Neg => neg_offcircuit(&self.value)?,
            ForeignUnaryOp::Inv => inv_offcircuit(&self.value)?,
            ForeignUnaryOp::MulGenerator => {
                let generator_type = ForeignType::new(self.ty.family, ForeignRole::Point);
                let bytes = match self.ty.family {
                    ForeignFamily::Secp256k1 => SECP256K1_GENERATOR.as_slice(),
                    ForeignFamily::Secp256r1 => SECP256R1_GENERATOR.as_slice(),
                    ForeignFamily::Curve25519 => CURVE25519_GENERATOR.as_slice(),
                };
                let generator = from_bytes_offcircuit(&generator_type.native_type(), bytes)?;
                ec_mul_offcircuit(&generator, &self.value)?
            }
            ForeignUnaryOp::X | ForeignUnaryOp::Y => {
                let (x, y) = into_coordinates_offcircuit(&self.value)?;
                if operation == ForeignUnaryOp::X { x } else { y }
            }
        };
        Self::checked_native(result_type, result)
    }

    pub fn binary(&self, operation: ForeignBinaryOp, right: &Self) -> Result<Self> {
        let result_type = self.ty.binary_result(operation, right.ty)?;
        let result = match operation {
            ForeignBinaryOp::Add => add_offcircuit(&self.value, &right.value)?,
            ForeignBinaryOp::Sub => {
                let negative = neg_offcircuit(&right.value)?;
                add_offcircuit(&self.value, &negative)?
            }
            ForeignBinaryOp::Mul => mul_offcircuit(&self.value, &right.value)?,
            ForeignBinaryOp::EcMul => ec_mul_offcircuit(&self.value, &right.value)?,
            ForeignBinaryOp::FromCoordinates => {
                from_coordinates_offcircuit(&self.value, &right.value)?
            }
        };
        Self::checked_native(result_type, result)
    }

    fn checked_native(ty: ForeignType, value: IrValue) -> Result<Self> {
        let encoded = encode_native(ty, &value)?;
        Self::decode(ty, &encoded)
    }
}

fn encode_native(ty: ForeignType, value: &IrValue) -> Result<Vec<Fr>> {
    ensure!(
        value_matches_type(value, ty),
        "native value does not match its declared foreign type"
    );
    let encoded = encode_offcircuit(value);
    ensure!(
        encoded.len() == ty.native_type().encoded_len(),
        "native encoder returned the wrong field count"
    );
    encoded
        .into_iter()
        .map(|field| match field {
            IrValue::Native(value) => Ok(value),
            _ => bail!("native encoder returned a non-native field"),
        })
        .collect()
}

fn value_matches_type(value: &IrValue, ty: ForeignType) -> bool {
    matches!(
        (ty.family, ty.role, value),
        (
            ForeignFamily::Secp256k1,
            ForeignRole::Base,
            IrValue::Secp256k1Base(_)
        ) | (
            ForeignFamily::Secp256k1,
            ForeignRole::Scalar,
            IrValue::Secp256k1Scalar(_)
        ) | (
            ForeignFamily::Secp256k1,
            ForeignRole::Point,
            IrValue::Secp256k1Point(_)
        ) | (
            ForeignFamily::Secp256r1,
            ForeignRole::Base,
            IrValue::Secp256r1Base(_)
        ) | (
            ForeignFamily::Secp256r1,
            ForeignRole::Scalar,
            IrValue::Secp256r1Scalar(_)
        ) | (
            ForeignFamily::Secp256r1,
            ForeignRole::Point,
            IrValue::Secp256r1Point(_)
        ) | (
            ForeignFamily::Curve25519,
            ForeignRole::Base,
            IrValue::Curve25519Base(_)
        ) | (
            ForeignFamily::Curve25519,
            ForeignRole::Scalar,
            IrValue::Curve25519Scalar(_)
        ) | (
            ForeignFamily::Curve25519,
            ForeignRole::Point,
            IrValue::Curve25519Point(_)
        )
    )
}
