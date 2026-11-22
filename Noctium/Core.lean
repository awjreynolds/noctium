import Noctium.ScalarPolicy

namespace Noctium

namespace Jubjub

/-- Scalar order from the pinned `midnight-curves` Jubjub field. -/
def scalarOrder : Nat :=
  6554484396890773809930967563523245729705921265872317281365359162392183254199

/-- The pinned Jubjub Edwards coefficient, equal to -(10240 / 10241). -/
private def edwardsCoefficient : Nat :=
  0x2a9318e74bfa2b48f5fd9207e6bd7fd4292d7f6d37579d2601065fd6d6343eb1

def pointValid (x y : Nat) : Bool :=
  Foreign.edwardsPrimePoint Field.modulus edwardsCoefficient scalarOrder x y

end Jubjub

structure SourceSpan where
  file : String := ""
  line : Nat := 1
  column : Nat := 1
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Ty where
  | native | bool
  | uint (maximum : Nat)
  | bytes (length : Nat)
  /-- Dynamically sized host bytes with the native FAB Compress projection. -/
  | opaqueBytes
  /-- Valid UTF-8 text with the native FAB Compress projection. -/
  | opaqueString
  | jubjubScalar | jubjubPoint
  | foreign (kind : Foreign.Kind)
  deriving Repr, BEq, DecidableEq, Inhabited

def Ty.scalarKind : Ty → ScalarPolicy.Kind
  | .native => .native
  | .bool => .bool
  | .uint maximum => .uint maximum
  | .bytes length => .bytes length
  | .opaqueBytes => .opaqueBytes
  | .opaqueString => .opaqueBytes
  | .jubjubScalar => .jubjubScalar
  | .jubjubPoint => .jubjubPoint
  | .foreign kind => .foreign kind

def Ty.isBytes : Ty → Bool
  | .bytes _ => true
  | _ => false

def Ty.isOpaqueBytes : Ty → Bool
  | .opaqueBytes => true
  | _ => false

def Ty.isOpaqueString : Ty → Bool
  | .opaqueString => true
  | _ => false

def Ty.isJubjub : Ty → Bool
  | .jubjubScalar | .jubjubPoint => true
  | _ => false

def Ty.isJubjubScalar : Ty → Bool
  | .jubjubScalar => true
  | _ => false

def Ty.isJubjubPoint : Ty → Bool
  | .jubjubPoint => true
  | _ => false

def Ty.isForeign : Ty → Bool
  | .foreign _ => true
  | _ => false

def Ty.nativeCallFieldCount : Ty → Nat
  | .bytes length => (length + 30) / 31
  | .jubjubPoint => 2
  | .foreign kind => kind.encodedFieldCount
  | _ => 1

end Noctium
