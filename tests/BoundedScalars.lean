import Noctium.Compiler
import Noctium.Semantics
open Noctium
section Source
open scoped Noctium

noctium_circuit unsignedSum where
  public expected : UIntRange 511
  private left : UInt 8
  private right : UInt 8
  let sum : UIntRange 511 := add(left, right)
  assert eq(sum, expected)
  output result : UIntRange 511 := disclose(sum)
end

noctium_circuit unsignedProduct where
  private left : UInt 8
  private right : UInt 8
  output result : UIntRange 65026 := disclose(mul(left, right))
end

noctium_circuit unsignedDifference where
  private left : UInt 8
  private right : UInt 8
  output result : UInt 8 := disclose(sub(left, right))
end

noctium_circuit unsignedOrdinaryBoundaries where
  private value : UInt 8
  private zeroRange : UIntRange 1
  let typedZero : UInt 8 := uint(0)
  output literalZero : UInt 8 := disclose(add(value, uint(0)))
  output rangeZero : UInt 8 := disclose(add(value, zeroRange))
  output typedZeroSum : UIntRange 511 := disclose(add(value, typedZero))
end

noctium_circuit unsignedMaximumMultiplyBit where
  private value : UInt 248
  private bit : UInt 1
  output result : UInt 248 := disclose(mul(value, bit))
end

noctium_circuit unsignedMaximumAddZero where
  private value : UInt 248
  private zero : UIntRange 1
  output result : UInt 248 := disclose(add(value, zero))
end

noctium_circuit scalarCasts where
  private field : Native
  private flag : Bool
  output narrowed : UInt 8 := disclose(cast(UInt 8, field))
  output truthy : Bool := disclose(cast(Bool, field))
  output bit : UInt 1 := disclose(cast(UInt 1, flag))
  output widened : Native := disclose(cast(Native, cast(UInt 8, field)))
end

noctium_circuit scalarDefaults where
  output field : Native := default(Native)
  output flag : Bool := default(Bool)
  output zero : UInt 0 := default(UInt 0)
  output contextual : UInt 8 := 255
  output prefixed : UIntRange 3 := uint(2)
  output mixed : Native := add(uint(2), 3)
  output joined : UIntRange 8 := select(true, uint(2), uint(7))
end

noctium_circuit unusedUnderflow where
  private left : UInt 8
  private right : UInt 8
  let ignored : UInt 8 := sub(left, right)
  output value : UInt 8 := disclose(left)
end

noctium_circuit unusedNarrowing where
  private field : Native
  let ignored : Native := cast(Native, cast(UInt 8, field))
  output value : Native := disclose(field)
end

noctium_circuit unusedBooleanUnderflow where
  private left : UInt 8
  private right : UInt 8
  let ignored : Bool := eq(sub(left, right), uint(0))
  output value : UInt 8 := disclose(left)
end

noctium_circuit unusedNativeUnderflow where
  private left : UInt 8
  private right : UInt 8
  let ignored : Native := add(sub(left, right), 0)
  output value : UInt 8 := disclose(left)
end

noctium_circuit unusedHashUnderflow where
  private left : UInt 8
  private right : UInt 8
  let ignored : Native := poseidon2(1, sub(left, right), 0)
  output value : UInt 8 := disclose(left)
end

noctium_circuit unusedSelectionUnderflow where
  private left : UInt 8
  private right : UInt 8
  let ignored : Bool := select(false, eq(sub(left, right), uint(0)), false)
  output value : UInt 8 := disclose(left)
end

noctium_circuit zeroBound where
  private zero : UInt 0
  output value : UInt 0 := disclose(zero)
end

noctium_circuit zeroNarrowing where
  private flag : Bool
  output zero : UInt 0 := disclose(cast(UInt 0, flag))
end

noctium_circuit topWidth where
  private value : UInt 248
  output result : UInt 248 := disclose(value)
end

noctium_contract UnsignedLedger where
  cell total : UIntRange 511
  entry apply uses unsignedSum where
    read total as old
    require eq(old, 0)
    write total := result
  end
end

end Source

private def ctx : EvalContext := {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"}
private def ledgerEntry : Entrypoint := UnsignedLedger.entrypoints.headD {name := "", circuit := {name := ""}}
private def goodSum : EvalEnv := [
  ("expected", .uint 510 510), ("left", .uint 255 255), ("right", .uint 255 255)]

#guard match unsignedSum.run ctx goodSum with
  | .ok [("result", .uint 510 510)] => Bool.true | _ => Bool.false
#guard match unsignedSum.run ctx [
    ("expected", .uint 510 511), ("left", .uint 255 255), ("right", .uint 255 255)] with
  | .error _ => Bool.true | _ => Bool.false
#guard match unsignedSum.run ctx [
    ("expected", .uint 510 510), ("left", .uint 255 256), ("right", .uint 255 254)] with
  | .error _ => Bool.true | _ => Bool.false
#guard match unsignedProduct.run ctx [("left", .uint 255 255), ("right", .uint 255 255)] with
  | .ok [("result", .uint 65025 65025)] => Bool.true | _ => Bool.false
#guard match unsignedDifference.run ctx [("left", .uint 255 3), ("right", .uint 255 5)] with
  | .error "unsigned subtraction underflow" => Bool.true | _ => Bool.false
#guard match unsignedDifference.run ctx [("left", .uint 255 255), ("right", .uint 255 1)] with
  | .ok [("result", .uint 255 254)] => Bool.true | _ => Bool.false
#guard match unsignedDifference.run ctx [("left", .uint 255 255), ("right", .uint 255 0)] with
  | .ok [("result", .uint 255 255)] => Bool.true | _ => Bool.false
#guard match unsignedOrdinaryBoundaries.run ctx [
    ("value", .uint 255 255), ("zeroRange", .uint 0 0)] with
  | .ok [("literalZero", .uint 255 255), ("rangeZero", .uint 255 255),
      ("typedZeroSum", .uint 510 255)] => Bool.true | _ => Bool.false
#guard match unsignedMaximumMultiplyBit.run ctx [
    ("value", .uint ScalarPolicy.maxUint ScalarPolicy.maxUint), ("bit", .uint 1 1)] with
  | .ok [("result", .uint maximum actual)] => maximum == ScalarPolicy.maxUint && actual == ScalarPolicy.maxUint | _ => Bool.false
#guard match unsignedMaximumMultiplyBit.run ctx [
    ("value", .uint ScalarPolicy.maxUint ScalarPolicy.maxUint), ("bit", .uint 1 2)] with
  | .error _ => Bool.true | _ => Bool.false
#guard match unsignedMaximumAddZero.run ctx [
    ("value", .uint ScalarPolicy.maxUint ScalarPolicy.maxUint), ("zero", .uint 0 0)] with
  | .ok [("result", .uint maximum actual)] => maximum == ScalarPolicy.maxUint && actual == ScalarPolicy.maxUint | _ => Bool.false
#guard match scalarCasts.run ctx [("field", .native 255), ("flag", .bool Bool.true)] with
  | .ok [("narrowed", .uint 255 255), ("truthy", .bool Bool.true),
      ("bit", .uint 1 1), ("widened", .native 255)] => Bool.true | _ => Bool.false
#guard match scalarCasts.run ctx [("field", .native 256), ("flag", .bool Bool.false)] with
  | .error _ => Bool.true | _ => Bool.false
#guard match scalarDefaults.run ctx [] with
  | .ok [("field", .native 0), ("flag", .bool Bool.false), ("zero", .uint 0 0),
      ("contextual", .uint 255 255), ("prefixed", .uint 2 2), ("mixed", .native 5),
      ("joined", .uint 7 2)] => Bool.true | _ => Bool.false
#guard match unusedUnderflow.run ctx [("left", .uint 255 3), ("right", .uint 255 5)] with
  | .error "unsigned subtraction underflow" => Bool.true | _ => Bool.false
#guard match unusedNarrowing.run ctx [("field", .native 256)] with
  | .error _ => Bool.true | _ => Bool.false
#guard unusedBooleanUnderflow.constraints.length == 1
#guard unusedNativeUnderflow.constraints.length == 1
#guard unusedHashUnderflow.constraints.length == 1
#guard unusedSelectionUnderflow.constraints.length == 1
#guard match unusedBooleanUnderflow.run ctx [("left", .uint 255 0), ("right", .uint 255 1)] with
  | .error "unsigned subtraction underflow" => Bool.true | _ => Bool.false
#guard match unusedNativeUnderflow.run ctx [("left", .uint 255 0), ("right", .uint 255 1)] with
  | .error "unsigned subtraction underflow" => Bool.true | _ => Bool.false
#guard match unusedHashUnderflow.run ctx [("left", .uint 255 0), ("right", .uint 255 1)] with
  | .error "unsigned subtraction underflow" => Bool.true | _ => Bool.false
#guard match unusedSelectionUnderflow.run ctx [("left", .uint 255 0), ("right", .uint 255 1)] with
  | .error "unsigned subtraction underflow" => Bool.true | _ => Bool.false
#guard match zeroBound.run ctx [("zero", .uint 0 0)] with
  | .ok [("value", .uint 0 0)] => Bool.true | _ => Bool.false
#guard match zeroBound.run ctx [("zero", .uint 0 1)] with
  | .error _ => Bool.true | _ => Bool.false
#guard match zeroNarrowing.run ctx [("flag", .bool Bool.true)] with
  | .error _ => Bool.true | _ => Bool.false
#guard match topWidth.run ctx [("value", .uint ScalarPolicy.maxUint ScalarPolicy.maxUint)] with
  | .ok [("result", .uint _ number)] => number == ScalarPolicy.maxUint | _ => Bool.false
#guard match topWidth.run ctx [("value", .uint ScalarPolicy.maxUint (ScalarPolicy.maxUint + 1))] with
  | .error _ => Bool.true | _ => Bool.false
#guard match ledgerEntry.run ctx goodSum {cells := [("total", .uint 510 0)]} with
  | .ok (_, state) => state.cells.lookup "total" == some (.uint 510 510)
  | _ => Bool.false
#guard match ledgerEntry.run ctx goodSum {cells := [("total", .uint 510 511)]} with
  | .error _ => Bool.true | _ => Bool.false

-- Ill-formed hand-built types must fail even when no expression references them.
private def invalidMaximum : Nat := ScalarPolicy.maxUint + 1
#guard match ({name := "unused", inputs := [⟨"unused", .uint invalidMaximum, .«private», {}⟩]} : Circuit).validate {} with
  | .error _ => Bool.true | _ => Bool.false
#guard match ({name := "unused", state := [{name := "bad", kind := .cell (.uint invalidMaximum)}]} : Contract).validate {} with
  | .error _ => Bool.true | _ => Bool.false
#guard match (Expr.uint 255 256).validate {} [] with
  | .error _ => Bool.true | _ => Bool.false
#guard match (Expr.uadd (Expr.uint ScalarPolicy.maxUint 0) (Expr.uint 1 0)).validate {} [] with
  | .error _ => Bool.true | _ => Bool.false
#guard match Backend.Zkir.lowerCircuit unsignedDifference with | .ok _ => Bool.true | _ => Bool.false
#guard match Backend.Zkir.lowerEntrypoint UnsignedLedger.state ledgerEntry with
  | .ok _ => Bool.true | _ => Bool.false

section SourceFailures
open scoped Noctium

/-- error: unsigned width exceeds target maximum -/
#guard_msgs in
noctium_circuit oversizedWidth where
  private value : UInt 249
end

/-- error: unsigned exclusive bound must be positive -/
#guard_msgs in
noctium_circuit zeroExclusive where
  private value : UIntRange 0
end

/-- error: unsigned constant exceeds its type -/
#guard_msgs in
noctium_circuit badConstant where
  output value : UInt 8 := 256
end

/-- error: Noctium expression type mismatch; use an explicit narrowing cast -/
#guard_msgs in
noctium_circuit implicitNarrowing where
  private wide : UInt 16
  output value : UInt 8 := wide
end

/-- error: boolean arithmetic requires an explicit cast -/
#guard_msgs in
noctium_circuit booleanArithmetic where
  private flag : Bool
  output value : Native := add(flag, 1)
end

/-- error: unsigned type exceeds target maximum -/
#guard_msgs in
noctium_circuit typeOverflow where
  private left : UInt 248
  output result : UInt 248 := add(left, uint(1))
end

/-- error: Noctium expression type mismatch; use an explicit narrowing cast -/
#guard_msgs in
noctium_circuit declaredZeroTooNarrow where
  private value : UInt 8
  let zero : UInt 8 := uint(0)
  output result : UInt 8 := add(value, zero)
end

/-- error: unsigned type exceeds target maximum -/
#guard_msgs in
noctium_circuit maxWidthAddBitOverflow where
  private value : UInt 248
  private bit : UInt 1
  output result : UInt 248 := add(value, bit)
end

end SourceFailures

example (a b m n : Nat) (ha : a ≤ m) (hb : b ≤ n) (hbound : m + n ≤ ScalarPolicy.maxUint) :
    (a + b) % Field.modulus = a + b := unsigned_addition_no_wrap a b m n ha hb hbound

example (a b : Nat) (hab : a < b) (hb : b ≤ ScalarPolicy.maxUint) :
    ScalarPolicy.maxUint < Field.modulus + a - b := unsigned_underflow_outside_range a b hab hb

example (a b : Nat) (hab : a < b) (hb : b ≤ ScalarPolicy.maxUint) :
    ScalarPolicy.maxUint < (Field.modulus + a - b) % Field.modulus :=
  unsigned_underflow_modulo_rejected a b hab hb
