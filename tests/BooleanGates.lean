import Noctium.Frontend
import Noctium.Disclosure
import Noctium.Backend.NativeProducer

open scoped Noctium
open Noctium
open Lean
open Noctium.Backend.Native

noctium_circuit booleanInputs where
  private left : Bool
  private right : Bool
  output notLeftValue : Bool := disclose(boolNot(left))
  output andValue : Bool := disclose(boolAnd(left, right))
  output orValue : Bool := disclose(boolOr(left, right))
  output xorValue : Bool := disclose(boolXor(left, right))
  output xorThreeValue : Bool := disclose(boolXor(boolXor(left, right), true))
end

noctium_circuit andEagerInput where
  private enabled : Bool
  output andGuardValue : Bool := disclose(boolAnd(false, assertThen(enabled, true)))
end

noctium_circuit orEagerInput where
  private enabled : Bool
  output orGuardValue : Bool := disclose(boolOr(true, assertThen(enabled, false)))
end

noctium_contract BooleanGates where
  entry truthTable uses booleanInputs where
    return andResult : Bool := disclose(andValue)
    return orResult : Bool := disclose(orValue)
    return notLeftResult : Bool := disclose(notLeftValue)
    return xorResult : Bool := disclose(xorValue)
    return xorThreeResult : Bool := disclose(xorThreeValue)
  end
  entry andEager uses andEagerInput where
    return andGuardResult : Bool := disclose(andGuardValue)
  end
  entry orEager uses orEagerInput where
    return orGuardResult : Bool := disclose(orGuardValue)
  end
end

private def booleanEvalContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => pure 0
}

private def booleanGateResult (left right : _root_.Bool) :
    Except String (_root_.Bool × _root_.Bool × _root_.Bool × _root_.Bool × _root_.Bool) := do
  let notLeftResult ← (Expr.boolXor (.bool left) (.bool Bool.true)).eval booleanEvalContext []
  let andResult ← (Expr.boolAnd (.bool left) (.bool right)).eval booleanEvalContext []
  let orResult ← (Expr.boolOr (.bool left) (.bool right)).eval booleanEvalContext []
  let xorResult ← (Expr.boolXor (.bool left) (.bool right)).eval booleanEvalContext []
  let xorThreeResult ← (Expr.boolXor (Expr.boolXor (.bool left) (.bool right)) (.bool Bool.true)).eval
    booleanEvalContext []
  pure (notLeftResult, andResult, orResult, xorResult, xorThreeResult)

#guard match booleanGateResult Bool.false Bool.false with
  | .ok (Bool.true, Bool.false, Bool.false, Bool.false, Bool.true) => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match booleanGateResult Bool.false Bool.true with
  | .ok (Bool.true, Bool.false, Bool.true, Bool.true, Bool.false) => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match booleanGateResult Bool.true Bool.false with
  | .ok (Bool.false, Bool.false, Bool.true, Bool.true, Bool.false) => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match booleanGateResult Bool.true Bool.true with
  | .ok (Bool.false, Bool.true, Bool.true, Bool.false, Bool.true) => _root_.Bool.true
  | _ => _root_.Bool.false

private def failingBool : Expr .bool := .assertE (.bool Bool.false) (.bool Bool.true)

#guard match (Expr.boolAnd (.bool Bool.false) failingBool).eval booleanEvalContext [] with
  | .error "helper assertion failed" => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match (Expr.boolOr (.bool Bool.true) failingBool).eval booleanEvalContext [] with
  | .error "helper assertion failed" => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match (Expr.boolXor (.bool Bool.false) failingBool).eval booleanEvalContext [] with
  | .error "helper assertion failed" => _root_.Bool.true
  | _ => _root_.Bool.false

noctium_circuit booleanNotRetainsPartialOperand where
  private enabled : Bool
  let unused : Bool := boolNot(assertThen(enabled, true))
  output result : Bool := true
end

#guard match booleanNotRetainsPartialOperand.constraints with
  | [constraint] => match constraint.eval booleanEvalContext [("enabled", .bool Bool.false)] with
    | .error "helper assertion failed" => _root_.Bool.true
    | _ => _root_.Bool.false
  | _ => _root_.Bool.false

noctium_witness_circuit booleanNotAuthoring where
  public value : Bool
  output inverted : Bool := boolNot(value)
end

private def booleanNotAuthoringResult (value : _root_.Bool) :=
  booleanNotAuthoring.run booleanEvalContext [("value", .bool value)]

#guard match booleanNotAuthoringResult Bool.false with
  | .ok [("inverted", .bool Bool.true)] => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match booleanNotAuthoringResult Bool.true with
  | .ok [("inverted", .bool Bool.false)] => _root_.Bool.true
  | _ => _root_.Bool.false

/-- error: Noctium expression type mismatch -/
#guard_msgs in
noctium_circuit invalidBooleanNotType where
  private value : Native
  output result : Bool := boolNot(value)
end

#guard match (Expr.boolAnd (.bool Bool.true) (.bool Bool.false)).validate
    {Capabilities.source with typedBoolean := _root_.Bool.false} [] with
  | .error "target lacks typed Boolean support" => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match Disclosure.circuit {
  name := "undisclosedBooleanGate"
  inputs := [
    {name := "left", ty := .bool, visibility := .private},
    {name := "right", ty := .bool, visibility := .private}]
  outputs := [{name := "result", ty := .bool, value := (Expr.boolXor (.ref "left") (.ref "right"))}]
} with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

/-- error: Noctium expression type mismatch -/
#guard_msgs in
noctium_circuit invalidBooleanGateType where
  private left : Bool
  private right : Native
  output result : Bool := boolAnd(left, right)
end

private def booleanGateProducerAccepts (opcode : String)
    (types : List NativeValueType) : _root_.Bool := Id.run do
  let expected : Expected := {
    mode := .relation, inputs := [], groups := [], returns := [], assertions := [], bounds := []}
  let names := types.zipIdx.map fun (_, index) => s!"%bool{index}"
  let definitions := (names.zip types).map fun (name, valueType) =>
    (name, ({term := .input name, maximum := 1, valueType} : Fact))
  let state : State := {definitions := definitions}
  let instruction := Json.mkObj [
    ("op", toJson opcode), ("inputs", toJson names), ("output", toJson ("%out" : String))]
  return (validateInstruction expected state instruction).isOk

#guard booleanGateProducerAccepts "and" [.bool, .bool]
#guard booleanGateProducerAccepts "and" [.bool]
#guard booleanGateProducerAccepts "or" [.bool, .bool]
#guard booleanGateProducerAccepts "xor" [.bool, .bool]
#guard !(booleanGateProducerAccepts "and" [.native, .native])
#guard !(booleanGateProducerAccepts "or" [.bool, .native])
#guard !(booleanGateProducerAccepts "xor" [])

private def booleanConstantAccepts (encoding : List String) : _root_.Bool := Id.run do
  let expected : Expected := {
    mode := .relation, inputs := [], groups := [], returns := [], assertions := [], bounds := []}
  let instruction := Json.mkObj [
    ("op", toJson ("load_constant" : String)), ("type", toJson ("Bool" : String)),
    ("encoding", toJson encoding), ("output", toJson ("%out" : String))]
  return (validateInstruction expected {} instruction).isOk

#guard booleanConstantAccepts ["0x00"]
#guard booleanConstantAccepts ["0x01"]
#guard !(booleanConstantAccepts ["0x02"])
#guard !(booleanConstantAccepts ["%bool0"])
#guard !(booleanConstantAccepts ["0x0100"])
#guard !(booleanConstantAccepts [])
