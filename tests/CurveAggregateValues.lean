import Noctium.Types.ValueSchema
import Noctium.Types.ValueExpressions

open Noctium Noctium.Types

def curveAggregateEnvironment : CompositeEnv := {}

def curveAggregateType : CompositeType := .tuple [
  .scalar .jubjubScalar,
  .scalar .jubjubPoint,
  .scalar (.foreign (.base .secp256k1)),
  .scalar (.foreign (.scalar .curve25519)),
  .scalar (.foreign (.point .curve25519)),
  .scalar (.foreign (.point .secp256k1))]

def curveAggregateValue : AggregateValue := .tuple [
  .scalar .jubjubScalar 17,
  .jubjubPoint 0 1,
  .scalar (.foreign (.base .secp256k1)) 42,
  .scalar (.foreign (.scalar .curve25519)) 7,
  .foreignPoint .curve25519 .identity,
  .foreignPoint .secp256k1 .identity]

private def compiledCurveAggregate : Except String CompiledType :=
  (compileType curveAggregateEnvironment curveAggregateType).mapError (·.message)

private def accepted (value : Except String α) : Bool :=
  match value with | .ok _ => true | .error _ => false

private def rejected (value : Except String α) : Bool := !accepted value

private def checkedExpressionWidth : Except String Nat := do
  let type ← compiledCurveAggregate
  let value ← checkValue type curveAggregateValue
  let expression ← literal type value
  pure (← flattenExpression type [] expression).length

#guard match compiledCurveAggregate with
  | .ok type => type.checked.expandedLeaves == 16 && type.checked.layoutNodes == 7
  | .error _ => false

#guard match (do
  let type ← compiledCurveAggregate
  let encoded ← encode type curveAggregateValue
  let decoded ← decode type encoded
  unless decoded == curveAggregateValue do throw "curve aggregate wire roundtrip changed the value"
  let checked ← decodeChecked type encoded
  unless checked.leaves.length == type.checked.expandedLeaves do throw "curve aggregate wire roundtrip changed leaf count") with
  | .ok () => true
  | .error _ => false

#guard match checkedExpressionWidth with | .ok 16 => true | _ => false

#guard match (do
  let type ← compiledCurveAggregate
  let json ← schemaJson type
  unless (json.compress.splitOn "\"kind\":\"curve\"").length == 7 do
    throw "curve schema must mark each logical curve leaf"
  unless (json.compress.splitOn "Secp256k1Point").length > 1 &&
      (json.compress.splitOn "Curve25519Point").length > 1 do
    throw "curve schema lost its nominal type names") with
  | .ok () => true
  | .error _ => false

#guard match (do
  let type ← compiledCurveAggregate
  let value ← checkValue type curveAggregateValue
  let json ← valueJson type value
  unless (json.compress.splitOn "jubjubPoint").length == 2 &&
      (json.compress.splitOn "Curve25519Point").length == 2 &&
      (json.compress.splitOn "Secp256k1Point").length == 2 do
    throw "curve value JSON lost a typed curve value") with
  | .ok () => true
  | .error _ => false

#guard rejected (do
  let type ← (compileType curveAggregateEnvironment (.scalar .jubjubPoint)).mapError (·.message)
  discard (checkValue type (.jubjubPoint 0 0)))

#guard rejected (do
  let type ← (compileType curveAggregateEnvironment (.scalar (.foreign (.point .secp256k1)))).mapError (·.message)
  discard (checkValue type (.foreignPoint .secp256k1 (.affine 0 0))))

#guard rejected (do
  let type ← (compileType curveAggregateEnvironment (.scalar .jubjubPoint)).mapError (·.message)
  discard (unflatten type [0]))
