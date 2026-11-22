import Lean
import Noctium.IR
import Noctium.Types.ValueSchema

namespace Noctium.NativeExpression
open Lean

def typeName : Ty → String
  | .native => "Native"
  | .bool => "Bool"
  | .uint maximum => s!"UIntRange<{maximum + 1}>"
  | .bytes byteLength => s!"Bytes<{byteLength}>"
  | .opaqueBytes => "OpaqueBytes"
  | .opaqueString => "OpaqueString"
  | .jubjubScalar => "JubjubScalar"
  | .jubjubPoint => "JubjubPoint"
  | .foreign kind => kind.sourceName

def foreignConstantJson (kind : Foreign.Kind) (value : kind.Denote) : Json :=
  Json.mkObj [
    ("tag", toJson ("foreignConstant" : String)),
    ("type", toJson kind.sourceName),
    ("encoding", toJson ((Foreign.encodeValue kind value).toOption.getD [] |>.map toString))]

/-- Keep sequential bindings flat in the host plan, even for wide call interfaces. -/
private def nativeLetJson (name : String) (value body : Json) : Json :=
  let binding := Json.arr #[toJson name, value]
  let rest : Except String (Array Json × Json) := do
    let tag ← (← body.getObjVal? "tag").getStr?
    match tag with
    | "lets" => pure (← (← body.getObjVal? "bindings").getArr?, ← body.getObjVal? "body")
    | "let" =>
      let next := Json.arr #[← body.getObjVal? "name", ← body.getObjVal? "value"]
      pure (#[next], ← body.getObjVal? "body")
    | _ => throw "not a binding"
  match rest with
  | .ok (bindings, tail) => Json.mkObj [("tag", toJson ("lets" : String)),
      ("bindings", Json.arr (#[binding] ++ bindings)), ("body", tail)]
  | .error _ => Json.mkObj [("tag", toJson ("let" : String)),
      ("name", toJson name), ("value", value), ("body", body)]

private def binaryJson (tag : String) (left right : Json) : Json :=
  Json.mkObj [("tag", toJson tag), ("left", left), ("right", right)]

private def unsignedJson (tag : String) (maximum : Nat) (left right : Json) : Json :=
  Json.mkObj [("tag", toJson tag), ("maximum", toJson (toString maximum)),
    ("left", left), ("right", right)]

mutual
private def nativeExpressionJson : Expr ty → Json
  | .copyValue value => nativeExpressionJson value
  | .native n => Json.mkObj [("tag", toJson ("constant" : String)), ("value", toJson (toString n))]
  | .bool b => Json.mkObj [("tag", toJson ("bool" : String)), ("value", toJson b)]
  | .uint maximum value => Json.mkObj [("tag", toJson ("uint" : String)),
      ("maximum", toJson (toString maximum)), ("value", toJson (toString value))]
  | .bytesField value index => Json.mkObj [("tag", toJson ("bytesField" : String)),
      ("value", nativeExpressionJson value), ("index", toJson index)]
  | .opaqueBytesProjection value => nativeExpressionJson value
  | .opaqueStringProjection value => nativeExpressionJson value
  | .opaqueBytesEmpty => Json.mkObj [
      ("tag", toJson ("opaqueEmpty" : String)), ("type", toJson ("OpaqueBytes" : String))]
  | .opaqueStringEmpty => Json.mkObj [
      ("tag", toJson ("opaqueEmpty" : String)), ("type", toJson ("OpaqueString" : String))]
  | .bytesAt value index => Json.mkObj [("tag", toJson ("byteAt" : String)),
      ("value", nativeExpressionJson value), ("index", toJson index)]
  | .bytesLiteral length values => Json.mkObj [("tag", toJson ("bytesLiteral" : String)),
      ("length", toJson length), ("values", toJson values)]
  | .reverseBytes (length := length) value => Json.mkObj [
      ("tag", toJson ("reverseBytes" : String)), ("length", toJson length),
      ("value", nativeExpressionJson value)]
  | .sliceBytes (length := length) value start stop => Json.mkObj [
      ("tag", toJson ("sliceBytes" : String)), ("length", toJson length),
      ("value", nativeExpressionJson value), ("start", toJson start), ("end", toJson stop)]
  | .concatBytes (leftLength := leftLength) (rightLength := rightLength) left right =>
      Json.mkObj [("tag", toJson ("concatBytes" : String)),
        ("leftLength", toJson leftLength), ("rightLength", toJson rightLength),
        ("left", nativeExpressionJson left), ("right", nativeExpressionJson right)]
  | .sha256 (length := length) value => Json.mkObj [
      ("tag", toJson ("sha256" : String)), ("length", toJson length),
      ("value", nativeExpressionJson value)]
  | .sha512 (length := length) value => Json.mkObj [
      ("tag", toJson ("sha512" : String)), ("length", toJson length),
      ("value", nativeExpressionJson value)]
  | .keccak256 (length := length) value => Json.mkObj [
      ("tag", toJson ("keccak256" : String)), ("length", toJson length),
      ("value", nativeExpressionJson value)]
  | .keccak256Secp256k1Point value => Json.mkObj [
      ("tag", toJson ("keccak256Secp256k1Point" : String)),
      ("value", nativeExpressionJson value)]
  | .reverseBytes32 value => Json.mkObj [("tag", toJson ("reverseBytes32" : String)),
      ("value", nativeExpressionJson value)]
  | .persistentHash32 value => Json.mkObj [("tag", toJson ("persistentHash32" : String)),
      ("value", nativeExpressionJson value)]
  | .bytes32Literal values => Json.mkObj [("tag", toJson ("bytes32Literal" : String)),
      ("values", toJson values)]
  | .persistentHashVector32 values => Json.mkObj [("tag", toJson ("persistentHashVector32" : String)),
      ("values", toJson (values.map nativeExpressionJson))]
  | .persistentHashNative value => Json.mkObj [("tag", toJson ("persistentHashNative" : String)),
      ("value", nativeExpressionJson value)]
  | .persistentHashNativeVector values => Json.mkObj [("tag", toJson ("persistentHashNativeVector" : String)),
      ("values", toJson (values.map nativeExpressionJson))]
  | .persistentHashFab environment type values => Id.run do
      let compiled := Types.compileType environment type
      let schema := match compiled with
        | .ok value => (Types.schemaJson value).toOption.getD Json.null
        | .error _ => Json.null
      let encodedValues := match compiled with
        | .ok value => match fabHashLayoutFields value.checked.value with
          | .ok fields => Json.arr
              (nativeExpressionFabValuesJson (fields.map Prod.snd) values)
          | .error _ => Json.arr #[]
        | .error _ => Json.arr #[]
      return Json.mkObj [
        ("tag", toJson ("persistentHashFab" : String)),
        ("schema", schema), ("values", encodedValues)]
  | .hashToCurveFab environment type values => Id.run do
      let compiled := Types.compileType environment type
      let schema := match compiled with
        | .ok value => (Types.schemaJson value).toOption.getD Json.null
        | .error _ => Json.null
      let encodedValues := match compiled with
        | .ok value => match fabHashLayoutFields value.checked.value with
          | .ok fields => Json.arr
              (nativeExpressionFabValuesJson (fields.map Prod.snd) values)
          | .error _ => Json.arr #[]
        | .error _ => Json.arr #[]
      return Json.mkObj [
        ("tag", toJson ("hashToCurveFab" : String)),
        ("schema", schema), ("values", encodedValues)]
  | .sha512Fab environment type values => Id.run do
      let compiled := Types.compileType environment type
      let schema := match compiled with
        | .ok value => (Types.schemaJson value).toOption.getD Json.null
        | .error _ => Json.null
      let encodedValues := match compiled with
        | .ok value => match fabHashLayoutFields value.checked.value with
          | .ok fields => Json.arr
              (nativeExpressionFabValuesJson (fields.map Prod.snd) values)
          | .error _ => Json.arr #[]
        | .error _ => Json.arr #[]
      return Json.mkObj [
        ("tag", toJson ("sha512Fab" : String)),
        ("schema", schema), ("values", encodedValues)]
  | .persistentCommitFab environment type opening values => Id.run do
      let compiled := Types.compileType environment type
      let schema := match compiled with
        | .ok value => (Types.schemaJson value).toOption.getD Json.null
        | .error _ => Json.null
      let encodedValues := match compiled with
        | .ok value => match fabHashLayoutFields value.checked.value with
          | .ok fields => Json.arr
              (nativeExpressionFabValuesJson (fields.map Prod.snd) values)
          | .error _ => Json.arr #[]
        | .error _ => Json.arr #[]
      return Json.mkObj [
        ("tag", toJson ("persistentCommitFab" : String)),
        ("schema", schema), ("opening", nativeExpressionJson opening),
        ("values", encodedValues)]
  | .transientCommitFab environment type opening values => Id.run do
      let compiled := Types.compileType environment type
      let schema := match compiled with
        | .ok value => (Types.schemaJson value).toOption.getD Json.null
        | .error _ => Json.null
      let encodedValues := match compiled with
        | .ok value => match fabHashLayoutFields value.checked.value with
          | .ok fields => Json.arr
              (nativeExpressionFabValuesJson (fields.map Prod.snd) values)
          | .error _ => Json.arr #[]
        | .error _ => Json.arr #[]
      return Json.mkObj [
        ("tag", toJson ("transientCommitFab" : String)),
        ("schema", schema), ("opening", nativeExpressionJson opening),
        ("values", encodedValues)]
  | .transientHashFab environment type values => Id.run do
      let compiled := Types.compileType environment type
      let schema := match compiled with
        | .ok value => (Types.schemaJson value).toOption.getD Json.null
        | .error _ => Json.null
      let encodedValues := match compiled with
        | .ok value => match fabHashLayoutFields value.checked.value with
          | .ok fields => Json.arr
              (nativeExpressionFabValuesJson (fields.map Prod.snd) values)
          | .error _ => Json.arr #[]
        | .error _ => Json.arr #[]
      return Json.mkObj [
        ("tag", toJson ("transientHashFab" : String)),
        ("schema", schema), ("values", encodedValues)]
  | .transientHash values => Json.mkObj [("tag", toJson ("transientHash" : String)),
      ("values", toJson (values.map nativeExpressionJson))]
  | .toBytes32 value => Json.mkObj [("tag", toJson ("toBytes32" : String)),
      ("value", nativeExpressionJson value)]
  | .fromBytes32 (target := target) value => Json.mkObj [("tag", toJson ("fromBytes32" : String)),
      ("type", toJson (typeName target)), ("value", nativeExpressionJson value)]
  | .fromBytes (target := target) (length := length) value => Json.mkObj [
      ("tag", toJson ("fromBytes" : String)), ("type", toJson (typeName target)),
      ("length", toJson length), ("value", nativeExpressionJson value)]
  | .jubjubScalarFromNative value => Json.mkObj [("tag", toJson ("jubjubScalarFromNative" : String)),
      ("value", nativeExpressionJson value)]
  | .jubjubScalarToNative value => Json.mkObj [("tag", toJson ("jubjubScalarToNative" : String)),
      ("value", nativeExpressionJson value)]
  | .jubjubMulGenerator scalar => Json.mkObj [("tag", toJson ("jubjubMulGenerator" : String)),
      ("scalar", nativeExpressionJson scalar)]
  | .jubjubMul point scalar => Json.mkObj [("tag", toJson ("jubjubMul" : String)),
      ("point", nativeExpressionJson point), ("scalar", nativeExpressionJson scalar)]
  | .jubjubAdd left right => Json.mkObj [("tag", toJson ("jubjubAdd" : String)),
      ("left", nativeExpressionJson left), ("right", nativeExpressionJson right)]
  | .jubjubNeg point => Json.mkObj [("tag", toJson ("jubjubNeg" : String)),
      ("point", nativeExpressionJson point)]
  | .jubjubCoordinate point index => Json.mkObj [("tag", toJson ("jubjubCoordinate" : String)),
      ("point", nativeExpressionJson point), ("index", toJson index)]
  | .jubjubFromCoordinates x y => Json.mkObj [("tag", toJson ("jubjubFromCoordinates" : String)),
      ("x", nativeExpressionJson x), ("y", nativeExpressionJson y)]
  | .hashToCurve values => Json.mkObj [("tag", toJson ("hashToCurve" : String)),
      ("values", toJson (values.map nativeExpressionJson))]
  | .foreignBase curve value => foreignConstantJson (.base curve) value
  | .foreignScalar curve value => foreignConstantJson (.scalar curve) value
  | .foreignPoint curve value => foreignConstantJson (.point curve) value
  | .foreignEncodedField (kind := kind) value index => Json.mkObj [
      ("tag", toJson ("foreignEncodedField" : String)),
      ("value", nativeExpressionJson value), ("index", toJson index)]
  | .foreignUnary operation value => Json.mkObj [
      ("tag", toJson ("foreignUnary" : String)),
      ("operation", toJson operation.name), ("value", nativeExpressionJson value)]
  | .foreignBinary operation left right => Json.mkObj [
      ("tag", toJson ("foreignBinary" : String)),
      ("operation", toJson operation.name),
      ("left", nativeExpressionJson left), ("right", nativeExpressionJson right)]
  | .foreignToBytes value => Json.mkObj [
      ("tag", toJson ("foreignToBytes" : String)), ("value", nativeExpressionJson value)]
  | .foreignFromBytes (kind := kind) (length := length) value => Json.mkObj [
      ("tag", toJson ("foreignFromBytes" : String)),
      ("type", toJson kind.sourceName), ("length", toJson length),
      ("value", nativeExpressionJson value)]
  | .boolAnd left right => Json.mkObj [("tag", toJson ("boolAnd" : String)),
      ("left", nativeExpressionJson left), ("right", nativeExpressionJson right)]
  | .boolOr left right => Json.mkObj [("tag", toJson ("boolOr" : String)),
      ("left", nativeExpressionJson left), ("right", nativeExpressionJson right)]
  | .boolXor left right => Json.mkObj [("tag", toJson ("boolXor" : String)),
      ("left", nativeExpressionJson left), ("right", nativeExpressionJson right)]
  | .ref name => Json.mkObj [("tag", toJson ("reference" : String)), ("name", toJson name)]
  | .add a b => binaryJson "add" (nativeExpressionJson a) (nativeExpressionJson b)
  | .mul a b => binaryJson "mul" (nativeExpressionJson a) (nativeExpressionJson b)
  | .sub a b => binaryJson "sub" (nativeExpressionJson a) (nativeExpressionJson b)
  | .uadd (m := m) (n := n) a b => unsignedJson "uadd" (m + n) (nativeExpressionJson a) (nativeExpressionJson b)
  | .usub (m := m) a b => unsignedJson "usub" m (nativeExpressionJson a) (nativeExpressionJson b)
  | .umul (m := m) (n := n) a b => unsignedJson "umul" (m * n) (nativeExpressionJson a) (nativeExpressionJson b)
  | .inv value => Json.mkObj [("tag", toJson ("inv" : String)), ("value", nativeExpressionJson value)]
  | .cast target value => Json.mkObj [("tag", toJson ("cast" : String)),
      ("type", toJson (typeName target)), ("value", nativeExpressionJson value)]
  | .letE name value body => nativeLetJson name (nativeExpressionJson value) (nativeExpressionJson body)
  | .assertE condition body => Json.mkObj [("tag", toJson ("assertThen" : String)),
      ("condition", nativeExpressionJson condition), ("body", nativeExpressionJson body)]
  | .disclose _ value => nativeExpressionJson value
  | .eq a b => binaryJson "eq" (nativeExpressionJson a) (nativeExpressionJson b)
  | .select c a b => Json.mkObj [("tag", toJson ("select" : String)),
      ("condition", nativeExpressionJson c), ("yes", nativeExpressionJson a), ("no", nativeExpressionJson b)]
  | .poseidon2 domain a b => Json.mkObj [("tag", toJson ("poseidon2" : String)),
      ("domain", toJson (toString domain)), ("left", nativeExpressionJson a), ("right", nativeExpressionJson b)]
termination_by value => sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals first
    | have h := Noctium.sizeOfMemberListLt (by assumption); omega
    | exact sizeOfSigmaExprHeadLt _ _
    | exact sizeOfSigmaExprValueLt _
    | have _h := sizeOfSigmaExprMemberLt (by assumption); omega
    | omega

private def nativeExpressionFabValuesJson : List Types.Layout → List (Sigma Expr) → Array Json
  | [], [] => #[]
  | layout :: layouts, value :: rest =>
    let encoded := match layout, value with
      | .bytes length .byteField, ⟨.bytes _, expression⟩ => Json.mkObj [
          ("tag", toJson ("bytes" : String)), ("length", toJson length),
          ("value", nativeExpressionJson expression)]
      | .scalar .nativeField, ⟨.native, expression⟩ => Json.mkObj [
          ("tag", toJson ("native" : String)), ("value", nativeExpressionJson expression)]
      | .scalar .booleanField, ⟨.bool, expression⟩ => Json.mkObj [
          ("tag", toJson ("bool" : String)), ("value", nativeExpressionJson expression)]
      | .scalar (.boundedUnsignedField maximum), ⟨.uint _, expression⟩ => Json.mkObj [
          ("tag", toJson ("uint" : String)), ("maximum", toJson (toString maximum)),
          ("value", nativeExpressionJson expression)]
      | .enumeration id (.enumTagField maximum) _ 0 _ _, ⟨.uint _, expression⟩ => Json.mkObj [
          ("tag", toJson ("enumTag" : String)), ("id", toJson id),
          ("maximum", toJson (toString maximum)), ("value", nativeExpressionJson expression)]
      | _, _ => Json.null
    #[encoded] ++ nativeExpressionFabValuesJson layouts rest
  | _, _ => #[]
termination_by _ values => sizeOf values
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact sizeOfSigmaExprHeadLt _ _
    | omega
end

/-- Symbolic source expressions for the native runtime. Values are AST constants or references,
never an execution witness. Decimal field constants avoid JavaScript number truncation. -/
def toJson {ty : Ty} (value : Expr ty) : Json := nativeExpressionJson value

end Noctium.NativeExpression
