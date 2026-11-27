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

private def transientHashOperandJson (expression : Expr .native) (encoded : Json) : Json :=
  match expression with
  | .opaqueBytesProjection _ | .opaqueStringProjection _ => Json.mkObj [
      ("tag", toJson ("opaqueProjection" : String)), ("value", encoded)]
  | _ => encoded

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
  | .keccak256Fab environment type values => Id.run do
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
        ("tag", toJson ("keccak256Fab" : String)),
        ("schema", schema), ("values", encodedValues)]
  | .persistentCommitFab environment type opening values => Id.run do
      let compiled := Types.compileType environment type
      let schema := match compiled with
        | .ok value => (Types.schemaJson value).toOption.getD Json.null
        | .error _ => Json.null
      let encodedValues := match compiled with
        | .ok value => match fabCommitHashLayoutFields value.checked.value with
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
        | .ok value => match fabCommitHashLayoutFields value.checked.value with
          | .ok fields => Json.arr
              (nativeExpressionFabValuesJson (fields.map Prod.snd) values)
          | .error _ => Json.arr #[]
        | .error _ => Json.arr #[]
      return Json.mkObj [
        ("tag", toJson ("transientCommitFab" : String)),
        ("schema", schema), ("opening", nativeExpressionJson opening),
        ("values", encodedValues)]
  | .transientHashFab environment type values => Id.run do
      let checked : Except String (Json × Json) := do
        let fields ← validateTransientFabHashFields environment type values
        let compiled ← (Types.compileType environment type).mapError (·.message)
        let schema ← Types.schemaJson compiled
        pure (schema, Json.arr (nativeExpressionFabValuesJson (fields.map Prod.snd) values))
      let (schema, encodedValues) := checked.toOption.getD (Json.null, Json.arr #[])
      return Json.mkObj [
        ("tag", toJson ("transientHashFab" : String)),
        ("schema", schema), ("values", encodedValues)]
  | .transientHash values =>
      let encodedValues := values.map nativeExpressionJson
      Json.mkObj [("tag", toJson ("transientHash" : String)),
        ("values", toJson (List.zipWith transientHashOperandJson values encodedValues))]
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
      | .curve expected, ⟨actual, expression⟩ =>
        if expected == actual then Json.mkObj [
          ("tag", toJson ("curve" : String)), ("type", toJson (typeName actual)),
          ("value", nativeExpressionJson expression)]
        else Json.null
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

/-- Serialize one binding, flattening it when the body already starts with a binding. -/
def letJson (name : String) (value body : Json) : Json := nativeLetJson name value body

/-- A body with an opcode other than `let` or `lets` stays nested under one binding. -/
theorem letJson_plain (name : String) (value raw : Json) (opcode : String)
    (tag : (raw.getObjVal? "tag" >>= Json.getStr?) = .ok opcode)
    (notLet : opcode ≠ "let") (notLets : opcode ≠ "lets") :
    letJson name value raw = Json.mkObj [
      ("tag", Lean.toJson ("let" : String)), ("name", Lean.toJson name),
      ("value", value), ("body", raw)] := by
  simp only [letJson, nativeLetJson, ← bind_assoc, tag]
  simp only [Bind.bind, Except.bind]
  rfl

/-- A single binding in the body is flattened into a two-binding `lets` node. -/
theorem letJson_single (name : String) (value : Json) (nextName : String)
    (nextValue tail : Json) :
    letJson name value (Json.mkObj [
      ("tag", Lean.toJson ("let" : String)), ("name", Lean.toJson nextName),
      ("value", nextValue), ("body", tail)]) = Json.mkObj [
        ("tag", Lean.toJson ("lets" : String)),
        ("bindings", Json.arr #[Json.arr #[Lean.toJson name, value],
          Json.arr #[Lean.toJson nextName, nextValue]]),
        ("body", tail)] := by
  rfl

/-- A `lets` body keeps its bindings and prepends the new binding. -/
theorem letJson_multiple (name : String) (value : Json) (bindings : Array Json)
    (tail : Json) :
    letJson name value (Json.mkObj [
      ("tag", Lean.toJson ("lets" : String)), ("bindings", Json.arr bindings),
      ("body", tail)]) = Json.mkObj [
        ("tag", Lean.toJson ("lets" : String)),
        ("bindings", Json.arr (#[Json.arr #[Lean.toJson name, value]] ++ bindings)),
        ("body", tail)] := by
  rfl

/-! These equations make the scalar-expression serializer available to verified
  clients without exposing the private well-founded recursive definition. -/

theorem toJson_native (value : Nat) :
    toJson (Expr.native value) = Json.mkObj [
      ("tag", Lean.toJson ("constant" : String)), ("value", Lean.toJson (toString value))] := by
  simp [toJson, nativeExpressionJson]

theorem toJson_bool (value : Bool) :
    toJson (Expr.bool value) = Json.mkObj [
      ("tag", Lean.toJson ("bool" : String)), ("value", Lean.toJson value)] := by
  simp [toJson, nativeExpressionJson]

theorem toJson_uint (maximum value : Nat) :
    toJson (Expr.uint maximum value) = Json.mkObj [
      ("tag", Lean.toJson ("uint" : String)),
      ("maximum", Lean.toJson (toString maximum)), ("value", Lean.toJson (toString value))] := by
  simp [toJson, nativeExpressionJson]

theorem toJson_ref {ty : Ty} (name : String) :
    toJson (Expr.ref (ty := ty) name) = Json.mkObj [
      ("tag", Lean.toJson ("reference" : String)), ("name", Lean.toJson name)] := by
  simp [toJson, nativeExpressionJson]

theorem toJson_add (left right : Expr .native) :
    toJson (Expr.add left right) = Json.mkObj [
      ("tag", Lean.toJson ("add" : String)), ("left", toJson left), ("right", toJson right)] := by
  simp [toJson, nativeExpressionJson, binaryJson]

theorem toJson_mul (left right : Expr .native) :
    toJson (Expr.mul left right) = Json.mkObj [
      ("tag", Lean.toJson ("mul" : String)), ("left", toJson left), ("right", toJson right)] := by
  simp [toJson, nativeExpressionJson, binaryJson]

theorem toJson_sub (left right : Expr .native) :
    toJson (Expr.sub left right) = Json.mkObj [
      ("tag", Lean.toJson ("sub" : String)), ("left", toJson left), ("right", toJson right)] := by
  simp [toJson, nativeExpressionJson, binaryJson]

theorem toJson_uadd {m n : Nat} (left : Expr (.uint m)) (right : Expr (.uint n)) :
    toJson (Expr.uadd left right) = Json.mkObj [
      ("tag", Lean.toJson ("uadd" : String)), ("maximum", Lean.toJson (toString (m + n))),
      ("left", toJson left), ("right", toJson right)] := by
  simp [toJson, nativeExpressionJson, unsignedJson]

theorem toJson_usub {m n : Nat} (left : Expr (.uint m)) (right : Expr (.uint n)) :
    toJson (Expr.usub left right) = Json.mkObj [
      ("tag", Lean.toJson ("usub" : String)), ("maximum", Lean.toJson (toString m)),
      ("left", toJson left), ("right", toJson right)] := by
  simp [toJson, nativeExpressionJson, unsignedJson]

theorem toJson_umul {m n : Nat} (left : Expr (.uint m)) (right : Expr (.uint n)) :
    toJson (Expr.umul left right) = Json.mkObj [
      ("tag", Lean.toJson ("umul" : String)), ("maximum", Lean.toJson (toString (m * n))),
      ("left", toJson left), ("right", toJson right)] := by
  simp [toJson, nativeExpressionJson, unsignedJson]

theorem toJson_cast (target : Ty) (value : Expr source) :
    toJson (Expr.cast target value) = Json.mkObj [
      ("tag", Lean.toJson ("cast" : String)), ("type", Lean.toJson (typeName target)),
      ("value", toJson value)] := by
  simp [toJson, nativeExpressionJson]

theorem toJson_assertE (condition : Expr .bool) (body : Expr ty) :
    toJson (Expr.assertE condition body) = Json.mkObj [
      ("tag", Lean.toJson ("assertThen" : String)),
      ("condition", toJson condition), ("body", toJson body)] := by
  simp [toJson, nativeExpressionJson]

theorem toJson_copyValue (value : Expr ty) :
    toJson (Expr.copyValue value) = toJson value := by
  simp [toJson, nativeExpressionJson]

theorem toJson_disclose (span : SourceSpan) (value : Expr ty) :
    toJson (Expr.disclose span value) = toJson value := by
  simp [toJson, nativeExpressionJson]

theorem toJson_eq {ty : Ty} (left right : Expr ty) :
    toJson (Expr.eq left right) = Json.mkObj [
      ("tag", Lean.toJson ("eq" : String)), ("left", toJson left), ("right", toJson right)] := by
  simp [toJson, nativeExpressionJson, binaryJson]

theorem toJson_select (condition : Expr .bool) (yes no : Expr ty) :
    toJson (Expr.select condition yes no) = Json.mkObj [
      ("tag", Lean.toJson ("select" : String)), ("condition", toJson condition),
      ("yes", toJson yes), ("no", toJson no)] := by
  simp [toJson, nativeExpressionJson]

theorem toJson_poseidon2 (domain : Nat) (left right : Expr .native) :
    toJson (Expr.poseidon2 domain left right) = Json.mkObj [
      ("tag", Lean.toJson ("poseidon2" : String)), ("domain", Lean.toJson (toString domain)),
      ("left", toJson left), ("right", toJson right)] := by
  simp [toJson, nativeExpressionJson]

theorem toJson_letE (name : String) (value : Expr source) (body : Expr ty) :
    toJson (Expr.letE name value body) = letJson name (toJson value) (toJson body) := by
  simp [toJson, letJson, nativeExpressionJson]

end Noctium.NativeExpression
