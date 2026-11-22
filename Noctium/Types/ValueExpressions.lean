import Noctium.Types.Values
import Noctium.Semantics
import Noctium.Wire

namespace Noctium.Types

structure ScalarExpression where
  type : Ty
  value : Expr type
  deriving Repr

def ScalarExpression.native (value : ScalarExpression) : Except String (Expr .native) :=
  match value with
  | ⟨.native, value⟩ => pure value
  | ⟨.bool, value⟩ => pure (.cast .native value)
  | ⟨.uint _, value⟩ => pure (.cast .native value)
  | ⟨.bytes _, _⟩ => throw "byte strings require an aggregate bytes expression"
  | ⟨.opaqueBytes, _⟩ => throw "OpaqueBytes require a qualified ledger scalar expression"
  | ⟨.opaqueString, _⟩ => throw "OpaqueString requires a qualified ledger scalar expression"
  | ⟨.jubjubScalar, _⟩ | ⟨.jubjubPoint, _⟩ =>
    throw "Jubjub values require a qualified curve expression"
  | ⟨.foreign _, _⟩ => throw "foreign values require a qualified curve expression"

inductive AggregateExpression where
  | unit
  | scalar (value : ScalarExpression)
  | tuple (items : List AggregateExpression)
  | structure (id : DeclId) (fields : List (String × AggregateExpression))
  | enumeration (id variant : String) (fields : List (String × AggregateExpression))
  | vector (items : List AggregateExpression)
  | bytes (values : List (Expr (.uint 255)))
  deriving Repr

private def scalarExpression (type : Ty) (number : Nat) : Except String ScalarExpression := do
  match type with
  | .jubjubScalar => do
    unless number < Jubjub.scalarOrder do throw "invalid aggregate Jubjub scalar expression constant"
    pure ⟨.jubjubScalar, .jubjubScalarFromNative (.native number)⟩
  | .foreign (.base curve) => do
    unless number < curve.baseModulus do throw "invalid aggregate foreign base expression constant"
    pure ⟨.foreign (.base curve), .foreignBase curve number⟩
  | .foreign (.scalar curve) => do
    unless number < curve.scalarModulus do throw "invalid aggregate foreign scalar expression constant"
    pure ⟨.foreign (.scalar curve), .foreignScalar curve number⟩
  | .jubjubPoint => throw "Jubjub points require a point aggregate expression"
  | .foreign (.point _) => throw "foreign points require a point aggregate expression"
  | .bytes _ => throw "byte strings require an aggregate bytes expression"
  | .opaqueBytes => throw "OpaqueBytes require a qualified ledger scalar expression"
  | .opaqueString => throw "OpaqueString requires a qualified ledger scalar expression"
  | .native | .bool | .uint _ => do
    ScalarPolicy.validate type.scalarKind
    unless ScalarPolicy.accepts type.scalarKind number do throw "invalid aggregate scalar expression constant"
    match type with
    | .native => pure ⟨.native, .native number⟩
    | .bool => pure ⟨.bool, .bool (number == 1)⟩
    | .uint maximum => pure ⟨.uint maximum, .uint maximum number⟩
    | _ => throw "invalid aggregate scalar expression constant"

private def literalAux : Nat → AggregateValue → Except String AggregateExpression
  | 0, _ => throw "aggregate literal traversal exhausted checked fuel"
  | fuel + 1, value => do
    match value with
    | .unit => pure .unit
    | .scalar type number => pure (.scalar (← scalarExpression type number))
    | .jubjubPoint x y => do
      unless Jubjub.pointValid x y do throw "aggregate Jubjub point is not canonical or on curve"
      pure (.scalar ⟨.jubjubPoint, .jubjubFromCoordinates (.native x) (.native y)⟩)
    | .foreignPoint curve point => pure (.scalar ⟨.foreign (.point curve), .foreignPoint curve point⟩)
    | .tuple items => pure (.tuple (← items.mapM (literalAux fuel)))
    | .structure id fields => pure (.structure id (← fields.mapM fun (name, value) => do pure (name, ← literalAux fuel value)))
    | .enumeration id variant fields => pure (.enumeration id variant (← fields.mapM fun (name, value) => do pure (name, ← literalAux fuel value)))
    | .vector items => pure (.vector (← items.mapM (literalAux fuel)))
    | .bytes values => pure (.bytes (values.map (Expr.uint 255)))

def literal (type : CompiledType) (value : TypedValue type) : Except String AggregateExpression :=
  literalAux (type.checked.layoutNodes + 1) value.value

private def expressionAux (environment : TypeEnv) : Nat → Layout → AggregateExpression → Except String (List ScalarExpression)
  | 0, _, _ => throw "aggregate expression traversal exhausted checked fuel"
  | fuel + 1, layout, expression => do
    match layout, expression with
    | .unit, .unit => pure []
    | .scalar leaf, .scalar value =>
      let expected ← match leaf with
        | .nativeField => pure Ty.native
        | .booleanField => pure Ty.bool
        | .boundedUnsignedField maximum => pure (Ty.uint maximum)
        | _ => throw "unsupported aggregate expression scalar"
      unless value.type == expected do throw "aggregate expression scalar type mismatch"
      value.value.validate Capabilities.crypto environment
      pure [value]
    | .curve type, .scalar value => do
      unless value.type == type do throw "aggregate expression curve type mismatch"
      value.value.validate Capabilities.crypto environment
      let fields := value.value.nativeCallFields
      unless fields.length == type.nativeCallFieldCount do throw "aggregate expression curve encoding width mismatch"
      pure (fields.map fun field => ⟨.native, field⟩)
    | .tuple layouts, .tuple values =>
      unless layouts.length == values.length do throw "aggregate expression tuple arity mismatch"
      pure (← (layouts.zip values).mapM fun (layout, value) => expressionAux environment fuel layout value).flatten
    | .structure id fields, .structure actual values =>
      unless id == actual && fields.map Prod.fst == values.map Prod.fst do throw "aggregate expression nominal struct/field mismatch"
      pure (← (fields.zip values).mapM fun (field, value) => expressionAux environment fuel field.2 value.2).flatten
    | .vector length element, .vector values =>
      unless length == values.length do throw "aggregate expression vector length mismatch"
      pure (← values.mapM (expressionAux environment fuel element)).flatten
    | .bytes length .byteField, .bytes values =>
      unless length == values.length do throw "aggregate expression byte length mismatch"
      for value in values do value.validate Capabilities.crypto environment
      pure (values.map fun value => ⟨.uint 255, value⟩)
    | .enumeration id _ maximum payloadLeaves _ variants, .enumeration actual variant values =>
      unless id == actual do throw "aggregate expression nominal enum mismatch"
      let some tag := variants.findIdx? (·.1 == variant) | throw "unknown aggregate expression enum variant"
      let some selected := variants[tag]? | throw "aggregate expression enum index mismatch"
      unless selected.2.1.map Prod.fst == values.map Prod.fst do throw "aggregate expression enum fields mismatch"
      let payload := (← (selected.2.1.zip values).mapM fun (field, value) => expressionAux environment fuel field.2 value.2).flatten
      unless payload.length ≤ payloadLeaves do throw "aggregate expression enum payload mismatch"
      pure (⟨.uint maximum, .uint maximum tag⟩ :: payload ++
        List.replicate (payloadLeaves - payload.length) ⟨.native, .native 0⟩)
    | _, _ => throw "aggregate expression/layout kind mismatch"

def flattenExpression (type : CompiledType) (environment : TypeEnv) (expression : AggregateExpression) :
    Except String (List ScalarExpression) := do
  let leaves ← expressionAux environment (type.checked.layoutNodes + 1) type.checked.value expression
  unless leaves.length == type.checked.expandedLeaves do throw "aggregate expression checked leaf count mismatch"
  pure leaves

structure TypedExpression (type : CompiledType) (environment : TypeEnv) where
  expression : AggregateExpression
  leaves : List ScalarExpression
  checked : flattenExpression type environment expression = .ok leaves

def checkExpression (type : CompiledType) (environment : TypeEnv) (expression : AggregateExpression) :
    Except String (TypedExpression type environment) :=
  match checked : flattenExpression type environment expression with
  | .error message => .error message
  | .ok leaves => .ok {expression, leaves, checked}

private def evalAux (context : EvalContext) (environment : EvalEnv) : Nat → AggregateExpression → Except String AggregateValue
  | 0, _ => throw "aggregate expression evaluation exhausted checked fuel"
  | fuel + 1, expression => do
    match expression with
    | .unit => pure .unit
    | .scalar value =>
      match value with
      | ⟨.jubjubPoint, expression⟩ => do
        let (x, y) ← Noctium.Expr.eval (ty := .jubjubPoint) context environment expression
        pure (.jubjubPoint x y)
      | ⟨.foreign (.point curve), expression⟩ => do
        pure (.foreignPoint curve (← Noctium.Expr.eval (ty := .foreign (.point curve)) context environment expression))
      | _ => do
        let number ← match value with
          | ⟨.native, value⟩ => value.eval context environment
          | ⟨.bool, value⟩ => pure (if ← value.eval context environment then 1 else 0)
          | ⟨.uint maximum, expression⟩ => @Noctium.Expr.eval (.uint maximum) context environment expression
          | ⟨.bytes _, _⟩ => throw "byte strings require an aggregate bytes expression"
          | ⟨.opaqueBytes, _⟩ => throw "OpaqueBytes require a qualified ledger scalar expression"
          | ⟨.opaqueString, _⟩ => throw "OpaqueString requires a qualified ledger scalar expression"
          | ⟨.jubjubScalar, expression⟩ => Noctium.Expr.eval (ty := .jubjubScalar) context environment expression
          | ⟨.jubjubPoint, _⟩ | ⟨.foreign (.point _), _⟩ => throw "unreachable aggregate point expression"
          | ⟨.foreign (.base curve), expression⟩ =>
            Noctium.Expr.eval (ty := .foreign (.base curve)) context environment expression
          | ⟨.foreign (.scalar curve), expression⟩ =>
            Noctium.Expr.eval (ty := .foreign (.scalar curve)) context environment expression
        pure (.scalar value.type number)
    | .tuple values => pure (.tuple (← values.mapM (evalAux context environment fuel)))
    | .structure id fields => pure (.structure id (← fields.mapM fun (name, value) => do pure (name, ← evalAux context environment fuel value)))
    | .enumeration id variant fields => pure (.enumeration id variant (← fields.mapM fun (name, value) => do pure (name, ← evalAux context environment fuel value)))
    | .vector values => pure (.vector (← values.mapM (evalAux context environment fuel)))
    | .bytes values => pure (.bytes (← values.mapM (Expr.eval context environment)))

def evaluateExpression (type : CompiledType) (types : TypeEnv) (value : TypedExpression type types)
    (context : EvalContext) (environment : EvalEnv) : Except String (TypedValue type) := do
  checkValue type (← evalAux context environment (type.checked.layoutNodes + 1) value.expression)

theorem checked_expression_flatten (type : CompiledType) (environment : TypeEnv)
    (value : TypedExpression type environment) :
    flattenExpression type environment value.expression = .ok value.leaves := value.checked

end Noctium.Types

namespace Noctium.Types

/-- Raw backend IR with a certified slot count, not a canonicality certificate.
Consumers must regenerate constraints with `checkNativeExpression` before lowering.
Enum slot types are constrained under their active tag. -/
structure NativeExpression (type : CompiledType) where
  leaves : List (Expr .native)
  count : leaves.length = type.checked.expandedLeaves
  constraints : List (Expr .bool)

private def boundWhen (active : Expr .bool) (maximum : Nat) (value : Expr .native) : Expr .bool :=
  let gated := Expr.select active value (.native 0)
  .eq (.cast .native (.cast (.uint maximum) gated)) gated

private def curveInactiveFields : (type : Ty) → Except String (List Nat)
  | .jubjubScalar => pure [0]
  | .jubjubPoint => pure [0, 1]
  | .foreign (.base curve) => Foreign.encodeValue (.base curve) 0
  | .foreign (.scalar curve) => Foreign.encodeValue (.scalar curve) 0
  | .foreign (.point curve) => Foreign.encodeValue (.point curve) .identity
  | _ => throw "invalid aggregate curve layout type"

private def constrainLayout (environment : TypeEnv) : Nat → Layout → Expr .bool → List (Expr .native) →
    Except String (List (Expr .bool) × List (Expr .native))
  | 0, _, _, _ => throw "aggregate native layout traversal exhausted checked fuel"
  | fuel + 1, layout, active, leaves => do
    match layout with
    | .unit => pure ([], leaves)
    | .scalar leaf =>
      let value :: rest := leaves | throw "short aggregate native scalar input"
      let constraints ← match leaf with
        | .nativeField => pure []
        | .booleanField => pure [boundWhen active 1 value]
        | .boundedUnsignedField maximum => pure [boundWhen active maximum value]
        | _ => throw "unsupported aggregate native scalar leaf"
      pure (constraints, rest)
    | .curve type => do
      let width := type.nativeCallFieldCount
      let (values, rest) := leaves.splitAt width
      unless values.length == width do throw "short aggregate native curve input"
      let defaults ← curveInactiveFields type
      unless defaults.length == width do throw "aggregate curve default encoding width mismatch"
      let safeValues := (values.zip defaults).map fun (value, default) =>
        Expr.select active value (.native default)
      let canonical ← Wire.curveFieldsCanonical type safeValues
      canonical.validate Capabilities.crypto environment
      pure ([canonical], rest)
    | .tuple items =>
      let mut rest := leaves
      let mut constraints := []
      for item in items do
        let (next, tail) ← constrainLayout environment fuel item active rest
        constraints := constraints ++ next
        rest := tail
      pure (constraints, rest)
    | .structure _ fields =>
      let mut rest := leaves
      let mut constraints := []
      for (_, item) in fields do
        let (next, tail) ← constrainLayout environment fuel item active rest
        constraints := constraints ++ next
        rest := tail
      pure (constraints, rest)
    | .vector length element =>
      let mut rest := leaves
      let mut constraints := []
      for _ in [:length] do
        let (next, tail) ← constrainLayout environment fuel element active rest
        constraints := constraints ++ next
        rest := tail
      pure (constraints, rest)
    | .bytes length .byteField =>
      let (values, rest) := leaves.splitAt length
      unless values.length == length do throw "short aggregate native byte input"
      pure (values.map (boundWhen active 255), rest)
    | .enumeration _ _ maximum payloadLeaves _ variants =>
      let tag :: rest := leaves | throw "short aggregate native enum tag"
      let (payload, rest) := rest.splitAt payloadLeaves
      unless payload.length == payloadLeaves do throw "short aggregate native enum payload"
      let mut constraints := [boundWhen active maximum tag]
      for ((_, fields, _), index) in variants.zipIdx do
        let selected := Expr.select active (.eq tag (.native index)) (.bool false)
        let mut remaining := payload
        for (_, field) in fields do
          let (next, tail) ← constrainLayout environment fuel field selected remaining
          constraints := constraints ++ next
          remaining := tail
        for padding in remaining do
          constraints := constraints ++ [.eq (.select selected padding (.native 0)) (.native 0)]
      pure (constraints, rest)
    | _ => throw "unsupported aggregate native byte layout"

def checkNativeExpression (type : CompiledType) (environment : TypeEnv)
    (leaves : List (Expr .native)) : Except String (NativeExpression type) := do
  if count : leaves.length = type.checked.expandedLeaves then
  for leaf in leaves do leaf.validate Capabilities.crypto environment
    let (constraints, remaining) ← constrainLayout environment (type.checked.layoutNodes + 1)
      type.checked.value (.bool true) leaves
    unless remaining.isEmpty do throw "trailing aggregate native leaves"
    pure {leaves, count, constraints}
  else throw "aggregate native checked leaf count mismatch"

/-- Index bounds enter the relation even for vectors whose elements have no
leaves. Origins remain separate for the later component disclosure analysis. -/
structure NativeSelection where
  type : CompiledType
  value : NativeExpression type
  componentOrigins : List Disclosure.Origins
  indexOrigins : Disclosure.Origins
  controlOrigins : Disclosure.Origins

-- The index arrives as Native so callers cannot bypass its range constraint by
-- assigning a bounded source type without emitting a checked cast.
def indexNativeVector (parent : CompiledType) (value : NativeExpression parent)
    (environment : TypeEnv) (index : Expr .native)
    (componentOrigins : List Disclosure.Origins) (indexOrigins : Disclosure.Origins)
    (controlOrigins : Disclosure.Origins := []) : Except String NativeSelection := do
  let .vector length element := parent.type | throw "dynamic aggregate index requires a fixed vector"
  unless length > 0 do throw "cannot dynamically index an empty aggregate vector"
  unless componentOrigins.length == parent.checked.expandedLeaves do throw "aggregate native origin count mismatch"
  index.validate Capabilities.crypto environment
  for condition in value.constraints do condition.validate Capabilities.crypto environment
  let checkedParent ← checkNativeExpression parent environment value.leaves
  let child ← (compileType parent.environment element parent.limits).mapError (·.message)
  let width := child.checked.expandedLeaves
  let selected := (List.range width).map fun offset =>
    (List.range length).foldr (fun position rest =>
      .select (.eq index (.native position)) ((value.leaves[position * width + offset]?).getD (.native 0)) rest)
      (.native 0)
  let result ← checkNativeExpression child environment selected
  let origins := (List.range width).map fun offset =>
    ((List.range length).flatMap fun position =>
      (componentOrigins[position * width + offset]?).getD []).eraseDups
  let checked : NativeExpression child := {
    leaves := result.leaves
    count := result.count
    constraints := value.constraints ++ checkedParent.constraints ++
      [boundWhen (.bool true) (length - 1) index] ++ result.constraints
  }
  pure {type := child, value := checked, componentOrigins := origins, indexOrigins, controlOrigins}

def NativeSelection.conservativeOrigins (value : NativeSelection) : List Disclosure.Origins :=
  value.componentOrigins.map fun origins =>
    (origins ++ value.indexOrigins ++ value.controlOrigins).eraseDups

end Noctium.Types
