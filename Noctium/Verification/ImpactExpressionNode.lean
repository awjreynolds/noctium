import Lean

namespace Noctium.Verification.ImpactExpressionNode

open Lean

/-- Native arithmetic operators in the emitted expression fragment. -/
inductive Binary where
  | add
  | mul
  | sub
  | eq
  deriving Inhabited, DecidableEq

/-- Bounded unsigned operators in the emitted expression fragment. -/
inductive Unsigned where
  | add
  | sub
  | mul
  deriving Inhabited, DecidableEq

/-- One decoded expression layer. Child expressions stay as their original JSON
values so callers can decode them independently and preserve their payloads. -/
inductive Node where
  | native (decimal : String)
  | bool (value : Bool)
  | uint (maximum value : String)
  | reference (name : String)
  | binary (op : Binary) (left right : Json)
  | unsigned (op : Unsigned) (maximum : String) (left right : Json)
  | cast (target : String) (value : Json)
  | bind (bindings : List (String × Json)) (body : Json)
  | assertThen (condition body : Json)
  | select (condition yes no : Json)
  | poseidon2 (domain : String) (left right : Json)
  deriving Inhabited

private def ensure (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def objectFieldNames (value : Json) : Except String (List String) := do
  pure ((← value.getObj?).toList.map Prod.fst)

private def exactFields (value : Json) (required : List String) : Except String Unit := do
  let names ← objectFieldNames value
  ensure (required.all names.contains && names.all required.contains)
    "missing or unknown native expression fields"

private def stringField (value : Json) (name : String) : Except String String := do
  (← value.getObjVal? name).getStr?

private def boolField (value : Json) (name : String) : Except String Bool := do
  (← value.getObjVal? name).getBool?

private def jsonField (value : Json) (name : String) : Except String Json :=
  value.getObjVal? name

private def decodeBinding (raw : Json) : Except String (String × Json) := do
  let pair ← raw.getArr?
  match pair.toList with
  | [name, value] => do
      let name ← name.getStr?
      pure (name, value)
  | _ => throw "native expression binding must be a name/value pair"

/-- Encode one binding pair in the emitted `lets` wire format. -/
def bindingJson (binding : String × Json) : Json :=
  Json.arr #[toJson binding.1, binding.2]

/-- Encode ordered binding pairs in the emitted `lets` wire format. -/
def bindingsJson (bindings : List (String × Json)) : Json :=
  Json.arr (bindings.toArray.map bindingJson)

private theorem decodeBinding_json (name : String) (value : Json) :
    decodeBinding (bindingJson (name, value)) = .ok (name, value) := by
  have nameJson : toJson name = Json.str name := rfl
  simp [decodeBinding, bindingJson, Json.getArr?, Json.getStr?, nameJson,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem decodeBindingList_json (bindings : List (String × Json)) :
    (bindings.map bindingJson).mapM decodeBinding = .ok bindings := by
  induction bindings with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk name value =>
          simp [List.mapM_cons, decodeBinding_json, ih,
            Bind.bind, Except.bind, Pure.pure, Except.pure]

private def decodeBindings (raw : Json) : Except String (List (String × Json)) := do
  let pairs ← raw.getArr?
  pairs.toList.mapM decodeBinding

private def decodeBinary (raw : Json) (op : Binary) : Except String Node := do
  exactFields raw ["tag", "left", "right"]
  return .binary op (← jsonField raw "left") (← jsonField raw "right")

private def decodeUnsigned (raw : Json) (op : Unsigned) : Except String Node := do
  exactFields raw ["tag", "maximum", "left", "right"]
  let maximum ← stringField raw "maximum"
  return .unsigned op maximum (← jsonField raw "left") (← jsonField raw "right")

/-- Decode one emitted scalar expression node without recursively decoding any
child. This covers the corresponding `NativeExpression` forms only. -/
def decode (raw : Json) : Except String Node := do
  let tag ← stringField raw "tag"
  match tag with
  | "constant" => do
      exactFields raw ["tag", "value"]
      return .native (← stringField raw "value")
  | "bool" => do
      exactFields raw ["tag", "value"]
      return .bool (← boolField raw "value")
  | "uint" => do
      exactFields raw ["tag", "maximum", "value"]
      return .uint (← stringField raw "maximum") (← stringField raw "value")
  | "reference" => do
      exactFields raw ["tag", "name"]
      return .reference (← stringField raw "name")
  | "add" => decodeBinary raw .add
  | "mul" => decodeBinary raw .mul
  | "sub" => decodeBinary raw .sub
  | "eq" => decodeBinary raw .eq
  | "uadd" => decodeUnsigned raw .add
  | "usub" => decodeUnsigned raw .sub
  | "umul" => decodeUnsigned raw .mul
  | "cast" => do
      exactFields raw ["tag", "type", "value"]
      return .cast (← stringField raw "type") (← jsonField raw "value")
  | "let" => do
      exactFields raw ["tag", "name", "value", "body"]
      let name ← stringField raw "name"
      let value ← jsonField raw "value"
      let body ← jsonField raw "body"
      return .bind [(name, value)] body
  | "lets" => do
      exactFields raw ["tag", "bindings", "body"]
      let bindings ← decodeBindings (← jsonField raw "bindings")
      let body ← jsonField raw "body"
      return .bind bindings body
  | "assertThen" => do
      exactFields raw ["tag", "condition", "body"]
      return .assertThen (← jsonField raw "condition") (← jsonField raw "body")
  | "select" => do
      exactFields raw ["tag", "condition", "yes", "no"]
      return .select (← jsonField raw "condition")
        (← jsonField raw "yes") (← jsonField raw "no")
  | "poseidon2" => do
      exactFields raw ["tag", "domain", "left", "right"]
      return .poseidon2 (← stringField raw "domain")
        (← jsonField raw "left") (← jsonField raw "right")
  | _ => throw "unsupported native expression node"

theorem decode_let (name : String) (value body : Json) :
    decode (Json.mkObj [
      ("tag", toJson ("let" : String)),
      ("name", toJson name), ("value", value), ("body", body)]) =
      .ok (.bind [(name, value)] body) := by
  rfl

theorem decode_lets (bindings : List (String × Json)) (body : Json) :
    decode (Json.mkObj [
      ("tag", toJson ("lets" : String)),
      ("bindings", bindingsJson bindings), ("body", body)]) =
      .ok (.bind bindings body) := by
  have rows : decodeBindings (bindingsJson bindings) = .ok bindings := by
    change ((bindings.toArray.map bindingJson).toList).mapM decodeBinding = .ok bindings
    rw [Array.toList_map, List.toList_toArray]
    exact decodeBindingList_json bindings
  let raw := Json.mkObj [
    ("tag", toJson ("lets" : String)),
    ("bindings", bindingsJson bindings), ("body", body)]
  have tagField : stringField raw "tag" = .ok "lets" := rfl
  have fields : exactFields raw ["tag", "bindings", "body"] = .ok () := rfl
  have bindingsField : raw.getObjVal? "bindings" = .ok (bindingsJson bindings) := rfl
  have bodyField : raw.getObjVal? "body" = .ok body := rfl
  change decode raw = .ok (.bind bindings body)
  simp [decode, jsonField, tagField, fields, bindingsField,
    bodyField, rows, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

end Noctium.Verification.ImpactExpressionNode
