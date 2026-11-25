import Lean

namespace Noctium.Verification.ImpactWireDecoder

open Lean

/-- The scalar Impact operations whose wire shape is decoded here. Expression
trees remain JSON values so this decoder is independent of the producer's
typed IR and retains each serialized operand exactly. -/
inductive Operation where
  | dup
  | index (slot : Nat) (pushPath : Bool) (key : Option Json)
  | push (storage : Bool) (alignment : String) (expression : Json)
  | popeq (alignment : String) (expression : Json)
  | member
  | insert (n : Nat)
  deriving Inhabited

/-- A schedule item can carry the single outer activity guard emitted by the
compiler. `guard` stores the exact native-expression JSON. -/
structure ScheduledOperation where
  guard : Option Json
  operation : Operation
  deriving Inhabited

private def ensure (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def objectFieldNames (value : Json) : Except String (List String) := do
  pure ((← value.getObj?).toList.map Prod.fst)

/-- Check Rust's `deny_unknown_fields` contract for one operation variant.
`optional` names are the only fields the wire format permits omitting. -/
private def exactFields (value : Json) (required optional : List String) : Except String Unit := do
  let names ← objectFieldNames value
  let allowed := required ++ optional
  ensure (required.all names.contains && names.all allowed.contains)
    "missing or unknown Impact operation fields"

private def hasField (value : Json) (name : String) : Except String Bool := do
  return (← objectFieldNames value).contains name

private def stringField (value : Json) (name : String) : Except String String := do
  (← value.getObjVal? name).getStr?

private def naturalField (value : Json) (name : String) : Except String Nat := do
  (← value.getObjVal? name).getNat?

private def boolField (value : Json) (name : String) : Except String Bool := do
  (← value.getObjVal? name).getBool?

private def checkAlignment (alignment : String) : Except String Unit :=
  ensure (alignment == "field" || alignment == "bit")
    "unsupported scalar Impact alignment"

def decodeBareOperation (raw : Json) : Except String Operation := do
  let opcode ← stringField raw "op"
  match opcode with
  | "dup" =>
      exactFields raw ["op"] []
      pure .dup
  | "index" => do
      exactFields raw ["op", "slot", "pushPath"] ["key"]
      let slot ← naturalField raw "slot"
      ensure (slot < 2 ^ 32) "Impact index slot exceeds Rust u32"
      let pushPath ← boolField raw "pushPath"
      let key ← if ← hasField raw "key" then
          let value ← raw.getObjVal? "key"
          if value.isNull then throw "Impact index key must contain an expression"
          pure (some value)
        else pure none
      ensure (key.isNone || !pushPath)
        "keyed Impact index cannot push a path"
      pure (.index slot pushPath key)
  | "push" => do
      exactFields raw ["op", "storage", "alignment", "expression"] []
      let storage ← boolField raw "storage"
      let alignment ← stringField raw "alignment"
      checkAlignment alignment
      let expression ← raw.getObjVal? "expression"
      pure (.push storage alignment expression)
  | "popeq" => do
      exactFields raw ["op", "alignment", "expression"] []
      let alignment ← stringField raw "alignment"
      checkAlignment alignment
      let expression ← raw.getObjVal? "expression"
      pure (.popeq alignment expression)
  | "member" =>
      exactFields raw ["op"] []
      pure .member
  | "insert" => do
      exactFields raw ["op", "n"] []
      let n ← naturalField raw "n"
      ensure (n < 2 ^ 8) "Impact insert depth exceeds Rust u8"
      pure (.insert n)
  | _ => throw "unsupported scalar Impact operation"

/-- Decode a scalar operation or the compiler's optional outer guard wrapper.
Nested wrappers and unsupported opcodes fail. -/
def decodeOperation (raw : Json) : Except String ScheduledOperation := do
  let opcode ← stringField raw "op"
  if opcode == "guarded" then do
    exactFields raw ["op", "guard", "operation"] []
    let guard ← raw.getObjVal? "guard"
    if guard.isNull then throw "Impact guard must contain an expression"
    let inner ← raw.getObjVal? "operation"
    let operation ← decodeBareOperation inner
    pure ⟨some guard, operation⟩
  else
    let operation ← decodeBareOperation raw
    pure ⟨none, operation⟩

/-- Decode an operations array while preserving source order. -/
def decodeOperations (raw : Json) : Except String (List ScheduledOperation) := do
  let values ← raw.getArr?
  values.toList.mapM decodeOperation

/-- Decode the operations member of a native Impact plan object. -/
def decodePlanOperations (raw : Json) : Except String (List ScheduledOperation) := do
  decodeOperations (← raw.getObjVal? "operations")

/-- A successfully decoded bare operation appears unguarded in the schedule
when its opcode is not the wrapper opcode. -/
theorem decode_unguarded {raw : Json} {opcode : String} {operation : Operation}
    (tag : (raw.getObjVal? "op" >>= Json.getStr?) = .ok opcode)
    (notGuarded : opcode ≠ "guarded")
    (decoded : decodeBareOperation raw = .ok operation) :
    decodeOperation raw = .ok ⟨none, operation⟩ := by
  have found : stringField raw "op" = .ok opcode := tag
  simp [decodeOperation, found, notGuarded, decoded, Bind.bind, Except.bind] <;> rfl

/-- Decode the compiler's single optional activity-guard wrapper while keeping
the guard expression JSON unchanged. -/
theorem decode_guarded (guardJson raw : Json) {operation : Operation}
    (guardNotNull : guardJson.isNull = false)
    (decoded : decodeBareOperation raw = .ok operation) :
    decodeOperation (Json.mkObj [
      ("op", toJson ("guarded" : String)),
      ("guard", guardJson),
      ("operation", raw)]) = .ok ⟨some guardJson, operation⟩ := by
  let wrapper := Json.mkObj [
    ("op", toJson ("guarded" : String)),
    ("guard", guardJson),
    ("operation", raw)]
  change decodeOperation wrapper = .ok ⟨some guardJson, operation⟩
  have tag : stringField wrapper "op" = .ok "guarded" := rfl
  have fields : exactFields wrapper ["op", "guard", "operation"] [] = .ok () := rfl
  have guardField : wrapper.getObjVal? "guard" = .ok guardJson := rfl
  have operationField : wrapper.getObjVal? "operation" = .ok raw := rfl
  simp [decodeOperation, tag, fields, guardField, operationField,
    guardNotNull, decoded, Bind.bind, Except.bind] <;> rfl

/-- Decode a positional slot within the Rust `u32` range. -/
theorem decode_index_positional (slot : Nat) (pushPath : Bool)
    (slotBound : slot < 2 ^ 32) :
    decodeBareOperation (Json.mkObj [
      ("op", toJson ("index" : String)),
      ("slot", toJson slot),
      ("pushPath", toJson pushPath)]) =
      .ok (.index slot pushPath none) := by
  let raw := Json.mkObj [
    ("op", toJson ("index" : String)),
    ("slot", toJson slot),
    ("pushPath", toJson pushPath)]
  have tag : stringField raw "op" = .ok "index" := rfl
  have fields : exactFields raw ["op", "slot", "pushPath"] ["key"] = .ok () := rfl
  have slotJson : naturalField raw "slot" = .ok slot := rfl
  have pushPathJson : boolField raw "pushPath" = .ok pushPath := rfl
  have noKey : hasField raw "key" = .ok false := rfl
  simp [decodeBareOperation, raw, tag, fields, slotJson, pushPathJson,
    noKey, ensure, slotBound, Bind.bind, Except.bind] <;> rfl

/-- Decode a keyed slot and retain the key expression JSON. -/
theorem decode_index_key (slot : Nat) (key : Json)
    (slotBound : slot < 2 ^ 32) (keyNotNull : key.isNull = false) :
    decodeBareOperation (Json.mkObj [
      ("op", toJson ("index" : String)),
      ("slot", toJson slot),
      ("pushPath", toJson (false : Bool)),
      ("key", key)]) =
      .ok (.index slot false (some key)) := by
  let raw := Json.mkObj [
    ("op", toJson ("index" : String)),
    ("slot", toJson slot),
    ("pushPath", toJson (false : Bool)),
    ("key", key)]
  have tag : stringField raw "op" = .ok "index" := rfl
  have fields : exactFields raw ["op", "slot", "pushPath"] ["key"] = .ok () := rfl
  have slotJson : naturalField raw "slot" = .ok slot := rfl
  have pushPathJson : boolField raw "pushPath" = .ok false := rfl
  have keyField : raw.getObjVal? "key" = .ok key := rfl
  have hasKey : hasField raw "key" = .ok true := rfl
  simp [decodeBareOperation, raw, tag, fields, slotJson, pushPathJson,
    keyField, hasKey, ensure, slotBound, keyNotNull, Bind.bind, Except.bind] <;> rfl

/-- The scalar `insert` encoding decodes for symbolic depths within the Rust
`u8` range. -/
theorem decode_insert (depth : Nat) (depthBound : depth < 2 ^ 8) :
    decodeBareOperation (Json.mkObj [
      ("op", toJson ("insert" : String)),
      ("n", toJson depth)]) =
      .ok (.insert depth) := by
  let raw := Json.mkObj [
    ("op", toJson ("insert" : String)),
    ("n", toJson depth)]
  have tag : stringField raw "op" = .ok "insert" := rfl
  have fields : exactFields raw ["op", "n"] [] = .ok () := rfl
  have depthJson : naturalField raw "n" = .ok depth := rfl
  simp [decodeBareOperation, raw, tag, fields, depthJson, ensure, depthBound,
    Bind.bind, Except.bind] <;> rfl

end Noctium.Verification.ImpactWireDecoder
