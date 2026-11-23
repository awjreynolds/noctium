import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Frontend

open Lean
open scoped Noctium
open Noctium

noctium_circuit guardedConstructorSetInspection where
  public owner : Bytes32
end

noctium_contract GuardedConstructorSet where
  sealed set privileged : Bytes32

  constructor(owner : Bytes32, enabled : Bool) where
    when enabled insert privileged[owner]
  end

  entry inspect uses guardedConstructorSetInspection where
    member privileged[owner] as memberPresent
    return present : Bool := memberPresent
  end
end

private def inspectEntry : Entrypoint :=
  (GuardedConstructorSet.entrypoints.find? (·.name == "inspect")).getD
    {name := "missing", circuit := {name := "missing"}}

private def constructorSetInserts (ctor : Noctium.Constructor) : Except String (Array Json) := do
  let plan ← (Backend.Impact.lower GuardedConstructorSet.state inspectEntry).mapError
    (·.message)
  let artifact := Compiler.nativePlanJson TargetProfile.selected321
    `GuardedConstructorSet GuardedConstructorSet.state (some ctor)
    inspectEntry plan
  let metadata ← artifact.getObjVal? "constructor"
  let insertions ← metadata.getObjVal? "setInserts"
  insertions.getArr?

private def setInsertWithWrongGuard (insertion : Noctium.ConstructorSetInsert) :
    Noctium.ConstructorSetInsert :=
  {insertion with guard := some (.ref "owner")}

#guard (GuardedConstructorSet.validate Capabilities.source).isOk
#guard (inspectEntry.validate Capabilities.source GuardedConstructorSet.state).isOk

#guard match GuardedConstructorSet.constructor with
  | some ctor =>
      match ctor.setInserts with
      | [{name := "privileged", key := .mk (.bytes 32) (.ref "owner"),
          guard := some (.ref "enabled")} ] => _root_.Bool.true
      | _ => _root_.Bool.false
  | _ => _root_.Bool.false

#guard match GuardedConstructorSet.constructor with
  | some ctor =>
      match constructorSetInserts ctor with
      | .ok #[insertion] =>
          let guard := NativeExpression.toJson (.ref "enabled" : Expr .bool)
          (insertion.getObjVal? "name").toOption == some (toJson ("privileged" : String)) &&
            (insertion.getObjVal? "guard").toOption == some guard &&
            (insertion.getObjVal? "key").isOk
      | _ => _root_.Bool.false
  | none => _root_.Bool.false

#guard match GuardedConstructorSet.constructor with
  | some ctor =>
      let unguarded := {ctor with setInserts := ctor.setInserts.map fun insertion =>
        {insertion with guard := none}}
      match constructorSetInserts unguarded with
      | .ok #[insertion] =>
          (insertion.getObjVal? "name").isOk &&
            (insertion.getObjVal? "key").isOk &&
            !(insertion.getObjVal? "guard").isOk
      | _ => _root_.Bool.false
  | none => _root_.Bool.false

private def wrongConstructorGuardRejected : _root_.Bool :=
  match GuardedConstructorSet.constructor with
  | none => _root_.Bool.false
  | some ctor =>
      let invalidCtor := {ctor with setInserts := ctor.setInserts.map setInsertWithWrongGuard}
      let invalid := {GuardedConstructorSet with
        «constructor» := some invalidCtor}
      match invalid.validate Capabilities.source with
      | .error diagnostic => diagnostic.message == "type mismatch for 'owner'"
      | .ok _ => _root_.Bool.false

#guard wrongConstructorGuardRejected

/- error: type mismatch -/
#guard_msgs (substring := true) in
noctium_contract WrongGuardedConstructorSet where
  set privileged : Bytes32

  constructor(owner : Bytes32) where
    when owner insert privileged[owner]
  end
end
