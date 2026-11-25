import Noctium.Compiler
import Noctium.Frontend
import Noctium.Semantics

open Noctium Noctium.Helpers
open scoped Noctium

/- The helper's UIntRange 511 parameter has inclusive maximum 510 in the
   checked helper IR. The exported wrapper accepts two UInt8 values, whose
   checked sum has that exact bound. -/
private def boundedUintHelperProgram : Program := {
  declarations := [
    {id := ⟨0, 0⟩, name := "addViaHelper",
      parameters := [⟨"left", .uint 255⟩, ⟨"right", .uint 255⟩],
      result := .scalar (.uint 510),
      body := [.return (some (.call "acceptBoundedSum" [
        .binary .add (.ref "left") (.ref "right")]))]},
    {id := ⟨0, 1⟩, name := "acceptBoundedSum", declaredPure := Bool.true,
      parameters := [⟨"value", .uint 510⟩], result := .scalar (.uint 510),
      body := [.return (some (.ref "value"))]}]
  exports := [{name := "addViaHelper", target := ⟨0, 0⟩, inputs := [
    {name := "left", ty := .uint 255, visibility := .public},
    {name := "right", ty := .uint 255, visibility := .public}]}]
}

noctium_helper_circuit boundedUintHelperCircuit from boundedUintHelperProgram entry "addViaHelper"

noctium_contract BoundedUintHelper where
  entry addViaHelper uses boundedUintHelperCircuit where
    return sum : UIntRange 511 := result
  end
end

private def ctx : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "this fixture does not hash"
}

#guard boundedUintHelperCircuit.inputs.map (·.name) == ["left", "right"]
#guard boundedUintHelperCircuit.outputs.map (·.name) == ["result"]
#guard boundedUintHelperCircuit.outputs.map (·.ty) == [.uint 510]
#guard match boundedUintHelperCircuit.run ctx [
    ("left", .uint 255 255), ("right", .uint 255 255)] with
  | .ok [("result", .uint 510 510)] => Bool.true
  | _ => Bool.false

/- Narrowing only the helper parameter must reject the same UInt8 addition.
   Its result remains a subtype of the wrapper's UIntRange 511 result. -/
private def narrowParameterProgram : Program :=
  match boundedUintHelperProgram.declarations with
  | outer :: helper :: rest =>
      {boundedUintHelperProgram with declarations :=
        outer :: {helper with parameters := [⟨"value", .uint 509⟩]} :: rest}
  | _ => boundedUintHelperProgram

/- error: :1:1: no compatible helper overload 'acceptBoundedSum' -/
#guard_msgs (substring := true) in
noctium_helper_circuit rejectsNarrowHelperArgument from narrowParameterProgram entry "addViaHelper"
