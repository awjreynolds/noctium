import Noctium.Frontend
import Noctium.Backend.Zkir

open scoped Noctium
open Lean
open Noctium

noctium_circuit ordinaryTupleProjection where
  public pair : [UInt 8, Bool]
  output first : UInt 8 := tupleAt(pair, 0)
  output flag : Bool := tupleAt(pair, 1)
end

noctium_circuit privateTupleProjection where
  private pair : [UInt 8, Bool]
  output first : UInt 8 := disclose(tupleAt(pair, 0))
  output flag : Bool := disclose(tupleAt(pair, 1))
end

noctium_contract OrdinaryTupleInputs where
  entry publicProject uses ordinaryTupleProjection where
    return firstResult : UInt 8 := first
    return flagResult : Bool := flag
  end
  entry project uses privateTupleProjection arguments [pair] where
    return firstResult : UInt 8 := first
    return flagResult : Bool := flag
  end
end

private def ordinaryTupleProjectionEntry : Entrypoint :=
  match OrdinaryTupleInputs.entrypoints with
  | publicEntry :: _ => publicEntry
  | _ => {name := "missing", circuit := {name := "missing"}}

private def privateTupleProjectionEntry : Entrypoint :=
  match OrdinaryTupleInputs.entrypoints with
  | _ :: privateEntry :: _ => privateEntry
  | _ => {name := "missing", circuit := {name := "missing"}}

private def ordinaryTupleContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "ordinary tuple projection does not hash"
}

#guard ordinaryTupleProjection.inputs.map (·.name) == ["pair.0", "pair.1"]
#guard ordinaryTupleProjection.inputs.map (·.ty) == [.uint 255, .bool]
#guard ordinaryTupleProjection.inputs.map (·.visibility) == [.public, .public]
#guard ordinaryTupleProjection.outputs.map (·.name) == ["first", "flag"]
#guard ordinaryTupleProjection.outputs.map (·.ty) == [.uint 255, .bool]
#guard ordinaryTupleProjectionEntry.callInputViews.isEmpty
#guard privateTupleProjection.inputs.map (·.visibility) == [.private, .private]
#guard privateTupleProjectionEntry.callInputViews.map (fun view => (view.name, view.fields)) == [
  ("pair", [("pair.0", .uint 255), ("pair.1", .bool)])]

#guard match ordinaryTupleProjection.run ordinaryTupleContext [
    ("pair.0", .uint 255 173), ("pair.1", .bool _root_.Bool.true)] with
  | .ok [("first", .uint 255 173), ("flag", .bool _root_.Bool.true)] => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match ordinaryTupleProjection.run ordinaryTupleContext [
    ("pair.0", .uint 255 256), ("pair.1", .bool _root_.Bool.true)] with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

private def ordinaryTupleZkirInputOrder : _root_.Bool :=
  match Backend.Zkir.lowerEntrypoint OrdinaryTupleInputs.state ordinaryTupleProjectionEntry with
  | .error _ => _root_.Bool.false
  | .ok program =>
    let instructions := (program.getObjValD "instructions").getArr?.toOption.getD #[]
    let inputNames := instructions.filterMap fun instruction =>
      if (instruction.getObjValD "op").getStr?.toOption == some "public_input" then
        (instruction.getObjValD "output").getStr?.toOption
      else none
    inputNames.toList == ["%input_pair.0", "%input_pair.1"]

#guard ordinaryTupleZkirInputOrder
