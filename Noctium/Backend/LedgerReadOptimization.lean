import Noctium.Backend.LedgerReadBound
import Noctium.Backend.Zkir
import Noctium.Verification.NativeRelationJson

namespace Noctium.Backend.LedgerReadOptimization

open Lean Verification.NativeRelation

/-- Experimental operation output for the qualified ledger path. Retain the
strict relation until the external verifier and exact artifact gate pass. -/
structure Operation where
  plan : Impact.Plan
  strict : Json
  optimized : Json
  proofInput : String
  rangeIndex : Nat
  exactRemoval : ∃ (original candidate : Program) (before after : List Instruction),
    Verification.NativeRelationJson.decode strict = .ok original ∧
    Verification.NativeRelationJson.decode optimized = .ok candidate ∧
    candidate.instructions = before ++ after ∧
    original = {candidate with instructions := before ++ [.bits (.reference proofInput) 128] ++ after}

/-- Derive both relations and the typed ledger read from the same source. This
entrypoint never accepts an unchecked or caller-supplied certificate or ZKIR. -/
def lower (contract : Contract) (entrypoint cell destination : String) : Except String Operation := do
  let read ← LedgerReadBound.check contract entrypoint cell destination
  let some entry := contract.entrypoints.find? (·.name == entrypoint)
    | throw s!"unknown entrypoint '{entrypoint}'"
  let entry := Passes.pruneEntrypoint entry
  let (plan, strict) ← (Zkir.lowerPrunedEntrypoint contract.state entry).mapError (·.message)
  let strictDecoded : {value // Verification.NativeRelationJson.decode strict = .ok value} ←
    match decoded : Verification.NativeRelationJson.decode strict with
    | .error reason => throw reason
    | .ok value => pure ⟨value, decoded⟩
  let relation := strictDecoded.val
  unless relation.communicationsCommitment do throw "ledger calls must bind the communications commitment"
  let input := Instruction.input .«public» read.readInput
  unless (relation.instructions.filter (· == input)).length == 1 do
    throw "expected exactly one matching unconditional public read input"
  let groups := relation.instructions.filterMap fun instruction => match instruction with
    | .impact guard values => some (guard, values)
    | _ => none
  let statement := (Operand.immediate one,
    [Operand.immediate (scalar 0x0c), .immediate one, .immediate (scalar 16), .reference read.readInput])
  unless groups[read.popeqGroup]? == some statement do
    throw "expected exact unguarded UInt128 read in the proof transcript"
  let range := Instruction.bits (.reference read.readInput) 128
  unless (relation.instructions.filter (· == range)).length == 1 do
    throw "expected exactly one UInt128 constraint for the certified read"
  let rangePosition : {index // relation.instructions.findIdx? (fun i => decide (i = range)) = some index} ←
    match found : relation.instructions.findIdx? (fun i => decide (i = range)) with
    | none => throw "missing source-derived UInt128 range constraint"
    | some index => pure ⟨index, found⟩
  let rangeIndex := rangePosition.val
  let attrs ← strict.getObj?
  let instructions ← Native.arrayField strict "instructions"
  let remaining := instructions.toList.take rangeIndex ++ instructions.toList.drop (rangeIndex + 1)
  let optimized := Json.obj (attrs.insert "instructions" (.arr remaining.toArray))
  let candidateDecoded : {value // Verification.NativeRelationJson.decode optimized = .ok value} ←
    match decoded : Verification.NativeRelationJson.decode optimized with
    | .error reason => throw reason
    | .ok value => pure ⟨value, decoded⟩
  let candidate := candidateDecoded.val
  let before := relation.instructions.take rangeIndex
  let after := relation.instructions.drop (rangeIndex + 1)
  if agrees : candidate = {relation with instructions := before ++ after} then
    have indexed := List.findIdx?_eq_some_iff_getElem.mp rangePosition.property
    have within : rangeIndex < relation.instructions.length := indexed.choose
    have atIndex : relation.instructions[rangeIndex] = range :=
      of_decide_eq_true indexed.choose_spec.1
    have originalInstructions : relation.instructions = before ++ [range] ++ after := by
      change relation.instructions = relation.instructions.take rangeIndex ++ [range] ++
        relation.instructions.drop (rangeIndex + 1)
      rw [← atIndex, ← List.take_succ_eq_append_getElem within, List.take_append_drop]
    pure {
      plan, strict, optimized, proofInput := read.readInput, rangeIndex
      exactRemoval := ⟨relation, candidate, before, after, strictDecoded.property, candidateDecoded.property,
        by rw [agrees], by
          rw [agrees]
          change relation = {relation with instructions := before ++ [range] ++ after}
          rw [← originalInstructions]⟩
    }
  else throw "optimized circuit changed more than the certified range constraint"

end Noctium.Backend.LedgerReadOptimization
