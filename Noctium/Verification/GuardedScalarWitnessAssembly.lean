import Noctium.Verification.GuardedScalarRows
import Noctium.Verification.ScalarWitness

namespace Noctium.Verification.GuardedScalarWitnessAssembly

open Lean NativeRelation NativeRelationJson GuardedScalarRows ScalarWitness

private def inputOutput : Row → Option String
  | .strict (.input _ output) => some output
  | .publicInput output _ => some output
  | _ => none

private def inputOutputs (rows : List Row) : List String :=
  rows.filterMap inputOutput

private def instructionReferences : Instruction → List String
  | .input _ _ => []
  | .boolean value | .bits value _ | .neg value _ | .not value _ | .assert value =>
      operandIdentifiers value
  | .lessThan left right _ _ | .add left right _ | .mul left right _
  | .equal left right | .testEq left right _ =>
      operandIdentifiers left ++ operandIdentifiers right
  | .select condition yes no _ =>
      operandIdentifiers condition ++ operandIdentifiers yes ++ operandIdentifiers no
  | .hash values _ | .output values => values.flatMap operandIdentifiers
  | .impact guard values => operandIdentifiers guard ++ values.flatMap operandIdentifiers

private def isCopy (raw : Json) : Bool :=
  match stringField raw "op" with
  | .ok "copy" => true
  | _ => false

private def rowReferences (raw : Json) : Row → List String
  | .strict (.equal source (.reference destination)) =>
      if isCopy raw then operandIdentifiers source
      else operandIdentifiers source ++ [destination]
  | .strict instruction => instructionReferences instruction
  | .publicInput _ guard => guard.toList.flatMap operandIdentifiers
  | .impact guard inputs => operandIdentifiers guard ++ inputs.flatMap operandIdentifiers

/-- A decoded Copy is represented as equality by the native relation decoder.
Only its exact raw opcode makes the destination a witness definition. -/
private def definitionValue (hash : Hash) (raw : Json) (witness : Assignment) :
    Row → Option (String × Scalar)
  | .strict (.equal source (.reference destination)) =>
      if isCopy raw then
        some (destination, source.read witness)
      else none
  | .strict (.lessThan left right _ destination) =>
      some (destination, bit (decide ((left.read witness).val < (right.read witness).val)))
  | .strict (.add left right destination) =>
      some (destination, scalar ((left.read witness).val + (right.read witness).val))
  | .strict (.mul left right destination) =>
      some (destination, scalar ((left.read witness).val * (right.read witness).val))
  | .strict (.neg value destination) =>
      some (destination, scalar (Field.modulus - (value.read witness).val))
  | .strict (.testEq left right destination) =>
      some (destination, bit (decide (left.read witness = right.read witness)))
  | .strict (.not value destination) =>
      some (destination, if value.read witness = zero then one else zero)
  | .strict (.select condition yes no destination) =>
      some (destination, if condition.read witness = one then yes.read witness else no.read witness)
  | .strict (.hash values destination) =>
      some (destination, hash (values.map (·.read witness)))
  | _ => none

private def FramedAssignment (seed : Assignment) :=
  { witness : Assignment // ∀ name, witness ("%input_" ++ name) = seed ("%input_" ++ name) }

private theorem inputName_startsWith (name : String) :
    ("%input_" ++ name).startsWith "%input_" = true := by
  apply String.startsWith_string_iff.mpr
  rw [String.toList_append]
  have marker : "%input_".toList = ['%', 'i', 'n', 'p', 'u', 't', '_'] := by decide
  rw [marker]
  exact ⟨name.toList, rfl⟩

private theorem different_from_inputName (output name : String)
    (notInput : output.startsWith "%input_" = false) :
    output ≠ "%input_" ++ name := by
  intro same
  have starts := congrArg (fun value : String => value.startsWith "%input_") same
  simp [notInput, inputName_startsWith] at starts

/-- `registered` begins with all caller-supplied arguments and all row input
outputs. Their values already exist in `seed`, so the order check applies to
SSA temporaries introduced by defining rows. -/
private def assembleRows (hash : Hash) (seed : Assignment)
    (rawRows : List Json) (rows : List Row) (registered : List String)
    (state : FramedAssignment seed) : Except String (FramedAssignment seed) := do
  match rawRows, rows with
  | [], [] => pure state
  | raw :: rawTail, row :: rowTail => do
      ensure ((rowReferences raw row).all registered.contains)
        "native scalar row references a name before definition"
      match definitionValue hash raw state.1 row with
      | none => assembleRows hash seed rawTail rowTail registered state
      | some (destination, value) =>
          if registered.contains destination then
            throw "repeated native scalar definition"
          if notInput : destination.startsWith "%input_" = false then
            let nextState : FramedAssignment seed := ⟨
              ScalarWitness.assign state.1 destination value,
              by
                intro name
                have destinationDifferent : destination ≠ "%input_" ++ name :=
                  different_from_inputName destination name notInput
                calc
                  ScalarWitness.assign state.1 destination value ("%input_" ++ name) =
                      state.1 ("%input_" ++ name) :=
                    ScalarWitness.assign_other state.1 destination ("%input_" ++ name)
                      value destinationDifferent.symm
                  _ = seed ("%input_" ++ name) := state.2 name⟩
            assembleRows hash seed rawTail rowTail (destination :: registered) nextState
          else throw "native scalar definition overwrites a preseeded input"
  | _, _ => throw "decoded native scalar row count mismatch"

/-- Build witness values for guarded scalar rows. Header arguments and all row
input outputs read from the seed assignment. Defining scalar opcodes extend the
assignment in row order; constraint and observation rows leave it unchanged. -/
def assemble (hash : NativeRelation.Hash) (seed : NativeRelation.Assignment)
    (arguments : List String) (rawRows : List Lean.Json) :
    Except String { output : NativeRelation.Assignment //
      ∀ name, output ("%input_" ++ name) = seed ("%input_" ++ name) } := do
  ensure (arguments.all validIdentifier) "invalid scalar call input identifier"
  let rows ← rawRows.mapM GuardedScalarRows.decodeRow
  let seededRows := inputOutputs rows
  let registered := arguments ++ seededRows
  ensure (registered.eraseDups.length == registered.length)
    "native scalar input names collide or repeat"
  let initial : FramedAssignment seed := ⟨seed, by intro name; rfl⟩
  assembleRows hash seed rawRows rows registered initial

end Noctium.Verification.GuardedScalarWitnessAssembly
