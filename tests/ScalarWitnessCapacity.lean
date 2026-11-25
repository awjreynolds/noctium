import Noctium.Compiler
import Noctium.Backend.Zkir
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarWitness

open Lean Noctium Noctium.Backend Noctium.Verification
open NativeRelation NativeRelationJson ScalarWitness

section Source
open scoped Noctium

noctium_circuit scalarWitnessCapacityAddition where
  private left : Native
  private right : Native
  output sum : Native := disclose(add(left, right))
end
end Source

private def expectedInstructions : List Instruction := [
  .input .private "%input_left",
  .input .private "%input_right",
  .add (.reference "%input_left") (.reference "%input_right") "%v0",
  .impact (.immediate (scalar 1)) [.reference "%v0"],
  .output [.reference "%v0"]
]

#guard match Zkir.lowerCircuit scalarWitnessCapacityAddition with
  | .ok json =>
    match NativeRelationJson.decode json with
    | .ok program => decide (program.instructions = expectedInstructions)
    | .error _ => Bool.false
  | .error _ => Bool.false

/-- Any field inputs extend to a satisfying assignment of the exact decoded
standalone circuit. The original input bindings stay intact, and `%v0` stores
their field sum. -/
theorem twoInputAddition_witness (hash : Hash) (base : Assignment)
    (left right : Scalar) (program : Program)
    (exactInstructions : program.instructions = expectedInstructions) :
    let inputs := assign (assign base "%input_left" left) "%input_right" right;
    let assignment := assign inputs "%v0" (scalar (left.val + right.val));
    assignment "%input_left" = left ∧ assignment "%input_right" = right ∧
      (∀ instruction ∈ program.instructions, Instruction.Holds hash assignment instruction) := by
  dsimp only
  rw [exactInstructions]
  constructor
  · simp [assign]
  constructor
  · simp [assign]
  · intro instruction present
    simp [expectedInstructions] at present
    rcases present with rfl | rfl | rfl | rfl | rfl
    · simp [Instruction.Holds]
    · simp [Instruction.Holds]
    · simp [Instruction.Holds, Operand.read, assign]
    · simp [Instruction.Holds, Operand.read]
      rfl
    · simp [Instruction.Holds]
