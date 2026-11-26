import Noctium.Verification.ScalarAllocationOutputFrame
import Noctium.Verification.NativeRelationInstructionProjection

namespace Noctium.Verification.GenericStateLedgerAllocation

open Lean
open Backend Backend.Native NativeRelation

/-- Strict native decoding connects the actual accepted instruction vector to
the list of relation instructions. The plan is extracted from accepted lowering. -/
theorem lowerEntrypoint_instruction_count (state : List StateDecl)
    (entry : Entrypoint) (json : Json) (program : Program)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok program) :
    ∃ plan, Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.instructions.size =
        program.instructions.length := by
  obtain ⟨plan, _, instructions, planAccepted, _, _, _, exactBodyInstructions,
    decodedInstructions⟩ :=
    NativeRelationInstructionProjection.lowerEntrypoint_instructionProjection
      state entry json program lowered decoded
  refine ⟨plan, planAccepted, ?_⟩
  calc
    ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.instructions.size =
        instructions.size := congrArg Array.size exactBodyInstructions.symm
    _ = program.instructions.length :=
      NativeRelationInstructionProjection.decodedRows_count decodedInstructions

/-- The exact accepted ledger body allocates from its emitted output slots.
The native validator separately checks row count and output-vector width. -/
theorem lowerEntrypoint_allocation_bounds (state : List StateDecl) (entry : Entrypoint)
    (json : Json) (lowered : Zkir.lowerEntrypoint state entry = .ok json) :
    ∃ plan, Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      let body := ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2
      body.next ≤ body.outputDefinitions ∧
        body.outputDefinitions ≤ body.instructions.size * Native.maxVectorLength ∧
        body.instructions.size ≤ Native.maxInstructions := by
  obtain ⟨plan, accepted, rows, outputs⟩ :=
    ScalarAllocationOutputFrame.lowerEntrypoint_instruction_and_output_bounds state entry json lowered
  have frame := Zkir.lowerEntrypointBody_outputCapacityFrame (Passes.pruneEntrypoint entry) plan {}
  have names := frame.next_le_outputDefinitions (by simp [Zkir.LowerState.outputDefinitions])
  exact ⟨plan, accepted, names, outputs, rows⟩

/-- Producer admission bounds allocated names by checked output slots. This
bound comes from the accepted lowering itself and is independent of decoded
instruction-row count. -/
theorem lowerEntrypoint_budget (state : List StateDecl) (entry : Entrypoint)
    (json : Json) (lowered : Zkir.lowerEntrypoint state entry = .ok json) :
    ∃ plan, Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
  obtain ⟨plan, planAccepted, names, outputs, rows⟩ :=
    lowerEntrypoint_allocation_bounds state entry json lowered
  exact ⟨plan, planAccepted,
    Nat.le_trans names (Nat.le_trans outputs (Nat.mul_le_mul_right Native.maxVectorLength rows))⟩

end Noctium.Verification.GenericStateLedgerAllocation
