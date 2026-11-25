import Noctium.Verification.ScalarAllocationOutputFrame
import Noctium.Verification.NativeRelationInstructionProjection

namespace Noctium.Verification.GenericStateLedgerAllocation

open Lean
open Backend Backend.Native NativeRelation

private theorem mapM_length {function : α → Except String β} {values : List α}
    {results : List β} (success : values.mapM function = .ok results) :
    results.length = values.length := by
  induction values generalizing results with
  | nil => cases success; rfl
  | cons value rest ih =>
    cases first : function value with
    | error error =>
      simp [List.mapM_cons, first, bind, Except.bind] at success
    | ok head =>
      cases tailResult : rest.mapM function with
      | error error =>
        simp [List.mapM_cons, first, tailResult, bind, Except.bind] at success
      | ok tail =>
        have successEq := success
        simp only [List.mapM_cons, first, tailResult, bind, Except.bind] at successEq
        change Except.ok (head :: tail) = Except.ok results at successEq
        have resultEq : head :: tail = results := Except.ok.inj successEq
        cases resultEq
        have tailSuccess : rest.mapM function = .ok tail := tailResult
        simp only [List.length_cons, ih tailSuccess]

/-- The strict relation decoder preserves the exact number of producer rows.
This bound concerns decoded instructions, not allocated SSA output slots. -/
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
    _ = instructions.toList.length := by simp
    _ = program.instructions.length := (mapM_length decodedInstructions).symm

/-- Producer admission bounds SSA names by checked output slots. This is
separate from the decoded instruction-row count above. -/
theorem lowerEntrypoint_outputCapacity (state : List StateDecl) (entry : Entrypoint)
    (json : Json) (lowered : Zkir.lowerEntrypoint state entry = .ok json) :
    ∃ plan, Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
  obtain ⟨plan, planAccepted, capacity, _⟩ :=
    ScalarAllocationOutputFrame.lowerEntrypoint_names_fit_outputCapacity
      state entry json lowered
  exact ⟨plan, planAccepted, capacity⟩

end Noctium.Verification.GenericStateLedgerAllocation
