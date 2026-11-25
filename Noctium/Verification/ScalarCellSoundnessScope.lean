import Noctium.Verification.GenericStateCheckedReadTrace
import Noctium.Verification.GenericStateEffectFold
import Noctium.Verification.GenericStateEffectStep
import Noctium.Verification.ScalarCellPlanScope
import Noctium.Verification.ScalarCellSourceReads
import Noctium.Verification.ScalarEffectReadFacts

namespace Noctium.Verification.ScalarCellSoundnessScope

open Backend GenericStateEffectValidation GenericStateInputValues
  GenericStatePrefixEnvironment ScalarNormalization ScalarCellSourceReads

private theorem cell_effects_scalar_state_effects (state : List StateDecl) :
    ∀ {effects : List Effect}, ScalarCellEffects state effects →
      ScalarStateEffects effects := by
  intro effects
  induction effects with
  | nil =>
      intro _
      exact .nil
  | cons effect rest ih =>
      intro scope
      have head := scope effect (by simp)
      have tailScope : ScalarCellEffects state rest := by
        intro next member
        exact scope next (List.mem_cons_of_mem _ member)
      have tail := ih tailScope
      cases head with
      | readCell name destination ty _ _ => exact .cons (.readCell name destination ty) tail
      | writeCell name ty value _ _ => exact .cons (.writeCell name ty value) tail

private theorem scalar_cell_type_validate {ty : Ty}
    (scalar : GenericStateCellAdmission.ScalarCellType ty) :
    ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok () := by
  cases scalar with
  | native => simp [Ty.validate, Ty.scalarKind, ScalarPolicy.validate, pure, Except.pure]
  | bool => simp [Ty.validate, Ty.scalarKind, ScalarPolicy.validate, pure, Except.pure]
  | uint maximum bound =>
      have belowModulus : maximum < Field.modulus :=
        Nat.lt_of_le_of_lt bound ScalarPolicy.maxUint_lt_native
      simp [Ty.validate, Ty.scalarKind, ScalarPolicy.validate, bound, belowModulus,
        pure, Except.pure, bind, Except.bind]

private theorem readChunks_scalar_cell_member (state : List StateDecl)
    (effects : List Effect) (ordinal : Nat)
    (cellEffects : ScalarCellEffects state effects)
    (metadata : GenericStateCheckedReadTrace.ReadMetadata)
    (member : metadata ∈
      (GenericStateCheckedReadTrace.readChunks effects ordinal).flatten) :
    ∃ name destination ty,
      Effect.readCell name destination ty ∈ effects ∧
      metadata = (destination, ty) ∧
      Nonempty (GenericStateCellAdmission.ScalarCellType ty) := by
  induction effects generalizing ordinal metadata with
  | nil => simp [GenericStateCheckedReadTrace.readChunks] at member
  | cons effect rest ih =>
      have headScope := cellEffects effect (by simp)
      have restScope : ScalarCellEffects state rest := by
        intro item itemMember
        exact cellEffects item (List.mem_cons_of_mem _ itemMember)
      cases headScope with
      | readCell name destination ty scalar declaration =>
          simp only [GenericStateCheckedReadTrace.readChunks,
            GenericStateCheckedReadTrace.effectReadChunk, List.flatten_cons] at member
          rcases List.mem_append.mp member with head | tail
          · simp only [List.mem_singleton] at head
            subst metadata
            exact ⟨name, destination, ty, by simp, rfl, ⟨scalar⟩⟩
          · obtain ⟨readName, readDestination, readTy, effectMember, same, support⟩ :=
              ih (ordinal + 1) restScope metadata tail
            exact ⟨readName, readDestination, readTy,
              List.mem_cons_of_mem _ effectMember, same, support⟩
      | writeCell name ty value scalar declaration =>
          simp only [GenericStateCheckedReadTrace.readChunks,
            GenericStateCheckedReadTrace.effectReadChunk, List.flatten_cons,
            List.nil_append] at member
          obtain ⟨readName, readDestination, readTy, effectMember, same, support⟩ :=
            ih ordinal restScope metadata member
          exact ⟨readName, readDestination, readTy,
            List.mem_cons_of_mem _ effectMember, same, support⟩

/-- Accepted scalar-cell lowering supplies the source-scope premises for the
checked soundness theorem. Type validity comes from the selected cell type
and the accepted plan's exact post-public read metadata. -/
theorem lowerEntrypoint_premises (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan)
    (accepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (unguarded : entry.effectGuards = [])
    (cellEffects : ScalarCellEffects state entry.effects)
    (operands : ∀ effect ∈ entry.effects, ScalarCellOperand effect) :
      ScalarStateEffects entry.effects ∧
      (∀ effect ∈ entry.effects, GenericStateEffectStep.ScalarOperands effect) ∧
      (∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
        read.components = [] ∧ (scalarType? read.ty).isSome = true ∧
          read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ()) := by
  have effectScope := cell_effects_scalar_state_effects state cellEffects
  have operandScope : ∀ effect ∈ entry.effects,
      GenericStateEffectStep.ScalarOperands effect := by
    intro effect member
    cases cellEffects effect member with
    | readCell name destination ty scalar declaration =>
        simp [GenericStateEffectStep.ScalarOperands]
    | writeCell name ty value scalar declaration =>
        have valueOperand : ScalarExpression value := by
          simpa [ScalarCellOperand] using operands (.writeCell name ty value) member
        exact valueOperand
  let ep := Passes.pruneEntrypoint entry
  have epUnguarded : ep.effectGuards = [] := by
    simpa [ep, Passes.pruneEntrypoint] using unguarded
  have epCellEffects : ScalarCellEffects state ep.effects := by
    simpa [ep, Passes.pruneEntrypoint] using cellEffects
  obtain ⟨_, scope⟩ := ScalarCellPlanScope.lower_scope state ep plan
    accepted epUnguarded epCellEffects
  have unguardedAll : ep.effectGuards.all Option.isNone = true := by
    simp [epUnguarded]
  have scalarEffects : ScalarStateEffects ep.effects := by
    simpa [ep, Passes.pruneEntrypoint] using effectScope
  have guardedScope := GenericStateEffectFold.unguarded_read_scope ep
    unguardedAll scalarEffects
  have metadata := ScalarEffectReadFacts.lower_postPublic_read_metadata state ep plan
    accepted guardedScope
  have sameInputs : ep.circuit.inputs = entry.circuit.inputs := rfl
  refine ⟨effectScope, operandScope, ?_⟩
  intro read member
  have epMember : read ∈
      plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs) := by
    simpa only [sameInputs] using member
  have scopeFacts := scope read epMember
  have metadataMember : GenericStateCheckedReadTrace.readMetadata read ∈
      (GenericStateCheckedReadTrace.readChunks ep.effects
        (Impact.publicInputReadCount ep.circuit.inputs)).flatten := by
    rw [← metadata]
    exact List.mem_map_of_mem epMember
  obtain ⟨name, destination, ty, sourceMember, signature, support⟩ :=
    readChunks_scalar_cell_member state ep.effects
      (Impact.publicInputReadCount ep.circuit.inputs) epCellEffects
      (GenericStateCheckedReadTrace.readMetadata read) metadataMember
  have readType : read.ty = ty := by
    change read.ty = ty
    exact congrArg Prod.snd signature
  obtain ⟨scalarType⟩ := scopeFacts.2
  have scalarSupport : scalarType? read.ty = some scalarType :=
    scalarType?_supported scalarType
  have typed : read.ty.validate
      {poseidon2 := true, stateCells := true, stateMaps := true} = .ok () := by
    rw [readType]
    obtain ⟨cellType⟩ := support
    exact scalar_cell_type_validate cellType
  exact ⟨scopeFacts.1.1, by simp [scalarSupport], typed⟩

end Noctium.Verification.ScalarCellSoundnessScope
