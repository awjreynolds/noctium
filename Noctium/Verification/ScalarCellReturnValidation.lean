import Noctium.Verification.GenericStateCaps
import Noctium.Verification.GenericStateCheckedReadDecode
import Noctium.Verification.GenericStateEffectValidation
import Noctium.Verification.GuardedEffectPrefix
import Noctium.Verification.ScalarCellSourceReads

namespace Noctium.Verification.ScalarCellReturnValidation

open Backend GenericStateEffectValidation GenericStateCellAdmission
open ScalarCellSourceReads

private def readSignature (read : Impact.Read) : String × Ty × List (String × Ty) :=
  (read.name, read.ty, read.components)

private def effectReadSignatures : Effect → List (String × Ty × List (String × Ty))
  | .readCell _ destination ty => [(destination, ty, [])]
  | _ => []

private theorem cell_effects_are_scalar_state_effects (state : List StateDecl) :
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

private theorem appendEffect_none_cell_read_signatures (state : List StateDecl)
    (effect : Effect) (scope : GenericStateCellAdmission.ScalarCellEffect state effect)
    (before after : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state effect none before = .ok after) :
    after.reads.map readSignature =
      before.reads.map readSignature ++ effectReadSignatures effect := by
  obtain ⟨raw, lowered, _, sameReads⟩ :=
    GuardedEffectPrefix.appendEffectWithActivity_none_result state effect before after accepted
  have same :
      (fun plan : Impact.Plan => plan.reads.map readSignature) <$>
        Impact.appendEffect state effect before =
      (fun _ : Impact.Plan => before.reads.map readSignature ++
        effectReadSignatures effect) <$> Impact.appendEffect state effect before := by
    cases scope <;>
      simp only [Impact.appendEffect, effectReadSignatures, readSignature,
        map_bind, LawfulApplicative.map_pure, List.map_append, List.map_cons,
        List.map_nil, List.append_nil] <;> rfl
  rw [lowered] at same
  have rawShape := Except.ok.inj same
  rw [sameReads]
  exact rawShape

private theorem guarded_cell_trace_read_signatures (state : List StateDecl)
    (effects : List Effect) (start : Nat) (before final : Impact.Plan)
    (offsets : List Nat) (scope : ScalarCellEffects state effects)
    (trace : Impact.GuardedEffectTrace state [] (effects.zipIdx start)
      before final offsets) :
    final.reads.map readSignature =
      before.reads.map readSignature ++ effects.flatMap effectReadSignatures := by
  induction effects generalizing start before final offsets with
  | nil =>
      cases trace
      simp
  | cons effect rest ih =>
      rw [List.zipIdx_cons] at trace
      cases trace with
      | @cons _ _ _ next _ nextOffsets step tail =>
          have headScope := scope effect (by simp)
          have head := appendEffect_none_cell_read_signatures state effect headScope
            before next (by simpa using step)
          have tailScope : ScalarCellEffects state rest := by
            intro item member
            exact scope item (List.mem_cons_of_mem _ member)
          have tailShape := ih (start + 1) next final nextOffsets tailScope tail
          rw [tailShape, head]
          simp [List.flatMap_cons, List.append_assoc]

private theorem plan_read_signatures_after_public_prefix (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan)
    (accepted : Impact.lower state entry = .ok plan)
    (unguarded : entry.effectGuards = [])
    (cellScope : ScalarCellEffects state entry.effects) :
    (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map
      readSignature = entry.effects.flatMap effectReadSignatures := by
  obtain ⟨boundaries, inputPlan, _, inputAccepted, effectsAccepted⟩ :=
    GenericStateAdmissionPrefix.lower_input_prefix state entry plan accepted
  rw [unguarded] at effectsAccepted
  have prefixCount : inputPlan.reads.length =
      Impact.publicInputReadCount entry.circuit.inputs := by
    exact GenericStateAdmissionPrefix.publicInputPlan_readCount
      entry.circuit.inputs inputPlan inputAccepted
  have trace := Impact.appendEffectsGuardedWithBoundaries_trace state entry.effects []
    inputPlan plan boundaries effectsAccepted
  have complete := guarded_cell_trace_read_signatures state entry.effects 0
    inputPlan plan boundaries cellScope trace
  rw [List.map_drop, complete, ← prefixCount]
  simp [List.length_map]

private theorem read_typeBindings_scalar_cell (read : Impact.Read)
    (plain : read.components = [])
    (supported : GenericStateCellAdmission.ScalarCellType read.ty) :
    read.typeBindings = [(read.name, read.ty)] := by
  cases read with
  | mk name ty components schema guard rootCellRead =>
      simp only at plain
      subst components
      let directRead : Impact.Read :=
        {name, ty, components := [], schema, guard, rootCellRead}
      have supportedType : (GenericStateInputValues.scalarType? ty).isSome = true := by
        cases supported <;> rfl
      have directReadPlain : directRead.components = [] := by
        simp [directRead]
      have bindings := GenericStateCheckedReadDecode.supported_plain_read_bindings
        directRead directReadPlain supportedType
      have plainScalarReads : directRead.scalarReads = [directRead] := by
        simp [Impact.Read.scalarReads, directRead]
      change directRead.typeBindings = [(name, ty)]
      cases supported <;>
        simp [Impact.Read.typeBindings, directRead, plainScalarReads, bindings]

private theorem postPublic_typeBindings_eq_effect_bindings
    (state : List StateDecl) (entry : Entrypoint) (plan : Impact.Plan)
    (accepted : Impact.lower state entry = .ok plan)
    (unguarded : entry.effectGuards = [])
    (cellScope : ScalarCellEffects state entry.effects) :
    (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).flatMap
        Impact.Read.typeBindings = entry.effects.flatMap effectTypeBindings := by
  let reads := plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)
  have shape : reads.map readSignature = entry.effects.flatMap effectReadSignatures := by
    exact plan_read_signatures_after_public_prefix state entry plan accepted unguarded cellScope
  have supportedPlain : ∀ read ∈ reads,
      read.components = [] ∧ Nonempty (GenericStateCellAdmission.ScalarCellType read.ty) := by
    intro read member
    have signatureMember : readSignature read ∈ entry.effects.flatMap effectReadSignatures := by
      rw [← shape]
      exact List.mem_map_of_mem member
    obtain ⟨effect, effectMember, readMember⟩ := List.mem_flatMap.mp signatureMember
    cases effectScope : cellScope effect effectMember with
    | readCell name destination ty supported declaration =>
        simp [effectReadSignatures] at readMember
        have signatureEqual : readSignature read = (destination, ty, []) := readMember
        have components : read.components = [] :=
          congrArg (fun signature => signature.2.2) signatureEqual
        have readType : read.ty = ty :=
          congrArg (fun signature => signature.2.1) signatureEqual
        refine ⟨components, ⟨?_⟩⟩
        rw [readType]
        exact supported
    | writeCell name ty value supported declaration =>
        simp [effectReadSignatures] at readMember
  have typeLists : reads.map Impact.Read.typeBindings =
      reads.map (fun read => [(read.name, read.ty)]) := by
    apply List.map_congr_left
    intro read member
    obtain ⟨plain, ⟨supported⟩⟩ := supportedPlain read member
    exact read_typeBindings_scalar_cell read plain supported
  have readTypes : reads.flatMap Impact.Read.typeBindings =
      reads.map (fun read => (read.name, read.ty)) := by
    rw [List.flatMap_def, typeLists]
    simpa only [List.flatMap_def] using
      (List.map_eq_flatMap (f := fun read : Impact.Read => (read.name, read.ty))
        (l := reads)).symm
  have projected := congrArg
    (List.map (fun signature : String × Ty × List (String × Ty) =>
      (signature.1, signature.2.1))) shape
  have effectBindings : reads.map (fun read => (read.name, read.ty)) =
      entry.effects.flatMap effectTypeBindings := by
    have projectedEffects (effects : List Effect)
        (scope : ScalarCellEffects state effects) :
        (effects.flatMap effectReadSignatures).map
            (fun signature : String × Ty × List (String × Ty) =>
              (signature.1, signature.2.1)) =
          effects.flatMap effectTypeBindings := by
      induction effects with
      | nil => rfl
      | cons effect rest ih =>
          have headScope := scope effect (by simp)
          have tailScope : ScalarCellEffects state rest := by
            intro item member
            exact scope item (List.mem_cons_of_mem _ member)
          have head :
              (effectReadSignatures effect).map
                  (fun signature : String × Ty × List (String × Ty) =>
                    (signature.1, signature.2.1)) = effectTypeBindings effect := by
            cases headScope <;> simp [effectReadSignatures, effectTypeBindings]
          simp only [List.flatMap_cons, List.map_append, head, ih tailScope]
    have effectsProjected := projectedEffects entry.effects cellScope
    calc
      _ = (entry.effects.flatMap effectReadSignatures).map
          (fun signature : String × Ty × List (String × Ty) =>
            (signature.1, signature.2.1)) := by
              simpa only [List.map_map, Function.comp_def, readSignature] using projected
      _ = _ := effectsProjected
  rw [readTypes, effectBindings]

theorem lower_cell_final_types (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan)
    (accepted : Impact.lower state entry = .ok plan)
    (unguarded : entry.effectGuards = [])
    (cellScope : ScalarCellEffects state entry.effects)
    (finalTypes : TypeEnv)
    (validated : ValidatedEffects state (initialEffectTypeEnv entry)
      entry.effects finalTypes) :
    finalTypes = plan.typeEnvironment entry := by
  have finalShape := validated.type_environment_shape
  have typeBindings := postPublic_typeBindings_eq_effect_bindings
    state entry plan accepted unguarded cellScope
  have planShape : plan.typeEnvironment entry =
      GenericStateEffectValidation.initialEffectTypeEnv entry ++
        entry.effects.flatMap effectTypeBindings := by
    change entry.circuit.inputs.map (fun input => (input.name, input.ty)) ++
        entry.circuit.outputs.map (fun output => (output.name, output.ty)) ++
        (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).flatMap
          Impact.Read.typeBindings = _
    rw [typeBindings]
    rfl
  rw [finalShape, planShape]

/-- Accepted unguarded scalar-cell lowering validates each physical return
under the exact type environment emitted for the plan's post-public reads. -/
theorem lower_cell_returns_valid (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan)
    (accepted : Impact.lower state entry = .ok plan)
    (unguarded : entry.effectGuards = [])
    (cellScope : ScalarCellEffects state entry.effects)
    (finalTypes : TypeEnv)
    (validated : ValidatedEffects state (initialEffectTypeEnv entry)
      entry.effects finalTypes) :
    ∀ output ∈ entry.returns,
      output.value.validate Capabilities.crypto (plan.typeEnvironment entry) = .ok () := by
  have scalarEffects := cell_effects_are_scalar_state_effects state cellScope
  obtain ⟨sourceFinal, sourceValidated, returnsValid⟩ :=
    GenericStateEffectValidation.lower_validated_effects_and_returns
      state entry plan accepted scalarEffects
  have sameFinal : sourceFinal = finalTypes :=
    ValidatedEffects.final_unique sourceValidated validated
  have sameEnvironment := lower_cell_final_types
    state entry plan accepted unguarded cellScope finalTypes validated
  intro output member
  have sourceValid : output.value.validate Capabilities.source finalTypes = .ok () := by
    rw [← sameFinal]
    simpa [GenericStateEffectValidation.stateEffectCaps, Capabilities.source] using
      returnsValid output member
  rw [← sameEnvironment]
  rw [← GenericStateCaps.expr_validate_source_crypto output.value finalTypes]
  exact sourceValid

end Noctium.Verification.ScalarCellReturnValidation
