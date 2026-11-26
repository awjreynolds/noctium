import Noctium.Verification.GenericStateAdmissionPrefix
import Noctium.Verification.GenericStateEffectValidation
import Noctium.Verification.GenericStateKeys

namespace Noctium.Verification.GenericStateSourceNames
open Backend

def sourceNames (entry : Entrypoint) : List String :=
  entry.circuit.inputs.map (·.name) ++
  entry.circuit.outputs.map (·.name) ++
  entry.effects.filterMap (fun effect => match effect with
    | .readCell _ destination _ | .readMap _ destination .. => some destination
    | _ => none)

private theorem sourceNames_subset_production (ep : Entrypoint) :
    ∀ name ∈ sourceNames ep, name ∈ Impact.sourceNames ep := by
  intro name member
  unfold sourceNames at member
  unfold Impact.sourceNames
  simp only [List.append_assoc, List.mem_append] at member ⊢
  rcases member with input | output | read
  · exact Or.inl input
  · exact Or.inr (Or.inl output)
  · apply Or.inr (Or.inr _)
    obtain ⟨effect, present, named⟩ := List.mem_filterMap.mp read
    apply List.mem_flatMap.mpr
    refine ⟨effect, present, ?_⟩
    cases effect <;> simp at named
    all_goals simp [named]

/-- Production lowering excludes every source symbol that could collide with
generated native transcript names. -/
theorem lower_production_source_names_unreserved (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    ∀ name ∈ Impact.sourceNames ep, name.startsWith "_noctium_" = false := by
  obtain ⟨boundaries, _, checkedLowering, _, _⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state ep plan accepted
  have clear := Impact.lowerWithEffectBoundaries_sourceNamesChecked
    state ep plan boundaries checkedLowering
  intro name member
  cases reserved : name.startsWith "_noctium_" with
  | false => rfl
  | true => exact False.elim (List.any_eq_false.mp clear name member reserved)

theorem lower_source_names_unreserved (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan)
    (accepted : Impact.lower state ep = .ok plan) :
    ∀ name ∈ sourceNames ep, name.startsWith "_noctium_" = false := by
  intro name member
  exact lower_production_source_names_unreserved state ep plan accepted name
    (sourceNames_subset_production ep name member)

theorem lower_input_names_unique (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan)
    (accepted : Impact.lower state ep = .ok plan) :
    (ep.circuit.inputs.map (·.name)).Nodup := by
  have validated := GenericStateEffectValidation.lower_circuit_validated_source
    state ep plan accepted
  have inputNames : uniqueNames (ep.circuit.inputs.map (·.name)) = true := by
    cases unique : uniqueNames (ep.circuit.inputs.map (·.name)) with
    | true => rfl
    | false => simp [Circuit.validate, unique, bind, Except.bind] at validated
  apply GenericStateKeys.nodup_of_eraseDups_length_eq
  apply beq_iff_eq.mp
  simpa [uniqueNames] using inputNames

/-- Source circuit validation makes the actual public-input prefix names
distinct before the native effect plan appends its reads. -/
theorem lower_public_input_names_unique (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan)
    (accepted : Impact.lower state ep = .ok plan) :
    ((ep.circuit.inputs.filter (·.visibility == .«public»)).map (·.name)).Nodup := by
  exact List.Nodup.sublist
    ((List.filter_sublist (l := ep.circuit.inputs)
      (p := fun input => input.visibility == .«public»)).map (·.name))
    (lower_input_names_unique state ep plan accepted)

end Noctium.Verification.GenericStateSourceNames
