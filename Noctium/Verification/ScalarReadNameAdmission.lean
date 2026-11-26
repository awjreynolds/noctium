import Noctium.Verification.ScalarEffectReadFacts
import Noctium.Verification.ScalarReadNames

namespace Noctium.Verification.ScalarReadNameAdmission

open Backend
open GenericStateCheckedReadTrace
open GenericStateEffectValidation

private theorem lower_source_names_unreserved (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan)
    (lowered : Impact.lower state ep = .ok plan) :
    ∀ name ∈ Impact.sourceNames ep, name.startsWith "_noctium_" = false := by
  obtain ⟨boundaries, _, boundedLowering, _, _⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state ep plan lowered
  have clear := Impact.lowerWithEffectBoundaries_sourceNamesChecked
    state ep plan boundaries boundedLowering
  intro name member
  cases reserved : name.startsWith "_noctium_" with
  | false => rfl
  | true => exact False.elim (List.any_eq_false.mp clear name member reserved)

private theorem lower_circuit_names_unreserved (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan)
    (lowered : Impact.lower state ep = .ok plan) :
    ∀ name ∈ ep.circuit.inputs.map (·.name) ++ ep.circuit.outputs.map (·.name),
      name.startsWith "_noctium_" = false := by
  have clear := lower_source_names_unreserved state ep plan lowered
  intro name member
  have sourceMember : name ∈ Impact.sourceNames ep := by
    unfold Impact.sourceNames
    simp only [List.append_assoc, List.mem_append] at member ⊢
    rcases member with input | output
    · exact Or.inl input
    · exact Or.inr (Or.inl output)
  exact clear name sourceMember

private theorem lower_scalar_destinations_unreserved (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan)
    (lowered : Impact.lower state ep = .ok plan) :
    ∀ name ∈ scalarReadDestinations ep.effects,
      name.startsWith "_noctium_" = false := by
  have clear := lower_source_names_unreserved state ep plan lowered
  intro name member
  have sourceMember : name ∈ Impact.sourceNames ep := by
    unfold Impact.sourceNames
    simp only [List.append_assoc, List.mem_append]
    apply Or.inr (Or.inr _)
    obtain ⟨effect, present, named⟩ := List.mem_filterMap.mp member
    apply List.mem_flatMap.mpr
    refine ⟨effect, present, ?_⟩
    cases effect <;> simp at named
    all_goals simp [named]
  exact clear name sourceMember

/-- Names in the accepted guarded scalar read suffix stay fresh from circuit
bindings and pairwise distinct, including generated absence aliases. -/
theorem lower_scalar_read_names (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan)
    (lowered : Impact.lower state ep = .ok plan)
    (scalar : ScalarStateEffects ep.effects)
    (scope : GuardedScalarReadEffects ep.effectGuards (ep.effects.zipIdx)) :
    let reads := plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)
    (∀ readSpec ∈ reads,
      readSpec.name ∉ ep.circuit.inputs.map (·.name) ++ ep.circuit.outputs.map (·.name)) ∧
      reads.Pairwise (fun left right => left.name ≠ right.name) := by
  let ordinal := Impact.publicInputReadCount ep.circuit.inputs
  let reads := plan.reads.drop ordinal
  have circuitNamesClear := lower_circuit_names_unreserved state ep plan lowered
  obtain ⟨distinctDestinations, freshDestinations⟩ :=
    GenericStateEffectValidation.lower_scalar_read_destinations_fresh_unique
      state ep plan lowered scalar
  have destinationsClear :=
    lower_scalar_destinations_unreserved state ep plan lowered
  obtain ⟨distinctNames, origins⟩ := ScalarReadNames.readChunkNames_fresh_unique
    ep.effects ordinal scalar distinctDestinations destinationsClear
  have metadata := ScalarEffectReadFacts.lower_postPublic_read_metadata
    state ep plan lowered scope
  have names : reads.map (·.name) =
      (readChunks ep.effects ordinal).flatten.map Prod.fst := by
    simpa only [List.map_map, Function.comp_def, readMetadata] using
      congrArg (List.map Prod.fst) metadata
  constructor
  · intro read member inCircuit
    have nameMember : read.name ∈
        (readChunks ep.effects ordinal).flatten.map Prod.fst := by
      rw [← names]
      exact List.mem_map_of_mem member
    rcases origins read.name nameMember with source | ⟨position, _, named⟩
    · have fresh := freshDestinations read.name source
      have freshCircuit : read.name ∉
          ep.circuit.inputs.map (·.name) ++ ep.circuit.outputs.map (·.name) := by
        simpa [GenericStateEffectValidation.initialEffectTypeEnv,
          List.map_append, List.map_map, Function.comp_def] using fresh
      exact freshCircuit inCircuit
    · have circuitClear := circuitNamesClear read.name inCircuit
      have reserved : read.name.startsWith "_noctium_" = true := by
        simpa [named] using ScalarReadNames.absenceName_reserved position
      rw [reserved] at circuitClear
      cases circuitClear
  · apply List.Pairwise.of_map (fun read : Impact.Read => read.name)
    · intro left right different
      exact different
    · rw [names]
      exact List.nodup_iff_pairwise_ne.mp distinctNames

end Noctium.Verification.ScalarReadNameAdmission
