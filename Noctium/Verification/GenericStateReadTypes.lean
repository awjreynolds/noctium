import Noctium.Verification.GenericStateTypeAdmission
import Noctium.Verification.GenericStateEffectValidation
import Noctium.Verification.ScalarEffectReadFacts

namespace Noctium.Verification.GenericStateReadTypes
open Backend GenericStateEffectValidation GenericStateCheckedReadTrace

private theorem read_types_of_validated_effects {state : List StateDecl}
    {types final : TypeEnv} {effects : List Effect}
    (checked : ValidatedEffects state types effects final)
    (stateTypes : ∀ decl ∈ state, ∀ ty ∈ (match decl.kind with
      | .cell ty => [ty]
      | .map keyTy valueTy => [keyTy, valueTy]
      | _ => []), ty.validate stateEffectCaps = .ok ()) :
    ∀ offset, ∀ binding ∈ (readChunks effects offset).flatten,
      binding.2.validate stateEffectCaps = .ok () := by
  induction checked with
  | nil => simp [readChunks]
  | @readCell _ _ _ stateName destination ty declared _ _ ih =>
    intro offset binding member
    simp only [readChunks, effectReadChunk, List.flatten_cons, List.singleton_append,
      List.mem_cons] at member
    rcases member with rfl | tail
    · obtain ⟨decl, found, kind⟩ := declared
      have valid := stateTypes decl (List.mem_of_find?_eq_some found)
      rw [kind] at valid
      exact valid ty (by simp)
    · exact ih _ _ tail
  | @readMap _ _ _ stateName destination keyTy valueTy key declared _ _ _ ih =>
    intro offset binding member
    simp only [readChunks, effectReadChunk, List.flatten_cons, List.singleton_append,
      List.mem_cons] at member
    rcases member with rfl | tail
    · obtain ⟨decl, found, kind⟩ := declared
      have valid := stateTypes decl (List.mem_of_find?_eq_some found)
      rw [kind] at valid
      exact valid valueTy (by simp)
    · exact ih _ _ tail
  | require _ _ ih | writeCell _ _ _ ih | writeMap _ _ _ _ ih =>
    intro offset binding member
    exact ih offset binding (by simpa [readChunks, effectReadChunk] using member)
  | requireAbsent _ _ _ ih =>
    intro offset binding member
    simp only [readChunks, effectReadChunk, List.flatten_cons, List.singleton_append,
      List.mem_cons] at member
    rcases member with rfl | tail
    · rfl
    · exact ih _ _ tail

/-- The exact post-public read schedule inherits its types from accepted
state declarations and the compiler's generated Boolean absence bindings. -/
theorem lower_read_types (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state entry = .ok plan)
    (typed : ScalarStateEffects entry.effects)
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx) :
    ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      read.ty.validate stateEffectCaps = .ok () := by
  obtain ⟨_, checked⟩ := lower_validated_effects state entry plan accepted typed
  have stateTypes := GenericStateTypeAdmission.validated_state_types state entry plan accepted
  have metadata := ScalarEffectReadFacts.lower_postPublic_read_metadata state entry plan
    accepted scope
  intro read member
  have occurrence := List.mem_map_of_mem (f := readMetadata) member
  rw [metadata] at occurrence
  exact read_types_of_validated_effects checked stateTypes _ (readMetadata read) occurrence

end Noctium.Verification.GenericStateReadTypes
