import Noctium.Verification.GuardedReadDescriptorTrace
import Noctium.Verification.ScalarEffectReadFacts
import Noctium.Verification.ScalarGuardedActivityAdmission
import Noctium.Verification.ScalarReadNameAdmission
import Noctium.Verification.ScalarReadTypeAdmission

namespace Noctium.Verification.ScalarGuardedReadAdmission

open Backend GenericStateCheckedReadTrace
open GenericStateInputValues (scalarType?)
open ScalarGuardedPlanAdmission (ScalarEffect)

/-- The actual post-public suffix of an admitted guarded plan has plain,
validated scalar descriptors with distinct names fresh against circuit values. -/
theorem lower_read_admission (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (lowered : Impact.lower state ep = .ok plan)
    (effects : ∀ effect ∈ ep.effects, ScalarEffect state effect) :
    let reads := plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)
    (∀ readSpec ∈ reads, readSpec.components = [] ∧
      (scalarType? readSpec.ty).isSome = _root_.Bool.true ∧
      readSpec.ty.validate
        {poseidon2 := _root_.Bool.true, stateCells := _root_.Bool.true,
         stateMaps := _root_.Bool.true} = .ok ()) ∧
    (∀ readSpec ∈ reads, readSpec.name ∉
      ep.circuit.inputs.map (·.name) ++ ep.circuit.outputs.map (·.name)) ∧
    reads.Pairwise (fun left right => left.name ≠ right.name) := by
  have scope := ScalarGuardedActivityAdmission.lower_guarded_scalar_read_scope
    state ep plan lowered effects
  have scalarEffects := ScalarGuardedActivityAdmission.scalar_state_effects_of_admitted
    state ep.effects effects
  have names := ScalarReadNameAdmission.lower_scalar_read_names
    state ep plan lowered scalarEffects scope
  have components := GuardedReadDescriptorTrace.lower_post_public_read_components
    state ep plan lowered scope
  have metadata := ScalarEffectReadFacts.lower_postPublic_read_metadata state ep plan lowered scope
  refine ⟨?_, names.1, names.2⟩
  intro readSpec present
  have readMetadataPresent := List.mem_map_of_mem (f := readMetadata) present
  rw [metadata] at readMetadataPresent
  obtain ⟨supported⟩ := ScalarReadTypeAdmission.readChunks_scalar_type state ep.effects
    (Impact.publicInputReadCount ep.circuit.inputs) effects (readMetadata readSpec)
    readMetadataPresent
  exact ⟨components readSpec present,
    ScalarReadTypeAdmission.scalarCellType_decoder_and_validation supported⟩

end Noctium.Verification.ScalarGuardedReadAdmission
