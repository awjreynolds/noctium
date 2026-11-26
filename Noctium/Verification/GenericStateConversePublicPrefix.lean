import Noctium.Verification.GenericStateAdmissionPrefix
import Noctium.Verification.ScalarCellNativePublicPrefix
import Noctium.Verification.GenericStateAliases
import Noctium.Verification.GenericStateEffectValidation
import Noctium.Verification.ScalarWitnessEntrypointAliases

namespace Noctium.Verification.GenericStateConversePublicPrefix

open Backend NativeRelation ScalarNormalization NativeState

private theorem lookup_none_of_absent_name (items : List (String × α))
    (name : String) (absent : name ∉ items.map Prod.fst) : items.lookup name = none := by
  apply List.lookup_eq_none_iff.mpr
  intro pair present
  have different : name ≠ pair.1 := by
    intro equal
    exact absent (List.mem_map.mpr ⟨pair, present, equal.symm⟩)
  simp [different]

/-- Circuit outputs and appended read bindings leave the original lookup of
every declared input unchanged. -/
theorem source_input_lookup (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext)
    (values outputs future : EvalEnv) (inputs : Assignment)
    (accepted : Impact.lower state entry = .ok plan)
    (admitted : CanonicalInputs entry.circuit values inputs)
    (source : entry.circuit.run ctx values = .ok outputs) :
    ∀ input ∈ entry.circuit.inputs,
      ((outputs ++ values) ++ future).lookup input.name = values.lookup input.name := by
  have validated := GenericStateEffectValidation.lower_circuit_validated_source
    state entry plan accepted
  have unshadowed :=
    (GenericStateAliases.validated_output_scope Capabilities.source entry.circuit
      validated).2
  obtain ⟨_, evaluated⟩ := ScalarNormalization.circuit_run_steps ctx
    entry.circuit values outputs source
  have outputNames := ScalarWitnessConstruction.evalOutputs_names ctx values
    entry.circuit.outputs outputs evaluated
  intro input member
  obtain ⟨value, lookup, _⟩ := admitted.complete input member
  have noOutput : input.name ∉ outputs.map Prod.fst := by
    intro present
    rw [outputNames] at present
    obtain ⟨output, outputMember, equal⟩ := List.mem_map.mp present
    have unused := unshadowed output outputMember
    have inputBinding : (input.name, input.ty) ∈
        entry.circuit.inputs.map (fun item => (item.name, item.ty)) :=
      List.mem_map.mpr ⟨input, member, rfl⟩
    have different := List.lookup_eq_none_iff.mp unused
      (input.name, input.ty) inputBinding
    simp [equal] at different
  have outputNone := lookup_none_of_absent_name outputs input.name noOutput
  simp [List.lookup_append, outputNone, lookup]

/-- Original source success constructs the public scalar prefix selected by
the checked production lowerer. The result carries the accepted prefix and
the exact guarded effect extension back to the accepted plan. -/
theorem source_public_prefix (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan) (ctx : EvalContext)
    (values outputs future : EvalEnv) (inputs : Assignment)
    (stack : List Node) (reads : List Cell)
    (accepted : Impact.lower state ep = .ok plan)
    (admitted : CanonicalInputs ep.circuit values inputs)
    (source : ep.circuit.run ctx values = .ok outputs)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ boundaries prefixPlan native cells,
      Impact.lowerWithEffectBoundaries state ep = .ok (plan, boundaries) ∧
      Impact.publicInputPlan ep.circuit.inputs {} = .ok prefixPlan ∧
      Impact.appendEffectsGuardedWithBoundaries state ep.effects ep.effectGuards
        prefixPlan = .ok (plan, boundaries) ∧
      prefixPlan.operations.mapM (GenericStateOps.evalOp ctx
        ((outputs ++ values) ++ future)) = .ok native ∧
      native = cells.flatMap (fun cell => [.push cell false, .popeq cell]) ∧
      run native ⟨stack, reads⟩ = some ⟨stack, reads ++ cells⟩ := by
  obtain ⟨boundaries, prefixPlan, lowerAccepted, prefixAccepted, effectsAccepted⟩ :=
    GenericStateAdmissionPrefix.lower_input_prefix state ep plan accepted
  have compatible := ScalarCellPublicFields.canonical_inputs_scalar_compatible
    ep.circuit values inputs admitted
  obtain ⟨native, cells, _, evaluated, _, shape, checkedRun⟩ :=
    ScalarCellNativePublicPrefix.run_public_prefix_from_candidate ep prefixPlan ctx
      values ((outputs ++ values) ++ future) inputs stack reads admitted compatible
      prefixAccepted
      (source_input_lookup state ep plan ctx values outputs future inputs accepted
        admitted source)
      modulus
  have publicRun : run native ⟨stack, reads⟩ =
      some ⟨stack, reads ++ cells⟩ := by
    rcases checkedRun with ⟨cellsExpected, nativeRun⟩
    rw [cellsExpected]
    exact nativeRun
  refine ⟨boundaries, prefixPlan, native, cells, lowerAccepted,
    prefixAccepted, effectsAccepted, ?_, shape, publicRun⟩
  simpa only [GenericStateOps.evalPlan] using evaluated

end Noctium.Verification.GenericStateConversePublicPrefix
