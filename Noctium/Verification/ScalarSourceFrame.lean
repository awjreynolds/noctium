import Noctium.Verification.GenericStateCaps
import Noctium.Verification.GenericStateEffectValidation
import Noctium.Verification.RangeDedupAcceptedEntrypoint
import Noctium.Verification.ScalarEntrypointSeedFrame
import Noctium.Verification.ScalarOutputFrame
import Noctium.Verification.ScalarPlanGuardSoundness

namespace Noctium.Verification.ScalarSourceFrame
open Backend Backend.Native NativeRelation ScalarNormalization GenericStateCircuitParts
open GenericStateEffectValidation (initialEffectTypeEnv)
open GenericStateInputValues (decodeReads scalarType?)

/-- Build the typed source frame from the accepted expected relation and its
checked requirements. This proof establishes circuit success from the accepted
plan and actual expected assertions and bounds, without assuming a successful
source run. -/
theorem sourceFrame_of_requirements
    (state : List StateDecl) (ep : Entrypoint) (expected : Expected)
    (plan : Impact.Plan) (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (values : EvalEnv)
    (assignment : Assignment)
    (planAccepted : Impact.lower state ep = .ok plan)
    (expectedAccepted : Native.expectedEntrypoint state ep = .ok expected)
    (scalarReads : ∀ read ∈
      (plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)).flatMap
        Impact.Read.scalarReads, scalarAliasReadType read.ty)
    (inputs : CanonicalInputs ep.circuit values assignment)
    (admitted : ScalarCircuitAdmission ep.circuit)
    (assertions : ∀ term ∈ expected.assertions,
      interpret hash assignment term = some one)
    (bounds : ∀ requirement ∈ expected.bounds,
      ∃ value, interpret hash assignment requirement.1 = some value ∧
        value.val ≤ requirement.2) :
    ∃ frame result,
      normalizeOutputs (entrypointSeedAliases ep plan) ep.circuit.outputs = .ok frame ∧
      ep.circuit.run ctx values = .ok result ∧
      result.map Prod.fst = ep.circuit.outputs.map (·.name) ∧
      TypedEnvironment hash assignment frame.1 (result ++ values)
        (initialEffectTypeEnv ep) := by
  obtain ⟨frame, conditions, normalizedOutputs, normalizedConditions, outputBounds,
    outputAssertions, conditionBounds, conditionAssertions⟩ :=
    expectedEntrypoint_sourceCircuitRequirements state ep expected plan planAccepted
      expectedAccepted scalarReads
  have checkedSource := GenericStateEffectValidation.lower_circuit_validated_source
    state ep plan planAccepted
  have checkedCircuit : ep.circuit.validate Capabilities.crypto = .ok () := by
    rwa [GenericStateCaps.circuit_validate_source_crypto] at checkedSource
  have runtimeValidation : ep.circuit.validate (evaluationCapabilities ctx) = .ok () := by
    simpa [evaluationCapabilities, Capabilities.crypto, implementation.modulus] using checkedCircuit
  obtain ⟨conditionValidation, outputValidation⟩ :=
    circuit_validation_parts ep.circuit checkedCircuit
  obtain ⟨distinctOutputs, unshadowed⟩ :=
    GenericStateAliases.validated_output_scope Capabilities.crypto ep.circuit checkedCircuit
  have unused := GenericStateAliases.canonicalInputs_output_unused_of_scope ep.circuit
    values assignment inputs unshadowed
  have seed := ScalarEntrypointSeedFrame.entrypointSeedAliases_typedEnvironment
    ep plan hash values assignment inputs
  obtain ⟨result, outputs, outputNames, inputsTyped, effectsTyped⟩ :=
    ScalarOutputFrame.normalizeOutputs_source_frame ctx hash implementation assignment
      (entrypointSeedAliases ep plan) _ values ep.circuit.outputs frame seed distinctOutputs
      (fun output member => by
        obtain ⟨_, scope⟩ := admitted.outputs output member
        exact scope)
      outputValidation unused unshadowed normalizedOutputs
      (fun requirement member => bounds requirement (outputBounds requirement member))
      (fun term member => assertions term (outputAssertions term member))
  have constraints := constraints_sound ctx hash implementation assignment _ frame.1 values
    inputsTyped ep.circuit.span ep.circuit.constraints conditions conditionValidation
    normalizedConditions
    (fun requirement member => bounds requirement (conditionBounds requirement member))
    (fun term member => assertions term (conditionAssertions term member))
    admitted.constraints
  have source := circuit_run_preflight ctx implementation.modulus ep.circuit values result
    assignment inputs runtimeValidation constraints outputs
  exact ⟨frame, result, normalizedOutputs,
    source, outputNames, effectsTyped⟩

/-- A satisfying witness for the exact emitted scalar call forces the source
circuit to succeed and supplies its typed input/output frame for state
effects. Canonical source inputs bind the declared values to the witness. -/
theorem lowerEntrypoint_sourceFrame
    (state : List StateDecl) (entry : Entrypoint) (rewrites : Zkir.Rewrites)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (witness : Assignment) (streams : InputStreams)
    (groups : List (List Scalar)) (json : Lean.Json) (call : NativeRelationJson.ScalarCall)
    (rows : Array Lean.Json) (plan : Impact.Plan)
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (decoded : NativeRelationJson.decodeScalarCall json = .ok call)
    (rowsParsed : Native.arrayField json "instructions" = .ok rows)
    (profile : ScalarValidationOpcodeProfile.checkedScalarOpcodeProfile
      rows.toList.zipIdx call.body.instructions = true)
    (satisfies : CircuitSatisfies hash call.body streams witness groups)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (inputSchema : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
        ∀ required ∈ expected.rawInputs ++ expected.inputs, required.ty.isForeign = false)
    (scalarReads : ∀ read ∈
      (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).flatMap
        Impact.Read.scalarReads, scalarAliasReadType read.ty)
    (inputs : CanonicalInputs entry.circuit values witness)
    (admitted : ScalarCircuitAdmission entry.circuit) :
    ∃ expected frame result,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      normalizeOutputs (entrypointSeedAliases (Passes.pruneEntrypoint entry) plan)
        entry.circuit.outputs = .ok frame ∧
      entry.circuit.run ctx values = .ok result ∧
      result.map Prod.fst = entry.circuit.outputs.map (·.name) ∧
      TypedEnvironment hash witness frame.1 (result ++ values)
        (initialEffectTypeEnv (Passes.pruneEntrypoint entry)) := by
  let ep := Passes.pruneEntrypoint entry
  obtain ⟨expected, expectedAccepted, requirements⟩ :=
    RangeDedupAcceptedEntrypoint.lowerEntrypoint_scalarCall_sourceRequirements
      rewrites lowered decoded rowsParsed profile inputSchema
  obtain ⟨assertions, bounds, _⟩ := requirements satisfies
  have canonical : CanonicalInputs ep.circuit values witness :=
    ⟨inputs.unique, inputs.declared, inputs.complete, inputs.binding⟩
  obtain ⟨frame, result, normalizedOutputs, source, outputNames, effectsTyped⟩ :=
    sourceFrame_of_requirements state ep expected plan ctx hash implementation values witness
      planAccepted expectedAccepted scalarReads canonical (admitted.pruneCircuit entry.circuit)
      assertions bounds
  exact ⟨expected, frame, result, expectedAccepted, normalizedOutputs,
    by simpa only [ep, Passes.pruneEntrypoint, Passes.pruneCircuit_run] using source,
    outputNames, effectsTyped⟩

private theorem lookup_none_of_name_not_mem (items : List (String × α))
    (name : String) (absent : name ∉ items.map Prod.fst) :
    items.lookup name = none := by
  apply List.lookup_eq_none_iff.mpr
  intro pair member
  have different : name ≠ pair.1 := by
    intro same
    exact absent (List.mem_map.mpr ⟨pair, member, same.symm⟩)
  simp [different]

private theorem scalar_shape (ty : Ty) (supported : (scalarType? ty).isSome = true) :
    scalarAliasReadType ty := by
  cases ty <;> simp [scalarAliasReadType, scalarType?] at supported ⊢

/-- Plain supported reads retain their scalar descriptor after flattening. -/
theorem plain_scalar_read_scope (entry : Entrypoint) (plan : Impact.Plan)
    (plain : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      read.components = [] ∧ (scalarType? read.ty).isSome = true) :
    ∀ read ∈ (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).flatMap
      Impact.Read.scalarReads, scalarAliasReadType read.ty := by
  intro read member
  obtain ⟨original, present, inOne⟩ := List.mem_flatMap.mp member
  have supported := plain original present
  have same : read = original := by simpa [Impact.Read.scalarReads, supported.1] using inOne
  rw [same]
  exact scalar_shape original.ty supported.2

/-- Ledger reads are fresh in the reconstructed base values and keep their raw
input aliases in the normalized output frame. -/
theorem candidate_read_frame_lookups (ep : Entrypoint) (plan : Impact.Plan)
    (frame : OutputFrame) (result values : EvalEnv) (witness : Assignment)
    (inputs : CanonicalInputs ep.circuit values witness)
    (frameAccepted : normalizeOutputs (entrypointSeedAliases ep plan)
      ep.circuit.outputs = .ok frame)
    (resultNames : result.map Prod.fst = ep.circuit.outputs.map (·.name))
    (plainReads : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs),
      read.components = [] ∧ (scalarType? read.ty).isSome = true)
    (separateReads : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs),
      read.name ∉ ep.circuit.inputs.map (·.name) ++ ep.circuit.outputs.map (·.name)) :
    let reads := plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)
    (∀ read ∈ reads,
      (result ++ values).lookup read.name = none ∧
        (initialEffectTypeEnv ep).lookup read.name = none) ∧
    (∀ read ∈ reads, frame.1.lookup read.name = some (.input ("%input_" ++ read.name))) := by
  let reads := plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)
  have readFresh : ∀ read ∈ reads,
      (result ++ values).lookup read.name = none ∧
        (initialEffectTypeEnv ep).lookup read.name = none := by
    intro read member
    have absent := separateReads read member
    have resultAbsent : read.name ∉ result.map Prod.fst := by
      rw [resultNames]
      exact fun present => absent (List.mem_append_right _ present)
    have valuesAbsent : read.name ∉ values.map Prod.fst := by
      intro member
      obtain ⟨pair, pairMember, same⟩ := List.mem_map.mp member
      obtain ⟨input, inputMember, inputName⟩ := inputs.declared pair.1 pair.2 pairMember
      exact absent (List.mem_append_left _ (List.mem_map.mpr
        ⟨input, inputMember, inputName.trans same⟩))
    constructor
    · simp only [List.lookup_append, lookup_none_of_name_not_mem _ _ resultAbsent,
        lookup_none_of_name_not_mem _ _ valuesAbsent, Option.none_or]
    · apply lookup_none_of_name_not_mem
      simpa only [initialEffectTypeEnv, List.map_append, List.map_map, Function.comp_def]
        using absent
  have singleton : ∀ read ∈ reads, read.bindings = [(read.name, read.ty)] := by
    intro read member
    obtain ⟨plain, supported⟩ := plainReads read member
    exact GenericStateCheckedReadDecode.supported_plain_read_bindings read plain supported
  have readAliases : ∀ read ∈ reads,
      frame.1.lookup read.name = some (.input ("%input_" ++ read.name)) := by
    exact ScalarEntrypointSeedFrame.normalized_read_lookup
      ep plan frame values witness inputs frameAccepted singleton separateReads
  exact ⟨readFresh, readAliases⟩

/-- Compose circuit execution with checked read decoding and plan assertions.
Read name separation and descriptor admission are stated in terms of the
actual plan. Checked native state execution authenticates the read values. -/
theorem lowerEntrypoint_sourceFrame_and_guards
    (state : List StateDecl) (entry : Entrypoint) (rewrites : Zkir.Rewrites)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (witness : Assignment) (streams : InputStreams)
    (groups : List (List Scalar)) (json : Lean.Json) (call : NativeRelationJson.ScalarCall)
    (rows : Array Lean.Json) (plan : Impact.Plan)
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (decoded : NativeRelationJson.decodeScalarCall json = .ok call)
    (rowsParsed : Native.arrayField json "instructions" = .ok rows)
    (profile : ScalarValidationOpcodeProfile.checkedScalarOpcodeProfile
      rows.toList.zipIdx call.body.instructions = true)
    (satisfies : CircuitSatisfies hash call.body streams witness groups)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (inputSchema : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
        ∀ required ∈ expected.rawInputs ++ expected.inputs, required.ty.isForeign = false)
    (inputs : CanonicalInputs entry.circuit values witness)
    (admitted : ScalarCircuitAdmission entry.circuit)
    (plainReads : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      read.components = [] ∧ (scalarType? read.ty).isSome = true ∧
        read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (separateReads : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      read.name ∉ entry.circuit.inputs.map (·.name) ++ entry.circuit.outputs.map (·.name))
    (distinctReads : (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).Pairwise
      (fun left right => left.name ≠ right.name))
    (guardAdmission : ∀ guard ∈ plan.guards, ScalarExpression guard) :
    let reads := plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)
    ∃ (frame : OutputFrame) (result readValues : EvalEnv),
      entry.circuit.run ctx values = .ok result ∧
      decodeReads reads witness = .ok readValues ∧
      TypedEnvironment hash witness frame.1 (result ++ values)
        (initialEffectTypeEnv (Passes.pruneEntrypoint entry)) ∧
      TypedEnvironment hash witness frame.1 ((result ++ values) ++ readValues)
        (plan.typeEnvironment (Passes.pruneEntrypoint entry)) ∧
      (∀ read ∈ reads,
        (witness ("%input_" ++ read.name)).val ≤ Native.sourceMaximum read.ty) ∧
      (∀ guard ∈ plan.guards, guard.eval ctx ((result ++ values) ++ readValues) = .ok true) ∧
      (∀ read ∈ reads, (result ++ values).lookup read.name = none) ∧
      normalizeOutputs (entrypointSeedAliases (Passes.pruneEntrypoint entry) plan)
        entry.circuit.outputs = .ok frame := by
  let ep := Passes.pruneEntrypoint entry
  let reads := plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)
  have scalarReads := plain_scalar_read_scope entry plan (fun read member =>
    ⟨(plainReads read member).1, (plainReads read member).2.1⟩)
  obtain ⟨expected, frame, result, expectedAccepted, frameAccepted, source, resultNames, base⟩ :=
    lowerEntrypoint_sourceFrame state entry rewrites ctx hash implementation
      values witness streams groups json call rows plan lowered decoded rowsParsed profile
      satisfies planAccepted inputSchema scalarReads inputs admitted
  have canonical : CanonicalInputs ep.circuit values witness :=
    ⟨inputs.unique, inputs.declared, inputs.complete, inputs.binding⟩
  obtain ⟨readFresh, readAliases⟩ := candidate_read_frame_lookups ep plan frame result values
    witness canonical frameAccepted resultNames
    (fun read member => ⟨(plainReads read member).1, (plainReads read member).2.1⟩)
    separateReads
  obtain ⟨readValues, readDecoded, environment, bounds, guards⟩ :=
    ScalarPlanGuardSoundness.lowerEntrypoint_guards_sound
      state entry rewrites ctx hash implementation witness streams groups json call rows
      plan expected frame (result ++ values) lowered decoded rowsParsed profile satisfies
      planAccepted expectedAccepted (inputSchema _ expectedAccepted) frameAccepted base
      plainReads readFresh distinctReads readAliases guardAdmission
  exact ⟨frame, result, readValues, source, readDecoded, base, environment, bounds, guards,
    (fun read member => (readFresh read member).1), frameAccepted⟩

end Noctium.Verification.ScalarSourceFrame
