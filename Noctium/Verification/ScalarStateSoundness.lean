import Noctium.Verification.ScalarSourceFrame
import Noctium.Verification.GenericStateEffectFold
import Noctium.Verification.ScalarEffectReadFacts
import Noctium.Verification.ScalarReadNames
import Noctium.Verification.ScalarImpactOperationMeaning

namespace Noctium.Verification.ScalarStateSoundness
open Backend NativeRelation ScalarNormalization
open GenericStateEffectValidation
  (ScalarStateEffects initialEffectTypeEnv ValidatedEffects scalarReadDestinations)
open GenericStateEffectStep (ScalarOperands)
open GenericStateInputValues (decodeReads scalarType?)
open GenericStateCheckedReadTrace (readMetadata readChunks)

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem lower_disclosure (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state entry = .ok plan) :
    Disclosure.entrypoint entry = .ok () := by
  obtain ⟨_, _, lowered, _, _⟩ :=
    GenericStateAdmissionPrefix.lower_input_prefix state entry plan accepted
  unfold Impact.lowerWithEffectBoundaries at lowered
  simp only [bind_ok] at lowered
  obtain ⟨_, _, checked, disclosure, _⟩ := lowered
  cases checked
  exact disclosure

private theorem public_inputs_scalar (entry : Entrypoint) (values : EvalEnv)
    (witness : Assignment) (inputs : CanonicalInputs entry.circuit values witness) :
    ∀ input ∈ entry.circuit.inputs, Impact.publicInputScalarCompatible input := by
  intro input member
  obtain ⟨value, _, canonical⟩ := inputs.complete input member
  obtain ⟨supported⟩ := GenericStateWriteEvaluation.scalarType_of_canonical canonical
  cases input with
  | mk name ty visibility span =>
    cases supported <;> simp [Impact.publicInputScalarCompatible]

private theorem encoding_clear_unshielded (state : List StateDecl) (initial : LedgerState) :
    GenericStateEncoding.encodeState state
      {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []} =
      GenericStateEncoding.encodeState state initial := by
  unfold GenericStateEncoding.encodeState
  congr 1

private theorem scalar_source_names_clear (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state entry = .ok plan) :
    ∀ name ∈ entry.circuit.inputs.map (·.name) ++ entry.circuit.outputs.map (·.name) ++
      scalarReadDestinations entry.effects,
      name.startsWith "_noctium_" = false := by
  obtain ⟨boundaries, _, lowered, _, _⟩ :=
    GenericStateAdmissionPrefix.lower_input_prefix state entry plan accepted
  have clear := Impact.lowerWithEffectBoundaries_sourceNamesChecked
    state entry plan boundaries lowered
  intro name member
  have sourceMember : name ∈ Impact.sourceNames entry := by
    unfold Impact.sourceNames
    simp only [List.append_assoc, List.mem_append] at member ⊢
    rcases member with input | output | read
    · exact Or.inl input
    · exact Or.inr (Or.inl output)
    · refine Or.inr (Or.inr ?_)
      obtain ⟨effect, present, named⟩ := List.mem_filterMap.mp read
      apply List.mem_flatMap.mpr
      refine ⟨effect, present, ?_⟩
      cases effect <;> simp at named
      all_goals simp [named]
  cases reserved : name.startsWith "_noctium_" with
  | false => rfl
  | true => exact False.elim (List.any_eq_false.mp clear name sourceMember reserved)

private theorem actual_read_name_scope (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state entry = .ok plan)
    (unguarded : entry.effectGuards.all Option.isNone = true) (scalar : ScalarStateEffects entry.effects) :
    let reads := plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)
    reads.Pairwise (fun left right => left.name ≠ right.name) ∧
      ∀ read ∈ reads,
        read.name ∉ entry.circuit.inputs.map (·.name) ++ entry.circuit.outputs.map (·.name) := by
  let ordinal := Impact.publicInputReadCount entry.circuit.inputs
  let reads := plan.reads.drop ordinal
  have clear := scalar_source_names_clear state entry plan accepted
  obtain ⟨distinctDestinations, freshDestinations⟩ :=
    GenericStateEffectValidation.lower_scalar_read_destinations_fresh_unique
      state entry plan accepted scalar
  have destinationsClear : ∀ name ∈ scalarReadDestinations entry.effects,
      name.startsWith "_noctium_" = false := by
    intro name member
    apply clear name
    simp [member]
  obtain ⟨distinctNames, origins⟩ := ScalarReadNames.readChunkNames_fresh_unique
    entry.effects ordinal scalar distinctDestinations destinationsClear
  have metadata := ScalarEffectReadFacts.lower_postPublic_read_metadata state entry plan accepted
    (GenericStateEffectFold.unguarded_read_scope entry unguarded scalar)
  have names : reads.map Impact.Read.name = (readChunks entry.effects ordinal).flatten.map Prod.fst := by
    simpa only [List.map_map, Function.comp_def, readMetadata] using congrArg
      (List.map Prod.fst) metadata
  constructor
  · apply List.Pairwise.of_map (fun read : Impact.Read => read.name)
    · intro left right different
      exact different
    · rw [names]
      exact List.nodup_iff_pairwise_ne.mp distinctNames
  · intro read member inBase
    have nameMember : read.name ∈ (readChunks entry.effects ordinal).flatten.map Prod.fst := by
      rw [← names]
      exact List.mem_map_of_mem member
    rcases origins read.name nameMember with source | ⟨position, _, generated⟩
    · apply freshDestinations read.name source
      simpa only [initialEffectTypeEnv, List.map_append, List.map_map, Function.comp_def]
        using inBase
    · have notReserved := clear read.name (List.mem_append_left _ inBase)
      rw [generated, ScalarReadNames.absenceName_reserved] at notReserved
      cases notReserved

/-- A satisfying emitted scalar relation and checked execution of its exact
Impact plan authenticate the reads and determine the ordered source successor.
The guard schedule may be empty or explicitly mark every effect unguarded.
For admitted normalized fields and unguarded native input requirements, the
public groups are exactly the fields consumed by the checked VM operations.
The final equation retains the original source return checks. -/
theorem lowerEntrypoint_checked_state
    (state : List StateDecl) (entry : Entrypoint) (rewrites : Zkir.Rewrites)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (witness : Assignment) (streams : InputStreams)
    (groups : List (List Scalar)) (json : Lean.Json) (call : NativeRelationJson.ScalarCall)
    (rows : Array Lean.Json) (plan : Impact.Plan)
    (initial : LedgerState) (slots : List NativeState.Slot)
    (native : List NativeState.Op) (final : NativeState.Machine)
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
    (circuitScope : ScalarCircuitAdmission entry.circuit)
    (unguarded : entry.effectGuards.all Option.isNone = true)
    (effectScope : ScalarStateEffects entry.effects)
    (operands : ∀ effect ∈ entry.effects, ScalarOperands effect)
    (plainReads : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      read.components = [] ∧ (scalarType? read.ty).isSome = true ∧
        read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (guardAdmission : ∀ guard ∈ plan.guards, ScalarExpression guard)
    (admittedState : GenericStateEncoding.AdmittedState state initial slots)
    (evaluated : (do
      let outputs ← entry.circuit.outputs.mapM (evalOutput ctx values)
      let reads ← decodeReads
        (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)) witness
      GenericStateOps.evalPlan ctx ((outputs ++ values) ++ reads) plan) = .ok native)
    (checked : NativeState.run native (GenericStateEncoding.initial slots) = some final) :
    ∃ (outputs readValues finalEnv : EvalEnv) (finalTypes : TypeEnv)
      (next : LedgerState) (finalSlots : List NativeState.Slot) (finalReads : List NativeState.Cell),
      entry.circuit.run ctx values = .ok outputs ∧
      decodeReads (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs))
        witness = .ok readValues ∧
      ValidatedEffects state (initialEffectTypeEnv entry) entry.effects finalTypes ∧
      runEffectsWithGuardsAndEnv ctx entry.effects entry.effectGuards (outputs ++ values)
        {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []} =
        .ok (finalEnv, next) ∧
      GenericStateEncoding.encodeState state next = some finalSlots ∧
      final = ⟨[.vector finalSlots], finalReads⟩ ∧
      GenericStatePrefixEnvironment.AgreesOnTypes finalTypes finalEnv
        ((outputs ++ values) ++ readValues) ∧
      ((∀ expected,
        Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
          ∀ input ∈ expected.inputs, input.activityGuard = none) →
        (∀ operation ∈ plan.operations, GenericStateOps.FieldAdmitted operation ∧
          ∀ field ∈ operation.fields, ScalarExpression field ∧
            field.validate Capabilities.scalarFragment
              (plan.typeEnvironment (Passes.pruneEntrypoint entry)) = .ok ()) →
        groups = NativeState.groups native) ∧
      entry.run ctx values initial = (do
        let returned ← Entrypoint.evalReturns ctx entry finalEnv
        pure (outputs ++ returned, next)) := by
  let ep := Passes.pruneEntrypoint entry
  let reset := {initial with
    unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []}
  obtain ⟨distinctReads, separateReads⟩ :=
    actual_read_name_scope state ep plan planAccepted unguarded effectScope
  obtain ⟨frame, outputs, readValues, source, readDecoded, base, typedPlan, readBounds, guards, readFresh, frameAccepted⟩ :=
    ScalarSourceFrame.lowerEntrypoint_sourceFrame_and_guards
      state entry rewrites ctx hash implementation values witness streams groups json call rows
      plan lowered decoded rowsParsed profile satisfies planAccepted inputSchema inputs circuitScope
      plainReads separateReads distinctReads guardAdmission
  have evaluatedOutputs := (circuit_run_steps ctx entry.circuit values outputs source).2
  have planEvaluated :
      GenericStateOps.evalPlan ctx ((outputs ++ values) ++ readValues) plan = .ok native := by
    simpa only [evaluatedOutputs, readDecoded, Bind.bind, Except.bind] using evaluated
  have initialAgreement := GenericStatePrefixEnvironment.initial_from_typed hash witness frame.1
    (initialEffectTypeEnv ep) (outputs ++ values) readValues base
  have scope := GenericStateEffectFold.unguarded_read_scope ep unguarded effectScope
  have readFacts := ScalarEffectReadFacts.lower_read_facts state ep plan (outputs ++ values)
    witness planAccepted scope readFresh
    (fun read member => (plainReads read member).2.2) readBounds
  have encoded : GenericStateEncoding.encodeState state reset = some slots := by
    rw [show GenericStateEncoding.encodeState state reset =
      GenericStateEncoding.encodeState state initial from encoding_clear_unshielded state initial]
    exact admittedState.encoded
  obtain ⟨finalTypes, finalEnv, next, finalSlots, finalReads,
    validated, effects, stateEncoded, layout, agreement⟩ :=
    GenericStateEffectFold.lower_checked_effects ctx state ep plan (outputs ++ values)
      readValues witness reset slots native final planAccepted unguarded effectScope operands
      (public_inputs_scalar entry values witness inputs) readDecoded distinctReads readFacts guards
      initialAgreement encoded admittedState.distinctDeclarations admittedState.slotBound
      implementation.modulus planEvaluated checked
  have sourceEffects :
      runEffectsWithGuardsAndEnv ctx entry.effects entry.effectGuards (outputs ++ values) reset =
        .ok (finalEnv, next) := effects
  have disclosure : Disclosure.entrypoint entry = .ok () := by
    rw [← Passes.pruneEntrypoint_disclosure]
    exact lower_disclosure state ep plan planAccepted
  refine ⟨outputs, readValues, finalEnv, finalTypes, next, finalSlots, finalReads, source,
    readDecoded, validated, sourceEffects, stateEncoded, layout, agreement, ?_, ?_⟩
  · intro inputGuards fields
    obtain ⟨_, expected, _, expectedAccepted, payloads⟩ :=
      RangeDedupAcceptedEntrypoint.lowerEntrypoint_scalarCall_impactPayloads
        rewrites lowered decoded rowsParsed profile inputSchema inputGuards
    obtain ⟨requirementsExpected, acceptedRequirements, requirements⟩ :=
      RangeDedupAcceptedEntrypoint.lowerEntrypoint_scalarCall_sourceRequirements
        rewrites lowered decoded rowsParsed profile inputSchema
    have sameExpected := Except.ok.inj (acceptedRequirements.symm.trans expectedAccepted)
    subst requirementsExpected
    obtain ⟨assertions, bounds, _⟩ := requirements satisfies
    have scalarReads := ScalarSourceFrame.plain_scalar_read_scope ep plan (fun read member =>
      ⟨(plainReads read member).1, (plainReads read member).2.1⟩)
    obtain ⟨collectedFrame, collectedBounds, collectedAssertions, normalized, collected,
      boundMembers, assertionMembers⟩ := GenericStateCircuitParts.expectedEntrypoint_operations
        state ep expected plan planAccepted expectedAccepted scalarReads
    have sameFrame := Except.ok.inj (normalized.symm.trans frameAccepted)
    subst collectedFrame
    have nativeGroups := ScalarImpactOperationMeaning.collectOperations_scalar_fields
      ctx hash implementation witness frame.1 ((outputs ++ values) ++ readValues)
      (plan.typeEnvironment ep) typedPlan ep.span plan.operations native frame.2.1
      expected.groups collectedBounds collectedAssertions
      (fun operation member => (fields operation member).1)
      (fun operation member expression present => (fields operation member).2 expression present |>.1)
      (fun operation member expression present => (fields operation member).2 expression present |>.2)
      (fun bound member => bounds bound (boundMembers bound member))
      (fun term member => assertions term (assertionMembers term member)) collected planEvaluated
    have exactPayloads := (payloads satisfies).symm.trans nativeGroups
    have values := congrArg (List.map (List.map (fun value : Option Scalar => value.getD zero)))
      exactPayloads
    simpa [List.map_map, Function.comp_def] using values
  · unfold Entrypoint.run
    simp only [disclosure, source, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [show runEffectsWithGuardsAndEnv ctx entry.effects entry.effectGuards (outputs ++ values)
          {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []} =
        .ok (finalEnv, next) from sourceEffects]

end Noctium.Verification.ScalarStateSoundness
