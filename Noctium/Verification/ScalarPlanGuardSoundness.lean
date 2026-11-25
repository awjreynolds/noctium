import Noctium.Verification.ScalarCircuit
import Noctium.Verification.GenericStateCheckedReadDecode
import Noctium.Verification.GenericStateEffectValidation
import Noctium.Verification.RangeDedupAcceptedEntrypoint

namespace Noctium.Verification.ScalarPlanGuardSoundness
open Backend NativeRelation ScalarNormalization Backend.Native
open GenericStateCircuitParts GenericStateInputValues

private theorem runConstraints_all (ctx : EvalContext) (values : EvalEnv)
    (conditions : List (Expr .bool))
    (success : runConstraints ctx values conditions = .ok ()) :
    ∀ condition ∈ conditions, condition.eval ctx values = .ok true := by
  induction conditions with
  | nil => simp
  | cons condition rest ih =>
    cases checked : condition.eval ctx values with
    | error message => simp [runConstraints, checked] at success
    | ok value =>
      cases value with
      | false => simp [runConstraints, checked] at success
      | true =>
        have tail : runConstraints ctx values rest = .ok () := by
          simpa [runConstraints, checked] using success
        intro item member
        rcases List.mem_cons.mp member with equal | member
        · simpa [equal] using checked
        · exact ih tail item member

/-- The expected native bounds and assertions imply truth of each source
guard under the same typed candidate environment used by normalization. -/
theorem checked_plan_guard_truth (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (witness : Assignment)
    (types : TypeEnv) (aliases : AliasEnvironment) (values : EvalEnv)
    (plan : Impact.Plan) (span : SourceSpan) (expected : Expected) (guards : List Normalized)
    (environment : TypedEnvironment hash witness aliases values types)
    (valid : validateConstraints Capabilities.crypto types span plan.guards = .ok ())
    (admitted : ∀ guard ∈ plan.guards, ScalarExpression guard)
    (normal : plan.guards.mapM (normalize aliases) = .ok guards)
    (guardBounds : ∀ requirement ∈ guards.flatMap (·.bounds), requirement ∈ expected.bounds)
    (guardAssertions : ∀ term ∈ guards.flatMap (fun result => result.assertions ++ [result.term]),
      term ∈ expected.assertions)
    (bounds : ∀ requirement ∈ expected.bounds,
      ∃ value, interpret hash witness requirement.1 = some value ∧ value.val ≤ requirement.2)
    (assertions : ∀ term ∈ expected.assertions, interpret hash witness term = some one) :
    ∀ guard ∈ plan.guards, guard.eval ctx values = .ok true := by
  apply runConstraints_all
  exact constraints_sound ctx hash implementation witness types aliases values environment
    span plan.guards guards valid normal
    (fun requirement member => bounds requirement (guardBounds requirement member))
    (fun term member => assertions term (guardAssertions term member)) admitted

/-- A scalar decoder type uses the corresponding source alias representation. -/
theorem scalarType_shape (ty : Ty) (supported : (scalarType? ty).isSome = true) :
    scalarAliasReadType ty := by
  cases ty <;> simp [scalarAliasReadType, scalarType?] at supported ⊢

/-- Plain reads contribute exactly one scalar descriptor each. -/
theorem plain_reads_scalarReads (reads : List Impact.Read)
    (plain : ∀ read ∈ reads, read.components = []) :
    reads.flatMap Impact.Read.scalarReads = reads := by
  have singletons : reads.map Impact.Read.scalarReads = reads.map (fun read => [read]) := by
    apply List.map_congr_left
    intro read member
    simp [Impact.Read.scalarReads, plain read member]
  rw [List.flatMap_def, singletons, ← List.flatMap_def, List.flatMap_singleton']

private theorem scalar_plan_types (entry : Entrypoint) (plan : Impact.Plan)
    (admitted : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      read.components = [] ∧ (scalarType? read.ty).isSome = true) :
    plan.typeEnvironment entry =
      GenericStateEffectValidation.initialEffectTypeEnv entry ++
        readTypes (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)) := by
  let reads := plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)
  have typeLists : reads.map Impact.Read.typeBindings = reads.map (fun read => [(read.name, read.ty)]) := by
    apply List.map_congr_left
    intro read member
    obtain ⟨plain, supported⟩ := admitted read member
    have simpleReads : read.scalarReads = [read] := by
      simp [Impact.Read.scalarReads, plain]
    have singleton := GenericStateCheckedReadDecode.supported_plain_read_bindings read plain supported
    unfold Impact.Read.typeBindings
    rw [simpleReads, List.flatMap_singleton, singleton]
    rcases scalarType_shape read.ty supported with native | boolean | ⟨width, unsigned⟩
    · simp [native]
    · simp [boolean]
    · simp [unsigned]
  have suffix : reads.flatMap Impact.Read.typeBindings = readTypes reads := by
    rw [List.flatMap_def, typeLists]
    simpa only [readTypes, List.flatMap_def] using
      (List.map_eq_flatMap (f := fun read : Impact.Read => (read.name, read.ty)) (l := reads)).symm
  simpa only [Impact.Plan.typeEnvironment, GenericStateEffectValidation.initialEffectTypeEnv,
    List.append_assoc, reads] using congrArg
      (fun suffix => GenericStateEffectValidation.initialEffectTypeEnv entry ++ suffix) suffix

/-- Recover the typed read frame and check the plan guards using the
requirements proved for its accepted expected relation. -/
theorem plan_guards_sound_of_requirements
    (state : List StateDecl) (entry : Entrypoint)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (witness : Assignment) (plan : Impact.Plan) (expected : Expected)
    (frame : OutputFrame) (base : EvalEnv)
    (planAccepted : Impact.lower state entry = .ok plan)
    (expectedAccepted : Native.expectedEntrypoint state entry = .ok expected)
    (frameAccepted : normalizeOutputs (entrypointSeedAliases entry plan)
      entry.circuit.outputs = .ok frame)
    (baseEnvironment : TypedEnvironment hash witness frame.1 base
      (GenericStateEffectValidation.initialEffectTypeEnv entry))
    (readAdmitted : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      read.components = [] ∧ (scalarType? read.ty).isSome = true ∧
        read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (readFresh : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      base.lookup read.name = none ∧
        (GenericStateEffectValidation.initialEffectTypeEnv entry).lookup read.name = none)
    (readDistinct : (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).Pairwise
      (fun left right => left.name ≠ right.name))
    (readAliases : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      frame.1.lookup read.name = some (.input ("%input_" ++ read.name)))
    (admitted : ∀ guard ∈ plan.guards, ScalarExpression guard)
    (assertions : ∀ term ∈ expected.assertions, interpret hash witness term = some one)
    (bounds : ∀ requirement ∈ expected.bounds,
      ∃ value, interpret hash witness requirement.1 = some value ∧ value.val ≤ requirement.2)
    (inputBounds : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      requirement.ty.isForeign = false → requirement.canonicalJubjubScalar = false →
      (witness requirement.identifier).val ≤ Native.sourceMaximum requirement.ty) :
    let reads := plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)
    ∃ readValues, decodeReads reads witness = .ok readValues ∧
      TypedEnvironment hash witness frame.1 (base ++ readValues) (plan.typeEnvironment entry) ∧
      (∀ read ∈ reads,
        (witness ("%input_" ++ read.name)).val ≤ Native.sourceMaximum read.ty) ∧
      (∀ guard ∈ plan.guards, guard.eval ctx (base ++ readValues) = .ok true) := by
  let reads := plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)
  have scalarReads : ∀ read ∈ reads, scalarAliasReadType read.ty := by
    intro read member
    exact scalarType_shape read.ty (readAdmitted read member).2.1
  have readBounds : ∀ read ∈ reads,
      (witness ("%input_" ++ read.name)).val ≤ Native.sourceMaximum read.ty := by
    intro read member
    obtain ⟨plain, supported, _⟩ := readAdmitted read member
    have singleton := GenericStateCheckedReadDecode.supported_plain_read_bindings read plain supported
    exact GenericStateCheckedReadDecode.accepted_scalarRead_inputBound_of_requirements
      state entry expected expectedAccepted plan planAccepted read read.name read.ty member singleton
      (scalarReads read member) inputBounds
  obtain ⟨readValues, readDecoded, environment⟩ :=
    GenericStateCandidateDecode.appendSupportedReads_existing reads hash witness frame.1 base
      (GenericStateEffectValidation.initialEffectTypeEnv entry) baseEnvironment
      (fun read member => (readAdmitted read member).2.1) readFresh readDistinct readAliases
      (fun read member => (readAdmitted read member).2.2) readBounds
  have shape := scalar_plan_types entry plan (fun read member =>
    ⟨(readAdmitted read member).1, (readAdmitted read member).2.1⟩)
  change TypedEnvironment hash witness frame.1 (base ++ readValues)
    (GenericStateEffectValidation.initialEffectTypeEnv entry ++
      readTypes (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs))) at environment
  rw [← shape] at environment
  have flattened := plain_reads_scalarReads reads (fun read member => (readAdmitted read member).1)
  obtain ⟨actualFrame, guards, actualFrameAccepted, normalized, guardAssertions, guardBounds⟩ :=
    expectedEntrypoint_guards state entry expected plan planAccepted expectedAccepted
      (by
        change ∀ read ∈ reads.flatMap Impact.Read.scalarReads, scalarAliasReadType read.ty
        rw [flattened]
        exact scalarReads)
  have frameEq : actualFrame = frame :=
    Except.ok.inj (actualFrameAccepted.symm.trans frameAccepted)
  subst actualFrame
  have guardsValid := Impact.lower_guards_validate state entry plan planAccepted
  refine ⟨readValues, readDecoded, environment, readBounds, ?_⟩
  exact checked_plan_guard_truth ctx hash implementation witness
    (plan.typeEnvironment entry) frame.1 (base ++ readValues) plan entry.span expected guards
    environment guardsValid admitted normalized guardBounds guardAssertions bounds assertions

/-- A satisfying assignment of the exact emitted scalar call supplies bounded
candidates for the accepted plan's reads and proves its guard assertions under
the corresponding typed evaluation frame. The initial source input/output
frame is supplied by its own semantic preservation proof. -/
theorem lowerEntrypoint_guards_sound
    (state : List StateDecl) (entry : Entrypoint) (rewrites : Zkir.Rewrites)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (witness : Assignment) (streams : InputStreams) (groups : List (List Scalar))
    (json : Lean.Json) (call : NativeRelationJson.ScalarCall) (rows : Array Lean.Json)
    (plan : Impact.Plan) (expected : Expected) (frame : OutputFrame) (base : EvalEnv)
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (decoded : NativeRelationJson.decodeScalarCall json = .ok call)
    (rowsParsed : Native.arrayField json "instructions" = .ok rows)
    (profile : ScalarValidationOpcodeProfile.checkedScalarOpcodeProfile
      rows.toList.zipIdx call.body.instructions = true)
    (satisfies : CircuitSatisfies hash call.body streams witness groups)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (expectedAccepted :
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected)
    (inputSchema : ∀ required ∈ expected.rawInputs ++ expected.inputs, required.ty.isForeign = false)
    (frameAccepted : normalizeOutputs (entrypointSeedAliases (Passes.pruneEntrypoint entry) plan)
      (Passes.pruneEntrypoint entry).circuit.outputs = .ok frame)
    (baseEnvironment : TypedEnvironment hash witness frame.1 base
      (GenericStateEffectValidation.initialEffectTypeEnv (Passes.pruneEntrypoint entry)))
    (readAdmitted : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      read.components = [] ∧ (scalarType? read.ty).isSome = true ∧
        read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (readFresh : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      base.lookup read.name = none ∧
        (GenericStateEffectValidation.initialEffectTypeEnv
          (Passes.pruneEntrypoint entry)).lookup read.name = none)
    (readDistinct : (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).Pairwise
      (fun left right => left.name ≠ right.name))
    (readAliases : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      frame.1.lookup read.name = some (.input ("%input_" ++ read.name)))
    (admitted : ∀ guard ∈ plan.guards, ScalarExpression guard) :
    let reads := plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)
    ∃ readValues, decodeReads reads witness = .ok readValues ∧
      TypedEnvironment hash witness frame.1 (base ++ readValues)
        (plan.typeEnvironment (Passes.pruneEntrypoint entry)) ∧
      (∀ read ∈ reads,
        (witness ("%input_" ++ read.name)).val ≤ Native.sourceMaximum read.ty) ∧
      (∀ guard ∈ plan.guards, guard.eval ctx (base ++ readValues) = .ok true) := by
  let ep := Passes.pruneEntrypoint entry
  have schemas : ∀ specimen, Native.expectedEntrypoint state ep = .ok specimen →
      ∀ required ∈ specimen.rawInputs ++ specimen.inputs, required.ty.isForeign = false := by
    intro specimen accepted
    rw [expectedAccepted] at accepted
    cases accepted
    exact inputSchema
  obtain ⟨actualExpected, actualExpectedAccepted, facts⟩ :=
    RangeDedupAcceptedEntrypoint.lowerEntrypoint_scalarCall_sourceRequirements
      rewrites lowered decoded rowsParsed profile schemas
  have expectedEq : actualExpected = expected :=
    Except.ok.inj (actualExpectedAccepted.symm.trans expectedAccepted)
  subst actualExpected
  obtain ⟨assertions, bounds, inputBounds⟩ := facts satisfies
  exact plan_guards_sound_of_requirements state ep ctx hash implementation witness plan
    expected frame base planAccepted expectedAccepted frameAccepted baseEnvironment
    readAdmitted readFresh readDistinct readAliases admitted assertions bounds inputBounds

end Noctium.Verification.ScalarPlanGuardSoundness
