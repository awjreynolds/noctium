import Noctium.Verification.GuardedScalarWitnessAssembly
import Noctium.Verification.GuardedScalarWitnessCheck
import Noctium.Verification.GuardedStatementConsumption
import Noctium.Verification.GuardedPlanExecution
import Noctium.Verification.ImpactStatementScalar
import Noctium.Verification.ScalarSourceReadWitness
import Noctium.Verification.ScalarValidationRawSeedMeaning
import Noctium.Verification.GuardedZkirRequirements
import Noctium.Verification.ScalarGuardedReadAdmission
import Noctium.Verification.GenericStateCheckedReadDecode
import Noctium.Verification.ScalarLedgerScalarSchema

namespace Noctium.Verification.GuardedScalarWitness

open Lean Backend NativeRelation
open GuardedStatementConsumption (Inputs)
open ScalarCellWitnessReadSeed (seedReadValues)
open ScalarNormalization

/-- An assignment to the exact guarded scalar rows accepted by the artifact
checker. The ordinary constraints and both transcript streams are checked
independently of assignment construction. -/
structure Checked (hash : Hash) (seed : Assignment)
    (bytes : ArtifactBytes.Bytes) (expected : Json) (inputs : Inputs) where
  assignment : Assignment
  view : GuardedZkirArtifact.View
  observations : List GuardedImpactObservation.Observation
  inputFrame : ∀ name ∈ view.header.arguments ++ GuardedScalarWitnessAssembly.inputOutputs view.rows,
    assignment name = seed name
  pinned : GuardedZkirArtifact.decodeView expected = .ok view
  producerJson : (ArtifactBytes.parse bytes).map Json.compress = .ok expected.compress
  artifact : GuardedZkirArtifact.check bytes expected = .ok view.rows
  ordinary : ∀ row ∈ view.rows, GuardedImpactTranscript.ordinaryHolds hash assignment row
  consumed : GuardedStatementConsumption.consumeArtifact bytes assignment inputs = some observations

/-- Build the scalar temporaries from the emitted producer rows. The guarded
artifact decoder and transcript checks keep inactive reads and Impact groups
in their original positions. -/
def build (hash : Hash) (seed : Assignment) (bytes : ArtifactBytes.Bytes)
    (expected : Json) (inputs : Inputs) :
    Except String (Checked hash seed bytes expected inputs) := do
  match parsed : ArtifactBytes.parse bytes with
  | .error reason => throw reason
  | .ok json =>
    -- Both copy and constrain_eq decode to equality. Assembly also needs the
    -- original producer tags to distinguish definitions from constraints.
    if same : json.compress = expected.compress then
      match artifact : GuardedZkirArtifact.check bytes expected with
      | .error reason => throw reason
      | .ok rows =>
        match pinned : GuardedZkirArtifact.decodeView expected with
        | .error reason => throw reason
        | .ok view =>
          let rawRows ← Native.arrayField expected "instructions"
          let ⟨assignment, frame⟩ ← GuardedScalarWitnessAssembly.assemble
            hash seed view.header.arguments rawRows.toList view.rows
          if ordinary : GuardedScalarWitnessCheck.check hash assignment view.rows = true then
            match consumed : GuardedStatementConsumption.consumeArtifact bytes assignment inputs with
            | none => throw "guarded witness does not consume the supplied transcript"
            | some observations =>
              have sameRows := GuardedZkirArtifact.check_pinned_rows artifact pinned
              pure ⟨assignment, view, observations, frame, pinned, by simp [parsed, same, Except.map],
                by simpa only [sameRows] using artifact,
                GuardedScalarWitnessCheck.check_sound hash assignment view.rows ordinary, consumed⟩
          else
            throw "guarded witness does not satisfy the emitted scalar constraints"
    else
      throw "guarded artifact JSON differs from the emitted program"

/-- With the ordered producer scope established, the executable builder
reconstructs any satisfying assignment's values on the observed names and
consumes the same exact-byte transcript. -/
theorem build_of_scope (hash : Hash) (seed target : Assignment) (bytes : ArtifactBytes.Bytes)
    (expected : Json) (transcript : Inputs) (view : GuardedZkirArtifact.View)
    (rawRows : Array Json) (finalNames : List String)
    (parsed : (ArtifactBytes.parse bytes).map Json.compress = .ok expected.compress)
    (checked : GuardedZkirArtifact.check bytes expected = .ok view.rows)
    (pinned : GuardedZkirArtifact.decodeView expected = .ok view)
    (raw : Native.arrayField expected "instructions" = .ok rawRows)
    (validArgs : view.header.arguments.all NativeRelationJson.validIdentifier = true)
    (distinctInputs :
      let names := view.header.arguments ++ GuardedScalarWitnessAssembly.inputOutputs view.rows
      names.eraseDups.length = names.length)
    (scope : GuardedScalarWitnessAssembly.Scope
      (view.header.arguments ++ GuardedScalarWitnessAssembly.inputOutputs view.rows)
      rawRows.toList view.rows finalNames)
    (inputAgreement : ∀ name ∈
      view.header.arguments ++ GuardedScalarWitnessAssembly.inputOutputs view.rows,
      seed name = target name)
    (holds : ∀ instruction, GuardedScalarRows.Row.strict instruction ∈ view.rows →
      Instruction.Holds hash target instruction)
    (widths : ∀ left right width destination,
      GuardedScalarRows.Row.strict (.lessThan left right width destination) ∈ view.rows →
      (left.read target).val < 2 ^ width ∧ (right.read target).val < 2 ^ width)
    (observations : List GuardedImpactObservation.Observation)
    (targetConsumed : GuardedStatementConsumption.consumeArtifact bytes target transcript =
      some observations) :
    ∃ built, build hash seed bytes expected transcript = .ok built ∧
      built.observations = observations ∧
      ∀ name ∈ finalNames, built.assignment name = target name := by
  obtain ⟨actualRows, found, foundRaw, decoded⟩ := GuardedZkirArtifact.check_sound checked
  have sameRaw : found = rawRows := Except.ok.inj (foundRaw.symm.trans raw)
  subst found
  obtain ⟨assignment, assembled, agrees, ordinary⟩ :=
    GuardedScalarWitnessAssembly.assemble_of_scope hash seed target view.header.arguments
      rawRows.toList view.rows finalNames validArgs distinctInputs scope
      inputAgreement holds widths
  have constraints : GuardedScalarWitnessCheck.check hash assignment.val view.rows = true := by
    apply GuardedScalarWitnessCheck.check_complete
    intro row present
    cases row with
    | strict instruction => exact ordinary instruction present
    | publicInput => trivial
    | impact => trivial
  obtain ⟨actual, actualDecoded, committed, consumedRows⟩ :=
    GuardedStatementConsumption.consumeArtifact_sound bytes target transcript observations
      targetConsumed
  have rowsEq : actual.rows = view.rows := by
    simpa only [actualDecoded, Except.map, Except.ok.injEq] using actualRows
  rw [rowsEq] at consumedRows
  have consumed : GuardedStatementConsumption.consumeArtifact bytes assignment.val transcript =
      some observations := by
    have rowsAgreement := GuardedStatementConsumption.consumeRows_agrees view.rows transcript
      (left := assignment.val) (right := target)
      (fun row present name used => agrees name (scope.transcript_identifiers row present name used))
    simp only [GuardedStatementConsumption.consumeArtifact, actualDecoded, Except.toOption,
      Bind.bind, Option.bind, committed, ite_true, rowsEq, rowsAgreement, consumedRows]
  cases bytesParsed : ArtifactBytes.parse bytes with
  | error reason => simp [bytesParsed, Except.map] at parsed
  | ok json =>
    have exactJson : json.compress = expected.compress := by
      simpa only [bytesParsed, Except.map, Except.ok.injEq] using parsed
    rcases assignment with ⟨witness, inputFrame⟩
    let built : Checked hash seed bytes expected transcript :=
      ⟨witness, view, observations, inputFrame, pinned, parsed, checked,
        GuardedScalarWitnessCheck.check_sound hash witness view.rows constraints, consumed⟩
    refine ⟨built, ?_, rfl, agrees⟩
    unfold build
    split
    · rename_i reason failed
      cases failed.symm.trans bytesParsed
    · rename_i decoded accepted
      have sameJson := Except.ok.inj (accepted.symm.trans bytesParsed)
      subst decoded
      rw [dite_eq_left exactJson]
      split
      · rename_i reason failed
        cases failed.symm.trans checked
      · rename_i decodedRows accepted
        have sameRows := Except.ok.inj (accepted.symm.trans checked)
        subst decodedRows
        split
        · rename_i reason failed
          cases failed.symm.trans pinned
        · rename_i decodedView accepted
          have sameView := Except.ok.inj (accepted.symm.trans pinned)
          subst decodedView
          simp only [raw, assembled, Bind.bind, Except.bind]
          rw [dite_eq_left constraints]
          split
          · rename_i rejected
            cases rejected.symm.trans consumed
          · rename_i seen accepted
            have sameObservations := Option.some.inj (accepted.symm.trans consumed)
            subst seen
            rfl

/-- Scalar source input types and admitted effects determine the nonforeign
descriptor schema and the named lanes required by source execution. -/
theorem lowered_scalar_descriptor_scope (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan) (shape : Native.Expected)
    (lowered : Impact.lower state ep = .ok plan)
    (accepted : Native.expectedEntrypoint state ep = .ok shape)
    (effects : ∀ effect ∈ ep.effects, ScalarGuardedPlanAdmission.ScalarEffect state effect)
    (inputTypes : ∀ input ∈ ep.circuit.inputs, Nonempty (ScalarType input.ty)) :
    (∀ requirement ∈ shape.rawInputs ++ shape.inputs, requirement.ty.isForeign = false) ∧
      ∀ name ∈ ep.circuit.inputs.map (·.name) ++
        (plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)).map (·.name),
        "%input_" ++ name ∈ (shape.rawInputs ++ shape.inputs).map (·.identifier) := by
  let reads := plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)
  have readScope := (ScalarGuardedReadAdmission.lower_read_admission
    state ep plan lowered effects).1
  have plainReads : ∀ descriptor ∈ reads,
      descriptor.bindings = [(descriptor.name, descriptor.ty)] ∧
      Nonempty (ScalarType descriptor.ty) := by
    intro descriptor present
    obtain ⟨plain, typed, _⟩ := readScope descriptor present
    obtain ⟨supported, _⟩ := Option.isSome_iff_exists.mp typed
    exact ⟨GenericStateCheckedReadDecode.supported_plain_read_bindings descriptor plain typed,
      ⟨supported⟩⟩
  refine ⟨?_, ScalarLedgerScalarSchema.accepted_source_input_identifier_membership
    state ep plan shape lowered accepted inputTypes plainReads⟩
  apply ScalarLedgerScalarSchema.accepted_nonforeign_input_schema state ep plan shape
    lowered accepted inputTypes
  intro descriptor present name ty binding
  obtain ⟨singleton, supported⟩ := plainReads descriptor present
  rw [singleton] at binding
  cases List.mem_singleton.mp binding
  exact supported

/-- Producer validation gives the exact eager input scope and the ordered
definitions of the decoded guarded relation. -/
private theorem lowered_scalar_scope
    (state : List StateDecl) (sourceEntry : Entrypoint) (rewrites : Zkir.Rewrites)
    (shape : Native.Expected) (json : Json) (view : GuardedZkirArtifact.View) (rawRows : Array Json)
    (lowered : Zkir.lowerEntrypoint state sourceEntry rewrites = .ok json)
    (expected : Native.expectedEntrypoint state (Passes.pruneEntrypoint sourceEntry) = .ok shape)
    (scalarSchema : ∀ requirement ∈ shape.rawInputs ++ shape.inputs,
      requirement.ty.isForeign = false)
    (pinned : GuardedZkirArtifact.decodeView json = .ok view)
    (raw : Native.arrayField json "instructions" = .ok rawRows) :
    let names := view.header.arguments ++ GuardedScalarWitnessAssembly.inputOutputs view.rows
    view.header.arguments.all NativeRelationJson.validIdentifier = true ∧
    names = (shape.rawInputs ++ shape.inputs).map (·.identifier) ∧
    names.Nodup ∧
    ∃ finalNames, GuardedScalarWitnessAssembly.Scope names rawRows.toList view.rows finalNames := by
  obtain ⟨_, actualShape, _, shapeAccepted, validated, _⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions_with_rewrites state sourceEntry rewrites
      json lowered
  have sameShape := Except.ok.inj (shapeAccepted.symm.trans expected)
  subst actualShape
  let optimized := Zkir.optimizedExpected rewrites shape
  have rawSchema : ∀ requirement ∈ optimized.rawInputs, requirement.ty.isForeign = false := by
    intro requirement present
    exact scalarSchema requirement (List.mem_append_left _ (by
      cases rewrites <;> exact present))
  have bodySchema : ∀ requirement ∈ optimized.inputs, requirement.ty.isForeign = false := by
    intro requirement present
    exact scalarSchema requirement (List.mem_append_right _ (by
      cases rewrites <;> exact present))
  obtain ⟨rawInputs, inputField, headerNames, validArgs⟩ :=
    GuardedZkirArtifact.lowered_view_arguments lowered pinned
  obtain ⟨instructions, driverInputs, initial, final, driver⟩ :=
    ScalarValidationProjection.validate_driver_result validated
  have sameRows := Except.ok.inj (driver.instructionsParsed.symm.trans raw)
  have sameInputs := Except.ok.inj (driver.rawInputsParsed.symm.trans inputField)
  subst instructions driverInputs
  obtain ⟨seededNames, distinctSeed⟩ :=
    ScalarValidationRawSeedMeaning.seedRawInputs_names_and_nodup rawSchema driver.seededRawInputs
  have argumentNames := Except.ok.inj (seededNames.symm.trans headerNames)
  have typed := (ScalarValidationRawSeedMeaning.seedRawInputs_meaning_and_nativeDefinitions
    (hash := fun _ => zero) (inputs := fun _ => zero) (witness := fun _ => zero)
    rawSchema (fun _ _ => rfl) driver.seededRawInputs).2
  obtain ⟨decodedRows, foundRows, decoded⟩ := GuardedZkirArtifact.decodeView_rows pinned
  have decodedSame := Except.ok.inj (foundRows.symm.trans raw)
  subst decodedRows
  have producer := GuardedScalarWitnessAssembly.ProducerScope.of_validation_loop
    bodySchema typed (by simpa only [List.zipIdx_map_fst] using decoded) driver.instructionTrace
  rw [List.zipIdx_map_fst, argumentNames] at producer
  have bodyNames := GuardedScalarWitnessAssembly.inputOutputs_eq_expectedInputs
    bodySchema typed (by simpa only [List.zipIdx_map_fst] using decoded)
    driver.instructionTrace driver.seedInputCount driver.inputCount
  have unchangedInputs : optimized.inputs = shape.inputs := by
    cases rewrites <;> rfl
  rw [unchangedInputs] at bodyNames
  have headerNames := GuardedZkirArtifact.lowered_view_arguments_expected lowered pinned expected
  have distinctArgs : view.header.arguments.Nodup := argumentNames ▸ distinctSeed
  exact ⟨validArgs, by rw [headerNames, bodyNames, List.map_append],
    producer.input_lanes_nodup distinctArgs, producer.assemble_scope⟩

/-- The actual assembler supplies a satisfying witness for the lowered
scalar relation once the remaining constraint and Boolean-domain checks hold. -/
theorem assemble_of_lowered_scalar_constraints (hash : Hash) (seed : Assignment)
    (state : List StateDecl) (sourceEntry : Entrypoint) (rewrites : Zkir.Rewrites)
    (shape : Native.Expected) (json : Json) (view : GuardedZkirArtifact.View) (rawRows : Array Json)
    (lowered : Zkir.lowerEntrypoint state sourceEntry rewrites = .ok json)
    (expected : Native.expectedEntrypoint state (Passes.pruneEntrypoint sourceEntry) = .ok shape)
    (scalarSchema : ∀ requirement ∈ shape.rawInputs ++ shape.inputs,
      requirement.ty.isForeign = false)
    (pinned : GuardedZkirArtifact.decodeView json = .ok view)
    (raw : Native.arrayField json "instructions" = .ok rawRows)
    (remaining : ∀ output, GuardedScalarWitnessAssembly.assemble hash seed
        view.header.arguments rawRows.toList view.rows = .ok output →
      ∀ pair ∈ rawRows.toList.zip view.rows,
        GuardedScalarWitnessAssembly.RemainingConstraint hash output.val pair.1 pair.2) :
    ∃ target : Assignment,
      (∀ row ∈ view.rows, GuardedImpactTranscript.ordinaryHolds hash target row) ∧
      ∀ name ∈ (shape.rawInputs ++ shape.inputs).map (·.identifier), target name = seed name := by
  obtain ⟨validArguments, names, distinct, finalNames, scope⟩ := lowered_scalar_scope
    state sourceEntry rewrites shape json view rawRows lowered expected scalarSchema pinned raw
  have distinctInputs := congrArg List.length
    (GenericStateEncoding.eraseDups_eq_self_of_nodup _ distinct)
  obtain ⟨output, assembled, _⟩ := GuardedScalarWitnessAssembly.assemble_with_scope hash seed
    view.header.arguments rawRows.toList view.rows finalNames validArguments distinctInputs scope
  have equations := (GuardedScalarWitnessAssembly.assemble_definition_equations hash seed
    view.header.arguments rawRows.toList view.rows finalNames validArguments distinctInputs scope assembled).2
  have strict := (scope.strict_holds_iff_remaining hash output.val equations).mpr
    (remaining output assembled)
  refine ⟨output.val, ?_, ?_⟩
  · intro row present
    cases row with
    | strict instruction => exact strict instruction present
    | publicInput => trivial
    | impact => trivial
  · intro name present
    apply output.property name
    rw [names]
    exact present

/-- The accepted lowering and guarded view determine the assembler's complete
ordered scope, input lanes and comparison widths. An independent satisfying
assignment and its transcript describe the computation to replay. -/
theorem build_of_lowered_scalar_artifact (hash : Hash) (seed target : Assignment)
    (state : List StateDecl) (sourceEntry : Entrypoint) (rewrites : Zkir.Rewrites)
    (shape : Native.Expected) (json : Json) (bytes : ArtifactBytes.Bytes)
    (transcript : Inputs) (view : GuardedZkirArtifact.View) (rawRows : Array Json)
    (lowered : Zkir.lowerEntrypoint state sourceEntry rewrites = .ok json)
    (expected : Native.expectedEntrypoint state (Passes.pruneEntrypoint sourceEntry) = .ok shape)
    (scalarSchema : ∀ requirement ∈ shape.rawInputs ++ shape.inputs,
      requirement.ty.isForeign = false)
    (parsed : (ArtifactBytes.parse bytes).map Json.compress = .ok json.compress)
    (checked : GuardedZkirArtifact.check bytes json = .ok view.rows)
    (pinned : GuardedZkirArtifact.decodeView json = .ok view)
    (raw : Native.arrayField json "instructions" = .ok rawRows)
    (inputAgreement : ∀ requirement ∈ shape.rawInputs ++ shape.inputs,
      seed requirement.identifier = target requirement.identifier)
    (holds : ∀ instruction, GuardedScalarRows.Row.strict instruction ∈ view.rows →
      Instruction.Holds hash target instruction)
    (observations : List GuardedImpactObservation.Observation)
    (targetConsumed : GuardedStatementConsumption.consumeArtifact bytes target transcript =
      some observations) :
    ∃ finalNames built,
      GuardedScalarWitnessAssembly.Scope
        (view.header.arguments ++ GuardedScalarWitnessAssembly.inputOutputs view.rows)
        rawRows.toList view.rows finalNames ∧
      build hash seed bytes json transcript = .ok built ∧
      built.observations = observations ∧
      ∀ name ∈ finalNames, built.assignment name = target name := by
  obtain ⟨validArgs, inputNames, distinct, finalNames, scope⟩ := lowered_scalar_scope
    state sourceEntry rewrites shape json view rawRows lowered expected scalarSchema pinned raw
  obtain ⟨decodedRows, foundRows, decoded⟩ := GuardedZkirArtifact.decodeView_rows pinned
  have decodedSame := Except.ok.inj (foundRows.symm.trans raw)
  subst decodedRows
  have ordinary : ∀ row ∈ view.rows, GuardedImpactTranscript.ordinaryHolds hash target row := by
    intro row present
    cases row with
    | strict instruction => exact holds instruction present
    | publicInput => trivial
    | impact => trivial
  have widths := GuardedZkirRequirements.lowerEntrypoint_guardedRows_comparison_bounds
    rewrites lowered raw decoded (fun _ accepted => by
      have same := Except.ok.inj (accepted.symm.trans expected)
      subst_vars
      exact scalarSchema) ordinary
  have seedAgreement : ∀ name ∈
      view.header.arguments ++ GuardedScalarWitnessAssembly.inputOutputs view.rows,
      seed name = target name := by
    intro name present
    rw [inputNames] at present
    obtain ⟨requirement, required, rfl⟩ := List.mem_map.mp present
    exact inputAgreement requirement required
  have distinctLength := congrArg List.length
    (GenericStateEncoding.eraseDups_eq_self_of_nodup _ distinct)
  obtain ⟨built, assembled, sameObservations, agrees⟩ :=
    build_of_scope hash seed target bytes json transcript view rawRows finalNames parsed
      checked pinned raw validArgs distinctLength scope seedAgreement holds widths
      observations targetConsumed
  exact ⟨finalNames, built, scope, assembled, sameObservations, agrees⟩

private def sourceInput (values : EvalEnv) (input : Input) :
    Except String (String × Scalar) := do
  let some raw := values.lookup input.name | throw s!"missing scalar input '{input.name}'"
  let some packed := ImpactTypedEnvironment.packedCanonical? input.ty raw
    | throw s!"invalid scalar input '{input.name}'"
  pure ("%input_" ++ input.name, scalar (GenericStateEncoding.number input.ty packed.val))

private theorem packedCanonical_complete {ty : Ty} (value : ty.Denote)
    (canonical : Canonical ty value) :
    ∃ packed,
      ImpactTypedEnvironment.packedCanonical? ty (Value.pack ty value) = some packed := by
  cases ty with
  | native =>
    refine ⟨⟨value, rfl, canonical⟩, ?_⟩
    change value < Field.modulus ∧ True at canonical
    have bound : value < Field.modulus := canonical.1
    simp [ImpactTypedEnvironment.packedCanonical?, Value.pack, bound]
  | bool =>
    refine ⟨⟨value, rfl, canonical⟩, ?_⟩
    simp [ImpactTypedEnvironment.packedCanonical?, Value.pack]
  | uint maximum =>
    refine ⟨⟨value, rfl, canonical⟩, ?_⟩
    change value < Field.modulus ∧
      (maximum ≤ ScalarPolicy.maxUint ∧ value ≤ maximum) at canonical
    have bounds := canonical
    simp [ImpactTypedEnvironment.packedCanonical?, Value.pack,
      bounds.1, bounds.2.1, bounds.2.2]
  | bytes length => simp [Canonical, sourceNumber?] at canonical
  | opaqueBytes => simp [Canonical, sourceNumber?] at canonical
  | opaqueString => simp [Canonical, sourceNumber?] at canonical
  | jubjubScalar => simp [Canonical, sourceNumber?] at canonical
  | jubjubPoint => simp [Canonical, sourceNumber?] at canonical
  | foreign kind => simp [Canonical, sourceNumber?] at canonical

private theorem sourceInput_complete (values : EvalEnv) (input : Input)
    (value : input.ty.Denote) (lookup : values.lookup input.name = some (Value.pack input.ty value))
    (canonical : Canonical input.ty value) :
    sourceInput values input = .ok
      ("%input_" ++ input.name, scalar (GenericStateEncoding.number input.ty value)) := by
  obtain ⟨packed, packedSuccess⟩ := packedCanonical_complete value canonical
  have packedValue : packed.val = value := by
    have same : Value.pack input.ty packed.val = Value.pack input.ty value := by
      exact packed.property.1.symm
    have packedTyped : (Value.pack input.ty packed.val).as input.ty = some packed.val :=
      ScalarNormalization.number_pack_as input.ty packed.val packed.property.2
    have valueTyped : (Value.pack input.ty value).as input.ty = some value :=
      ScalarNormalization.number_pack_as input.ty value canonical
    have typedEq := congrArg (fun raw : Value => raw.as input.ty) same
    rw [packedTyped, valueTyped] at typedEq
    exact Option.some.inj typedEq
  simp [sourceInput, lookup, packedSuccess, packedValue, pure, Except.pure]

private theorem scalarNumber_generic {ty : Ty} (support : ScalarType ty)
    (value : ty.Denote) :
    scalar (ScalarNormalization.number support value) =
      scalar (GenericStateEncoding.number ty value) :=
  Option.some.inj <| (ScalarNormalization.sourceScalar_number support value).symm.trans
    (GenericStateEncoding.sourceScalar_eq_field support value)

private theorem sourceInputs_success_and_binding (inputs : List Input) (values : EvalEnv)
    (arbitraryAssignment : Assignment)
    (complete : ∀ input ∈ inputs, ∃ value : input.ty.Denote,
      values.lookup input.name = some (Value.pack input.ty value) ∧ Canonical input.ty value)
    (binding : ∀ input ∈ inputs, ∀ value : input.ty.Denote,
      values.lookup input.name = some (Value.pack input.ty value) →
        ∀ (_canonical : Canonical input.ty value),
          arbitraryAssignment ("%input_" ++ input.name) =
            scalar (GenericStateEncoding.number input.ty value)) :
    ∃ sourceInputs,
      inputs.mapM (sourceInput values) = .ok sourceInputs ∧
      ∀ input ∈ inputs, arbitraryAssignment ("%input_" ++ input.name) =
        (sourceInputs.lookup ("%input_" ++ input.name)).getD zero := by
  induction inputs with
  | nil =>
    refine ⟨[], rfl, ?_⟩
    intro input member
    simp at member
  | cons head tail ih =>
    obtain ⟨headValue, headLookup, headCanonical⟩ := complete head (by simp)
    have headSuccess := sourceInput_complete values head headValue headLookup headCanonical
    obtain ⟨tailInputs, tailSuccess, tailBinding⟩ := ih
      (fun input member => complete input (by simp [member]))
      (fun input member value lookup canonical => binding input (by simp [member]) value lookup canonical)
    refine ⟨("%input_" ++ head.name,
      scalar (GenericStateEncoding.number head.ty headValue)) :: tailInputs, ?_, ?_⟩
    · simp [List.mapM_cons, headSuccess, tailSuccess,
        bind, Except.bind, pure, Except.pure]
    · intro input member
      rcases List.mem_cons.mp member with same | member
      · subst input
        have headBinding := binding head (by simp) headValue headLookup headCanonical
        simp [headBinding]
      · by_cases sameKey : ("%input_" ++ input.name) = ("%input_" ++ head.name)
        · obtain ⟨value, lookup, canonical⟩ := complete input (by simp [member])
          have targetBinding := binding input (by simp [member]) value lookup canonical
          have headBinding := binding head (by simp) headValue headLookup headCanonical
          have bindingsEqual := congrArg arbitraryAssignment sameKey
          rw [targetBinding, headBinding] at bindingsEqual
          calc
            arbitraryAssignment ("%input_" ++ input.name) =
                scalar (GenericStateEncoding.number input.ty value) := targetBinding
            _ = scalar (GenericStateEncoding.number head.ty headValue) := bindingsEqual
            _ = ((("%input_" ++ head.name,
                scalar (GenericStateEncoding.number head.ty headValue)) :: tailInputs).lookup
                  ("%input_" ++ input.name)).getD zero := by
              simp [sameKey]
        · have keyDifferent : ("%input_" ++ input.name) ≠ ("%input_" ++ head.name) := sameKey
          have unequal : (("%input_" ++ input.name) == ("%input_" ++ head.name)) = false :=
            beq_eq_false_iff_ne.mpr keyDifferent
          simpa [List.lookup_cons, unequal] using tailBinding input member

/-- Canonical source inputs make the executable public-input collection
succeed. The exact lookup seed used by `buildSourceCall` retains canonical
input admission. -/
theorem source_inputs_seed_canonical (ep : Entrypoint) (values : EvalEnv)
    (arbitraryAssignment : Assignment)
    (admitted : CanonicalInputs ep.circuit values arbitraryAssignment) :
    ∃ sourceInputs,
      ep.circuit.inputs.mapM (sourceInput values) = .ok sourceInputs ∧
      CanonicalInputs ep.circuit values
        (fun name => (sourceInputs.lookup name).getD zero) := by
  obtain ⟨sourceInputs, success, sourceBinding⟩ := sourceInputs_success_and_binding
    ep.circuit.inputs values arbitraryAssignment admitted.complete (by
      intro input member value lookup canonical
      have assigned := admitted.binding input member value lookup canonical
      rw [scalarNumber_generic] at assigned
      cases input with
      | mk name ty visibility span => exact assigned)
  refine ⟨sourceInputs, success, ⟨admitted.unique, admitted.declared, admitted.complete, ?_⟩⟩
  intro input member value lookup canonical
  exact (sourceBinding input member).symm.trans
    (admitted.binding input member value lookup canonical)

structure SourceCall (hash : Hash) (bytes : ArtifactBytes.Bytes) where
  expected : Json
  seed : Assignment
  transcript : Inputs
  checked : Checked hash seed bytes expected transcript

/-- Derive scalar call inputs and ledger reads from source execution. Build
the witness against the compiler's guarded artifact and the matching VM
transcript. The source and VM frames must encode the same successor. -/
def buildSourceCall (ctx : EvalContext) (hash : Hash) (state : List StateDecl)
    (sourceEntry : Entrypoint) (values : EvalEnv) (initial : LedgerState)
    (bytes : ArtifactBytes.Bytes) (rewrites : Zkir.Rewrites := .disabled) :
    Except String (SourceCall hash bytes) := do
  let ep := Passes.pruneEntrypoint sourceEntry
  let expected ← (Zkir.lowerEntrypoint state sourceEntry rewrites).mapError Diagnostic.message
  let plan ← (Impact.lower state ep).mapError Diagnostic.message
  let sourceInputs ← ep.circuit.inputs.mapM (sourceInput values)
  let outputs ← sourceEntry.circuit.run ctx values
  let cutoff := Impact.publicInputReadCount ep.circuit.inputs
  let (entries, sourceAfter) ← ScalarSourceReadTape.sourceReadInputs ctx ep.effectGuards
    ep.effects.zipIdx cutoff (outputs ++ values, initial)
  let descriptors := plan.reads.drop cutoff
  let metadata := GenericStateCheckedReadTrace.readMetadata
  unless descriptors.map metadata == entries.map (metadata ∘ Prod.fst) do
    throw "source read records differ from the accepted Impact descriptors"
  let seed := seedReadValues (fun name => (sourceInputs.lookup name).getD zero) entries
  let reads ← GenericStateInputValues.decodeReads descriptors seed
  let ops ← GuardedPlanExecution.evalPlan ctx ((outputs ++ values) ++ reads) plan
  let some slots := GenericStateEncoding.encodeInitialState state initial
    | throw "initial state cannot be encoded for a scalar call"
  let some final := NativeState.run ops (GenericStateEncoding.initial slots)
    | throw "scalar VM rejected the source call"
  let some sourceSlots := GenericStateEncoding.encodeState state sourceAfter.2
    | throw "source successor cannot be encoded for a scalar call"
  unless final.stack == [.vector sourceSlots] do
    throw "scalar VM successor differs from the encoded source successor"
  let transcript := ⟨ops.flatMap ImpactStatementScalar.opFields,
    final.reads.map NativeState.Cell.value⟩
  let checked ← build hash seed bytes expected transcript
  pure ⟨expected, seed, transcript, checked⟩

/-- The accepted source and artifact schedules preserve the named circuit
inputs and the exact ordered post-public ledger reads. -/
theorem Checked.source_read_values (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan) (rewrites : Zkir.Rewrites)
    (ctx : EvalContext) (inputs : Assignment)
    (initial final : SourceEffects.Frame) (records : List (Impact.Read × Scalar))
    (lowered : Impact.lower state (Passes.pruneEntrypoint ep) = .ok plan)
    (effects : ∀ effect ∈ ep.effects, ScalarGuardedPlanAdmission.ScalarEffect state effect)
    (inputTypes : ∀ input ∈ ep.circuit.inputs, Nonempty (ScalarType input.ty))
    (recorded : ScalarSourceReadTape.sourceReadInputs ctx ep.effectGuards ep.effects.zipIdx
       (Impact.publicInputReadCount ep.circuit.inputs) initial = .ok (records, final))
    {hash : Hash} {bytes : ArtifactBytes.Bytes} {expected : Json} {transcript : Inputs}
    (emitted : Zkir.lowerEntrypoint state ep rewrites = .ok expected)
    (built : Checked hash (seedReadValues inputs records) bytes expected transcript) :
    let reads := plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)
    (∀ input ∈ ep.circuit.inputs,
      built.assignment ("%input_" ++ input.name) = inputs ("%input_" ++ input.name)) ∧
    ∃ readValues,
      GenericStateInputValues.decodeReads reads built.assignment = .ok readValues ∧
      readValues.map Prod.fst = records.map (fun record => record.1.name) := by
  let pruned := Passes.pruneEntrypoint ep
  let reads := plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)
  obtain ⟨_, shape, _, shapeAccepted, _, _⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions_with_rewrites state ep rewrites expected emitted
  obtain ⟨scalarSchema, sourceLanes⟩ := lowered_scalar_descriptor_scope
    state pruned plan shape lowered shapeAccepted effects inputTypes
  obtain ⟨rawRows, raw, _⟩ := GuardedZkirArtifact.decodeView_rows built.pinned
  obtain ⟨_, lanes, _, _, _⟩ := lowered_scalar_scope state ep rewrites shape
    expected built.view rawRows emitted shapeAccepted scalarSchema built.pinned raw
  have frame (name : String) (present : name ∈ ep.circuit.inputs.map (·.name) ++
      reads.map (·.name)) :
      built.assignment ("%input_" ++ name) = seedReadValues inputs records ("%input_" ++ name) :=
    built.inputFrame _ (by rw [lanes]; exact sourceLanes name present)
  obtain ⟨_, _, preserved, readValues, decoded, order, _⟩ :=
    ScalarSourceReadWitness.lower_source_read_witness state pruned plan ctx inputs initial final
      records lowered effects recorded
  refine ⟨fun input present => (frame input.name
    (List.mem_append_left _ (List.mem_map_of_mem present))).trans (preserved input present),
    readValues, ?_, order⟩
  rw [GenericStateInputValues.decodeReads_agree_on reads _ built.assignment (fun descriptor present =>
    frame descriptor.name (List.mem_append_right _ (List.mem_map_of_mem present)))]
  exact decoded

end Noctium.Verification.GuardedScalarWitness
