import Noctium.Verification.GuardedScalarSchedule
import Noctium.Verification.GenericStateWriteEvaluation
import Noctium.Verification.ScalarLedgerScalarSchema
import Noctium.Verification.ScalarSourceFrame

namespace Noctium.Verification.GuardedScalarCandidateSchedule

open Lean Backend NativeRelation ScalarNormalization
open GenericStateCircuitParts GuardedImpactObservation GuardedImpactTranscript
open GenericStateInputValues (decodeReads scalarType?)
open ScalarGuardedPlanAdmission (ScalarEffect)

/-- Checked circuit and input requirements construct the complete source and
candidate value frame using the accepted plan's exact read order and aliases. -/
theorem expected_candidate_frame
    (state : List StateDecl) (ep : Entrypoint) (expected : Native.Expected) (plan : Impact.Plan)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (assignment : Assignment)
    (planAccepted : Impact.lower state ep = .ok plan)
    (expectedAccepted : Native.expectedEntrypoint state ep = .ok expected)
    (inputs : CanonicalInputs ep.circuit values assignment)
    (admitted : ScalarCircuitAdmission ep.circuit)
    (plainReads : ∀ readSpec ∈ plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs),
      readSpec.components = [] ∧ (scalarType? readSpec.ty).isSome = _root_.Bool.true ∧
        readSpec.ty.validate {poseidon2 := _root_.Bool.true, stateCells := _root_.Bool.true, stateMaps := _root_.Bool.true} = .ok ())
    (separateReads : ∀ readSpec ∈ plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs),
      readSpec.name ∉ ep.circuit.inputs.map (·.name) ++ ep.circuit.outputs.map (·.name))
    (distinctReads : (plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)).Pairwise
      (fun left right => left.name ≠ right.name))
    (assertions : ∀ term ∈ expected.assertions, interpret hash assignment term = some one)
    (bounds : ∀ requirement ∈ expected.bounds,
      ∃ value, interpret hash assignment requirement.1 = some value ∧ value.val ≤ requirement.2)
    (inputBounds : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      requirement.ty.isForeign = _root_.Bool.false → requirement.canonicalJubjubScalar = _root_.Bool.false →
      (assignment requirement.identifier).val ≤ Native.sourceMaximum requirement.ty) :
    let reads := plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)
    ∃ (frame : OutputFrame) (result candidates : EvalEnv),
      normalizeOutputs (entrypointSeedAliases ep plan) ep.circuit.outputs = .ok frame ∧
      ep.circuit.run ctx values = .ok result ∧
      decodeReads reads assignment = .ok candidates ∧
      TypedEnvironment hash assignment frame.1 ((result ++ values) ++ candidates)
        (plan.typeEnvironment ep) ∧
      forIn (reads.flatMap Impact.Read.scalarReads) frame.1 (readAliasStep ep) = .ok frame.1 := by
  have scalarReads := ScalarSourceFrame.plain_scalar_read_scope ep plan
    (fun readSpec present => ⟨(plainReads readSpec present).1, (plainReads readSpec present).2.1⟩)
  obtain ⟨frame, result, normalized, executed, resultNames, base⟩ :=
    ScalarSourceFrame.sourceFrame_of_requirements state ep expected plan ctx hash implementation
      values assignment planAccepted expectedAccepted scalarReads inputs admitted assertions bounds
  obtain ⟨readFresh, readAliases⟩ := ScalarSourceFrame.candidate_read_frame_lookups
    ep plan frame result values assignment inputs normalized resultNames
    (fun readSpec present => ⟨(plainReads readSpec present).1, (plainReads readSpec present).2.1⟩)
    separateReads
  obtain ⟨candidates, decoded, environment, _⟩ :=
    ScalarPlanGuardSoundness.typed_candidates_of_input_bounds state ep hash assignment
      plan expected frame (result ++ values) planAccepted expectedAccepted base
      plainReads readFresh distinctReads readAliases inputBounds
  exact ⟨frame, result, candidates, normalized, executed, decoded, environment,
    expectedEntrypoint_scalar_read_aliases state ep expected plan frame planAccepted
      expectedAccepted normalized scalarReads⟩

/-- A checked guarded artifact and canonical source inputs determine a source
result, decoded candidate reads, and the exact active native groups. The
admission of the accepted read descriptors and row satisfaction are explicit. -/
theorem lower_checked_guarded_candidate_schedule
    (state : List StateDecl) (sourceEntry : Entrypoint) (rewrites : Zkir.Rewrites)
    (expected : Native.Expected) (plan : Impact.Plan)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (assignment : Assignment)
    (bytes : ArtifactBytes.Bytes) (json : Json) (rows : List GuardedScalarRows.Row)
    (emitted : Zkir.lowerEntrypoint state sourceEntry rewrites = .ok json)
    (artifact : GuardedZkirArtifact.check bytes json = .ok rows)
    (ordinary : ∀ row ∈ rows, ordinaryHolds hash assignment row)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint sourceEntry) = .ok plan)
    (expectedAccepted :
      Native.expectedEntrypoint state (Passes.pruneEntrypoint sourceEntry) = .ok expected)
    (inputs : CanonicalInputs sourceEntry.circuit values assignment)
    (admitted : ScalarCircuitAdmission sourceEntry.circuit)
    (effects : ∀ effect ∈ sourceEntry.effects, ScalarEffect state effect)
    (guardsAdmitted : ∀ condition, some condition ∈ sourceEntry.effectGuards →
      ScalarExpression condition)
    (plainReads : ∀ readSpec ∈ plan.reads.drop
        (Impact.publicInputReadCount sourceEntry.circuit.inputs),
      readSpec.components = [] ∧ (scalarType? readSpec.ty).isSome = _root_.Bool.true ∧
        readSpec.ty.validate {poseidon2 := _root_.Bool.true, stateCells := _root_.Bool.true, stateMaps := _root_.Bool.true} = .ok ())
    (separateReads : ∀ readSpec ∈ plan.reads.drop
        (Impact.publicInputReadCount sourceEntry.circuit.inputs),
      readSpec.name ∉ sourceEntry.circuit.inputs.map (·.name) ++
        sourceEntry.circuit.outputs.map (·.name))
    (distinctReads : (plan.reads.drop
      (Impact.publicInputReadCount sourceEntry.circuit.inputs)).Pairwise
      (fun left right => left.name ≠ right.name)) :
    let ep := Passes.pruneEntrypoint sourceEntry
    let reads := plan.reads.drop (Impact.publicInputReadCount sourceEntry.circuit.inputs)
    (GuardedZkirArtifact.decodeBytes bytes).map GuardedZkirArtifact.View.rows = .ok rows ∧
    ∃ (frame : OutputFrame) (result candidates : EvalEnv)
        (observations : List Observation) (active : List NativeState.Op),
      normalizeOutputs (entrypointSeedAliases ep plan) ep.circuit.outputs = .ok frame ∧
      sourceEntry.circuit.run ctx values = .ok result ∧
      decodeReads reads assignment = .ok candidates ∧
      TypedEnvironment hash assignment frame.1 ((result ++ values) ++ candidates)
        (plan.typeEnvironment ep) ∧
      emittedObservations assignment rows = some observations ∧
      GuardedPlanExecution.evalPlan ctx ((result ++ values) ++ candidates) plan = .ok active ∧
      NativeState.groups active = (observations.filter (·.active)).map (·.payload) := by
  let ep := Passes.pruneEntrypoint sourceEntry
  let reads := plan.reads.drop (Impact.publicInputReadCount sourceEntry.circuit.inputs)
  have inputScope : ∀ input ∈ ep.circuit.inputs, Nonempty (ScalarType input.ty) := by
    intro input present
    obtain ⟨_, _, canonical⟩ := inputs.complete input present
    exact GenericStateWriteEvaluation.scalarType_of_canonical canonical
  have readScope : ∀ readSpec ∈ reads, ∀ name ty,
      (name, ty) ∈ readSpec.bindings → Nonempty (ScalarType ty) := by
    intro readSpec present name ty binding
    obtain ⟨plain, supported, _⟩ := plainReads readSpec present
    rw [GenericStateCheckedReadDecode.supported_plain_read_bindings readSpec plain supported]
      at binding
    have sameType : ty = readSpec.ty := congrArg Prod.snd (List.mem_singleton.mp binding)
    subst ty
    cases decoded : scalarType? readSpec.ty with
    | none => simp [decoded] at supported
    | some support => exact ⟨support⟩
  have schema := ScalarLedgerScalarSchema.accepted_nonforeign_input_schema
    state ep plan expected planAccepted expectedAccepted inputScope readScope
  have schemaFromExpected (other : Native.Expected)
      (accepted : Native.expectedEntrypoint state ep = .ok other) :
      ∀ requirement ∈ other.rawInputs ++ other.inputs,
        requirement.ty.isForeign = Bool.false := by
    have same := Except.ok.inj (accepted.symm.trans expectedAccepted)
    subst other
    exact schema
  obtain ⟨_, _, parsed, decoded⟩ := GuardedZkirArtifact.check_sound artifact
  obtain ⟨requirementExpected, requirementAccepted, requirements⟩ :=
    GuardedZkirRequirements.lowerEntrypoint_guardedRows_sourceRequirements
      rewrites emitted parsed decoded schemaFromExpected
  have same := Except.ok.inj (requirementAccepted.symm.trans expectedAccepted)
  subst requirementExpected
  obtain ⟨assertions, bounds, inputBounds⟩ := requirements ordinary
  have canonical : CanonicalInputs ep.circuit values assignment :=
    ⟨inputs.unique, inputs.declared, inputs.complete, inputs.binding⟩
  obtain ⟨frame, result, candidates, normalized, executed, candidatesDecoded,
    environment, readAliases⟩ :=
    expected_candidate_frame state ep expected plan ctx hash implementation values assignment
      planAccepted expectedAccepted canonical (admitted.pruneCircuit sourceEntry.circuit)
      plainReads separateReads distinctReads assertions bounds inputBounds
  have compatible : ∀ input ∈ ep.circuit.inputs, Impact.publicInputScalarCompatible input := by
    intro input present
    obtain ⟨supported⟩ := inputScope input present
    cases input with
    | mk name ty visibility span => cases supported <;> simp [Impact.publicInputScalarCompatible]
  have scalarReads := ScalarSourceFrame.plain_scalar_read_scope ep plan
    (fun readSpec present => ⟨(plainReads readSpec present).1, (plainReads readSpec present).2.1⟩)
  obtain ⟨exactRows, observations, active, observed, evaluated, groups⟩ :=
    GuardedScalarSchedule.lower_checked_guarded_artifact_schedule
      state sourceEntry rewrites expected plan frame ctx hash implementation assignment
      ((result ++ values) ++ candidates) bytes json rows environment emitted artifact ordinary
      expectedAccepted planAccepted normalized readAliases compatible effects guardsAdmitted
      scalarReads schema
  have sourceRun : sourceEntry.circuit.run ctx values = .ok result := by
    simpa only [ep, Passes.pruneEntrypoint, Passes.pruneCircuit_run] using executed
  exact ⟨exactRows, frame, result, candidates, observations, active, normalized, sourceRun,
    candidatesDecoded, environment, observed, evaluated, groups⟩

end Noctium.Verification.GuardedScalarCandidateSchedule
