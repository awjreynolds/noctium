import Noctium.Verification.GenericStateAliases
import Noctium.Verification.GenericStateCaps
import Noctium.Verification.GenericStateEffectValidation
import Noctium.Verification.GuardedScalarInput
import Noctium.Verification.GuardedSourceReadTranscript
import Noctium.Verification.NativeStateReadTape
import Noctium.Verification.ScalarCellNativePublicPrefix

namespace Noctium.Verification.GuardedVmPublicPrefix

open Backend NativeRelation NativeState ScalarNormalization
open GuardedScalarInput GuardedSourceReadTranscript

private theorem evalOutputs_names (ctx : EvalContext) (values : EvalEnv)
    (outputs : List Output) (result : EvalEnv)
    (evaluated : outputs.mapM (evalOutput ctx values) = .ok result) :
    result.map Prod.fst = outputs.map Output.name := by
  induction outputs generalizing result with
  | nil => simp at evaluated; cases evaluated; rfl
  | cons output rest ih =>
    simp only [List.mapM_cons] at evaluated
    cases head : evalOutput ctx values output with
    | error message => simp [head, bind, Except.bind] at evaluated
    | ok pair =>
      cases tail : rest.mapM (evalOutput ctx values) with
      | error message => simp [head, tail, bind, Except.bind] at evaluated
      | ok tailResult =>
        simp [head, tail, bind, Except.bind] at evaluated
        cases evaluated
        have headName : pair.1 = output.name := by
          unfold evalOutput at head
          simp only [bind, Except.bind] at head
          cases value : output.value.eval ctx values with
          | error message => simp [value] at head
          | ok value =>
            simp [value] at head
            cases head
            rfl
        simp [headName, ih tailResult tail]

private theorem lookup_none_of_absent_keys (items : List (String × α))
    (name : String) (absent : name ∉ items.map Prod.fst) :
    items.lookup name = none := by
  apply List.lookup_eq_none_iff.mpr
  intro pair member
  have different : name ≠ pair.1 := by
    intro equal
    exact absent (List.mem_map.mpr ⟨pair, member, equal.symm⟩)
  simp [different]

/-- A successful source circuit keeps its typed inputs available after the
actual output frame and any decoded read candidates are appended. -/
theorem source_candidate_input_lookup
    (state : List StateDecl) (entry : Entrypoint) (plan : Impact.Plan)
    (ctx : EvalContext) (values outputs future : EvalEnv)
    (assignment : Assignment)
    (admitted : CanonicalInputs entry.circuit values assignment)
    (lowered : Impact.lower state entry = .ok plan)
    (source : entry.circuit.run ctx values = .ok outputs)
    : ∀ input ∈ entry.circuit.inputs,
      ((outputs ++ values) ++ future).lookup input.name = values.lookup input.name := by
  have sourceValid := GenericStateEffectValidation.lower_circuit_validated_source
    state entry plan lowered
  rw [GenericStateCaps.circuit_validate_source_crypto] at sourceValid
  have unshadowed :=
    (GenericStateAliases.validated_output_scope Capabilities.crypto entry.circuit sourceValid).2
  obtain ⟨_, outputEval⟩ := circuit_run_steps ctx entry.circuit values outputs source
  have outputNames := evalOutputs_names ctx values entry.circuit.outputs outputs outputEval
  intro input member
  obtain ⟨inputValue, inputLookup, _⟩ := admitted.complete input member
  have outputAbsent : input.name ∉ outputs.map Prod.fst := by
    intro present
    rw [outputNames] at present
    obtain ⟨output, outputMember, same⟩ := List.mem_map.mp present
    have typedMember : (input.name, input.ty) ∈
        entry.circuit.inputs.map (fun declared => (declared.name, declared.ty)) :=
      List.mem_map.mpr ⟨input, member, rfl⟩
    have different := List.lookup_eq_none_iff.mp
      (unshadowed output outputMember) (input.name, input.ty) typedMember
    rw [same] at different
    simp at different
  have outputLookup := lookup_none_of_absent_keys outputs input.name outputAbsent
  have candidateLookup :
      ((outputs ++ values) ++ future).lookup input.name =
        some (Value.pack input.ty inputValue) := by
    simp [List.lookup_append, outputLookup, inputLookup]
  exact candidateLookup.trans inputLookup.symm

/-- Every observation from a public circuit declaration carries the active
guard. -/
theorem publicCircuitObservations_guard_one (inputs : List Input) (assignment : Assignment)
    (observation : ReadObservation)
    (member : observation ∈ publicCircuitObservations inputs assignment) :
    observation.guard = one := by
  unfold publicCircuitObservations at member
  simp only [List.mem_filterMap] at member
  obtain ⟨input, _, observed⟩ := member
  split at observed
  · cases observed
    rfl
  · simp at observed

private theorem sourcePublicCells_values_as_numbers (inputs : List Input)
    (assignment : Assignment) :
    (ScalarCellNativePublicPrefix.sourcePublicCells inputs assignment).map Cell.value =
      (inputs.filter (·.visibility == .«public»)).map
        (fun input => assignment ("%input_" ++ input.name)) := by
  unfold ScalarCellNativePublicPrefix.sourcePublicCells
  simp [List.map_map, NativeState.field]

private theorem publicCircuitObservations_filter (inputs : List Input)
    (assignment : Assignment) :
    publicCircuitObservations inputs assignment =
      (inputs.filter (·.visibility == .«public»)).map
        (fun input => ⟨one, assignment ("%input_" ++ input.name)⟩) := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
    cases visibility : input.visibility <;>
      simp [publicCircuitObservations, visibility, ← ih]

private theorem publicCircuitObservations_active_values (inputs : List Input)
    (assignment : Assignment) :
    activeReadValues (publicCircuitObservations inputs assignment) =
      (inputs.filter (·.visibility == .«public»)).map
        (fun input => assignment ("%input_" ++ input.name)) := by
  rw [publicCircuitObservations_filter]
  induction inputs.filter (·.visibility == .«public») with
  | nil => rfl
  | cons input rest ih => simp [activeReadValues, ih]

private theorem sourcePublicCells_values (inputs : List Input) (assignment : Assignment) :
    (ScalarCellNativePublicPrefix.sourcePublicCells inputs assignment).map Cell.value =
      activeReadValues (publicCircuitObservations inputs assignment) := by
  rw [sourcePublicCells_values_as_numbers, publicCircuitObservations_active_values]

/-- The exact evaluated native operations of the accepted public-input plan
read the scalars emitted by public circuit observations, in declaration order. -/
theorem public_input_prefix_expected_cells_values
    (entry : Entrypoint) (plan : Impact.Plan) (ctx : EvalContext)
    (values candidate : EvalEnv) (assignment : Assignment)
    (admitted : CanonicalInputs entry.circuit values assignment)
    (compatible : ∀ input ∈ entry.circuit.inputs,
      Impact.publicInputScalarCompatible input)
    (accepted : Impact.publicInputPlan entry.circuit.inputs {} = .ok plan)
    (lookup : ∀ input ∈ entry.circuit.inputs,
      candidate.lookup input.name = values.lookup input.name)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ native, GenericStateOps.evalPlan ctx candidate plan = .ok native ∧
      (NativeStateReadTape.expectedCells native).map Cell.value =
        activeReadValues (publicCircuitObservations entry.circuit.inputs assignment) := by
  obtain ⟨native, cells, _, evaluated, _, nativeShape, cellsExpected, run⟩ :=
    ScalarCellNativePublicPrefix.run_public_prefix_from_candidate entry plan ctx values candidate
      assignment [] [] admitted compatible accepted lookup modulus
  have publicRun : NativeState.run native ⟨[], []⟩ =
      some ⟨[], ScalarCellNativePublicPrefix.sourcePublicCells entry.circuit.inputs assignment⟩ := by
    simpa only [List.nil_append, cellsExpected] using run
  have tape := NativeStateReadTape.run_reads publicRun
  have expectedCells : NativeStateReadTape.expectedCells native =
      ScalarCellNativePublicPrefix.sourcePublicCells entry.circuit.inputs assignment := by
    simpa only [List.nil_append] using tape.symm
  refine ⟨native, evaluated, ?_⟩
  rw [expectedCells, sourcePublicCells_values]

/-- Source circuit success provides the candidate lookup needed by the public
prefix bridge. The `future` environment may contain decoded state-read
candidates appended after the original source inputs and outputs. -/
theorem source_candidate_public_input_prefix_expected_cells_values
    (state : List StateDecl) (entry : Entrypoint) (plan inputPlan : Impact.Plan)
    (ctx : EvalContext) (values outputs future : EvalEnv) (assignment : Assignment)
    (admitted : CanonicalInputs entry.circuit values assignment)
    (lowered : Impact.lower state entry = .ok plan)
    (source : entry.circuit.run ctx values = .ok outputs)
    (compatible : ∀ input ∈ entry.circuit.inputs,
      Impact.publicInputScalarCompatible input)
    (accepted : Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ native, GenericStateOps.evalPlan ctx ((outputs ++ values) ++ future) inputPlan =
        .ok native ∧
      (NativeStateReadTape.expectedCells native).map Cell.value =
        activeReadValues (publicCircuitObservations entry.circuit.inputs assignment) := by
  have lookup := source_candidate_input_lookup state entry plan ctx values outputs future
    assignment admitted lowered source
  exact public_input_prefix_expected_cells_values entry inputPlan ctx values
    ((outputs ++ values) ++ future) assignment admitted compatible accepted lookup modulus

end Noctium.Verification.GuardedVmPublicPrefix
