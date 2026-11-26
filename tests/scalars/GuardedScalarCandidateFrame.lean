import Noctium.Frontend
import Noctium.Verification.GuardedScalarCandidateSchedule

open scoped Noctium
open Noctium
open Noctium.Verification
open Noctium.Verification.NativeRelation
open Noctium.Verification.NativeState
open Noctium.Verification.GenericStateInputValues (decodeReads scalarType?)

noctium_circuit guardedCandidateInputs where
  public enabled : Bool
  output prepared : Native := 7
end

noctium_contract GuardedScalarCandidateFrame where
  map balances : Native => Native

  entry observe uses guardedCandidateInputs where
    when enabled read balances[17] as saved
  end
end

namespace GuardedScalarCandidateFrameProof

open Noctium.Backend.Native
open Noctium.Verification.GenericStateCircuitParts
open Noctium.Verification.ScalarNormalization

private def fixtureEntry : Entrypoint :=
  (GuardedScalarCandidateFrame.entrypoints.find? (·.name == "observe")).getD
    {name := "missing", circuit := {name := "missing"}}

private def state : List StateDecl := GuardedScalarCandidateFrame.state

private def plan : Backend.Impact.Plan :=
  match Backend.Impact.lower state fixtureEntry with
  | .ok lowered => lowered
  | .error _ => {}

private theorem plan_accepted : Backend.Impact.lower state fixtureEntry = .ok plan := by
  with_unfolding_all rfl

private def expected : Expected :=
  match Noctium.Backend.Native.expectedEntrypoint state fixtureEntry with
  | .ok value => value
  | .error _ => {
      mode := .relation
      inputs := []
      groups := []
      returns := []
      assertions := []
      bounds := []
    }

private theorem expected_accepted :
    Noctium.Backend.Native.expectedEntrypoint state fixtureEntry = .ok expected := by
  with_unfolding_all rfl

private def context : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .ok zero
}

private def hash : Hash := fun _ => zero

private theorem hash_agrees : HashAgreement context hash := by
  constructor
  · rfl
  · intro domain left right
    rfl

private def values : EvalEnv := [("enabled", .bool _root_.Bool.true)]

private def assignment : Assignment := fun identifier =>
  if identifier == "%input_enabled" then scalar 1 else
  if identifier == "%input_saved" then scalar 41 else zero

private def enabledInput : Input := guardedCandidateInputs.inputs[0]'(by decide)

private theorem exact_single_input : fixtureEntry.circuit.inputs = [enabledInput] := by
  with_unfolding_all rfl

private theorem canonical_inputs :
    CanonicalInputs fixtureEntry.circuit values assignment := by
  constructor
  · decide +kernel
  · intro name raw present
    simp only [values, List.mem_singleton, Prod.mk.injEq] at present
    rcases present with ⟨rfl, rfl⟩
    exact ⟨enabledInput, by simp [exact_single_input], by with_unfolding_all rfl⟩
  · intro input present
    rw [exact_single_input] at present
    obtain rfl := List.mem_singleton.mp present
    exact ⟨_root_.Bool.true, by with_unfolding_all rfl,
      by exact ⟨by decide +kernel, trivial⟩⟩
  · intro input present value lookup canonical
    rw [exact_single_input] at present
    obtain rfl := List.mem_singleton.mp present
    change (some (.bool _root_.Bool.true) : Option Value) = some (.bool value) at lookup
    have same : value = _root_.Bool.true := (Value.bool.inj (Option.some.inj lookup)).symm
    subst value
    with_unfolding_all rfl

private theorem circuit_admitted : ScalarCircuitAdmission fixtureEntry.circuit := by
  constructor
  · intro condition present
    simp [fixtureEntry, guardedCandidateInputs, GuardedScalarCandidateFrame] at present
  · intro outSpec present
    simp [fixtureEntry, guardedCandidateInputs, GuardedScalarCandidateFrame] at present
    subst outSpec
    exact ⟨.native, .native 7⟩

private def reads : List Backend.Impact.Read :=
  plan.reads.drop (Backend.Impact.publicInputReadCount fixtureEntry.circuit.inputs)

private theorem exact_reads : reads =
    [{name := "saved", ty := .native, components := [], schema := none,
      guard := some (.ref "enabled"), rootCellRead := none}] := by
  with_unfolding_all rfl

private theorem plain_reads : ∀ readSpec ∈ reads,
    readSpec.components = [] ∧ (scalarType? readSpec.ty).isSome = _root_.Bool.true ∧
      readSpec.ty.validate
        {poseidon2 := _root_.Bool.true, stateCells := _root_.Bool.true,
          stateMaps := _root_.Bool.true} = .ok () := by
  intro readSpec present
  rw [exact_reads] at present
  simp only [List.mem_singleton] at present
  subst readSpec
  simp [scalarType?, Ty.validate, Ty.scalarKind, ScalarPolicy.validate, pure, Except.pure]

private theorem separate_reads : ∀ readSpec ∈ reads,
    readSpec.name ∉ fixtureEntry.circuit.inputs.map (·.name) ++
      fixtureEntry.circuit.outputs.map (·.name) := by
  intro readSpec present
  rw [exact_reads] at present
  simp only [List.mem_singleton] at present
  subst readSpec
  simp [fixtureEntry, guardedCandidateInputs, GuardedScalarCandidateFrame]

private theorem distinct_reads : reads.Pairwise (fun left right => left.name ≠ right.name) := by
  rw [exact_reads]
  simp

private def guardAssertion : Term :=
  .binary "test_eq" (.input "%input_saved")
    (.select (.input "%input_enabled") (.input "%input_saved") (.constant 0))

private theorem exact_assertions : expected.assertions = [guardAssertion] := by
  with_unfolding_all rfl

private theorem assertions : ∀ term ∈ expected.assertions,
    interpret hash assignment term = some one := by
  intro term present
  rw [exact_assertions] at present
  simp only [List.mem_singleton] at present
  subst term
  simp [guardAssertion, interpret, assignment, scalar_one, bit]

private theorem exact_bounds : expected.bounds =
    List.replicate 5 (Term.input "%input_enabled", 1) ++
      [(guardAssertion, 1)] ++ List.replicate 3 (Term.input "%input_enabled", 1) := by
  with_unfolding_all rfl

private theorem bounds : ∀ requirement ∈ expected.bounds,
    ∃ value, interpret hash assignment requirement.1 = some value ∧ value.val ≤ requirement.2 := by
  intro requirement present
  rw [exact_bounds] at present
  have shape : requirement = (Term.input "%input_enabled", 1) ∨
      requirement = (guardAssertion, 1) := by
    simpa [List.mem_replicate, or_assoc, or_left_comm, or_comm] using present
  rcases shape with rfl | rfl
  · exact ⟨scalar 1, by simp [interpret, assignment], by decide +kernel⟩
  · exact ⟨one, by simp [guardAssertion, interpret, assignment, scalar_one, bit], by decide +kernel⟩

private theorem exact_expected_inputs : expected.rawInputs ++ expected.inputs = [
    {identifier := "%input_enabled", visibility := .«public», ty := .bool},
    {identifier := "%input_saved", visibility := .«public», ty := .native,
      activityGuard := some (.input "%input_enabled")} ] := by
  with_unfolding_all rfl

private theorem input_bounds : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
    requirement.ty.isForeign = _root_.Bool.false →
      requirement.canonicalJubjubScalar = _root_.Bool.false →
      (assignment requirement.identifier).val ≤ Backend.Native.sourceMaximum requirement.ty := by
  intro requirement present _ _
  rw [exact_expected_inputs] at present
  simp at present
  rcases present with rfl | rfl <;> decide +kernel

private def expectedFrame : OutputFrame :=
  ([ ("prepared", .constant 7),
     ("enabled", .input "%input_enabled"),
     ("saved", .input "%input_saved") ], [], [])

private theorem normalized_frame :
    normalizeOutputs (entrypointSeedAliases fixtureEntry plan) fixtureEntry.circuit.outputs =
      .ok expectedFrame := by
  with_unfolding_all rfl

private theorem circuit_run :
    fixtureEntry.circuit.run context values = .ok [("prepared", .native 7)] := by
  with_unfolding_all rfl

private theorem decoded_reads : decodeReads reads assignment =
    .ok [("saved", .native 41)] := by
  with_unfolding_all rfl

theorem guarded_candidate_frame_exact :
    ∃ frame,
      normalizeOutputs (entrypointSeedAliases fixtureEntry plan) fixtureEntry.circuit.outputs =
        .ok frame ∧
      frame.1 = expectedFrame.1 ∧
      fixtureEntry.circuit.run context values = .ok [("prepared", .native 7)] ∧
      decodeReads reads assignment = .ok [("saved", .native 41)] ∧
      TypedEnvironment hash assignment frame.1
        (([("prepared", .native 7)] ++ values) ++ [("saved", .native 41)])
        (plan.typeEnvironment fixtureEntry) := by
  obtain ⟨frame, result, candidates, normalized, executed, decoded, environment, aliases⟩ :=
    GuardedScalarCandidateSchedule.expected_candidate_frame state fixtureEntry expected plan
      context hash hash_agrees values assignment plan_accepted expected_accepted canonical_inputs
      circuit_admitted plain_reads separate_reads distinct_reads assertions bounds input_bounds
  have frameExact := Except.ok.inj (normalized.symm.trans normalized_frame)
  have resultExact := Except.ok.inj (executed.symm.trans circuit_run)
  have candidatesExact := Except.ok.inj (decoded.symm.trans decoded_reads)
  subst frame
  subst result
  subst candidates
  exact ⟨expectedFrame, normalized_frame, rfl, circuit_run, decoded_reads, environment⟩

end GuardedScalarCandidateFrameProof
