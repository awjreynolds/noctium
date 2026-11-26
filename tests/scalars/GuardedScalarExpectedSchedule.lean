import Noctium.Frontend
import Noctium.Verification.ScalarGuardedPlanAdmission

open scoped Noctium
open Noctium
open Noctium.Verification
open Noctium.Verification.NativeRelation
open Noctium.Verification.NativeState

noctium_circuit guardedScalarScheduleInputs where
  public enabled : Bool
end

noctium_contract GuardedScalarExpectedSchedule where
  map balances : Native => Native

  entry guardedRoundTrip uses guardedScalarScheduleInputs where
    when enabled insert balances[17] := 41
    read balances[17] as saved
    return result : Native := 7
  end
end

namespace GuardedScalarExpectedScheduleProof

open Noctium.Backend.Native
open Noctium.Verification.GenericStateCircuitParts
open Noctium.Verification.ScalarNormalization
open Noctium.Verification.ScalarOperationSyntax
open Noctium.Verification.ScalarGuardedPlanAdmission (ScalarEffect)

private def fixtureEntry : Entrypoint :=
  (GuardedScalarExpectedSchedule.entrypoints.find? (·.name == "guardedRoundTrip")).getD
    {name := "missing", circuit := {name := "missing"}}

private def state : List StateDecl := GuardedScalarExpectedSchedule.state

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

private def guardedAbsence : Entrypoint := {
  fixtureEntry with
  effects := [.requireAbsent "balances" .native (.native 17)]
  effectGuards := [some (.ref "enabled")]
  returns := []
}

private theorem guarded_absence_exact_rejection :
    (Backend.Impact.lower state guardedAbsence).mapError (·.message) =
      .error "native guards are supported only on ledger reads, writes, and require effects" := by
  with_unfolding_all rfl

private def outputFrame : OutputFrame :=
  match normalizeOutputs (entrypointSeedAliases fixtureEntry plan) fixtureEntry.circuit.outputs with
  | .ok frame => frame
  | .error _ => ([], [], [])

private theorem normalized_output :
    normalizeOutputs (entrypointSeedAliases fixtureEntry plan) fixtureEntry.circuit.outputs =
      .ok outputFrame := by
  with_unfolding_all rfl

private def aliases : AliasEnvironment := outputFrame.1

private theorem exact_normalized_output_aliases :
    outputFrame.1 = [
      ("enabled", .input "%input_enabled"),
      ("saved", .input "%input_saved")
    ] := by
  with_unfolding_all rfl

private theorem exact_normalized_output_frame :
    outputFrame = (
      [("enabled", .input "%input_enabled"),
       ("saved", .input "%input_saved")], [], []) := by
  with_unfolding_all rfl

private theorem read_aliases :
    forIn ((plan.reads.drop (Backend.Impact.publicInputReadCount fixtureEntry.circuit.inputs)).flatMap
      Backend.Impact.Read.scalarReads) outputFrame.1 (readAliasStep fixtureEntry) = .ok aliases := by
  with_unfolding_all rfl

private theorem exact_plan_types :
    plan.typeEnvironment fixtureEntry = [("enabled", .bool), ("saved", .native)] := by
  with_unfolding_all rfl

private def context : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .ok zero
}

private def hash : Hash := fun _ => zero

private theorem hash_agrees : HashAgreement context hash := by
  constructor <;> simp [context, hash]

private def assignment : Assignment := fun identifier =>
  match identifier with
  | "%input_enabled" => scalar 1
  | "%input_saved" => scalar 41
  | _ => zero

private def values : EvalEnv := [
  ("enabled", .bool _root_.Bool.true),
  ("saved", .native 41)
]

private theorem typed_environment :
    TypedEnvironment hash assignment aliases values (plan.typeEnvironment fixtureEntry) := by
  have empty : TypedEnvironment hash assignment [] [] [] := by
    constructor
    · intro name ty raw value lookup typed
      simp at lookup
    · intro name ty lookup
      simp at lookup
  have savedCanonical : Canonical .native 41 := by
    unfold Canonical
    simp only [sourceNumber?]
    change 41 < Field.modulus ∧ True
    exact ⟨by decide +kernel, trivial⟩
  have savedMeaning : interpret hash assignment (.input "%input_saved") =
      sourceScalar? .native 41 := by
    simp [interpret, assignment, sourceScalar?, sourceNumber?]
  have savedEnvironment := TypedEnvironment.cons hash assignment [] [] [] empty
    "saved" .native 41 (.input "%input_saved") savedCanonical savedMeaning
  have enabledCanonical : Canonical .bool _root_.Bool.true := by
    unfold Canonical
    simp only [sourceNumber?]
    change 1 < Field.modulus ∧ True
    exact ⟨by decide +kernel, trivial⟩
  have enabledMeaning : interpret hash assignment (.input "%input_enabled") =
      sourceScalar? .bool _root_.Bool.true := by
    simp [interpret, assignment, sourceScalar?, sourceNumber?]
  have stacked := TypedEnvironment.cons hash assignment
    [("saved", .input "%input_saved")] [("saved", .native 41)] [("saved", .native)]
    savedEnvironment "enabled" .bool _root_.Bool.true (.input "%input_enabled")
    enabledCanonical enabledMeaning
  change TypedEnvironment hash assignment outputFrame.1 values
    (plan.typeEnvironment fixtureEntry)
  rw [exact_normalized_output_aliases, exact_plan_types]
  exact stacked

private theorem compatible :
    ∀ input ∈ fixtureEntry.circuit.inputs, Backend.Impact.publicInputScalarCompatible input := by
  intro input inputIn
  simp [fixtureEntry, GuardedScalarExpectedSchedule, guardedScalarScheduleInputs] at inputIn
  subst input
  simp [Backend.Impact.publicInputScalarCompatible]

private theorem effects_admitted :
    ∀ effect ∈ fixtureEntry.effects, ScalarEffect state effect := by
  intro effect effectIn
  simp [fixtureEntry, GuardedScalarExpectedSchedule, guardedScalarScheduleInputs] at effectIn
  rcases effectIn with writeEffect | readEffect
  · cases writeEffect
    exact .writeMap "balances" .native .native (.native 17) (.native 41)
      .native .native (.native 17) (.native 41)
  · cases readEffect
    exact .readMap "balances" "saved" .native .native (.native 17)
      .native .native (.native 17)

private theorem guards_admitted :
    ∀ condition, some condition ∈ fixtureEntry.effectGuards → ScalarExpression condition := by
  intro condition conditionIn
  simp [fixtureEntry, GuardedScalarExpectedSchedule, guardedScalarScheduleInputs] at conditionIn
  subst condition
  exact .ref "enabled" .bool

private theorem exact_expected_bounds :
    expected.bounds = List.replicate 8 (Term.input "%input_enabled", 1) := by
  with_unfolding_all rfl

private theorem exact_expected_assertions : expected.assertions = [] := by
  with_unfolding_all rfl

private theorem boundsChecked : ∀ requirement ∈ expected.bounds,
    ∃ value, interpret hash assignment requirement.1 = some value ∧ value.val ≤ requirement.2 := by
  intro requirement boundIn
  rw [exact_expected_bounds] at boundIn
  have same : requirement = (Term.input "%input_enabled", 1) := by
    simpa using boundIn
  cases same
  exact ⟨scalar 1, by simp [interpret, assignment], by decide⟩

private theorem assertionsChecked : ∀ assertion ∈ expected.assertions,
    interpret hash assignment assertion = some one := by
  intro assertion assertionIn
  rw [exact_expected_assertions] at assertionIn
  simp at assertionIn

theorem guarded_map_expected_schedule :
    ∃ operations, GenericStateOps.evalPlan context values plan = .ok operations ∧
      expected.groups.map (List.map (interpret hash assignment)) =
        (NativeState.groups operations).map (List.map some) := by
  exact ScalarGuardedPlanAdmission.lower_expected_scalar_schedule state fixtureEntry expected plan
    outputFrame aliases context hash hash_agrees assignment values typed_environment
    expected_accepted plan_accepted normalized_output read_aliases compatible
    effects_admitted guards_admitted boundsChecked assertionsChecked

#guard (aliases.lookup "saved" == some (.input "%input_saved"))
#guard (outputFrame.2.1 == [] && outputFrame.2.2 == [])

end GuardedScalarExpectedScheduleProof
