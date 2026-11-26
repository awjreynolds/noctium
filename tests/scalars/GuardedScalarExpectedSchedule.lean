import Noctium.Frontend
import Noctium.Verification.GuardedImpactTranscript
import Noctium.Verification.GuardedScalarSchedule
import Noctium.Verification.ScalarGuardedPlanAdmission

open scoped Noctium
open Noctium
open Noctium.Verification
open Noctium.Verification.NativeRelation
open Noctium.Verification.NativeState
open Noctium.Verification.GuardedImpactObservation
open Noctium.Verification.GuardedImpactTranscript

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

private def assignmentFor (enabled : _root_.Bool) : Assignment := fun identifier =>
  match identifier with
  | "%input_enabled" => scalar (if enabled then 1 else 0)
  | "%input_saved" => scalar 41
  | _ => zero

private def valuesFor (enabled : _root_.Bool) : EvalEnv := [
  ("enabled", .bool enabled),
  ("saved", .native 41)
]

private def assignment : Assignment := assignmentFor _root_.Bool.true

private def values : EvalEnv := valuesFor _root_.Bool.true

private def disabledAssignment : Assignment := assignmentFor _root_.Bool.false

private def disabledValues : EvalEnv := valuesFor _root_.Bool.false

private theorem bool_canonical (enabled : _root_.Bool) : Canonical .bool enabled := by
  cases enabled
  ·
    unfold Canonical
    simp only [sourceNumber?]
    change 0 < Field.modulus ∧ True
    exact ⟨by decide +kernel, trivial⟩
  ·
    unfold Canonical
    simp only [sourceNumber?]
    change 1 < Field.modulus ∧ True
    exact ⟨by decide +kernel, trivial⟩

private theorem enabled_meaning (enabled : _root_.Bool) :
    interpret hash (assignmentFor enabled) (.input "%input_enabled") =
      sourceScalar? .bool enabled := by
  cases enabled <;>
    simp [interpret, assignmentFor, sourceScalar?, sourceNumber?]

private theorem typed_environment_for (enabled : _root_.Bool) :
    TypedEnvironment hash (assignmentFor enabled) aliases (valuesFor enabled)
      (plan.typeEnvironment fixtureEntry) := by
  have empty : TypedEnvironment hash (assignmentFor enabled) [] [] [] := by
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
  have savedMeaning : interpret hash (assignmentFor enabled) (.input "%input_saved") =
      sourceScalar? .native 41 := by
    simp [interpret, assignmentFor, sourceScalar?, sourceNumber?]
  have savedEnvironment := TypedEnvironment.cons hash (assignmentFor enabled) [] [] [] empty
    "saved" .native 41 (.input "%input_saved") savedCanonical savedMeaning
  have stacked := TypedEnvironment.cons hash (assignmentFor enabled)
    [("saved", .input "%input_saved")] [("saved", .native 41)] [("saved", .native)]
    savedEnvironment "enabled" .bool enabled (.input "%input_enabled")
    (bool_canonical enabled) (enabled_meaning enabled)
  change TypedEnvironment hash (assignmentFor enabled) outputFrame.1 (valuesFor enabled)
    (plan.typeEnvironment fixtureEntry)
  rw [exact_normalized_output_aliases, exact_plan_types]
  exact stacked

private theorem typed_environment :
    TypedEnvironment hash assignment aliases values (plan.typeEnvironment fixtureEntry) := by
  simpa [assignment, values] using typed_environment_for _root_.Bool.true

private theorem disabled_typed_environment :
    TypedEnvironment hash disabledAssignment aliases disabledValues
      (plan.typeEnvironment fixtureEntry) := by
  simpa [disabledAssignment, disabledValues] using typed_environment_for _root_.Bool.false

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

private theorem boundsCheckedFor (enabled : _root_.Bool) :
    ∀ requirement ∈ expected.bounds,
      ∃ value, interpret hash (assignmentFor enabled) requirement.1 = some value ∧
        value.val ≤ requirement.2 := by
  intro requirement boundIn
  rw [exact_expected_bounds] at boundIn
  have same : requirement = (Term.input "%input_enabled", 1) := by
    simpa using boundIn
  cases same
  cases enabled
  · exact ⟨scalar 0, by simp [interpret, assignmentFor], by decide⟩
  · exact ⟨scalar 1, by simp [interpret, assignmentFor], by decide⟩

private theorem boundsChecked : ∀ requirement ∈ expected.bounds,
    ∃ value, interpret hash assignment requirement.1 = some value ∧ value.val ≤ requirement.2 := by
  simpa [assignment] using boundsCheckedFor _root_.Bool.true

private theorem assertionsChecked : ∀ assertion ∈ expected.assertions,
    interpret hash assignment assertion = some one := by
  intro assertion assertionIn
  rw [exact_expected_assertions] at assertionIn
  simp at assertionIn

private theorem disabledBoundsChecked : ∀ requirement ∈ expected.bounds,
    ∃ value, interpret hash disabledAssignment requirement.1 = some value ∧
      value.val ≤ requirement.2 := by
  simpa [disabledAssignment] using boundsCheckedFor _root_.Bool.false

private theorem disabledAssertionsChecked : ∀ assertion ∈ expected.assertions,
    interpret hash disabledAssignment assertion = some one := by
  intro assertion assertionIn
  rw [exact_expected_assertions] at assertionIn
  simp at assertionIn

private def enabledObservations : List Observation :=
  (expectedObservations hash assignment expected).getD []

private def tapeTerms : List (List Term) :=
  let field := Term.constant (Field.modulus - 2)
  let gate := Term.input "%input_enabled"
  [[.constant 16, .constant 1, .constant 1, field, gate],
   [.constant 12, .constant 1, field, gate],
   [.constant 112, .constant 1, field, .constant 0],
   [.constant 16, .constant 1, .constant 1, field, .constant 17],
   [.constant 17, .constant 1, .constant 1, field, .constant 41],
   [.constant 146], [.constant 48],
   [.constant 81, .constant 1, field, .constant 0, .constant 1, field, .constant 17],
   [.constant 12, .constant 1, field, .input "%input_saved"]]

private def tapeGuards : List Term :=
  let gate := Term.input "%input_enabled"
  [.constant 1, .constant 1, gate, gate, gate, gate,
    .constant 1, .constant 1, .constant 1]

private theorem exact_tape_groups : expected.groups = tapeTerms := by
  with_unfolding_all rfl

private theorem exact_tape_guards : expected.groupGuards = tapeGuards := by
  with_unfolding_all rfl

private theorem enabled_observations_isSome :
    (expectedObservations hash assignment expected).isSome = _root_.Bool.true := by
  unfold expectedObservations
  rw [exact_tape_groups, show List.range tapeTerms.length = [0, 1, 2, 3, 4, 5, 6, 7, 8] from rfl]
  simp [expectedObservationAt, ScalarValidationOutputMeaning.sourceImpactGuard,
    exact_tape_groups, exact_tape_guards, tapeTerms, tapeGuards, sourceObservation, interpret,
    assignment, assignmentFor, observeImpact,
    List.mapM_cons, Bind.bind, Option.bind, Pure.pure, scalar_one]

private theorem enabled_observations_checked :
    expectedObservations hash assignment expected = some enabledObservations := by
  have isSome := enabled_observations_isSome
  cases result : expectedObservations hash assignment expected with
  | none => simp [result] at isSome
  | some observations => simp [enabledObservations, result]

private def disabledObservations : List Observation :=
  (expectedObservations hash disabledAssignment expected).getD []

private theorem disabled_observations_checked :
    expectedObservations hash disabledAssignment expected = some disabledObservations := by
  have isSome : (expectedObservations hash disabledAssignment expected).isSome = _root_.Bool.true := by
    unfold expectedObservations
    rw [exact_tape_groups,
      show List.range tapeTerms.length = [0, 1, 2, 3, 4, 5, 6, 7, 8] from rfl]
    simp [expectedObservationAt, ScalarValidationOutputMeaning.sourceImpactGuard,
      exact_tape_groups, exact_tape_guards, tapeTerms, tapeGuards, sourceObservation,
      interpret, disabledAssignment, assignmentFor, observeImpact,
      List.mapM_cons, Bind.bind, Option.bind, Pure.pure, scalar_one, zero_ne_one]
  cases result : expectedObservations hash disabledAssignment expected with
  | none => simp [result] at isSome
  | some observations => simp [disabledObservations, result]

private theorem disabled_expected_active_groups_exact :
    (disabledObservations.filter (·.active)).map (·.payload) = [
      [scalar 0x10, one, one, scalar (Field.modulus - 2), zero],
      [scalar 0x0c, one, scalar (Field.modulus - 2), zero],
      [scalar 0x30],
      [scalar 0x51, one, scalar (Field.modulus - 2), zero,
        one, scalar (Field.modulus - 2), scalar 17],
      [scalar 0x0c, one, scalar (Field.modulus - 2), scalar 41]
    ] := by
  unfold disabledObservations expectedObservations
  rw [exact_tape_groups,
    show List.range tapeTerms.length = [0, 1, 2, 3, 4, 5, 6, 7, 8] from rfl]
  simp [expectedObservationAt, ScalarValidationOutputMeaning.sourceImpactGuard,
    exact_tape_groups, exact_tape_guards, tapeTerms, tapeGuards, sourceObservation,
    interpret, disabledAssignment, assignmentFor, observeImpact,
    List.mapM_cons, Bind.bind, Option.bind, Pure.pure, scalar_one, zero_ne_one]

private theorem scalar_reads_admitted :
    ∀ scalarRead ∈ (plan.reads.drop
      (Backend.Impact.publicInputReadCount fixtureEntry.circuit.inputs)).flatMap
        Backend.Impact.Read.scalarReads,
      scalarAliasReadType scalarRead.ty := by
  have exactReads :
      (plan.reads.drop
        (Backend.Impact.publicInputReadCount fixtureEntry.circuit.inputs)).flatMap
          Backend.Impact.Read.scalarReads =
        [({name := "saved", ty := .native} : Backend.Impact.Read)] := by
    with_unfolding_all rfl
  intro scalarRead readIn
  rw [exactReads] at readIn
  rcases List.mem_singleton.mp readIn with rfl
  exact Or.inl rfl

theorem guarded_map_expected_schedule :
    ∃ operations, GenericStateOps.evalPlan context values plan = .ok operations ∧
      expected.groups.map (List.map (interpret hash assignment)) =
        (NativeState.groups operations).map (List.map some) := by
  exact ScalarGuardedPlanAdmission.lower_expected_scalar_schedule state fixtureEntry expected plan
    outputFrame aliases context hash hash_agrees assignment values typed_environment
    expected_accepted plan_accepted normalized_output read_aliases compatible
    effects_admitted guards_admitted boundsChecked assertionsChecked

theorem guarded_map_enabled_active_schedule :
    ∃ active, GuardedPlanExecution.evalPlan context values plan = .ok active ∧
      NativeState.groups active =
        (enabledObservations.filter (·.active)).map (·.payload) := by
  exact GuardedScalarSchedule.lower_active_scalar_schedule state fixtureEntry expected plan
    outputFrame context hash hash_agrees assignment values typed_environment
    expected_accepted plan_accepted normalized_output read_aliases compatible effects_admitted
    guards_admitted scalar_reads_admitted boundsChecked assertionsChecked
    enabled_observations_checked

theorem guarded_map_disabled_active_schedule :
    ∃ active, GuardedPlanExecution.evalPlan context disabledValues plan = .ok active ∧
      NativeState.groups active = [
        [scalar 0x10, one, one, scalar (Field.modulus - 2), zero],
        [scalar 0x0c, one, scalar (Field.modulus - 2), zero],
        [scalar 0x30],
        [scalar 0x51, one, scalar (Field.modulus - 2), zero,
          one, scalar (Field.modulus - 2), scalar 17],
        [scalar 0x0c, one, scalar (Field.modulus - 2), scalar 41]
      ] := by
  obtain ⟨active, evaluated, groups⟩ :=
    GuardedScalarSchedule.lower_active_scalar_schedule state fixtureEntry expected plan
    outputFrame context hash hash_agrees disabledAssignment disabledValues
    disabled_typed_environment expected_accepted plan_accepted normalized_output read_aliases
    compatible effects_admitted guards_admitted scalar_reads_admitted disabledBoundsChecked
    disabledAssertionsChecked disabled_observations_checked
  exact ⟨active, evaluated, groups.trans disabled_expected_active_groups_exact⟩

theorem guarded_map_malformed_activity_count_rejected :
    GuardedPlanExecution.evalPlan context values
      {plan with activityGuards := [none]} =
        .error "Impact operation activity guard count mismatch" := by
  with_unfolding_all rfl

#guard (aliases.lookup "saved" == some (.input "%input_saved"))
#guard (outputFrame.2.1 == [] && outputFrame.2.2 == [])

end GuardedScalarExpectedScheduleProof
