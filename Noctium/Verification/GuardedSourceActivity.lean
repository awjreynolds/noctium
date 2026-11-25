import Noctium.Verification.GuardedStatementConsumption
import Noctium.Verification.GuardedStatementWidths
import Noctium.Verification.ImpactTranscriptSchedule
import Noctium.Verification.ScalarImpactOperationMeaning

namespace Noctium.Verification.GuardedSourceActivity

open Backend NativeRelation ScalarNormalization
open GenericStateCircuitParts GuardedImpactObservation GuardedImpactTranscript

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- Normalization preserves the activity of every source field group, in order.
An absent guard is the unconditional native field constant. -/
private theorem normalize_guards_eval (ep : Entrypoint) (ctx : EvalContext)
    (hash : Hash) (inputs : Assignment) (aliases : Native.AliasEnvironment)
    (env : EvalEnv) (types : TypeEnv)
    (implementation : HashAgreement ctx hash)
    (environment : TypedEnvironment hash inputs aliases env types)
    (sources : List (Option (Expr .bool))) (terms : List Native.Normalized)
    (admitted : ∀ guard, some guard ∈ sources →
      ScalarExpression guard ∧ guard.validate Capabilities.scalarFragment types = .ok ())
    (normalized : sources.mapM (normalizeActivityGuard ep aliases) = .ok terms)
    (requirements : ∀ item ∈ terms, Requirements hash inputs item) :
    ∃ activities : List (Option _root_.Bool),
      sources.mapM (GuardedPlanExecution.evalActivity ctx env) = .ok activities ∧
      activities.length = sources.length ∧
      terms.map (fun item => interpret hash inputs item.term) =
        activities.map (fun activity => some (bit (activity.getD _root_.Bool.true))) := by
  induction sources generalizing terms with
  | nil =>
    cases normalized
    exact ⟨[], rfl, rfl, rfl⟩
  | cons source rest ih =>
    simp only [List.mapM_cons, bind_ok] at normalized
    obtain ⟨term, head, tail, tailAccepted, joined⟩ := normalized
    cases joined
    obtain ⟨activities, restEvaluated, length, restMeaning⟩ := ih tail
      (fun guard inside => admitted guard (List.mem_cons_of_mem _ inside))
      tailAccepted (fun item inside => requirements item (List.mem_cons_of_mem _ inside))
    have evaluated : ∃ activity,
        GuardedPlanExecution.evalActivity ctx env source = .ok activity ∧
        interpret hash inputs term.term = some (bit (activity.getD _root_.Bool.true)) := by
      cases source with
      | none =>
        cases head
        refine ⟨none, rfl, ?_⟩
        change ScalarTermMeaning.interpret? hash inputs (.constant 1) = _
        rw [ScalarTermMeaning.interpret_constant]
        exact congrArg some (Fin.ext (by decide))
      | some guard =>
        have normal : Native.normalize aliases guard = .ok term :=
          (Native.convert_ok ep.span _ term).mp
            (by simpa [normalizeActivityGuard, Native.convert_eq_mapError] using head)
        obtain ⟨allowed, valid⟩ := admitted guard (by simp)
        obtain ⟨value, found, _, _, meaning⟩ :=
          normalize_sound ctx hash implementation inputs types aliases env environment guard
            allowed term valid normal (requirements term (by simp))
        refine ⟨some value, ?_, ?_⟩
        · simp [GuardedPlanExecution.evalActivity, Option.mapM, found, Functor.map, Except.map]
        · rw [meaning]
          cases value <;> rfl
    obtain ⟨activity, headEvaluated, headMeaning⟩ := evaluated
    refine ⟨activity :: activities, ?_, by simp [length], ?_⟩
    · simp only [List.mapM_cons, headEvaluated, restEvaluated]
      rfl
    · simp only [List.map_cons, headMeaning, restMeaning]

private theorem mapM_option_frame (f : α → Option β) {items : List α} {results : List β}
    (evaluated : items.mapM f = some results) :
    results.length = items.length ∧ ∀ index : Nat, results[index]? = (items[index]?.bind f) := by
  induction items generalizing results with
  | nil => cases evaluated; exact ⟨rfl, fun _ => rfl⟩
  | cons item rest ih =>
    simp only [List.mapM_cons, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
      Option.some.injEq] at evaluated
    obtain ⟨head, first, tail, next, exactList⟩ := evaluated
    cases exactList
    obtain ⟨length, indexed⟩ := ih next
    refine ⟨by simp [length], ?_⟩
    intro index
    cases index with
    | zero => simpa using first.symm
    | succ index => exact indexed index

private def groupActivity (active : Option _root_.Bool) (width : Nat) : Option Nat :=
  if active.getD _root_.Bool.true then none else some width

private theorem evaluate_groups (ctx : EvalContext) (env : EvalEnv)
    (sources : List (Option (Expr .bool))) (activities : List (Option _root_.Bool))
    (widths : List Nat)
    (evaluated : sources.mapM (GuardedPlanExecution.evalActivity ctx env) = .ok activities) :
    (sources.zip widths).mapM (fun (source, width) =>
      (GuardedPlanExecution.evalActivity ctx env source).toOption.map
        (fun active => groupActivity active width)) =
      some (List.zipWith groupActivity activities widths) := by
  induction sources generalizing activities widths with
  | nil => cases evaluated; rfl
  | cons head rest ih =>
    simp only [List.mapM_cons, bind_ok] at evaluated
    obtain ⟨active, first, tail, next, exactList⟩ := evaluated
    cases exactList
    cases widths with
    | nil => rfl
    | cons width widths =>
      rw [List.zip_cons_cons, List.mapM_cons, ih tail widths next, List.zipWith_cons_cons]
      simp [first, Except.toOption]

private theorem sourceGuard_mem {plan : Impact.Plan} {guard : Expr .bool}
    (inside : some guard ∈ activityGuardSources plan) : some guard ∈ plan.activityGuards := by
  unfold activityGuardSources at inside
  split at inside
  · simp at inside
  · obtain ⟨⟨_, source⟩, present, replicated⟩ := List.mem_flatMap.mp inside
    have same : some guard = source := (List.mem_replicate.mp replicated).2
    rw [same]
    exact List.of_mem_zip present |>.2

private theorem observation_shapes (hash : Hash) (inputs : Assignment)
    (expected : Native.Expected) (observations : List Observation)
    (activities : List (Option _root_.Bool))
    (guardMeaning : expected.groupGuards.map (interpret hash inputs) =
      activities.map (fun activity => some (bit (activity.getD _root_.Bool.true))))
    (aligned : activities.length = expected.groups.length)
    (observed : expectedObservations hash inputs expected = some observations) :
    observations.map (fun observation => (observation.active, observation.payload.length)) =
      List.zipWith (fun activity width => (activity.getD _root_.Bool.true, width))
        activities (expected.groups.map List.length) := by
  obtain ⟨obsLength, observationAt⟩ := mapM_option_frame _ observed
  have lengths : expected.groupGuards.length = activities.length := by
    simpa using congrArg List.length guardMeaning
  apply List.ext_getElem?
  intro index
  by_cases inside : index < expected.groups.length
  · have activityInside : index < activities.length := by simpa [aligned] using inside
    have guardInside : index < expected.groupGuards.length := by simpa [lengths] using activityInside
    let activity := activities[index]
    let guard := expected.groupGuards[index]
    let group := expected.groups[index]
    have scheduled : expected.groupGuards.isEmpty = _root_.Bool.false := by
      cases groups : expected.groupGuards with
      | nil => simp [groups] at guardInside
      | cons => rfl
    have term : interpret hash inputs guard = some (bit (activity.getD _root_.Bool.true)) := by
      have value := congrArg (fun list : List (Option Scalar) => list[index]?) guardMeaning
      simpa only [List.getElem?_map, List.getElem?_eq_getElem guardInside,
        List.getElem?_eq_getElem activityInside, Option.map_some, Option.some.injEq] using value
    have atIndex := observationAt index
    rw [List.getElem?_range inside] at atIndex
    change observations[index]? = expectedObservationAt hash inputs expected index at atIndex
    simp only [expectedObservationAt, ScalarValidationOutputMeaning.sourceImpactGuard,
      scheduled, Bool.false_eq_true, ite_false, List.getElem?_eq_getElem guardInside,
      List.getElem?_eq_getElem inside, Bind.bind, Option.bind_some] at atIndex
    change observations[index]? = sourceObservation hash inputs guard group at atIndex
    have obsInside : index < observations.length := by simpa [obsLength] using inside
    have existsObs : observations[index]? = some observations[index] :=
      List.getElem?_eq_getElem obsInside
    cases payload : group.mapM (interpret hash inputs) with
    | none => simp [sourceObservation, term, payload, existsObs] at atIndex
    | some fields =>
      have width := (mapM_option_frame _ payload).1
      simp only [sourceObservation, term, payload, Bind.bind, Option.bind_some] at atIndex
      simp only [List.getElem?_map,
        List.getElem?_zipWith, List.getElem?_eq_getElem activityInside, List.getElem?_eq_getElem inside,
        atIndex, Option.map_some]
      change (observeImpact (bit (activity.getD _root_.Bool.true)) fields).map _ =
        some (activity.getD _root_.Bool.true, group.length)
      cases activity.getD _root_.Bool.true <;>
        simp [bit, observeImpact_active, observeImpact_inactive, width]
  · have obsOutside : observations.length ≤ index := by simpa [obsLength] using Nat.le_of_not_gt inside
    simp [List.getElem?_zipWith,
      List.getElem?_eq_none obsOutside, List.getElem?_eq_none (Nat.le_of_not_gt inside)]

/-- The checked ZKIR rows follow the exact Impact plan's activity and field
widths. Each active group retains the width of the native operation at that ordinal. -/
theorem lower_observations_activity (state : List StateDecl) (ep : Entrypoint)
    (ctx : EvalContext) (hash : Hash) (inputs : Assignment) (env : EvalEnv)
    (implementation : HashAgreement ctx hash)
    (plan : Impact.Plan) (expected : Native.Expected) (frame : OutputFrame)
    (observations : List Observation) (native : List NativeState.Op)
    (evaluatedNative : GuardedPlanExecution.evalPlan ctx env plan = .ok native)
    (planAccepted : Impact.lower state ep = .ok plan)
    (expectedAccepted : Native.expectedEntrypoint state ep = .ok expected)
    (frameAccepted : normalizeOutputs (entrypointSeedAliases ep plan)
      ep.circuit.outputs = .ok frame)
    (environment : TypedEnvironment hash inputs frame.1 env (plan.typeEnvironment ep))
    (reads : ∀ readSpec ∈
      (plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)).flatMap
        Impact.Read.scalarReads, scalarAliasReadType readSpec.ty)
    (guardAdmission : ∀ guard, some guard ∈ plan.activityGuards → ScalarExpression guard)
    (single : ∀ op ∈ plan.operations, op.fieldGroups = [op.fields])
    (assertions : ∀ term ∈ expected.assertions, interpret hash inputs term = some one)
    (bounds : ∀ bound ∈ expected.bounds,
      ∃ value, interpret hash inputs bound.1 = some value ∧ value.val ≤ bound.2)
    (observed : expectedObservations hash inputs expected = some observations) :
    (plan.operations.zipIdx.mapM (ImpactTranscriptSchedule.sourceGroups ctx env plan)).map
      List.flatten = some (GuardedStatementConsumption.observationActivity observations) ∧
    native.map (fun op => (ImpactStatementScalar.opFields op).length) =
      (observations.filter (·.active)).map (fun row => row.payload.length) := by
  obtain ⟨activityFrame, terms, activityFrameAccepted, normalized, guardShape,
    guardAssertions, guardBounds⟩ :=
    expectedEntrypoint_activity state ep expected plan planAccepted expectedAccepted reads
  have sameFrame := Except.ok.inj (activityFrameAccepted.symm.trans frameAccepted)
  subst activityFrame
  obtain ⟨operationFrame, operationBounds, operationAssertions, operationFrameAccepted,
    collected, _, _⟩ :=
    expectedEntrypoint_operations state ep expected plan planAccepted expectedAccepted reads
  have sameFrame := Except.ok.inj (operationFrameAccepted.symm.trans frameAccepted)
  subst operationFrame
  have widths := ScalarImpactOperationMeaning.collectOperations_group_widths ep.span frame.1
    plan.operations frame.2.1 expected.groups operationBounds operationAssertions collected
  obtain ⟨aligned, guardValid⟩ := plan.validate_activity_success ep
    (Impact.lower_validated state ep plan planAccepted)
  obtain ⟨activities, evaluated, activityLength, termMeaning⟩ := normalize_guards_eval
    ep ctx hash inputs frame.1 env (plan.typeEnvironment ep) implementation environment
    (activityGuardSources plan) terms (fun guard inside =>
      ⟨guardAdmission guard (sourceGuard_mem inside), guardValid guard (sourceGuard_mem inside)⟩)
    normalized (fun item inside =>
      ⟨fun bound present => bounds bound (guardBounds bound (List.mem_flatMap.mpr ⟨item, inside, present⟩)),
       fun term present => assertions term
         (guardAssertions term (List.mem_flatMap.mpr ⟨item, inside, present⟩))⟩)
  have meaning : expected.groupGuards.map (interpret hash inputs) =
      activities.map (fun activity => some (bit (activity.getD _root_.Bool.true))) := by
    simpa only [guardShape, List.map_map, Function.comp_def] using termMeaning
  have widthLength := (congrArg List.length widths)
  have activityAligned : activities.length = expected.groups.length := by
    rw [activityLength, ImpactTranscriptSchedule.sourceGroupGuards_length plan aligned single]
    simpa using widthLength.symm
  have observedShapes := observation_shapes hash inputs expected observations activities
    meaning activityAligned observed
  constructor
  · have observationSchedule := congrArg
      (List.map (fun group : _root_.Bool × Nat => if group.1 then none else some group.2))
      observedShapes
    have observationActivity : GuardedStatementConsumption.observationActivity observations =
        List.zipWith groupActivity activities (expected.groups.map List.length) := by
      change _ = List.zipWith (fun activity width =>
        if activity.getD _root_.Bool.true then none else some width)
        activities (expected.groups.map List.length)
      simpa only [GuardedStatementConsumption.observationActivity, List.map_map, List.map_zipWith,
        Function.comp_def] using observationSchedule
    rw [ImpactTranscriptSchedule.sourceGroups_flatten ctx env plan aligned single]
    have sourceSchedule := evaluate_groups ctx env (activityGuardSources plan) activities
      (plan.operations.flatMap (fun op => op.fieldGroups.map List.length)) evaluated
    rw [← widths] at sourceSchedule
    rw [← widths]
    exact sourceSchedule.trans (congrArg some observationActivity.symm)
  · obtain ⟨_, _, sourceGuards, operationWidths⟩ :=
      ImpactTranscriptSchedule.scalar_source_shapes plan aligned single
    have evaluatedGuards : (GuardedPlanActivity.operationGuards plan).mapM
        (GuardedPlanExecution.evalActivity ctx env) = .ok activities := by
      rw [← sourceGuards]
      exact evaluated
    have opShapes : observations.map (fun row => (row.active, row.payload.length)) =
        (plan.operations.zip activities).map (fun item =>
          (item.2.getD _root_.Bool.true, item.1.fields.length)) := by
      rw [observedShapes, widths, operationWidths, List.map_zip_eq_zipWith,
        List.zipWith_map_right, List.zipWith_comm]
      rfl
    have matchedWidths := congrArg
      (fun groups : List (_root_.Bool × Nat) => (groups.filter Prod.fst).map Prod.snd) opShapes
    have activeWidths := GuardedStatementWidths.evalPlan_active_field_widths ctx env plan
      native evaluatedNative implementation.modulus
      (GenericStateAdmissionBridge.lower_field_admission state ep plan planAccepted)
      activities evaluatedGuards
    rw [activeWidths]
    simpa only [List.filter_map, List.map_map, Function.comp_def] using matchedWidths.symm

end Noctium.Verification.GuardedSourceActivity
