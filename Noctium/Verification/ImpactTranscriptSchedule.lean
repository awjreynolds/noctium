import Noctium.Verification.ImpactNoopPreview
import Noctium.Verification.ImpactPlanAgreement
import Noctium.Verification.ImpactScheduleTraversal
import Noctium.Verification.ImpactScheduledAgreement
import Noctium.Verification.ImpactTranscriptWidth
import Noctium.Verification.GenericStateCircuitParts

namespace Noctium.Verification.ImpactTranscriptSchedule

open Lean Backend ImpactWireDecoder ImpactWireSoundness
open ImpactScheduledAgreement ImpactReferenceEvaluation
open ImpactTranscriptWidth ScalarNormalization

/-- Active groups consume a native operation. Skipped groups retain the width
of the omitted transcript payload without evaluating that payload. -/
def evaluateGroups (fuel : Nat) (ctx : EvalContext) (env : EvalEnv)
    (keyWidth : Nat → Option Nat) (item : ScheduledOperation) : Option (List (Option Nat)) := do
  let activity ← evaluateActivityGuard fuel ctx env item.guard
  if activity.getD Bool.true then some [none]
  else (operationWidth keyWidth item.operation).map fun count => [some count]

/-- Compute the activity metadata for the independently decoded operations.
Active operand evaluation and state execution are checked separately. -/
def evaluateSchedule (fuel : Nat) (ctx : EvalContext) (env : EvalEnv)
    (keyWidth : Nat → Option Nat) (raw : Json) : Option (List (Option Nat)) :=
  (decodePlanOperations raw).toOption.bind fun schedule =>
    (schedule.mapM (evaluateGroups fuel ctx env keyWidth)).map List.flatten

/-- The source group shape comes from the compiler's actual Impact field
groups. Guard failure rejects and a false guard retains the omitted widths. -/
def sourceGroups (ctx : EvalContext) (env : EvalEnv) (plan : Impact.Plan)
    (item : Impact.Op × Nat) : Option (List (Option Nat)) :=
  (GuardedPlanExecution.evalActivity ctx env
    (plan.activityGuards[item.2]?.getD none)).toOption.map fun activity =>
    item.1.fieldGroups.map fun fields =>
      if activity.getD Bool.true then none else some fields.length


private theorem indexed_guards (ops : List Impact.Op) (guards : List (Option (Expr .bool)))
    (aligned : guards.length = ops.length) :
    ops.zipIdx.map (fun item => (item.1, guards[item.2]?.getD none)) = ops.zip guards := by
  apply List.ext_getElem?
  intro i
  by_cases inside : i < ops.length
  · have present : i < guards.length := by simpa [aligned] using inside
    simp [List.getElem?_map, List.getElem?_zipIdx, List.zip,
      List.getElem?_zipWith, List.getElem?_eq_getElem inside, List.getElem?_eq_getElem present]
  · simp [List.getElem?_map, List.getElem?_zipIdx, List.zip,
      List.getElem?_zipWith, List.getElem?_eq_none (Nat.le_of_not_gt inside)]

private theorem flatten_singletons (items : List α) (f : α → Option β) :
    (items.mapM (fun item => (f item).map List.singleton)).map List.flatten = items.mapM f := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.mapM_cons, Bind.bind]
    rw [← ih]
    cases head : f item <;> cases tail : rest.mapM (fun item => (f item).map List.singleton) <;>
      simp [Option.bind, List.singleton]

private theorem flatMap_eq_map {items : List α} {f : α → List β} {g : α → β}
    (pointwise : ∀ item ∈ items, f item = [g item]) : items.flatMap f = items.map g := by
  calc
    items.flatMap f = items.flatMap (fun item => [g item]) :=
      congrArg List.flatten (List.map_congr_left pointwise)
    _ = items.map g := by
      rw [← List.flatMap_map (f := g) (g := fun value => [value]), List.flatMap_singleton']

private theorem mapM_eq_of_members {items : List α} {f g : α → Option β}
    (pointwise : ∀ item ∈ items, f item = g item) : items.mapM f = items.mapM g := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.mapM_cons, pointwise item (by simp),
      ih (fun value inside => pointwise value (List.mem_cons_of_mem _ inside))]

private theorem source_shapes (plan : Impact.Plan)
    (shape : plan.activityGuards.isEmpty = Bool.true ∨
      plan.activityGuards.length = plan.operations.length)
    (single : ∀ op ∈ plan.operations, op.fieldGroups = [op.fields]) :
    let guards := GuardedPlanActivity.operationGuards plan
    guards.length = plan.operations.length ∧
    (∀ i : Nat, guards[i]?.getD none = plan.activityGuards[i]?.getD none) ∧
    GenericStateCircuitParts.activityGuardSources plan = guards ∧
    plan.operations.flatMap (fun op => op.fieldGroups.map List.length) =
      plan.operations.map (fun op => op.fields.length) := by
  have widths :
      plan.operations.flatMap (fun op => op.fieldGroups.map List.length) =
        plan.operations.map (fun op => op.fields.length) := by
    apply flatMap_eq_map
    intro op inside
    rw [single op inside]
    rfl
  dsimp only
  refine ⟨?_, ?_, ?_, widths⟩
  · unfold GuardedPlanActivity.operationGuards
    split
    · simp
    · exact shape.resolve_left (by assumption)
  · intro i
    unfold GuardedPlanActivity.operationGuards
    split
    · rename_i empty
      have nil := List.isEmpty_iff.mp empty
      rw [nil]
      by_cases inside : i < plan.operations.length <;> simp [inside]
    · rfl
  · unfold GenericStateCircuitParts.activityGuardSources GuardedPlanActivity.operationGuards
    split
    · rw [← List.map_const']
      apply flatMap_eq_map
      intro op inside
      simp [single op inside]
    · rename_i notEmpty
      have aligned := shape.resolve_left notEmpty
      calc
        _ = (plan.operations.zip plan.activityGuards).map Prod.snd := by
          apply flatMap_eq_map
          intro pair inside
          simp [single pair.1 (List.of_mem_zip inside).1]
        _ = plan.activityGuards := List.map_snd_zip (Nat.le_of_eq aligned)

/-- Scalar operations contribute one group each. The guard and skip width
come from the same source ordinal as the operation. -/
theorem sourceGroups_flatten
    (ctx : EvalContext) (env : EvalEnv) (plan : Impact.Plan)
    (shape : plan.activityGuards.isEmpty = Bool.true ∨
      plan.activityGuards.length = plan.operations.length)
    (single : ∀ op ∈ plan.operations, op.fieldGroups = [op.fields]) :
    (plan.operations.zipIdx.mapM (sourceGroups ctx env plan)).map List.flatten =
      ((GenericStateCircuitParts.activityGuardSources plan).zip
        (plan.operations.flatMap fun op => op.fieldGroups.map List.length)).mapM
        (fun (guard, width) =>
          (GuardedPlanExecution.evalActivity ctx env guard).toOption.map fun activity =>
            if activity.getD Bool.true then none else some width) := by
  obtain ⟨aligned, guardAt, guards, widths⟩ := source_shapes plan shape single
  let effective := GuardedPlanActivity.operationGuards plan
  let eval (item : Impact.Op × Option (Expr .bool)) : Option (Option Nat) :=
    (GuardedPlanExecution.evalActivity ctx env item.2).toOption.map fun activity =>
      if activity.getD Bool.true then none else some item.1.fields.length
  let selected (item : Impact.Op × Nat) := (item.1, effective[item.2]?.getD none)
  have pointwise : ∀ item ∈ plan.operations.zipIdx,
      sourceGroups ctx env plan item = (eval (selected item)).map List.singleton := by
    intro item inside
    have singleton := single item.1 (List.fst_mem_of_mem_zipIdx inside)
    simp only [sourceGroups, selected, eval, singleton, List.map_cons, List.map_nil,
      Option.map_map, Function.comp_def, List.singleton]
    rw [show effective[item.2]?.getD none = plan.activityGuards[item.2]?.getD none from guardAt item.2]
  rw [mapM_eq_of_members pointwise, flatten_singletons]
  change plan.operations.zipIdx.mapM (eval ∘ selected) = _
  rw [← List.mapM_map]
  have zipped := indexed_guards plan.operations effective aligned
  change (plan.operations.zipIdx.map selected).mapM eval = _
  rw [zipped, guards, widths]
  change (plan.operations.zip effective).mapM eval =
    (effective.zip (plan.operations.map (fun op => op.fields.length))).mapM _
  rw [List.zip_map_right]
  have swap : (effective.zip plan.operations).map Prod.swap = plan.operations.zip effective := by
    rw [List.map_zip_eq_zipWith, List.zipWith_comm]
    rfl
  rw [← swap, List.mapM_map, List.mapM_map]
  rfl

theorem sourceGroupGuards_length (plan : Impact.Plan)
    (shape : plan.activityGuards.isEmpty = Bool.true ∨
      plan.activityGuards.length = plan.operations.length)
    (single : ∀ op ∈ plan.operations, op.fieldGroups = [op.fields]) :
    (GenericStateCircuitParts.activityGuardSources plan).length =
      (plan.operations.flatMap fun op => op.fieldGroups.map List.length).length := by
  obtain ⟨length, _, guards, widths⟩ := source_shapes plan shape single
  simpa [guards, widths] using length

private theorem evaluateGroups_agrees (ctx : EvalContext)
    (modulus : ctx.modulus = Field.modulus)
    {types : TypeEnv} {env : EvalEnv} (typed : TypedScalarEnv types env)
    (keyWidth : Nat → Option Nat) (plan : Impact.Plan) (item : Impact.Op × Nat)
    {projected : Operation} (projects : Projects item.1 projected)
    (keys : ScalarKeyWidths keyWidth item.1)
    (guardAdmitted : ∀ guard, plan.activityGuards[item.2]?.getD none = some guard →
      ScalarExpression guard)
    (guardValid : ∀ guard, plan.activityGuards[item.2]?.getD none = some guard →
      guard.validate Capabilities.scalarFragment types = .ok ()) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel →
      evaluateGroups fuel ctx env keyWidth
        ⟨(plan.activityGuards[item.2]?.getD none).map NativeExpression.toJson, projected⟩ =
        sourceGroups ctx env plan item := by
  have width := operationWidth_projects projects keys
  cases decodedWidth : operationWidth keyWidth projected with
  | none => simp [decodedWidth] at width
  | some count =>
      have groupWidths : item.1.fieldGroups.map List.length = [count] := by
        rw [decodedWidth] at width
        exact (Option.some.inj width).symm
      obtain ⟨minimum, guardAgrees⟩ := evaluateActivityGuard_toJson ctx modulus
        (plan.activityGuards[item.2]?.getD none) guardAdmitted guardValid typed
      refine ⟨minimum, ?_⟩
      intro fuel enough
      unfold evaluateGroups sourceGroups
      rw [guardAgrees fuel enough]
      cases guardResult : GuardedPlanExecution.evalActivity ctx env
          (plan.activityGuards[item.2]?.getD none) with
      | error message => rfl
      | ok activity =>
          cases active : activity.getD Bool.true with
          | «false» =>
              have skips := congrArg (List.map some) groupWidths
              simpa [Except.toOption, active, decodedWidth, Bind.bind, Option.bind,
                List.map_map, Function.comp_def] using skips.symm
          | «true» =>
              have takes := congrArg (List.map (fun _ : Nat => (none : Option Nat))) groupWidths
              simpa [Except.toOption, active, Bind.bind, Option.bind,
                List.map_map, Function.comp_def] using takes.symm

/-- The exact emitted scalar schedule agrees with the compiler field-group
widths at every guarded ordinal, including rejection when a guard fails.
Keyed operations rely on the supplied declared scalar key-width lookup. -/
theorem evaluate_nativePlanJson_agrees
    (profile : TargetProfile) (contractName : Name) (state : List StateDecl)
    (ctor : Option Constructor) (ep : Entrypoint) (plan : Impact.Plan)
    (standaloneFile : _root_.Bool) (projected : Nat → Operation)
    (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    {types : TypeEnv} {env : EvalEnv} (typed : TypedScalarEnv types env)
    (keyWidth : Nat → Option Nat)
    (projects : ∀ op index, (op, index) ∈ plan.operations.zipIdx →
      Projects op (projected index))
    (keys : ∀ op index, (op, index) ∈ plan.operations.zipIdx →
      ScalarKeyWidths keyWidth op)
    (guardsAdmitted : ∀ op index, (op, index) ∈ plan.operations.zipIdx →
      ∀ guard, plan.activityGuards[index]?.getD none = some guard →
        ScalarExpression guard)
    (guardsValid : ∀ op index, (op, index) ∈ plan.operations.zipIdx →
      ∀ guard, plan.activityGuards[index]?.getD none = some guard →
        guard.validate Capabilities.scalarFragment types = .ok ()) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel →
      evaluateSchedule fuel ctx env keyWidth
          (Compiler.nativePlanJson profile contractName state ctor ep plan standaloneFile) =
        (plan.operations.zipIdx.mapM (sourceGroups ctx env plan)).map List.flatten := by
  let wireItem (item : Impact.Op × Nat) : ScheduledOperation :=
    ⟨(plan.activityGuards[item.2]?.getD none).map NativeExpression.toJson, projected item.2⟩
  have guardNonNull (op : Impact.Op) (index : Nat)
      (inside : (op, index) ∈ plan.operations.zipIdx) :
      ∀ guard, plan.activityGuards[index]?.getD none = some guard →
        (NativeExpression.toJson guard).isNull = Bool.false := by
    intro guard selected
    exact ImpactExpressionSoundness.toJson_nonNull (guardsAdmitted op index inside guard selected)
  have decoded := decode_nativePlanJson_operations profile contractName state
    ctor ep plan standaloneFile projected projects guardNonNull
  have pointwise (item : Impact.Op × Nat) (inside : item ∈ plan.operations.zipIdx) :
      ∃ minimum, ∀ fuel, minimum ≤ fuel →
        evaluateGroups fuel ctx env keyWidth (wireItem item) =
          sourceGroups ctx env plan item :=
    evaluateGroups_agrees ctx modulus typed keyWidth plan item
      (projects item.1 item.2 inside) (keys item.1 item.2 inside)
      (guardsAdmitted item.1 item.2 inside) (guardsValid item.1 item.2 inside)
  obtain ⟨minimum, agrees⟩ :=
    ImpactScheduleTraversal.mapM_eventually_agrees plan.operations.zipIdx
      (fun fuel item => evaluateGroups fuel ctx env keyWidth (wireItem item))
      (fun _ => sourceGroups ctx env plan) pointwise
  refine ⟨minimum, ?_⟩
  intro fuel enough
  unfold evaluateSchedule
  rw [decoded]
  change ((plan.operations.zipIdx.map wireItem).mapM
    (evaluateGroups fuel ctx env keyWidth)).map List.flatten = _
  simp only [List.mapM_map, Function.comp_def, agrees fuel enough]

private theorem groupActiveCount (fuel : Nat) (ctx : EvalContext) (env : EvalEnv)
    (keyWidth : Nat → Option Nat) (item : ScheduledOperation)
    {groups : List (Option Nat)} {operations : List NativeState.Op}
    (matched : evaluateGroups fuel ctx env keyWidth item = some groups)
    (evaluated : evaluateScheduledOperation fuel ctx env item = some operations) :
    groups.countP Option.isNone = operations.length := by
  cases guard : evaluateActivityGuard fuel ctx env item.guard with
  | none => simp [evaluateGroups, guard] at matched
  | some activity =>
      cases active : activity.getD Bool.true with
      | «false» =>
          cases width : operationWidth keyWidth item.operation with
          | none => simp [evaluateGroups, guard, active, width] at matched
          | some count =>
              simp [evaluateGroups, guard, active, width] at matched
              simp [evaluateScheduledOperation, guard, active] at evaluated
              subst groups operations
              rfl
      | «true» =>
          cases result : ImpactOperationAgreement.evaluateOperation fuel ctx env item.operation with
          | none => simp [evaluateScheduledOperation, guard, active, result] at evaluated
          | some operation =>
              simp [evaluateGroups, guard, active] at matched
              simp [evaluateScheduledOperation, guard, active, result, List.singleton] at evaluated
              subst groups operations
              rfl

private theorem traversalActiveCount (fuel : Nat) (ctx : EvalContext) (env : EvalEnv)
    (keyWidth : Nat → Option Nat) (items : List ScheduledOperation)
    {groups : List (List (Option Nat))} {operations : List (List NativeState.Op)}
    (matched : items.mapM (evaluateGroups fuel ctx env keyWidth) = some groups)
    (evaluated : items.mapM (evaluateScheduledOperation fuel ctx env) = some operations) :
    groups.flatten.countP Option.isNone = operations.flatten.length := by
  induction items generalizing groups operations with
  | nil =>
      simp at matched evaluated
      subst groups operations
      rfl
  | cons item rest ih =>
      simp only [List.mapM_cons] at matched evaluated
      cases group : evaluateGroups fuel ctx env keyWidth item with
      | none => simp [group] at matched
      | some group =>
          cases operation : evaluateScheduledOperation fuel ctx env item with
          | none => simp [operation] at evaluated
          | some operation =>
              cases restGroups : rest.mapM (evaluateGroups fuel ctx env keyWidth) with
              | none => simp [group, restGroups] at matched
              | some remainingGroups =>
                  cases restOps : rest.mapM (evaluateScheduledOperation fuel ctx env) with
                  | none => simp [operation, restOps] at evaluated
                  | some remainingOps =>
                      simp [group, restGroups] at matched
                      simp [operation, restOps] at evaluated
                      subst groups operations
                      simp [groupActiveCount fuel ctx env keyWidth item group operation,
                        ih restGroups restOps]

/-- Successful schedule and program evaluation satisfy the runtime invariant:
every active group accounts for one native scalar operation. -/
theorem activeCount_matches_plan (fuel : Nat) (ctx : EvalContext) (env : EvalEnv)
    (keyWidth : Nat → Option Nat) (raw : Json)
    {groups : List (Option Nat)} {operations : List NativeState.Op}
    (matched : evaluateSchedule fuel ctx env keyWidth raw = some groups)
    (evaluated : ImpactPlanAgreement.evaluatePlan fuel ctx env raw = some operations) :
    (groups.filter Option.isNone).length = operations.length := by
  unfold evaluateSchedule at matched
  unfold ImpactPlanAgreement.evaluatePlan at evaluated
  cases decode : decodePlanOperations raw with
  | error message => simp [decode, Except.toOption] at matched
  | ok items =>
      cases groupResult : items.mapM (evaluateGroups fuel ctx env keyWidth) with
      | none => simp [decode, Except.toOption, groupResult] at matched
      | some groupParts =>
          cases operationResult : items.mapM (evaluateScheduledOperation fuel ctx env) with
          | none => simp [decode, Except.toOption, operationResult] at evaluated
          | some operationParts =>
              simp [decode, Except.toOption, groupResult] at matched
              simp [decode, Except.toOption, operationResult] at evaluated
              subst groups operations
              rw [← List.countP_eq_length_filter]
              exact traversalActiveCount fuel ctx env keyWidth items groupResult operationResult

/-- A successful admitted wire schedule and program give a checked preview
with the original active order and every skipped field accounted for. -/
theorem preview_valid_schedule (fuel : Nat) (ctx : EvalContext) (env : EvalEnv)
    (keyWidth : Nat → Option Nat) (raw : Json)
    {groups : List (Option Nat)} {operations : List NativeState.Op}
    (matched : evaluateSchedule fuel ctx env keyWidth raw = some groups)
    (evaluated : ImpactPlanAgreement.evaluatePlan fuel ctx env raw = some operations)
    (fits : ImpactNoopPreview.skipRunsFit groups = Bool.true) :
    ∃ entries,
      ImpactNoopPreview.previewProgram operations groups = some entries ∧
      ImpactNoopPreview.activeProjection entries = operations ∧
      ImpactNoopPreview.skippedWidth entries = ImpactNoopPreview.activityWidth groups := by
  apply ImpactNoopPreview.previewProgram_preserves _ fits
  rw [ImpactNoopPreview.activeCount_eq_filter_length]
  exact activeCount_matches_plan fuel ctx env keyWidth raw matched evaluated

end Noctium.Verification.ImpactTranscriptSchedule
