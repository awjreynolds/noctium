import Noctium.Verification.GenericStateCheckedReadTrace
import Noctium.Verification.GenericStateCircuitParts
import Noctium.Verification.GuardedEffectEvaluation

namespace Noctium.Verification.GuardedPlanActivity
open Backend
open GenericStateCheckedReadTrace

/-- Effective source guard at each operation. An empty stored guard list
represents a plan whose operations are all unconditional. -/
def operationGuards (plan : Impact.Plan) : List (Option (Expr .bool)) :=
  if plan.activityGuards.isEmpty then List.replicate plan.operations.length none
  else plan.activityGuards

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem raw_append_frame (state : List StateDecl) (effect : Effect)
    (scope : ScalarReadEffect effect) (before after : Impact.Plan)
    (step : Impact.appendEffect state effect before = .ok after) :
    ∃ chunk, after.operations = before.operations ++ chunk ∧
      after.activityGuards = before.activityGuards := by
  cases scope <;> simp only [Impact.appendEffect, bind_ok] at step
  case readCell =>
    obtain ⟨_, _, _, _, finished⟩ := step
    cases finished
    exact ⟨_, rfl, rfl⟩
  case readMap =>
    obtain ⟨_, _, _, _, _, _, finished⟩ := step
    cases finished
    exact ⟨_, rfl, rfl⟩
  case requireAbsent =>
    obtain ⟨_, _, _, _, finished⟩ := step
    cases finished
    exact ⟨_, rfl, rfl⟩
  case require =>
    cases step
    exact ⟨[], List.append_nil _ |>.symm, rfl⟩
  case writeCell =>
    obtain ⟨_, _, _, _, finished⟩ := step
    cases finished
    exact ⟨_, rfl, rfl⟩
  case writeMap =>
    obtain ⟨_, _, _, _, _, _, finished⟩ := step
    cases finished
    exact ⟨_, rfl, rfl⟩

private theorem operationGuards_of_complete (plan : Impact.Plan)
    (complete : plan.activityGuards.length = plan.operations.length) :
    operationGuards plan = plan.activityGuards := by
  unfold operationGuards
  split
  · rename_i empty
    have nil := List.isEmpty_iff.mp (show plan.activityGuards.isEmpty = true from empty)
    simp [nil, ← complete]
  · rfl

private theorem append_explicit_guards (before after : Impact.Plan) (chunk : List Impact.Op)
    (condition : Option (Expr .bool))
    (lengths : (operationGuards before).length = before.operations.length)
    (ops : after.operations = before.operations ++ chunk)
    (guards : after.activityGuards = operationGuards before ++
      List.replicate (after.operations.length - before.operations.length) condition) :
    operationGuards after = operationGuards before ++ List.replicate chunk.length condition := by
  have diff : after.operations.length - before.operations.length = chunk.length := by
    rw [ops]
    simp
  have complete : after.activityGuards.length = after.operations.length := by
    rw [guards, diff, List.length_append, List.length_replicate, lengths, ops, List.length_append]
  rw [operationGuards_of_complete after complete, guards, diff]

private theorem unguarded_chunk (state : List StateDecl) (effect : Effect)
    (scope : ScalarReadEffect effect) (before after : Impact.Plan)
    (lengths : (operationGuards before).length = before.operations.length)
    (step : Impact.appendEffectWithActivity state effect none before = .ok after) :
    ∃ chunk, after.operations = before.operations ++ chunk ∧
      operationGuards after = operationGuards before ++ List.replicate chunk.length none := by
  have shape : Impact.appendEffectWithActivity state effect none before = (do
      let raw ← Impact.appendEffect state effect before
      if before.activityGuards.isEmpty then pure raw
      else
        let guards := before.activityGuards ++
          List.replicate (raw.operations.length - before.operations.length) none
        pure ({raw with activityGuards := guards} : Impact.Plan)) := by
    cases effect <;> rfl
  rw [shape, bind_ok] at step
  obtain ⟨raw, accepted, wrapped⟩ := step
  obtain ⟨chunk, ops, guardFrame⟩ := raw_append_frame state effect scope before raw accepted
  split at wrapped
  · rename_i empty
    cases wrapped
    refine ⟨chunk, ops, ?_⟩
    simp [operationGuards, guardFrame, empty, ops, List.replicate_append_replicate]
  · rename_i nonempty
    cases wrapped
    refine ⟨chunk, ops, ?_⟩
    refine append_explicit_guards before _ chunk none lengths ?_ ?_
    · exact ops
    · simp [operationGuards, nonempty]

/-- The accepted compiler step appends one exact chunk and one effective
source guard per operation in the chunk. Source-only requirements add no
operations. The input prefix may use the compiler's empty-list encoding. -/
theorem appendActivity_chunk (state : List StateDecl) (effect : Effect)
    (guard : Option (Expr .bool)) (scope : GuardedScalarReadEffect guard effect)
    (before after : Impact.Plan)
    (lengths : (operationGuards before).length = before.operations.length)
    (step : Impact.appendEffectWithActivity state effect guard before = .ok after) :
    ∃ chunk, after.operations = before.operations ++ chunk ∧
      operationGuards after = operationGuards before ++ List.replicate chunk.length guard := by
  cases scope with
  | unguarded scope => exact unguarded_chunk state effect scope before after lengths step
  | require condition required =>
    rw [Impact.appendEffectWithActivity_require] at step
    simp only [Impact.appendEffect] at step
    cases step
    exact ⟨[], (List.append_nil _).symm, by simp [operationGuards]⟩
  | readCell condition name destination ty =>
    obtain ⟨slot, value, _, _, _, _, _, ops, guards⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_readCell_provenance state name destination ty
        condition before after step
    refine ⟨[.dup, .index slot, value], ops, ?_⟩
    have diff : after.operations.length - before.operations.length = 3 := by rw [ops]; simp
    apply append_explicit_guards before after _ (some condition) lengths ops
    simpa [operationGuards, diff] using guards
  | readMap condition name destination keyTy valueTy key =>
    unfold Impact.appendEffectWithActivity at step
    simp only [bind_ok] at step
    obtain ⟨effect, lowered, raw, appended, wrapped⟩ := step
    have effectShape : ∃ key' : Expr keyTy, effect = .readMap name destination keyTy valueTy key' := by
      simp only [Pure.pure, Except.pure] at lowered
      cases lowered
      exact ⟨_, rfl⟩
    obtain ⟨key', rfl⟩ := effectShape
    obtain ⟨chunk, ops, _⟩ := raw_append_frame state _ (.readMap name destination keyTy valueTy key')
      before raw appended
    cases readAt : raw.reads[before.reads.length]? with
    | none => simp [readAt] at wrapped
    | some read =>
      simp only [readAt, Pure.pure, Except.pure] at wrapped
      cases wrapped
      exact ⟨chunk, ops, append_explicit_guards before _ chunk (some condition) lengths ops rfl⟩
  | writeCell condition name ty value =>
    unfold Impact.appendEffectWithActivity at step
    simp only [bind_ok] at step
    obtain ⟨effect, lowered, raw, appended, wrapped⟩ := step
    have effectShape : ∃ value' : Expr ty, effect = .writeCell name ty value' := by
      simp only [Pure.pure, Except.pure] at lowered
      cases lowered
      exact ⟨_, rfl⟩
    obtain ⟨value', rfl⟩ := effectShape
    obtain ⟨chunk, ops, _⟩ := raw_append_frame state _ (.writeCell name ty value') before raw appended
    cases wrapped
    exact ⟨chunk, ops, append_explicit_guards before _ chunk (some condition) lengths ops rfl⟩
  | writeMap condition name keyTy valueTy key value =>
    unfold Impact.appendEffectWithActivity at step
    simp only [bind_ok] at step
    obtain ⟨effect, lowered, raw, appended, wrapped⟩ := step
    have effectShape : ∃ key' : Expr keyTy, ∃ value' : Expr valueTy,
        effect = .writeMap name keyTy valueTy key' value' := by
      simp only [Pure.pure, Except.pure] at lowered
      cases lowered
      exact ⟨_, _, rfl⟩
    obtain ⟨key', value', rfl⟩ := effectShape
    obtain ⟨chunk, ops, _⟩ := raw_append_frame state _ (.writeMap name keyTy valueTy key' value')
      before raw appended
    cases wrapped
    exact ⟨chunk, ops, append_explicit_guards before _ chunk (some condition) lengths ops rfl⟩

private theorem zip_replicate_width {α β : Type} (values : List α) (value : β) :
    values.zip (List.replicate values.length value) = values.map (·, value) := by
  induction values with
  | nil => rfl
  | cons head rest ih => simp [List.replicate_succ, ih]

private abbrev fieldGuardsFor (operations : List Impact.Op) (guard : Option (Expr .bool)) :
    List (Option (Expr .bool)) :=
  operations.flatMap fun operation => List.replicate operation.fieldGroups.length guard

private theorem activityGuardSources_zip (plan : Impact.Plan) :
    GenericStateCircuitParts.activityGuardSources plan =
      (plan.operations.zip (operationGuards plan)).flatMap fun (operation, guard) =>
        List.replicate operation.fieldGroups.length guard := by
  unfold GenericStateCircuitParts.activityGuardSources operationGuards
  split
  · rw [zip_replicate_width, List.flatMap_map]
  · rfl

private theorem activityGuardSources_append (before after : Impact.Plan) (chunk : List Impact.Op)
    (guard : Option (Expr .bool))
    (lengths : (operationGuards before).length = before.operations.length)
    (ops : after.operations = before.operations ++ chunk)
    (guards : operationGuards after = operationGuards before ++ List.replicate chunk.length guard) :
    GenericStateCircuitParts.activityGuardSources after =
      GenericStateCircuitParts.activityGuardSources before ++ fieldGuardsFor chunk guard := by
  rw [activityGuardSources_zip, activityGuardSources_zip before, ops, guards,
    List.zip_append lengths.symm, List.flatMap_append, zip_replicate_width, List.flatMap_map]

/-- Expand the source activity condition across the actual field groups of
each emitted chunk. A source-only assertion contributes an empty chunk. -/
def effectFieldGuards (guards : List (Option (Expr .bool)))
    (items : List (Effect × Nat)) (chunks : List (List Impact.Op)) : List (Option (Expr .bool)) :=
  (items.zip chunks).flatMap fun (item, operations) =>
    fieldGuardsFor operations (guards[item.2]?.getD none)

/-- The accepted guarded append trace recovers source-ordered operation chunks
and exact guard sources at native field-group granularity. -/
theorem trace_field_guards {state : List StateDecl} {guards : List (Option (Expr .bool))}
    {items : List (Effect × Nat)} {initial result : Impact.Plan} {offsets : List Nat}
    (scope : GuardedScalarReadEffects guards items)
    (trace : Impact.GuardedEffectTrace state guards items initial result offsets)
    (aligned : (operationGuards initial).length = initial.operations.length) :
    ∃ chunks,
      GuardedEffectEvaluation.GuardedEffectOperationChunks state guards items initial result offsets chunks ∧
      GenericStateCircuitParts.activityGuardSources result =
        GenericStateCircuitParts.activityGuardSources initial ++ effectFieldGuards guards items chunks := by
  induction trace with
  | nil before => exact ⟨[], .nil before, by simp [effectFieldGuards]⟩
  | @cons item rest before next result offsets first tail ih =>
    have headScope := scope item (by simp)
    obtain ⟨chunk, ops, guardSources⟩ := appendActivity_chunk state item.1
      (guards[item.2]?.getD none) headScope before next aligned first
    have nextAligned : (operationGuards next).length = next.operations.length := by
      rw [guardSources, ops, List.length_append, List.length_append, List.length_replicate, aligned]
    obtain ⟨chunks, chunksAccepted, tailSources⟩ := ih
      (fun nextItem member => scope nextItem (List.mem_cons_of_mem item member)) nextAligned
    have chunkSources := activityGuardSources_append before next chunk _ aligned ops guardSources
    refine ⟨chunk :: chunks, .cons first ops chunksAccepted, ?_⟩
    rw [tailSources, chunkSources]
    simp [effectFieldGuards, List.append_assoc]

private theorem fieldGuardsFor_replicate (operations : List Impact.Op) (guard : Option (Expr .bool)) :
    fieldGuardsFor operations guard =
      List.replicate ((operations.flatMap Impact.Op.fieldGroups).length) guard := by
  induction operations with
  | nil => rfl
  | cons operation rest ih =>
    simp only [fieldGuardsFor, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih, List.replicate_append_replicate]

/-- Actual entrypoint lowering aligns source activity with every native field
group, including unconditional public input groups and zero-width assertions. -/
theorem lower_field_guards (state : List StateDecl) (entry : Entrypoint) (plan : Impact.Plan)
    (lowered : Impact.lower state entry = .ok plan)
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx) :
    ∃ offsets inputPlan chunks,
      Impact.lowerWithEffectBoundaries state entry = .ok (plan, offsets) ∧
      Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan ∧
      GuardedEffectEvaluation.GuardedEffectOperationChunks state entry.effectGuards
        entry.effects.zipIdx inputPlan plan offsets chunks ∧
      GenericStateCircuitParts.activityGuardSources plan =
        List.replicate inputPlan.fieldGroups.length none ++
          effectFieldGuards entry.effectGuards entry.effects.zipIdx chunks := by
  obtain ⟨offsets, inputPlan, accepted, publicInputs, trace⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state entry plan lowered
  have empty : inputPlan.activityGuards = [] :=
    Impact.publicInputPlan_activity_guards entry.circuit.inputs {} inputPlan publicInputs
  have aligned : (operationGuards inputPlan).length = inputPlan.operations.length := by
    simp [operationGuards, empty]
  obtain ⟨chunks, chunkTrace, activity⟩ := trace_field_guards scope trace aligned
  refine ⟨offsets, inputPlan, chunks, accepted, publicInputs, chunkTrace, ?_⟩
  rw [activity]
  have publicGuards : GenericStateCircuitParts.activityGuardSources inputPlan =
      List.replicate inputPlan.fieldGroups.length none := by
    simp only [GenericStateCircuitParts.activityGuardSources, empty, List.isEmpty_nil, if_true,
      Impact.Plan.fieldGroups]
    exact fieldGuardsFor_replicate inputPlan.operations none
  rw [publicGuards]

/-- The same production chunk trace supplies native operations and their exact
ordered source field-group conditions. The admitted effect scope discharges
the older per-effect prefix premise. -/
theorem lower_scoped_guarded_evaluation (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext) (env : EvalEnv) (native : List NativeState.Op)
    (lowered : Impact.lower state entry = .ok plan)
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
    (evaluated : GenericStateOps.evalPlan ctx env plan = .ok native) :
    ∃ offsets inputPlan chunks publicNative groups,
      Impact.lowerWithEffectBoundaries state entry = .ok (plan, offsets) ∧
      Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan ∧
      GuardedEffectEvaluation.GuardedEffectOperationChunks state entry.effectGuards
        entry.effects.zipIdx inputPlan plan offsets chunks ∧
      GenericStateCircuitParts.activityGuardSources plan =
        List.replicate inputPlan.fieldGroups.length none ++
          effectFieldGuards entry.effectGuards entry.effects.zipIdx chunks ∧
      inputPlan.operations.mapM (GenericStateOps.evalOp ctx env) = .ok publicNative ∧
      chunks.mapM (fun chunk => chunk.mapM (GenericStateOps.evalOp ctx env)) = .ok groups ∧
      native = publicNative ++ groups.flatten := by
  obtain ⟨offsets, inputPlan, chunks, accepted, publicInputs, trace, activity⟩ :=
    lower_field_guards state entry plan lowered scope
  obtain ⟨publicNative, groups, evaluatedInput, evaluatedGroups, ordered⟩ :=
    GuardedEffectEvaluation.eval_guarded_chunks ctx env native trace
      (by simpa only [GenericStateOps.evalPlan] using evaluated)
  exact ⟨offsets, inputPlan, chunks, publicNative, groups, accepted, publicInputs, trace, activity,
    evaluatedInput, evaluatedGroups, ordered⟩

/-- The production native checker expects the condition from the source effect
owning each field-group ordinal. Public prefix groups normalize as unconditional. -/
theorem expectedEntrypoint_effect_guard_at (state : List StateDecl) (entry : Entrypoint)
    (expected : Native.Expected)
    (accepted : Native.expectedEntrypoint state entry = .ok expected)
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx) :
    ∃ plan offsets inputPlan chunks aliases,
      Impact.lowerWithEffectBoundaries state entry = .ok (plan, offsets) ∧
      Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan ∧
      GuardedEffectEvaluation.GuardedEffectOperationChunks state entry.effectGuards
        entry.effects.zipIdx inputPlan plan offsets chunks ∧
      ∀ index : Nat,
        ((((List.replicate inputPlan.fieldGroups.length none ++
            effectFieldGuards entry.effectGuards entry.effects.zipIdx chunks)[index]?).mapM
              (GenericStateCircuitParts.normalizeActivityGuard entry aliases)).map
          (Option.map (·.term))) = .ok expected.groupGuards[index]? := by
  obtain ⟨plan, aliases, lowered, atIndex⟩ :=
    GenericStateCircuitParts.expectedEntrypoint_activityGuard_at state entry expected accepted
  obtain ⟨offsets, inputPlan, chunks, boundaries, publicInputs, trace, sources⟩ :=
    lower_field_guards state entry plan lowered scope
  refine ⟨plan, offsets, inputPlan, chunks, aliases, boundaries, publicInputs, trace, ?_⟩
  intro index
  simpa only [sources] using atIndex index

end Noctium.Verification.GuardedPlanActivity
