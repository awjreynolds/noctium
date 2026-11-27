import Noctium.Verification.GenericStateCheckedReadTrace
import Noctium.Verification.GenericStateAdmissionPrefix
import Noctium.Verification.ScalarGuardedActivityAdmission
import Noctium.Verification.GuardedScalarExpressionAdmission

namespace Noctium.Verification.GuardedPlanAssertions

open Backend
open GenericStateCheckedReadTrace
open ScalarNormalization
open ScalarGuardedPlanAdmission (ScalarEffect)

/-- Assertions emitted by the raw effect compiler. The generated absence
name matches Impact's production spelling. -/
private def sourceEffectAssertionChunk (effect : Effect) (ordinal : Nat) :
    List (Expr .bool) :=
  match effect with
  | .require condition => [condition]
  | .requireAbsent .. =>
    [.eq (.ref ("_noctium_absence_" ++ toString ordinal) : Expr .bool) (.bool false)]
  | _ => []

/-- Assertions appended by one source effect under its effective activity
guard. Generated absence assertions use the current read count. -/
def guardedEffectAssertionChunk (guard : Option (Expr .bool))
    (effect : Effect) (ordinal : Nat) : List (Expr .bool) :=
  match guard, effect with
  | some condition, .require required =>
      [Impact.totalizeActivityCondition condition required]
  | none, _ => sourceEffectAssertionChunk effect ordinal
  | some _, _ => []

/-- Source-ordered assertion chunks, indexed by the live read count. -/
def guardedAssertionChunks (guards : List (Option (Expr .bool))) :
    List (Effect × Nat) → Nat → List (List (Expr .bool))
  | [], _ => []
  | item :: rest, ordinal =>
      guardedEffectAssertionChunk (guards[item.2]?.getD none) item.1 ordinal ::
        guardedAssertionChunks guards rest
          (ordinal + (GenericStateCheckedReadTrace.effectReadChunk item.1 ordinal).length)

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem appendEffect_assertion_chunk (state : List StateDecl)
    (effect : Effect) (scope : ScalarReadEffect effect) (before after : Impact.Plan)
    (accepted : Impact.appendEffect state effect before = .ok after) :
    after.guards = before.guards ++ sourceEffectAssertionChunk effect before.reads.length := by
  have same :
      Impact.Plan.guards <$> Impact.appendEffect state effect before =
      (fun _ => before.guards ++ sourceEffectAssertionChunk effect before.reads.length) <$>
        Impact.appendEffect state effect before := by
    cases scope <;>
      simp only [Impact.appendEffect, sourceEffectAssertionChunk, map_bind,
        LawfulApplicative.map_pure, List.append_nil] <;> rfl
  rw [accepted] at same
  exact Except.ok.inj same

private theorem appendEffectWithActivity_none_guard_frame (state : List StateDecl)
    (effect : Effect) (before after : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state effect none before = .ok after) :
    ∃ raw, Impact.appendEffect state effect before = .ok raw ∧
      after.guards = raw.guards := by
  have shape : Impact.appendEffectWithActivity state effect none before = (do
      let raw ← Impact.appendEffect state effect before
      if before.activityGuards.isEmpty then pure raw
      else
        let activityGuards := before.activityGuards ++
          List.replicate (raw.operations.length - before.operations.length) none
        pure ({raw with activityGuards} : Impact.Plan)) := by
    cases effect <;> rfl
  rw [shape, bind_ok] at accepted
  obtain ⟨raw, appended, wrapped⟩ := accepted
  refine ⟨raw, appended, ?_⟩
  by_cases empty : before.activityGuards.isEmpty
  · simp only [empty, Pure.pure, Except.pure] at wrapped
    exact congrArg Impact.Plan.guards (Except.ok.inj wrapped).symm
  · simp only [empty, Pure.pure, Except.pure] at wrapped
    simpa using congrArg Impact.Plan.guards (Except.ok.inj wrapped).symm

private theorem appendEffectWithActivity_guarded_readCell_guard_frame
    (state : List StateDecl) (name destination : String) (ty : Ty)
    (condition : Expr .bool) (before after : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state (.readCell name destination ty)
      (some condition) before = .ok after) : after.guards = before.guards := by
  unfold Impact.appendEffectWithActivity at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨lowered, loweredAccepted, raw, appended, wrapped⟩
  simp only [Pure.pure, Except.pure] at loweredAccepted
  have loweredShape := Except.ok.inj loweredAccepted
  subst lowered
  cases readAt : raw.reads[before.reads.length]? with
  | none => simp [readAt] at wrapped
  | some read =>
    simp only [readAt, Pure.pure, Except.pure] at wrapped
    have wrappedGuards := congrArg Impact.Plan.guards (Except.ok.inj wrapped).symm
    have rawGuards := appendEffect_assertion_chunk state
      (.readCell name destination ty) (.readCell name destination ty) before raw appended
    simpa [sourceEffectAssertionChunk] using wrappedGuards.trans rawGuards

private theorem appendEffectWithActivity_guarded_readMap_guard_frame
    (state : List StateDecl) (name destination : String) (keyTy valueTy : Ty)
    (key : Expr keyTy) (condition : Expr .bool) (before after : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state
      (.readMap name destination keyTy valueTy key) (some condition) before = .ok after) :
    after.guards = before.guards := by
  unfold Impact.appendEffectWithActivity at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨lowered, loweredAccepted, raw, appended, wrapped⟩
  simp only [Pure.pure, Except.pure] at loweredAccepted
  obtain ⟨guardedKey, loweredShape⟩ :=
    (show ∃ guardedKey : Expr keyTy,
      lowered = .readMap name destination keyTy valueTy guardedKey from
        ⟨_, (Except.ok.inj loweredAccepted).symm⟩)
  subst lowered
  cases readAt : raw.reads[before.reads.length]? with
  | none => simp [readAt] at wrapped
  | some read =>
    simp only [readAt, Pure.pure, Except.pure] at wrapped
    have wrappedGuards := congrArg Impact.Plan.guards (Except.ok.inj wrapped).symm
    have rawGuards := appendEffect_assertion_chunk state
      (.readMap name destination keyTy valueTy guardedKey)
      (.readMap name destination keyTy valueTy guardedKey) before raw appended
    simpa [sourceEffectAssertionChunk] using wrappedGuards.trans rawGuards

private theorem appendEffectWithActivity_guarded_writeCell_guard_frame
    (state : List StateDecl) (name : String) (ty : Ty) (value : Expr ty)
    (condition : Expr .bool) (before after : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state (.writeCell name ty value)
      (some condition) before = .ok after) : after.guards = before.guards := by
  unfold Impact.appendEffectWithActivity at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨lowered, loweredAccepted, raw, appended, wrapped⟩
  simp only [Pure.pure, Except.pure] at loweredAccepted
  obtain ⟨guardedValue, loweredShape⟩ :=
    (show ∃ guardedValue : Expr ty,
      lowered = .writeCell name ty guardedValue from
        ⟨_, (Except.ok.inj loweredAccepted).symm⟩)
  subst lowered
  simp only [Pure.pure, Except.pure] at wrapped
  have wrappedGuards := congrArg Impact.Plan.guards (Except.ok.inj wrapped).symm
  have rawGuards := appendEffect_assertion_chunk state
    (.writeCell name ty guardedValue) (.writeCell name ty guardedValue) before raw appended
  simpa [sourceEffectAssertionChunk] using wrappedGuards.trans rawGuards

private theorem appendEffectWithActivity_guarded_writeMap_guard_frame
    (state : List StateDecl) (name : String) (keyTy valueTy : Ty)
    (key : Expr keyTy) (value : Expr valueTy) (condition : Expr .bool)
    (before after : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state
      (.writeMap name keyTy valueTy key value) (some condition) before = .ok after) :
    after.guards = before.guards := by
  unfold Impact.appendEffectWithActivity at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨lowered, loweredAccepted, raw, appended, wrapped⟩
  simp only [Pure.pure, Except.pure] at loweredAccepted
  obtain ⟨guardedKey, guardedValue, loweredShape⟩ := (show
      ∃ guardedKey : Expr keyTy, ∃ guardedValue : Expr valueTy,
        lowered = .writeMap name keyTy valueTy guardedKey guardedValue from
          ⟨_, _, (Except.ok.inj loweredAccepted).symm⟩)
  subst lowered
  simp only [Pure.pure, Except.pure] at wrapped
  have wrappedGuards := congrArg Impact.Plan.guards (Except.ok.inj wrapped).symm
  have rawGuards := appendEffect_assertion_chunk state
    (.writeMap name keyTy valueTy guardedKey guardedValue)
    (.writeMap name keyTy valueTy guardedKey guardedValue) before raw appended
  simpa [sourceEffectAssertionChunk] using wrappedGuards.trans rawGuards

/-- The actual append step adds exactly the assertions for its source effect.
Guarded reads and writes append none. -/
theorem appendEffectWithActivity_guarded_assertion_chunk (state : List StateDecl)
    (effect : Effect) (guard : Option (Expr .bool))
    (scope : GuardedScalarReadEffect guard effect) (before after : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state effect guard before = .ok after) :
    after.guards = before.guards ++
      guardedEffectAssertionChunk guard effect before.reads.length := by
  cases scope with
  | unguarded scope =>
    obtain ⟨raw, appended, guardFrame⟩ := appendEffectWithActivity_none_guard_frame
      state effect before after accepted
    rw [guardFrame]
    rw [appendEffect_assertion_chunk state effect scope before raw appended]
    rfl
  | require condition required =>
    rw [Impact.appendEffectWithActivity_require] at accepted
    have guards := appendEffect_assertion_chunk state
      (.require (Impact.totalizeActivityCondition condition required))
      (.require _) before after accepted
    simpa [guardedEffectAssertionChunk, sourceEffectAssertionChunk] using guards
  | readCell condition name destination ty =>
    have guardFrame := appendEffectWithActivity_guarded_readCell_guard_frame
      state name destination ty condition before after accepted
    simpa [guardedEffectAssertionChunk] using guardFrame
  | readMap condition name destination keyTy valueTy key =>
    have guardFrame := appendEffectWithActivity_guarded_readMap_guard_frame
      state name destination keyTy valueTy key condition before after accepted
    simpa [guardedEffectAssertionChunk] using guardFrame
  | writeCell condition name ty value =>
    have guardFrame := appendEffectWithActivity_guarded_writeCell_guard_frame
      state name ty value condition before after accepted
    simpa [guardedEffectAssertionChunk] using guardFrame
  | writeMap condition name keyTy valueTy key value =>
    have guardFrame := appendEffectWithActivity_guarded_writeMap_guard_frame
      state name keyTy valueTy key value condition before after accepted
    simpa [guardedEffectAssertionChunk] using guardFrame

private theorem trace_guarded_plan_assertions (state : List StateDecl)
    (guards : List (Option (Expr .bool))) (items : List (Effect × Nat))
    (initial result : Impact.Plan) (offsets : List Nat)
    (scope : GuardedScalarReadEffects guards items)
    (trace : Impact.GuardedEffectTrace state guards items initial result offsets) :
    result.guards = initial.guards ++
      (guardedAssertionChunks guards items initial.reads.length).flatten := by
  induction items generalizing initial result offsets with
  | nil =>
    cases trace
    simp [guardedAssertionChunks]
  | cons item rest ih =>
    cases trace with
    | cons step tail =>
      rename_i middle offsets
      have headScope : GuardedScalarReadEffect
          (guards[item.2]?.getD none) item.1 := by
        apply scope
        simp
      have tailScope : GuardedScalarReadEffects guards rest := by
        intro next member
        apply scope next
        simp [member]
      have resultGuards := appendEffectWithActivity_guarded_assertion_chunk
        state item.1 (guards[item.2]?.getD none) headScope initial middle step
      have resultReads := GenericStateCheckedReadTrace.appendEffectWithActivity_guarded_read_chunk
        state item.1 (guards[item.2]?.getD none) headScope initial middle step
      have ordinal : middle.reads.length = initial.reads.length +
          (GenericStateCheckedReadTrace.effectReadChunk item.1 initial.reads.length).length := by
        have lengths := congrArg List.length resultReads
        simpa [GenericStateCheckedReadTrace.planReadMetadata, List.length_append] using lengths
      have tailResult := ih middle result offsets tailScope tail
      rw [tailResult, resultGuards, ordinal]
      simp [guardedAssertionChunks, List.flatten_cons, List.append_assoc]

/-- Exact assertion rows of the actual accepted guarded source trace. -/
theorem guarded_trace_plan_assertions (state : List StateDecl)
    (guards : List (Option (Expr .bool))) (items : List (Effect × Nat))
    (initial result : Impact.Plan) (offsets : List Nat)
    (scope : GuardedScalarReadEffects guards items)
    (trace : Impact.GuardedEffectTrace state guards items initial result offsets) :
    result.guards = initial.guards ++
      (guardedAssertionChunks guards items initial.reads.length).flatten :=
  trace_guarded_plan_assertions state guards items initial result offsets scope trace

private theorem totalizeActivityCondition_scalar (guard condition : Expr .bool)
    (guardAdmitted : ScalarExpression guard) (conditionAdmitted : ScalarExpression condition) :
    ScalarExpression (Impact.totalizeActivityCondition guard condition) := by
  obtain ⟨name, shape, _, _⟩ := Impact.totalizeActivityCondition_shape guard condition
  rw [shape]
  exact ScalarExpression.letE name guard _ .bool guardAdmitted
    (ScalarExpression.select (.ref name)
      (GuardedExpression.totalize (.ref name) condition) (.bool true) .bool
      (ScalarExpression.ref name .bool)
      (GuardedScalarExpressionAdmission.totalize_scalarExpression (.ref name)
        (ScalarExpression.ref name .bool) condition conditionAdmitted)
      (ScalarExpression.bool true))

private theorem guardedEffectAssertionChunk_scalar (state : List StateDecl)
    (guard : Option (Expr .bool)) (effect : Effect) (ordinal : Nat)
    (source : ScalarEffect state effect)
    (guardsAdmitted : ∀ condition, guard = some condition → ScalarExpression condition) :
    ∀ condition ∈ guardedEffectAssertionChunk guard effect ordinal,
      ScalarExpression condition := by
  cases source with
  | cell effect cell operand =>
    cases cell with
    | readCell name destination ty scalar declaration =>
      cases guard <;> intro condition present <;>
        simp [guardedEffectAssertionChunk, sourceEffectAssertionChunk] at present
    | writeCell name ty value scalar declaration =>
      cases guard <;> intro condition present <;>
        simp [guardedEffectAssertionChunk, sourceEffectAssertionChunk] at present
  | readMap name destination keyTy valueTy key keyScalar valueScalar keyAdmitted =>
    cases guard <;> intro condition present <;>
      simp [guardedEffectAssertionChunk, sourceEffectAssertionChunk] at present
  | writeMap name keyTy valueTy key value keyScalar valueScalar keyAdmitted valueAdmitted =>
    cases guard <;> intro condition present <;>
      simp [guardedEffectAssertionChunk, sourceEffectAssertionChunk] at present
  | require required requiredAdmitted =>
    cases guard with
    | none =>
      intro condition present
      simp [guardedEffectAssertionChunk, sourceEffectAssertionChunk] at present
      simpa [present] using requiredAdmitted
    | some gate =>
      intro condition present
      simp [guardedEffectAssertionChunk] at present
      simpa [present] using totalizeActivityCondition_scalar gate required
        (guardsAdmitted gate rfl) requiredAdmitted
  | requireAbsent name keyTy key keyScalar keyAdmitted =>
    cases guard with
    | none =>
      intro condition present
      simp [guardedEffectAssertionChunk, sourceEffectAssertionChunk] at present
      subst condition
      exact ScalarExpression.eq _ _ .bool
        (ScalarExpression.ref _ .bool) (ScalarExpression.bool false)
    | some gate =>
      intro condition present
      simp [guardedEffectAssertionChunk] at present

private theorem guardedAssertionChunks_scalar (state : List StateDecl)
    (guards : List (Option (Expr .bool))) (items : List (Effect × Nat)) (ordinal : Nat)
    (effects : ∀ item ∈ items, ScalarEffect state item.1)
    (guardsAdmitted : ∀ condition, some condition ∈ guards → ScalarExpression condition) :
    ∀ condition ∈ (guardedAssertionChunks guards items ordinal).flatten,
      ScalarExpression condition := by
  induction items generalizing ordinal with
  | nil => simp [guardedAssertionChunks]
  | cons item rest ih =>
    intro condition present
    simp only [guardedAssertionChunks, List.flatten_cons, List.mem_append] at present
    rcases present with head | tail
    · have effectAdmitted := effects item (by simp)
      have selectedGuardAdmitted (gate : Expr .bool)
          (selected : guards[item.2]?.getD none = some gate) : ScalarExpression gate := by
        have member : some gate ∈ guards := by
          cases found : guards[item.2]? with
          | none => simp [found] at selected
          | some value =>
            have same : value = some gate := by simpa [found] using selected
            exact same ▸ List.mem_of_getElem? found
        exact guardsAdmitted gate member
      exact guardedEffectAssertionChunk_scalar state
        (guards[item.2]?.getD none) item.1 ordinal effectAdmitted
        (by
          intro gate selected
          exact selectedGuardAdmitted gate selected) condition head
    · have remainingEffects : ∀ later ∈ rest, ScalarEffect state later.1 := by
        intro later member
        exact effects later (List.mem_cons_of_mem item member)
      exact ih (ordinal +
        (GenericStateCheckedReadTrace.effectReadChunk item.1 ordinal).length)
        remainingEffects condition tail

/-- Every guard in an accepted source plan belongs to the scalar expression
fragment when source effects and source activity guards satisfy scalar
admission. The public-input prefix contributes no guards, each source effect
contributes its exact assertion chunk, and guarded absence is rejected by the
accepted activity trace. -/
theorem lower_plan_guards_scalar (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (lowered : Impact.lower state entry = .ok plan)
    (effects : ∀ effect ∈ entry.effects, ScalarEffect state effect)
    (guardsAdmitted : ∀ condition, some condition ∈ entry.effectGuards →
      ScalarExpression condition) :
    ∀ condition ∈ plan.guards, ScalarExpression condition := by
  obtain ⟨_, inputPlan, _, inputAccepted, trace⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state entry plan lowered
  have scope := ScalarGuardedActivityAdmission.lower_guarded_scalar_read_scope
    state entry plan lowered effects
  have assertions := guarded_trace_plan_assertions state entry.effectGuards
    entry.effects.zipIdx inputPlan plan _ scope trace
  have prefixGuards := Impact.publicInputPlan_guards entry.circuit.inputs {}
    inputPlan inputAccepted
  have prefixEmpty : inputPlan.guards = [] := by simpa using prefixGuards
  intro condition present
  rw [assertions, prefixEmpty] at present
  exact guardedAssertionChunks_scalar state entry.effectGuards entry.effects.zipIdx
    inputPlan.reads.length (by
      intro item member
      apply effects item.1
      rw [← List.zipIdx_map_fst 0 entry.effects]
      exact List.mem_map_of_mem member) guardsAdmitted condition present

private theorem unguarded_require_occurrence_guard_chunk
    (guards : List (Option (Expr .bool))) (items : List (Effect × Nat))
    (ordinal : Nat) (condition : Expr .bool) (index : Nat)
    (occurrence : (Effect.require condition, index) ∈ items)
    (unguarded : guards[index]?.getD none = none) :
    condition ∈ (guardedAssertionChunks guards items ordinal).flatten := by
  induction items generalizing ordinal with
  | nil => cases occurrence
  | cons item rest ih =>
    rcases List.mem_cons.mp occurrence with same | later
    · rw [← same]
      simp [guardedAssertionChunks, guardedEffectAssertionChunk, unguarded,
        sourceEffectAssertionChunk]
    · simp only [guardedAssertionChunks, List.flatten_cons, List.mem_append]
      exact Or.inr (ih (ordinal +
        (GenericStateCheckedReadTrace.effectReadChunk item.1 ordinal).length) later)

/-- An unguarded source REQUIRE occurrence contributes its exact condition to
the assertions of the successfully lowered plan. The index identifies the
occurrence in `entry.effects.zipIdx`. -/
theorem lower_unguarded_require_assertion (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (condition : Expr .bool) (index : Nat)
    (accepted : Impact.lower state entry = .ok plan)
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
    (occurrence : (Effect.require condition, index) ∈ entry.effects.zipIdx)
    (unguarded : entry.effectGuards[index]?.getD none = none) :
    condition ∈ plan.guards := by
  obtain ⟨_, inputPlan, _, publicAccepted, trace⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state entry plan accepted
  have assertions := guarded_trace_plan_assertions state entry.effectGuards
    entry.effects.zipIdx inputPlan plan _ scope trace
  rw [assertions]
  exact List.mem_append_right _ (unguarded_require_occurrence_guard_chunk
    entry.effectGuards entry.effects.zipIdx inputPlan.reads.length condition index occurrence unguarded)

end Noctium.Verification.GuardedPlanAssertions
