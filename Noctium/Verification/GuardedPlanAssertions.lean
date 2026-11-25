import Noctium.Verification.GenericStateCheckedReadTrace
import Noctium.Verification.GenericStateAdmissionPrefix

namespace Noctium.Verification.GuardedPlanAssertions

open Backend
open GenericStateCheckedReadTrace

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
