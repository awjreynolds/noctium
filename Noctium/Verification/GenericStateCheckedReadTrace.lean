import Noctium.Verification.GenericStateAdmissionPrefix

namespace Noctium.Verification.GenericStateCheckedReadTrace
open Backend

abbrev ReadMetadata := String × Ty

def readMetadata (read : Impact.Read) : ReadMetadata := (read.name, read.ty)

def planReadMetadata (plan : Impact.Plan) : List ReadMetadata :=
  plan.reads.map readMetadata

def effectReadChunk (effect : Effect) (ordinal : Nat) : List ReadMetadata :=
  match effect with
  | .readCell _ destination ty => [(destination, ty)]
  | .readMap _ destination _ ty _ => [(destination, ty)]
  | .requireAbsent .. =>
    [("_noctium_absence_" ++ toString ordinal, .bool)]
  | _ => []

def readChunks : List Effect → Nat → List (List ReadMetadata)
  | [], _ => []
  | effect :: rest, ordinal =>
    let chunk := effectReadChunk effect ordinal
    chunk :: readChunks rest (ordinal + chunk.length)

inductive ScalarReadEffect : Effect → Prop where
  | readCell (name destination : String) (ty : Ty) :
      ScalarReadEffect (.readCell name destination ty)
  | readMap (name destination : String) (keyTy valueTy : Ty)
      (key : Expr keyTy) :
      ScalarReadEffect (.readMap name destination keyTy valueTy key)
  | requireAbsent (name : String) (keyTy : Ty) (key : Expr keyTy) :
      ScalarReadEffect (.requireAbsent name keyTy key)
  | require (condition : Expr .bool) :
      ScalarReadEffect (.require condition)
  | writeCell (name : String) (ty : Ty) (value : Expr ty) :
      ScalarReadEffect (.writeCell name ty value)
  | writeMap (name : String) (keyTy valueTy : Ty)
      (key : Expr keyTy) (value : Expr valueTy) :
      ScalarReadEffect (.writeMap name keyTy valueTy key value)

def ScalarReadEffects (effects : List Effect) : Prop :=
  ∀ effect ∈ effects, ScalarReadEffect effect

private theorem appendEffectWithActivity_none_shape (state : List StateDecl)
    (effect : Effect) (scope : ScalarReadEffect effect) (before : Impact.Plan) :
    Impact.appendEffectWithActivity state effect none before = (do
      let result ← Impact.appendEffect state effect before
      if before.activityGuards.isEmpty then
        pure result
      else
        let activityGuards := before.activityGuards ++
          List.replicate (result.operations.length - before.operations.length) none
        pure ({result with activityGuards := activityGuards} : Impact.Plan)) := by
  cases scope <;> rfl

private theorem appendEffect_read_chunk (state : List StateDecl) (effect : Effect)
    (scope : ScalarReadEffect effect) (before after : Impact.Plan)
    (accepted : Impact.appendEffect state effect before = .ok after) :
    after.reads.map readMetadata =
      planReadMetadata before ++ effectReadChunk effect before.reads.length := by
  have same :
      planReadMetadata <$> Impact.appendEffect state effect before =
      (fun _ => planReadMetadata before ++ effectReadChunk effect before.reads.length) <$>
        Impact.appendEffect state effect before := by
    cases scope <;>
      simp only [Impact.appendEffect, planReadMetadata, readMetadata,
        effectReadChunk, map_bind, LawfulApplicative.map_pure, List.append_nil,
        List.map_append, List.map_cons, List.map_nil] <;> rfl
  rw [accepted] at same
  exact Except.ok.inj same

private theorem appendEffectWithActivity_preservesReadMetadata (state : List StateDecl)
    (effect : Effect) (scope : ScalarReadEffect effect) (before after : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state effect none before = .ok after) :
    ∃ middle, Impact.appendEffect state effect before = .ok middle ∧
      planReadMetadata after = planReadMetadata middle := by
  rw [appendEffectWithActivity_none_shape state effect scope before] at accepted
  cases lower : Impact.appendEffect state effect before with
  | error message =>
    simp [lower, bind, Except.bind] at accepted
  | ok middle =>
    refine ⟨middle, rfl, ?_⟩
    by_cases empty : before.activityGuards.isEmpty = true
    · have equal : middle = after := by
        simpa [lower, empty, bind, Except.bind, pure, Except.pure] using accepted
      exact congrArg planReadMetadata equal.symm
    · have equal :
          {middle with activityGuards := before.activityGuards ++
            List.replicate (middle.operations.length - before.operations.length) none} =
            after := by
        simpa [lower, empty, bind, Except.bind, pure, Except.pure] using accepted
      calc
        planReadMetadata after = planReadMetadata
            {middle with activityGuards := before.activityGuards ++
              List.replicate (middle.operations.length - before.operations.length) none} :=
          congrArg planReadMetadata equal.symm
        _ = planReadMetadata middle := rfl

private theorem appendEffectWithActivity_read_chunk (state : List StateDecl)
    (effect : Effect) (scope : ScalarReadEffect effect) (before after : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state effect none before = .ok after) :
    planReadMetadata after =
      planReadMetadata before ++ effectReadChunk effect before.reads.length := by
  obtain ⟨middle, lower, sameReads⟩ :=
    appendEffectWithActivity_preservesReadMetadata state effect scope before after accepted
  rw [sameReads]
  exact appendEffect_read_chunk state effect scope before middle lower

private theorem trace_read_metadata (state : List StateDecl)
    (items : List (Effect × Nat)) (initial result : Impact.Plan) (offsets : List Nat)
    (scope : ScalarReadEffects (items.map Prod.fst))
    (trace : Impact.GuardedEffectTrace state [] items initial result offsets) :
    planReadMetadata result = planReadMetadata initial ++
      (readChunks (items.map Prod.fst) initial.reads.length).flatten := by
  induction items generalizing initial result offsets with
  | nil =>
    cases trace
    simp [readChunks]
  | cons item rest ih =>
    cases trace with
    | cons step tail =>
      rename_i middle offsets
      have headScope : ScalarReadEffect item.1 := by
        apply scope
        simp
      have tailScope : ScalarReadEffects (rest.map Prod.fst) := by
        intro effect member
        apply scope effect
        simp [member]
      have unguardedStep :
          Impact.appendEffectWithActivity state item.1 none initial = .ok middle := by
        simpa using step
      have resultReads := appendEffectWithActivity_read_chunk
        state item.1 headScope initial middle unguardedStep
      have tailResult := ih middle result offsets tailScope tail
      have ordinal : middle.reads.length = initial.reads.length +
          (effectReadChunk item.1 initial.reads.length).length := by
        have lengths := congrArg List.length resultReads
        simpa [planReadMetadata, List.length_append] using lengths
      rw [tailResult, resultReads, ordinal]
      simp [readChunks, List.flatten_cons, List.append_assoc]

theorem lowerWithEffectBoundaries_read_metadata (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (boundaries : List Nat)
    (accepted : Impact.lowerWithEffectBoundaries state entry = .ok (plan, boundaries))
    (unguarded : entry.effectGuards = [])
    (scope : ScalarReadEffects entry.effects) :
    ∃ inputPlan, Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan ∧
      planReadMetadata plan = planReadMetadata inputPlan ++
        (readChunks entry.effects inputPlan.reads.length).flatten := by
  have lowered : Impact.lower state entry = .ok plan := by
    unfold Impact.lower
    rw [accepted]
    rfl
  obtain ⟨_, inputPlan, _, prefixAccepted, trace⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state entry plan lowered
  rw [unguarded] at trace
  have zippedEffects : (entry.effects.zipIdx).map Prod.fst = entry.effects := by
    induction entry.effects with
    | nil => rfl
    | cons effect rest ih => simp
  have zippedScope : ScalarReadEffects ((entry.effects.zipIdx).map Prod.fst) := by
    simpa [zippedEffects] using scope
  exact ⟨inputPlan, prefixAccepted, by
    simpa [zippedEffects] using trace_read_metadata state entry.effects.zipIdx
      inputPlan plan _ zippedScope trace⟩

end Noctium.Verification.GenericStateCheckedReadTrace
