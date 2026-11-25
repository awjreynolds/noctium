import Noctium.Verification.GenericStateAdmissionPrefix
import Noctium.Verification.GuardedEffectPrefix

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

inductive GuardedScalarReadEffect : Option (Expr .bool) → Effect → Prop where
  | unguarded {effect : Effect} (scope : ScalarReadEffect effect) :
      GuardedScalarReadEffect none effect
  | require (condition required : Expr .bool) :
      GuardedScalarReadEffect (some condition) (.require required)
  | readCell (condition : Expr .bool) (name destination : String) (ty : Ty) :
      GuardedScalarReadEffect (some condition) (.readCell name destination ty)
  | readMap (condition : Expr .bool) (name destination : String)
      (keyTy valueTy : Ty) (key : Expr keyTy) :
      GuardedScalarReadEffect (some condition)
        (.readMap name destination keyTy valueTy key)
  | writeCell (condition : Expr .bool) (name : String) (ty : Ty)
      (value : Expr ty) :
      GuardedScalarReadEffect (some condition) (.writeCell name ty value)
  | writeMap (condition : Expr .bool) (name : String) (keyTy valueTy : Ty)
      (key : Expr keyTy) (value : Expr valueTy) :
      GuardedScalarReadEffect (some condition)
        (.writeMap name keyTy valueTy key value)

/-- Tie the guard to each indexed effect from the production fold. Guard
metadata is handled for cell and plain map reads. Guarded writes and
requirements preserve the read list. The decoder checks read types separately. -/
def GuardedScalarReadEffects (guards : List (Option (Expr .bool)))
    (items : List (Effect × Nat)) : Prop :=
  ∀ item ∈ items,
    GuardedScalarReadEffect (guards[item.2]?.getD none) item.1

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

private theorem appendEffectWithActivity_read_chunk (state : List StateDecl)
    (effect : Effect) (scope : ScalarReadEffect effect) (before after : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state effect none before = .ok after) :
    planReadMetadata after =
      planReadMetadata before ++ effectReadChunk effect before.reads.length := by
  obtain ⟨middle, lower, _, sameReads⟩ :=
    GuardedEffectPrefix.appendEffectWithActivity_none_result state effect before after accepted
  change after.reads.map readMetadata = _
  rw [sameReads]
  exact appendEffect_read_chunk state effect scope before middle lower

theorem appendEffectWithActivity_guarded_read_chunk (state : List StateDecl)
    (effect : Effect) (guard : Option (Expr .bool))
    (scope : GuardedScalarReadEffect guard effect) (before after : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state effect guard before = .ok after) :
    planReadMetadata after =
      planReadMetadata before ++ effectReadChunk effect before.reads.length := by
  cases scope with
  | unguarded scope =>
    exact appendEffectWithActivity_read_chunk state effect scope before after accepted
  | readCell condition name destination ty =>
    obtain ⟨_, _, read, readName, readTy, _, reads, _, _⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_readCell_provenance
        state name destination ty condition before after accepted
    change after.reads.map readMetadata = _
    rw [reads]
    simp [planReadMetadata, readMetadata, effectReadChunk, readName, readTy]
  | readMap condition name destination keyTy valueTy key =>
    have reads := GuardedEffectPrefix.appendEffectWithActivity_readMap_read_suffix
      state name destination keyTy valueTy key condition before after accepted
    change after.reads.map readMetadata = _
    rw [reads]
    simp [planReadMetadata, readMetadata, effectReadChunk]
  | writeCell condition name ty value =>
    have reads := GuardedEffectPrefix.appendEffectWithActivity_guarded_writeCell_no_reads
      state name ty value condition before after accepted
    change after.reads.map readMetadata = _
    rw [reads]
    simp [planReadMetadata, effectReadChunk]
  | writeMap condition name keyTy valueTy key value =>
    have reads := GuardedEffectPrefix.appendEffectWithActivity_guarded_writeMap_no_reads
      state name keyTy valueTy key value condition before after accepted
    change after.reads.map readMetadata = _
    rw [reads]
    simp [planReadMetadata, effectReadChunk]
  | require condition required =>
    have reads := GuardedEffectPrefix.appendEffectWithActivity_guarded_require_no_reads
      state condition required before after accepted
    change after.reads.map readMetadata = _
    rw [reads]
    simp [planReadMetadata, effectReadChunk]

private theorem trace_guarded_read_metadata (state : List StateDecl)
    (guards : List (Option (Expr .bool))) (items : List (Effect × Nat))
    (initial result : Impact.Plan) (offsets : List Nat)
    (scope : GuardedScalarReadEffects guards items)
    (trace : Impact.GuardedEffectTrace state guards items initial result offsets) :
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
      have headScope : GuardedScalarReadEffect
          (guards[item.2]?.getD none) item.1 := by
        apply scope
        simp
      have tailScope : GuardedScalarReadEffects guards rest := by
        intro next member
        apply scope next
        simp [member]
      have resultReads := appendEffectWithActivity_guarded_read_chunk
        state item.1 (guards[item.2]?.getD none) headScope initial middle step
      have tailResult := ih middle result offsets tailScope tail
      have ordinal : middle.reads.length = initial.reads.length +
          (effectReadChunk item.1 initial.reads.length).length := by
        have lengths := congrArg List.length resultReads
        simpa [planReadMetadata, List.length_append] using lengths
      rw [tailResult, resultReads, ordinal]
      simp [readChunks, List.flatten_cons, List.append_assoc]

/-- The production guarded effect trace preserves projected read metadata for
the supported guarded scalar fragment. Guarded cell and plain map reads keep
their source names and types. Guarded writes and requirements add no read
descriptors, and ordinals follow preceding reads. -/
theorem lowerWithEffectBoundaries_guarded_read_metadata (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (boundaries : List Nat)
    (accepted : Impact.lowerWithEffectBoundaries state entry = .ok (plan, boundaries))
    (scope : GuardedScalarReadEffects entry.effectGuards (entry.effects.zipIdx)) :
    ∃ inputPlan, Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan ∧
      planReadMetadata plan = planReadMetadata inputPlan ++
        (readChunks entry.effects inputPlan.reads.length).flatten := by
  have lowered : Impact.lower state entry = .ok plan := by
    unfold Impact.lower
    rw [accepted]
    rfl
  obtain ⟨_, inputPlan, _, prefixAccepted, trace⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state entry plan lowered
  have zippedEffects : (entry.effects.zipIdx).map Prod.fst = entry.effects := by
    induction entry.effects with
    | nil => rfl
    | cons effect rest ih => simp
  exact ⟨inputPlan, prefixAccepted, by
    simpa [zippedEffects] using trace_guarded_read_metadata state entry.effectGuards
      entry.effects.zipIdx inputPlan plan _ scope trace⟩

theorem lowerWithEffectBoundaries_read_metadata (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (boundaries : List Nat)
    (accepted : Impact.lowerWithEffectBoundaries state entry = .ok (plan, boundaries))
    (unguarded : entry.effectGuards = [])
    (scope : ScalarReadEffects entry.effects) :
    ∃ inputPlan, Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan ∧
      planReadMetadata plan = planReadMetadata inputPlan ++
        (readChunks entry.effects inputPlan.reads.length).flatten := by
  apply lowerWithEffectBoundaries_guarded_read_metadata state entry plan boundaries accepted
  rw [unguarded]
  intro item member
  have mapped : item.1 ∈ (entry.effects.zipIdx).map Prod.fst :=
    List.mem_map.mpr ⟨item, member, rfl⟩
  exact .unguarded (scope item.1 (by simpa using mapped))

end Noctium.Verification.GenericStateCheckedReadTrace
