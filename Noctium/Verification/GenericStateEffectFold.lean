import Noctium.Verification.GenericStateEffectStep
import Noctium.Verification.GenericStateReadCandidates
import Noctium.Verification.GuardedPlanActivity
import Noctium.Verification.GuardedPlanAssertions

namespace Noctium.Verification.GenericStateEffectFold
open Backend NativeRelation NativeState ScalarNormalization
open GenericStatePrefixEnvironment GenericStateEffectStep GenericStateEffectValidation
open GenericStateCheckedReadTrace GenericStateInputValues

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- A checked native run ordered by the exact compiler trace produces the
original typed source fold and retains agreement on every newly bound read. -/
theorem checked_effects_fold (ctx : EvalContext) (state : List StateDecl)
    (items : List (Effect × Nat)) (types finalTypes : TypeEnv)
    (sourceEnv complete : EvalEnv) (current : LedgerState)
    (slots : List NativeState.Slot) (reads : List NativeState.Cell)
    (before plan : Impact.Plan) (offsets : List Nat) (chunks : List (List Impact.Op))
    (segments : List (List NativeState.Op)) (final : NativeState.Machine)
    (validated : ValidatedEffects state types (items.map Prod.fst) finalTypes)
    (compiled : GuardedEffectEvaluation.GuardedEffectOperationChunks state [] items
      before plan offsets chunks)
    (evaluated : chunks.mapM (fun chunk => chunk.mapM (GenericStateOps.evalOp ctx complete)) = .ok segments)
    (trace : GenericStateVM.RunsChunks segments ⟨[.vector slots], reads⟩ final)
    (operands : ∀ effect ∈ items.map Prod.fst, ScalarOperands effect)
    (candidates : ∀ effect ∈ items.map Prod.fst, ReadCandidate effect complete)
    (guards : ∀ effect ∈ items.map Prod.fst, GuardTrue ctx effect complete)
    (agrees : AgreesOnTypes types sourceEnv complete)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus) (modulus : ctx.modulus = Field.modulus) :
    ∃ finalEnv finalState finalSlots finalReads,
      SourceEffects.fold ctx (items.map Prod.fst) (sourceEnv, current) = .ok (finalEnv, finalState) ∧
      GenericStateEncoding.encodeState state finalState = some finalSlots ∧
      final = ⟨[.vector finalSlots], finalReads⟩ ∧
      AgreesOnTypes finalTypes finalEnv complete := by
  induction compiled generalizing types finalTypes sourceEnv current slots reads segments final with
  | nil before =>
    cases validated
    change Except.ok [] = Except.ok segments at evaluated
    cases evaluated
    cases trace
    exact ⟨sourceEnv, current, slots, reads, rfl, encoded, rfl, agrees⟩
  | @cons item rest before next plan offsets chunk chunks step operations tail ih =>
    obtain ⟨nextTypes, validatedHead, validatedTail⟩ := ValidatedEffects.uncons validated
    simp only [List.mapM_cons, bind_ok] at evaluated
    obtain ⟨head, headEvaluation, remaining, tailEvaluation, joined⟩ := evaluated
    cases joined
    cases trace with
    | cons _ _ _ middle _ firstRun restRun =>
      have compiledHead : Impact.appendEffectWithActivity state item.1 none before = .ok next := by
        simpa using step
      have exactSuffix : (next.operations.drop before.operations.length).mapM
          (GenericStateOps.evalOp ctx complete) = .ok head := by
        rw [operations, List.drop_left]
        exact headEvaluation
      obtain ⟨nextEnv, nextState, nextSlots, nextReads, firstStep, nextEncoded, middleShape, nextAgrees⟩ :=
        checked_effect_step ctx state types nextTypes item.1 sourceEnv complete current slots reads
          before next head middle validatedHead (operands item.1 (by simp)) agrees
          (candidates item.1 (by simp)) (guards item.1 (by simp)) compiledHead exactSuffix
          firstRun encoded distinct stateBound modulus
      subst middle
      obtain ⟨finalEnv, finalState, finalSlots, finalReads, restFold, finalEncoded, finalShape, finalAgrees⟩ :=
        ih nextTypes finalTypes nextEnv nextState nextSlots nextReads remaining final validatedTail
          tailEvaluation restRun (fun effect member => operands effect (by simp [member]))
          (fun effect member => candidates effect (by simp [member]))
          (fun effect member => guards effect (by simp [member])) nextAgrees nextEncoded
      refine ⟨finalEnv, finalState, finalSlots, finalReads, ?_, finalEncoded, finalShape, finalAgrees⟩
      rw [List.map_cons, SourceEffects.fold_cons, firstStep]
      exact restFold

private theorem scalar_read_scope {effects : List Effect} (admitted : ScalarStateEffects effects) :
    ScalarReadEffects effects := by
  induction admitted with
  | nil => intro effect member; exact False.elim (List.not_mem_nil member)
  | @cons effect rest head tail ih =>
    intro found member
    rcases List.mem_cons.mp member with rfl | inTail
    · cases head <;> constructor
    · exact ih found inTail

theorem unguarded_read_scope (entry : Entrypoint) (unguarded : entry.effectGuards = [])
    (admitted : ScalarStateEffects entry.effects) :
    GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx := by
  rw [unguarded]
  intro item member
  apply GuardedScalarReadEffect.unguarded
  apply scalar_read_scope admitted item.1
  have projected : item.1 ∈ entry.effects.zipIdx.map Prod.fst := List.mem_map_of_mem member
  simpa only [List.zipIdx_map_fst] using projected

/-- An accepted unguarded entrypoint with a typed initial state and decoded
candidate bindings agrees with checked native execution of its full effect
sequence, including the actual public-input prefix and the emitted assertion
checks. The result exposes the final typed environment for return checking. -/
theorem lower_checked_effects (ctx : EvalContext) (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (base decoded : EvalEnv) (witness : Assignment)
    (initial : LedgerState) (slots : List NativeState.Slot)
    (native : List NativeState.Op) (final : NativeState.Machine)
    (lowered : Impact.lower state entry = .ok plan)
    (unguarded : entry.effectGuards = []) (admitted : ScalarStateEffects entry.effects)
    (operands : ∀ effect ∈ entry.effects, ScalarOperands effect)
    (publicCompatible : ∀ input ∈ entry.circuit.inputs, Impact.publicInputScalarCompatible input)
    (decodedReads : decodeReads (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs))
      witness = .ok decoded)
    (distinctReads : (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).Pairwise
      (fun left right => left.name ≠ right.name))
    (readFacts : ∀ effect ∈ entry.effects, match effect with
      | .readCell _ destination ty | .readMap _ destination _ ty _ =>
        base.lookup destination = none ∧
        ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok () ∧
        (witness ("%input_" ++ destination)).val ≤ Native.sourceMaximum ty
      | _ => True)
    (guardValues : ∀ guard ∈ plan.guards, guard.eval ctx (base ++ decoded) = .ok true)
    (initialAgreement : AgreesOnTypes (initialEffectTypeEnv entry) base (base ++ decoded))
    (encoded : GenericStateEncoding.encodeState state initial = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus) (modulus : ctx.modulus = Field.modulus)
    (evaluated : GenericStateOps.evalPlan ctx (base ++ decoded) plan = .ok native)
    (checked : NativeState.run native ⟨[.vector slots], []⟩ = some final) :
    ∃ finalTypes finalEnv finalState finalSlots finalReads,
      ValidatedEffects state (initialEffectTypeEnv entry) entry.effects finalTypes ∧
      runEffectsWithGuardsAndEnv ctx entry.effects entry.effectGuards base initial =
        .ok (finalEnv, finalState) ∧
      GenericStateEncoding.encodeState state finalState = some finalSlots ∧
      final = ⟨[.vector finalSlots], finalReads⟩ ∧
      AgreesOnTypes finalTypes finalEnv (base ++ decoded) := by
  have scope := unguarded_read_scope entry unguarded admitted
  obtain ⟨finalTypes, validated⟩ := lower_validated_effects state entry plan lowered unguarded admitted
  obtain ⟨offsets, inputPlan, chunks, publicNative, segments, _, publicAccepted,
    chunkTrace, _, publicEvaluated, effectEvaluated, sequence⟩ :=
    GuardedPlanActivity.lower_scoped_guarded_evaluation state entry plan ctx (base ++ decoded)
      native lowered scope evaluated
  obtain ⟨publicReads, _, publicRun⟩ := GenericStateAdmissionPrefix.public_prefix_run
    entry.circuit.inputs inputPlan ctx (base ++ decoded) publicNative [.vector slots] []
    publicAccepted publicCompatible publicEvaluated
  rw [sequence, NativeState.run_append, publicRun, Option.bind_some] at checked
  have nativeTrace := (GenericStateVM.run_chunks_iff segments _ final).mp checked
  have orderedEffects := List.zipIdx_map_fst 0 entry.effects
  have typedTrace : ValidatedEffects state (initialEffectTypeEnv entry)
      (entry.effects.zipIdx.map Prod.fst) finalTypes := by rwa [orderedEffects]
  have compiled : GuardedEffectEvaluation.GuardedEffectOperationChunks state [] entry.effects.zipIdx
      inputPlan plan offsets chunks := by simpa [unguarded] using chunkTrace
  have candidates : ∀ effect ∈ entry.effects, ReadCandidate effect (base ++ decoded) := by
    intro effect present
    have facts := readFacts effect present
    cases effect <;> try trivial
    case readCell name destination ty =>
      obtain ⟨value, lookup, canonical, _⟩ := GenericStateReadCandidates.readCell_candidate
        state entry plan base decoded witness name destination ty lowered scope present decodedReads
        distinctReads facts.1 facts.2.1 facts.2.2
      exact ⟨value, lookup, canonical⟩
    case readMap name destination keyTy valueTy key =>
      obtain ⟨value, lookup, canonical, _⟩ := GenericStateReadCandidates.readMap_candidate
        state entry plan base decoded witness name destination keyTy valueTy key lowered scope present
        decodedReads distinctReads facts.1 facts.2.1 facts.2.2
      exact ⟨value, lookup, canonical⟩
  have assertions : ∀ effect ∈ entry.effects, GuardTrue ctx effect (base ++ decoded) := by
    intro effect present
    cases effect <;> try trivial
    case require condition =>
      have projected : Effect.require condition ∈ entry.effects.zipIdx.map Prod.fst := by
        simpa only [orderedEffects] using present
      obtain ⟨⟨effect, index⟩, occurrence, same⟩ := List.mem_map.mp projected
      change effect = Effect.require condition at same
      subst effect
      exact guardValues condition (GuardedPlanAssertions.lower_unguarded_require_assertion
        state entry plan condition index lowered scope occurrence (by simp [unguarded]))
  obtain ⟨finalEnv, finalState, finalSlots, finalReads, folded, finalEncoded, layout, agreement⟩ :=
    checked_effects_fold ctx state entry.effects.zipIdx (initialEffectTypeEnv entry) finalTypes
      base (base ++ decoded) initial slots publicReads inputPlan plan offsets chunks segments final
      typedTrace compiled effectEvaluated nativeTrace (by rwa [orderedEffects])
      (by rwa [orderedEffects]) (by rwa [orderedEffects]) initialAgreement encoded distinct
      stateBound modulus
  refine ⟨finalTypes, finalEnv, finalState, finalSlots, finalReads, validated, ?_, finalEncoded,
    layout, agreement⟩
  rw [unguarded]
  change SourceEffects.fold ctx entry.effects (base, initial) = .ok (finalEnv, finalState)
  simpa only [orderedEffects] using folded

end Noctium.Verification.GenericStateEffectFold
