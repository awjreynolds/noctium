import Noctium.Verification.GenericStateEffectFold
import Noctium.Verification.GuardedMapReadAuthentication
import Noctium.Verification.GuardedRequireSemantics
import Noctium.Verification.GuardedWriteSourceStep
import Noctium.Verification.GuardedWriteEffectStep
import Noctium.Verification.GuardedCellEffectStep
import Noctium.Verification.GuardedSourceEffects
import Noctium.Verification.GuardedPlanExecution
import Noctium.Verification.GuardedPlanTrace

namespace Noctium.Verification.GuardedStateEffectFold
open Backend NativeRelation NativeState ScalarNormalization
open GenericStateCheckedReadTrace GenericStateEffectStep GenericStateEffectValidation
open GenericStateInputValues GenericStatePrefixEnvironment
open GuardedEffectEvaluation

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem assertion_prefix {state : List StateDecl} {guards : List (Option (Expr .bool))}
    {items : List (Effect × Nat)} {before plan : Impact.Plan} {offsets : List Nat}
    {chunks : List (List Impact.Op)}
    (compiled : GuardedEffectOperationChunks state guards items before plan offsets chunks)
    (scope : GuardedScalarReadEffects guards items) :
    ∀ expression ∈ before.guards, expression ∈ plan.guards := by
  induction compiled with
  | nil _ => exact fun _ member => member
  | @cons item rest before next plan offsets chunk chunks step _ _ ih =>
    intro expression member
    apply ih (fun found present => scope found (by simp [present]))
    have appended := GuardedPlanAssertions.appendEffectWithActivity_guarded_assertion_chunk
      state item.1 (guards[item.2]?.getD none) (scope item (by simp)) before next step
    rw [appended]
    exact List.mem_append_left _ member

/-- Inactive public reads bind the typed scalar default in the complete candidate
environment. A successful active read authenticates its value against the VM. -/
def InactiveReadCandidate (effect : Effect) (complete : EvalEnv) : Prop :=
  match effect with
  | .readCell _ destination ty | .readMap _ destination _ ty _ =>
    ∃ support : ScalarType ty,
      complete.lookup destination = some (Value.pack ty (sourceValue support zero))
  | _ => True

private theorem candidate_is_default {ty : Ty} {candidate : ty.Denote}
    (canonical : Canonical ty candidate) (asZero : sourceScalar? ty candidate = some zero) :
    ∃ support : ScalarType ty, candidate = sourceValue support zero := by
  obtain ⟨support⟩ := GenericStateWriteEvaluation.scalarType_of_canonical canonical
  refine ⟨support, ?_⟩
  have fieldZero := Option.some.inj ((sourceScalar_number support candidate).symm.trans asZero)
  have noWrap := scalar_no_wrap _ (scalar_number_canonical support candidate canonical)
  have numberZero : number support candidate = 0 :=
    noWrap.symm.trans (congrArg Fin.val fieldZero)
  cases support with
  | native => exact numberZero
  | uint => exact numberZero
  | bool => cases candidate <;> simp_all [ScalarNormalization.number, sourceValue, zero]

private theorem checked_guarded_readMap (ctx : EvalContext) (state : List StateDecl)
    (types : TypeEnv) (name destination : String) (keyTy valueTy : Ty) (key : Expr keyTy)
    (guard : Expr .bool) (sourceEnv complete : EvalEnv) (current : LedgerState)
    (slots : List NativeState.Slot) (reads : List NativeState.Cell)
    (before plan : Impact.Plan) (segment : List NativeState.Op) (after : NativeState.Machine)
    (declared : HasDeclaration state name (.map keyTy valueTy))
    (fresh : types.lookup destination = none)
    (keyValid : key.validate stateEffectCaps types = .ok ())
    (operand : ScalarExpression key) (agrees : AgreesOnTypes types sourceEnv complete)
    (candidate : ReadCandidate (.readMap name destination keyTy valueTy key) complete)
    (active : Bool) (sourceGuard : guard.eval ctx sourceEnv = .ok active)
    (sameGuard : guard.eval ctx sourceEnv = guard.eval ctx complete)
    (inactive : active = false →
      InactiveReadCandidate (.readMap name destination keyTy valueTy key) complete)
    (compiled : Impact.appendEffectWithActivity state (.readMap name destination keyTy valueTy key)
      (some guard) before = .ok plan)
    (evaluated : (if active then (plan.operations.drop before.operations.length).mapM
        (GenericStateOps.evalOp ctx complete) else .ok []) = .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ nextEnv nextReads,
      runEffectsWithGuardsAndEnv ctx [.readMap name destination keyTy valueTy key] [some guard]
        sourceEnv current = .ok (nextEnv, current) ∧
      after = ⟨[.vector slots], nextReads⟩ ∧
      AgreesOnTypes (types ++ [(destination, valueTy)]) nextEnv complete := by
  cases active with
  | false =>
    obtain ⟨support, lookup⟩ := inactive rfl
    have empty : segment = [] := (Except.ok.inj (show Except.ok [] = .ok segment from evaluated)).symm
    subst segment
    exact ⟨_, reads,
      GuardedScalarInput.run_inactive_scalarMap_read ctx sourceEnv current name destination
        key support guard sourceGuard,
      (Option.some.inj checked).symm,
      extend_read types sourceEnv complete destination valueTy _ agrees fresh lookup⟩
  | true =>
    obtain ⟨value, lookup, canonical⟩ := candidate
    obtain ⟨declaration, found, kind⟩ := declared
    obtain ⟨sourceStep, machine⟩ :=
      GuardedMapReadAuthentication.active_readMap_candidate_source_step ctx sourceEnv complete
        state current slots name destination keyTy valueTy key operand
        (eval_scoped types sourceEnv complete agrees ctx stateEffectCaps key keyValid)
        guard sourceGuard sameGuard value before plan segment reads after compiled
        declaration found kind encoded lookup canonical modulus (by simpa using evaluated) checked
    exact ⟨_, _, sourceStep, machine,
      extend_read types sourceEnv complete destination valueTy _ agrees fresh lookup⟩

private theorem checked_guarded_require (ctx : EvalContext) (state : List StateDecl)
    (types : TypeEnv) (guard required : Expr .bool) (sourceEnv complete : EvalEnv)
    (current : LedgerState) (slots : List NativeState.Slot) (reads : List NativeState.Cell)
    (before plan : Impact.Plan) (segment : List NativeState.Op) (after : NativeState.Machine)
    (requiredValid : required.validate stateEffectCaps types = .ok ())
    (operand : ScalarExpression required) (agrees : AgreesOnTypes types sourceEnv complete)
    (active : Bool) (sourceGuard : guard.eval ctx sourceEnv = .ok active)
    (completeGuard : guard.eval ctx complete = .ok active)
    (assertion : (Impact.totalizeActivityCondition guard required).eval ctx complete = .ok true)
    (compiled : Impact.appendEffectWithActivity state (.require required)
      (some guard) before = .ok plan)
    (evaluated : (if active then (plan.operations.drop before.operations.length).mapM
        (GenericStateOps.evalOp ctx complete) else .ok []) = .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after)
    (modulus : ctx.modulus = Field.modulus) :
    runEffectsWithGuardsAndEnv ctx [.require required] [some guard] sourceEnv current =
      .ok (sourceEnv, current) ∧ after = ⟨[.vector slots], reads⟩ := by
  have shape := GuardedRequireSemantics.appendEffectWithActivity_require_shape
    state guard required before plan compiled
  have empty : segment = [] := by
    have evalNil : (Except.ok [] : Except String (List NativeState.Op)) = .ok segment := by
      cases active <;> simpa [shape, List.drop_length, Pure.pure, Except.pure] using evaluated
    exact (Except.ok.inj evalNil).symm
  subst segment
  refine ⟨?_, (Option.some.inj checked).symm⟩
  rw [GuardedRequireSemantics.run_guarded_require ctx sourceEnv current guard required active sourceGuard]
  cases active with
  | false => rfl
  | true =>
    have completeRequired : required.eval ctx complete = .ok true :=
      (GuardedRequireSemantics.totalizeActivityCondition_active_eval ctx complete guard required
        operand modulus completeGuard).symm.trans assertion
    have sourceRequired := (eval_scoped types sourceEnv complete agrees ctx stateEffectCaps
      required requiredValid).trans completeRequired
    exact GenericStateVM.require_source_step ctx sourceEnv current required sourceRequired

private theorem unguarded_singleton (ctx : EvalContext) (effect : Effect)
    (env : EvalEnv) (state : LedgerState) :
    runEffectsWithGuardsAndEnv ctx [effect] [none] env state =
      SourceEffects.step ctx effect (env, state) := by
  change runEffectsWithEnv ctx [effect] env state = _
  rw [SourceEffects.runEffectsWithEnv_eq_fold, SourceEffects.fold_cons]
  cases SourceEffects.step ctx effect (env, state) <;> rfl

private theorem guard_some_eval (ctx : EvalContext) (env : EvalEnv) (guard : Expr .bool)
    (activity : Option Bool)
    (evaluated : (some guard).mapM (Expr.eval ctx env) = .ok activity) :
    ∃ active, activity = some active ∧ guard.eval ctx env = .ok active := by
  cases result : guard.eval ctx env with
  | error message => simp [Option.mapM, result, Except.map, Functor.map] at evaluated
  | ok active =>
    have same : some active = activity := by
      simpa [Option.mapM, result, Except.map, Functor.map] using evaluated
    exact ⟨active, same.symm, rfl⟩

private theorem checked_step (ctx : EvalContext) (state : List StateDecl)
    (types nextTypes : TypeEnv) (effect : Effect) (guard : Option (Expr .bool))
    (sourceEnv complete : EvalEnv) (current : LedgerState)
    (slots : List NativeState.Slot) (reads : List NativeState.Cell)
    (before plan : Impact.Plan) (segment : List NativeState.Op) (after : NativeState.Machine)
    (validated : EffectValidation state types effect nextTypes)
    (scope : GuardedScalarReadEffect guard effect)
    (operands : ScalarOperands effect) (agrees : AgreesOnTypes types sourceEnv complete)
    (candidate : ReadCandidate effect complete)
    (guardValid : ∀ condition, guard = some condition →
      condition.validate stateEffectCaps types = .ok ())
    (inactiveCandidate : ∀ condition, guard = some condition →
      condition.eval ctx complete = .ok false → InactiveReadCandidate effect complete)
    (assertions : ∀ condition ∈ GuardedPlanAssertions.guardedEffectAssertionChunk
      guard effect before.reads.length, condition.eval ctx complete = .ok true)
    (compiled : Impact.appendEffectWithActivity state effect guard before = .ok plan)
    (activity : Option Bool) (activation : guard.mapM (Expr.eval ctx complete) = .ok activity)
    (evaluated : (if activity.getD true then
        (plan.operations.drop before.operations.length).mapM
          (GenericStateOps.evalOp ctx complete) else .ok []) = .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus) (modulus : ctx.modulus = Field.modulus) :
    ∃ nextEnv nextState nextSlots nextReads,
      runEffectsWithGuardsAndEnv ctx [effect] [guard] sourceEnv current = .ok (nextEnv, nextState) ∧
      GenericStateEncoding.encodeState state nextState = some nextSlots ∧
      after = ⟨[.vector nextSlots], nextReads⟩ ∧
      AgreesOnTypes nextTypes nextEnv complete := by
  cases guard with
  | none =>
    have noneActivity : activity = none := (Except.ok.inj
      (show (Except.ok none : Except String (Option Bool)) = .ok activity from activation)).symm
    subst activity
    have guardHolds : GuardTrue ctx effect complete := by
      cases effect <;> try exact True.intro
      case require condition =>
        apply assertions
        change condition ∈ [condition]
        simp
    rw [unguarded_singleton]
    exact checked_effect_step ctx state types nextTypes effect sourceEnv complete current
      slots reads before plan segment after validated operands agrees candidate guardHolds
      compiled evaluated checked encoded distinct stateBound modulus
  | some condition =>
    obtain ⟨active, activityShape, completeGuard⟩ := guard_some_eval ctx complete condition
      activity activation
    subst activity
    have valid := guardValid condition rfl
    have sameGuard := eval_scoped types sourceEnv complete agrees ctx stateEffectCaps condition valid
    have sourceGuard := sameGuard.trans completeGuard
    have skipped : active = false → segment = [] := by
      intro inactive
      rw [inactive] at evaluated
      exact (Except.ok.inj (show Except.ok [] = .ok segment from evaluated)).symm
    have emptyRun : active = false → after = ⟨[.vector slots], reads⟩ := by
      intro inactive
      rw [skipped inactive] at checked
      exact (Option.some.inj checked).symm
    have suffix : active = true →
        (plan.operations.drop before.operations.length).mapM
          (GenericStateOps.evalOp ctx complete) = .ok segment := by
      intro enabled
      simpa [enabled] using evaluated
    cases scope with
    | readCell _ name destination ty =>
      obtain ⟨nextEnv, nextState, nextSlots, nextReads, source, encoding, machine, agreement, _⟩ :=
        GuardedCellEffectStep.checked_guarded_readCell ctx state types nextTypes sourceEnv complete
          current slots reads name destination ty condition active validated agrees candidate
          valid completeGuard
          (fun inactive => inactiveCandidate condition rfl (by simpa [inactive] using completeGuard))
          before plan segment after compiled suffix skipped checked encoded modulus
      exact ⟨nextEnv, nextState, nextSlots, nextReads, source, encoding, machine, agreement⟩
    | require _ required =>
      cases validated with
      | require requiredValid =>
        have assertion := assertions (Impact.totalizeActivityCondition condition required) (by
          simp [GuardedPlanAssertions.guardedEffectAssertionChunk])
        obtain ⟨source, machine⟩ := checked_guarded_require ctx state types condition required
          sourceEnv complete current slots reads before plan segment after requiredValid operands agrees
          active sourceGuard completeGuard assertion compiled evaluated checked modulus
        exact ⟨sourceEnv, current, slots, reads, source, encoded, machine, agrees⟩
    | readMap _ name destination keyTy valueTy key =>
      cases validated with
      | readMap declared keyValid fresh =>
        obtain ⟨nextEnv, nextReads, source, machine, agreement⟩ :=
          checked_guarded_readMap ctx state types name destination keyTy valueTy key condition
            sourceEnv complete current slots reads before plan segment after declared fresh
            keyValid operands agrees candidate active sourceGuard sameGuard
            (fun inactive => inactiveCandidate condition rfl (by simpa [inactive] using completeGuard))
            compiled evaluated checked encoded modulus
        exact ⟨nextEnv, current, slots, nextReads, source, encoded, machine, agreement⟩
    | writeCell _ name ty expression =>
      cases enabled : active with
      | false =>
        cases validated
        exact ⟨sourceEnv, current, slots, reads,
          GuardedWriteSourceStep.run_inactive_writeCell ctx sourceEnv current name expression condition
            (by simpa [enabled] using sourceGuard),
          encoded, emptyRun enabled, agrees⟩
      | true =>
        obtain ⟨nextEnv, nextState, nextSlots, nextReads, source, encoding, machine, agreement, _, _⟩ :=
          GuardedWriteEffectStep.checked_active_writeCell_step ctx state types nextTypes sourceEnv
            complete current slots reads name ty expression condition validated operands agrees
            (by simpa [enabled] using sourceGuard) sameGuard before plan segment after compiled
            (suffix enabled) checked encoded distinct stateBound modulus
        exact ⟨nextEnv, nextState, nextSlots, nextReads, source, encoding, machine, agreement⟩
    | writeMap _ name keyTy valueTy key value =>
      cases enabled : active with
      | false =>
        cases validated
        exact ⟨sourceEnv, current, slots, reads,
          GuardedWriteSourceStep.run_inactive_writeMap ctx sourceEnv current name key value condition
            (by simpa [enabled] using sourceGuard),
          encoded, emptyRun enabled, agrees⟩
      | true =>
        obtain ⟨nextEnv, nextState, nextSlots, nextReads, source, encoding, machine, agreement, _, _⟩ :=
          GuardedWriteEffectStep.checked_active_writeMap_step ctx state types nextTypes sourceEnv
            complete current slots reads name keyTy valueTy key value condition validated
            operands.1 operands.2 agrees (by simpa [enabled] using sourceGuard) sameGuard
            before plan segment after compiled (suffix enabled) checked encoded distinct stateBound modulus
        exact ⟨nextEnv, nextState, nextSlots, nextReads, source, encoding, machine, agreement⟩

/-- Checked active chunks preserve the ordered typed source execution.
The compiled chunk determines the operations, and the validated prefix
ties its guard to the current source bindings. -/
theorem checked_effects_fold (ctx : EvalContext) (state : List StateDecl) (entry : Entrypoint)
    (items : List (Effect × Nat)) (types finalTypes : TypeEnv)
    (sourceEnv complete : EvalEnv) (current : LedgerState)
    (slots : List NativeState.Slot) (reads : List NativeState.Cell)
    (before plan : Impact.Plan) (offsets : List Nat) (chunks : List (List Impact.Op))
    (segments : List (Option Bool × List NativeState.Op)) (final : NativeState.Machine)
    (validated : GuardValidatedEffects state entry types items finalTypes)
    (compiled : GuardedEffectOperationChunks state entry.effectGuards items before plan offsets chunks)
    (evaluated : (items.zip chunks).mapM (fun (item, chunk) =>
      GuardedPlanExecution.evalChunk ctx complete (entry.effectGuardAt item.2) chunk) = .ok segments)
    (trace : GenericStateVM.RunsChunks (segments.map Prod.snd) ⟨[.vector slots], reads⟩ final)
    (scope : GuardedScalarReadEffects entry.effectGuards items)
    (operands : ∀ item ∈ items, ScalarOperands item.1)
    (candidates : ∀ item ∈ items, ReadCandidate item.1 complete)
    (inactive : ∀ item ∈ items, ∀ condition, entry.effectGuardAt item.2 = some condition →
      condition.eval ctx complete = .ok false → InactiveReadCandidate item.1 complete)
    (assertions : ∀ expression ∈ plan.guards, expression.eval ctx complete = .ok true)
    (agrees : AgreesOnTypes types sourceEnv complete)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus) (modulus : ctx.modulus = Field.modulus) :
    ∃ finalEnv finalState finalSlots finalReads,
      GuardedSourceEffects.fold ctx entry.effectGuards items (sourceEnv, current) = .ok (finalEnv, finalState) ∧
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
    cases validated with
    | cons validatedHead validGuard validatedTail =>
      simp only [List.zip_cons_cons, List.mapM_cons, bind_ok] at evaluated
      obtain ⟨⟨activity, head⟩, headEvaluation, remaining, tailEvaluation, joined⟩ := evaluated
      cases joined
      cases trace with
      | cons _ _ _ middle _ firstRun restRun =>
        have headScope := scope item (by simp)
        have tailScope : GuardedScalarReadEffects entry.effectGuards rest :=
          fun found member => scope found (by simp [member])
        have assertionShape := GuardedPlanAssertions.appendEffectWithActivity_guarded_assertion_chunk
          state item.1 (entry.effectGuardAt item.2) headScope before next step
        have headAssertions : ∀ expression ∈ GuardedPlanAssertions.guardedEffectAssertionChunk
            (entry.effectGuardAt item.2) item.1 before.reads.length,
            expression.eval ctx complete = .ok true := by
          intro expression member
          apply assertions expression (assertion_prefix tail tailScope expression ?_)
          rw [assertionShape]
          exact List.mem_append_right _ member
        obtain ⟨activation, segmentEvaluation⟩ := GuardedPlanExecution.evalChunk_success
          ctx complete (entry.effectGuardAt item.2) chunk activity head headEvaluation
        have exactSuffix : (if activity.getD true then
            (next.operations.drop before.operations.length).mapM
              (GenericStateOps.evalOp ctx complete) else .ok []) = .ok head := by
          rwa [operations, List.drop_left]
        obtain ⟨nextEnv, nextState, nextSlots, nextReads, firstStep, nextEncoded, middleShape, nextAgrees⟩ :=
          checked_step ctx state types _ item.1 (entry.effectGuardAt item.2) sourceEnv complete
            current slots reads before next head middle validatedHead headScope
            (operands item (by simp)) agrees (candidates item (by simp)) validGuard
            (inactive item (by simp)) headAssertions step activity activation exactSuffix
            firstRun encoded distinct stateBound modulus
        subst middle
        obtain ⟨finalEnv, finalState, finalSlots, finalReads, restFold, finalEncoded, finalShape, finalAgrees⟩ :=
          ih _ finalTypes nextEnv nextState nextSlots nextReads remaining final validatedTail
            tailEvaluation restRun tailScope (fun found member => operands found (by simp [member]))
            (fun found member => candidates found (by simp [member]))
            (fun found member => inactive found (by simp [member])) assertions nextAgrees nextEncoded
        refine ⟨finalEnv, finalState, finalSlots, finalReads, ?_, finalEncoded, finalShape, finalAgrees⟩
        rw [GuardedSourceEffects.fold_cons]
        change (runEffectsWithGuardsAndEnv ctx [item.1] [entry.effectGuardAt item.2]
          sourceEnv current >>= _) = _
        rw [firstStep]
        exact restFold

private theorem decoded_candidates (ctx : EvalContext) (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (base decoded : EvalEnv) (witness : Assignment)
    (lowered : Impact.lower state entry = .ok plan)
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
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
    (inactiveZero : ∀ item ∈ entry.effects.zipIdx, ∀ condition,
      entry.effectGuardAt item.2 = some condition →
      condition.eval ctx (base ++ decoded) = .ok false → match item.1 with
      | .readCell _ destination _ | .readMap _ destination _ _ _ =>
        witness ("%input_" ++ destination) = zero
      | _ => True) :
    ∀ item ∈ entry.effects.zipIdx, ReadCandidate item.1 (base ++ decoded) ∧
      (∀ condition, entry.effectGuardAt item.2 = some condition →
        condition.eval ctx (base ++ decoded) = .ok false →
        InactiveReadCandidate item.1 (base ++ decoded)) := by
  intro item present
  have member : item.1 ∈ entry.effects := by
    simpa only [List.zipIdx_map_fst] using List.mem_map_of_mem (f := Prod.fst) present
  have facts := readFacts item.1 member
  have skipped := inactiveZero item present
  rcases item with ⟨effect, index⟩
  cases effect <;> try exact ⟨True.intro, fun _ _ _ => True.intro⟩
  case readCell name destination ty =>
    obtain ⟨value, lookup, canonical, represented⟩ := GenericStateReadCandidates.readCell_candidate
      state entry plan base decoded witness name destination ty lowered scope member decodedReads
      distinctReads facts.1 facts.2.1 facts.2.2
    refine ⟨⟨value, lookup, canonical⟩, ?_⟩
    intro condition guard inactive
    obtain ⟨support, equal⟩ := candidate_is_default canonical
      (represented.trans (congrArg some (skipped condition guard inactive)))
    exact ⟨support, by simpa only [equal] using lookup⟩
  case readMap name destination keyTy ty key =>
    obtain ⟨value, lookup, canonical, represented⟩ := GenericStateReadCandidates.readMap_candidate
      state entry plan base decoded witness name destination keyTy ty key lowered scope member
      decodedReads distinctReads facts.1 facts.2.1 facts.2.2
    refine ⟨⟨value, lookup, canonical⟩, ?_⟩
    intro condition guard inactive
    obtain ⟨support, equal⟩ := candidate_is_default canonical
      (represented.trans (congrArg some (skipped condition guard inactive)))
    exact ⟨support, by simpa only [equal] using lookup⟩

/-- A checked run of an accepted scalar Impact plan preserves ordered guarded
source effects. Reads authenticate the decoded candidates against current state.
The caller supplies the assertion and inactive-lane checks from the relation. -/
theorem lower_checked_guarded_effects (ctx : EvalContext) (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (base decoded : EvalEnv)
    (witness : Assignment) (initial : LedgerState) (slots : List NativeState.Slot)
    (native : List NativeState.Op) (final : NativeState.Machine)
    (lowered : Impact.lower state entry = .ok plan)
    (admitted : ScalarStateEffects entry.effects)
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
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
    (inactiveZero : ∀ item ∈ entry.effects.zipIdx, ∀ condition,
      entry.effectGuardAt item.2 = some condition →
      condition.eval ctx (base ++ decoded) = .ok false → match item.1 with
      | .readCell _ destination _ | .readMap _ destination _ _ _ =>
        witness ("%input_" ++ destination) = zero
      | _ => True)
    (assertions : ∀ expression ∈ plan.guards, expression.eval ctx (base ++ decoded) = .ok true)
    (initialAgreement : AgreesOnTypes (initialEffectTypeEnv entry) base (base ++ decoded))
    (encoded : GenericStateEncoding.encodeState state initial = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus) (modulus : ctx.modulus = Field.modulus)
    (evaluated : GuardedPlanExecution.evalPlan ctx (base ++ decoded) plan = .ok native)
    (checked : NativeState.run native ⟨[.vector slots], []⟩ = some final) :
    ∃ finalTypes finalEnv finalState finalSlots finalReads,
      runEffectsWithGuardsAndEnv ctx entry.effects entry.effectGuards base initial =
        .ok (finalEnv, finalState) ∧
      GenericStateEncoding.encodeState state finalState = some finalSlots ∧
      final = ⟨[.vector finalSlots], finalReads⟩ ∧
      AgreesOnTypes finalTypes finalEnv (base ++ decoded) ∧
      GuardValidatedEffects state entry (initialEffectTypeEnv entry) entry.effects.zipIdx finalTypes ∧
      ∀ output ∈ entry.returns, output.value.validate stateEffectCaps finalTypes = .ok () := by
  obtain ⟨finalTypes, validated, returns⟩ :=
    lower_validated_guarded_effects_and_returns state entry plan lowered admitted
  obtain ⟨offsets, inputPlan, chunks, publicNative, groups, _, publicAccepted,
    compiled, publicEvaluated, effectEvaluated, sequence⟩ :=
    GuardedPlanTrace.lower_scoped_active_chunks state entry plan ctx (base ++ decoded)
      native lowered scope evaluated assertions
  obtain ⟨publicReads, _, publicRun⟩ := GenericStateAdmissionPrefix.public_prefix_run
    entry.circuit.inputs inputPlan ctx (base ++ decoded) publicNative [.vector slots] []
    publicAccepted publicCompatible publicEvaluated
  rw [sequence, NativeState.run_append, publicRun, Option.bind_some] at checked
  have trace := (GenericStateVM.run_chunks_iff (groups.map Prod.snd) _ final).mp checked
  have admittedOperand : ∀ item ∈ entry.effects.zipIdx, ScalarOperands item.1 := by
    intro item present
    apply operands
    simpa only [List.zipIdx_map_fst] using List.mem_map_of_mem (f := Prod.fst) present
  have facts := decoded_candidates ctx state entry plan base decoded witness lowered
    scope decodedReads distinctReads readFacts inactiveZero
  obtain ⟨finalEnv, finalState, finalSlots, finalReads, folded, finalEncoded, layout, agrees⟩ :=
    checked_effects_fold ctx state entry entry.effects.zipIdx (initialEffectTypeEnv entry)
      finalTypes base (base ++ decoded) initial slots publicReads inputPlan plan offsets chunks groups
      final validated compiled effectEvaluated trace scope admittedOperand
      (fun item member => (facts item member).1) (fun item member => (facts item member).2)
      assertions initialAgreement encoded distinct stateBound modulus
  refine ⟨finalTypes, finalEnv, finalState, finalSlots, finalReads, ?_, finalEncoded, layout,
    agrees, validated, returns⟩
  have guardLength := lower_guard_metadata_valid state entry plan lowered
  rw [GuardedSourceEffects.runEffectsWithGuardsAndEnv_eq_fold ctx entry.effects
    entry.effectGuards (base, initial) (by simpa using guardLength) scope]
  exact folded

end Noctium.Verification.GuardedStateEffectFold
