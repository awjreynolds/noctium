import Noctium.Verification.GenericStateEffectStep
import Noctium.Verification.GuardedEffectPrefix
import Noctium.Verification.GuardedScalarInput
import Noctium.Verification.GenericStateSchemaSpans
import Noctium.Verification.GenericStateCellAdmission

namespace Noctium.Verification.GuardedCellEffectStep

open Backend NativeRelation ScalarNormalization NativeState
open GenericStateEffectStep GenericStatePrefixEnvironment

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem appendEffectWithActivity_readCell_raw
    (state : List StateDecl) (name destination : String) (ty : Ty)
    (condition : Expr .bool) (before plan : Impact.Plan)
    (compiled : Impact.appendEffectWithActivity state
      (.readCell name destination ty) (some condition) before = .ok plan) :
    ∃ raw, Impact.appendEffect state (.readCell name destination ty) before = .ok raw := by
  unfold Impact.appendEffectWithActivity at compiled
  simp only [bind_ok] at compiled
  rcases compiled with ⟨rawEffect, effectAccepted, raw, appendAccepted, _⟩
  have sameEffect : rawEffect = Effect.readCell name destination ty := by
    change Except.ok (Effect.readCell name destination ty) = Except.ok rawEffect at effectAccepted
    exact (Except.ok.inj effectAccepted).symm
  subst rawEffect
  exact ⟨raw, appendAccepted⟩

private theorem appendEffect_readCell_empty_base
    (state : List StateDecl) (name destination : String) (ty : Ty)
    (before raw : Impact.Plan)
    (compiled : Impact.appendEffect state (.readCell name destination ty) before = .ok raw) :
    ∃ base, Impact.appendEffect state (.readCell name destination ty) {} = .ok base ∧
      raw.operations = before.operations ++ base.operations ∧
      raw.reads = before.reads ++ base.reads := by
  simp only [Impact.appendEffect, bind_ok] at compiled
  obtain ⟨slot, slotAccepted, value, valueAccepted, finished⟩ := compiled
  let base : Impact.Plan :=
    {raw with
      operations := raw.operations.drop before.operations.length
      activityGuards := []
      reads := raw.reads.drop before.reads.length
      guards := []}
  have rawShape := Except.ok.inj finished
  refine ⟨base, ?_, ?_, ?_⟩
  · simp only [Impact.appendEffect, bind_ok]
    refine ⟨slot, slotAccepted, value, valueAccepted, ?_⟩
    simp [base, ← rawShape, Pure.pure, Except.pure]
  · rw [← rawShape]
    simp [base, ← rawShape]
  · rw [← rawShape]
    simp [base, ← rawShape]

private theorem guarded_readCell_empty_chunk
    (state : List StateDecl) (name destination : String) (ty : Ty)
    (condition : Expr .bool) (before plan : Impact.Plan)
    (compiled : Impact.appendEffectWithActivity state
      (.readCell name destination ty) (some condition) before = .ok plan) :
    ∃ base, Impact.appendEffect state (.readCell name destination ty) {} = .ok base ∧
      plan.operations = before.operations ++ base.operations ∧
      plan.reads = before.reads ++
        base.reads.map (fun read => {read with guard := some condition}) := by
  obtain ⟨raw, rawAccepted⟩ := appendEffectWithActivity_readCell_raw
    state name destination ty condition before plan compiled
  obtain ⟨base, baseAccepted, _, _⟩ := appendEffect_readCell_empty_base
    state name destination ty before raw rawAccepted
  have suffix := GuardedEffectPrefix.appendEffectWithActivity_readCell_empty_chunk
    state name destination ty condition before plan base compiled baseAccepted
  exact ⟨base, baseAccepted, suffix.1, suffix.2⟩

private theorem declaration_name (state : List StateDecl) (name : String)
    (declaration : StateDecl) (found : state.find? (·.name == name) = some declaration) :
    declaration.name = name :=
  beq_iff_eq.mp (List.find?_some (p := fun item : StateDecl => item.name == name) found)

private def sourceScalarTypeOfCanonical {ty : Ty} {value : ty.Denote}
    (canonical : Canonical ty value) : ScalarType ty := by
  cases ty with
  | native => exact .native
  | bool => exact .bool
  | uint maximum => exact .uint maximum
  | bytes _ | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ =>
      simp [Canonical, sourceNumber?] at canonical

/-- A guarded scalar Cell read uses the real compiled suffix when active and
an empty native segment when inactive. The inactive relation binding must be
the same typed zero supplied by guarded read decoding. -/
theorem checked_guarded_readCell (ctx : EvalContext) (state : List StateDecl)
    (types nextTypes : TypeEnv) (sourceEnv complete : EvalEnv)
    (current : LedgerState) (slots : List NativeState.Slot)
    (reads : List NativeState.Cell) (name destination : String) (ty : Ty)
    (condition : Expr .bool) (active : Bool)
    (validated : GenericStateEffectValidation.EffectValidation state types
      (.readCell name destination ty) nextTypes)
    (agrees : AgreesOnTypes types sourceEnv complete)
    (readCandidate : ReadCandidate (.readCell name destination ty) complete)
    (guardValid : condition.validate GenericStateEffectValidation.stateEffectCaps types = .ok ())
    (guardEval : condition.eval ctx complete = .ok active)
    (inactiveBinding : active = false → ∃ support : ScalarType ty,
      complete.lookup destination = some
        (Value.pack ty (GenericStateInputValues.sourceValue support zero)))
    (before plan : Impact.Plan) (segment : List NativeState.Op)
    (after : NativeState.Machine)
    (compiled : Impact.appendEffectWithActivity state
      (.readCell name destination ty) (some condition) before = .ok plan)
    (evaluated : active = true →
      (plan.operations.drop before.operations.length).mapM
        (GenericStateOps.evalOp ctx complete) = .ok segment)
    (inactiveEmpty : active = false → segment = [])
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ nextEnv nextState nextSlots nextReads,
      runEffectsWithGuardsAndEnv ctx [.readCell name destination ty] [some condition]
        sourceEnv current = .ok (nextEnv, nextState) ∧
      GenericStateEncoding.encodeState state nextState = some nextSlots ∧
      after = ⟨[.vector nextSlots], nextReads⟩ ∧
      AgreesOnTypes nextTypes nextEnv complete ∧
      (if active then
        ∃ candidate, complete.lookup destination = some (Value.pack ty candidate) ∧
          Canonical ty candidate ∧ nextReads = reads ++ [NativeState.field
            (scalar (GenericStateEncoding.number ty candidate))]
       else nextReads = reads) := by
  cases validated with
  | readCell declared fresh =>
    obtain ⟨candidate, candidateLookup, canonical⟩ := readCandidate
    let support := sourceScalarTypeOfCanonical canonical
    obtain ⟨declaration, found, kind⟩ := declared
    obtain ⟨slot, located, declarationAt⟩ :=
      GenericStateSchemaSpans.find_declaration_slot state name declaration found
    have named := declaration_name state name declaration found
    have guardAgreement : condition.eval ctx sourceEnv = condition.eval ctx complete :=
      GenericStatePrefixEnvironment.eval_scoped types sourceEnv complete agrees ctx
        GenericStateEffectValidation.stateEffectCaps condition guardValid
    obtain ⟨base, baseCompiled, operationsSuffix, _⟩ :=
      guarded_readCell_empty_chunk state name destination ty condition before plan compiled
    cases active with
    | false =>
      obtain ⟨inactiveSupport, inactiveLookup⟩ := inactiveBinding rfl
      have sourceInactive : condition.eval ctx sourceEnv = .ok false := by
        rw [guardAgreement, guardEval]
      have emptySegment := inactiveEmpty rfl
      rw [emptySegment] at checked
      have checkedNil : (some ⟨[.vector slots], reads⟩ : Option NativeState.Machine) =
          some after := by
        simpa [NativeState.run] using checked
      have afterUnchanged : after = ⟨[.vector slots], reads⟩ :=
        (Option.some.inj checkedNil).symm
      have sourceStep := GuardedScalarInput.run_inactive_scalarCell_read
        ctx sourceEnv current name destination inactiveSupport condition sourceInactive
      have agreement := GenericStatePrefixEnvironment.extend_read types sourceEnv complete
        destination ty (Value.pack ty (GenericStateInputValues.sourceValue inactiveSupport zero))
        agrees fresh inactiveLookup
      exact ⟨(destination, Value.pack ty
          (GenericStateInputValues.sourceValue inactiveSupport zero)) :: sourceEnv,
        current, slots, reads, sourceStep, encoded, afterUnchanged, agreement, rfl⟩
    | true =>
      have sourceActive : condition.eval ctx sourceEnv = .ok true := by
        rw [guardAgreement, guardEval]
      have baseEvaluation : base.operations.mapM
          (GenericStateOps.evalOp ctx complete) = .ok segment := by
        have suffixIdentity : plan.operations.drop before.operations.length = base.operations := by
          rw [operationsSuffix]
          simp
        rw [← suffixIdentity]
        exact evaluated rfl
      obtain ⟨sourceStep, nativeStep⟩ :=
        GenericStateReadAuthentication.readCell_candidate_source_step ctx
          sourceEnv complete state current slots name destination ty base segment slot
          candidate reads after baseCompiled located declaration declarationAt named kind
          encoded candidateLookup canonical modulus baseEvaluation checked
      have guardedSource := GuardedScalarInput.run_active_scalarCell_read
        ctx sourceEnv current name destination support condition sourceActive
      rw [guardedSource]
      have agreement := GenericStatePrefixEnvironment.extend_read types sourceEnv complete
        destination ty (Value.pack ty candidate) agrees fresh candidateLookup
      exact ⟨(destination, Value.pack ty candidate) :: sourceEnv, current, slots,
        reads ++ [NativeState.field (scalar (GenericStateEncoding.number ty candidate))],
        sourceStep, encoded, nativeStep, agreement,
        ⟨candidate, candidateLookup, canonical, rfl⟩⟩

end Noctium.Verification.GuardedCellEffectStep
