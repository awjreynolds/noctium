import Noctium.Verification.GenericStateEffectValidation
import Noctium.Verification.GenericStatePrefixEnvironment
import Noctium.Verification.GenericStateReadAuthentication
import Noctium.Verification.GenericStateWriteAuthentication
import Noctium.Verification.GenericStateMapReadAuthentication
import Noctium.Verification.GenericStateOrderedAbsence

namespace Noctium.Verification.GenericStateEffectStep
open Backend NativeRelation ScalarNormalization NativeState
open GenericStatePrefixEnvironment

/-- The current expression-to-native proofs supply a separate scalar scope
for every operand evaluated by the source effect. -/
def ScalarOperands : Effect → Prop
  | .readCell .. => True
  | .readMap _ _ _ _ key => ScalarExpression key
  | .require condition => ScalarExpression condition
  | .writeCell _ _ value => ScalarExpression value
  | .writeMap _ _ _ key value => ScalarExpression key ∧ ScalarExpression value
  | .requireAbsent _ _ key => ScalarExpression key
  | _ => False

/-- A typed candidate comes from the decoded relation environment. The
native step still has to authenticate it against the current state. -/
def ReadCandidate (effect : Effect) (complete : EvalEnv) : Prop :=
  match effect with
  | .readCell _ destination ty | .readMap _ destination _ ty _ =>
    ∃ value : ty.Denote,
      complete.lookup destination = some (Value.pack ty value) ∧ Canonical ty value
  | _ => True

def GuardTrue (ctx : EvalContext) (effect : Effect) (complete : EvalEnv) : Prop :=
  match effect with
  | .require condition => condition.eval ctx complete = .ok true
  | _ => True

private theorem declaration_name (state : List StateDecl) (name : String)
    (declaration : StateDecl) (found : state.find? (·.name == name) = some declaration) :
    declaration.name = name :=
  beq_iff_eq.mp (List.find?_some (p := fun item : StateDecl => item.name == name) found)

/-- An accepted unguarded scalar effect and its checked native operation suffix
agree on the next frame, state encoding and read tape. On a typed fresh read,
the authenticated binding extends source-prefix agreement. -/
theorem checked_effect_step (ctx : EvalContext) (state : List StateDecl)
    (types nextTypes : TypeEnv) (effect : Effect)
    (sourceEnv complete : EvalEnv) (current : LedgerState)
    (slots : List NativeState.Slot) (reads : List NativeState.Cell)
    (before plan : Impact.Plan) (segment : List NativeState.Op)
    (after : NativeState.Machine)
    (validated : GenericStateEffectValidation.EffectValidation state types effect nextTypes)
    (operands : ScalarOperands effect)
    (agrees : AgreesOnTypes types sourceEnv complete)
    (readCandidate : ReadCandidate effect complete)
    (guardTrue : GuardTrue ctx effect complete)
    (compiled : Impact.appendEffectWithActivity state effect none before = .ok plan)
    (evaluated : (plan.operations.drop before.operations.length).mapM
      (GenericStateOps.evalOp ctx complete) = .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus) (modulus : ctx.modulus = Field.modulus) :
    ∃ nextEnv nextState nextSlots nextReads,
      SourceEffects.step ctx effect (sourceEnv, current) = .ok (nextEnv, nextState) ∧
      GenericStateEncoding.encodeState state nextState = some nextSlots ∧
      after = ⟨[.vector nextSlots], nextReads⟩ ∧
      AgreesOnTypes nextTypes nextEnv complete := by
  cases validated with
  | @readCell stateName destination ty declared fresh =>
    obtain ⟨declaration, found, kind⟩ := declared
    obtain ⟨candidate, lookup, canonical⟩ := readCandidate
    obtain ⟨slot, located, declarationAt⟩ :=
      GenericStateSchemaSpans.find_declaration_slot state stateName declaration found
    obtain ⟨base, emptyAccepted, operations⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_unguarded_readCell_chunk
        state stateName destination ty before plan compiled
    rw [operations, List.drop_left] at evaluated
    obtain ⟨sourceStep, final⟩ :=
      GenericStateReadAuthentication.readCell_candidate_source_step ctx
        sourceEnv complete state current slots stateName destination ty base segment slot
        candidate reads after emptyAccepted located declaration declarationAt
        (declaration_name state stateName declaration found) kind encoded lookup canonical
        modulus evaluated checked
    exact ⟨_, current, slots, _, sourceStep, encoded, final,
      extend_read types sourceEnv complete destination ty _ agrees fresh lookup⟩
  | @readMap stateName destination keyTy valueTy key declared keyValid fresh =>
    obtain ⟨declaration, found, kind⟩ := declared
    obtain ⟨candidate, lookup, canonical⟩ := readCandidate
    have keyAgreement := eval_scoped types sourceEnv complete agrees ctx
      GenericStateEffectValidation.stateEffectCaps key keyValid
    obtain ⟨sourceStep, final⟩ := GenericStateMapReadAuthentication.readMap_candidate_source_step
      ctx sourceEnv complete state current slots stateName destination keyTy valueTy key
      operands keyAgreement candidate before plan segment reads after compiled declaration
      found kind encoded lookup canonical modulus evaluated checked
    exact ⟨_, current, slots, _, sourceStep, encoded, final,
      extend_read types sourceEnv complete destination valueTy _ agrees fresh lookup⟩
  | @require condition conditionValid =>
    have truth : condition.eval ctx sourceEnv = .ok true :=
      (eval_scoped types sourceEnv complete agrees ctx
        GenericStateEffectValidation.stateEffectCaps condition conditionValid).trans guardTrue
    obtain ⟨raw, appended, operations, _⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_none_result state (.require condition) before plan compiled
    simp only [Impact.appendEffect] at appended
    cases appended
    rw [operations, List.drop_length] at evaluated
    cases evaluated
    cases checked
    exact ⟨sourceEnv, current, slots, reads, GenericStateVM.require_source_step ctx sourceEnv current
      condition truth, encoded, rfl, agrees⟩
  | @writeCell stateName ty value declared valueValid =>
    obtain ⟨declaration, found, kind⟩ := declared
    have agreement := eval_scoped types sourceEnv complete agrees ctx
      GenericStateEffectValidation.stateEffectCaps value valueValid
    obtain ⟨next, nextSlots, sourceStep, nextEncoded, final⟩ :=
      GenericStateWriteAuthentication.writeCell_candidate_source_step ctx sourceEnv complete
        state current slots stateName ty value operands agreement before plan segment reads
        after compiled declaration found (declaration_name state stateName declaration found)
        kind distinct encoded stateBound modulus evaluated checked
    exact ⟨sourceEnv, next, nextSlots, reads, sourceStep, nextEncoded, final, agrees⟩
  | @writeMap stateName keyTy valueTy key value declared keyValid valueValid =>
    obtain ⟨declaration, found, kind⟩ := declared
    have keyAgreement := eval_scoped types sourceEnv complete agrees ctx
      GenericStateEffectValidation.stateEffectCaps key keyValid
    have valueAgreement := eval_scoped types sourceEnv complete agrees ctx
      GenericStateEffectValidation.stateEffectCaps value valueValid
    obtain ⟨next, nextSlots, sourceStep, nextEncoded, final⟩ :=
      GenericStateWriteAuthentication.writeMap_candidate_source_step ctx sourceEnv complete
        state current slots stateName keyTy valueTy key value operands.1 operands.2
        keyAgreement valueAgreement before plan segment reads after compiled declaration found
        (declaration_name state stateName declaration found) kind distinct encoded stateBound
        modulus evaluated checked
    exact ⟨sourceEnv, next, nextSlots, reads, sourceStep, nextEncoded, final, agrees⟩
  | @requireAbsent stateName keyTy key valueTy declared keyValid =>
    obtain ⟨declaration, found, kind⟩ := declared
    have keyAgreement := eval_scoped types sourceEnv complete agrees ctx
      GenericStateEffectValidation.stateEffectCaps key keyValid
    obtain ⟨sourceStep, final, _, _⟩ := GenericStateOrderedAbsence.requireAbsent_checked_suffix
      ctx sourceEnv complete state current slots stateName keyTy valueTy key operands keyAgreement
      before plan segment reads after compiled declaration found
      (declaration_name state stateName declaration found) kind encoded modulus evaluated checked
    exact ⟨sourceEnv, current, slots, _, sourceStep, encoded, final, agrees⟩

end Noctium.Verification.GenericStateEffectStep
