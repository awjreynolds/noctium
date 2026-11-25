import Noctium.Verification.GenericStateOps
import Noctium.Verification.GenericStateSchemaSpans

namespace Noctium.Verification.GenericStateAbsenceAuthentication
open Backend NativeRelation ScalarNormalization NativeState

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

theorem absence_guard_candidate_false (ctx : EvalContext)
    (env : EvalEnv) (name : String) (value : Bool)
    (lookup : env.lookup name = some (Value.bool value))
    (guard : (Expr.eq (.ref name : Expr .bool) (.bool false)).eval ctx env =
      .ok true) : value = false := by
  cases value with
  | false => rfl
  | true =>
    simp only [Expr.eval, lookup] at guard
    change (Except.ok false : Except String Bool) = .ok true at guard
    cases guard

/-- The actual absence operation segment uses the same slot as Impact's
source-name lookup, with no independent slot-agreement premise. -/
theorem requireAbsent_candidate_eval (state : List StateDecl)
    (name : String) (keyTy : Ty) (keyExpr : Expr keyTy)
    (base : Impact.Plan) (ctx : EvalContext) (env : EvalEnv)
    (key : keyTy.Denote)
    (compiled : Impact.appendEffect state
      (.requireAbsent name keyTy keyExpr) {} = .ok base)
    (modulus : ctx.modulus = Field.modulus)
    (keyEval : keyExpr.eval ctx env = .ok key)
    (canonical : Canonical keyTy key) :
    ∃ slot, state.findIdx? (·.name == name) = some slot ∧
      base.operations.mapM (GenericStateOps.evalOp ctx env) =
        .ok (GenericStateVM.requireAbsentOps slot
          (scalar (GenericStateEncoding.number keyTy key))) := by
  simp only [Impact.appendEffect, bind_ok] at compiled
  obtain ⟨slot, found, aligned, alignment, result⟩ := compiled
  have located : state.findIdx? (·.name == name) = some slot := by
    change (match state.findIdx? (·.name == name) with
      | some index => (pure index : Except String Nat)
      | none => throw s!"unknown ledger state '{name}'") = .ok slot at found
    cases index : state.findIdx? (·.name == name) with
    | none => simp [index] at found
    | some actual =>
      simp [index] at found
      cases found
      rfl
  have keyField : ∃ nativeKey : Expr .native,
      aligned = .field nativeKey ∧
      nativeKey.eval ctx env = .ok (GenericStateEncoding.number keyTy key) := by
    cases keyTy with
    | native =>
      exact ⟨keyExpr, (Except.ok.inj alignment).symm, keyEval⟩
    | bool =>
      refine ⟨.select keyExpr (.native 1) (.native 0),
        (Except.ok.inj alignment).symm, ?_⟩
      cases key <;>
        simp [Expr.eval, keyEval, modulus, Field.modulus, GenericStateEncoding.number,
          bind, Except.bind, pure, Except.pure]
    | uint maximum =>
      refine ⟨.cast .native keyExpr, (Except.ok.inj alignment).symm, ?_⟩
      have bound : key < Field.modulus := canonical.1
      rw [eval_cast_scalar ctx env keyExpr (.uint maximum) .native key keyEval]
      simp [scalarCast, modulus, number, GenericStateEncoding.number, bound]
    | bytes _ | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ =>
      simp [Canonical, sourceNumber?] at canonical
  obtain ⟨nativeKey, rfl, keyNative⟩ := keyField
  have equal := Except.ok.inj result
  subst base
  refine ⟨slot, located, ?_⟩
  change [Impact.Op.dup, .index slot, .push (.field nativeKey) false, .member,
    .popeq (.bit false)].mapM (GenericStateOps.evalOp ctx env) = _
  simp [GenericStateVM.requireAbsentOps, GenericStateOps.evalOp, GenericStateOps.evalAligned,
    keyNative, List.mapM_cons, bind, Except.bind, pure, Except.pure]

/-- The checked production absence segment enforces the original source
absence transition on the current encoded map slot. -/
theorem requireAbsent_candidate_source_step (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name : String) (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (key : keyTy.Denote) (base : Impact.Plan)
    (segment : List NativeState.Op) (reads : List NativeState.Cell)
    (after : NativeState.Machine)
    (compiled : Impact.appendEffect state
      (.requireAbsent name keyTy keyExpr) {} = .ok base)
    (declaration : StateDecl)
    (sourceFound : state.find? (·.name == name) = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .map keyTy valueTy)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (modulus : ctx.modulus = Field.modulus)
    (candidateEval : keyExpr.eval ctx candidateEnv = .ok key)
    (sourceEval : keyExpr.eval ctx sourceEnv = .ok key)
    (canonical : Canonical keyTy key)
    (evaluated : base.operations.mapM (GenericStateOps.evalOp ctx candidateEnv) =
      .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after) :
    SourceEffects.step ctx (.requireAbsent name keyTy keyExpr)
      (sourceEnv, current) = .ok (sourceEnv, current) ∧
    after = ⟨[.vector slots], reads ++ [NativeState.boolean false]⟩ := by
  obtain ⟨slot, found, actualEval⟩ := requireAbsent_candidate_eval
    state name keyTy keyExpr base ctx candidateEnv key compiled
    modulus candidateEval canonical
  have declarationAt : state[slot]? = some declaration := by
    rw [List.find?_eq_bind_findIdx?_getElem?, found] at sourceFound
    exact sourceFound
  rw [actualEval] at evaluated
  cases evaluated
  exact GenericStateSchemaSpans.requireAbsent_source_step ctx sourceEnv state current
    slots slot declaration name keyTy valueTy keyExpr key reads after
    declarationAt named kind encoded sourceEval canonical checked

end Noctium.Verification.GenericStateAbsenceAuthentication
