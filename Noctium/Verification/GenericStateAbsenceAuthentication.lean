import Noctium.Verification.GenericStateWriteEvaluation
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

/-- The production absence chunk pushes the selected scalar key at the exact
Impact slot, then checks and records false membership. -/
theorem requireAbsent_scalar_chunk (state : List StateDecl)
    (name : String) (keyTy : Ty) (keyExpr : Expr keyTy) (base : Impact.Plan)
    (support : ScalarType keyTy)
    (compiled : Impact.appendEffect state (.requireAbsent name keyTy keyExpr) {} = .ok base) :
    ∃ slot, state.findIdx? (·.name == name) = some slot ∧
      base.operations = [.dup, .index slot,
        .push (.field (GenericStateWriteEvaluation.scalarProjection support keyExpr)) false,
        .member, .popeq (.bit false)] := by
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
  have alignedKey : aligned = .field (GenericStateWriteEvaluation.scalarProjection support keyExpr) := by
    cases support <;> exact (Except.ok.inj alignment).symm
  subst aligned
  cases result
  exact ⟨slot, located, rfl⟩

/-- A canonical key evaluates to exactly the field value checked by the
production absence chunk at the selected slot. -/
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
  obtain ⟨support⟩ := GenericStateWriteEvaluation.scalarType_of_canonical canonical
  obtain ⟨slot, located, operations⟩ :=
    requireAbsent_scalar_chunk state name keyTy keyExpr base support compiled
  have keyNative := GenericStateWriteEvaluation.scalarProjection_eval
    support ctx env keyExpr key modulus keyEval canonical
  refine ⟨slot, located, ?_⟩
  rw [operations]
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
