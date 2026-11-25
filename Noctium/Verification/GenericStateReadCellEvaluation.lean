import Noctium.Verification.GenericStateCellAdmission
import Noctium.Verification.GenericStateEncoding
import Noctium.Verification.GenericStateVM

namespace Noctium.Verification.GenericStateReadCellEvaluation
open Backend GenericStateCellAdmission GenericStateEncoding NativeRelation
  NativeState ScalarNormalization

def scalarCellTypeOfCanonical {ty : Ty} {value : ty.Denote}
    (canonical : Canonical ty value) : ScalarCellType ty := by
  cases ty with
  | native => exact .native
  | bool => exact .bool
  | uint maximum => exact .uint maximum canonical.2.1
  | bytes _ | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ =>
    simp [Canonical, ScalarNormalization.sourceNumber?] at canonical

/-- Proof-facing spelling of the exact private nativeRead implementation.
Only checked scalar cell types have a native field projection. -/
def readExpression {ty : Ty} (scalar : ScalarCellType ty)
    (name : String) : Expr .native :=
  match scalar with
  | .native => .ref name
  | .bool => .cast .native (.ref name : Expr .bool)
  | .uint maximum _ => .cast .native (.ref name : Expr (.uint maximum))

theorem canonical_ref_eval (ctx : EvalContext) (env : EvalEnv)
    (name : String) (ty : Ty) (value : ty.Denote)
    (lookup : env.lookup name = some (Value.pack ty value))
    (modulus : ctx.modulus = Field.modulus) (canonical : Canonical ty value) :
    (Expr.ref name : Expr ty).eval ctx env = .ok value := by
  simp only [Expr.eval, lookup]
  rw [ScalarNormalization.number_pack_as ty value canonical]
  cases ty with
  | native =>
    have bound : value < ctx.modulus := by
      simpa [modulus, GenericStateEncoding.number] using canonical.1
    simp [canonical_eq, bound]
    rfl
  | bool => rfl
  | uint maximum =>
    have bound : value < ctx.modulus := by
      simpa [modulus, GenericStateEncoding.number] using canonical.1
    simp [canonical_eq, bound, canonical.2.1, canonical.2.2]
    rfl
  | bytes length => simp [Canonical, sourceNumber?] at canonical
  | opaqueBytes => simp [Canonical, sourceNumber?] at canonical
  | opaqueString => simp [Canonical, sourceNumber?] at canonical
  | jubjubScalar => simp [Canonical, sourceNumber?] at canonical
  | jubjubPoint => simp [Canonical, sourceNumber?] at canonical
  | foreign kind => simp [Canonical, sourceNumber?] at canonical

/-- Native, Boolean and bounded integer read candidates retain their canonical
field representation through the actual cast used by Impact. -/
theorem readExpression_eval (ctx : EvalContext) (env : EvalEnv)
    (name : String) (ty : Ty) (value : ty.Denote) (scalar : ScalarCellType ty)
    (lookup : env.lookup name = some (Value.pack ty value))
    (modulus : ctx.modulus = Field.modulus) (canonical : Canonical ty value) :
    (readExpression scalar name).eval ctx env = .ok (GenericStateEncoding.number ty value) := by
  have reference := canonical_ref_eval ctx env name ty value lookup modulus canonical
  cases scalar with
  | native => exact reference
  | bool =>
    simp only [readExpression]
    rw [Expr.eval, reference]
    simp only [bind, Except.bind]
    change (if (if value then 1 else 0) < ctx.modulus
      then Except.ok (if value then 1 else 0)
      else Except.error "noncanonical scalar conversion") =
      Except.ok (if value then 1 else 0)
    cases value <;> simp [modulus, Field.modulus]
  | uint maximum =>
    simp only [readExpression]
    rw [Expr.eval, reference]
    have bound : value < ctx.modulus := by
      simpa [modulus, GenericStateEncoding.number] using canonical.1
    change (if value < ctx.modulus then Except.ok value
      else Except.error "noncanonical scalar conversion") = Except.ok value
    simp [bound]

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem readCell_ops_eval_of_field (ctx : EvalContext) (env : EvalEnv)
    (slot : Nat) (expression : Expr .native) (value : Nat)
    (evaluated : expression.eval ctx env = .ok value) :
    [Impact.Op.dup, .index slot, .popeq (.field expression)].mapM
      (GenericStateOps.evalOp ctx env) =
      .ok (GenericStateVM.readCellOps slot
        (NativeState.field (NativeRelation.scalar value))) := by
  simp [GenericStateVM.readCellOps, GenericStateOps.evalOp,
    GenericStateOps.evalAligned, evaluated, Except.map, Functor.map] <;> rfl

/-- The actual emitted read-cell chunk compares against the canonical typed
candidate at its real declared slot. No source transition success is assumed. -/
theorem readCell_candidate_eval (state : List StateDecl)
    (name destination : String) (ty : Ty) (base : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv) (value : ty.Denote)
    (scalar : ScalarCellType ty)
    (declaration : ScalarCellDeclaration state name ty)
    (accepted : Impact.appendEffect state (.readCell name destination ty) {} = .ok base)
    (lookup : env.lookup destination = some (Value.pack ty value))
    (modulus : ctx.modulus = Field.modulus) (canonical : Canonical ty value) :
    ∃ slot, state.findIdx? (·.name == name) = some slot ∧
      base.operations.mapM (GenericStateOps.evalOp ctx env) =
        .ok (GenericStateVM.readCellOps slot
          (NativeState.field (NativeRelation.scalar (GenericStateEncoding.number ty value)))) := by
  obtain ⟨supportedSlot, operationsShape, _⟩ :=
    GenericStateCellAdmission.append_read_cell_scalar_supported state {} base
      name destination ty scalar declaration accepted (by simp)
  simp only [Impact.appendEffect, bind_ok] at accepted
  obtain ⟨slot, found, readValue, _, resultAccepted⟩ := accepted
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
  refine ⟨slot, located, ?_⟩
  have actualShape : base.operations =
      [] ++ [.dup, .index slot, readValue] := by
    exact (congrArg Impact.Plan.operations (Except.ok.inj resultAccepted)).symm
  have sameShape := actualShape.symm.trans operationsShape
  simp only [List.nil_append] at sameShape
  have tail := (List.cons.inj sameShape).2
  have indexEq := (List.cons.inj tail).1
  have slotEq : supportedSlot = slot := by
    cases indexEq
    rfl
  subst supportedSlot
  have evaluated := readExpression_eval ctx env destination ty value scalar
    lookup modulus canonical
  rw [operationsShape]
  cases scalar with
  | native =>
    change [.dup, .index slot,
      .popeq (.field (.ref destination))].mapM (GenericStateOps.evalOp ctx env) = _
    have evalRead : (Expr.ref destination : Expr .native).eval ctx env =
        .ok (GenericStateEncoding.number .native value) := by
      simpa [readExpression] using evaluated
    exact readCell_ops_eval_of_field ctx env slot (.ref destination)
      (GenericStateEncoding.number .native value) evalRead
  | bool =>
    change [.dup, .index slot,
      .popeq (.field (.cast .native (.ref destination : Expr .bool)))].mapM
        (GenericStateOps.evalOp ctx env) = _
    have evalRead : (Expr.cast .native (.ref destination : Expr .bool)).eval ctx env =
        .ok (GenericStateEncoding.number .bool value) := by
      simpa [readExpression] using evaluated
    exact readCell_ops_eval_of_field ctx env slot
      (.cast .native (.ref destination : Expr .bool))
      (GenericStateEncoding.number .bool value) evalRead
  | uint maximum valid =>
    change [.dup, .index slot,
      .popeq (.field (.cast .native (.ref destination : Expr (.uint maximum))))].mapM
        (GenericStateOps.evalOp ctx env) = _
    have evalRead : (Expr.cast .native (.ref destination : Expr (.uint maximum))).eval ctx env =
        .ok (GenericStateEncoding.number (.uint maximum) value) := by
      simpa [readExpression] using evaluated
    exact readCell_ops_eval_of_field ctx env slot
      (.cast .native (.ref destination : Expr (.uint maximum)))
      (GenericStateEncoding.number (.uint maximum) value) evalRead

end Noctium.Verification.GenericStateReadCellEvaluation
