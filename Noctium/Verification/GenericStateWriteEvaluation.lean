import Noctium.Verification.GenericStateOps
import Noctium.Verification.GenericStateVM
import Noctium.Verification.GenericStateEncoding
import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.GenericStateWriteEvaluation
open Backend ScalarNormalization

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem stateSlot_found (state : List StateDecl) (name : String)
    (slot : Nat)
    (accepted : (match state.findIdx? (·.name == name) with
      | some index => (pure index : Except String Nat)
      | none => throw s!"unknown ledger state '{name}'") = .ok slot) :
    state.findIdx? (·.name == name) = some slot := by
  cases located : state.findIdx? (·.name == name) with
  | none => simp [located] at accepted
  | some actual =>
    have same : actual = slot := by simpa [located, pure, Except.pure] using accepted
    simp [same]

/-- Canonicality implies support for the scalar fragment. -/
theorem scalarType_of_canonical {ty : Ty} {value : ty.Denote}
    (canonical : Canonical ty value) : Nonempty (ScalarType ty) := by
  cases ty with
  | native => exact ⟨.native⟩
  | bool => exact ⟨.bool⟩
  | uint maximum => exact ⟨.uint maximum⟩
  | bytes length => simp [Canonical, sourceNumber?] at canonical
  | opaqueBytes => simp [Canonical, sourceNumber?] at canonical
  | opaqueString => simp [Canonical, sourceNumber?] at canonical
  | jubjubScalar => simp [Canonical, sourceNumber?] at canonical
  | jubjubPoint => simp [Canonical, sourceNumber?] at canonical
  | foreign kind => simp [Canonical, sourceNumber?] at canonical

/-- The native projection emitted by a scalar cell or map write. -/
def scalarProjection {ty : Ty} (support : ScalarType ty)
    (expression : Expr ty) : Expr .native :=
  match support with
  | .native => expression
  | .bool => .select expression (.native 1) (.native 0)
  | .uint _ => .cast .native expression

/-- The production projection evaluates to the source value's exact scalar
encoding. -/
theorem scalarProjection_eval {ty : Ty} (support : ScalarType ty)
    (ctx : EvalContext) (env : EvalEnv) (expression : Expr ty)
    (value : ty.Denote) (modulus : ctx.modulus = Field.modulus)
    (evaluated : expression.eval ctx env = .ok value)
    (canonical : Canonical ty value) :
    (scalarProjection support expression).eval ctx env =
      .ok (GenericStateEncoding.number ty value) := by
  cases support with
  | native => exact evaluated
  | bool =>
    cases value <;>
      simp [scalarProjection, Expr.eval, evaluated, modulus, Field.modulus,
        GenericStateEncoding.number, bind, Except.bind] <;> rfl
  | uint maximum =>
    have castEval := ScalarNormalization.eval_cast_scalar ctx env expression
      (.uint maximum) .native value evaluated
    have bound : value < ctx.modulus := by
      rw [modulus]
      exact canonical.1
    simpa [scalarProjection, ScalarNormalization.scalarCast,
      ScalarNormalization.number, GenericStateEncoding.number, bound] using castEval

/-- Empty-plan scalar cell writes retain the production slot and exact push
sequence. The declaration witness excludes the special u128 storage alignment. -/
theorem writeCell_scalar_chunk (state : List StateDecl) (name : String)
    (ty : Ty) (expression : Expr ty) (base : Impact.Plan)
    (support : ScalarType ty)
    (declaration : Impact.UnalignedCellDeclaration state name ty)
    (accepted : Impact.appendEffect state (.writeCell name ty expression) {} = .ok base) :
    ∃ slot, state.findIdx? (·.name == name) = some slot ∧
      base.operations = [.push (.field (.native slot)),
        .push (.field (scalarProjection support expression)) true, .insert 1] := by
  cases support with
  | native =>
    simp only [Impact.appendEffect, bind_ok] at accepted
    rcases accepted with ⟨slot, slotAccepted, stored, storedAccepted, resultAccepted⟩
    have located : state.findIdx? (·.name == name) = some slot := by
      apply stateSlot_found state name slot
      change (match state.findIdx? (·.name == name) with
        | some index => (pure index : Except String Nat)
        | none => throw s!"unknown ledger state '{name}'") = .ok slot at slotAccepted
      exact slotAccepted
    have storedShape : stored = .push (.field expression) true := by
      change (Except.ok (.push (.field expression) true) : Except String Impact.Op) =
        .ok stored at storedAccepted
      exact (Except.ok.inj storedAccepted).symm
    cases resultAccepted
    exact ⟨slot, located, by simp [storedShape, scalarProjection]⟩
  | bool =>
    simp only [Impact.appendEffect, bind_ok] at accepted
    rcases accepted with ⟨slot, slotAccepted, stored, storedAccepted, resultAccepted⟩
    have located : state.findIdx? (·.name == name) = some slot := by
      apply stateSlot_found state name slot
      change (match state.findIdx? (·.name == name) with
        | some index => (pure index : Except String Nat)
        | none => throw s!"unknown ledger state '{name}'") = .ok slot at slotAccepted
      exact slotAccepted
    have storedShape : stored = .push
        (.field (.select expression (.native 1) (.native 0))) true := by
      change (Except.ok (.push
        (.field (.select expression (.native 1) (.native 0))) true) :
        Except String Impact.Op) = .ok stored at storedAccepted
      exact (Except.ok.inj storedAccepted).symm
    cases resultAccepted
    exact ⟨slot, located, by simp [storedShape, scalarProjection]⟩
  | uint maximum =>
    have acceptedOriginal := accepted
    simp only [Impact.appendEffect, bind_ok] at accepted
    rcases accepted with ⟨slot, slotAccepted, stored, storedAccepted, resultAccepted⟩
    have located : state.findIdx? (·.name == name) = some slot := by
      apply stateSlot_found state name slot
      change (match state.findIdx? (·.name == name) with
        | some index => (pure index : Except String Nat)
        | none => throw s!"unknown ledger state '{name}'") = .ok slot at slotAccepted
      exact slotAccepted
    have planEq :
        ({ operations := [] ++
          [.push (.field (.native slot)), stored, .insert 1] } : Impact.Plan) = base := by
      change (Except.ok ({ operations := [] ++
        [.push (.field (.native slot)), stored, .insert 1] } : Impact.Plan)) =
          .ok base at resultAccepted
      exact Except.ok.inj resultAccepted
    have baseShape : base.operations =
        [.push (.field (.native slot)), stored, .insert 1] := by
      have fields := congrArg Impact.Plan.operations planEq
      simpa using fields.symm
    obtain ⟨shapeSlot, shape⟩ :=
      Impact.appendEffect_unalignedUIntCell_write_shape state name maximum
        expression declaration {} base acceptedOriginal
    have shapeExact : base.operations =
        [.push (.field (.native shapeSlot)),
          .push (.field (scalarProjection (.uint maximum) expression)) true,
          .insert 1] := by
      simpa [scalarProjection] using shape
    have sameSlot : slot = shapeSlot := by
      have operations := baseShape.symm.trans shapeExact
      have first := (List.cons.inj operations).1
      exact Expr.native.inj
        (Impact.Aligned.field.inj (Impact.Op.push.inj first).1)
    exact ⟨shapeSlot, by simpa [sameSlot] using located, shapeExact⟩

/-- Empty-plan scalar map writes retain the selected slot and production
index/key/value/insert order. -/
theorem writeMap_scalar_chunk (state : List StateDecl) (name : String)
    (keyTy valueTy : Ty) (keyExpr : Expr keyTy) (valueExpr : Expr valueTy)
    (base : Impact.Plan) (keySupport : ScalarType keyTy)
    (valueSupport : ScalarType valueTy)
    (accepted : Impact.appendEffect state
      (.writeMap name keyTy valueTy keyExpr valueExpr) {} = .ok base) :
    ∃ slot, state.findIdx? (·.name == name) = some slot ∧
      base.operations = [.index slot true,
        .push (.field (scalarProjection keySupport keyExpr)) false,
        .push (.field (scalarProjection valueSupport valueExpr)) true,
        .insert 2] := by
  simp only [Impact.appendEffect, bind_ok] at accepted
  rcases accepted with
    ⟨slot, slotAccepted, alignedKey, keyAccepted, stored, storedAccepted, resultAccepted⟩
  have located : state.findIdx? (·.name == name) = some slot := by
    apply stateSlot_found state name slot
    change (match state.findIdx? (·.name == name) with
      | some index => (pure index : Except String Nat)
      | none => throw s!"unknown ledger state '{name}'") = .ok slot at slotAccepted
    exact slotAccepted
  have keyShape : alignedKey = .field (scalarProjection keySupport keyExpr) := by
    cases keySupport with
    | native =>
      change (Except.ok (.field keyExpr) : Except String Impact.Aligned) =
        .ok alignedKey at keyAccepted
      exact (Except.ok.inj keyAccepted).symm
    | bool =>
      change (Except.ok (.field (.select keyExpr (.native 1) (.native 0))) :
        Except String Impact.Aligned) = .ok alignedKey at keyAccepted
      exact (Except.ok.inj keyAccepted).symm
    | uint maximum =>
      change (Except.ok (.field (.cast .native keyExpr)) :
        Except String Impact.Aligned) = .ok alignedKey at keyAccepted
      exact (Except.ok.inj keyAccepted).symm
  have storedShape : stored = .push
      (.field (scalarProjection valueSupport valueExpr)) true := by
    cases valueSupport with
    | native =>
      change (Except.ok (.push (.field valueExpr) true) : Except String Impact.Op) =
        .ok stored at storedAccepted
      exact (Except.ok.inj storedAccepted).symm
    | bool =>
      change (Except.ok (.push
        (.field (.select valueExpr (.native 1) (.native 0))) true) :
        Except String Impact.Op) = .ok stored at storedAccepted
      exact (Except.ok.inj storedAccepted).symm
    | uint maximum =>
      change (Except.ok (.push (.field (.cast .native valueExpr)) true) :
        Except String Impact.Op) = .ok stored at storedAccepted
      exact (Except.ok.inj storedAccepted).symm
  rw [keyShape, storedShape] at resultAccepted
  change (Except.ok ({ operations := [] ++
    [.index slot true,
      .push (.field (scalarProjection keySupport keyExpr)) false,
      .push (.field (scalarProjection valueSupport valueExpr)) true,
      .insert 2] } : Impact.Plan)) = .ok base at resultAccepted
  cases resultAccepted
  exact ⟨slot, located, by simp [scalarProjection]⟩

/-- A typed canonical cell write evaluates to the actual emitted slot and
value, with the slot bound derived from the admitted declaration count. -/
theorem writeCell_candidate_eval (state : List StateDecl) (name : String)
    (ty : Ty) (expression : Expr ty) (base : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv) (value : ty.Denote)
    (accepted : Impact.appendEffect state (.writeCell name ty expression) {} = .ok base)
    (cellDecl : Impact.UnalignedCellDeclaration state name ty)
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : expression.eval ctx env = .ok value)
    (canonical : Canonical ty value) :
    ∃ slot, state.findIdx? (·.name == name) = some slot ∧
      base.operations.mapM (GenericStateOps.evalOp ctx env) =
        .ok (GenericStateVM.writeCellOps slot
          (NativeState.field (NativeRelation.scalar (GenericStateEncoding.number ty value)))) := by
  obtain ⟨support⟩ := scalarType_of_canonical canonical
  obtain ⟨slot, located, shape⟩ := writeCell_scalar_chunk state name ty
    expression base support cellDecl accepted
  have inside := (List.findIdx?_eq_some_iff_getElem.mp located).1
  have slotBound := Nat.lt_trans inside stateBound
  have slotEval : (Expr.native slot : Expr .native).eval ctx env = .ok slot := by
    simp [Expr.eval, modulus, slotBound] <;> rfl
  have nativeValue := scalarProjection_eval support ctx env expression value
    modulus evaluated canonical
  refine ⟨slot, located, ?_⟩
  rw [shape]
  simp [GenericStateVM.writeCellOps, GenericStateOps.evalOp,
    GenericStateOps.evalAligned, slotEval, nativeValue, Except.map, Functor.map] <;> rfl

/-- Map key and value projection preserve their canonical field encodings at
the exact slot selected by production state lookup. -/
theorem writeMap_candidate_eval (state : List StateDecl) (name : String)
    (keyTy valueTy : Ty) (keyExpr : Expr keyTy) (valueExpr : Expr valueTy)
    (base : Impact.Plan) (ctx : EvalContext) (env : EvalEnv)
    (key : keyTy.Denote) (value : valueTy.Denote)
    (accepted : Impact.appendEffect state
      (.writeMap name keyTy valueTy keyExpr valueExpr) {} = .ok base)
    (modulus : ctx.modulus = Field.modulus)
    (keyEval : keyExpr.eval ctx env = .ok key)
    (valueEval : valueExpr.eval ctx env = .ok value)
    (keyCanonical : Canonical keyTy key) (valueCanonical : Canonical valueTy value) :
    ∃ slot, state.findIdx? (·.name == name) = some slot ∧
      base.operations.mapM (GenericStateOps.evalOp ctx env) =
        .ok (GenericStateVM.writeMapOps slot
          (NativeRelation.scalar (GenericStateEncoding.number keyTy key))
          (NativeRelation.scalar (GenericStateEncoding.number valueTy value))) := by
  obtain ⟨keySupport⟩ := scalarType_of_canonical keyCanonical
  obtain ⟨valueSupport⟩ := scalarType_of_canonical valueCanonical
  obtain ⟨slot, located, shape⟩ := writeMap_scalar_chunk state name keyTy valueTy
    keyExpr valueExpr base keySupport valueSupport accepted
  have keyNative := scalarProjection_eval keySupport ctx env keyExpr key
    modulus keyEval keyCanonical
  have valueNative := scalarProjection_eval valueSupport ctx env valueExpr value
    modulus valueEval valueCanonical
  refine ⟨slot, located, ?_⟩
  rw [shape]
  simp [GenericStateVM.writeMapOps, GenericStateOps.evalOp,
    GenericStateOps.evalAligned, keyNative, valueNative,
    Except.map, Functor.map] <;> rfl

end Noctium.Verification.GenericStateWriteEvaluation
