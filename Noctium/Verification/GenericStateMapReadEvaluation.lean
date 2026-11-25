import Noctium.Verification.GenericStateCellAdmission
import Noctium.Verification.GenericStateEncoding
import Noctium.Verification.GenericStateOps
import Noctium.Verification.GenericStateReadCellEvaluation
import Noctium.Verification.GenericStateVM
import Noctium.Verification.GenericStateWriteEvaluation

namespace Noctium.Verification.GenericStateMapReadEvaluation
open Backend GenericStateCellAdmission GenericStateEncoding NativeRelation
  NativeState ScalarNormalization

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- A supported source map read keeps the exact selected slot, field
projections, appended operations, and plain read descriptor from Impact. -/
theorem readMap_scalar_chunk (state : List StateDecl) (name destination : String)
    (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (before after : Impact.Plan) (keySupport : ScalarType keyTy)
    (valueSupport : ScalarCellType valueTy)
    (accepted : Impact.appendEffect state
      (.readMap name destination keyTy valueTy keyExpr) before = .ok after) :
    ∃ slot, state.findIdx? (·.name == name) = some slot ∧
      after.operations = before.operations ++
        [.dup,
          .mapIndex slot (.field (GenericStateWriteEvaluation.scalarProjection
            keySupport keyExpr)),
          .popeq (.field (GenericStateReadCellEvaluation.readExpression
            valueSupport destination))] ∧
      after.reads = before.reads ++ [{name := destination, ty := valueTy}] := by
  simp only [Impact.appendEffect, bind_ok] at accepted
  rcases accepted with
    ⟨slot, slotAccepted, alignedKey, keyAccepted, readValue, readValueAccepted,
      resultAccepted⟩
  have located : state.findIdx? (·.name == name) = some slot := by
    apply GenericStateWriteEvaluation.stateSlot_found state name slot
    change (match state.findIdx? (·.name == name) with
      | some index => (pure index : Except String Nat)
      | none => throw s!"unknown ledger state '{name}'") = .ok slot at slotAccepted
    exact slotAccepted
  have keyShape : alignedKey = .field
      (GenericStateWriteEvaluation.scalarProjection keySupport keyExpr) := by
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
  have readShape : readValue = .popeq (.field
      (GenericStateReadCellEvaluation.readExpression valueSupport destination)) := by
    cases valueSupport with
    | native =>
      change (Except.ok (.popeq (.field (.ref destination))) :
        Except String Impact.Op) = .ok readValue at readValueAccepted
      exact (Except.ok.inj readValueAccepted).symm
    | bool =>
      change (Except.ok (.popeq
        (.field (.cast .native (.ref destination : Expr .bool))) :
        Impact.Op) : Except String Impact.Op) = .ok readValue at readValueAccepted
      exact (Except.ok.inj readValueAccepted).symm
    | uint maximum valid =>
      change (Except.ok (.popeq
        (.field (.cast .native (.ref destination : Expr (.uint maximum)))) :
        Impact.Op) : Except String Impact.Op) = .ok readValue at readValueAccepted
      exact (Except.ok.inj readValueAccepted).symm
  rw [keyShape, readShape] at resultAccepted
  change (Except.ok ({ before with
    operations := before.operations ++
      [.dup,
        .mapIndex slot (.field (GenericStateWriteEvaluation.scalarProjection
          keySupport keyExpr)),
        .popeq (.field (GenericStateReadCellEvaluation.readExpression
          valueSupport destination))]
    reads := before.reads ++ [{name := destination, ty := valueTy}] } : Impact.Plan)) =
      .ok after at resultAccepted
  cases resultAccepted
  exact ⟨slot, located, rfl, rfl⟩

/-- Evaluating the actual map-read suffix uses the source key and candidate
value that the production operations project. -/
theorem readMap_candidate_eval (state : List StateDecl) (name destination : String)
    (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (before after : Impact.Plan) (ctx : EvalContext) (env : EvalEnv)
    (key : keyTy.Denote) (value : valueTy.Denote)
    (accepted : Impact.appendEffect state
      (.readMap name destination keyTy valueTy keyExpr) before = .ok after)
    (lookup : env.lookup destination = some (Value.pack valueTy value))
    (modulus : ctx.modulus = Field.modulus)
    (keyEval : keyExpr.eval ctx env = .ok key)
    (keyCanonical : Canonical keyTy key)
    (valueCanonical : Canonical valueTy value) :
    ∃ slot, state.findIdx? (·.name == name) = some slot ∧
      (after.operations.drop before.operations.length).mapM
        (GenericStateOps.evalOp ctx env) =
        .ok (GenericStateVM.readMapOps slot
          (NativeRelation.scalar (GenericStateEncoding.number keyTy key))
          (NativeRelation.scalar (GenericStateEncoding.number valueTy value))) := by
  obtain ⟨keySupport⟩ :=
    GenericStateWriteEvaluation.scalarType_of_canonical keyCanonical
  let valueSupport := GenericStateReadCellEvaluation.scalarCellTypeOfCanonical valueCanonical
  obtain ⟨slot, located, operationsShape, _⟩ := readMap_scalar_chunk
    state name destination keyTy valueTy keyExpr before after keySupport
    valueSupport accepted
  have suffixShape : after.operations.drop before.operations.length =
      [.dup,
        .mapIndex slot (.field (GenericStateWriteEvaluation.scalarProjection
          keySupport keyExpr)),
        .popeq (.field (GenericStateReadCellEvaluation.readExpression
          valueSupport destination))] := by
    rw [operationsShape]
    simp
  have keyValue := GenericStateWriteEvaluation.scalarProjection_eval keySupport
    ctx env keyExpr key modulus keyEval keyCanonical
  have readValue := GenericStateReadCellEvaluation.readExpression_eval ctx env
    destination valueTy value valueSupport lookup modulus valueCanonical
  refine ⟨slot, located, ?_⟩
  rw [suffixShape]
  simp [GenericStateVM.readMapOps, GenericStateOps.evalOp,
    GenericStateOps.evalAligned, keyValue, readValue, Except.map, Functor.map] <;> rfl

end Noctium.Verification.GenericStateMapReadEvaluation
