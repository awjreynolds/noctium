import Noctium.Verification.ImpactExpressionAgreement
import Noctium.Verification.ImpactExpressionSchedule
import Noctium.Verification.GenericStateOps

namespace Noctium.Verification.ImpactOperationAgreement

open Lean Backend NativeRelation NativeState
open ImpactExpressionEvaluation ImpactExpressionAgreement ImpactExpressionSchedule
open ImpactWireDecoder ImpactWireSoundness ScalarNormalization
open ImpactReferenceEvaluation

/-- Validation required by each expression-bearing scalar operation. -/
def SourceOperandsValid (types : TypeEnv) : Impact.Op → Prop
  | .mapIndex _ (.field key) =>
      key.validate Capabilities.scalarFragment types = .ok ()
  | .push (.field value) _ =>
      value.validate Capabilities.scalarFragment types = .ok ()
  | .push (.bitExpr value) _ =>
      value.validate Capabilities.scalarFragment types = .ok ()
  | .popeq (.field value) =>
      value.validate Capabilities.scalarFragment types = .ok ()
  | .popeq (.bitExpr value) =>
      value.validate Capabilities.scalarFragment types = .ok ()
  | _ => True

/-- Convert the JSON evaluator's scalar value to the cell selected by the wire
alignment. A field expression cannot become a bit cell, or the reverse. -/
private def alignedValue : String → Value → Option NativeState.Cell
  | "field", .native value => some (NativeState.field (scalar value))
  | "bit", .bool value => some (NativeState.boolean value)
  | _, _ => none

def evaluateAligned (fuel : Nat) (ctx : EvalContext) (env : EvalEnv)
    (alignment : String) (raw : Json) : Option NativeState.Cell :=
  (ImpactExpressionEvaluation.evaluate fuel ctx env raw).bind (alignedValue alignment)

/-- Interpret one operation recovered from the native wire. Unsupported or
malformed operation shapes and rejected operands return none. -/
def evaluateOperation (fuel : Nat) (ctx : EvalContext) (env : EvalEnv) :
    ImpactWireDecoder.Operation → Option NativeState.Op
  | .dup => some .dup
  | .index slot pushPath none =>
      if slot < 2 ^ 32 then some (.index slot pushPath) else none
  | .index slot Bool.false (some raw) => do
      if slot < 2 ^ 32 then pure () else none
      let key ← evaluateAligned fuel ctx env "field" raw
      some (.mapIndex slot key)
  | .index _ Bool.true (some _) => none
  | .push storage alignment raw => do
      let value ← evaluateAligned fuel ctx env alignment raw
      some (.push value storage)
  | .popeq alignment raw => do
      let value ← evaluateAligned fuel ctx env alignment raw
      some (.popeq value)
  | .member => some .member
  | .insert depth =>
      if depth < 2 ^ 8 then some (.insert depth) else none

private theorem evaluateField_toJson (ctx : EvalContext)
    (modulus : ctx.modulus = Field.modulus) (expression : Expr .native)
    (supported : ScalarExpression expression) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel → ∀ types env,
      expression.validate Capabilities.scalarFragment types = .ok () →
      TypedScalarEnv types env →
      evaluateAligned fuel ctx env "field" (NativeExpression.toJson expression) =
        (GenericStateOps.evalAligned ctx env (.field expression)).toOption := by
  obtain ⟨minimum, agrees⟩ := ImpactExpressionAgreement.evaluate_toJson
    ctx modulus supported
  refine ⟨minimum, ?_⟩
  intro fuel enough types env valid typed
  unfold evaluateAligned
  rw [agrees fuel enough types env valid typed]
  cases evaluated : expression.eval ctx env <;>
    simp [alignedValue, GenericStateOps.evalAligned,
      evaluated, Except.toOption, Except.map, Functor.map, Value.pack]

private theorem evaluateBitExpr_toJson (ctx : EvalContext)
    (modulus : ctx.modulus = Field.modulus) (expression : Expr .bool)
    (supported : ScalarExpression expression) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel → ∀ types env,
      expression.validate Capabilities.scalarFragment types = .ok () →
      TypedScalarEnv types env →
      evaluateAligned fuel ctx env "bit" (NativeExpression.toJson expression) =
        (GenericStateOps.evalAligned ctx env (.bitExpr expression)).toOption := by
  obtain ⟨minimum, agrees⟩ := ImpactExpressionAgreement.evaluate_toJson
    ctx modulus supported
  refine ⟨minimum, ?_⟩
  intro fuel enough types env valid typed
  unfold evaluateAligned
  rw [agrees fuel enough types env valid typed]
  cases evaluated : expression.eval ctx env <;>
    simp [alignedValue, GenericStateOps.evalAligned,
      evaluated, Except.toOption, Except.map, Functor.map, Value.pack]

private theorem evaluateBitLiteral_toJson (ctx : EvalContext)
    (modulus : ctx.modulus = Field.modulus) (value : _root_.Bool) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel → ∀ types env,
      TypedScalarEnv types env →
      evaluateAligned fuel ctx env "bit" (NativeExpression.toJson (.bool value)) =
        (GenericStateOps.evalAligned ctx env (.bit value)).toOption := by
  obtain ⟨minimum, agrees⟩ := evaluateBitExpr_toJson ctx modulus (.bool value)
    (ScalarExpression.bool value)
  refine ⟨minimum, ?_⟩
  intro fuel enough types env typed
  rw [agrees fuel enough types env (by simp [Expr.validate]) typed]
  simp [GenericStateOps.evalAligned, Expr.eval, Except.toOption,
    Except.map, Functor.map] <;> rfl

private theorem toOption_bind {α β : Type} (value : Except String α)
    (f : α → β) :
    (value.bind fun x => Except.pure (f x)).toOption =
      value.toOption.bind (fun x => some (f x)) := by
  cases value <;> rfl

/-- The decoded operation evaluator has the same exact optional result as the
source scalar VM. The equality covers both successful evaluation and every
operand rejection. -/
theorem evaluateOperation_projects (ctx : EvalContext)
    (modulus : ctx.modulus = Field.modulus)
    {operation : Impact.Op} {projected : ImpactWireDecoder.Operation}
    {types : TypeEnv} {env : EvalEnv}
    (projects : ImpactWireSoundness.Projects operation projected)
    (admitted : ScalarOperandAdmission operation)
    (valid : SourceOperandsValid types operation)
    (typed : TypedScalarEnv types env) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel →
      evaluateOperation fuel ctx env projected =
        (GenericStateOps.evalOp ctx env operation).toOption := by
  cases projects with
  | dup =>
      refine ⟨0, ?_⟩
      intro fuel enough
      rfl
  | index slot path fits =>
      refine ⟨0, ?_⟩
      intro fuel enough
      simp [evaluateOperation, GenericStateOps.evalOp, fits] <;> rfl
  | mapIndex slot key fits nonNull =>
      have keySupported : ScalarExpression key := by
        simpa [ScalarOperandAdmission] using admitted
      have keyValid : key.validate Capabilities.scalarFragment types = .ok () := by
        simpa [SourceOperandsValid] using valid
      obtain ⟨minimum, agrees⟩ := evaluateField_toJson ctx modulus key
        keySupported
      refine ⟨minimum, ?_⟩
      intro fuel enough
      change evaluateOperation fuel ctx env
          (.index slot Bool.false (some (NativeExpression.toJson key))) =
        (GenericStateOps.evalOp ctx env (.mapIndex slot (.field key))).toOption
      simp [evaluateOperation, agrees fuel enough types env keyValid typed, GenericStateOps.evalOp,
        Bind.bind, Pure.pure, fits]
      exact (toOption_bind _ _).symm
  | pushField value storage =>
      have valueSupported : ScalarExpression value := by
        simpa [ScalarOperandAdmission] using admitted
      have valueValid : value.validate Capabilities.scalarFragment types = .ok () := by
        simpa [SourceOperandsValid] using valid
      obtain ⟨minimum, agrees⟩ := evaluateField_toJson ctx modulus value
        valueSupported
      refine ⟨minimum, ?_⟩
      intro fuel enough
      change evaluateOperation fuel ctx env
          (.push storage "field" (NativeExpression.toJson value)) =
        (GenericStateOps.evalOp ctx env (.push (.field value) storage)).toOption
      simp [evaluateOperation, agrees fuel enough types env valueValid typed, GenericStateOps.evalOp,
        Bind.bind, Pure.pure]
      exact (toOption_bind _ _).symm
  | pushBit value storage =>
      obtain ⟨minimum, agrees⟩ := evaluateBitLiteral_toJson ctx modulus value
      refine ⟨minimum, ?_⟩
      intro fuel enough
      change evaluateOperation fuel ctx env
          (.push storage "bit" (NativeExpression.toJson (.bool value))) =
        (GenericStateOps.evalOp ctx env (.push (.bit value) storage)).toOption
      simp [evaluateOperation, agrees fuel enough types env typed, GenericStateOps.evalOp,
        Bind.bind, Pure.pure]
      exact (toOption_bind _ _).symm
  | pushBitExpr value storage =>
      have valueSupported : ScalarExpression value := by
        simpa [ScalarOperandAdmission] using admitted
      have valueValid : value.validate Capabilities.scalarFragment types = .ok () := by
        simpa [SourceOperandsValid] using valid
      obtain ⟨minimum, agrees⟩ := evaluateBitExpr_toJson ctx modulus value
        valueSupported
      refine ⟨minimum, ?_⟩
      intro fuel enough
      change evaluateOperation fuel ctx env
          (.push storage "bit" (NativeExpression.toJson value)) =
        (GenericStateOps.evalOp ctx env (.push (.bitExpr value) storage)).toOption
      simp [evaluateOperation, agrees fuel enough types env valueValid typed, GenericStateOps.evalOp,
        Bind.bind, Pure.pure]
      exact (toOption_bind _ _).symm
  | popeqField value =>
      have valueSupported : ScalarExpression value := by
        simpa [ScalarOperandAdmission] using admitted
      have valueValid : value.validate Capabilities.scalarFragment types = .ok () := by
        simpa [SourceOperandsValid] using valid
      obtain ⟨minimum, agrees⟩ := evaluateField_toJson ctx modulus value
        valueSupported
      refine ⟨minimum, ?_⟩
      intro fuel enough
      change evaluateOperation fuel ctx env
          (.popeq "field" (NativeExpression.toJson value)) =
        (GenericStateOps.evalOp ctx env (.popeq (.field value))).toOption
      simp [evaluateOperation, agrees fuel enough types env valueValid typed, GenericStateOps.evalOp,
        Bind.bind, Pure.pure]
      exact (toOption_bind _ _).symm
  | popeqBit value =>
      obtain ⟨minimum, agrees⟩ := evaluateBitLiteral_toJson ctx modulus value
      refine ⟨minimum, ?_⟩
      intro fuel enough
      change evaluateOperation fuel ctx env
          (.popeq "bit" (NativeExpression.toJson (.bool value))) =
        (GenericStateOps.evalOp ctx env (.popeq (.bit value))).toOption
      simp [evaluateOperation, agrees fuel enough types env typed, GenericStateOps.evalOp,
        Bind.bind, Pure.pure]
      exact (toOption_bind _ _).symm
  | popeqBitExpr value =>
      have valueSupported : ScalarExpression value := by
        simpa [ScalarOperandAdmission] using admitted
      have valueValid : value.validate Capabilities.scalarFragment types = .ok () := by
        simpa [SourceOperandsValid] using valid
      obtain ⟨minimum, agrees⟩ := evaluateBitExpr_toJson ctx modulus value
        valueSupported
      refine ⟨minimum, ?_⟩
      intro fuel enough
      change evaluateOperation fuel ctx env
          (.popeq "bit" (NativeExpression.toJson value)) =
        (GenericStateOps.evalOp ctx env (.popeq (.bitExpr value))).toOption
      simp [evaluateOperation, agrees fuel enough types env valueValid typed, GenericStateOps.evalOp,
        Bind.bind, Pure.pure]
      exact (toOption_bind _ _).symm
  | «member» =>
      refine ⟨0, ?_⟩
      intro fuel enough
      rfl
  | «insert» depth fits =>
      refine ⟨0, ?_⟩
      intro fuel enough
      simp [evaluateOperation, GenericStateOps.evalOp, fits] <;> rfl

end Noctium.Verification.ImpactOperationAgreement
