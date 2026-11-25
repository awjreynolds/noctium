import Noctium.Verification.ImpactExpressionSoundness
import Noctium.Verification.ImpactWireSoundness

namespace Noctium.Verification.ImpactExpressionSchedule

open Lean Backend ImpactWireDecoder ImpactWireSoundness
open ImpactExpressionMatch ScalarNormalization

/-- Scalar admission required for expression-bearing operations in the
projected Impact fragment. Literal bit operands need no separate admission. -/
def ScalarOperandAdmission : Impact.Op → Prop
  | .mapIndex _ (.field key) => ScalarExpression key
  | .push (.field value) _ => ScalarExpression value
  | .push (.bitExpr value) _ => ScalarExpression value
  | .popeq (.field value) => ScalarExpression value
  | .popeq (.bitExpr value) => ScalarExpression value
  | _ => True

/-- Each admitted typed operand matches the raw JSON field in the projected
operation, including the exact `index.key`, `push.expression`, or
`popeq.expression` value. -/
def TypedOperandMatches : Impact.Op → Operation → Prop
  | .mapIndex _ (.field key), .index _ Bool.false (some raw) => Matches key raw
  | .push (.field value) _, .push _ "field" raw => Matches value raw
  | .push (.bit value) _, .push _ "bit" raw => Matches (.bool value) raw
  | .push (.bitExpr value) _, .push _ "bit" raw => Matches value raw
  | .popeq (.field value), .popeq "field" raw => Matches value raw
  | .popeq (.bit value), .popeq "bit" raw => Matches (.bool value) raw
  | .popeq (.bitExpr value), .popeq "bit" raw => Matches value raw
  | .dup, .dup | .index _ _, .index _ _ none | .member, .member | .insert _, .insert _ => True
  | _, _ => False

private def activityGuardAt (plan : Impact.Plan) (index : Nat) : Option (Expr .bool) :=
  plan.activityGuards[index]?.getD none

/-- A source guard matches the exact optional JSON value retained by the
schedule item decoded from the native plan. -/
def GuardMatches (guard : Option (Expr .bool)) (raw : Option Json) : Prop :=
  match guard, raw with
  | none, none => True
  | some expression, some encoded => Matches expression encoded
  | _, _ => False

def ScheduleGuardMatches (plan : Impact.Plan) (index : Nat) : Prop :=
  GuardMatches (activityGuardAt plan index)
    ((activityGuardAt plan index).map NativeExpression.toJson)

theorem projects_typedOperandMatches {operation : Impact.Op} {projected : Operation}
    (projects : Projects operation projected)
    (admitted : ScalarOperandAdmission operation) :
    TypedOperandMatches operation projected := by
  cases projects with
  | dup => trivial
  | index => trivial
  | mapIndex slot key fits nonNull =>
      exact ImpactExpressionSoundness.matches_toJson admitted
  | pushField value storage =>
      exact ImpactExpressionSoundness.matches_toJson admitted
  | pushBit value storage =>
      exact ImpactExpressionSoundness.matches_toJson (ScalarExpression.bool value)
  | pushBitExpr value storage =>
      exact ImpactExpressionSoundness.matches_toJson admitted
  | popeqField value =>
      exact ImpactExpressionSoundness.matches_toJson admitted
  | popeqBit value =>
      exact ImpactExpressionSoundness.matches_toJson (ScalarExpression.bool value)
  | popeqBitExpr value =>
      exact ImpactExpressionSoundness.matches_toJson admitted
  | «member» => trivial
  | «insert» => trivial

theorem guardMatches_of_admission (plan : Impact.Plan) (index : Nat)
    (admitted : ∀ guard, activityGuardAt plan index = some guard →
      ScalarExpression guard) :
    ScheduleGuardMatches plan index := by
  unfold ScheduleGuardMatches GuardMatches
  cases selected : activityGuardAt plan index with
  | none => trivial
  | some guard =>
      simpa [selected] using
        ImpactExpressionSoundness.matches_toJson (admitted guard selected)

/-- Decode the production plan operations and retain a typed expression match
for every projected operand and activity guard at its original operation
index. Source scalar admission is explicit for each expression-bearing field. -/
theorem decode_nativePlanJson_operations_with_expression_matches
    (profile : TargetProfile) (contractName : Name) (state : List StateDecl)
    (ctor : Option Constructor) (ep : Entrypoint) (plan : Impact.Plan)
    (standaloneFile : _root_.Bool) (projected : Nat → Operation)
    (projects : ∀ op index, (op, index) ∈ plan.operations.zipIdx →
      Projects op (projected index))
    (operandsAdmitted : ∀ op index, (op, index) ∈ plan.operations.zipIdx →
      ScalarOperandAdmission op)
    (guardsAdmitted : ∀ op index, (op, index) ∈ plan.operations.zipIdx →
      ∀ guard, activityGuardAt plan index = some guard →
        ScalarExpression guard) :
    decodePlanOperations
        (Compiler.nativePlanJson profile contractName state ctor ep plan standaloneFile) =
      .ok (projectedSchedule plan projected) ∧
    ∀ op index, (op, index) ∈ plan.operations.zipIdx →
      TypedOperandMatches op (projected index) ∧ ScheduleGuardMatches plan index := by
  have guardValid : ∀ op index, (op, index) ∈ plan.operations.zipIdx →
      ∀ guard, plan.activityGuards[index]?.getD none = some guard →
        (NativeExpression.toJson guard).isNull = Bool.false := by
    intro op index present guard selected
    exact ImpactExpressionSoundness.toJson_nonNull (guardsAdmitted op index present guard selected)
  constructor
  · exact ImpactWireSoundness.decode_nativePlanJson_operations profile contractName state
      ctor ep plan standaloneFile projected projects guardValid
  · intro op index present
    exact ⟨projects_typedOperandMatches (projects op index present)
        (operandsAdmitted op index present),
      guardMatches_of_admission plan index (guardsAdmitted op index present)⟩

end Noctium.Verification.ImpactExpressionSchedule
