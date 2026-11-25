import Noctium.Compiler
import Noctium.Verification.ImpactWireDecoder

namespace Noctium.Verification.ImpactWireSoundness
open Lean Backend ImpactWireDecoder

/-- The scalar schedule fields independently recovered from an Impact plan.
Guard and operand terms retain the runtime expression JSON. -/
inductive Projects : Impact.Op → Operation → Prop where
  | dup : Projects .dup .dup
  | index (slot : Nat) (path : _root_.Bool) (fits : slot < 2 ^ 32) :
      Projects (.index slot path) (.index slot path none)
  | mapIndex (slot : Nat) (key : Expr .native) (fits : slot < 2 ^ 32)
      (nonNull : (NativeExpression.toJson key).isNull = Bool.false) :
      Projects (.mapIndex slot (.field key))
        (.index slot Bool.false (some (NativeExpression.toJson key)))
  | pushField (value : Expr .native) (storage : _root_.Bool) :
      Projects (.push (.field value) storage)
        (.push storage "field" (NativeExpression.toJson value))
  | pushBit (value storage : _root_.Bool) :
      Projects (.push (.bit value) storage)
        (.push storage "bit" (NativeExpression.toJson (.bool value)))
  | pushBitExpr (value : Expr .bool) (storage : _root_.Bool) :
      Projects (.push (.bitExpr value) storage)
        (.push storage "bit" (NativeExpression.toJson value))
  | popeqField (value : Expr .native) :
      Projects (.popeq (.field value)) (.popeq "field" (NativeExpression.toJson value))
  | popeqBit (value : _root_.Bool) :
      Projects (.popeq (.bit value)) (.popeq "bit" (NativeExpression.toJson (.bool value)))
  | popeqBitExpr (value : Expr .bool) :
      Projects (.popeq (.bitExpr value)) (.popeq "bit" (NativeExpression.toJson value))
  | member : Projects .member .member
  | insert (levels : Nat) (fits : levels < 2 ^ 8) :
      Projects (.insert levels) (.insert levels)

/-- Project the scalar Impact operations supported by the wire decoder.
Operations outside this subset, and values outside the decoder's integer
bounds, are rejected. -/
def project? : Impact.Op → Option Operation
  | .dup => some .dup
  | .index slot path =>
      if slot < 2 ^ 32 then some (.index slot path none) else none
  | .mapIndex slot (.field key) =>
      if slot < 2 ^ 32 then
        if (NativeExpression.toJson key).isNull = Bool.false then
          some (.index slot Bool.false (some (NativeExpression.toJson key)))
        else none
      else none
  | .push (.field value) storage =>
      some (.push storage "field" (NativeExpression.toJson value))
  | .push (.bit value) storage =>
      some (.push storage "bit" (NativeExpression.toJson (.bool value)))
  | .push (.bitExpr value) storage =>
      some (.push storage "bit" (NativeExpression.toJson value))
  | .popeq (.field value) =>
      some (.popeq "field" (NativeExpression.toJson value))
  | .popeq (.bit value) =>
      some (.popeq "bit" (NativeExpression.toJson (.bool value)))
  | .popeq (.bitExpr value) =>
      some (.popeq "bit" (NativeExpression.toJson value))
  | .member => some .member
  | .insert levels => if levels < 2 ^ 8 then some (.insert levels) else none
  | _ => none

/-- Every successful projection is justified by the existing relation. -/
theorem project?_sound {op : Impact.Op} {projected : Operation}
    (accepted : project? op = some projected) : Projects op projected := by
  cases op with
  | dup =>
      simp [project?] at accepted
      cases accepted
      exact .dup
  | index slot path =>
      by_cases fits : slot < 2 ^ 32
      · simp [project?, fits] at accepted
        cases accepted
        exact .index slot path fits
      · simp [project?, fits] at accepted
  | mapIndex slot key =>
      cases key with
      | field key =>
          by_cases fits : slot < 2 ^ 32
          · by_cases nonNull : (NativeExpression.toJson key).isNull = Bool.false
            · simp [project?, fits, nonNull] at accepted
              cases accepted
              exact .mapIndex slot key fits nonNull
            · simp [project?, fits, nonNull] at accepted
          · simp [project?, fits] at accepted
      | _ => simp [project?] at accepted
  | push value storage =>
      cases value with
      | field value =>
          simp [project?] at accepted
          cases accepted
          exact .pushField value storage
      | bit value =>
          simp [project?] at accepted
          cases accepted
          exact .pushBit value storage
      | bitExpr value =>
          simp [project?] at accepted
          cases accepted
          exact .pushBitExpr value storage
      | _ => simp [project?] at accepted
  | popeq value =>
      cases value with
      | field value =>
          simp [project?] at accepted
          cases accepted
          exact .popeqField value
      | bit value =>
          simp [project?] at accepted
          cases accepted
          exact .popeqBit value
      | bitExpr value =>
          simp [project?] at accepted
          cases accepted
          exact .popeqBitExpr value
      | _ => simp [project?] at accepted
  | «member» =>
      simp [project?] at accepted
      cases accepted
      exact .member
  | «insert» levels =>
      by_cases fits : levels < 2 ^ 8
      · simp [project?, fits] at accepted
        cases accepted
        exact .insert levels fits
      · simp [project?, fits] at accepted
  | _ => simp [project?] at accepted

/-- Totalize indexed projection for callers that build a schedule. The
fallback applies only when the requested index is absent or unsupported. -/
def projectedOperation (plan : Impact.Plan) (index : Nat) : Operation :=
  (plan.operations[index]?.bind project?).getD .dup

/-- A successful projection check for every plan operation proves that each
indexed schedule entry belongs to `Projects`. -/
theorem projects_of_check (plan : Impact.Plan)
    (checked : plan.operations.all (fun op => (project? op).isSome) = Bool.true) :
    ∀ op index, (op, index) ∈ plan.operations.zipIdx →
      Projects op (projectedOperation plan index) := by
  intro op index inside
  have getOperation : plan.operations[index]? = some op :=
    List.mk_mem_zipIdx_iff_getElem?.mp inside
  have supported : (project? op).isSome = Bool.true :=
    (List.all_eq_true.mp checked) op (List.mem_of_getElem? getOperation)
  cases projectedEq : project? op with
  | none => simp [projectedEq] at supported
  | some projected =>
      have fallbackEq : projectedOperation plan index = projected := by
        simp [projectedOperation, getOperation, projectedEq]
      rw [fallbackEq]
      exact project?_sound projectedEq

private theorem decode_bare {operation : Impact.Op} {projected : Operation}
    (projects : Projects operation projected) :
    decodeBareOperation (Compiler.nativeOperationJson none operation) = .ok projected := by
  cases projects
  case index slot path fits => exact decode_index_positional slot path fits
  case mapIndex slot key fits nonNull => exact decode_index_key slot _ fits nonNull
  case «insert» levels fits => exact decode_insert levels fits
  all_goals rfl

private def operationTag : Operation → String
  | .dup => "dup"
  | .index .. => "index"
  | .push .. => "push"
  | .popeq .. => "popeq"
  | .member => "member"
  | .insert .. => "insert"

theorem decode_operation {operation : Impact.Op} {projected : Operation}
    (projects : Projects operation projected) (guard : Option (Expr .bool))
    (guardValid : ∀ g, guard = some g → (NativeExpression.toJson g).isNull = Bool.false) :
    decodeOperation (Compiler.nativeOperationJson guard operation) =
      .ok ⟨guard.map NativeExpression.toJson, projected⟩ := by
  cases guard with
  | none =>
    have tag : ((Compiler.nativeOperationJson none operation).getObjVal? "op" >>=
        Json.getStr?) = .ok (operationTag projected) := by cases projects <;> rfl
    have plain : operationTag projected ≠ "guarded" := by cases projected <;> simp [operationTag]
    exact decode_unguarded tag plain (decode_bare projects)
  | some guard =>
    exact decode_guarded (NativeExpression.toJson guard)
      (Compiler.nativeOperationJson none operation) (guardValid guard rfl)
      (decode_bare projects)

private def guardAt (plan : Impact.Plan) (index : Nat) : Option (Expr .bool) :=
  plan.activityGuards[index]?.getD none

def projectedSchedule (plan : Impact.Plan) (projected : Nat → Operation) :
    List ScheduledOperation :=
  plan.operations.zipIdx.map fun (_, index) =>
    ⟨(guardAt plan index).map NativeExpression.toJson, projected index⟩

private theorem decode_list {α : Type}
    (items : List α) (encode : α → Json) (project : α → ScheduledOperation)
    (pointwise : ∀ item ∈ items, decodeOperation (encode item) = .ok (project item)) :
    (items.map encode).mapM decodeOperation = .ok (items.map project) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, List.mapM_cons,
      pointwise head (by simp),
      ih (fun item inside => pointwise item (List.mem_cons_of_mem _ inside))]
    rfl

/-- Recover the ordered operation and guard fields of the production Impact
tree. This result leaves expression interpretation to the runtime semantics. -/
theorem decode_nativePlanJson_operations
    (profile : TargetProfile) (contractName : Name) (state : List StateDecl)
    (ctor : Option Constructor) (ep : Entrypoint) (plan : Impact.Plan)
    (standaloneFile : _root_.Bool) (projected : Nat → Operation)
    (supported : ∀ op index, (op, index) ∈ plan.operations.zipIdx →
      Projects op (projected index))
    (guardValid : ∀ op index, (op, index) ∈ plan.operations.zipIdx →
      ∀ g, guardAt plan index = some g → (NativeExpression.toJson g).isNull = Bool.false) :
    decodePlanOperations
        (Compiler.nativePlanJson profile contractName state ctor ep plan standaloneFile) =
      .ok (projectedSchedule plan projected) := by
  unfold decodePlanOperations
  rw [Compiler.nativePlanJson_operations]
  change ((plan.operations.zipIdx.map _).toArray.map (id : Json → Json)).toList.mapM
    decodeOperation = .ok _
  simp only [Array.map_id, List.toList_toArray]
  apply decode_list
  rintro ⟨op, index⟩ inside
  exact decode_operation (supported op index inside) (guardAt plan index)
    (guardValid op index inside)

end Noctium.Verification.ImpactWireSoundness
