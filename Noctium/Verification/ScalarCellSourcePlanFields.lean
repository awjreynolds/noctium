import Noctium.Verification.GenericStateCellAdmission
import Noctium.Verification.GenericStateReadCellEvaluation
import Noctium.Verification.GenericStateWriteEvaluation
import Noctium.Verification.GenericStateOps
import Noctium.Verification.GenericStateEffectValidation
import Noctium.Verification.GenericStatePrefixEnvironment
import Noctium.Verification.ScalarCellSourceReads
import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.ScalarWitnessConstruction

open Noctium Backend NativeRelation NativeState GenericStateCellAdmission
  GenericStateOps ScalarNormalization GenericStateEffectValidation
  GenericStatePrefixEnvironment

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private def scalarTypeOfCell {ty : Ty} : ScalarCellType ty → ScalarType ty
  | .native => .native
  | .bool => .bool
  | .uint maximum _ => .uint maximum

private theorem native_validation_bound (types : TypeEnv) (value : Nat)
    (valid : (Expr.native value).validate Capabilities.crypto types = .ok ()) :
    value < Field.modulus := by
  by_cases bound : value < Field.modulus
  · exact bound
  · simp [Expr.validate, Capabilities.crypto, bound] at valid

private theorem native_literal_eval_of_valid (ctx : EvalContext) (env : EvalEnv)
    (types : TypeEnv) (modulus : ctx.modulus = Field.modulus) (value : Nat)
    (valid : (Expr.native value).validate Capabilities.crypto types = .ok ()) :
    (Expr.native value).eval ctx env = .ok value := by
  have bound := native_validation_bound types value valid
  simp [Expr.eval, modulus, bound] <;> rfl

private theorem scalarOperation_groups_singleton {operation : Impact.Op}
    (supported : ScalarOperation operation) :
    operation.fieldGroups = [operation.fields] := by
  cases operation <;> simp_all [ScalarOperation, Impact.Op.fieldGroups]

private theorem grouped_fields_evaluate_of_fields
    (ctx : EvalContext) (env : EvalEnv) (operation : Impact.Op)
    (supported : ScalarOperation operation)
    (fieldsEvaluate : ∀ field ∈ operation.fields,
      ∃ value, field.eval ctx env = .ok value) :
    ∀ group ∈ operation.fieldGroups, ∀ field ∈ group,
      ∃ value, field.eval ctx env = .ok value := by
  intro group groupMember field fieldMember
  rw [scalarOperation_groups_singleton supported] at groupMember
  simp only [List.mem_singleton] at groupMember
  subst group
  exact fieldsEvaluate field fieldMember

private theorem operation_fields_valid_of_groups (types : TypeEnv)
    (operation : Impact.Op) (supported : ScalarOperation operation)
    (validated : ∀ group ∈ operation.fieldGroups, ∀ field ∈ group,
      field.validate Capabilities.crypto types = .ok ()) :
    ∀ field ∈ operation.fields, field.validate Capabilities.crypto types = .ok () := by
  intro field member
  have groupEq := scalarOperation_groups_singleton supported
  have groupMember : operation.fields ∈ operation.fieldGroups := by
    rw [groupEq]
    simp
  exact validated operation.fields groupMember field member

private theorem operation_field_admitted_of_validated (types : TypeEnv)
    (operation : Impact.Op)
    (valid : ∀ field ∈ operation.fields,
      field.validate Capabilities.crypto types = .ok ()) :
    GenericStateOps.FieldAdmitted operation := by
  cases operation with
  | index slot pushPath =>
    have slotMember : (Expr.native slot : Impact.Scalar) ∈
        (Impact.Op.index slot pushPath).fields := by
      simp [Impact.Op.fields, Impact.Aligned.fields]
    exact native_validation_bound types slot (valid (.native slot) slotMember)
  | mapIndex slot key =>
    have slotMember : (Expr.native slot : Impact.Scalar) ∈
        (Impact.Op.mapIndex slot key).fields := by
      simp [Impact.Op.fields, Impact.Aligned.fields]
    exact native_validation_bound types slot (valid (.native slot) slotMember)
  | insert levels =>
    have opcodeMember : (Expr.native (0x90 + levels) : Impact.Scalar) ∈
        (Impact.Op.insert levels).fields := by
      simp [Impact.Op.fields]
    exact native_validation_bound types (0x90 + levels)
      (valid (.native (0x90 + levels)) opcodeMember)
  | _ => simp [GenericStateOps.FieldAdmitted]

private theorem evalFields_member (ctx : EvalContext) (env : EvalEnv)
    (fields : List Impact.Scalar) (values : List Scalar)
    (accepted : GenericStateOps.evalFields ctx env fields = .ok values) :
    ∀ field ∈ fields, ∃ value, field.eval ctx env = .ok value := by
  induction fields generalizing values with
  | nil => intro field member; simp at member
  | cons head tail ih =>
    simp only [GenericStateOps.evalFields, List.mapM_cons] at accepted
    obtain ⟨first, firstAccepted, restAccepted⟩ := bind_ok.mp accepted
    cases headEval : head.eval ctx env with
    | error message => simp [headEval, Except.map, Functor.map] at firstAccepted
    | ok headValue =>
      have firstEq : first = scalar headValue := by
        have okEq : (Except.ok (scalar headValue) : Except String Scalar) =
            Except.ok first := by
          simpa [headEval, Except.map, Functor.map] using firstAccepted
        exact (Except.ok.inj okEq).symm
      subst first
      obtain ⟨tailValues, tailAccepted, _⟩ := bind_ok.mp restAccepted
      have tailFieldsAccepted : GenericStateOps.evalFields ctx env tail = .ok tailValues := by
        simpa [GenericStateOps.evalFields] using tailAccepted
      intro field member
      simp only [List.mem_cons] at member
      rcases member with same | member
      · subst field
        exact ⟨headValue, headEval⟩
      · exact ih tailValues tailFieldsAccepted field member

private theorem eval_fields_of_evalOp (ctx : EvalContext) (env : EvalEnv)
    (operation : Impact.Op) (native : NativeState.Op)
    (modulus : ctx.modulus = Field.modulus)
    (admitted : GenericStateOps.FieldAdmitted operation)
    (accepted : GenericStateOps.evalOp ctx env operation = .ok native) :
    ∀ field ∈ operation.fields, ∃ value, field.eval ctx env = .ok value := by
  have fields := GenericStateOps.evalOp_fields ctx env operation native modulus admitted accepted
  exact evalFields_member ctx env operation.fields native.fields fields

private theorem suffix_group_fields_evaluate (ctx : EvalContext) (env : EvalEnv)
    (types : TypeEnv) (modulus : ctx.modulus = Field.modulus)
    (plan next : Impact.Plan) (suffix : List Impact.Op)
    (shape : next.operations = plan.operations ++ suffix)
    (supported : ∀ operation ∈ next.operations, ScalarOperation operation)
    (validated : ∀ operation ∈ next.operations, ∀ group ∈ operation.fieldGroups,
      ∀ field ∈ group, field.validate Capabilities.crypto types = .ok ())
    (evaluated : ∀ operation ∈ suffix, ∃ native : NativeState.Op,
      GenericStateOps.evalOp ctx env operation = .ok native) :
    ∀ operation ∈ suffix, ∀ group ∈ operation.fieldGroups, ∀ field ∈ group,
      ∃ value, field.eval ctx env = .ok value := by
  intro operation member group groupMember field fieldMember
  have nextMember : operation ∈ next.operations := by
    rw [shape]
    exact List.mem_append.mpr (Or.inr member)
  have operationSupported := supported operation nextMember
  have groupShape := scalarOperation_groups_singleton operationSupported
  rw [groupShape] at groupMember
  simp only [List.mem_singleton] at groupMember
  subst group
  have fieldsValid := operation_fields_valid_of_groups types operation operationSupported
    (fun group groupMember => validated operation nextMember group groupMember)
  have fieldAdmitted := operation_field_admitted_of_validated types operation fieldsValid
  obtain ⟨native, nativeEval⟩ := evaluated operation member
  exact eval_fields_of_evalOp ctx env operation native modulus fieldAdmitted nativeEval
    field fieldMember

/-- A single unguarded scalar-cell effect appends only field groups whose
operands evaluate in the complete candidate environment after its source step.
Literal fields are covered by accepted plan validation evidence. -/
theorem append_cell_effect_group_fields_eval (ctx : EvalContext)
    (state : List StateDecl) (effect : Effect) (source : ScalarCellEffect state effect)
    (operand : ScalarCellSourceReads.ScalarCellOperand effect)
    (plan next : Impact.Plan) (planTypes sourceTypes nextTypes : TypeEnv)
    (accepted : Impact.appendEffect state effect plan = .ok next)
    (before after : SourceEffects.Frame)
    (modulus : ctx.modulus = Field.modulus)
    (sourceStep : SourceEffects.step ctx effect before = .ok after)
    (effectValidation : EffectValidation state sourceTypes effect nextTypes)
    (complete : EvalEnv) (agrees : AgreesOnTypes sourceTypes before.1 complete)
    (readBinding : ∀ name destination ty, effect = .readCell name destination ty →
      complete.lookup destination = after.1.lookup destination)
    (previous : ∀ operation ∈ plan.operations, ScalarOperation operation)
    (validated : ∀ operation ∈ next.operations, ∀ group ∈ operation.fieldGroups,
      ∀ field ∈ group, field.validate Capabilities.crypto planTypes = .ok ()) :
    ∃ suffix, next.operations = plan.operations ++ suffix ∧
      ∀ operation ∈ suffix, ∀ group ∈ operation.fieldGroups, ∀ field ∈ group,
        ∃ value, field.eval ctx complete = .ok value := by
  cases source with
  | readCell name destination ty scalar declaration =>
    cases effectValidation with
    | readCell _ _ =>
      obtain ⟨slot, operationsShape, nextSupported⟩ :=
        GenericStateCellAdmission.append_read_cell_scalar_supported state plan next
          name destination ty scalar declaration accepted previous
      obtain ⟨value, _, canonical, frameShape⟩ :=
        ScalarCellSourceReads.readCell_step_value ctx before.1 before.2 state
          name destination ty (.readCell name destination ty scalar declaration)
          after modulus sourceStep
      subst after
      let readExpr := GenericStateCellAdmission.scalarCellReadExpression scalar destination
      let suffix : List Impact.Op := [.dup, .index slot, .popeq (.field readExpr)]
      have suffixShape : next.operations = plan.operations ++ suffix := by
        simpa [suffix] using operationsShape
      have readExprEq : readExpr = GenericStateReadCellEvaluation.readExpression scalar destination := by
        cases scalar <;> rfl
      have candidateLookup : complete.lookup destination = some (Value.pack ty value) := by
        have binding := readBinding name destination ty rfl
        simpa using binding
      have readExprEval : readExpr.eval ctx complete =
          .ok (GenericStateEncoding.number ty value) := by
        rw [readExprEq]
        exact GenericStateReadCellEvaluation.readExpression_eval ctx
            complete destination ty value scalar candidateLookup modulus canonical
      have suffixEvaluated : ∀ operation ∈ suffix, ∃ native : NativeState.Op,
          GenericStateOps.evalOp ctx complete operation =
            .ok native := by
        intro operation member
        simp only [suffix, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact ⟨.dup, rfl⟩
        · exact ⟨.index slot false, rfl⟩
        · exact ⟨.popeq (NativeState.field
            (NativeRelation.scalar (GenericStateEncoding.number ty value))), by
            simp [GenericStateOps.evalOp, GenericStateOps.evalAligned, readExprEval,
              Except.map, Functor.map]⟩
      exact ⟨suffix, suffixShape,
        suffix_group_fields_evaluate ctx complete planTypes modulus plan next suffix suffixShape
          nextSupported validated suffixEvaluated⟩
  | writeCell name ty expression scalar declaration =>
    cases effectValidation with
    | writeCell _ valueValid =>
      have expressionAdmission : ScalarExpression expression := by
        simpa [ScalarCellSourceReads.ScalarCellOperand] using operand
      obtain ⟨slot, operationsShape, nextSupported⟩ :=
        GenericStateCellAdmission.append_write_cell_scalar_supported state plan next
          name ty expression scalar declaration accepted previous
      obtain ⟨_, value, _, expressionEval, canonical, frameShape⟩ :=
        ScalarCellSourceReads.writeCell_step_value ctx before.1 before.2 state
          name ty expression (.writeCell name ty expression scalar declaration)
          expressionAdmission after modulus sourceStep
      subst after
      let writeExpr := GenericStateCellAdmission.scalarCellWriteExpression scalar expression
      have writeExprEq : writeExpr = GenericStateWriteEvaluation.scalarProjection
          (scalarTypeOfCell scalar) expression := by
        cases scalar <;> rfl
      have expressionEvalComplete : expression.eval ctx complete = .ok value := by
        have scopedEval := GenericStatePrefixEnvironment.eval_scoped sourceTypes before.1 complete
          agrees ctx GenericStateEffectValidation.stateEffectCaps expression valueValid
        calc
          expression.eval ctx complete = expression.eval ctx before.1 := scopedEval.symm
          _ = .ok value := expressionEval
      have writeExprEvalComplete : writeExpr.eval ctx complete =
          .ok (GenericStateEncoding.number ty value) := by
        rw [writeExprEq]
        exact GenericStateWriteEvaluation.scalarProjection_eval (scalarTypeOfCell scalar)
          ctx complete expression value modulus expressionEvalComplete canonical
      let suffix : List Impact.Op := [
        .push (.field (.native slot)), .push (.field writeExpr) true, .insert 1]
      have suffixShape : next.operations = plan.operations ++ suffix := by
        simpa [suffix] using operationsShape
      have firstOperation : Impact.Op.push (.field (.native slot)) ∈ next.operations := by
        rw [suffixShape]
        exact List.mem_append.mpr (Or.inr (by simp [suffix]))
      have firstSupported := nextSupported _ firstOperation
      have firstFieldsValid := operation_fields_valid_of_groups planTypes _ firstSupported
        (fun group groupMember => validated _ firstOperation group groupMember)
      have slotMember : (.native slot : Impact.Scalar) ∈
          (Impact.Op.push (.field (.native slot))).fields := by
        simp [Impact.Op.fields, Impact.Aligned.fields]
      have slotEval := native_literal_eval_of_valid ctx complete planTypes modulus slot
        (firstFieldsValid (.native slot) slotMember)
      have suffixEvaluated : ∀ operation ∈ suffix, ∃ native : NativeState.Op,
          GenericStateOps.evalOp ctx complete operation = .ok native := by
        intro operation member
        simp only [suffix, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact ⟨.push (NativeState.field (NativeRelation.scalar slot)) false, by
            simp [GenericStateOps.evalOp, GenericStateOps.evalAligned, slotEval,
              Except.map, Functor.map]⟩
        · exact ⟨.push (NativeState.field
            (NativeRelation.scalar (GenericStateEncoding.number ty value))) true, by
            simp [GenericStateOps.evalOp, GenericStateOps.evalAligned, writeExprEvalComplete,
              Except.map, Functor.map]⟩
        · exact ⟨.insert 1, rfl⟩
      exact ⟨suffix, suffixShape,
        suffix_group_fields_evaluate ctx complete planTypes modulus plan next suffix suffixShape
          nextSupported validated suffixEvaluated⟩

/-- Unguarded cell reads and writes append no source guards. -/
theorem append_cell_effect_guards_preserved (state : List StateDecl)
    (effect : Effect) (source : ScalarCellEffect state effect)
    (plan next : Impact.Plan)
    (accepted : Impact.appendEffect state effect plan = .ok next) :
    next.guards = plan.guards := by
  cases source with
  | readCell name destination ty scalar declaration =>
    simp only [Impact.appendEffect, bind_ok] at accepted
    obtain ⟨slot, slotAccepted, value, valueAccepted, resultAccepted⟩ := accepted
    have guardsEqual := congrArg Impact.Plan.guards (Except.ok.inj resultAccepted)
    simpa using guardsEqual.symm
  | writeCell name ty value scalar declaration =>
    simp only [Impact.appendEffect, bind_ok] at accepted
    obtain ⟨slot, slotAccepted, stored, storedAccepted, resultAccepted⟩ := accepted
    have guardsEqual := congrArg Impact.Plan.guards (Except.ok.inj resultAccepted)
    simpa using guardsEqual.symm

end Noctium.Verification.ScalarWitnessConstruction
