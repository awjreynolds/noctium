import Noctium.Verification.GenericStateAdmissionPrefix
import Noctium.Verification.GenericStateCellAdmission
import Noctium.Verification.GenericStateReadCellEvaluation
import Noctium.Verification.GenericStateScalarPrefix
import Noctium.Verification.ScalarCircuit

namespace Noctium.Verification.ScalarCellPublicFields

open Backend NativeRelation ScalarNormalization
open Noctium.Verification.GenericStateOps
open Noctium.Verification.GenericStateScalarPrefix
open Noctium.Verification.GenericStateReadCellEvaluation

theorem canonical_inputs_scalar_compatible (circuit : Circuit) (values : EvalEnv)
    (inputs : Assignment) (admitted : CanonicalInputs circuit values inputs) :
    ∀ input ∈ circuit.inputs, Impact.publicInputScalarCompatible input := by
  intro input member
  obtain ⟨_, _, canonical⟩ := admitted.complete input member
  have support := scalarCellTypeOfCanonical canonical
  cases input with
  | mk name ty visibility span =>
    cases support <;> simp [Impact.publicInputScalarCompatible]

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem publicInputPlan_single_guards (input : Input) (before after : Impact.Plan)
    (compatible : Impact.publicInputScalarCompatible input)
    (accepted : Impact.publicInputPlan [input] before = .ok after) :
    after.guards = before.guards := by
  cases input with
  | mk name ty visibility span =>
    cases visibility with
    | «private» =>
      simp [Impact.publicInputPlan] at accepted ⊢
      cases accepted
      rfl
    | «public» =>
      cases ty with
      | native | bool | uint _ =>
        simp [Impact.publicInputPlan] at accepted ⊢
        cases accepted
        rfl
      | bytes _ | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ =>
        simp [Impact.publicInputScalarCompatible] at compatible

private theorem publicInputPlan_cons (input : Input) (rest : List Input)
    (before : Impact.Plan) :
    Impact.publicInputPlan (input :: rest) before =
      (Impact.publicInputPlan [input] before >>= fun middle =>
        Impact.publicInputPlan rest middle) := by
  simp [Impact.publicInputPlan, List.foldlM_cons]

private theorem publicInputPlan_guards_preserved (inputs : List Input)
    (before after : Impact.Plan)
    (compatible : ∀ input ∈ inputs, Impact.publicInputScalarCompatible input)
    (accepted : Impact.publicInputPlan inputs before = .ok after) :
    after.guards = before.guards := by
  induction inputs generalizing before after with
  | nil =>
    simp [Impact.publicInputPlan] at accepted
    cases accepted
    rfl
  | cons input rest ih =>
    rw [publicInputPlan_cons] at accepted
    rw [bind_ok] at accepted
    obtain ⟨middle, first, tail⟩ := accepted
    have firstGuards := publicInputPlan_single_guards input before middle
      (compatible input (by simp)) first
    have tailCompatible : ∀ item ∈ rest, Impact.publicInputScalarCompatible item := by
      intro item member
      exact compatible item (by simp [member])
    have tailGuards := ih middle after tailCompatible tail
    exact tailGuards.trans firstGuards

/-- Scalar-compatible public inputs preserve the source guard list, while
the production activity theorem preserves its activity schedule. -/
theorem publicInputPlan_empty_guards (inputs : List Input) (plan : Impact.Plan)
    (compatible : ∀ input ∈ inputs, Impact.publicInputScalarCompatible input)
    (accepted : Impact.publicInputPlan inputs {} = .ok plan) :
    plan.guards = [] ∧ plan.activityGuards = [] := by
  have guards := publicInputPlan_guards_preserved inputs {} plan compatible accepted
  have activity := Impact.publicInputPlan_activity_guards inputs {} plan accepted
  exact ⟨by simpa using guards, by simpa using activity⟩

private theorem evalFields_member (ctx : EvalContext) (env : EvalEnv)
    (fields : List Impact.Scalar) (numbers : List Scalar)
    (evaluated : GenericStateOps.evalFields ctx env fields = .ok numbers) :
    ∀ field ∈ fields, ∃ value, field.eval ctx env = .ok value := by
  induction fields generalizing numbers with
  | nil => simp
  | cons head rest ih =>
    simp only [GenericStateOps.evalFields, List.mapM_cons, bind_ok] at evaluated
    obtain ⟨headValue, headEval, tailValues, tailEval, shape⟩ := evaluated
    cases shape
    intro field member
    rcases List.mem_cons.mp member with same | later
    · subst field
      cases evaluatedHead : head.eval ctx env with
      | error message => simp [evaluatedHead, Except.map, Functor.map] at headEval
      | ok value =>
        simp [evaluatedHead, Except.map, Functor.map] at headEval
        exact ⟨value, rfl⟩
    · exact ih tailValues tailEval field later

private theorem scalarOperation_groups_singleton {operation : Impact.Op}
    (supported : GenericStateOps.ScalarOperation operation) :
    operation.fieldGroups = [operation.fields] := by
  cases operation <;> simp_all [GenericStateOps.ScalarOperation, Impact.Op.fieldGroups]

private theorem scalarOperation_group_fields_eval (ctx : EvalContext) (env : EvalEnv)
    (operation : Impact.Op) (supported : GenericStateOps.ScalarOperation operation)
    (modulus : ctx.modulus = Field.modulus)
    (admitted : GenericStateOps.FieldAdmitted operation)
    (evaluated : ∃ native, GenericStateOps.evalOp ctx env operation = .ok native) :
    ∀ group ∈ operation.fieldGroups, ∀ field ∈ group,
      ∃ value, field.eval ctx env = .ok value := by
  obtain ⟨native, nativeEval⟩ := evaluated
  have fieldsEval := GenericStateOps.evalOp_fields ctx env operation native
    modulus admitted nativeEval
  have groups := scalarOperation_groups_singleton supported
  intro group groupMember field fieldMember
  rw [groups] at groupMember
  simp only [List.mem_singleton] at groupMember
  subst group
  exact evalFields_member ctx env operation.fields native.fields fieldsEval field fieldMember

private theorem fieldPush_eval (ctx : EvalContext) (env : EvalEnv)
    (expression : Expr .native) (value : Nat)
    (evaluated : expression.eval ctx env = .ok value) :
    GenericStateOps.evalOp ctx env (.push (.field expression) false) =
      .ok (.push (NativeState.field (NativeRelation.scalar value)) false) := by
  have aligned : GenericStateOps.evalAligned ctx env (.field expression) =
      .ok (NativeState.field (NativeRelation.scalar value)) := by
    simp [GenericStateOps.evalAligned, evaluated, Except.map, Functor.map]
  simp [GenericStateOps.evalOp, aligned, Except.map, Functor.map]

private theorem fieldPopeq_eval (ctx : EvalContext) (env : EvalEnv)
    (expression : Expr .native) (value : Nat)
    (evaluated : expression.eval ctx env = .ok value) :
    GenericStateOps.evalOp ctx env (.popeq (.field expression)) =
      .ok (.popeq (NativeState.field (NativeRelation.scalar value))) := by
  have aligned : GenericStateOps.evalAligned ctx env (.field expression) =
      .ok (NativeState.field (NativeRelation.scalar value)) := by
    simp [GenericStateOps.evalAligned, evaluated, Except.map, Functor.map]
  simp [GenericStateOps.evalOp, aligned, Except.map, Functor.map]

private theorem publicInputExpression_eval
    (ctx : EvalContext) (entry : Entrypoint) (values complete : EvalEnv)
    (assignment : Assignment) (input : Input) (expression : Expr .native)
    (admitted : CanonicalInputs entry.circuit values assignment)
    (lookup : ∀ input ∈ entry.circuit.inputs,
      complete.lookup input.name = values.lookup input.name)
    (modulus : ctx.modulus = Field.modulus)
    (inputMember : input ∈ entry.circuit.inputs)
    (member : expression ∈ publicInputScalarExpressions input) :
    ∃ value, expression.eval ctx complete = .ok value := by
  cases input with
  | mk name ty visibility span =>
    cases visibility with
    | «private» => simp [publicInputScalarExpressions] at member
    | «public» =>
      obtain ⟨value, sourceLookup, canonical⟩ := admitted.complete
        ⟨name, ty, .public, span⟩ inputMember
      have completeLookup : complete.lookup name = some (Value.pack ty value) := by
        rw [lookup ⟨name, ty, .public, span⟩ inputMember, sourceLookup]
      cases ty with
      | native =>
        simp only [publicInputScalarExpressions, List.mem_singleton] at member
        subst expression
        exact ⟨value, canonical_ref_eval ctx complete name .native value
          completeLookup modulus canonical⟩
      | bool =>
        simp only [publicInputScalarExpressions, List.mem_singleton] at member
        subst expression
        have evaluated := readExpression_eval ctx complete name .bool value .bool
          completeLookup modulus canonical
        simpa [readExpression] using
          ⟨GenericStateEncoding.number .bool value, evaluated⟩
      | uint maximum =>
        simp only [publicInputScalarExpressions, List.mem_singleton] at member
        subst expression
        have evaluated := readExpression_eval ctx complete name (.uint maximum) value
          (.uint maximum canonical.2.1) completeLookup modulus canonical
        simpa [readExpression] using
          ⟨GenericStateEncoding.number (.uint maximum) value, evaluated⟩
      | bytes length | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ =>
        simp [publicInputScalarExpressions] at member

private theorem publicInputOperation_group_fields_eval
    (ctx : EvalContext) (entry : Entrypoint) (values complete : EvalEnv)
    (assignment : Assignment) (input : Input) (operation : Impact.Op)
    (admitted : CanonicalInputs entry.circuit values assignment)
    (lookup : ∀ input ∈ entry.circuit.inputs,
      complete.lookup input.name = values.lookup input.name)
    (modulus : ctx.modulus = Field.modulus)
    (inputMember : input ∈ entry.circuit.inputs)
    (operationMember : operation ∈ Impact.publicInputScalarOperations input) :
    ∀ group ∈ operation.fieldGroups, ∀ field ∈ group,
      ∃ value, field.eval ctx complete = .ok value := by
  cases input with
  | mk name ty visibility span =>
    cases visibility with
    | «private» => simp [Impact.publicInputScalarOperations] at operationMember
    | «public» =>
      cases ty with
      | native =>
        have operationShape :
            operation = .push (.field (.ref name : Expr .native)) false ∨
            operation = .popeq (.field (.ref name : Expr .native)) := by
          simpa [Impact.publicInputScalarOperations] using operationMember
        have expressionMember :
            (.ref name : Expr .native) ∈ publicInputScalarExpressions
              ⟨name, .native, .public, span⟩ := by simp [publicInputScalarExpressions]
        obtain ⟨value, valueEval⟩ := publicInputExpression_eval ctx entry values complete
          assignment ⟨name, .native, .public, span⟩ (.ref name) admitted lookup modulus
          inputMember expressionMember
        rcases operationShape with push | popeq
        · subst operation
          exact scalarOperation_group_fields_eval ctx complete _
            (by simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned])
            modulus (by simp [GenericStateOps.FieldAdmitted])
            ⟨_, fieldPush_eval ctx complete _ value valueEval⟩
        · subst operation
          exact scalarOperation_group_fields_eval ctx complete _
            (by simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned])
            modulus (by simp [GenericStateOps.FieldAdmitted])
            ⟨_, fieldPopeq_eval ctx complete _ value valueEval⟩
      | bool =>
        have operationShape :
            operation = .push (.field (.cast .native (.ref name : Expr .bool))) false ∨
            operation = .popeq (.field (.cast .native (.ref name : Expr .bool))) := by
          simpa [Impact.publicInputScalarOperations] using operationMember
        have expressionMember :
            (.cast .native (.ref name : Expr .bool) : Expr .native) ∈
              publicInputScalarExpressions ⟨name, .bool, .public, span⟩ := by
          simp [publicInputScalarExpressions]
        obtain ⟨value, valueEval⟩ := publicInputExpression_eval ctx entry values complete
          assignment ⟨name, .bool, .public, span⟩
          (.cast .native (.ref name : Expr .bool)) admitted lookup modulus inputMember
          expressionMember
        rcases operationShape with push | popeq
        · subst operation
          exact scalarOperation_group_fields_eval ctx complete _
            (by simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned])
            modulus (by simp [GenericStateOps.FieldAdmitted])
            ⟨_, fieldPush_eval ctx complete _ value valueEval⟩
        · subst operation
          exact scalarOperation_group_fields_eval ctx complete _
            (by simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned])
            modulus (by simp [GenericStateOps.FieldAdmitted])
            ⟨_, fieldPopeq_eval ctx complete _ value valueEval⟩
      | uint maximum =>
        have operationShape :
            operation = .push (.field (.cast .native (.ref name : Expr (.uint maximum)))) false ∨
            operation = .popeq (.field (.cast .native (.ref name : Expr (.uint maximum)))) := by
          simpa [Impact.publicInputScalarOperations] using operationMember
        have expressionMember :
            (.cast .native (.ref name : Expr (.uint maximum)) : Expr .native) ∈
              publicInputScalarExpressions ⟨name, .uint maximum, .public, span⟩ := by
          simp [publicInputScalarExpressions]
        obtain ⟨value, valueEval⟩ := publicInputExpression_eval ctx entry values complete
          assignment ⟨name, .uint maximum, .public, span⟩
          (.cast .native (.ref name : Expr (.uint maximum))) admitted lookup modulus
          inputMember expressionMember
        rcases operationShape with push | popeq
        · subst operation
          exact scalarOperation_group_fields_eval ctx complete _
            (by simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned])
            modulus (by simp [GenericStateOps.FieldAdmitted])
            ⟨_, fieldPush_eval ctx complete _ value valueEval⟩
        · subst operation
          exact scalarOperation_group_fields_eval ctx complete _
            (by simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned])
            modulus (by simp [GenericStateOps.FieldAdmitted])
            ⟨_, fieldPopeq_eval ctx complete _ value valueEval⟩
      | bytes length | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ =>
        simp [Impact.publicInputScalarOperations] at operationMember

/-- Every field in the accepted scalar public-input prefix evaluates under
the candidate environment. Lookup agreement carries the admitted source
values to each public scalar input expression. -/
theorem publicInputPlan_group_fields_eval
    (entry : Entrypoint) (plan : Impact.Plan) (ctx : EvalContext)
    (values complete : EvalEnv) (assignment : Assignment)
    (admitted : CanonicalInputs entry.circuit values assignment)
    (compatible : ∀ input ∈ entry.circuit.inputs,
      Impact.publicInputScalarCompatible input)
    (accepted : Impact.publicInputPlan entry.circuit.inputs {} = .ok plan)
    (lookup : ∀ input ∈ entry.circuit.inputs,
      complete.lookup input.name = values.lookup input.name)
    (modulus : ctx.modulus = Field.modulus) :
    ∀ operation ∈ plan.operations, ∀ group ∈ operation.fieldGroups,
      ∀ field ∈ group, ∃ value, field.eval ctx complete = .ok value := by
  have operations := Impact.publicInputPlan_scalar_operations
    entry.circuit.inputs {} plan accepted compatible
  intro operation operationMember
  rw [operations] at operationMember
  simp only [List.nil_append] at operationMember
  obtain ⟨input, inputMember, member⟩ := List.mem_flatMap.mp operationMember
  exact publicInputOperation_group_fields_eval ctx entry values complete assignment
    input operation admitted lookup modulus inputMember member

end Noctium.Verification.ScalarCellPublicFields
