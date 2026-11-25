import Noctium.Verification.GenericStateAdmissionPrefix
import Noctium.Verification.GenericStateScalarPrefix
import Noctium.Verification.GenericStateVM
import Noctium.Verification.ScalarCellPublicFields
import Noctium.Verification.ScalarCircuit

namespace Noctium.Verification.ScalarCellNativePublicPrefix

open Backend NativeRelation NativeState ScalarNormalization
open Noctium.Verification.GenericStateOps
open Noctium.Verification.GenericStateScalarPrefix

/-- The actual cells supplied by public scalar circuit inputs, in source
declaration order. -/
def sourcePublicCells (inputs : List Input) (assignment : Assignment) : List Cell :=
  (inputs.filter (·.visibility == .«public»)).map fun input =>
    NativeState.field (assignment ("%input_" ++ input.name))

private def cellPair (cell : Cell) : List NativeState.Op :=
  [.push cell false, .popeq cell]

private def scalarPair (value : Nat) : List NativeState.Op :=
  cellPair (NativeState.field (NativeRelation.scalar value))

private def sourcePublicNumbers (inputs : List Input) (assignment : Assignment) : List Nat :=
  (inputs.filter (·.visibility == .«public»)).map fun input =>
    (assignment ("%input_" ++ input.name)).val

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem scalarOperation_groups_singleton {operation : Impact.Op}
    (supported : GenericStateOps.ScalarOperation operation) :
    operation.fieldGroups = [operation.fields] := by
  cases operation <;> simp_all [GenericStateOps.ScalarOperation, Impact.Op.fieldGroups]

private theorem evalFields_of_each (ctx : EvalContext) (env : EvalEnv)
    (fields : List Impact.Scalar)
    (each : ∀ field ∈ fields, ∃ value, field.eval ctx env = .ok value) :
    ∃ values, GenericStateOps.evalFields ctx env fields = .ok values := by
  induction fields with
  | nil => exact ⟨[], rfl⟩
  | cons head rest ih =>
    obtain ⟨headValue, headEval⟩ := each head (by simp)
    obtain ⟨tailValues, tailEval⟩ := ih (by
      intro field member
      exact each field (by simp [member]))
    have tailEval' := tailEval
    simp only [GenericStateOps.evalFields, Except.map, Functor.map] at tailEval'
    refine ⟨scalar headValue :: tailValues, ?_⟩
    simp [GenericStateOps.evalFields, List.mapM_cons, headEval, tailEval',
      Bind.bind, Except.bind, Except.map, Functor.map, pure, Except.pure]

private theorem evalOperations_of_each_fields (ctx : EvalContext) (env : EvalEnv)
    (operations : List Impact.Op)
    (supported : ∀ operation ∈ operations, GenericStateOps.ScalarOperation operation)
    (fields : ∀ operation ∈ operations,
      ∃ values, GenericStateOps.evalFields ctx env operation.fields = .ok values) :
    ∃ native, operations.mapM (GenericStateOps.evalOp ctx env) = .ok native := by
  induction operations with
  | nil => exact ⟨[], rfl⟩
  | cons operation rest ih =>
    obtain ⟨headFields, headFieldsEval⟩ := fields operation (by simp)
    obtain ⟨tailNative, tailEval⟩ := ih
      (fun item member => supported item (by simp [member]))
      (fun item member => fields item (by simp [member]))
    obtain ⟨headNative, headEval⟩ := GenericStateOps.evalOp_of_fields ctx env operation
      headFields (supported operation (by simp)) headFieldsEval
    refine ⟨headNative :: tailNative, ?_⟩
    simp [List.mapM_cons, headEval, tailEval, Bind.bind, Except.bind,
      pure, Except.pure]

private theorem publicInputPlan_eval_of_group_fields
    (inputs : List Input) (plan : Impact.Plan) (ctx : EvalContext) (env : EvalEnv)
    (compatible : ∀ input ∈ inputs, Impact.publicInputScalarCompatible input)
    (accepted : Impact.publicInputPlan inputs {} = .ok plan)
    (groupFields : ∀ operation ∈ plan.operations, ∀ group ∈ operation.fieldGroups,
      ∀ field ∈ group, ∃ value, field.eval ctx env = .ok value) :
    ∃ native, GenericStateOps.evalPlan ctx env plan = .ok native := by
  have supported := GenericStateOps.publicInputPlan_scalar_supported
    inputs {} plan accepted compatible (by simp)
  have fields : ∀ operation ∈ plan.operations,
      ∃ values, GenericStateOps.evalFields ctx env operation.fields = .ok values := by
    intro operation member
    have operationSupported := supported operation member
    have groups := scalarOperation_groups_singleton operationSupported
    have each : ∀ field ∈ operation.fields, ∃ value, field.eval ctx env = .ok value := by
      intro field fieldMember
      have groupMember : operation.fields ∈ operation.fieldGroups := by
        rw [groups]
        simp
      exact groupFields operation member operation.fields groupMember field fieldMember
    exact evalFields_of_each ctx env operation.fields each
  obtain ⟨native, evaluated⟩ := evalOperations_of_each_fields ctx env plan.operations
    supported fields
  exact ⟨native, by simpa only [GenericStateOps.evalPlan] using evaluated⟩

private theorem publicInputExpression_eval_seed
    (ctx : EvalContext) (circuit : Circuit) (values candidate : EvalEnv)
    (assignment : Assignment) (input : Input)
    (admitted : CanonicalInputs circuit values assignment)
    (lookup : ∀ input ∈ circuit.inputs,
      candidate.lookup input.name = values.lookup input.name)
    (modulus : ctx.modulus = Field.modulus)
    (member : input ∈ circuit.inputs)
    (isPublic : input.visibility = .«public»)
    (compatible : Impact.publicInputScalarCompatible input) :
    ∃ expression ∈ publicInputScalarExpressions input,
      expression.eval ctx candidate = .ok (assignment ("%input_" ++ input.name)).val := by
  cases input with
  | mk name ty visibility span =>
    cases visibility with
    | «private» => cases isPublic
    | «public» =>
      obtain ⟨value, sourceLookup, canonical⟩ := admitted.complete
        ⟨name, ty, .public, span⟩ member
      have candidateLookup : candidate.lookup name = some (Value.pack ty value) := by
        rw [lookup ⟨name, ty, .public, span⟩ member, sourceLookup]
      cases ty with
      | native =>
        have binding := admitted.binding ⟨name, .native, .public, span⟩ member value
          sourceLookup canonical
        have assignedValue : (assignment ("%input_" ++ name)).val = value := by
          change assignment ("%input_" ++ name) = NativeRelation.scalar value at binding
          have h := congrArg Fin.val binding
          simpa [NativeRelation.scalar_no_wrap value canonical.1] using h
        have expressionMember :
            (.ref name : Expr .native) ∈ publicInputScalarExpressions
              ⟨name, .native, .public, span⟩ := by simp [publicInputScalarExpressions]
        have evaluated := GenericStateReadCellEvaluation.canonical_ref_eval
          ctx candidate name .native value
          candidateLookup modulus canonical
        refine ⟨.ref name, expressionMember, ?_⟩
        rw [evaluated, ← assignedValue]
      | bool =>
        have binding := admitted.binding ⟨name, .bool, .public, span⟩ member value
          sourceLookup canonical
        have bound : (if value then 1 else 0) < Field.modulus := by
          cases value <;> decide
        have assignedValue :
            (assignment ("%input_" ++ name)).val = (if value then 1 else 0) := by
          change assignment ("%input_" ++ name) =
            NativeRelation.scalar (if value then 1 else 0) at binding
          have h := congrArg Fin.val binding
          simpa [NativeRelation.scalar_no_wrap _ bound] using h
        have expressionMember :
            (.cast .native (.ref name : Expr .bool) : Expr .native) ∈
              publicInputScalarExpressions ⟨name, .bool, .public, span⟩ := by
          simp [publicInputScalarExpressions]
        have evaluated := GenericStateReadCellEvaluation.readExpression_eval ctx candidate
          name .bool value .bool candidateLookup modulus canonical
        refine ⟨.cast .native (.ref name), expressionMember, ?_⟩
        simpa [GenericStateReadCellEvaluation.readExpression,
          GenericStateEncoding.number, assignedValue] using evaluated
      | uint maximum =>
        have binding := admitted.binding ⟨name, .uint maximum, .public, span⟩ member value
          sourceLookup canonical
        have assignedValue : (assignment ("%input_" ++ name)).val = value := by
          change assignment ("%input_" ++ name) = NativeRelation.scalar value at binding
          have h := congrArg Fin.val binding
          simpa [NativeRelation.scalar_no_wrap value canonical.1] using h
        have expressionMember :
            (.cast .native (.ref name : Expr (.uint maximum)) : Expr .native) ∈
              publicInputScalarExpressions ⟨name, .uint maximum, .public, span⟩ := by
          simp [publicInputScalarExpressions]
        have evaluated := GenericStateReadCellEvaluation.readExpression_eval ctx candidate
          name (.uint maximum) value (.uint maximum canonical.2.1) candidateLookup modulus canonical
        refine ⟨.cast .native (.ref name), expressionMember, ?_⟩
        have exactEval :
            (Expr.cast .native (.ref name : Expr (.uint maximum))).eval ctx candidate =
              .ok (GenericStateEncoding.number (.uint maximum) value) := by
          simpa [GenericStateReadCellEvaluation.readExpression] using evaluated
        rw [exactEval, ← assignedValue]
        rfl
      | bytes length | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ =>
        simp [Impact.publicInputScalarCompatible] at compatible

private theorem publicInputExpressions_eval_source_numbers
    (inputs : List Input) (ctx : EvalContext) (values candidate : EvalEnv)
    (assignment : Assignment) (circuit : Circuit)
    (admitted : CanonicalInputs circuit values assignment)
    (lookup : ∀ input ∈ circuit.inputs,
      candidate.lookup input.name = values.lookup input.name)
    (modulus : ctx.modulus = Field.modulus)
    (members : ∀ input ∈ inputs, input ∈ circuit.inputs)
    (compatible : ∀ input ∈ inputs, Impact.publicInputScalarCompatible input) :
    (inputs.flatMap publicInputScalarExpressions).mapM
      (fun expression => expression.eval ctx candidate) =
      .ok (sourcePublicNumbers inputs assignment) := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
    have inputMember : input ∈ circuit.inputs := members input (by simp)
    have tailMembers : ∀ next ∈ rest, next ∈ circuit.inputs := by
      intro next member
      exact members next (List.mem_cons_of_mem input member)
    have tailCompatible : ∀ next ∈ rest, Impact.publicInputScalarCompatible next := by
      intro next member
      exact compatible next (List.mem_cons_of_mem input member)
    have tailLookup : ∀ next ∈ rest,
        candidate.lookup next.name = values.lookup next.name := by
      intro next member
      exact lookup next (tailMembers next member)
    have tailEval := ih tailMembers tailCompatible
    cases input with
    | mk name ty visibility span =>
      cases visibility with
      | «private» =>
        have privateFilter : (Visibility.private == Visibility.public) = false := by
          decide
        simp [GenericStateScalarPrefix.publicInputScalarExpressions,
          sourcePublicNumbers, privateFilter, tailEval]
      | «public» =>
        have publicFilter : (Visibility.public == Visibility.public) = true := by
          decide
        cases ty with
        | native =>
          have expr := publicInputExpression_eval_seed ctx circuit values candidate
            assignment {name, ty := .native, visibility := .«public», span} admitted lookup modulus
            inputMember rfl (compatible _ (by exact List.mem_cons_self))
          rcases expr with ⟨expression, expressionMember, expressionEval⟩
          simp [GenericStateScalarPrefix.publicInputScalarExpressions] at expressionMember
          subst expression
          simp [sourcePublicNumbers, publicFilter,
            GenericStateScalarPrefix.publicInputScalarExpressions,
            expressionEval, tailEval, Bind.bind, Except.bind, Pure.pure] <;> rfl
        | bool =>
          have expr := publicInputExpression_eval_seed ctx circuit values candidate
            assignment {name, ty := .bool, visibility := .«public», span} admitted lookup modulus
            inputMember rfl (compatible _ (by exact List.mem_cons_self))
          rcases expr with ⟨expression, expressionMember, expressionEval⟩
          simp [GenericStateScalarPrefix.publicInputScalarExpressions] at expressionMember
          subst expression
          simp [sourcePublicNumbers, publicFilter,
            GenericStateScalarPrefix.publicInputScalarExpressions,
            expressionEval, tailEval, Bind.bind, Except.bind, Pure.pure] <;> rfl
        | uint maximum =>
          have expr := publicInputExpression_eval_seed ctx circuit values candidate
            assignment {name, ty := .uint maximum, visibility := .«public», span}
            admitted lookup modulus inputMember (by rfl)
            (compatible _ (by exact List.mem_cons_self))
          rcases expr with ⟨expression, expressionMember, expressionEval⟩
          simp [GenericStateScalarPrefix.publicInputScalarExpressions] at expressionMember
          subst expression
          simp [sourcePublicNumbers, publicFilter,
            GenericStateScalarPrefix.publicInputScalarExpressions,
            expressionEval, tailEval, Bind.bind, Except.bind, Pure.pure] <;> rfl
        | bytes _ | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ =>
          have impossible := compatible _ (by exact List.mem_cons_self)
          simp [Impact.publicInputScalarCompatible] at impossible

/-- Evaluate the accepted native public-input prefix from the exact candidate
environment. Its checked native run preserves the supplied slot stack and
appends precisely the source public input cells in declaration order. -/
theorem run_public_prefix_from_candidate
    (entry : Entrypoint) (plan : Impact.Plan) (ctx : EvalContext)
    (values candidate : EvalEnv) (assignment : Assignment)
    (stack : List NativeState.Node) (reads : List NativeState.Cell)
    (admitted : CanonicalInputs entry.circuit values assignment)
    (compatible : ∀ input ∈ entry.circuit.inputs, Impact.publicInputScalarCompatible input)
    (accepted : Impact.publicInputPlan entry.circuit.inputs {} = .ok plan)
    (lookup : ∀ input ∈ entry.circuit.inputs,
      candidate.lookup input.name = values.lookup input.name)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ native cells sourceNumbers,
      GenericStateOps.evalPlan ctx candidate plan = .ok native ∧
      (entry.circuit.inputs.flatMap publicInputScalarExpressions).mapM
        (fun expression => expression.eval ctx candidate) = .ok sourceNumbers ∧
      native = cells.flatMap cellPair ∧
      cells = sourcePublicCells entry.circuit.inputs assignment ∧
      NativeState.run native ⟨stack, reads⟩ =
        some ⟨stack, reads ++ sourcePublicCells entry.circuit.inputs assignment⟩ := by
  have groupFields := ScalarCellPublicFields.publicInputPlan_group_fields_eval
    entry plan ctx values candidate assignment admitted compatible
    accepted lookup modulus
  obtain ⟨native, evaluated⟩ := publicInputPlan_eval_of_group_fields
    entry.circuit.inputs plan ctx candidate compatible accepted groupFields
  have inputEvaluation := GenericStateScalarPrefix.publicInputPlan_scalar_eval_order
    entry.circuit.inputs plan ctx candidate native compatible accepted evaluated
  obtain ⟨sourceNumbers, expressionsEvaluated, scalarShape⟩ := inputEvaluation
  obtain ⟨cells, nativeShape, nativeRun⟩ :=
    GenericStateAdmissionPrefix.public_prefix_run entry.circuit.inputs plan ctx candidate
      native stack reads accepted compatible
      (by simpa only [GenericStateOps.evalPlan] using evaluated)
  have cellsExpected : cells = sourcePublicCells entry.circuit.inputs assignment := by
    have sourceNumbersExact := publicInputExpressions_eval_source_numbers
      entry.circuit.inputs ctx values candidate assignment entry.circuit admitted lookup modulus
      (fun input member => member) compatible
    have sameNumbers : sourceNumbers = sourcePublicNumbers entry.circuit.inputs assignment :=
      Except.ok.inj (expressionsEvaluated.symm.trans sourceNumbersExact)
    have scalarShape' : native = sourceNumbers.flatMap scalarPair := by
      change native = sourceNumbers.flatMap scalarPair at scalarShape
      exact scalarShape
    have expectedShape : native = (sourcePublicNumbers entry.circuit.inputs assignment).flatMap
        scalarPair := by rw [← sameNumbers]; exact scalarShape'
    have expectedShape' := expectedShape
    change native = (sourcePublicNumbers entry.circuit.inputs assignment).flatMap
      (fun value => [.push (NativeState.field (NativeRelation.scalar value)) false,
        .popeq (NativeState.field (NativeRelation.scalar value))]) at expectedShape'
    have exactCellsShape : sourcePublicCells entry.circuit.inputs assignment =
        (sourcePublicNumbers entry.circuit.inputs assignment).map
          (fun value => NativeState.field (NativeRelation.scalar value)) := by
      unfold sourcePublicCells sourcePublicNumbers
      rw [List.map_map]
      apply List.map_congr_left
      intro input member
      congr 1
      apply Fin.ext
      exact (NativeRelation.scalar_no_wrap _
        (assignment ("%input_" ++ input.name)).isLt).symm
    have expectedOps : native = (sourcePublicCells entry.circuit.inputs assignment).flatMap
        cellPair := by
      rw [exactCellsShape, List.flatMap_map]
      exact expectedShape'
    have sameRuns := Option.some.inj (nativeRun.symm.trans
      (by
        rw [expectedOps]
        exact GenericStateVM.run_input_pairs
          (sourcePublicCells entry.circuit.inputs assignment) stack reads))
    have readEq := congrArg NativeState.Machine.reads sameRuns
    exact List.append_cancel_left readEq
  have nativeShape' : native = cells.flatMap cellPair := by
    change native = cells.flatMap (fun cell => [.push cell false, .popeq cell])
    exact nativeShape
  exact ⟨native, cells, sourceNumbers, evaluated, expressionsEvaluated,
    nativeShape', cellsExpected, by simpa [cellsExpected] using nativeRun⟩

end Noctium.Verification.ScalarCellNativePublicPrefix
