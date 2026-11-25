import Noctium.Verification.GenericStateAdmissionBridge
import Noctium.Verification.ScalarNormalizationSoundness

namespace Noctium.Verification.ScalarImpactOperationMeaning

open Backend NativeRelation ScalarNormalization

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- Each supported scalar VM operation has one ordered public field group. -/
private theorem fieldGroups_eq_singleton {operation : Impact.Op}
    (supported : GenericStateOps.ScalarOperation operation) :
    operation.fieldGroups = [operation.fields] := by
  cases operation <;> simp_all [GenericStateOps.ScalarOperation, Impact.Op.fieldGroups]

private theorem normalized_fields (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (aliases : Native.AliasEnvironment) (env : EvalEnv) (types : TypeEnv)
    (typed : TypedEnvironment hash inputs aliases env types)
    (fields : List Impact.Scalar) (normalized : List Native.Normalized)
    (admitted : ∀ field ∈ fields, ScalarExpression field)
    (valid : ∀ field ∈ fields, field.validate Capabilities.scalarFragment types = .ok ())
    (normal : fields.mapM (Native.normalize aliases) = .ok normalized)
    (requirements : ∀ item ∈ normalized, Requirements hash inputs item) :
    (GenericStateOps.evalFields ctx env fields).map (List.map some) =
      .ok (normalized.map (fun item => interpret hash inputs item.term)) := by
  induction fields generalizing normalized with
  | nil =>
    cases normal
    rfl
  | cons field rest ih =>
    simp only [List.mapM_cons, bind_ok] at normal
    obtain ⟨head, headNormal, tail, tailNormal, exactList⟩ := normal
    cases exactList
    obtain ⟨value, evaluated, represented⟩ := normalize_sound ctx hash implementation inputs
      types aliases env typed field (admitted field (by simp)) head (valid field (by simp))
      headNormal (requirements head (by simp))
    have tailFields := ih tail
      (fun field member => admitted field (List.mem_cons_of_mem _ member))
      (fun field member => valid field (List.mem_cons_of_mem _ member))
      tailNormal (fun item member => requirements item (List.mem_cons_of_mem _ member))
    have headValue : interpret hash inputs head.term = some (scalar value) := represented.2.2
    simp only [GenericStateOps.evalFields, List.mapM_cons]
    change (do
      let first ← scalar <$> field.eval ctx env
      let tailValues ← GenericStateOps.evalFields ctx env rest
      pure (first :: tailValues)).map (List.map some) = _
    cases tailResult : GenericStateOps.evalFields ctx env rest with
    | error error => simp [tailResult, Except.map] at tailFields
    | ok tailValues =>
      simp only [tailResult, Except.map, Except.ok.injEq] at tailFields
      simp [evaluated, headValue, ← tailFields, Bind.bind, Except.bind,
        Except.map, Functor.map, Pure.pure, Except.pure]

private theorem collectOperation_scalar_fields
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (witness : Assignment) (aliases : Native.AliasEnvironment) (env : EvalEnv) (types : TypeEnv)
    (typed : TypedEnvironment hash witness aliases env types) (span : SourceSpan)
    (operation : Impact.Op)
    (groups : List (List Native.Term)) (bounds : List (Native.Term × Nat)) (assertions : List Native.Term)
    (supported : GenericStateOps.ScalarOperation operation)
    (expressions : ∀ field ∈ operation.fields, ScalarExpression field)
    (valid : ∀ field ∈ operation.fields, field.validate Capabilities.scalarFragment types = .ok ())
    (boundsChecked : ∀ requirement ∈ bounds,
      ∃ value, interpret hash witness requirement.1 = some value ∧ value.val ≤ requirement.2)
    (assertionsChecked : ∀ assertion ∈ assertions, interpret hash witness assertion = some one)
    (collected : Native.collectOperation span aliases operation = .ok (groups, bounds, assertions)) :
    ∃ fields, GenericStateOps.evalFields ctx env operation.fields = .ok fields ∧
      groups.map (List.map (interpret hash witness)) = [fields.map some] := by
  unfold Native.collectOperation at collected
  rw [fieldGroups_eq_singleton supported] at collected
  simp only [List.mapM_cons, List.mapM_nil, bind_ok, Pure.pure, Except.pure,
    Except.ok.injEq] at collected
  obtain ⟨_, ⟨first, head, _, rfl, rfl⟩, result⟩ := collected
  have exact := (Native.convert_ok span _ first).mp head
  rw [Native.collect_eq] at exact
  simp only [bind_ok, Pure.pure, Except.pure, Except.ok.injEq] at exact
  obtain ⟨normalized, normal, exactFirst⟩ := exact
  subst first
  cases result
  have requirements : ∀ item ∈ normalized, Requirements hash witness item := by
    intro item member
    constructor
    · intro bound present
      apply boundsChecked bound
      simp only [List.flatMap_singleton, List.mem_flatMap]
      exact ⟨item, member, present⟩
    · intro term present
      apply assertionsChecked term
      simp only [List.flatMap_singleton, List.mem_flatMap]
      exact ⟨item, member, present⟩
  have semantic := normalized_fields ctx hash implementation witness aliases env types typed
    operation.fields normalized expressions valid normal requirements
  cases evaluated : GenericStateOps.evalFields ctx env operation.fields with
  | error error => simp [evaluated, Except.map] at semantic
  | ok fields =>
    simp only [evaluated, Except.map, Except.ok.injEq] at semantic
    refine ⟨fields, rfl, ?_⟩
    simpa only [List.map_cons, List.map_nil, List.map_map, Function.comp_def] using
      congrArg (fun group : List (Option Scalar) => [group]) semantic.symm

private theorem collected_operation_payloads
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (witness : Assignment) (aliases : Native.AliasEnvironment) (env : EvalEnv) (types : TypeEnv)
    (typed : TypedEnvironment hash witness aliases env types) (span : SourceSpan)
    (operations : List Impact.Op)
    (pieces : List (List (List Native.Term) × List (Native.Term × Nat) × List Native.Term))
    (supported : ∀ operation ∈ operations, GenericStateOps.ScalarOperation operation)
    (expressions : ∀ operation ∈ operations, ∀ field ∈ operation.fields, ScalarExpression field)
    (valid : ∀ operation ∈ operations, ∀ field ∈ operation.fields,
      field.validate Capabilities.scalarFragment types = .ok ())
    (bounds : ∀ requirement ∈ pieces.flatMap (·.2.1),
      ∃ value, interpret hash witness requirement.1 = some value ∧ value.val ≤ requirement.2)
    (assertions : ∀ assertion ∈ pieces.flatMap (·.2.2),
      interpret hash witness assertion = some one)
    (collected : operations.mapM (Native.collectOperation span aliases) = .ok pieces) :
    ∃ fields, operations.mapM (fun operation =>
        GenericStateOps.evalFields ctx env operation.fields) = .ok fields ∧
      (pieces.flatMap (·.1)).map (List.map (interpret hash witness)) =
        fields.map (List.map some) := by
  induction operations generalizing pieces with
  | nil =>
    cases collected
    exact ⟨[], rfl, rfl⟩
  | cons operation rest ih =>
    simp only [List.mapM_cons, bind_ok] at collected
    obtain ⟨⟨groups, firstBounds, firstAssertions⟩, firstCollected, remaining, restCollected,
      collection⟩ := collected
    cases collection
    obtain ⟨first, firstEvaluated, firstExact⟩ := collectOperation_scalar_fields
      ctx hash implementation witness aliases env types typed span operation
      groups firstBounds firstAssertions
      (supported operation (by simp)) (expressions operation (by simp)) (valid operation (by simp))
      (fun bound member => bounds bound (by simp [member]))
      (fun term member => assertions term (by simp [member])) firstCollected
    obtain ⟨tail, restEvaluated, restExact⟩ := ih remaining
      (fun op member => supported op (List.mem_cons_of_mem _ member))
      (fun op member => expressions op (List.mem_cons_of_mem _ member))
      (fun op member => valid op (List.mem_cons_of_mem _ member))
      (fun bound member => bounds bound (by simp [member]))
      (fun term member => assertions term (by simp [member])) restCollected
    refine ⟨first :: tail, ?_, ?_⟩
    · simp only [List.mapM_cons, firstEvaluated, restEvaluated]
      rfl
    · simp only [List.flatMap_cons, List.map_append, List.map_cons]
      rw [firstExact, restExact]
      rfl

/-- For an admitted lowered plan, the producer's exact fields determine an
ordered scalar VM schedule. Typed field collection alone cannot admit opcodes. -/
theorem collectPlan_scalar_schedule
    (state : List StateDecl) (entry : Entrypoint) (plan : Impact.Plan)
    (lowered : Impact.lower state entry = .ok plan)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (witness : Assignment) (aliases : Native.AliasEnvironment) (env : EvalEnv)
    (typed : TypedEnvironment hash witness aliases env (plan.typeEnvironment entry))
    (initialBounds : List (Native.Term × Nat)) (groups : List (List Native.Term))
    (bounds : List (Native.Term × Nat)) (assertions : List Native.Term)
    (supported : ∀ operation ∈ plan.operations, GenericStateOps.ScalarOperation operation)
    (expressions : ∀ operation ∈ plan.operations, ∀ field ∈ operation.fields, ScalarExpression field)
    (boundsChecked : ∀ requirement ∈ bounds,
      ∃ value, interpret hash witness requirement.1 = some value ∧ value.val ≤ requirement.2)
    (assertionsChecked : ∀ assertion ∈ assertions, interpret hash witness assertion = some one)
    (collected : Native.collectOperations entry.span aliases plan.operations initialBounds =
      .ok (groups, bounds, assertions)) :
    ∃ native, GenericStateOps.evalPlan ctx env plan = .ok native ∧
      groups.map (List.map (interpret hash witness)) =
        (NativeState.groups native).map (List.map some) := by
  unfold Native.collectOperations at collected
  simp only [bind_ok] at collected
  obtain ⟨pieces, pieceCollection, exactShape⟩ := collected
  cases exactShape
  have validated := plan.validate_fields_success entry
    (Impact.lower_validated state entry plan lowered)
  obtain ⟨fields, fieldEval, payloads⟩ := collected_operation_payloads
    ctx hash implementation witness aliases env (plan.typeEnvironment entry) typed
    entry.span plan.operations pieces supported expressions
    (fun operation member field present => validated field
      (List.mem_flatMap.mpr ⟨operation, member, present⟩))
    (fun bound member => boundsChecked bound (List.mem_append_right _ member))
    assertionsChecked pieceCollection
  have exactSchedule := GenericStateAdmissionBridge.lower_evaluated_plan_groups_exact
    state entry plan ctx env lowered implementation.modulus supported
  rw [fieldEval] at exactSchedule
  cases evaluation : GenericStateOps.evalPlan ctx env plan with
  | error message => simp [evaluation, Except.map] at exactSchedule
  | ok native =>
    simp only [evaluation, Except.map, Except.ok.injEq] at exactSchedule
    exact ⟨native, rfl, by rw [payloads, exactSchedule]⟩

end Noctium.Verification.ScalarImpactOperationMeaning
