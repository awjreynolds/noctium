import Noctium.Verification.GenericStateOps
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

/-- Fields collected by the producer for one scalar operation agree with
the fields evaluated by the checked scalar VM. -/
theorem collectOperation_scalar_fields
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (witness : Assignment) (aliases : Native.AliasEnvironment) (env : EvalEnv) (types : TypeEnv)
    (typed : TypedEnvironment hash witness aliases env types) (span : SourceSpan)
    (operation : Impact.Op) (native : NativeState.Op)
    (groups : List (List Native.Term)) (bounds : List (Native.Term × Nat)) (assertions : List Native.Term)
    (admitted : GenericStateOps.FieldAdmitted operation)
    (expressions : ∀ field ∈ operation.fields, ScalarExpression field)
    (valid : ∀ field ∈ operation.fields, field.validate Capabilities.scalarFragment types = .ok ())
    (boundsChecked : ∀ requirement ∈ bounds,
      ∃ value, interpret hash witness requirement.1 = some value ∧ value.val ≤ requirement.2)
    (assertionsChecked : ∀ assertion ∈ assertions, interpret hash witness assertion = some one)
    (collected : Native.collectOperation span aliases operation = .ok (groups, bounds, assertions))
    (evaluated : GenericStateOps.evalOp ctx env operation = .ok native) :
    groups.map (List.map (interpret hash witness)) = [native.fields.map some] := by
  have supported := GenericStateOps.evalOp_supported ctx env operation native evaluated
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
  rw [GenericStateOps.evalOp_fields ctx env operation native implementation.modulus admitted
    evaluated] at semantic
  simp only [Except.map, Except.ok.injEq] at semantic
  simpa only [List.map_cons, List.map_nil, List.map_map, Function.comp_def] using
    congrArg (fun group : List (Option Scalar) => [group]) semantic.symm

private theorem collected_operation_payloads
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (witness : Assignment) (aliases : Native.AliasEnvironment) (env : EvalEnv) (types : TypeEnv)
    (typed : TypedEnvironment hash witness aliases env types) (span : SourceSpan)
    (operations : List Impact.Op) (native : List NativeState.Op)
    (pieces : List (List (List Native.Term) × List (Native.Term × Nat) × List Native.Term))
    (admitted : ∀ operation ∈ operations, GenericStateOps.FieldAdmitted operation)
    (expressions : ∀ operation ∈ operations, ∀ field ∈ operation.fields, ScalarExpression field)
    (valid : ∀ operation ∈ operations, ∀ field ∈ operation.fields,
      field.validate Capabilities.scalarFragment types = .ok ())
    (bounds : ∀ requirement ∈ pieces.flatMap (·.2.1),
      ∃ value, interpret hash witness requirement.1 = some value ∧ value.val ≤ requirement.2)
    (assertions : ∀ assertion ∈ pieces.flatMap (·.2.2),
      interpret hash witness assertion = some one)
    (collected : operations.mapM (Native.collectOperation span aliases) = .ok pieces)
    (evaluated : operations.mapM (GenericStateOps.evalOp ctx env) = .ok native) :
    (pieces.flatMap (·.1)).map (List.map (interpret hash witness)) =
      (NativeState.groups native).map (List.map some) := by
  induction operations generalizing native pieces with
  | nil =>
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at collected evaluated
    subst pieces native
    rfl
  | cons operation rest ih =>
    simp only [List.mapM_cons, bind_ok] at collected evaluated
    obtain ⟨⟨groups, firstBounds, firstAssertions⟩, firstCollected, remaining, restCollected,
      collection⟩ := collected
    obtain ⟨step, firstEvaluated, tail, restEvaluated, evaluation⟩ := evaluated
    cases collection
    cases evaluation
    have first := collectOperation_scalar_fields
      ctx hash implementation witness aliases env types typed span operation step
      groups firstBounds firstAssertions
      (admitted operation (by simp)) (expressions operation (by simp)) (valid operation (by simp))
      (fun bound member => bounds bound (by simp [member]))
      (fun term member => assertions term (by simp [member]))
      firstCollected firstEvaluated
    have next := ih tail remaining
      (fun op member => admitted op (List.mem_cons_of_mem _ member))
      (fun op member => expressions op (List.mem_cons_of_mem _ member))
      (fun op member => valid op (List.mem_cons_of_mem _ member))
      (fun bound member => bounds bound (by simp [member]))
      (fun term member => assertions term (by simp [member]))
      restCollected restEvaluated
    simp only [List.flatMap_cons, List.map_append, NativeState.groups, List.map_cons] at *
    rw [first, next]
    rfl

/-- The production operation collector preserves the exact public field
groups of successfully evaluated scalar operations in list order. -/
theorem collectOperations_scalar_fields
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (witness : Assignment) (aliases : Native.AliasEnvironment) (env : EvalEnv) (types : TypeEnv)
    (typed : TypedEnvironment hash witness aliases env types) (span : SourceSpan)
    (operations : List Impact.Op) (native : List NativeState.Op)
    (initialBounds : List (Native.Term × Nat)) (groups : List (List Native.Term))
    (bounds : List (Native.Term × Nat)) (assertions : List Native.Term)
    (admitted : ∀ operation ∈ operations, GenericStateOps.FieldAdmitted operation)
    (expressions : ∀ operation ∈ operations, ∀ field ∈ operation.fields, ScalarExpression field)
    (valid : ∀ operation ∈ operations, ∀ field ∈ operation.fields,
      field.validate Capabilities.scalarFragment types = .ok ())
    (boundsChecked : ∀ requirement ∈ bounds,
      ∃ value, interpret hash witness requirement.1 = some value ∧ value.val ≤ requirement.2)
    (assertionsChecked : ∀ assertion ∈ assertions, interpret hash witness assertion = some one)
    (collected : Native.collectOperations span aliases operations initialBounds =
      .ok (groups, bounds, assertions))
    (evaluated : operations.mapM (GenericStateOps.evalOp ctx env) = .ok native) :
    groups.map (List.map (interpret hash witness)) =
      (NativeState.groups native).map (List.map some) := by
  unfold Native.collectOperations at collected
  simp only [bind_ok] at collected
  obtain ⟨pieces, pieceCollection, exactShape⟩ := collected
  cases exactShape
  exact collected_operation_payloads ctx hash implementation witness aliases env types typed
    span operations native pieces admitted expressions valid
    (fun bound member => boundsChecked bound (List.mem_append_right _ member))
    assertionsChecked pieceCollection evaluated

end Noctium.Verification.ScalarImpactOperationMeaning
