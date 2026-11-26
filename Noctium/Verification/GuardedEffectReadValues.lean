import Noctium.Verification.GuardedPlanExecution
import Noctium.Verification.NativeStateReadTape
import Noctium.Verification.ScalarRequireOperationAdmission
import Noctium.Verification.GuardedPlanAssertions
import Noctium.Verification.GenericStateAbsenceAuthentication
import Noctium.Verification.GenericStateCellAdmission
import Noctium.Verification.GenericStateMapOperations
import Noctium.Verification.GenericStateMapReadEvaluation
import Noctium.Verification.GenericStateReadCellEvaluation
import Noctium.Verification.GenericStateWriteEvaluation
import Noctium.Verification.GuardedEffectPrefix
import Noctium.Verification.GuardedVmReadObservations
import Noctium.Verification.ScalarGuardedPlanAdmission

namespace Noctium.Verification.GuardedEffectReadValues

open Backend NativeRelation ScalarNormalization
open GenericStateCellAdmission GenericStateCheckedReadTrace GenericStateEncoding
open GenericStateOps GuardedPlanExecution GuardedPlanAssertions GuardedVmReadObservations
open GenericStateReadCellEvaluation GenericStateMapReadEvaluation GenericStateWriteEvaluation
open NativeStateReadTape ScalarGuardedPlanAdmission GuardedScalarInput

private def popeqAlignment : Impact.Op → Option Impact.Aligned
  | .popeq alignment => some alignment
  | _ => none

private theorem except_bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem evalOp_readAlignment (ctx : EvalContext) (values : EvalEnv)
    (operation : Impact.Op) (native : NativeState.Op)
    (evaluated : evalOp ctx values operation = .ok native) :
    ((popeqAlignment operation).toList.mapM (evalAligned ctx values)) =
      .ok (NativeStateReadTape.expectedCells [native]) := by
  cases operation <;>
    simp only [evalOp, Pure.pure, Except.pure] at evaluated
  all_goals try
    { obtain rfl := Except.ok.inj evaluated
      rfl }
  all_goals try
    { cases evaluated }
  case mapIndex slot key =>
    cases key
    case field expression =>
      obtain ⟨cell, cellEval, shape⟩ := except_bind_ok.mp evaluated
      obtain rfl := Except.ok.inj shape
      rfl
    all_goals cases evaluated
  case push alignment storage =>
    obtain ⟨cell, cellEval, shape⟩ := except_bind_ok.mp evaluated
    obtain rfl := Except.ok.inj shape
    rfl
  case popeq alignment =>
    obtain ⟨cell, cellEval, shape⟩ := except_bind_ok.mp evaluated
    obtain rfl := Except.ok.inj shape
    simp [popeqAlignment, cellEval, NativeStateReadTape.expectedCells, Pure.pure,
      Except.pure, Bind.bind, Except.bind]

/-- Evaluation preserves the relative order of symbolic popeq alignments. -/
private theorem evalOps_readAlignments (ctx : EvalContext) (values : EvalEnv)
    (operations : List Impact.Op) (native : List NativeState.Op)
    (evaluated : operations.mapM (evalOp ctx values) = .ok native) :
    ((operations.filterMap popeqAlignment).mapM (evalAligned ctx values)) =
      .ok (NativeStateReadTape.expectedCells native) := by
  induction operations generalizing native with
  | nil =>
    cases evaluated
    rfl
  | cons op rest ih =>
    simp only [List.mapM_cons, except_bind_ok] at evaluated
    obtain ⟨active, headEval, tail, tailEval, same⟩ := evaluated
    cases same
    have head := evalOp_readAlignment ctx values op active headEval
    have tailRead := ih tail tailEval
    rw [show (op :: rest).filterMap popeqAlignment =
        (popeqAlignment op).toList ++ rest.filterMap popeqAlignment by
      cases h : popeqAlignment op <;> simp [h],
      List.mapM_append, head, tailRead]
    cases active <;> rfl

/-- One active chunk comparison supplies the single observed read. -/
private theorem singleton_chunk_reads
    (ctx : EvalContext) (assignment : Assignment) (values : EvalEnv)
    (guard : Option (Expr .bool)) (chunk : List Impact.Op)
    (descriptor : Impact.Read) (descriptorGuard : descriptor.guard = guard)
    (activity : Option Bool) (native : List NativeState.Op)
    (evaluated : evalChunk ctx values guard chunk = .ok (activity, native))
    (alignment : Impact.Aligned)
    (comparison : chunk.filterMap popeqAlignment = [alignment])
    (alignmentValue : evalAligned ctx values alignment =
      .ok (NativeState.field (assignment ("%input_" ++ descriptor.name)))) :
    ∃ observations,
      evaluateReadObservations ctx assignment values [descriptor] = .ok observations ∧
      (NativeStateReadTape.expectedCells native).map NativeState.Cell.value =
        activeReadValues observations := by
  obtain ⟨evaluatedGuard, operations⟩ :=
    evalChunk_success ctx values guard chunk activity native evaluated
  refine ⟨[⟨bit (activity.getD true), assignment ("%input_" ++ descriptor.name)⟩], ?_, ?_⟩
  · simp [evaluateReadObservations, evaluateReadObservation, descriptorGuard,
      evaluatedGuard, Pure.pure, Except.pure, Bind.bind, Except.bind]
  · cases active : activity.getD true with
    | false =>
      simp only [active, Bool.false_eq_true, ite_false] at operations
      obtain rfl := (Except.ok.inj operations).symm
      simp [NativeStateReadTape.expectedCells, activeReadValues, bit, zero_ne_one]
    | true =>
      simp only [active, ite_true] at operations
      have tape := evalOps_readAlignments ctx values chunk native operations
      rw [comparison] at tape
      simp only [List.mapM_cons, List.mapM_nil, alignmentValue, Pure.pure,
        Except.pure, Bind.bind, Except.bind] at tape
      rw [← Except.ok.inj tape]
      simp [activeReadValues, NativeState.field, bit]

private theorem no_read_chunk_of_comparisons
    (ctx : EvalContext) (assignment : Assignment) (values : EvalEnv)
    (guard : Option (Expr .bool)) (chunk : List Impact.Op)
    (activity : Option Bool) (native : List NativeState.Op)
    (evaluated : evalChunk ctx values guard chunk = .ok (activity, native))
    (comparison : chunk.filterMap popeqAlignment = []) :
    ∃ observations,
      evaluateReadObservations ctx assignment values [] = .ok observations ∧
      (NativeStateReadTape.expectedCells native).map NativeState.Cell.value =
        activeReadValues observations := by
  obtain ⟨_, operations⟩ := evalChunk_success ctx values guard chunk activity native evaluated
  refine ⟨[], rfl, ?_⟩
  cases active : activity.getD true with
  | false =>
    simp only [active, Bool.false_eq_true, ite_false] at operations
    obtain rfl := (Except.ok.inj operations).symm
    rfl
  | true =>
    simp only [active, ite_true] at operations
    have tape := evalOps_readAlignments ctx values chunk native operations
    rw [comparison] at tape
    change Except.ok [] = Except.ok (NativeStateReadTape.expectedCells native) at tape
    rw [← Except.ok.inj tape]
    rfl

private theorem appendEffect_readCell_empty_base
    (state : List StateDecl) (name destination : String) (ty : Ty)
    (before raw : Impact.Plan)
    (compiled : Impact.appendEffect state (.readCell name destination ty) before = .ok raw) :
    ∃ base, Impact.appendEffect state (.readCell name destination ty) {} = .ok base ∧
      raw.operations = before.operations ++ base.operations := by
  simp only [Impact.appendEffect, except_bind_ok] at compiled
  obtain ⟨slot, slotAccepted, value, valueAccepted, finished⟩ := compiled
  let base : Impact.Plan :=
    {raw with
      operations := raw.operations.drop before.operations.length,
      activityGuards := [],
      reads := raw.reads.drop before.reads.length,
      guards := []}
  have rawShape := Except.ok.inj finished
  refine ⟨base, ?_, ?_⟩
  · simp only [Impact.appendEffect, except_bind_ok]
    refine ⟨slot, slotAccepted, value, valueAccepted, ?_⟩
    simp [base, ← rawShape, Pure.pure, Except.pure]
  · rw [← rawShape]
    simp [base, ← rawShape]

private theorem readCell_base
    (state : List StateDecl) (name destination : String) (ty : Ty)
    (guard : Option (Expr .bool)) (before next : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state
      (.readCell name destination ty) guard before = .ok next) :
    ∃ base, Impact.appendEffect state (.readCell name destination ty) {} = .ok base ∧
      next.operations = before.operations ++ base.operations := by
  cases guard with
  | none =>
    exact GuardedEffectPrefix.appendEffectWithActivity_unguarded_readCell_chunk
      state name destination ty before next accepted
  | some condition =>
    have originalAccepted := accepted
    unfold Impact.appendEffectWithActivity at accepted
    simp only [except_bind_ok] at accepted
    obtain ⟨lowered, loweredEq, raw, rawAccepted, _⟩ := accepted
    have effectEq : lowered = Effect.readCell name destination ty :=
      (Except.ok.inj loweredEq).symm
    subst lowered
    obtain ⟨base, baseAccepted, baseOperations⟩ := appendEffect_readCell_empty_base
      state name destination ty before raw rawAccepted
    obtain ⟨operations, _⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_readCell_empty_chunk
        state name destination ty condition before next base originalAccepted baseAccepted
    exact ⟨base, baseAccepted, operations⟩

private def scalarTypeOfCell : {ty : Ty} → ScalarCellType ty → ScalarType ty
  | _, .native => .native
  | _, .bool => .bool
  | _, .uint maximum _ => .uint maximum

private theorem readMap_raw
    (state : List StateDecl) (name destination : String)
    (keyTy valueTy : Ty) (key : Expr keyTy)
    (guard : Option (Expr .bool)) (before next : Impact.Plan)
    (keySupport : ScalarCellType keyTy) (keyAdmission : ScalarExpression key)
    (accepted : Impact.appendEffectWithActivity state
      (.readMap name destination keyTy valueTy key) guard before = .ok next) :
    ∃ emittedKey raw,
      Impact.appendEffect state (.readMap name destination keyTy valueTy emittedKey)
        before = .ok raw ∧ next.operations = raw.operations := by
  cases guard with
  | none =>
    obtain ⟨raw, appended, operations, _⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_none_result
        state (.readMap name destination keyTy valueTy key) before next accepted
    exact ⟨key, raw, appended, operations⟩
  | some condition =>
    have nonForeign : ∀ kind, keyTy ≠ .foreign kind := by
      intro kind same
      subst keyTy
      cases keySupport
    obtain ⟨binder, fresh, raw, appended, operations⟩ :=
      Impact.appendEffectWithActivity_readMap_key state name destination keyTy valueTy key
        condition before next nonForeign accepted
    let emittedKey := Expr.letE binder condition
      (Noctium.GuardedExpression.totalize (.ref binder) key)
    exact ⟨emittedKey, raw, by simpa [emittedKey] using appended, operations⟩

/-- The actual active Cell chunk compares the candidate's canonical typed value. -/
private theorem read_cell_alignment
    (ctx : EvalContext) (values : EvalEnv) (assignment : Assignment)
    (state : List StateDecl) (name destination : String) (ty : Ty)
    (guard : Option (Expr .bool)) (before next : Impact.Plan)
    (chunk : List Impact.Op) (cellSupport : ScalarCellType ty)
    (declaration : ScalarCellDeclaration state name ty)
    (accepted : Impact.appendEffectWithActivity state
      (.readCell name destination ty) guard before = .ok next)
    (operationSuffix : next.operations = before.operations ++ chunk)
    (value : ty.Denote) (lookup : values.lookup destination = some (Value.pack ty value))
    (canonical : Canonical ty value) (modulus : ctx.modulus = Field.modulus)
    (meaning : sourceScalar? ty value = some (assignment ("%input_" ++ destination))) :
    ∃ alignment, chunk.filterMap popeqAlignment = [alignment] ∧
      evalAligned ctx values alignment =
        .ok (NativeState.field (assignment ("%input_" ++ destination))) := by
  obtain ⟨base, baseAccepted, baseOperations⟩ := readCell_base
    state name destination ty guard before next accepted
  have chunkEq : chunk = base.operations :=
    List.append_cancel_left (operationSuffix.symm.trans baseOperations)
  subst chunk
  obtain ⟨_, symbolicOperations, _⟩ :=
    GenericStateCellAdmission.append_read_cell_scalar_supported
      state {} base name destination ty cellSupport declaration baseAccepted (by simp)
  let alignment : Impact.Aligned :=
    .field (GenericStateCellAdmission.scalarCellReadExpression cellSupport destination)
  refine ⟨alignment, ?_, ?_⟩
  · rw [symbolicOperations]
    simp [alignment, popeqAlignment, List.filterMap]
  · have expressionEval := GenericStateReadCellEvaluation.readExpression_eval ctx values
      destination ty value cellSupport lookup modulus canonical
    have sameExpression : GenericStateCellAdmission.scalarCellReadExpression
        cellSupport destination =
      GenericStateReadCellEvaluation.readExpression cellSupport destination := by
      cases cellSupport <;> rfl
    have assignmentValue :
        assignment ("%input_" ++ destination) = scalar (GenericStateEncoding.number ty value) := by
      obtain ⟨support⟩ := GenericStateWriteEvaluation.scalarType_of_canonical canonical
      exact Option.some.inj
        (meaning.symm.trans (GenericStateEncoding.sourceScalar_eq_field support value))
    dsimp only [alignment]
    rw [sameExpression]
    simp [GenericStateOps.evalAligned, expressionEval, assignmentValue,
      Except.map, Functor.map]

/-- The actual active Map chunk compares the typed candidate's scalar value.
The key remains the expression accepted by guarded production lowering. -/
private theorem read_map_alignment
    (ctx : EvalContext) (values : EvalEnv) (assignment : Assignment)
    (state : List StateDecl) (name destination : String)
    (keyTy valueTy : Ty) (key : Expr keyTy)
    (guard : Option (Expr .bool)) (before next : Impact.Plan)
    (chunk : List Impact.Op) (keySupport : ScalarCellType keyTy)
    (keyAdmission : ScalarExpression key)
    (accepted : Impact.appendEffectWithActivity state
      (.readMap name destination keyTy valueTy key) guard before = .ok next)
    (operationSuffix : next.operations = before.operations ++ chunk)
    (value : valueTy.Denote)
    (lookup : values.lookup destination = some (Value.pack valueTy value))
    (canonical : Canonical valueTy value) (modulus : ctx.modulus = Field.modulus)
    (meaning : sourceScalar? valueTy value = some (assignment ("%input_" ++ destination))) :
    ∃ alignment, chunk.filterMap popeqAlignment = [alignment] ∧
      evalAligned ctx values alignment =
        .ok (NativeState.field (assignment ("%input_" ++ destination))) := by
  obtain ⟨emittedKey, raw, rawAccepted, sameOperations⟩ :=
    readMap_raw state name destination keyTy valueTy key guard before next keySupport
      keyAdmission accepted
  have chunkEq : chunk = raw.operations.drop before.operations.length := by
    have same := operationSuffix.symm.trans sameOperations
    simpa using congrArg (fun operations => operations.drop before.operations.length) same
  obtain ⟨slot, _, operationsShape, _⟩ := GenericStateMapReadEvaluation.readMap_scalar_chunk
    state name destination keyTy valueTy emittedKey before raw (scalarTypeOfCell keySupport)
    (GenericStateReadCellEvaluation.scalarCellTypeOfCanonical canonical) rawAccepted
  have suffixShape : raw.operations.drop before.operations.length =
      [.dup, .mapIndex slot (.field (GenericStateWriteEvaluation.scalarProjection
        (scalarTypeOfCell keySupport) emittedKey)), .popeq (.field
        (GenericStateReadCellEvaluation.readExpression
          (GenericStateReadCellEvaluation.scalarCellTypeOfCanonical canonical) destination))] := by
    rw [operationsShape]
    simp
  let alignment : Impact.Aligned := .field (GenericStateReadCellEvaluation.readExpression
    (GenericStateReadCellEvaluation.scalarCellTypeOfCanonical canonical) destination)
  refine ⟨alignment, ?_, ?_⟩
  · rw [chunkEq, suffixShape]
    simp [alignment, popeqAlignment, List.filterMap]
  · have expressionEval := GenericStateReadCellEvaluation.readExpression_eval ctx values
      destination valueTy value
      (GenericStateReadCellEvaluation.scalarCellTypeOfCanonical canonical)
      lookup modulus canonical
    have assignmentValue :
        assignment ("%input_" ++ destination) = scalar (GenericStateEncoding.number valueTy value) := by
      obtain ⟨support⟩ := GenericStateWriteEvaluation.scalarType_of_canonical canonical
      exact Option.some.inj
        (meaning.symm.trans (GenericStateEncoding.sourceScalar_eq_field support value))
    simp [alignment, GenericStateOps.evalAligned, expressionEval, assignmentValue,
      Except.map, Functor.map]

private theorem require_has_no_operations (state : List StateDecl)
    (condition : Expr .bool) (guard : Option (Expr .bool))
    (before after : Impact.Plan) (chunk : List Impact.Op)
    (accepted : Impact.appendEffectWithActivity state (.require condition) guard before = .ok after)
    (operations : after.operations = before.operations ++ chunk) :
    chunk = [] := by
  have unchanged : after.operations = before.operations := by
    cases guard with
    | none =>
      obtain ⟨raw, wrapped, same, _⟩ := GuardedEffectPrefix.appendEffectWithActivity_none_result
        state (.require condition) before after accepted
      simp only [Impact.appendEffect, Pure.pure, Except.pure] at wrapped
      obtain rfl := Except.ok.inj wrapped
      exact same
    | some gate =>
      rw [Impact.appendEffectWithActivity_require] at accepted
      simp only [Impact.appendEffect, Pure.pure, Except.pure] at accepted
      obtain rfl := Except.ok.inj accepted
      rfl
  apply List.append_cancel_left (as := before.operations)
  simpa only [List.append_nil] using operations.symm.trans unchanged

private theorem absence_descriptor_assignment_zero (ctx : EvalContext)
    (assignment : Assignment) (values : EvalEnv)
    (name : String) (keyTy : Ty) (key : Expr keyTy) (ordinal : Nat)
    (descriptor : Impact.Read)
    (descriptorName : descriptor.name = "_noctium_absence_" ++ toString ordinal)
    (descriptorType : descriptor.ty = .bool)
    (bound : ∃ value : descriptor.ty.Denote,
      values.lookup descriptor.name = some (Value.pack descriptor.ty value) ∧
      Canonical descriptor.ty value ∧
      sourceScalar? descriptor.ty value = some (assignment ("%input_" ++ descriptor.name)))
    (assertions : ∀ expression ∈ guardedEffectAssertionChunk none (.requireAbsent name keyTy key)
      ordinal, expression.eval ctx values = .ok _root_.Bool.true) :
    assignment ("%input_" ++ descriptor.name) = zero := by
  have asserted : (Expr.eq (.ref descriptor.name : Expr .bool) (.bool false)).eval
      ctx values = .ok _root_.Bool.true := by
    apply assertions
    rw [descriptorName]
    exact List.mem_cons_self
  cases descriptor with
  | mk destination ty components guard =>
    dsimp at descriptorType bound ⊢
    subst ty
    obtain ⟨value, lookup, _, scalarValue⟩ := bound
    have valueFalse := GenericStateAbsenceAuthentication.absence_guard_candidate_false ctx values
      destination value lookup asserted
    subst value
    exact (Option.some.inj scalarValue).symm

private theorem absence_chunk_reads (ctx : EvalContext) (assignment : Assignment)
    (values : EvalEnv) (state : List StateDecl)
    (name : String) (keyTy : Ty) (key : Expr keyTy) (keyScalar : ScalarCellType keyTy)
    (before after : Impact.Plan) (chunk : List Impact.Op) (descriptor : Impact.Read)
    (descriptorName : descriptor.name = "_noctium_absence_" ++ toString before.reads.length)
    (descriptorType : descriptor.ty = .bool) (descriptorGuard : descriptor.guard = none)
    (bound : ∃ value : descriptor.ty.Denote,
      values.lookup descriptor.name = some (Value.pack descriptor.ty value) ∧
      Canonical descriptor.ty value ∧
      sourceScalar? descriptor.ty value = some (assignment ("%input_" ++ descriptor.name)))
    (assertions : ∀ expression ∈ guardedEffectAssertionChunk none (.requireAbsent name keyTy key)
      before.reads.length, expression.eval ctx values = .ok _root_.Bool.true)
    (accepted : Impact.appendEffectWithActivity state (.requireAbsent name keyTy key)
      none before = .ok after)
    (operations : after.operations = before.operations ++ chunk)
    (native : List NativeState.Op) (activity : Option _root_.Bool)
    (evaluated : evalChunk ctx values none chunk = .ok (activity, native)) :
    ∃ observations, evaluateReadObservations ctx assignment values [descriptor] = .ok observations ∧
      (NativeStateReadTape.expectedCells native).map NativeState.Cell.value =
        activeReadValues observations := by
  obtain ⟨slot, absenceShape⟩ :=
    ScalarRequireOperationAdmission.append_require_absent_operation_suffix state before after
      name keyTy key keyScalar accepted
  have chunkShape := List.append_cancel_left (operations.symm.trans absenceShape)
  have operationEval : (chunk.mapM (evalOp ctx values)).map (fun ops => (none, ops)) =
      .ok (activity, native) := by simpa [evalChunk, Pure.pure, Except.pure] using evaluated
  cases computed : chunk.mapM (evalOp ctx values) with
  | error reason => simp [computed, Except.map] at operationEval
  | ok actual =>
    have matched : (none, actual) = (activity, native) := by
      simpa [computed, Except.map] using operationEval
    cases matched
    have cells := evalOps_readAlignments ctx values chunk native computed
    rw [chunkShape] at cells
    change Except.ok [NativeState.boolean false] =
      Except.ok (NativeStateReadTape.expectedCells native) at cells
    have tape := (Except.ok.inj cells).symm
    have zeroValue := absence_descriptor_assignment_zero ctx assignment values name keyTy key
      before.reads.length descriptor descriptorName descriptorType bound assertions
    refine ⟨[⟨one, zero⟩], ?_, ?_⟩
    · simp [evaluateReadObservations, evaluateReadObservation, descriptorGuard, zeroValue, bit,
        Pure.pure, Bind.bind, Except.bind, Except.pure]
    · rw [tape]
      simp [activeReadValues, NativeState.boolean, bit]


private theorem singleton_descriptor
    (descriptors : List Impact.Read) (name : String) (ty : Ty)
    (metadata : descriptors.map readMetadata = [(name, ty)]) :
    ∃ descriptor, descriptors = [descriptor] ∧ descriptor.name = name ∧ descriptor.ty = ty := by
  cases descriptors with
  | nil => simp at metadata
  | cons descriptor rest =>
    cases rest with
    | nil =>
      obtain ⟨destination, valueTy⟩ := Prod.mk.inj (List.cons.inj metadata).1
      exact ⟨descriptor, rfl, destination, valueTy⟩
    | cons next tail => simp at metadata

private theorem empty_descriptors (descriptors : List Impact.Read)
    (metadata : descriptors.map readMetadata = []) :
    descriptors = [] := by
  cases descriptors <;> simp_all

/-- The accepted scalar Cell write appends no read comparisons. -/
private theorem accepted_writeCell_chunk_no_popeq
    (state : List StateDecl) (name : String) (ty : Ty) (value : Expr ty)
    (guard : Option (Expr .bool)) (before after : Impact.Plan)
    (chunk : List Impact.Op) (scalar : ScalarCellType ty)
    (declaration : ScalarCellDeclaration state name ty)
    (accepted : Impact.appendEffectWithActivity state
      (.writeCell name ty value) guard before = .ok after)
    (chunkShape : after.operations = before.operations ++ chunk) :
    chunk.filterMap popeqAlignment = [] := by
  have rawStep : ∃ emitted raw,
      Impact.appendEffect state (.writeCell name ty emitted) before = .ok raw ∧
      after.operations = raw.operations := by
    cases guard with
    | none =>
      obtain ⟨raw, appended, operations, _⟩ :=
        GuardedEffectPrefix.appendEffectWithActivity_none_result state
          (.writeCell name ty value) before after accepted
      exact ⟨value, raw, appended, operations⟩
    | some condition =>
      obtain ⟨binder, _, raw, appended, operations⟩ :=
        Impact.appendEffectWithActivity_writeCell_value state name ty value condition before after accepted
      exact ⟨.letE binder condition (GuardedExpression.totalize (.ref binder) value),
        raw, appended, operations⟩
  obtain ⟨emitted, raw, appended, operations⟩ := rawStep
  obtain ⟨base, baseAccepted, rawShape⟩ :=
    GuardedEffectPrefix.appendEffect_writeCell_chunk state name ty emitted before raw appended
  obtain ⟨_, baseShape, _⟩ := append_write_cell_scalar_supported state {} base
    name ty emitted scalar declaration baseAccepted (by simp)
  have sameChunk := List.append_cancel_left (chunkShape.symm.trans (operations.trans rawShape))
  rw [sameChunk, baseShape]
  rfl

/-- The accepted scalar Map write appends no read comparisons. -/
private theorem accepted_writeMap_chunk_no_popeq
    (state : List StateDecl) (name : String) (keyTy valueTy : Ty)
    (key : Expr keyTy) (value : Expr valueTy)
    (guard : Option (Expr .bool)) (before after : Impact.Plan)
    (chunk : List Impact.Op) (keyScalar : ScalarCellType keyTy) (valueScalar : ScalarCellType valueTy)
    (accepted : Impact.appendEffectWithActivity state
      (.writeMap name keyTy valueTy key value) guard before = .ok after)
    (chunkShape : after.operations = before.operations ++ chunk) :
    chunk.filterMap popeqAlignment = [] := by
  have rawStep : ∃ emittedKey emittedValue raw,
      Impact.appendEffect state (.writeMap name keyTy valueTy emittedKey emittedValue)
        before = .ok raw ∧ after.operations = raw.operations := by
    cases guard with
    | none =>
      obtain ⟨raw, appended, operations, _⟩ :=
        GuardedEffectPrefix.appendEffectWithActivity_none_result state
          (.writeMap name keyTy valueTy key value) before after accepted
      exact ⟨key, value, raw, appended, operations⟩
    | some condition =>
      obtain ⟨keyBinder, _, valueBinder, _, raw, appended, operations⟩ :=
        Impact.appendEffectWithActivity_writeMap_key_value state name keyTy valueTy
          key value condition before after (by cases keyScalar <;> simp) accepted
      exact ⟨.letE keyBinder condition (GuardedExpression.totalize (.ref keyBinder) key),
        .letE valueBinder condition (GuardedExpression.totalize (.ref valueBinder) value),
        raw, appended, operations⟩
  obtain ⟨emittedKey, emittedValue, raw, appended, operations⟩ := rawStep
  obtain ⟨base, baseAccepted, rawShape⟩ := GuardedEffectPrefix.appendEffect_writeMap_chunk
    state name keyTy valueTy emittedKey emittedValue before raw appended
  obtain ⟨_, baseShape, _⟩ := GenericStateMapOperations.append_write_map_scalar_supported
    state {} base name keyTy valueTy emittedKey emittedValue keyScalar valueScalar
    baseAccepted (by simp)
  have sameChunk := List.append_cancel_left (chunkShape.symm.trans (operations.trans rawShape))
  rw [sameChunk, baseShape]
  rfl

private theorem binding_of_descriptor
    (assignment : Assignment) (values : EvalEnv) (descriptor : Impact.Read)
    (name : String) (ty : Ty)
    (nameExact : descriptor.name = name) (typeExact : descriptor.ty = ty)
    (bound : ∃ value : descriptor.ty.Denote,
      values.lookup descriptor.name = some (Value.pack descriptor.ty value) ∧
      Canonical descriptor.ty value ∧
      sourceScalar? descriptor.ty value = some (assignment ("%input_" ++ descriptor.name))) :
    ∃ value : ty.Denote,
      values.lookup name = some (Value.pack ty value) ∧
      Canonical ty value ∧
      sourceScalar? ty value = some (assignment ("%input_" ++ name)) := by
  rw [← typeExact, ← nameExact]
  exact bound

/-- Each evaluated source effect consumes exactly its active read descriptors.
The candidate binding and generated absence assertion fix the compared value. -/
theorem evaluated_chunk_reads
    (ctx : EvalContext) (assignment : Assignment) (values : EvalEnv)
    (modulus : ctx.modulus = Field.modulus)
    (state : List StateDecl) (effect : Effect) (guard : Option (Expr .bool))
    (before after : Impact.Plan) (chunk : List Impact.Op)
    (descriptors : List Impact.Read) (activity : Option _root_.Bool)
    (native : List NativeState.Op)
    (source : ScalarEffect state effect)
    (accepted : Impact.appendEffectWithActivity state effect guard before = .ok after)
    (operations : after.operations = before.operations ++ chunk)
    (metadata : descriptors.map readMetadata = effectReadChunk effect before.reads.length)
    (guards : ∀ descriptor ∈ descriptors, descriptor.guard = guard)
    (bound : ∀ descriptor ∈ descriptors, ∃ value : descriptor.ty.Denote,
      values.lookup descriptor.name = some (Value.pack descriptor.ty value) ∧
      Canonical descriptor.ty value ∧
      sourceScalar? descriptor.ty value = some (assignment ("%input_" ++ descriptor.name)))
    (assertions : ∀ expression ∈ guardedEffectAssertionChunk guard effect before.reads.length,
      expression.eval ctx values = .ok _root_.Bool.true)
    (evaluated : evalChunk ctx values guard chunk = .ok (activity, native)) :
    ∃ observations, evaluateReadObservations ctx assignment values descriptors = .ok observations ∧
      (NativeStateReadTape.expectedCells native).map NativeState.Cell.value =
        activeReadValues observations := by
  cases source with
  | cell _ cellScope _ =>
    cases cellScope with
    | readCell name destination ty support declared =>
      obtain ⟨descriptor, rfl, descriptorName, descriptorType⟩ :=
        singleton_descriptor descriptors destination ty metadata
      obtain ⟨candidate, lookup, canonical, meaning⟩ :=
        binding_of_descriptor assignment values descriptor destination ty descriptorName descriptorType
          (bound descriptor (by simp))
      obtain ⟨alignment, comparisons, value⟩ := read_cell_alignment ctx values assignment
        state name destination ty guard before after chunk support declared accepted operations
        candidate lookup canonical modulus meaning
      exact singleton_chunk_reads ctx assignment values guard chunk descriptor
        (guards descriptor (by simp)) activity native evaluated alignment comparisons
        (by simpa only [descriptorName] using value)
    | writeCell name ty value support declared =>
      have empty := empty_descriptors descriptors metadata
      subst descriptors
      exact no_read_chunk_of_comparisons ctx assignment values guard chunk activity native
        evaluated (accepted_writeCell_chunk_no_popeq state name ty value guard before after
          chunk support declared accepted operations)
  | readMap name destination keyTy valueTy key keySupport _ keyAdmission =>
    obtain ⟨descriptor, rfl, descriptorName, descriptorType⟩ :=
      singleton_descriptor descriptors destination valueTy metadata
    obtain ⟨candidate, lookup, canonical, meaning⟩ :=
      binding_of_descriptor assignment values descriptor destination valueTy descriptorName descriptorType
        (bound descriptor (by simp))
    obtain ⟨alignment, comparisons, value⟩ := read_map_alignment ctx values assignment
      state name destination keyTy valueTy key guard before after chunk keySupport keyAdmission
      accepted operations candidate lookup canonical modulus meaning
    exact singleton_chunk_reads ctx assignment values guard chunk descriptor
      (guards descriptor (by simp)) activity native evaluated alignment comparisons
      (by simpa only [descriptorName] using value)
  | writeMap name keyTy valueTy key value keySupport valueSupport _ _ =>
    have empty := empty_descriptors descriptors metadata
    subst descriptors
    exact no_read_chunk_of_comparisons ctx assignment values guard chunk activity native
      evaluated (accepted_writeMap_chunk_no_popeq state name keyTy valueTy key value guard before after
        chunk keySupport valueSupport accepted operations)
  | require condition _ =>
    have empty := empty_descriptors descriptors metadata
    subst descriptors
    have emptyChunk := require_has_no_operations state condition guard before after chunk accepted operations
    subst chunk
    exact no_read_chunk_of_comparisons ctx assignment values guard [] activity native evaluated rfl
  | requireAbsent name keyTy key keySupport _ =>
    cases guard with
    | some condition =>
      exact False.elim (ScalarRequireOperationAdmission.append_requireAbsent_guarded_rejected
        state name keyTy key condition before after accepted)
    | none =>
      obtain ⟨descriptor, rfl, descriptorName, descriptorType⟩ := singleton_descriptor
        descriptors ("_noctium_absence_" ++ toString before.reads.length) .bool metadata
      exact absence_chunk_reads ctx assignment values state name keyTy key keySupport before after
        chunk descriptor descriptorName descriptorType (guards descriptor (by simp))
        (bound descriptor (by simp)) assertions accepted operations native activity evaluated

end Noctium.Verification.GuardedEffectReadValues
