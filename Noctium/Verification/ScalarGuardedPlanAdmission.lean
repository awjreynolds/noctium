import Noctium.Verification.GenericStateAdmissionPrefix
import Noctium.Verification.ScalarCellPublicAdmission
import Noctium.Verification.ScalarGuardedCellOperationAdmission
import Noctium.Verification.ScalarMapOperationAdmission
import Noctium.Verification.ScalarRequireOperationAdmission
import Noctium.Verification.ScalarExpectedPlanSchedule

namespace Noctium.Verification.ScalarGuardedPlanAdmission

open Backend GenericStateCircuitParts NativeRelation ScalarNormalization
open GenericStateCellAdmission (ScalarCellEffect ScalarCellType)
open ScalarOperationSyntax (AdmittedOps)

/-- Typed scalar effects and their admitted source operands. Acceptance of
the actual lowerer determines which of these effects support a guard. -/
inductive ScalarEffect (state : List StateDecl) : Effect → Prop where
  | cell (effect : Effect) : ScalarCellEffect state effect →
      ScalarCellSourceReads.ScalarCellOperand effect → ScalarEffect state effect
  | readMap (name destination : String) (keyTy valueTy : Ty) (key : Expr keyTy) :
      ScalarCellType keyTy → ScalarCellType valueTy → ScalarExpression key →
      ScalarEffect state (.readMap name destination keyTy valueTy key)
  | writeMap (name : String) (keyTy valueTy : Ty) (key : Expr keyTy) (value : Expr valueTy) :
      ScalarCellType keyTy → ScalarCellType valueTy →
      ScalarExpression key → ScalarExpression value →
      ScalarEffect state (.writeMap name keyTy valueTy key value)
  | require (condition : Expr .bool) :
      ScalarExpression condition → ScalarEffect state (.require condition)
  | requireAbsent (name : String) (keyTy : Ty) (key : Expr keyTy) :
      ScalarCellType keyTy → ScalarExpression key →
      ScalarEffect state (.requireAbsent name keyTy key)

private theorem append_admitted_ops
    (state : List StateDecl) (before after : Impact.Plan) (effect : Effect)
    (guard : Option (Expr .bool)) (source : ScalarEffect state effect)
    (guardAdmitted : ∀ condition, guard = some condition → ScalarExpression condition)
    (accepted : Impact.appendEffectWithActivity state effect guard before = .ok after)
    (previous : AdmittedOps before.operations) : AdmittedOps after.operations := by
  cases source with
  | cell effect shape operand =>
    exact ScalarGuardedCellOperationAdmission.append_cell_fields_admitted
      state before after effect guard shape operand guardAdmitted accepted previous
  | readMap name destination keyTy valueTy key keyScalar valueScalar keyAdmitted =>
    exact ScalarMapOperationAdmission.append_read_map_fields_admitted
      state before after name destination keyTy valueTy key guard keyScalar valueScalar
      keyAdmitted guardAdmitted accepted previous
  | writeMap name keyTy valueTy key value keyScalar valueScalar keyAdmitted valueAdmitted =>
    exact ScalarMapOperationAdmission.append_write_map_fields_admitted
      state before after name keyTy valueTy key value guard keyScalar valueScalar
      keyAdmitted valueAdmitted guardAdmitted accepted previous
  | require condition _ =>
    exact ScalarRequireOperationAdmission.append_require_fields_admitted
      state before after condition guard accepted previous
  | requireAbsent name keyTy key keyScalar keyAdmitted =>
    exact ScalarRequireOperationAdmission.append_require_absent_fields_admitted
      state before after name keyTy key keyScalar keyAdmitted guard accepted previous

private theorem guarded_trace_admitted_ops {state : List StateDecl}
    {guards : List (Option (Expr .bool))} {items : List (Effect × Nat)}
    {initial final : Impact.Plan} {offsets : List Nat}
    (trace : Impact.GuardedEffectTrace state guards items initial final offsets)
    (effects : ∀ item ∈ items, ScalarEffect state item.1)
    (guardsAdmitted : ∀ condition, some condition ∈ guards → ScalarExpression condition)
    (initialAdmitted : AdmittedOps initial.operations) : AdmittedOps final.operations := by
  induction trace with
  | nil plan => exact initialAdmitted
  | @cons item rest before next final offsets step tail ih =>
    have guardAdmitted (condition : Expr .bool)
        (selected : guards[item.2]?.getD none = some condition) : ScalarExpression condition := by
      cases found : guards[item.2]? with
      | none => simp [found] at selected
      | some guard =>
        have equal : guard = some condition := by simpa [found] using selected
        exact guardsAdmitted condition (equal ▸ List.mem_of_getElem? found)
    have nextAdmitted := append_admitted_ops state before next item.1
      (guards[item.2]?.getD none) (effects item (by simp)) guardAdmitted step initialAdmitted
    exact ih (fun remaining member => effects remaining (List.mem_cons_of_mem item member))
      nextAdmitted

/-- The exact accepted public-input and effect trace preserves both opcode
support and field-expression admission. Interpreter success plays no role. -/
theorem lower_admitted_ops (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (lowered : Impact.lower state entry = .ok plan)
    (compatible : ∀ input ∈ entry.circuit.inputs, Impact.publicInputScalarCompatible input)
    (effects : ∀ effect ∈ entry.effects, ScalarEffect state effect)
    (guardsAdmitted : ∀ condition, some condition ∈ entry.effectGuards →
      ScalarExpression condition) : AdmittedOps plan.operations := by
  obtain ⟨_, inputPlan, _, inputAccepted, trace⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state entry plan lowered
  have initialSupported := GenericStateOps.publicInputPlan_scalar_supported
    entry.circuit.inputs {} inputPlan inputAccepted compatible (by simp)
  have initialFields := ScalarCellPublicAdmission.publicInputPlan_fields_admitted
    entry.circuit.inputs inputPlan compatible inputAccepted
  have initialAdmitted : AdmittedOps inputPlan.operations := by
    intro operation member
    exact ⟨initialSupported operation member,
      fun field fieldMember =>
        ScalarOperationSyntax.field_of_group (initialFields operation member) fieldMember⟩
  apply guarded_trace_admitted_ops trace _ guardsAdmitted initialAdmitted
  intro item member
  apply effects item.1
  rw [← List.zipIdx_map_fst 0 entry.effects]
  exact List.mem_map_of_mem member

/-- An accepted scalar source plan with checked requirements evaluates to the
ordered native groups selected by the compiler's expected entrypoint. -/
theorem lower_expected_scalar_schedule (state : List StateDecl) (entry : Entrypoint)
    (expected : Native.Expected) (plan : Impact.Plan) (frame : OutputFrame)
    (aliases : Native.AliasEnvironment) (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (witness : Assignment) (values : EvalEnv)
    (environment : TypedEnvironment hash witness aliases values (plan.typeEnvironment entry))
    (accepted : Native.expectedEntrypoint state entry = .ok expected)
    (lowered : Impact.lower state entry = .ok plan)
    (normalized : normalizeOutputs (entrypointSeedAliases entry plan)
      entry.circuit.outputs = .ok frame)
    (readAliases : forIn ((plan.reads.drop
      (Impact.publicInputReadCount entry.circuit.inputs)).flatMap Impact.Read.scalarReads)
      frame.1 (readAliasStep entry) = .ok aliases)
    (compatible : ∀ input ∈ entry.circuit.inputs, Impact.publicInputScalarCompatible input)
    (effects : ∀ effect ∈ entry.effects, ScalarEffect state effect)
    (guardsAdmitted : ∀ condition, some condition ∈ entry.effectGuards →
      ScalarExpression condition)
    (bounds : ∀ requirement ∈ expected.bounds,
      ∃ value, interpret hash witness requirement.1 = some value ∧ value.val ≤ requirement.2)
    (assertions : ∀ term ∈ expected.assertions, interpret hash witness term = some one) :
    ∃ operations, GenericStateOps.evalPlan ctx values plan = .ok operations ∧
      expected.groups.map (List.map (interpret hash witness)) =
        (NativeState.groups operations).map (List.map some) := by
  exact ScalarExpectedPlanSchedule.expected_schedule_of_admitted_operations state entry expected
    plan frame aliases ctx hash implementation witness values environment accepted lowered
    normalized readAliases (lower_admitted_ops state entry plan lowered compatible effects guardsAdmitted)
    bounds assertions

end Noctium.Verification.ScalarGuardedPlanAdmission
