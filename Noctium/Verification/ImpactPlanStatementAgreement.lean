import Noctium.Verification.ImpactPlanStatement
import Noctium.Verification.ImpactOperandValidation
import Noctium.Verification.ImpactScheduleComparison
import Noctium.Verification.ImpactTypedEnvironment

namespace Noctium.Verification.ImpactPlanStatementAgreement

open Lean Backend ImpactPlanStatement ImpactTranscriptSchedule
open ImpactExpressionSchedule ImpactOperationAgreement ImpactReferenceEvaluation
open ImpactTranscriptWidth ImpactWireDecoder ImpactWireSoundness ScalarNormalization
open ImpactOperandValidation

/-- The source statement evaluates the typed plan and traverses its guarded
field groups in source order. -/
def fromSource (ctx : EvalContext) (env : EvalEnv) (plan : Impact.Plan)
    (inputs : ImpactPlanStatement.Inputs) : Option (List NativeRelation.Scalar) := do
  let operations ← (GuardedPlanExecution.evalPlan ctx env plan).toOption
  let activity ← (plan.operations.zipIdx.mapM (sourceGroups ctx env plan)).map List.flatten
  publicInputs inputs operations activity

/-- Lower an entrypoint with the production Impact pass, then construct its
source statement. Callers supply the entrypoint used at the compiler seam. -/
def fromEntrypoint (ctx : EvalContext) (env : EvalEnv) (state : List StateDecl)
    (ep : Entrypoint) (inputs : ImpactPlanStatement.Inputs) :
    Option (List NativeRelation.Scalar) := do
  let plan ← (Backend.Impact.lower state ep).toOption
  fromSource ctx env plan inputs

/-- Successful production lowering connects the entrypoint statement to the
source-plan statement. -/
theorem fromEntrypoint_eq_fromSource
    (ctx : EvalContext) (env : EvalEnv) (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan) (inputs : ImpactPlanStatement.Inputs)
    (lowered : Backend.Impact.lower state ep = .ok plan) :
    fromEntrypoint ctx env state ep inputs = fromSource ctx env plan inputs := by
  simp [fromEntrypoint, lowered, Except.toOption, Bind.bind]

/-- Check whether a supplied artifact has the compiler's scalar operation
schedule, including all operands and activity guards. -/
def matchesBytes (budget : Nat) (bytes : ArtifactBytes.Bytes) (expected : Json) : _root_.Bool :=
  match ArtifactBytes.parse bytes with
  | .ok raw => ImpactScheduleComparison.matches budget raw expected
  | .error _ => Bool.false

private def keyWidthSupported (keyWidth : Nat → Option Nat) : Impact.Op → _root_.Bool
  | .mapIndex slot _ => decide (keyWidth slot = some 3)
  | _ => Bool.true

private theorem keyWidthSupported_sound (keyWidth : Nat → Option Nat) (op : Impact.Op)
    (checked : keyWidthSupported keyWidth op = Bool.true) : ScalarKeyWidths keyWidth op := by
  cases op <;> simp [ScalarKeyWidths]
  simpa [keyWidthSupported] using checked

/-- Check that the operation and activity expressions are in the scalar
statement fragment and that the supplied lookup provides each map key width. -/
def admitsScalarPlan (keyWidth : Nat → Option Nat) (plan : Impact.Plan) : _root_.Bool :=
  plan.operations.all (fun op =>
    (project? op).isSome && operandsSupported op && keyWidthSupported keyWidth op) &&
  plan.activityGuards.all (Option.all (fun guard => (ScalarExpressionAdmission.certify guard).isSome))

private theorem guard_mem_of_at (plan : Impact.Plan) (index : Nat) (guard : Expr .bool)
    (selected : plan.activityGuards[index]?.getD none = some guard) :
    some guard ∈ plan.activityGuards := by
  cases found : plan.activityGuards[index]? with
  | none => simp [found] at selected
  | some value =>
      have same : value = some guard := by simpa [found] using selected
      exact List.mem_of_getElem? (found.trans (congrArg some same))

/-- A checked scalar plan and matching artifact preserve both the evaluated
Impact operations and their public transcript activity. Operand and guard
validation follow from successful production lowering under the actual plan's
type environment. Circuit assertions and native acceptance have separate
proof obligations. -/
theorem evaluations_fromBytes_agree
    (profile : TargetProfile) (contractName : Name) (state : List StateDecl)
    (ctor : Option Constructor) (ep : Entrypoint) (plan : Impact.Plan)
    (standaloneFile : _root_.Bool)
    (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    {env : EvalEnv} (environmentChecked : ImpactTypedEnvironment.check (plan.typeEnvironment ep) env = Bool.true)
    (keyWidth : Nat → Option Nat)
    (admitted : admitsScalarPlan keyWidth plan = Bool.true)
    (budget : Nat) (bytes : ArtifactBytes.Bytes)
    (lowered : Impact.lower state ep = .ok plan)
    (matched : matchesBytes budget bytes
      (Compiler.nativePlanJson profile contractName state ctor ep plan standaloneFile) = Bool.true) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel →
      ∃ raw, ArtifactBytes.parse bytes = .ok raw ∧
        ImpactPlanAgreement.evaluatePlan fuel ctx env raw =
          (GuardedPlanExecution.evalPlan ctx env plan).toOption ∧
        ImpactTranscriptSchedule.evaluateSchedule fuel ctx env keyWidth raw =
          (plan.operations.zipIdx.mapM (ImpactTranscriptSchedule.sourceGroups ctx env plan)).map
            List.flatten := by
  let emitted := Compiler.nativePlanJson profile contractName state ctor ep plan standaloneFile
  let projected := projectedOperation plan
  have typed := ImpactTypedEnvironment.check_sound environmentChecked
  obtain ⟨operationCheck, guardCheck⟩ := Bool.and_eq_true_iff.mp admitted
  have checkedOp (op : Impact.Op) (inside : op ∈ plan.operations) :=
    Bool.and_eq_true_iff.mp (List.all_eq_true.mp operationCheck op inside)
  have projectCheck : plan.operations.all (fun op => (project? op).isSome) = Bool.true :=
    List.all_eq_true.mpr fun op inside => (Bool.and_eq_true_iff.mp (checkedOp op inside).1).1
  have projects := projects_of_check plan projectCheck
  have valid := Impact.lower_validated state ep plan lowered
  obtain ⟨guardShape, activityValid⟩ := plan.validate_activity_success ep valid
  have aligned : (GuardedPlanActivity.operationGuards plan).length = plan.operations.length := by
    unfold GuardedPlanActivity.operationGuards
    split
    · simp
    · rename_i notEmpty
      exact guardShape.resolve_left notEmpty
  have operandsAdmitted (op : Impact.Op) (index : Nat) (inside : (op, index) ∈ plan.operations.zipIdx) :
      ScalarOperandAdmission op :=
    sourceOperandsAdmitted_of_check op
      (Bool.and_eq_true_iff.mp (checkedOp op (List.fst_mem_of_mem_zipIdx inside)).1).2
  have operandsValid (op : Impact.Op) (index : Nat) (inside : (op, index) ∈ plan.operations.zipIdx) :
      SourceOperandsValid (plan.typeEnvironment ep) op := by
    apply sourceOperandsValid_of_fields
    intro field inOperation
    exact plan.validate_fields_success ep valid field
      (List.mem_flatMap.mpr ⟨op, List.fst_mem_of_mem_zipIdx inside, inOperation⟩)
  have guardsAdmitted (op : Impact.Op) (index : Nat) (_ : (op, index) ∈ plan.operations.zipIdx)
      (guard : Expr .bool) (selected : plan.activityGuards[index]?.getD none = some guard) :
      ScalarExpression guard := by
    have checked := List.all_eq_true.mp guardCheck (some guard)
      (guard_mem_of_at plan index guard selected)
    change (ScalarExpressionAdmission.certify guard).isSome = Bool.true at checked
    cases result : ScalarExpressionAdmission.certify guard with
    | none => simp [result] at checked
    | some proof => exact proof.down
  have guardsValid (op : Impact.Op) (index : Nat) (_ : (op, index) ∈ plan.operations.zipIdx)
      (guard : Expr .bool) (selected : plan.activityGuards[index]?.getD none = some guard) :
      guard.validate Capabilities.scalarFragment (plan.typeEnvironment ep) = .ok () :=
    activityValid guard (guard_mem_of_at plan index guard selected)
  have keys (op : Impact.Op) (index : Nat) (inside : (op, index) ∈ plan.operations.zipIdx) :
      ScalarKeyWidths keyWidth op :=
    keyWidthSupported_sound keyWidth op (checkedOp op (List.fst_mem_of_mem_zipIdx inside)).2
  obtain ⟨operationMinimum, operationsAgree⟩ :=
    ImpactPlanAgreement.evaluate_nativePlanJson_agrees
      profile contractName state ctor ep plan standaloneFile projected ctx modulus
      typed aligned projects operandsAdmitted operandsValid guardsAdmitted guardsValid
  obtain ⟨activityMinimum, activityAgree⟩ :=
    ImpactTranscriptSchedule.evaluate_nativePlanJson_agrees
      profile contractName state ctor ep plan standaloneFile projected ctx modulus
      typed keyWidth projects keys guardsAdmitted guardsValid
  let minimum := max operationMinimum activityMinimum
  refine ⟨minimum, ?_⟩
  intro fuel enough
  have operationFuel : operationMinimum ≤ fuel :=
    Nat.le_trans (Nat.le_max_left _ _) enough
  have activityFuel : activityMinimum ≤ fuel :=
    Nat.le_trans (Nat.le_max_right _ _) enough
  have compared : ∃ raw, ArtifactBytes.parse bytes = .ok raw ∧
      ImpactScheduleComparison.matches budget raw emitted = Bool.true := by
    cases parsed : ArtifactBytes.parse bytes with
    | error reason => simp [matchesBytes, parsed] at matched
    | ok raw => exact ⟨raw, rfl, by simpa [matchesBytes, parsed, emitted] using matched⟩
  obtain ⟨raw, parsed, scheduleMatches⟩ := compared
  obtain ⟨operationsMatch, activityMatches⟩ :=
    ImpactScheduleComparison.evaluations_eq_of_matches scheduleMatches fuel ctx env keyWidth
  have operationsSource : ImpactPlanAgreement.evaluatePlan fuel ctx env raw =
      (GuardedPlanExecution.evalPlan ctx env plan).toOption := by
    calc
      ImpactPlanAgreement.evaluatePlan fuel ctx env raw =
          ImpactPlanAgreement.evaluatePlan fuel ctx env emitted := operationsMatch
      _ = (GuardedPlanExecution.evalPlan ctx env plan).toOption := by
        dsimp only [emitted]
        exact operationsAgree fuel operationFuel
  have activitySource : ImpactTranscriptSchedule.evaluateSchedule fuel ctx env keyWidth raw =
      (plan.operations.zipIdx.mapM (ImpactTranscriptSchedule.sourceGroups ctx env plan)).map
        List.flatten := by
    calc
      ImpactTranscriptSchedule.evaluateSchedule fuel ctx env keyWidth raw =
          ImpactTranscriptSchedule.evaluateSchedule fuel ctx env keyWidth emitted := activityMatches
      _ = (plan.operations.zipIdx.mapM (ImpactTranscriptSchedule.sourceGroups ctx env plan)).map
          List.flatten := by
        dsimp only [emitted]
        exact activityAgree fuel activityFuel
  exact ⟨raw, parsed, operationsSource, activitySource⟩

/-- A checked scalar plan and matching artifact yield the same modeled public
statement. Operand and guard validation follow from successful production
lowering under the actual plan's type environment. -/
theorem fromBytes_nativePlanJson_agrees
    (profile : TargetProfile) (contractName : Name) (state : List StateDecl)
    (ctor : Option Constructor) (ep : Entrypoint) (plan : Impact.Plan)
    (standaloneFile : _root_.Bool)
    (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    {env : EvalEnv} (environmentChecked : ImpactTypedEnvironment.check (plan.typeEnvironment ep) env = Bool.true)
    (keyWidth : Nat → Option Nat)
    (admitted : admitsScalarPlan keyWidth plan = Bool.true)
    (budget : Nat) (bytes : ArtifactBytes.Bytes) (inputs : ImpactPlanStatement.Inputs)
    (lowered : Impact.lower state ep = .ok plan)
    (matched : matchesBytes budget bytes
      (Compiler.nativePlanJson profile contractName state ctor ep plan standaloneFile) = Bool.true) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel →
      fromBytes fuel ctx env keyWidth bytes inputs = fromEntrypoint ctx env state ep inputs := by
  obtain ⟨minimum, agrees⟩ := evaluations_fromBytes_agree profile contractName state ctor ep plan
    standaloneFile ctx modulus environmentChecked keyWidth admitted budget bytes lowered matched
  refine ⟨minimum, ?_⟩
  intro fuel enough
  obtain ⟨raw, parsed, operationsMatch, activityMatches⟩ := agrees fuel enough
  unfold ImpactPlanStatement.fromBytes
  rw [parsed]
  simp only [Except.toOption, Bind.bind, Option.bind_some]
  rw [operationsMatch, activityMatches,
    fromEntrypoint_eq_fromSource ctx env state ep plan inputs lowered]
  rfl

end Noctium.Verification.ImpactPlanStatementAgreement
