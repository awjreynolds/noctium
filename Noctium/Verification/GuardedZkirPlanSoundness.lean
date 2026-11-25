import Noctium.Verification.ScalarPlanGuardSoundness
import Noctium.Verification.ScalarEffectReadFacts
import Noctium.Verification.GenericStateWriteEvaluation
import Noctium.Verification.GuardedReadDefaultSemantics
import Noctium.Verification.GuardedReadDescriptorTrace
import Noctium.Verification.GuardedZkirRequirements
import Noctium.Verification.GuardedImpactTranscript

namespace Noctium.Verification.GuardedZkirPlanSoundness
open Lean Backend NativeRelation ScalarNormalization
open GenericStateCircuitParts GenericStateInputValues GenericStateCheckedReadTrace
open GuardedImpactTranscript
open GuardedReadDefaultSemantics

private theorem asserted_evaluation_true (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (witness : Assignment)
    (aliases : Native.AliasEnvironment) (values : EvalEnv)
    (agrees : AliasAgreement hash witness aliases values)
    (condition : Expr .bool) (admission : ScalarExpression condition) (value : Bool)
    (evaluated : condition.eval ctx values = .ok value)
    (result : Native.Normalized) (normal : Native.normalize aliases condition = .ok result)
    (asserted : interpret hash witness result.term = some one) :
    value = true := by
  obtain ⟨actual, normalized, represented⟩ :=
    normalize_success ctx hash implementation witness aliases values agrees
      condition admission value evaluated
  have same := Except.ok.inj (normalized.symm.trans normal)
  subst actual
  have meaning := represented.2.2
  rw [meaning] at asserted
  cases value with
  | false => exact False.elim (zero_ne_one (Option.some.inj asserted))
  | true => rfl

private theorem checked_inactive_read (state : List StateDecl) (entry : Entrypoint)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (witness : Assignment) (plan : Impact.Plan) (expected : Native.Expected)
    (frame : OutputFrame) (base decoded : EvalEnv) (read : Impact.Read) (guard : Expr .bool)
    (planAccepted : Impact.lower state entry = .ok plan)
    (expectedAccepted : Native.expectedEntrypoint state entry = .ok expected)
    (frameAccepted : normalizeOutputs (entrypointSeedAliases entry plan) entry.circuit.outputs = .ok frame)
    (environment : TypedEnvironment hash witness frame.1 (base ++ decoded) (plan.typeEnvironment entry))
    (scalarReads : ∀ read ∈
      (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).flatMap Impact.Read.scalarReads,
      scalarAliasReadType read.ty)
    (decodedReads : decodeReads (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs))
      witness = .ok decoded)
    (distinct : (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).Pairwise
      (fun left right => left.name ≠ right.name))
    (member : read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs))
    (plain : read.components = [])
    (guarded : read.guard = some guard)
    (admission : ScalarExpression guard)
    (fresh : base.lookup read.name = none)
    (typed : read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (bounded : (witness ("%input_" ++ read.name)).val ≤ Native.sourceMaximum read.ty)
    (inactive : guard.eval ctx (base ++ decoded) = .ok false)
    (assertions : ∀ term ∈ expected.assertions, interpret hash witness term = some one) :
    witness ("%input_" ++ read.name) = zero := by
  obtain ⟨candidate, lookup, canonical, meaning⟩ :=
    GenericStateReadEnvironment.read_candidate_from_decoded_reads base
      (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs))
      witness decoded decodedReads distinct read member fresh typed bounded
  obtain ⟨support⟩ := GenericStateWriteEvaluation.scalarType_of_canonical canonical
  let condition := inactiveReadDefaultConstraint read.name guard support
  have conditionMember : condition ∈ read.inactiveDefaultConstraints := by
    rw [inactiveDefaultConstraints_plain_scalar read guard support plain guarded]
    exact List.mem_cons_self
  have conditionAdmitted := inactiveReadDefaultConstraint_scalarExpression
    read.name guard support admission
  obtain ⟨value, evaluated, defaultOfTrue⟩ :=
    inactiveReadDefaultConstraint_eval ctx (base ++ decoded) read.name guard
      support candidate lookup canonical implementation.modulus inactive
  obtain ⟨actualFrame, normalized, actualAccepted, normal, _, participates⟩ :=
    expectedEntrypoint_inactiveDefault state entry expected plan planAccepted expectedAccepted
      scalarReads read condition member conditionMember
  have sameFrame := Except.ok.inj (actualAccepted.symm.trans frameAccepted)
  subst actualFrame
  have truth := asserted_evaluation_true ctx hash implementation witness frame.1 (base ++ decoded)
    environment.aliases condition conditionAdmitted value evaluated normalized normal
    (assertions normalized.term (participates normalized.term (by simp)))
  have scalarZero := (scalarDefaultValue_source_zero support candidate canonical).mp
    (defaultOfTrue.mp truth)
  exact Option.some.inj (meaning.symm.trans scalarZero)

/-- The actual accepted mixed ZKIR rows establish the plan assertions and
canonical zeros for inactive scalar reads. The initial call frame supplies
the source and witness alias agreement. -/
theorem lowerEntrypoint_guardedPlanRequirements
    (state : List StateDecl) (entry : Entrypoint) (rewrites : Zkir.Rewrites)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (witness : Assignment) (json : Json) (instructions : Array Json)
    (rows : List GuardedScalarRows.Row) (plan : Impact.Plan) (expected : Native.Expected)
    (frame : OutputFrame) (base : EvalEnv)
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (parsed : Native.arrayField json "instructions" = .ok instructions)
    (decoded : instructions.toList.mapM GuardedScalarRows.decodeRow = .ok rows)
    (holds : ∀ row ∈ rows, ordinaryHolds hash witness row)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (expectedAccepted : Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected)
    (inputSchema : ∀ requirement ∈ expected.rawInputs ++ expected.inputs, requirement.ty.isForeign = false)
    (frameAccepted : normalizeOutputs (entrypointSeedAliases (Passes.pruneEntrypoint entry) plan)
      (Passes.pruneEntrypoint entry).circuit.outputs = .ok frame)
    (baseEnvironment : TypedEnvironment hash witness frame.1 base
      (GenericStateEffectValidation.initialEffectTypeEnv (Passes.pruneEntrypoint entry)))
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
    (readAdmitted : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      read.components = [] ∧ (scalarType? read.ty).isSome = true ∧
        read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (readFresh : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      base.lookup read.name = none ∧
        (GenericStateEffectValidation.initialEffectTypeEnv
          (Passes.pruneEntrypoint entry)).lookup read.name = none)
    (readDistinct : (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).Pairwise
      (fun left right => left.name ≠ right.name))
    (readAliases : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      frame.1.lookup read.name = some (.input ("%input_" ++ read.name)))
    (readGuards : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      ∀ guard, read.guard = some guard → ScalarExpression guard)
    (admitted : ∀ guard ∈ plan.guards, ScalarExpression guard) :
    ∃ values, decodeReads (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs))
        witness = .ok values ∧
      TypedEnvironment hash witness frame.1 (base ++ values)
        (plan.typeEnvironment (Passes.pruneEntrypoint entry)) ∧
      (∀ effect ∈ entry.effects, match effect with
        | .readCell _ destination ty | .readMap _ destination _ ty _ =>
          base.lookup destination = none ∧
          ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok () ∧
          (witness ("%input_" ++ destination)).val ≤ Native.sourceMaximum ty
        | _ => True) ∧
      (∀ expression ∈ plan.guards, expression.eval ctx (base ++ values) = .ok true) ∧
      ∀ item ∈ entry.effects.zipIdx, ∀ condition, entry.effectGuardAt item.2 = some condition →
        condition.eval ctx (base ++ values) = .ok false → match item.1 with
        | .readCell _ destination _ | .readMap _ destination _ _ _ =>
          witness ("%input_" ++ destination) = zero
        | _ => True := by
  let ep := Passes.pruneEntrypoint entry
  have schema : ∀ specimen, Native.expectedEntrypoint state ep = .ok specimen →
      ∀ requirement ∈ specimen.rawInputs ++ specimen.inputs, requirement.ty.isForeign = false := by
    intro specimen accepted
    rw [expectedAccepted] at accepted
    cases accepted
    exact inputSchema
  obtain ⟨actual, actualAccepted, requirements⟩ :=
    GuardedZkirRequirements.lowerEntrypoint_guardedRows_sourceRequirements rewrites
      lowered parsed decoded schema
  have actualEq := Except.ok.inj (actualAccepted.symm.trans expectedAccepted)
  subst actual
  have ⟨assertions, bounds, inputBounds⟩ := requirements holds
  obtain ⟨values, readDecoded, environment, readBounds, planAssertions⟩ :=
    ScalarPlanGuardSoundness.plan_guards_sound_of_requirements state ep ctx hash implementation witness
      plan expected frame base planAccepted expectedAccepted frameAccepted baseEnvironment
      readAdmitted readFresh readDistinct readAliases admitted assertions bounds inputBounds
  have readFacts := ScalarEffectReadFacts.lower_read_facts state ep plan base witness planAccepted
    scope (fun read member => (readFresh read member).1)
    (fun read member => (readAdmitted read member).2.2) readBounds
  have allReadTypes : ∀ read ∈
      (plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)).flatMap Impact.Read.scalarReads,
      scalarAliasReadType read.ty := by
    rw [ScalarPlanGuardSoundness.plain_reads_scalarReads
      (plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs))
      (fun read member => (readAdmitted read member).1)]
    exact fun read member =>
      ScalarPlanGuardSoundness.scalarType_shape read.ty (readAdmitted read member).2.1
  have zeroRead : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs),
      ∀ guard, read.guard = some guard → guard.eval ctx (base ++ values) = .ok false →
      witness ("%input_" ++ read.name) = zero := by
    intro read member guard guarded inactive
    exact checked_inactive_read state ep ctx hash implementation witness plan expected frame base
      values read guard planAccepted expectedAccepted frameAccepted environment allReadTypes
      readDecoded readDistinct member (readAdmitted read member).1 guarded
      (readGuards read member guard guarded) (readFresh read member).1
      (readAdmitted read member).2.2 (readBounds read member) inactive assertions
  refine ⟨values, readDecoded, environment, readFacts, planAssertions, ?_⟩
  intro item member condition selected inactive
  rcases item with ⟨effect, index⟩
  cases effect <;> try exact True.intro
  case readCell name destination ty =>
    obtain ⟨read, descriptor, nameEq, _, activity⟩ :=
      GuardedReadDescriptorTrace.lower_readCell_descriptor state ep plan index condition
        name destination ty planAccepted scope member selected
    simpa only [nameEq] using zeroRead read descriptor condition activity inactive
  case readMap name destination keyTy ty key =>
    obtain ⟨read, descriptor, nameEq, _, activity⟩ :=
      GuardedReadDescriptorTrace.lower_readMap_descriptor state ep plan index condition
        name destination keyTy ty key planAccepted scope member selected
    simpa only [nameEq] using zeroRead read descriptor condition activity inactive

end Noctium.Verification.GuardedZkirPlanSoundness
