import Noctium.Verification.GenericStateCircuitParts
import Noctium.Verification.ScalarImpactOperationMeaning
import Noctium.Verification.ScalarOperationSyntax

namespace Noctium.Verification.ScalarExpectedPlanSchedule

open Backend Native NativeRelation ScalarNormalization
open GenericStateCircuitParts

/-- A production expected entrypoint fixes the admitted scalar plan schedule.
The output frame and read-alias fold remain explicit so typed normalization
uses the exact aliases selected by the constructor. -/
theorem expected_schedule_of_admitted_operations
    (state : List StateDecl) (entry : Entrypoint) (expected : Native.Expected)
    (plan : Backend.Impact.Plan) (outputFrame : OutputFrame)
    (aliases : Native.AliasEnvironment)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (witness : Assignment) (values : EvalEnv)
    (typed : TypedEnvironment hash witness aliases values (plan.typeEnvironment entry))
    (accepted : Native.expectedEntrypoint state entry = .ok expected)
    (planAccepted : Backend.Impact.lower state entry = .ok plan)
    (normalizedOutput : normalizeOutputs (entrypointSeedAliases entry plan)
      entry.circuit.outputs = .ok outputFrame)
    (readAliases : forIn ((plan.reads.drop
      (Backend.Impact.publicInputReadCount entry.circuit.inputs)).flatMap
        Backend.Impact.Read.scalarReads) outputFrame.1 (readAliasStep entry) = .ok aliases)
    (admitted : ScalarOperationSyntax.AdmittedOps plan.operations)
    (boundsChecked : ∀ requirement ∈ expected.bounds,
      ∃ value, interpret hash witness requirement.1 = some value ∧
        value.val ≤ requirement.2)
    (assertionsChecked : ∀ assertion ∈ expected.assertions,
      interpret hash witness assertion = some one) :
    ∃ native, GenericStateOps.evalPlan ctx values plan = .ok native ∧
      expected.groups.map (List.map (interpret hash witness)) =
        (NativeState.groups native).map (List.map some) := by
  obtain ⟨actualPlan, actualOutputFrame, actualAliases, inputState, conditions,
    guards, constraintCollection, guardCollection, operationFrame, returns,
    activity, actualPlanAccepted, outputAccepted, aliasesAccepted, inputStateAccepted,
    conditionsAccepted, guardsAccepted, constraintCollectionAccepted,
    guardCollectionAccepted, operationsAccepted, returnsAccepted,
    activityAccepted, inputShape, groupsShape, returnShape, modeShape, rawShape,
    groupGuardsShape, assertionsShape, boundsShape⟩ :=
    GenericStateCircuitParts.expectedEntrypoint_parts state entry expected accepted
  have samePlan : actualPlan = plan :=
    Except.ok.inj (actualPlanAccepted.symm.trans planAccepted)
  subst actualPlan
  have sameOutputFrame : actualOutputFrame = outputFrame :=
    Except.ok.inj (outputAccepted.symm.trans normalizedOutput)
  subst actualOutputFrame
  have sameAliases : actualAliases = aliases :=
    Except.ok.inj (aliasesAccepted.symm.trans readAliases)
  subst actualAliases
  have collected : Native.collectOperations entry.span aliases plan.operations
      outputFrame.2.1 = .ok
        (expected.groups, operationFrame.2.1, operationFrame.2.2) := by
    simpa only [Native.collectOperations, groupsShape] using operationsAccepted
  have supported : ∀ operation ∈ plan.operations,
      GenericStateOps.ScalarOperation operation :=
    fun operation member => (admitted operation member).1
  have expressions : ∀ operation ∈ plan.operations,
      ∀ field ∈ operation.fields, ScalarExpression field :=
    fun operation member => (admitted operation member).2
  have operationBoundsChecked : ∀ requirement ∈ operationFrame.2.1,
      ∃ value, interpret hash witness requirement.1 = some value ∧
        value.val ≤ requirement.2 := by
    intro requirement member
    apply boundsChecked requirement
    rw [boundsShape]
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl member))))
  have operationAssertionsChecked : ∀ assertion ∈ operationFrame.2.2,
      interpret hash witness assertion = some one := by
    intro assertion member
    apply assertionsChecked assertion
    rw [assertionsShape]
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr member))
  exact ScalarImpactOperationMeaning.collectPlan_scalar_schedule
    state entry plan planAccepted ctx hash implementation witness aliases values typed
    outputFrame.2.1 expected.groups operationFrame.2.1 operationFrame.2.2
    supported expressions operationBoundsChecked operationAssertionsChecked collected

end Noctium.Verification.ScalarExpectedPlanSchedule
