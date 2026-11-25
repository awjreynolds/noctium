import Noctium.Verification.ArtifactCertificate
import Noctium.Verification.ImpactTypedEnvironment
import Noctium.Verification.ScalarCellImpactByteEvaluation
import Noctium.Verification.ScalarCellNativeTranscript
import Noctium.Verification.ScalarCellZkirByteBinding

namespace Noctium.Verification.ScalarCellArtifactExecution

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization
open NativePrivacy
open ScalarCellSourceReads ScalarLedgerWitnessPreflight
open ScalarValidationOpcodeProfile (checkedScalarOpcodeProfile)

/-- Compose checked byte parsing and independent build identity with the
scalar-cell source proof. The call bytes retain the raw header. The plan
bytes must parse to the full emitted plan tree and pass the operation schedule
check. The result concerns Lean's byte and VM models. -/
theorem lowerEntrypoint_checked_artifact_execution
    (profile : TargetProfile) (contractName : Name) (ctor : Option Constructor)
    (standaloneFile : _root_.Bool)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (declarations : List StateDecl) (ep : Entrypoint) (plan : Impact.Plan)
    (values result : EvalEnv) (initial next : LedgerState)
    (inputs : NativeRelation.Assignment) (initialSlots : List NativeState.Slot)
    (authority : ArtifactCertificate.Authority) (build : ArtifactCertificate.BuildIdentity)
    (sourceIdentity : String) (planBytes callBytes : ArtifactBytes.Bytes) (budget : Nat)
    (keyWidth : Nat → Option Nat) {call : ScalarCall}
    (authenticated : ArtifactCertificate.Authenticated authority build sourceIdentity planBytes callBytes)
    (lowered : Zkir.lowerEntrypoint declarations ep = .ok (ArtifactBytes.tree callBytes))
    (callDecoded : ScalarCellZkirByteBinding.decodeScalarCallBytes callBytes = .ok call)
    (planAccepted : Impact.lower declarations (Passes.pruneEntrypoint ep) = .ok plan)
    (planParsed : ArtifactBytes.parse planBytes =
      .ok (Compiler.nativePlanJson profile contractName declarations ctor
        (Passes.pruneEntrypoint ep) plan standaloneFile))
    (planMatched : ImpactPlanStatementAgreement.matchesBytes budget planBytes
      (Compiler.nativePlanJson profile contractName declarations ctor
        (Passes.pruneEntrypoint ep) plan standaloneFile) = Bool.true)
    (planAdmitted : ImpactPlanStatementAgreement.admitsScalarPlan keyWidth plan = Bool.true)
    (opcodeProfile : checkedScalarOpcodeProfile
      (defaultEntrypointRows ep plan).toList.zipIdx call.body.instructions = Bool.true)
    (admittedInputs : CanonicalInputs ep.circuit values inputs)
    (circuitAdmission : ScalarCircuitAdmission ep.circuit)
    (returnScope : ∀ declaredReturn ∈ ep.returns,
      ∃ _ : ScalarType declaredReturn.ty, ScalarExpression declaredReturn.value)
    (unguarded : ep.effectGuards = [])
    (cellScope : ScalarCellEffects declarations ep.effects)
    (cellOperands : ∀ effect ∈ ep.effects, ScalarCellOperand effect)
    (admittedState : GenericStateEncoding.AdmittedState declarations initial initialSlots)
    (success : ep.run ctx values initial = .ok (result, next)) :
    let planTree := Compiler.nativePlanJson profile contractName declarations ctor
      (Passes.pruneEntrypoint ep) plan standaloneFile
    ExactArtifactBinding ArtifactBytes.Bytes ArtifactCertificate.BuildIdentity sourceIdentity planBytes callBytes
      planTree (ArtifactBytes.tree callBytes) build ArtifactBytes.parse (ArtifactCertificate.Authenticated authority) ∧
    ∃ expected outputs finalEnv entries assignment readValues operations finalSlots returned,
      Native.expectedEntrypoint declarations (Passes.pruneEntrypoint ep) = .ok expected ∧
      sourceReadInputs ctx ep.effects (Impact.publicInputReadCount ep.circuit.inputs)
        (outputs ++ values,
          {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []}) =
        .ok (entries, (finalEnv, next)) ∧
      CircuitSatisfies hash call.body
        ⟨ScalarValidatedProgram.inputValues expected .public
            (ScalarCellWitnessReadSeed.seedReadValues inputs entries),
          ScalarValidatedProgram.inputValues expected .private
            (ScalarCellWitnessReadSeed.seedReadValues inputs entries)⟩
        assignment (NativeState.groups operations) ∧
      call.arguments.map assignment = expected.rawInputs.map
        (fun input => ScalarCellWitnessReadSeed.seedReadValues inputs entries input.identifier) ∧
      GenericStateInputValues.decodeReads
        (plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)) assignment = .ok readValues ∧
      (∃ minimum, ∀ fuel, minimum ≤ fuel →
        ImpactPlanAgreement.evaluatePlan fuel ctx ((outputs ++ values) ++ readValues) planTree =
          some operations ∧
        ImpactPlanAgreement.runPlanBytes fuel ctx ((outputs ++ values) ++ readValues) planBytes
          (GenericStateEncoding.initial initialSlots) =
          some ⟨[.vector finalSlots],
            ScalarCellNativePublicPrefix.sourcePublicCells ep.circuit.inputs inputs ++
              ScalarCellNativeTrace.tapeCells entries⟩) ∧
      GenericStateEncoding.encodeState declarations next = some finalSlots ∧
      ep.evalReturns ctx finalEnv = .ok returned ∧ result = outputs ++ returned ∧
      call.body.returns assignment = returned.map (fun binding => scalar (valueNumber binding.2)) := by
  obtain ⟨callParsed, decoded⟩ := ScalarCellZkirByteBinding.checked_tree callDecoded
  obtain ⟨expected, outputs, finalEnv, entries, assignment, readValues, operations, finalSlots, _,
    returned, expectedAccepted, circuitRun, tape, _, satisfies, arguments, readDecoded,
    evaluated, nativeRun, _, _, _, encoded, groups, returnEvaluated, resultShape, returns, typedFrame⟩ :=
    ScalarCellNativeTranscript.lowerEntrypoint_checked_native_transcript
      ctx hash implementation declarations ep plan values result initial next inputs initialSlots
      lowered decoded planAccepted opcodeProfile admittedInputs circuitAdmission returnScope
      unguarded cellScope cellOperands admittedState success
  obtain ⟨_, typedEnvironment⟩ := typedFrame
  obtain ⟨minimum, byteAgrees⟩ := ScalarCellImpactByteEvaluation.evaluations_fromBytes_agree
    profile contractName declarations ctor (Passes.pruneEntrypoint ep) plan standaloneFile
    ctx implementation.modulus (ImpactTypedEnvironment.of_normalization typedEnvironment)
    keyWidth planAdmitted budget planBytes planAccepted unguarded cellScope planMatched evaluated
  refine ⟨⟨planParsed, callParsed, authenticated⟩, expected, outputs, finalEnv, entries, assignment,
    readValues, operations, finalSlots, returned, expectedAccepted, tape, ?_, arguments, readDecoded,
    ⟨minimum, ?_⟩, encoded, returnEvaluated, resultShape, returns⟩
  · rw [← groups]
    exact satisfies
  · intro fuel enough
    obtain ⟨raw, parsed, evaluatedAtFuel⟩ := byteAgrees fuel enough
    rw [Except.ok.inj (parsed.symm.trans planParsed)] at evaluatedAtFuel
    refine ⟨evaluatedAtFuel, ?_⟩
    unfold ImpactPlanAgreement.runPlanBytes
    simpa only [planParsed, Except.toOption, Bind.bind, Option.bind_some, evaluatedAtFuel] using nativeRun

end Noctium.Verification.ScalarCellArtifactExecution
