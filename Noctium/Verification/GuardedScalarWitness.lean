import Noctium.Verification.GuardedScalarWitnessAssembly
import Noctium.Verification.GuardedScalarWitnessCheck
import Noctium.Verification.GuardedStatementConsumption
import Noctium.Verification.GuardedPlanExecution
import Noctium.Verification.ImpactStatementScalar
import Noctium.Verification.ScalarSourceReadWitness

namespace Noctium.Verification.GuardedScalarWitness

open Lean Backend NativeRelation
open GuardedStatementConsumption (Inputs)
open ScalarCellWitnessReadSeed (seedReadValues)

/-- An assignment to the exact guarded scalar rows accepted by the artifact
checker. The ordinary constraints and both transcript streams are checked
independently of assignment construction. -/
structure Checked (hash : Hash) (seed : Assignment)
    (bytes : ArtifactBytes.Bytes) (expected : Json) (inputs : Inputs) where
  assignment : Assignment
  rows : List GuardedScalarRows.Row
  observations : List GuardedImpactObservation.Observation
  inputFrame : ∀ name, assignment ("%input_" ++ name) = seed ("%input_" ++ name)
  producerJson : (ArtifactBytes.parse bytes).map Json.compress = .ok expected.compress
  artifact : GuardedZkirArtifact.check bytes expected = .ok rows
  ordinary : ∀ row ∈ rows, GuardedImpactTranscript.ordinaryHolds hash assignment row
  consumed : GuardedStatementConsumption.consumeArtifact bytes assignment inputs = some observations

/-- Build the scalar temporaries from the emitted producer rows. The guarded
artifact decoder and transcript checks keep inactive reads and Impact groups
in their original positions. -/
def build (hash : Hash) (seed : Assignment) (bytes : ArtifactBytes.Bytes)
    (expected : Json) (inputs : Inputs) :
    Except String (Checked hash seed bytes expected inputs) := do
  match parsed : ArtifactBytes.parse bytes with
  | .error reason => throw reason
  | .ok json =>
    -- Both copy and constrain_eq decode to equality. Assembly also needs the
    -- original producer tags to distinguish definitions from constraints.
    if same : json.compress = expected.compress then
      match artifact : GuardedZkirArtifact.check bytes expected with
      | .error reason => throw reason
      | .ok rows =>
        let view ← GuardedZkirArtifact.decodeView expected
        let rawRows ← Native.arrayField expected "instructions"
        let ⟨assignment, frame⟩ ← GuardedScalarWitnessAssembly.assemble
          hash seed view.header.arguments rawRows.toList
        if ordinary : GuardedScalarWitnessCheck.check hash assignment rows = true then
          match consumed : GuardedStatementConsumption.consumeArtifact bytes assignment inputs with
          | none => throw "guarded witness does not consume the supplied transcript"
          | some observations =>
            pure ⟨assignment, rows, observations, frame, by simp [parsed, same, Except.map], artifact,
              GuardedScalarWitnessCheck.check_sound hash assignment rows ordinary, consumed⟩
        else
          throw "guarded witness does not satisfy the emitted scalar constraints"
    else
      throw "guarded artifact JSON differs from the emitted program"

private def sourceInput (values : EvalEnv) (input : Input) :
    Except String (String × Scalar) := do
  let some raw := values.lookup input.name | throw s!"missing scalar input '{input.name}'"
  let some packed := ImpactTypedEnvironment.packedCanonical? input.ty raw
    | throw s!"invalid scalar input '{input.name}'"
  pure ("%input_" ++ input.name, scalar (GenericStateEncoding.number input.ty packed.val))

structure SourceCall (hash : Hash) (bytes : ArtifactBytes.Bytes) where
  expected : Json
  seed : Assignment
  transcript : Inputs
  checked : Checked hash seed bytes expected transcript

/-- Derive scalar call inputs and ledger reads from source execution. Build
the witness against the compiler's guarded artifact and the matching VM
transcript. The source and VM frames must encode the same successor. -/
def buildSourceCall (ctx : EvalContext) (hash : Hash) (state : List StateDecl)
    (sourceEntry : Entrypoint) (values : EvalEnv) (initial : LedgerState)
    (bytes : ArtifactBytes.Bytes) (rewrites : Zkir.Rewrites := .disabled) :
    Except String (SourceCall hash bytes) := do
  let ep := Passes.pruneEntrypoint sourceEntry
  let expected ← (Zkir.lowerEntrypoint state sourceEntry rewrites).mapError Diagnostic.message
  let plan ← (Impact.lower state ep).mapError Diagnostic.message
  let sourceInputs ← ep.circuit.inputs.mapM (sourceInput values)
  let outputs ← sourceEntry.circuit.run ctx values
  let cutoff := Impact.publicInputReadCount ep.circuit.inputs
  let (entries, sourceAfter) ← ScalarSourceReadTape.sourceReadInputs ctx ep.effectGuards
    ep.effects.zipIdx cutoff (outputs ++ values, initial)
  let descriptors := plan.reads.drop cutoff
  let metadata := GenericStateCheckedReadTrace.readMetadata
  unless descriptors.map metadata == entries.map (metadata ∘ Prod.fst) do
    throw "source read records differ from the accepted Impact descriptors"
  let seed := seedReadValues (fun name => (sourceInputs.lookup name).getD zero) entries
  let reads ← GenericStateInputValues.decodeReads descriptors seed
  let ops ← GuardedPlanExecution.evalPlan ctx ((outputs ++ values) ++ reads) plan
  let some slots := GenericStateEncoding.encodeInitialState state initial
    | throw "initial state cannot be encoded for a scalar call"
  let some final := NativeState.run ops (GenericStateEncoding.initial slots)
    | throw "scalar VM rejected the source call"
  let some sourceSlots := GenericStateEncoding.encodeState state sourceAfter.2
    | throw "source successor cannot be encoded for a scalar call"
  unless final.stack == [.vector sourceSlots] do
    throw "scalar VM successor differs from the encoded source successor"
  let transcript := ⟨ops.flatMap ImpactStatementScalar.opFields,
    final.reads.map NativeState.Cell.value⟩
  let checked ← build hash seed bytes expected transcript
  pure ⟨expected, seed, transcript, checked⟩

/-- Assembling the proof temporaries preserves the checked source read tape.
The accepted plan fixes the descriptor names, types and order. -/
theorem Checked.source_read_values (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan)
    (ctx : EvalContext) (inputs : Assignment)
    (initial final : SourceEffects.Frame) (records : List (Impact.Read × Scalar))
    (lowered : Impact.lower state ep = .ok plan)
    (effects : ∀ effect ∈ ep.effects, ScalarGuardedPlanAdmission.ScalarEffect state effect)
    (recorded : ScalarSourceReadTape.sourceReadInputs ctx ep.effectGuards ep.effects.zipIdx
       (Impact.publicInputReadCount ep.circuit.inputs) initial = .ok (records, final))
    {hash : Hash} {bytes : ArtifactBytes.Bytes} {expected : Json} {transcript : Inputs}
    (built : Checked hash (seedReadValues inputs records) bytes expected transcript) :
    let reads := plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)
    (∀ input ∈ ep.circuit.inputs,
      built.assignment ("%input_" ++ input.name) = inputs ("%input_" ++ input.name)) ∧
    ∃ readValues,
      GenericStateInputValues.decodeReads reads built.assignment = .ok readValues ∧
      readValues.map Prod.fst = records.map (fun record => record.1.name) := by
  obtain ⟨_, _, preserved, readValues, decoded, order, _⟩ :=
    ScalarSourceReadWitness.lower_source_read_witness state ep plan ctx inputs initial final
      records lowered effects recorded
  refine ⟨fun input present => (built.inputFrame input.name).trans (preserved input present),
    readValues, ?_, order⟩
  rw [GenericStateInputValues.decodeReads_input_frame _ _ _ built.inputFrame]
  exact decoded

end Noctium.Verification.GuardedScalarWitness
