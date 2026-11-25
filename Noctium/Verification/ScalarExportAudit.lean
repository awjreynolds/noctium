import Noctium.Verification
import Noctium.Verification.ScalarCircuitWitness
import Lean.Replay
import LeanExport.Parse

namespace Noctium.Verification.ScalarExportAudit
open Lean

private def soundnessAnchor : Name := `Noctium.Verification.ScalarTranslationSoundness.lowerCircuit_sound
private def completenessAnchor : Name := `Noctium.Verification.ScalarWitnessConstruction.lowerCircuit_complete

private def load (path : System.FilePath) : IO LeanExport.ExportedEnv := do
  unless (← path.metadata).byteSize ≤ 160 * 1024 * 1024 do
    throw (IO.userError "export_limit")
  IO.FS.withFile path .read fun handle => LeanExport.parseStream (.ofHandle handle)

private def merge (model candidate : Std.HashMap Name ConstantInfo) : Except String (Std.HashMap Name ConstantInfo) := do
  let mut result := candidate
  for (name, trusted) in model.toList do
    if let some supplied := candidate[name]? then
      unless supplied == trusted do throw s!"model_declaration_mismatch: {name}"
    result := result.insert name trusted
  return result

private def replay (constants : Std.HashMap Name ConstantInfo) : IO Environment := do
  let primitives := [`Quot.mk, `Quot.lift, `Quot.ind]
  let checked ← (← mkEmptyEnvironment).toKernelEnv.replay (primitives.foldl (fun values name => values.erase name) constants)
  for name in `Quot :: primitives do
    if let some supplied := constants[name]? then
      unless checked.find? name == some supplied do throw (IO.userError "quotient_declaration_mismatch")
  return .ofKernelEnv checked

private def parseName (text : String) : IO Name := do
  let some name := Syntax.decodeNameLit ("`" ++ text) | throw (IO.userError "invalid_name")
  if name.isAnonymous then throw (IO.userError "invalid_name")
  return name

private def checkRole (environment : Environment) (proof anchor : Name) (role : String) : IO (Array Name) := do
  let some trusted := environment.toKernelEnv.find? anchor | throw (IO.userError s!"missing_trusted_role: {role}")
  let some candidate := environment.toKernelEnv.find? proof | throw (IO.userError s!"missing_proof: {role}")
  unless trusted.levelParams.isEmpty && candidate.levelParams.isEmpty do
    throw (IO.userError s!"polymorphic_role: {role}")
  match candidate with
  | .thmInfo _ => pure ()
  | _ => throw (IO.userError s!"proof_must_be_theorem: {role}")
  match Kernel.isDefEq environment {} candidate.type trusted.type with
  | .ok true => pure ()
  | _ => throw (IO.userError s!"wrong_statement: {role}")
  match Audit.axiomsIn environment proof with
  | .ok axioms => return axioms
  | .error error => throw (IO.userError error)

/-- Check exported data in a fresh kernel environment. The caller must pin the
model bytes independently. Candidate modules and initializers are never loaded. -/
def run (args : List String) : IO UInt32 := do
  try
    let (modelPath, proofPath, soundnessName, completenessName) ← match args with
      | [model, proof, soundness, completeness] => pure (model, proof, soundness, completeness)
      | _ => throw (IO.userError "usage: AuditScalarExport MODEL PROOFS SOUNDNESS_PROOF COMPLETENESS_PROOF")
    let model ← load modelPath
    let candidate ← load proofPath
    for name in Audit.approvedAxioms ++ [soundnessAnchor, completenessAnchor] do
      unless model.constMap.contains name do throw (IO.userError s!"missing_trusted_model_root: {name}")
    let soundnessProof ← parseName soundnessName
    let completenessProof ← parseName completenessName
    for (name, role) in [(soundnessProof, "soundness"), (completenessProof, "completeness")] do
      unless candidate.constMap.contains name do throw (IO.userError s!"missing_proof: {role}")
    let constants ← match merge model.constMap candidate.constMap with
      | .ok values => pure values
      | .error error => throw (IO.userError error)
    let environment ← replay constants
    let soundness ← checkRole environment soundnessProof soundnessAnchor "soundness"
    let completeness ← checkRole environment completenessProof completenessAnchor "completeness"
    IO.println (Json.mkObj [
      ("status", toJson ("scalar-circuit-lowering-proofs-checked" : String)),
      ("soundnessProof", toJson soundnessName), ("completenessProof", toJson completenessName),
      ("axioms", toJson (((soundness ++ completeness).toList.eraseDups.mergeSort Name.lt).map Name.toString)),
      ("statementComparison", toJson ("kernel definitional equality to externally pinned model roles" : String)),
      ("externalModelPinRequired", toJson true), ("wholeCompilerVerified", toJson false),
      ("ledgerStatePreservationProved", toJson false), ("deployedIdentityVerified", toJson false)]).compress
    return 0
  catch error =>
    IO.eprintln (Json.mkObj [("status", toJson ("rejected" : String)), ("error", toJson (toString error))]).compress
    return 1

end Noctium.Verification.ScalarExportAudit
