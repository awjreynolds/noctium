import Noctium.Control
import Noctium.Witness.Ledger
import Noctium.Backend.Zkir
import Noctium.NativeExpression

namespace Noctium.Witness
open Lean Helpers

private def fail (span : SourceSpan) (message : String) : Except Diagnostic α :=
  .error {span, message}

/-- Private stages remain in the host plan. Their computations remain in the
constraint program, without claiming the private write is circuit-proved. -/
def eraseStages : List Statement → List Statement
  | [] => []
  | .stage _ _ _ value :: rest => .evaluate value :: eraseStages rest
  | .branch condition yes no :: rest =>
    .branch condition (eraseStages yes) (eraseStages no) :: eraseStages rest
  | .forRange index start stop body :: rest =>
    .forRange index start stop (eraseStages body) :: eraseStages rest
  | statement :: rest => statement :: eraseStages rest
termination_by body => sizeOf body

def eraseProgram (program : Program) : Program :=
  Helpers.mapDeclarationBodies eraseStages program

private def scalarName : Ty → String
  | .native => "Native"
  | .bool => "Bool"
  | .uint maximum => s!"UIntRange<{maximum + 1}>"
  | .bytes 32 => "Bytes<32>"
  | .bytes length => s!"Bytes<{length}>"
  | .opaqueBytes => "OpaqueBytes"
  | .opaqueString => "OpaqueString"
  | .jubjubScalar => "JubjubScalar"
  | .jubjubPoint => "JubjubPoint"
  | .foreign kind => kind.sourceName

private def idName (id : DeclarationId) : String := s!"s{id.scope}d{id.ordinal}"

private def setField (json : Json) (name : String) (value : Json) : Except Diagnostic Json := do
  let object ← (json.getObj?).mapError fun _ => {span := {}, message := "invalid witness artifact object"}
  pure (Json.mkObj ((object.toList.filter (·.1 != name)) ++ [(name, value)]))

private def arrayField (json : Json) (name : String) : Except Diagnostic (Array Json) :=
  ((json.getObjVal? name).bind Json.getArr?).mapError fun _ =>
    {span := {}, message := "missing typed control metadata"}

private def resultToken (program : Program) (plan : Json) (span : SourceSpan)
    (type : ResultType) : Except Diagnostic String := do
  match type with
  | .unit => pure "Unit"
  | .scalar type => pure (scalarName type)
  | .composite type =>
    let compiled ← (Types.compileType program.composites type).mapError fun diagnostic =>
      {span, message := diagnostic.message}
    for entry in (← arrayField plan "types") do
      if ((entry.getObjVal? "schema").bind (·.getObjValAs? String "typeFingerprint")).toOption == some compiled.fingerprint then
        match entry.getObjValAs? String "id" with
        | .ok id => return "Aggregate:" ++ id
        | .error _ => fail span "invalid typed control schema identity"
    fail span "typed witness result schema is absent from control plan"

private def inputBindings (program : Program) (plan : Json) (entry : Export) : Except Diagnostic Json := do
  let some declaration := program.declarations.find? (·.id == entry.target)
    | fail entry.span "missing witness entry declaration"
  let mut scalarInputs := entry.inputs
  let mut aggregateInputs := entry.compositeInputs
  let mut bindings := []
  for parameter in declaration.parameters do
    let (name, type, names) ← match declaration.parameterType parameter with
      | .scalar _ => do
        let some input := scalarInputs.head? | fail entry.span "witness source input mismatch"
        scalarInputs := scalarInputs.drop 1
        pure (input.name, ResultType.scalar input.ty, [input.name])
      | .composite _ => do
        let some input := aggregateInputs.head? | fail entry.span "witness source input mismatch"
        aggregateInputs := aggregateInputs.drop 1
        let compiled ← (Types.compileType program.composites input.type).mapError fun diagnostic =>
          {span := input.span, message := diagnostic.message}
        let names := (Helpers.sourceLeafPaths compiled.checked.value "").map fun path => input.name ++ path
        pure (input.name, ResultType.composite input.type, names)
      | .unit => do
        let some input := aggregateInputs.head? | fail entry.span "witness source input mismatch"
        aggregateInputs := aggregateInputs.drop 1
        unless input.type == .unit do fail input.span "witness Unit input type mismatch"
        pure (input.name, .unit, [])
    bindings := bindings ++ [Json.mkObj [("name", toJson name),
      ("type", toJson (← resultToken program plan entry.span type)), ("inputs", toJson names)]]
  pure (toJson bindings)

structure Compiled where
  circuit : Circuit
  plan : Json
  binding : Json
  calls : List Helpers.WitnessCallBinding := []

private def boundedNativePlan (plan binding : Json) : Except Diagnostic Json := do
  let text := binding.compress ++ "\n"
  if text.utf8ByteSize > 524288 then fail {} "witness binding exceeds byte limit"
  let plan ← setField plan "mode" (toJson ("native" : String))
  let plan ← setField plan "binding" (toJson text)
  if plan.compress.utf8ByteSize > 1048576 then fail {} "bound witness plan exceeds byte limit"
  pure plan

private def bindHosted (program : Program) (entry : Export) (entryName : String)
    (plan : Json) (circuit : Circuit) (calls : List Helpers.WitnessCallBinding)
    (native : Json) (bindingOutputs : List Output) (forceGuards : Bool := false) :
    Except Diagnostic Compiled := do
  let guardedCalls := forceGuards || calls.any (·.guarded)
  let mut callRows := []
  for call in calls do
    let fields := [("ordinal", toJson (toString call.ordinal)), ("site", toJson call.site),
      ("name", toJson call.name), ("path", toJson (call.path.map idName)),
      ("resultType", toJson (← resultToken program plan entry.span call.result)),
      ("inputs", toJson call.inputs)]
    let fields := if guardedCalls then fields ++
      [("guard", Noctium.NativeExpression.toJson call.guard)] else fields
    callRows := callRows ++ [Json.mkObj fields]
  let binding := Json.mkObj [("schemaVersion", toJson ((if guardedCalls then 2 else 1) : Nat)),
    ("kind", toJson ("typed-witness-bindings" : String)), ("circuitName", toJson circuit.name),
    ("sourceExport", toJson entryName), ("target", Json.mkObj [("kind", toJson ("standalone" : String))]),
    ("types", toJson (← arrayField plan "types")), ("signatures", toJson (← arrayField plan "witnesses")),
    ("inputBindings", ← inputBindings program plan entry),
    ("circuitInputs", toJson (circuit.inputs.map fun input => Json.mkObj [("name", toJson input.name),
      ("type", toJson (scalarName input.ty)), ("visibility", toJson (if input.visibility == .public then "public" else "private"))])),
    ("circuitOutputs", toJson (bindingOutputs.map fun output => Json.mkObj [("name", toJson output.name),
      ("type", toJson (scalarName output.ty))])),
    ("calls", toJson callRows), ("nativeRelation", native)]
  pure {circuit, binding, calls, plan := ← boundedNativePlan plan binding}

/-- The native workflow requires declared providers and an exact ordered map
from executed calls to actual fresh private inputs. Host-only control is separate. -/
def compileWithLimits (limits : Helpers.Limits) (program : Program) (entryName : String)
    (circuitName : String := "") (outputName : String := "")
    (rewrites : Backend.Zkir.Rewrites := .disabled)
    (assertionDiagnostics : List (SourceSpan × String) := []) : Except Diagnostic Compiled := do
  let program ← Helpers.prepareProgramWithLimits limits program
  let plan ← Control.compileTypedWithLimits limits program entryName 1048576 assertionDiagnostics
  let some entry := program.exports.find? (·.name == entryName) | fail {} "unknown witness entrypoint"
  let lowered ← Helpers.compileHostedWitnessWithLimits limits (eraseProgram program) entryName
  let mut circuit := if circuitName.isEmpty then lowered.circuit else {lowered.circuit with name := circuitName}
  unless outputName.isEmpty do
    let some declaration := program.declarations.find? (·.id == entry.target)
      | fail entry.span "missing witness entry declaration"
    unless (match declaration.result with | .scalar _ => true | _ => false) do
      fail entry.span "named witness outputs require one scalar result"
    let [output] := circuit.outputs | fail entry.span "named witness outputs require one scalar result"
    if circuit.inputs.any (·.name == outputName) then
      fail entry.span "witness output name collides with an input"
    circuit := {circuit with outputs := [{output with name := outputName}]}
  let native ← Backend.Zkir.lowerCircuit circuit rewrites
  bindHosted program entry entryName plan circuit lowered.calls native circuit.outputs

def compile (program : Program) (entryName : String) (circuitName : String := "")
    (outputName : String := "") (rewrites : Backend.Zkir.Rewrites := .disabled)
    (assertionDiagnostics : List (SourceSpan × String) := []) : Except Diagnostic Compiled :=
  compileWithLimits {} program entryName circuitName outputName rewrites assertionDiagnostics

/-- Bind the same source invocation to the actual ledger call relation, rather
than substituting the standalone relation's public-return convention. -/
def bindEntrypoint (compiled : Compiled) (relation : Json) (contractName entrypoint nativeCircuitFile targetProfile : String)
    (ledgerInputs : List (String × Ty) := []) (callInputs : List String := []) :
    Except Diagnostic Compiled := do
  let mut binding ← setField compiled.binding "nativeRelation" relation
  unless ledgerInputs.isEmpty do
    for (_, ty) in ledgerInputs do
      (ty.validate Capabilities.crypto).mapError fun message => {span := {}, message}
    binding ← setField binding "ledgerInputs" (toJson (ledgerInputs.map fun (name, ty) =>
      Json.mkObj [("name", toJson name), ("type", toJson (scalarName ty)),
        ("visibility", toJson ("public" : String))]))
  unless callInputs.isEmpty do
    binding ← setField binding "callInputs" (toJson callInputs)
  binding ← setField binding "target" (Json.mkObj [("kind", toJson ("entrypoint" : String)),
    ("contractName", toJson contractName), ("entrypoint", toJson entrypoint),
    ("nativeCircuitFile", toJson nativeCircuitFile), ("targetProfile", toJson targetProfile)])
  pure {compiled with binding, plan := ← boundedNativePlan compiled.plan binding}

structure CompiledEntrypoint where
  entrypoint : Entrypoint
  witness : Compiled

/-- Host execution is needed for provider calls and invocation-local private stages. -/
def needsLedgerHost (program : Program) : Except Diagnostic Bool := do
  let summaries ← Helpers.analyzeWithLimits {} program
  pure (summaries.any fun summary => summary.effects.any fun effect =>
    effect == .witness || effect == .privateState)

/-- Compile one source body into the typed host scheduler and its native ledger relation. -/
def compileLedger (program : Program) (entryName : String) (ledger : List StateDecl)
    (circuitName : String := "") (rewrites : Backend.Zkir.Rewrites := .disabled) : Except Diagnostic CompiledEntrypoint := do
  let transformed ← Ledger.transform program
  let plan ← Control.compileTypedWithLimits {} transformed.host entryName
  let some entry := transformed.host.exports.find? (·.name == entryName)
    | fail {} "unknown ledger witness entrypoint"
  let lowered ← Helpers.compileHostedEntrypointForWithLimits {} (eraseProgram transformed.native) entryName ledger
  let compiledEntry := if circuitName.isEmpty then lowered.entrypoint else
    {lowered.entrypoint with circuit := {lowered.entrypoint.circuit with name := circuitName}}
  let native ← Backend.Zkir.lowerEntrypoint ledger compiledEntry rewrites
  let (impact, boundaries) ← Backend.Impact.lowerWithEffectBoundaries ledger compiledEntry
  let mut rows := []
  for call in lowered.calls do
    if let some descriptor := transformed.calls.find? (·.site == call.site) then
      let preceding := compiledEntry.effects.take call.effectCount
      let some (effect, index) := (preceding.zipIdx.reverse.find? fun (effect, _) =>
        match effect with | .require _ => false | _ => true)
        | fail entry.span "ledger callback has no preceding state effect"
      let read ← match effect with
        | .readCell state destination ty => do
          unless descriptor.kind == "readCell" && descriptor.state == state && descriptor.valueTy == ty do
            fail entry.span "ledger callback cell read mismatch"
          pure (some destination)
        | .readMap state destination keyTy valueTy _ => do
          unless descriptor.kind == "readMap" && descriptor.state == state &&
              descriptor.keyTy == some keyTy && descriptor.valueTy == valueTy do
            fail entry.span "ledger callback map read mismatch"
          pure (some destination)
        | .readMember state destination keyTy valueTy _ => do
          unless descriptor.kind == "readMember" && descriptor.state == state &&
              descriptor.keyTy == some keyTy && descriptor.valueTy == valueTy do
            fail entry.span "ledger callback membership read mismatch"
          pure (some destination)
        | .writeCell state ty _ => do
          unless descriptor.kind == "writeCell" && descriptor.state == state && descriptor.valueTy == ty do
            fail entry.span "ledger callback cell write mismatch"
          pure none
        | .writeMap state keyTy valueTy _ _ => do
          unless descriptor.kind == "writeMap" && descriptor.state == state &&
              descriptor.keyTy == some keyTy && descriptor.valueTy == valueTy do
            fail entry.span "ledger callback map write mismatch"
          pure none
        | _ => fail entry.span "ledger callback must follow a typed cell or map effect"
      let some operationEnd := boundaries[index]?
        | fail entry.span "ledger callback operation boundary is absent"
      unless operationEnd > 0 && operationEnd ≤ impact.operations.length do
        fail entry.span "ledger callback operation boundary is invalid"
      rows := rows ++ [Json.mkObj [("ordinal", toJson (toString call.ordinal)),
        ("operationEnd", toJson operationEnd), ("read", toJson read)]]
  let compiled ← bindHosted transformed.host entry entryName plan compiledEntry.circuit lowered.calls native
    compiledEntry.returns true
  let binding ← setField compiled.binding "ledgerCalls" (toJson rows)
  let compiled := {compiled with binding, plan := ← boundedNativePlan compiled.plan binding}
  pure {entrypoint := compiledEntry, witness := compiled}

/-- Existing state-only bodies retain their native-only path. -/
def compileStateEntrypointWithWitness (program : Program) (entryName : String)
    (ledger : List StateDecl) (circuitName : String := "") (rewrites : Backend.Zkir.Rewrites := .disabled) :
    Except Diagnostic (Entrypoint × Option Compiled) := do
  if ← needsLedgerHost program then
    let compiled ← compileLedger program entryName ledger circuitName rewrites
    return (compiled.entrypoint, some compiled.witness)
  return (← Helpers.compileEntrypointFor program entryName ledger, none)

def compileStateEntrypoint (program : Program) (entryName : String) (ledger : List StateDecl) :
    Except Diagnostic Entrypoint := do
  return (← compileStateEntrypointWithWitness program entryName ledger).1

end Noctium.Witness
