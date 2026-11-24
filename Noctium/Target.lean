import Lean
import Lake.Util.Version

register_option noctium.requiredTarget : String := {
  defValue := ""
  descr := "Exact Midnight target profile required by this Noctium source file"
}

namespace Noctium

open Lean Elab Command

/-- Noctium's public Lean source API version. This is independent of native targets. -/
def sourceApiVersion : Lake.StdVer := { major := 0, minor := 1, patch := 0 }

private def normalizeSourceVersion (version : String) : Except String String := do
  let parts := (version.trimAscii.toString.splitOn ".").toArray
  unless parts.size == 2 || parts.size == 3 do
    throw s!"expected a two- or three-component version, got '{version}'"
  let numbers ← parts.mapM fun part =>
    match part.toNat? with
    | some number => pure number
    | none => throw s!"invalid source API version '{version}'"
  return s!"{numbers[0]!}.{numbers[1]!}.{numbers[2]?.getD 0}"

/-- Parse exact versions and Lake SemVer ranges for Noctium's source API. -/
def parseSourceApiRequirement (source : String) : Except String Lake.VerRange := do
  let text := source.trimAscii.toString
  if text.isEmpty then throw "source API version requirement is empty"
  let parts := text.splitOn "."
  if (parts.length == 2 || parts.length == 3) && parts.all (·.toNat?.isSome) then
    Lake.VerRange.parse ("=" ++ (← normalizeSourceVersion text))
  else
    Lake.VerRange.parse text

structure SourceApiRequirement where
  moduleName : Name
  expression : String

private initialize moduleSourceApiRequirements : SimplePersistentEnvExtension
    SourceApiRequirement (Array SourceApiRequirement) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

def sourceApiRequirements (env : Environment) : Array SourceApiRequirement :=
  moduleSourceApiRequirements.getState env

elab "noctium_require_source_api" requirement:str : command => do
  let expression := requirement.getString
  match parseSourceApiRequirement expression with
  | .error error => throwErrorAt requirement "invalid Noctium source API requirement: {error}"
  | .ok _ => pure ()
  let moduleName ← getMainModule
  modifyEnv fun env => moduleSourceApiRequirements.addEntry env {moduleName, expression}

def checkSourceApiRequirements (env : Environment) : CommandElabM Unit := do
  for requirement in sourceApiRequirements env do
    let expression := requirement.expression
    let range ← match parseSourceApiRequirement expression with
      | .ok range => pure range
      | .error error => throwError "invalid Noctium source API requirement '{expression}': {error}"
    unless range.test sourceApiVersion do
      throwError "Noctium module '{requirement.moduleName}' requires source API '{expression}', current version is {sourceApiVersion}"

/-- The upstream source identity used by the selected native toolchain profile. -/
structure NativeSourcePin where
  repository : String
  tag : String
  revision : String
  declaredCrateVersion : String
  reportedCliVersion : String
  deriving Repr, BEq, Lean.FromJson, Lean.ToJson

/-- Components are pinned independently. Producer format and binary release are distinct. -/
structure TargetProfile where
  schemaVersion : Nat
  name : String
  ledger : String
  zkir : String
  circuits : String
  zkStdlib : String
  proofServer : String
  onchainRuntime : String
  qualification : String
  nativeSource : Option NativeSourcePin := none
  deriving Repr, BEq

namespace TargetProfile

/-- Source baseline retained for the default 3.2.0 output. -/
def sourceBaseline : TargetProfile := {
  schemaVersion := 1
  name := "midnight-ledger-9"
  ledger := "9.1.0.1"
  zkir := "3.2.0"
  circuits := "7.3.0"
  zkStdlib := "2.4.0"
  proofServer := "9.0.0"
  onchainRuntime := "4.0.1"
  qualification := "source-baseline-unqualified"
}

def native321Source : NativeSourcePin := {
  repository := "https://github.com/midnightntwrk/midnight-zkir"
  tag := "zkir-3.2.1"
  revision := "7a51b3385bbf4bce3604df87a7c70867c9ab43c0"
  declaredCrateVersion := "3.2.0"
  reportedCliVersion := "midnight-zkir 3.2.0"
}

def selected321 : TargetProfile := {
  schemaVersion := 1
  name := "midnight-ledger-9-zkir-3.2.1"
  ledger := "9.1.0.1"
  zkir := "3.2.1"
  circuits := "7.3.0"
  zkStdlib := "2.4.0"
  proofServer := "9.0.0"
  onchainRuntime := "4.0.1"
  qualification := "selected-native-subset-qualified"
  nativeSource := some native321Source
}

def supportsName (name : String) : Bool :=
  name == sourceBaseline.name || name == selected321.name

end TargetProfile

structure SourceTargetRequirement where
  moduleName : Name
  profileName : String

private initialize moduleTargetRequirements : SimplePersistentEnvExtension
    SourceTargetRequirement (Array SourceTargetRequirement) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

def sourceTargetRequirements (env : Environment) : Array SourceTargetRequirement :=
  moduleTargetRequirements.getState env

/-- Require an exact Midnight profile in this module and its importers. -/
elab "noctium_require_target" profile:str : command => do
  let profileName := profile.getString
  unless TargetProfile.supportsName profileName do
    throwErrorAt profile "unknown Noctium source target requirement '{profileName}'"
  let moduleName ← getMainModule
  modifyEnv fun env => moduleTargetRequirements.addEntry env {moduleName, profileName}

instance : Lean.FromJson TargetProfile where
  fromJson? json := do
    let schemaVersion ← json.getObjValAs? Nat "schemaVersion"
    let name ← json.getObjValAs? String "name"
    let ledger ← json.getObjValAs? String "ledger"
    let zkir ← json.getObjValAs? String "zkir"
    let circuits ← json.getObjValAs? String "circuits"
    let zkStdlib ← json.getObjValAs? String "zkStdlib"
    let proofServer ← json.getObjValAs? String "proofServer"
    let onchainRuntime ← json.getObjValAs? String "onchainRuntime"
    let qualification ← json.getObjValAs? String "qualification"
    let nativeSource ← match json.getObjVal? "nativeSource" with
      | .ok .null => pure none
      | .ok value => some <$> Lean.fromJson? value
      | .error _ => pure none
    return {
      schemaVersion, name, ledger, zkir, circuits, zkStdlib, proofServer,
      onchainRuntime, qualification, nativeSource
    }

instance : Lean.ToJson TargetProfile where
  toJson profile := Lean.Json.mkObj <| [
    ("schemaVersion", Lean.toJson profile.schemaVersion),
    ("name", Lean.toJson profile.name),
    ("ledger", Lean.toJson profile.ledger),
    ("zkir", Lean.toJson profile.zkir),
    ("circuits", Lean.toJson profile.circuits),
    ("zkStdlib", Lean.toJson profile.zkStdlib),
    ("proofServer", Lean.toJson profile.proofServer),
    ("onchainRuntime", Lean.toJson profile.onchainRuntime),
    ("qualification", Lean.toJson profile.qualification)
  ] ++ profile.nativeSource.toList.map fun source => ("nativeSource", Lean.toJson source)

def TargetProfile.validate (profile : TargetProfile) : Except String TargetProfile := do
  unless profile.schemaVersion == 1 do
    throw "unsupported target profile schema version"
  unless profile.ledger == "9.1.0.1" && profile.circuits == "7.3.0" &&
      profile.zkStdlib == "2.4.0" && profile.proofServer == "9.0.0" &&
      profile.onchainRuntime == "4.0.1" do
    throw "target component versions do not match a supported ledger 9 profile"
  if profile.name == "midnight-ledger-9" then
    unless profile.zkir == "3.2.0" do
      throw "target component versions do not match the ledger 9 source baseline"
    unless profile.qualification == "source-baseline-unqualified" do
      throw "target qualification must be source-baseline-unqualified for the default profile"
    unless profile.nativeSource.isNone do
      throw "the default target profile cannot declare a native source pin"
  else if profile.name == "midnight-ledger-9-zkir-3.2.1" then
    unless profile.zkir == "3.2.1" do
      throw "target component versions do not match the selected ZKIR 3.2.1 profile"
    unless profile.qualification == "selected-native-subset-qualified" do
      throw "target qualification must be selected-native-subset-qualified for ZKIR 3.2.1"
    unless profile.nativeSource == some TargetProfile.native321Source do
      throw "ZKIR 3.2.1 requires the pinned midnight-zkir source identity"
  else
    throw "unsupported target profile name"
  return profile

def TargetProfile.parse (source : String) : Except String TargetProfile := do
  let json ← Lean.Json.parse source
  let profile : TargetProfile ← Lean.fromJson? json
  profile.validate

def TargetProfile.load (path : System.FilePath) : IO (Except String TargetProfile) := do
  try
    return TargetProfile.parse (← IO.FS.readFile path)
  catch _ =>
    return .error s!"cannot read target manifest '{path}'"

end Noctium
