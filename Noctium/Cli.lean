import Noctium.Target
import Noctium.ArtifactRole

namespace Noctium.Cli

def version : String := "0.1.0"

def usage : String := "Noctium " ++ version ++ "\n\
Usage: noctium --version\n\
       noctium profiles\n\
       noctium check <file> [--target <manifest>]\n\
       noctium compile <file> [--target <manifest>] [--emit <role>]... [--bindings rust]\n\
                       [--dedup-range-checks | --ledger-read-bound <Contract.entrypoint>] [--output <new-or-empty-directory>]\n\
Artifact roles: ledger, standalone, witness, control, specialization, observations.\n\
Omit --emit to generate all applicable roles.\n\
Default target: profiles/midnight-ledger-9.json\n\
The selectable ZKIR 3.2.1 profile qualifies a selected native subset only."

structure Options where
  input : String
  target : String := "profiles/midnight-ledger-9.json"
  output : String := "build/noctium"
  emit : List ArtifactRole := []
  rustBindings : Bool := false
  dedupRangeChecks : Bool := false
  ledgerReadBound : Option String := none
  deriving Repr

private def parseOptions (input : String) (args : List String) (compiling : Bool) :
    Except String Options := go { input } args false false
where
  go (opts : Options) (args : List String) (hasTarget hasOutput : Bool) :
      Except String Options :=
    match args with
    | [] => do
      ArtifactRole.validateSelection opts.emit opts.rustBindings
      pure opts
    | "--target" :: value :: rest =>
      if hasTarget then .error "duplicate --target option"
      else if value.startsWith "--" then .error "--target requires a manifest path"
      else go { opts with target := value } rest true hasOutput
    | "--output" :: value :: rest =>
      if !compiling then .error "--output is only supported by compile"
      else if hasOutput then .error "duplicate --output option"
      else if value.startsWith "--" then .error "--output requires a directory"
      else go { opts with output := value } rest hasTarget true
    | "--emit" :: value :: rest => do
      unless compiling do throw "--emit is only supported by compile"
      let role ← ArtifactRole.parse value
      if opts.emit.contains role then throw s!"duplicate artifact role '{value}'"
      go { opts with emit := role :: opts.emit } rest hasTarget hasOutput
    | "--bindings" :: value :: rest => do
      unless compiling do throw "--bindings is only supported by compile"
      unless value == "rust" do throw s!"unsupported binding target '{value}'"
      if opts.rustBindings then throw "duplicate binding target 'rust'"
      go { opts with rustBindings := true } rest hasTarget hasOutput
    | "--dedup-range-checks" :: rest => do
      unless compiling do throw "--dedup-range-checks is only supported by compile"
      if opts.dedupRangeChecks then throw "duplicate --dedup-range-checks option"
      go { opts with dedupRangeChecks := true } rest hasTarget hasOutput
    | "--ledger-read-bound" :: value :: rest => do
      unless compiling do throw "--ledger-read-bound is only supported by compile"
      if opts.ledgerReadBound.isSome then throw "duplicate --ledger-read-bound option"
      if value.isEmpty || value.startsWith "--" then throw "--ledger-read-bound requires Contract.entrypoint"
      go { opts with ledgerReadBound := some value } rest hasTarget hasOutput
    | ["--ledger-read-bound"] => .error "--ledger-read-bound requires Contract.entrypoint"
    | ["--target"] => .error "--target requires a manifest path"
    | ["--output"] => .error "--output requires a directory"
    | ["--emit"] => .error "--emit requires an artifact role"
    | ["--bindings"] => .error "--bindings requires a language target"
    | arg :: _ => .error s!"unexpected argument '{arg}'"

private def error (message : String) : IO UInt32 := do
  (← IO.getStderr).putStrLn s!"noctium: error: {message}"
  return 1

private def runFrontend (input source command : String) : IO IO.Process.Output := do
  -- Only load a library Lake considers current for this workspace.
  let shared ← IO.Process.output {cmd := "lake", args := #["--no-build", "-J", "query", "Noctium:shared"]}
  let mut args := #["env", "lean"]
  if shared.exitCode == 0 then
    if let .ok (.str path) := Lean.Json.parse shared.stdout then
      args := args.push ("--load-dynlib=" ++ path)
  IO.Process.output
    {cmd := "lake", args := args ++ #["-D", "Elab.async=false", "--stdin", input]}
    (some ("import Noctium.Compiler " ++ source ++ "\n" ++ command ++ "\n"))

private def compile (opts : Options) (source profileLiteral : String) : IO IO.Process.Output := do
  let path : System.FilePath := opts.output
  let path := System.FilePath.mk
    ((path.normalize.toString.dropEndWhile (· == System.FilePath.pathSeparator)).toString)
  unless path.fileName.isSome do
    throw (IO.userError "--output requires a new or empty directory")
  if ← path.pathExists then
    unless (← path.isDir) && (← path.readDir).isEmpty do
      throw (IO.userError s!"output '{opts.output}' must be a new or empty directory")
  let parent := path.parent.getD "."
  IO.FS.createDirAll parent
  let stage := parent / s!".noctium-{← IO.Process.getPID}-{← IO.monoNanosNow}"
  IO.FS.createDir stage
  let result ← try
    let directory := (Lean.toJson stage.toString).compress
    let display := (Lean.toJson opts.output).compress
    let roles := (Lean.toJson (Lean.toJson (opts.emit.map ArtifactRole.label)).compress).compress
    let bindings := if opts.rustBindings then "\"rust\"" else "\"\""
    let optimization := if opts.dedupRangeChecks then "\"dedup-range-checks\"" else "\"\""
    let ledgerReadBound := (Lean.toJson (opts.ledgerReadBound.getD "")).compress
    let result ← runFrontend opts.input source
      s!"#noctium_compile_target {directory} {profileLiteral} {display} {roles} {bindings} {optimization} {ledgerReadBound}"
    if result.exitCode == 0 then
      unless ← (stage / "noctium.json").pathExists do
        throw (IO.userError "Lean exited before producing Noctium artifacts")
      -- Publish the complete bundle only after Lean has reported all source diagnostics.
      IO.FS.rename stage path
    pure result
  finally
    if ← stage.pathExists then IO.FS.removeDirAll stage
  return result

private def process (opts : Options) (compiling : Bool) : IO UInt32 := do
  let profile ← match ← TargetProfile.load opts.target with
  | .error message => return ← error message
  | .ok profile => pure profile
  let profileJson := (Lean.toJson profile).compress
  let profileLiteral := (Lean.toJson profileJson).compress
  let source ← try IO.FS.readFile opts.input catch _ =>
    return ← error s!"cannot read source '{opts.input}'"
  if source.trimAscii.toString.startsWith "module" then
    return ← error "Lean module-mode files are not part of the current Noctium source surface"
  -- Lean accepts a filename with --stdin. This keeps module identity and source diagnostics,
  -- avoids a temporary source file, and preserves line numbers by placing the extra import
  -- on the original first line. Inputs are trusted Lean source, like `lake env lean` itself.
  let result ← try
    if compiling then compile opts source profileLiteral
    else runFrontend opts.input source s!"#noctium_check_target {profileLiteral}"
  catch e => return ← error e.toString
  (← IO.getStdout).putStr result.stdout
  (← IO.getStderr).putStr result.stderr
  return result.exitCode

def run (args : List String) : IO UInt32 := do
  match args with
  | [] | ["--help"] | ["-h"] =>
    IO.println usage
    return 0
  | ["--version"] =>
    IO.println s!"Noctium {version} (Lean {Lean.versionString})"
    return 0
  | ["profiles"] =>
    IO.println "midnight-ledger-9 profiles/midnight-ledger-9.json source-baseline-unqualified"
    IO.println "midnight-ledger-9-zkir-3.2.1 profiles/midnight-ledger-9-zkir-3.2.1-target.json selected-native-subset-qualified"
    return 0
  | command :: input :: rest =>
    if command != "check" && command != "compile" then
      return ← error s!"unknown command '{command}'"
    if input.startsWith "--" then return ← error "expected a source path"
    match parseOptions input rest (command == "compile") with
    | .error message => return ← error message
    | .ok opts => process opts (command == "compile")
  | ["check"] | ["compile"] => error "expected a source path"
  | command :: _ => error s!"unknown command '{command}'"

end Noctium.Cli
