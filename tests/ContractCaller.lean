import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers

noctium_circuit protectedInput where
  private amount : Native
end

noctium_contract ProtectedCallee where
  cell permitted : Bytes32
  cell enforce : Bool
  cell balance : Native
  entry move uses protectedInput arguments [amount] where
    read permitted as parent
    read enforce as checkCaller
    when checkCaller requireContractCaller(parent)
    read balance as previous
    write balance := disclose(add(previous, amount))
    return result : Native := disclose(add(previous, amount))
  end
end

noctium_circuit forwardingInput where
  public target : Bytes32
  private opening : Native
  private amount : Native
  private expected : Native
end

noctium_contract ForwardingCaller where
  cell marker : Native
  entry forward uses forwardingInput where
    claimContractCall(target,
      disclose(callCommitment(ProtectedCallee, "move", opening, [amount], [expected])))
  end
end

private def helperClaimStatement (discloseOperands : _root_.Bool) : Statement :=
  .claimContractCall
    (if discloseOperands then .disclose {} (.ref "target") else .ref "target")
    (if discloseOperands then .disclose {} (.ref "entryHash") else .ref "entryHash")
    (if discloseOperands then
      .disclose {} (.bytes .transientHashNativeVector
        [.ref "opening", .ref "amount", .ref "expected"])
    else .bytes .transientHashNativeVector
      [.ref "opening", .ref "amount", .ref "expected"])

private def helperForwardingProgramWith (discloseGuard discloseOperands declaredPure : _root_.Bool) : Program := {
  declarations := [
    {id := ⟨0, 0⟩, name := "claimInner",
      parameters := [
        ⟨"target", .bytes 32⟩, ⟨"entryHash", .bytes 32⟩, ⟨"enabled", .bool⟩,
        ⟨"opening", .native⟩, ⟨"amount", .native⟩, ⟨"expected", .native⟩],
      result := .unit,
      body := [
        .branch (if discloseGuard then .disclose {} (.ref "enabled") else .ref "enabled")
          [helperClaimStatement discloseOperands] [],
        .return none]},
    {id := ⟨0, 1⟩, name := "forward", declaredPure,
      parameters := [
        ⟨"target", .bytes 32⟩, ⟨"entryHash", .bytes 32⟩, ⟨"enabled", .bool⟩,
        ⟨"opening", .native⟩, ⟨"amount", .native⟩, ⟨"expected", .native⟩],
      result := .unit,
      body := [
        .evaluate (.call "claimInner" [
          .ref "target", .ref "entryHash", .ref "enabled",
          .ref "opening", .ref "amount", .ref "expected"]),
        .return none]}],
  exports := [{name := "forward", target := ⟨0, 1⟩, inputs := [
    {name := "target", ty := .bytes 32, visibility := .private},
    {name := "entryHash", ty := .bytes 32, visibility := .private},
    {name := "enabled", ty := .bool, visibility := .private},
    {name := "opening", ty := .native, visibility := .private},
    {name := "amount", ty := .native, visibility := .private},
    {name := "expected", ty := .native, visibility := .private}]}]
}

private def helperForwardingProgram : Program :=
  helperForwardingProgramWith _root_.Bool.true _root_.Bool.true _root_.Bool.false

noctium_contract HelperForwardingCaller where
  cell marker : Native
  entry forward from helperForwardingProgram entry "forward" end
end

private def helperForwardingEntry : Noctium.Entrypoint :=
  match HelperForwardingCaller.entrypoints.find? (·.name == "forward") with
  | some found => found
  | none => {name := "missing", circuit := {name := "missing"}}

#guard helperForwardingEntry.circuit.inputs.map (·.name) ==
  ["target", "entryHash", "enabled", "opening", "amount", "expected"]
#guard helperForwardingEntry.circuit.inputs.all (·.visibility == .private)
#guard (helperForwardingEntry.effects.filterMap fun effect =>
  match effect with
  | .require _ => some "require"
  | .claimContractCall .. => some "claimContractCall"
  | _ => none) == ["require", "require", "claimContractCall"]
#guard helperForwardingEntry.effectGuards.length == helperForwardingEntry.effects.length
#guard helperForwardingEntry.effectGuards.all Option.isSome

private def helperUndisclosedGuard : Program :=
  helperForwardingProgramWith _root_.Bool.false _root_.Bool.true _root_.Bool.false
private def helperUndisclosedClaimOperands : Program :=
  helperForwardingProgramWith _root_.Bool.true _root_.Bool.false _root_.Bool.false
private def helperTransitivePureClaim : Program :=
  helperForwardingProgramWith _root_.Bool.true _root_.Bool.true _root_.Bool.true

#guard match Helpers.compileEntrypointFor helperUndisclosedGuard "forward" [] with
  | .error diagnostic => (diagnostic.message.splitOn "undisclosed private control").length > 1
  | .ok _ => _root_.Bool.false
#guard match Helpers.compileEntrypointFor helperUndisclosedClaimOperands "forward" [] with
  | .error diagnostic => (diagnostic.message.splitOn "undisclosed private").length > 1
  | .ok _ => _root_.Bool.false
#guard match Helpers.analyze helperTransitivePureClaim with
  | .error diagnostic => (diagnostic.message.splitOn "transitive effects").length > 1
  | .ok _ => _root_.Bool.false

private def protectedEntry : Noctium.Entrypoint :=
  match ProtectedCallee.entrypoints with
  | value :: _ => value
  | [] => {name := "missing", circuit := {name := "missing"}}

#guard !(Noctium.Disclosure.entrypoint {protectedEntry with
  circuit := {protectedEntry.circuit with inputs := protectedEntry.circuit.inputs ++
    [{name := "secretAddress", ty := .bytes 32, visibility := .private}]},
  effects := protectedEntry.effects.map fun effect => match effect with
    | .requireContractCaller _ => .requireContractCaller (.ref "secretAddress")
    | _ => effect}).isOk
