import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit rawShieldedClaimInputs where
  private digest : Bytes32
end

noctium_circuit guardedRawShieldedClaimInputs where
  private enabled : Bool
  private digest : Bytes32
end

private def rawShieldedReceiveHelper : Helpers.Program := {
  declarations := [
    {id := ⟨0, 0⟩, name := "recordReceive", parameters := [⟨"digest", .bytes 32⟩],
      result := .unit, body := [
        .claimShielded .receive (.disclose {} (.ref "digest")),
        .return none]},
    {id := ⟨0, 1⟩, name := "guardedReceive",
      parameters := [⟨"enabled", .bool⟩, ⟨"digest", .bytes 32⟩],
      result := .unit, body := [
        .branch (.disclose {} (.ref "enabled")) [
          .evaluate (.call "recordReceive" [.ref "digest"])] [],
        .return none]}]
  exports := [{name := "guardedReceive", target := ⟨0, 1⟩, inputs := [
    {name := "enabled", ty := .bool, visibility := .private},
    {name := "digest", ty := .bytes 32, visibility := .private}]}]
}

noctium_contract RawShieldedClaims where
  entry claimNullifier uses rawShieldedClaimInputs where
    claimShielded(nullifier, disclose(digest))
  end

  entry claimNullifierTwice uses rawShieldedClaimInputs where
    claimShielded(nullifier, disclose(digest))
    claimShielded(nullifier, disclose(digest))
  end

  entry claimReceive uses rawShieldedClaimInputs where
    claimShielded(receive, disclose(digest))
  end

  entry claimSpend uses rawShieldedClaimInputs where
    claimShielded(spend, disclose(digest))
  end

  entry guardedClaimReceive uses guardedRawShieldedClaimInputs where
    when disclose(enabled) claimShielded(receive, disclose(digest))
  end

  entry helperClaimReceive from rawShieldedReceiveHelper entry "guardedReceive" end
end

noctium_contract FundedRawShieldedClaim where
  entry helperClaimReceive from rawShieldedReceiveHelper entry "guardedReceive" end
end

private def rawClaimEntry (name : String) : Entrypoint :=
  (RawShieldedClaims.entrypoints.find? fun candidate => candidate.name == name).getD
    {name := "missing", circuit := {name := "missing"}}

private def claimBytes : List Nat := List.replicate 32 7

private def rawClaimContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by raw shielded claim fixture"
  ownContractAddress := some (List.replicate 32 4)
}

private def rawClaimInputs : EvalEnv := [("digest", .bytes 32 claimBytes)]

private def guardedRawClaimInputs (enabled : _root_.Bool) : EvalEnv := [
  ("enabled", .bool enabled), ("digest", .bytes 32 claimBytes)]

#guard (rawClaimEntry "claimNullifier").name == "claimNullifier"
#guard (rawClaimEntry "claimReceive").name == "claimReceive"
#guard (rawClaimEntry "claimSpend").name == "claimSpend"

#guard match (rawClaimEntry "claimNullifier").effects with
  | [.claimShielded .nullifier (.disclose _ (.ref "digest"))] => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match (rawClaimEntry "claimReceive").effects with
  | [.claimShielded .receive (.disclose _ (.ref "digest"))] => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match (rawClaimEntry "claimSpend").effects with
  | [.claimShielded .spend (.disclose _ (.ref "digest"))] => _root_.Bool.true
  | _ => _root_.Bool.false

#guard (Disclosure.entrypoint (rawClaimEntry "claimNullifier")).isOk
#guard (Disclosure.entrypoint (rawClaimEntry "claimNullifierTwice")).isOk
#guard (Disclosure.entrypoint (rawClaimEntry "claimReceive")).isOk
#guard (Disclosure.entrypoint (rawClaimEntry "claimSpend")).isOk
#guard (Disclosure.entrypoint (rawClaimEntry "guardedClaimReceive")).isOk
#guard !(Disclosure.entrypoint {rawClaimEntry "claimReceive" with
  effects := [.claimShielded .receive (.ref "digest")]}).isOk
#guard !(Disclosure.entrypoint {rawClaimEntry "guardedClaimReceive" with
  effectGuards := [some (.ref "enabled")]}).isOk

private def privateHelperGuard : Helpers.Program := {
  rawShieldedReceiveHelper with
  declarations := rawShieldedReceiveHelper.declarations.map fun declaration =>
    if declaration.name == "guardedReceive" then
      {declaration with body := [
        .branch (.ref "enabled") [.evaluate (.call "recordReceive" [.ref "digest"])] [],
        .return none]}
    else declaration
}

private def privateHelperDigest : Helpers.Program := {
  rawShieldedReceiveHelper with
  declarations := rawShieldedReceiveHelper.declarations.map fun declaration =>
    if declaration.name == "recordReceive" then
      {declaration with body := [.claimShielded .receive (.ref "digest"), .return none]}
    else declaration
}

#guard match Helpers.compileEntrypointFor privateHelperGuard "guardedReceive" [] with
  | .error diagnostic => (diagnostic.message.splitOn "undisclosed private control").length > 1
  | .ok _ => _root_.Bool.false
#guard match Helpers.compileEntrypointFor privateHelperDigest "guardedReceive" [] with
  | .error diagnostic => (diagnostic.message.splitOn "undisclosed private").length > 1
  | .ok _ => _root_.Bool.false

private def rawClaimPlanOperation (name : String) : Except String (String × String) := do
  let selected := rawClaimEntry name
  let plan ← (Backend.Impact.lower RawShieldedClaims.state selected).mapError (·.message)
  let json := Compiler.nativePlanJson TargetProfile.selected321 `RawShieldedClaims
    RawShieldedClaims.state none selected plan
  let operations ← json.getObjVal? "operations"
  let .arr operations := operations | throw "native plan operations are not an array"
  let some operation := operations[0]? | throw "native plan has no operation"
  let op ← operation.getObjVal? "op"
  let .str op := op | throw "native operation tag is not a string"
  let kind ← operation.getObjVal? "kind"
  let .str kind := kind | throw "native shielded claim kind is not a string"
  pure (op, kind)

#guard match rawClaimPlanOperation "claimNullifier" with
  | .ok ("claimShielded", "nullifier") => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match rawClaimPlanOperation "claimReceive" with
  | .ok ("claimShielded", "receive") => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match rawClaimPlanOperation "claimSpend" with
  | .ok ("claimShielded", "spend") => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match Entrypoint.run rawClaimContext (rawClaimEntry "claimNullifier") rawClaimInputs {} with
  | .ok state => state.2.shieldedClaims == [(ShieldedClaimKind.nullifier, claimBytes)]
  | .error _ => _root_.Bool.false
#guard match Entrypoint.run rawClaimContext (rawClaimEntry "claimNullifierTwice") rawClaimInputs {} with
  | .ok state => state.2.shieldedClaims == [(ShieldedClaimKind.nullifier, claimBytes)]
  | .error _ => _root_.Bool.false
#guard match Entrypoint.run rawClaimContext (rawClaimEntry "claimReceive") rawClaimInputs {} with
  | .ok state => state.2.shieldedClaims == [(ShieldedClaimKind.receive, claimBytes)]
  | .error _ => _root_.Bool.false
#guard match Entrypoint.run rawClaimContext (rawClaimEntry "claimSpend") rawClaimInputs {} with
  | .ok state => state.2.shieldedClaims == [(ShieldedClaimKind.spend, claimBytes)]
  | .error _ => _root_.Bool.false
#guard match Entrypoint.run rawClaimContext (rawClaimEntry "guardedClaimReceive")
    (guardedRawClaimInputs _root_.Bool.false) {} with
  | .ok state => state.2.shieldedClaims.isEmpty
  | .error _ => _root_.Bool.false
#guard match Entrypoint.run rawClaimContext (rawClaimEntry "guardedClaimReceive")
    (guardedRawClaimInputs _root_.Bool.true) {} with
  | .ok state => state.2.shieldedClaims == [(ShieldedClaimKind.receive, claimBytes)]
  | .error _ => _root_.Bool.false

#guard match Entrypoint.run rawClaimContext (rawClaimEntry "helperClaimReceive")
    (guardedRawClaimInputs _root_.Bool.false) {} with
  | .ok state => state.2.shieldedClaims.isEmpty
  | .error _ => _root_.Bool.false
#guard match Entrypoint.run rawClaimContext (rawClaimEntry "helperClaimReceive")
    (guardedRawClaimInputs _root_.Bool.true) {} with
  | .ok state => state.2.shieldedClaims == [(ShieldedClaimKind.receive, claimBytes)]
  | .error _ => _root_.Bool.false

#guard match (Backend.Impact.Op.claimShielded .nullifier (.ref "digest")).fieldGroups with
  | [_, [.native 0x80, .native 1, .native 1, .native 0], _, _, _, _] => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match (Backend.Impact.Op.claimShielded .receive (.ref "digest")).fieldGroups with
  | [_, [.native 0x80, .native 1, .native 1, .native 1], _, _, _, _] => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match (Backend.Impact.Op.claimShielded .spend (.ref "digest")).fieldGroups with
  | [_, [.native 0x80, .native 1, .native 1, .native 2], _, _, _, _] => _root_.Bool.true
  | _ => _root_.Bool.false
