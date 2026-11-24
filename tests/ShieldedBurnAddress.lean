import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.ShieldedBurn

open Lean
open Noctium
open scoped Noctium

noctium_contract ShieldedBurnAddressReturnFixture where
  entry burn from ShieldedBurnAddress.program entry "shieldedBurnAddress" end
end

private def shieldedBurnValueFixture : Entrypoint := {
  name := "shieldedBurnAddress"
  circuit := {
    name := "shieldedBurnAddress"
    outputs := [
      {name := "is_left", ty := .bool,
        value := .bool shieldedBurnAddress.walletBranch},
      {name := "recipient", ty := .bytes 32,
        value := shieldedBurnAddress.recipient}
    ]
  }
}

private def shieldedBurnFixturePlan : Except String Json := do
  let plan ← (Backend.Impact.lower [] shieldedBurnValueFixture).mapError (·.message)
  pure (Compiler.nativePlanJson TargetProfile.selected321 `ShieldedBurnAddress
    [] none shieldedBurnValueFixture plan)

#guard shieldedBurnAddress.walletBranch
#guard match shieldedBurnAddress.recipient with
  | .bytes32Literal bytes => bytes == List.replicate 32 0
  | _ => _root_.Bool.false

#guard match shieldedBurnFixturePlan with
  | .ok plan =>
      match (plan.getObjVal? "circuit").toOption with
      | some circuit =>
          match (circuit.getObjVal? "outputs").toOption with
          | some (.arr outputs) =>
              match outputs[0]?, outputs[1]? with
              | some isLeft, some recipient =>
                  isLeft.getObjValD "expression" == Lean.Json.mkObj [
                    ("tag", toJson ("bool" : String)),
                    ("value", toJson (_root_.Bool.true))] &&
                  recipient.getObjValD "expression" == Lean.Json.mkObj [
                    ("tag", toJson ("bytes32Literal" : String)),
                    ("values", toJson (List.replicate 32 (0 : Nat)))]
              | _, _ => _root_.Bool.false
          | _ => _root_.Bool.false
      | none => _root_.Bool.false
  | .error _ => _root_.Bool.false

private def shieldedBurnReturnEntry : Entrypoint :=
  (ShieldedBurnAddressReturnFixture.entrypoints.find? (·.name == "burn")).getD
    {name := "missing", circuit := {name := "missing"}}

private def shieldedBurnPhysicalFields : List String :=
  (List.range 5).map fun index => s!"result_{index}"

private def shieldedBurnLogicalLayout : _root_.Bool :=
  match Types.compileType ShieldedBurnAddress.composites ShieldedBurnAddress.logicalType with
  | .ok compiled =>
      match compiled.checked.value with
      | .structure "Noctium.Midnight.ShieldedBurnAddressResult" [
          ("is_left", .scalar .booleanField),
          ("left", .structure "Noctium.Midnight.ZswapCoinPublicKey" [
            ("bytes", .bytes 32 .byteField)]),
          ("right", .structure "Noctium.Midnight.ContractAddress" [
            ("bytes", .bytes 32 .byteField)])] => _root_.Bool.true
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard shieldedBurnLogicalLayout
#guard match shieldedBurnReturnEntry.returnViews, shieldedBurnReturnEntry.returns with
  | [view], fields =>
      view.name == "result" && view.type == ShieldedBurnAddress.logicalType &&
      view.environment == ShieldedBurnAddress.composites &&
      view.fields == shieldedBurnPhysicalFields &&
      view.packedBytesFields == [
        {leafOffset := 1, byteLength := 32, fields := ["result_1", "result_2"], chunkWidths := [1, 31]},
        {leafOffset := 33, byteLength := 32, fields := ["result_3", "result_4"], chunkWidths := [1, 31]}] &&
      fields.map (·.name) == shieldedBurnPhysicalFields &&
      fields.all (·.ty == .native)
  | _, _ => _root_.Bool.false

private def packedShieldedBurnPlan : Except String Lean.Json := do
  let plan ← (Backend.Impact.lower [] shieldedBurnReturnEntry).mapError (·.message)
  pure (Compiler.nativePlanJson TargetProfile.selected321 `ShieldedBurnAddress
    [] none shieldedBurnReturnEntry plan)

#guard match packedShieldedBurnPlan with
  | .ok plan =>
    let returns := (plan.getObjValD "returns").getArr?.toOption.getD #[]
    let views := (plan.getObjValD "returnViews").getArr?.toOption.getD #[]
    returns.size == 5 && views.size == 1 &&
      ((views[0]!.getObjValD "fields").getArr?.toOption.getD #[]).size == 5 &&
      ((views[0]!.getObjValD "packedBytesFields").getArr?.toOption.getD #[]).size == 2
  | .error _ => _root_.Bool.false

private def shieldedBurnReturnContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by shielded burn return fixture"
}

#guard match shieldedBurnReturnEntry.run shieldedBurnReturnContext [] {trees := []} with
  | .ok (outputs, _) =>
      (List.range 5).all fun index =>
        outputs.lookup s!"result_{index}" ==
          some (.native (if index == 0 then 1 else 0))
  | .error _ => _root_.Bool.false

private def packedReturnPatternBytes (bias : Nat) : List Nat :=
  (List.range 32).map fun index => if index == 30 then 165 else if index == 31 then bias else (index * 7) % 256

private def packedReturnPatternProgram (wallet : _root_.Bool)
    (badByte : _root_.Bool := _root_.Bool.false) : Helpers.Program := Id.run do
  let active := packedReturnPatternBytes (if wallet then 90 else 165)
  let active := if badByte then active.set 30 256 else active
  let inactive := List.replicate 32 0
  let left := if wallet then active else inactive
  let right := if wallet then inactive else active
  let leaves := [.bool wallet] ++
    left.map (fun byte => Helpers.Term.native byte) ++
    right.map (fun byte => Helpers.Term.native byte)
  return {
    composites := ShieldedBurnAddress.composites
    declarations := [{
      id := ⟨0, 0⟩
      name := "packedPattern"
      result := .composite ShieldedBurnAddress.logicalType
      body := [.return (some (.composite ShieldedBurnAddress.logicalType leaves))]
    }]
    exports := [{
      name := "packedPattern"
      target := ⟨0, 0⟩
      packedByteReturnPaths := [["left", "bytes"], ["right", "bytes"]]
    }]
  }

private def packedPatternEntry (wallet : _root_.Bool)
    (badByte : _root_.Bool := _root_.Bool.false) : Except String Entrypoint := do
  (Helpers.compileEntrypoint (packedReturnPatternProgram wallet badByte) "packedPattern").mapError (·.message)

private def packedReturnPatternChunk (bytes : List Nat) : Nat :=
  bytes.zipIdx.foldl (fun total (byte, index) => total + byte * 256 ^ index) 0

private def packedReturnPatternPasses (wallet : _root_.Bool) : _root_.Bool := Id.run do
  return match packedPatternEntry wallet with
  | .error _ => _root_.Bool.false
  | .ok compiledEntry =>
    let active := packedReturnPatternBytes (if wallet then 90 else 165)
    let zero := List.replicate 32 0
    let left := if wallet then active else zero
    let right := if wallet then zero else active
    let expected := [
      if wallet then 1 else 0,
      left[31]!, packedReturnPatternChunk (left.take 31),
      right[31]!, packedReturnPatternChunk (right.take 31)]
    match compiledEntry.run shieldedBurnReturnContext [] {trees := []} with
    | .ok (outputs, _) =>
      (List.range 5).all fun index =>
        outputs.lookup s!"result_{index}" == some (.native expected[index]!)
    | .error _ => _root_.Bool.false

#guard (packedReturnPatternPasses _root_.Bool.true)
#guard (packedReturnPatternPasses _root_.Bool.false)

private def packedReturnOverwidthByteRejected : _root_.Bool := Id.run do
  match packedPatternEntry _root_.Bool.true _root_.Bool.true with
  | .error _ => return _root_.Bool.false
  | .ok compiledEntry =>
    match compiledEntry.run shieldedBurnReturnContext [] {trees := []} with
    | .error _ => return _root_.Bool.true
    | .ok _ => return _root_.Bool.false

#guard packedReturnOverwidthByteRejected

noctium_circuit shieldedBurnInputs where
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
  output burnKey : Bytes32 := shieldedBurnKey()
end

/-- error: relayShieldedImmediate expects ContractAddress, got ZswapCoinPublicKey -/
#guard_msgs (substring := true) in
noctium_contract WrongShieldedBurnAddress where
  entry relay uses shieldedBurnInputs where
    relayShieldedImmediate(disclose(nonce), disclose(color), disclose(amount), shieldedBurnKey())
  end
end
