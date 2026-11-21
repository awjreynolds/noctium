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
  (List.range 65).map fun index => s!"result_{index}"

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
      fields.map (·.name) == shieldedBurnPhysicalFields &&
      fields.all (·.ty == .native)
  | _, _ => _root_.Bool.false

private def shieldedBurnReturnContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by shielded burn return fixture"
}

#guard match shieldedBurnReturnEntry.run shieldedBurnReturnContext [] {trees := []} with
  | .ok (outputs, _) =>
      (List.range 65).all fun index =>
        outputs.lookup s!"result_{index}" ==
          some (.native (if index == 0 then 1 else 0))
  | .error _ => _root_.Bool.false

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
