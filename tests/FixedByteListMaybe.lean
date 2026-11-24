import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Compiler
import Noctium.Frontend

open scoped Noctium
open Lean
open Noctium

noctium_circuit fixedByteMaybePushInputs where
  private byte1 : Bytes 1
  private byte32 : Bytes 32
  private byte128 : Bytes 128
end

noctium_circuit fixedByteMaybeNoInputs where
end

noctium_contract FixedByteListMaybe where
  list bytes1 : Bytes 1
  list bytes32 : Bytes 32
  list bytes128 : Bytes 128

  entry push uses fixedByteMaybePushInputs where
    pushFront bytes1 := disclose(byte1)
    pushFront bytes32 := disclose(byte32)
    pushFront bytes128 := disclose(byte128)
  end

  entry head uses fixedByteMaybeNoInputs where
    headOrDefault bytes1 as (present1, value1)
    headOrDefault bytes32 as (present32, value32)
    headOrDefault bytes128 as (present128, value128)
    returnMaybe maybe1 as (present1, value1)
    returnMaybe maybe32 as (present32, value32)
    returnMaybe maybe128 as (present128, value128)
  end
end

private def maybeEntry (name : String) : Entrypoint :=
  (FixedByteListMaybe.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def maybeContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by fixed-byte List Maybe fixture"
}

private def emptyMaybeState : LedgerState := {
  trees := [("bytes1", .list []), ("bytes32", .list []), ("bytes128", .list [])]
}

private def byte1Value : Value := .bytes 1 [77]
private def byte32Value : Value := .bytes 32 (List.range 32)
private def byte128Value : Value := .bytes 128 ((List.range 128).map fun index => (index * 17 + 5) % 256)

private def packedChunks (bytes : List Nat) : List Nat := Id.run do
  let count := (bytes.length + 30) / 31
  let mut result := []
  for index in List.range count do
    let start := (count - 1 - index) * 31
    let mut field := 0
    for (byte, offset) in (bytes.drop start).take 31 |>.zipIdx do
      field := field + byte * 256 ^ offset
    result := result ++ [field]
  return result

private def expectedMaybeOutputs (label : String) (isPresent : _root_.Bool) (bytes : List Nat) : List (String × Value) :=
  let payload := (List.range ((bytes.length + 30) / 31)).map fun index =>
    (s!"{label}_value_chunk_{index}", .native (packedChunks bytes)[index]!)
  (s!"{label}_is_some", .native (if isPresent then 1 else 0)) :: payload

private def outputsMatch (outputs expected : List (String × Value)) : _root_.Bool :=
  expected.all fun (name, value) => outputs.lookup name == some value

private def chunkNames (label : String) (length : Nat) : List String :=
  (List.range ((length + 30) / 31)).map fun index => s!"{label}_value_chunk_{index}"

private def packedMaybeField (label : String) (length : Nat) : PackedBytesReturnField := {
  leafOffset := 1
  byteLength := length
  fields := chunkNames label length
  chunkWidths := ((List.range ((length + 30) / 31)).reverse.map fun index =>
    bytesChunkWidth length index)
}

private def hasZeroDefaultChunk (returned : Output) (length index : Nat) : _root_.Bool :=
  match returned with
  | {ty := .native, value := .bytesField (.select _ _ (.bytesLiteral actualLength values)) actualIndex, ..} =>
    actualLength == length && values == List.replicate length 0 && actualIndex == index
  | _ => Bool.false

private def hasZeroDefaultChunks (headEntrypoint : Entrypoint) (label : String) (length : Nat) : _root_.Bool :=
  (List.range ((length + 30) / 31)).all fun index =>
    match headEntrypoint.returns.find? (·.name == s!"{label}_value_chunk_{index}") with
    | some returned => hasZeroDefaultChunk returned length index
    | none => Bool.false

private def runHead (state : LedgerState) :=
  (maybeEntry "head").run maybeContext [] state

#guard match Backend.Impact.lower FixedByteListMaybe.state (maybeEntry "push") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower FixedByteListMaybe.state (maybeEntry "head") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint FixedByteListMaybe.state (maybeEntry "head") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

private def nativeByteMaybeLayout : _root_.Bool := Id.run do
  let headEntry := maybeEntry "head"
  return headEntry.returns.map (·.name) == [
      "maybe1_is_some", "maybe1_value_chunk_0",
      "maybe32_is_some", "maybe32_value_chunk_0", "maybe32_value_chunk_1",
      "maybe128_is_some", "maybe128_value_chunk_0", "maybe128_value_chunk_1",
      "maybe128_value_chunk_2", "maybe128_value_chunk_3", "maybe128_value_chunk_4"] &&
    headEntry.returns.all (·.ty == .native) &&
    headEntry.returnViews.map (·.fields) == [
      "maybe1_is_some" :: chunkNames "maybe1" 1,
      "maybe32_is_some" :: chunkNames "maybe32" 32,
      "maybe128_is_some" :: chunkNames "maybe128" 128] &&
    headEntry.returnViews.map (·.packedBytesFields) == [
      [packedMaybeField "maybe1" 1],
      [packedMaybeField "maybe32" 32],
      [packedMaybeField "maybe128" 128]] &&
    hasZeroDefaultChunks headEntry "maybe1" 1 &&
    hasZeroDefaultChunks headEntry "maybe32" 32 &&
    hasZeroDefaultChunks headEntry "maybe128" 128

#guard nativeByteMaybeLayout

private def nativeMaybePlan : Except String Lean.Json := do
  let headEntry := maybeEntry "head"
  let plan ← (Backend.Impact.lower FixedByteListMaybe.state headEntry).mapError (·.message)
  pure (Compiler.nativePlanJson TargetProfile.selected321 `FixedByteListMaybe
    FixedByteListMaybe.state none headEntry plan)

#guard match nativeMaybePlan with
  | .ok artifact =>
    let returns := (artifact.getObjValD "returns").getArr?.toOption.getD #[]
    let views := (artifact.getObjValD "returnViews").getArr?.toOption.getD #[]
    let middlePacked := ((views[1]!.getObjValD "packedBytesFields").getArr?.toOption.getD #[])[0]!
    let longestPacked := ((views[2]!.getObjValD "packedBytesFields").getArr?.toOption.getD #[])[0]!
    returns.size == 11 && views.size == 3 &&
      ((views[0]!.getObjValD "fields").getArr?.toOption.getD #[]).size == 2 &&
      ((views[1]!.getObjValD "fields").getArr?.toOption.getD #[]).size == 3 &&
      ((views[2]!.getObjValD "fields").getArr?.toOption.getD #[]).size == 6 &&
      middlePacked.getObjValD "chunkWidths" == toJson ([1, 31] : List Nat) &&
      longestPacked.getObjValD "chunkWidths" == toJson ([4, 31, 31, 31, 31] : List Nat)
  | .error _ => Bool.false

#guard match runHead emptyMaybeState with
  | .ok (outputs, _) =>
    outputsMatch outputs (expectedMaybeOutputs "maybe1" _root_.Bool.false [0]) &&
    outputsMatch outputs (expectedMaybeOutputs "maybe32" _root_.Bool.false (List.replicate 32 0)) &&
    outputsMatch outputs (expectedMaybeOutputs "maybe128" _root_.Bool.false (List.replicate 128 0))
  | .error _ => Bool.false

#guard match (maybeEntry "push").run maybeContext [
    ("byte1", byte1Value), ("byte32", byte32Value), ("byte128", byte128Value)] emptyMaybeState with
  | .ok (_, populated) =>
    match runHead populated with
    | .ok (outputs, _) =>
      outputsMatch outputs (expectedMaybeOutputs "maybe1" _root_.Bool.true [77]) &&
      outputsMatch outputs (expectedMaybeOutputs "maybe32" _root_.Bool.true (List.range 32)) &&
      outputsMatch outputs (expectedMaybeOutputs "maybe128" _root_.Bool.true ((List.range 128).map fun index => (index * 17 + 5) % 256))
    | .error _ => Bool.false
  | .error _ => Bool.false
