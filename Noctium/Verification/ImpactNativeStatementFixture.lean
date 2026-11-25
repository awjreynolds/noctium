import Lean
import Noctium.Verification.ImpactDecimal
import Noctium.Verification.ImpactPreviewBinding
import Noctium.Verification.ImpactStatementScalar

namespace Noctium.Verification.ImpactNativeStatementFixture

open Lean
open Noctium.Verification.ImpactCallPreview
open Noctium.Verification.ImpactPreviewBinding
open Noctium.Verification.ImpactStatementScalar
open Noctium.Verification.NativeRelation
open Noctium.Verification.NativeState

/-- Native transcript metadata before the preview inserts skipped operations. -/
structure Partition where
  operationCount : Nat
  readTime : Nat
  computeTime : Nat
  bytesWritten : Nat
  bytesDeleted : Nat
  effects : ByteArray

/-- Native inputs to the preview and the ledger's public fields after preview. -/
structure NativeStatementFixture where
  address : ByteArray
  entryPoint : ByteArray
  parentPedersen : ByteArray
  communication : Scalar
  cost : ImpactPreviewGas.CostModel
  guaranteed : Option Partition
  fallible : Option Partition
  fields : List Scalar

private def objectField (json : Json) (name : String) : Except String Json :=
  match json.getObjVal? name with
  | .ok value => .ok value
  | .error _ => .error s!"missing required field '{name}'"

private def exactFields (json : Json) (expected : List String)
    (label : String) : Except String Unit := do
  let object ← match json.getObj? with
    | .ok object => pure object
    | .error _ => throw s!"{label} must be an object"
  let actual := object.toList.map Prod.fst
  let allExpected := actual.all (fun name => expected.contains name)
  let allPresent := expected.all (fun name => actual.contains name)
  if actual.length == expected.length && allExpected && allPresent then
    pure ()
  else
    throw s!"{label} has missing or unknown fields"

private def stringField (json : Json) (name label : String) : Except String String := do
  match ← objectField json name with
  | .str value => pure value
  | _ => throw s!"{label} must be a string"

private def naturalNumber (value : Json) (label : String) : Except String Nat := do
  match value with
  | .num number => do
      if number.exponent != 0 then throw s!"{label} must be an integer"
      match number.mantissa with
      | .ofNat natural => pure natural
      | .negSucc _ => throw s!"{label} must be nonnegative"
  | _ => throw s!"{label} must be a JSON number"

private def u64Field (json : Json) (name label : String) : Except String Nat := do
  let value ← objectField json name
  let natural ← naturalNumber value label
  if natural < ImpactBindingNumber.u64Limit then
    pure natural
  else
    throw s!"{label} exceeds u64"

private def byteArrayField (json : Json) (name label : String) : Except String ByteArray := do
  let value ← objectField json name
  let values ← match value.getArr? with
    | .ok values => pure values
    | .error _ => throw s!"{label} must be an array of bytes"
  let bytes ← (values.toList.zipIdx).mapM fun (item, index) => do
    let itemLabel := s!"{label}[{index}]"
    let natural ← naturalNumber item itemLabel
    if natural < 256 then
      pure (UInt8.ofNat natural)
    else
      throw s!"{itemLabel} exceeds u8"
  pure (ByteArray.mk bytes.toArray)

private def scalarText (text label : String) : Except String Scalar := do
  let some natural := ImpactDecimal.parseCanonical text
    | throw s!"{label} must be a canonical unsigned decimal string"
  if natural < Field.modulus then
    pure (NativeRelation.scalar natural)
  else
    throw s!"{label} is outside the canonical field range"

private def scalarArrayField (json : Json) (name label : String) :
    Except String (List Scalar) := do
  let value ← objectField json name
  let values ← match value.getArr? with
    | .ok values => pure values
    | .error _ => throw s!"{label} must be an array of decimal strings"
  (values.toList.zipIdx).mapM fun (item, index) => do
    let itemLabel := s!"{label}[{index}]"
    let text ← match item with
      | .str text => pure text
      | _ => throw s!"{itemLabel} must be a decimal string"
    scalarText text itemLabel

private def partitionField (json : Json) (name : String) :
    Except String (Option Partition) := do
  let value ← objectField json name
  match value with
  | .null => pure none
  | .obj _ => do
      let label := name
      exactFields value
        ["operationCount", "readTime", "computeTime", "bytesWritten", "bytesDeleted", "effects"]
        label
      let operationCount ← u64Field value "operationCount" s!"{label}.operationCount"
      let readTime ← u64Field value "readTime" s!"{label}.readTime"
      let computeTime ← u64Field value "computeTime" s!"{label}.computeTime"
      let bytesWritten ← u64Field value "bytesWritten" s!"{label}.bytesWritten"
      let bytesDeleted ← u64Field value "bytesDeleted" s!"{label}.bytesDeleted"
      let effects ← byteArrayField value "effects" s!"{label}.effects"
      pure <| some ⟨operationCount, readTime, computeTime, bytesWritten, bytesDeleted, effects⟩
  | _ => throw s!"{name} must be null or a partition object"

/-- Decode the exact native statement fixture schema. Unknown and missing
fields, invalid bytes, noncanonical scalars, and out-of-range counters reject. -/
def decode (json : Json) : Except String NativeStatementFixture := do
  exactFields json
    ["address", "entryPoint", "parentPedersen", "communication", "noopConstant",
      "noopCoefficient", "guaranteed", "fallible", "fields"]
    "native statement fixture"
  let address ← byteArrayField json "address" "address"
  if address.size != ImpactBindingIdentity.contractAddressWidth then
    throw "address must contain exactly 32 bytes"
  let entryPoint ← byteArrayField json "entryPoint" "entryPoint"
  if entryPoint.size ≥ ImpactBindingIdentity.entryPointLengthLimit then
    throw "entryPoint length must fit u32"
  let parentPedersen ← byteArrayField json "parentPedersen" "parentPedersen"
  if parentPedersen.size != ImpactBindingIdentity.contractAddressWidth then
    throw "parentPedersen must contain exactly 32 bytes"
  let communicationText ← stringField json "communication" "communication"
  let communication ← scalarText communicationText "communication"
  let constant ← u64Field json "noopConstant" "noopConstant"
  let coefficient ← u64Field json "noopCoefficient" "noopCoefficient"
  let guaranteed ← partitionField json "guaranteed"
  let fallible ← partitionField json "fallible"
  let fields ← scalarArrayField json "fields" "fields"
  pure ⟨address, entryPoint, parentPedersen, communication,
    ⟨constant, coefficient⟩, guaranteed, fallible, fields⟩

private def operationCount : Option Partition → Nat
  | none => 0
  | some partition => partition.operationCount

private def mismatchIndex : Nat → List Scalar → List Scalar → Option Nat
  | _, [], [] => none
  | index, expected :: expectedRest, actual :: actualRest =>
      if expected == actual then mismatchIndex (index + 1) expectedRest actualRest
      else some index
  | index, _, _ => some index

/-- Preview native partitions using the independently decoded operations and
activity. Compare the resulting public inputs with the native ledger fields. -/
def check (fixture : NativeStatementFixture) (operations : List NativeState.Op)
    (activity : List (Option Nat)) : Except String Unit := do
  let guaranteedCount := operationCount fixture.guaranteed
  let fallibleCount := operationCount fixture.fallible
  if guaranteedCount + fallibleCount != operations.length then
    throw s!"partition operation counts total {guaranteedCount + fallibleCount}, but resolved operation list has {operations.length}"
  let guaranteed := fixture.guaranteed.map fun partition =>
    ({ program := operations.take guaranteedCount,
       computeTime := partition.computeTime } : Transcript NativeState.Op)
  let fallible := fixture.fallible.map fun partition =>
    ({ program := operations.drop guaranteedCount,
       computeTime := partition.computeTime } : Transcript NativeState.Op)
  let some call := previewCall fixture.cost ⟨guaranteed, fallible⟩ activity
    | throw "fixture partitions and decoded activity cannot form a preview"
  let metadata : ImpactPreviewBinding.Metadata := {
    address := fixture.address
    entryPoint := fixture.entryPoint
    guaranteed := fixture.guaranteed.map fun partition =>
      ⟨partition.readTime, partition.bytesWritten, partition.bytesDeleted, partition.effects⟩
    fallible := fixture.fallible.map fun partition =>
      ⟨partition.readTime, partition.bytesWritten, partition.bytesDeleted, partition.effects⟩
    parentPedersen := fixture.parentPedersen
  }
  let some header := ImpactPreviewBinding.header metadata call fixture.communication
    | throw "fixture identity, counters, or partition metadata cannot form a statement header"
  let some calculated := ImpactCallStatement.publicInputs ImpactStatementScalar.opFields header call
    | throw "calculated statement exceeds the pinned public-input limit"
  if calculated.length != fixture.fields.length then
    throw s!"public statement field count mismatch: calculated {calculated.length}, fixture has {fixture.fields.length}"
  match mismatchIndex 0 calculated fixture.fields with
  | none => pure ()
  | some index => throw s!"public statement field mismatch at index {index}"

end Noctium.Verification.ImpactNativeStatementFixture
