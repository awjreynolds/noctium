import examples.openzeppelin.ConfidentialToken
import Noctium.Verification.NativeRelation
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.NativeState
import Noctium.Verification.GenericStateVM
import Noctium.Verification
import proofs.ConfidentialTokenTotalSupply
import Lean
import Lean.Elab.Command
open Lean Elab Command Tactic

namespace OpenZeppelinPort.ConfidentialTokenTotalSupplyNative

open Noctium
open Noctium.Verification.NativeRelation
open Noctium.Verification.NativeState
open Noctium.Verification.GenericStateVM

def supplyMaximum : Nat := 2 ^ 128 - 1

def sourceEntry : Entrypoint :=
  OpenZeppelinPort.ConfidentialToken.entrypoints[7]'(by decide)

theorem source_read_and_return_are_actual :
    sourceEntry.effects = [.readCell "totalSupply" "currentSupply" (.uint supplyMaximum)] ∧
    sourceEntry.returns = [{
      name := "supply"
      ty := .uint supplyMaximum
      value := .ref "currentSupply"
      span := { file := "examples/openzeppelin/ConfidentialToken.lean", line := 769, column := 5 }
    }] := by
  exact ⟨OpenZeppelinPort.ConfidentialTokenTotalSupply.totalSupply_entry_shape.1,
    OpenZeppelinPort.ConfidentialTokenTotalSupply.totalSupply_entry_shape.2.2⟩
theorem source_exact_run (state : LedgerState) (supply : Nat)
    (supplyCell : state.cells.lookup "totalSupply" = some (.uint supplyMaximum supply))
    (supplyBound : supply ≤ supplyMaximum)
    (clean : state.unshieldedInputs = [] ∧ state.unshieldedOutputs = [] ∧
      state.unshieldedSpendClaims = []) :
    sourceEntry.run OpenZeppelinPort.ConfidentialTokenTotalSupply.sourceContext [] state =
      .ok ([ ("supply", .uint supplyMaximum supply) ], state) := by
  exact OpenZeppelinPort.ConfidentialTokenTotalSupply.totalSupply_run
    state supply supplyCell supplyBound clean

def inputName : String := "%input_currentSupply"

def supplyProgram : Program := {
  instructions := [
    .input .public inputName,
    .bits (.reference inputName) 128,
    .impact (.immediate (scalar 1)) [.immediate (scalar 48)],
    .impact (.immediate (scalar 1))
      [.immediate (scalar 80), .immediate (scalar 1),
        .immediate (scalar (Field.modulus - 2)), .immediate (scalar 6)],
    .impact (.immediate (scalar 1))
      [.immediate (scalar 12), .immediate (scalar 1),
        .immediate (scalar (Field.modulus - 2)), .reference inputName],
    .output [.reference inputName]
  ],
  outputArity := 1,
  communicationsCommitment := _root_.Bool.true
}

def supplyWitness (supply : Nat) : Assignment := fun name =>
  if name == inputName then scalar supply else zero

def supplyImpactGroups (supply : Nat) : List (List Scalar) := [
  [scalar 48],
  [scalar 80, scalar 1, scalar (Field.modulus - 2), scalar 6],
  [scalar 12, scalar 1, scalar (Field.modulus - 2), scalar supply]
]

def isPinnedProfile (profile : Lean.Json) : _root_.Bool :=
  (profile.getObjValAs? String "zkir").toOption == some "3.2.1" &&
  (profile.getObjValAs? String "name").toOption == some "midnight-ledger-9-zkir-3.2.1"

example : isPinnedProfile (Lean.Json.mkObj [
    ("zkir", Lean.toJson "3.2.0"),
    ("name", Lean.toJson "midnight-ledger-9-zkir-3.2.0")]) = _root_.Bool.false := by decide

def stripCircuitFile (impact : Lean.Json) : Lean.Json :=
  match impact with
  | .obj fields => Lean.Json.mkObj (fields.toList.map fun (key, value) =>
      if key == "circuit" then
        match value with
        | .obj circuit => (key, Lean.Json.mkObj (circuit.toList.filter (·.1 != "file")))
        | _ => (key, value)
      else (key, value))
  | _ => impact

def wrongSlotProgram : Program := { supplyProgram with instructions := [
  .input .public inputName,
  .bits (.reference inputName) 128,
  .impact (.immediate (scalar 1)) [.immediate (scalar 48)],
  .impact (.immediate (scalar 1))
    [.immediate (scalar 80), .immediate (scalar 1),
      .immediate (scalar (Field.modulus - 2)), .immediate (scalar 7)],
  .impact (.immediate (scalar 1))
    [.immediate (scalar 12), .immediate (scalar 1),
      .immediate (scalar (Field.modulus - 2)), .reference inputName],
  .output [.reference inputName]
] }

def missingRangeProgram : Program := { supplyProgram with instructions := [
  .input .public inputName,
  .impact (.immediate (scalar 1)) [.immediate (scalar 48)],
  .impact (.immediate (scalar 1))
    [.immediate (scalar 80), .immediate (scalar 1),
      .immediate (scalar (Field.modulus - 2)), .immediate (scalar 6)],
  .impact (.immediate (scalar 1))
    [.immediate (scalar 12), .immediate (scalar 1),
      .immediate (scalar (Field.modulus - 2)), .reference inputName],
  .output [.reference inputName]
] }

def staleReadProgram : Program := { supplyProgram with instructions := [
  .input .public inputName,
  .bits (.reference inputName) 128,
  .impact (.immediate (scalar 1)) [.immediate (scalar 48)],
  .impact (.immediate (scalar 1))
    [.immediate (scalar 80), .immediate (scalar 1),
      .immediate (scalar (Field.modulus - 2)), .immediate (scalar 6)],
  .impact (.immediate (scalar 1))
    [.immediate (scalar 12), .immediate (scalar 1),
      .immediate (scalar (Field.modulus - 2)), .reference "%staleSupply"],
  .output [.reference inputName]
] }

def wrongOutputProgram : Program := { supplyProgram with instructions := [
  .input .public inputName,
  .bits (.reference inputName) 128,
  .impact (.immediate (scalar 1)) [.immediate (scalar 48)],
  .impact (.immediate (scalar 1))
    [.immediate (scalar 80), .immediate (scalar 1),
      .immediate (scalar (Field.modulus - 2)), .immediate (scalar 6)],
  .impact (.immediate (scalar 1))
    [.immediate (scalar 12), .immediate (scalar 1),
      .immediate (scalar (Field.modulus - 2)), .reference inputName],
  .output [.immediate (scalar 0)]
] }

example : wrongSlotProgram ≠ supplyProgram := by decide
example : missingRangeProgram ≠ supplyProgram := by decide
example : staleReadProgram ≠ supplyProgram := by decide
example : wrongOutputProgram ≠ supplyProgram := by decide

/-- Soundness for any satisfying assignment. The native processor premise maps
the canonical typed slot-6 value to its decoded vector entry. The accepted VM
read then binds that entry to the public input and proves its read-only vector
frame. The circuit itself checks the width and returns the same field. -/
theorem native_sound_arbitrary (state : LedgerState) (items : List Slot)
    (afterVm : Machine) (supply : Nat) (assignment : Assignment)
    (publicGroups : List (List Scalar))
    (slot6Decodes : state.cells.lookup "totalSupply" =
      some (.uint supplyMaximum supply))
    (slot6Encoding : items[6]? = some (.cell (field (scalar supply))))
    (canonicalSupply : supply < Field.modulus)
    (clean : state.unshieldedInputs = [] ∧ state.unshieldedOutputs = [] ∧
      state.unshieldedSpendClaims = [])
    (nativeRead : run (readCellOps 6 (field (assignment inputName)))
      ⟨[.vector items], []⟩ = some afterVm)
    (sat : CircuitSatisfies (fun _ => zero) supplyProgram
      {publicValues := [scalar supply], privateValues := []}
      assignment publicGroups) :
    supply ≤ supplyMaximum ∧
    supplyProgram.returns assignment = [scalar supply] ∧
    publicGroups = supplyImpactGroups supply ∧
    state.cells.lookup "totalSupply" = some (.uint supplyMaximum supply) ∧
    afterVm = ⟨[.vector items], [field (scalar supply)]⟩ ∧
    sourceEntry.run OpenZeppelinPort.ConfidentialTokenTotalSupply.sourceContext [] state =
      .ok ([("supply", .uint supplyMaximum supply)], state) := by
  obtain ⟨readSlot, vmFrame⟩ := readCell_sound_prefix items 6
    (field (assignment inputName)) [] afterVm nativeRead
  have cellBinding : field (assignment inputName) = field (scalar supply) := by
    have equality := readSlot.symm.trans slot6Encoding
    have slotEquality : Slot.cell (field (assignment inputName)) =
        Slot.cell (field (scalar supply)) := Option.some.inj equality
    injection slotEquality
  have nativeReadBinds : assignment inputName = scalar supply := by
    exact (field_inj _ _).mp cellBinding
  have widthMember : .bits (.reference inputName) 128 ∈ supplyProgram.instructions := by
    simp [supplyProgram]
  have widthHolds := sat.instructions _ widthMember
  change (assignment inputName).val < 2 ^ 128 at widthHolds
  rw [nativeReadBinds] at widthHolds
  have supplyValue : (scalar supply).val = supply := scalar_no_wrap supply canonicalSupply
  rw [supplyValue] at widthHolds
  have bounded : supply ≤ supplyMaximum := by
    unfold supplyMaximum
    omega
  have observedFrame : afterVm = ⟨[.vector items], [field (scalar supply)]⟩ := by
    rw [vmFrame]
    simp [nativeReadBinds]
  have observedGroups : supplyProgram.groups assignment = supplyImpactGroups supply := by
    simp [Program.groups, supplyProgram, supplyImpactGroups, Operand.read, nativeReadBinds]
  refine ⟨bounded, ?_, ?_, slot6Decodes, observedFrame,
    source_exact_run state supply slot6Decodes bounded clean⟩
  simp [Program.returns, supplyProgram, Operand.read, nativeReadBinds]
  simpa [supplyImpactGroups] using sat.groups.symm.trans observedGroups

/-- Every admitted UInt128 supply has a satisfying native witness with the
exact output and ordered read-impact groups. -/
theorem native_complete (supply : Nat) (bounded : supply ≤ supplyMaximum) :
    CircuitSatisfies (fun _ => zero) supplyProgram
      {publicValues := [scalar supply], privateValues := []}
      (supplyWitness supply) (supplyImpactGroups supply) := by
  constructor
  · intro instruction hmem
    simp only [supplyProgram, List.mem_cons, List.not_mem_nil] at hmem
    rcases hmem with h1 | h2 | h3 | h4 | h5 | h6
    · cases h1
      trivial
    · cases h2
      simp only [Instruction.Holds]
      have supplyLt : supply < 2 ^ 128 := by
        unfold supplyMaximum at bounded
        omega
      have maxField : supplyMaximum < Field.modulus := by decide
      have supplyField : supply < Field.modulus := Nat.lt_of_le_of_lt bounded maxField
      simp [Operand.read, supplyWitness, inputName]
      rw [scalar_no_wrap supply supplyField]
      exact supplyLt
    · rw [h3]
      rfl
    · cases h4 <;> trivial
    · cases h5 <;> trivial
    · rcases h6 with h6 | h6
      · cases h6
        trivial
      · contradiction
  · rfl
  · rfl
  · rfl

/-- Under the slot encoding premise, the accepted source supply gives both
a satisfying circuit witness and an accepted read with unchanged VM state. -/
theorem complete_for_encoded_state (state : LedgerState) (items : List Slot)
    (supply : Nat) (bounded : supply ≤ supplyMaximum)
    (slot6Decodes : state.cells.lookup "totalSupply" = some (.uint supplyMaximum supply))
    (slot6Encoding : items[6]? = some (.cell (field (scalar supply))))
    (clean : state.unshieldedInputs = [] ∧ state.unshieldedOutputs = [] ∧
      state.unshieldedSpendClaims = []) :
    CircuitSatisfies (fun _ => zero) supplyProgram
      {publicValues := [scalar supply], privateValues := []}
      (supplyWitness supply) (supplyImpactGroups supply) ∧
    supplyProgram.returns (supplyWitness supply) = [scalar supply] ∧
    run (readCellOps 6 (field (scalar supply))) ⟨[.vector items], []⟩ =
      some ⟨[.vector items], [field (scalar supply)]⟩ ∧
    sourceEntry.run OpenZeppelinPort.ConfidentialTokenTotalSupply.sourceContext [] state =
      .ok ([("supply", .uint supplyMaximum supply)], state) :=
  ⟨native_complete supply bounded, rfl, readCell_exact items 6 (field (scalar supply)) []
    slot6Encoding, source_exact_run state supply slot6Decodes bounded clean⟩

/-- A read claiming a different field value cannot pass the slot-6 comparison. -/
theorem stale_slot_value_rejected (items : List Slot) (stored claimed : Scalar)
    (slot6 : items[6]? = some (.cell (field stored)))
    (different : claimed ≠ stored) :
    run (readCellOps 6 (field claimed)) ⟨[.vector items], []⟩ = none := by
  cases accepted : run (readCellOps 6 (field claimed)) ⟨[.vector items], []⟩ with
  | none => rfl
  | some after =>
    have readSlot := (readCell_sound_prefix items 6 (field claimed) [] after accepted).1
    have sameCell := Slot.cell.inj (Option.some.inj (readSlot.symm.trans slot6))
    exact (different ((field_inj _ _).mp sameCell)).elim

#eval show IO Unit from do
  let fixtureDirectory := (← IO.getEnv "NOCTIUM_TOTAL_SUPPLY_FIXTURE_DIR").getD
    "runtime/tests/fixtures/confidential-token/321"
  let contents ← IO.FS.readFile
    (fixtureDirectory ++ "/OpenZeppelinPort.ConfidentialToken.totalSupply.zkir")
  let json ← match Lean.Json.parse contents with
    | .ok json => pure json
    | .error error => throw (IO.userError s!"invalid totalSupply ZKIR fixture: {error}")
  let decoded ← match Noctium.Verification.NativeRelationJson.decode json with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"unsupported totalSupply ZKIR fixture: {error}")
  if decoded = supplyProgram then pure ()
  else throw (IO.userError "totalSupply ZKIR fixture differs from the checked native program")

#eval show IO Unit from do
  let fixtureDirectory := (← IO.getEnv "NOCTIUM_TOTAL_SUPPLY_FIXTURE_DIR").getD
    "runtime/tests/fixtures/confidential-token/321"
  let contents ← IO.FS.readFile
    (fixtureDirectory ++ "/OpenZeppelinPort.ConfidentialToken.totalSupply.impact.json")
  let impact ← match Lean.Json.parse contents with
    | .ok json => pure json
    | .error error => throw (IO.userError s!"invalid totalSupply Impact fixture: {error}")
  let retainedContents ← IO.FS.readFile
    "runtime/tests/fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.totalSupply.impact.json"
  let retained ← match Lean.Json.parse retainedContents with
    | .ok json => pure json
    | .error error => throw (IO.userError s!"invalid retained totalSupply Impact fixture: {error}")
  unless stripCircuitFile impact == stripCircuitFile retained do
    throw (IO.userError "totalSupply Impact fixture differs beyond circuit.file metadata")
  let profile ← match impact.getObjVal? "targetProfile" with
    | .ok profile => pure profile
    | .error error => throw (IO.userError s!"missing totalSupply target profile: {error}")
  unless isPinnedProfile profile do
    throw (IO.userError "totalSupply Impact fixture has an unexpected target profile")
  unless (impact.getObjValAs? String "target").toOption == some "midnight-ledger-9-zkir-3.2.1" do
    throw (IO.userError "totalSupply Impact fixture target does not match its profile")
  unless (impact.getObjValAs? String "entrypoint").toOption == some "totalSupply" do
    throw (IO.userError "totalSupply Impact fixture entrypoint changed")
  let operations ← match impact.getObjVal? "operations" >>= Lean.Json.getArr? with
    | .ok operations => pure operations
    | .error error => throw (IO.userError s!"missing totalSupply operations: {error}")
  let expectedOperations ← match Lean.Json.parse
      "[{\"op\":\"dup\"},{\"slot\":6,\"pushPath\":false,\"op\":\"index\"},{\"op\":\"popeq\",\"expression\":{\"value\":{\"tag\":\"reference\",\"name\":\"currentSupply\"},\"type\":\"Native\",\"tag\":\"cast\"},\"alignment\":\"field\"}]" with
    | .ok expected => pure expected
    | .error error => throw (IO.userError s!"invalid expected source operation JSON: {error}")
  unless Json.arr operations == expectedOperations do
    throw (IO.userError "totalSupply Impact operations differ from source read at slot 6")
  let reads ← match impact.getObjVal? "reads" >>= Lean.Json.getArr? with
    | .ok reads => pure reads
    | .error error => throw (IO.userError s!"missing totalSupply read declarations: {error}")
  let expectedReads ← match Lean.Json.parse
      "[{\"type\":\"UIntRange<340282366920938463463374607431768211456>\",\"name\":\"currentSupply\"}]" with
    | .ok expected => pure expected
    | .error error => throw (IO.userError s!"invalid expected totalSupply read JSON: {error}")
  unless Json.arr reads == expectedReads do
    throw (IO.userError "totalSupply Impact read declaration changed")
  let returns ← match impact.getObjVal? "returns" >>= Lean.Json.getArr? with
    | .ok returns => pure returns
    | .error error => throw (IO.userError s!"missing totalSupply return declaration: {error}")
  let expectedReturns ← match Lean.Json.parse
      "[{\"visibility\":\"public\",\"type\":\"UIntRange<340282366920938463463374607431768211456>\",\"name\":\"supply\",\"expression\":{\"tag\":\"reference\",\"name\":\"currentSupply\"}}]" with
    | .ok expected => pure expected
    | .error error => throw (IO.userError s!"invalid expected totalSupply return JSON: {error}")
  unless Json.arr returns == expectedReturns do
    throw (IO.userError "totalSupply Impact return binding changed")

end OpenZeppelinPort.ConfidentialTokenTotalSupplyNative
