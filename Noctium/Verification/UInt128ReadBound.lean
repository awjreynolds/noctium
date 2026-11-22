import Noctium.Verification.ScalarTermMeaning
import Noctium.Backend.LedgerReadOptimization

namespace Noctium.Verification.UInt128ReadBound

open NativeRelation

/-- The Ledger bridge must provide the value from the same typed, checked
Popeq transcript item that binds the circuit input. This condition says only
what that exact atom decodes to and makes no claim about arbitrary witnesses. -/
def BoundRead (witness : Assignment) (name : String) : Prop :=
  ∃ bytes : List UInt8, bytes.length = 16 ∧
    (witness name).val = Backend.Native.littleEndian (bytes.map UInt8.toNat)

theorem read_lt (witness : Assignment) (name : String) (bound : BoundRead witness name) :
    (witness name).val < 2 ^ 128 := by
  obtain ⟨bytes, length, value⟩ := bound
  have inRange := ScalarTermMeaning.littleEndian_lt_pow_of_bytes (bytes.map UInt8.toNat) (by
    intro value member
    obtain ⟨byte, _, rfl⟩ := List.mem_map.mp member
    exact byte.toFin.isLt)
  rw [List.length_map, length] at inRange
  simpa only [value, show 256 ^ 16 = 2 ^ 128 by decide] using inRange

/-- Under the exact ledger input premise, restoring the one removed range
check preserves the arbitrary witness, input streams, and Impact groups. -/
theorem restore_range (hash : Hash) (candidate : Program) (streams : InputStreams)
    (witness : Assignment) (groups : List (List Scalar)) (name : String)
    (before after : List Instruction)
    (instructions : candidate.instructions = before ++ after)
    (bound : BoundRead witness name)
    (satisfies : CircuitSatisfies hash candidate streams witness groups) :
    CircuitSatisfies hash {candidate with
      instructions := before ++ [.bits (.reference name) 128] ++ after}
      streams witness groups := by
  constructor
  · intro instruction member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with (inBefore | restored) | inAfter
    · exact satisfies.instructions instruction (by rw [instructions]; exact List.mem_append_left _ inBefore)
    · subst instruction
      exact read_lt witness name bound
    · exact satisfies.instructions instruction (by rw [instructions]; exact List.mem_append_right _ inAfter)
  · simpa [Program.inputValues, List.filterMap_append, instructions] using satisfies.publicInputs
  · simpa [Program.inputValues, List.filterMap_append, instructions] using satisfies.privateInputs
  · simpa [Program.groups, List.filterMap_append, instructions] using satisfies.groups

/-- Positive and negative circuit agreement when the verifier has authenticated
this read's exact 16-byte value. The raw baseline needs no such premise. -/
theorem equivalent_on_bound_read (hash : Hash) (candidate : Program) (streams : InputStreams)
    (witness : Assignment) (groups : List (List Scalar)) (name : String)
    (before after : List Instruction)
    (instructions : candidate.instructions = before ++ after)
    (bound : BoundRead witness name) :
    CircuitSatisfies hash candidate streams witness groups ↔
      CircuitSatisfies hash {candidate with
        instructions := before ++ [.bits (.reference name) 128] ++ after}
        streams witness groups := by
  refine ⟨restore_range hash candidate streams witness groups name before after instructions bound, ?_⟩
  intro satisfies
  constructor
  · intro instruction member
    rw [instructions, List.mem_append] at member
    rcases member with inBefore | inAfter
    · exact satisfies.instructions instruction
        (List.mem_append_left _ (List.mem_append_left _ inBefore))
    · exact satisfies.instructions instruction (List.mem_append_right _ inAfter)
  · simpa [Program.inputValues, List.filterMap_append, instructions] using satisfies.publicInputs
  · simpa [Program.inputValues, List.filterMap_append, instructions] using satisfies.privateInputs
  · simpa [Program.groups, List.filterMap_append, instructions] using satisfies.groups

theorem equivalent_with_returns (hash : Hash) (candidate : Program) (streams : InputStreams)
    (witness : Assignment) (groups : List (List Scalar)) (returns : List Scalar) (name : String)
    (before after : List Instruction)
    (instructions : candidate.instructions = before ++ after)
    (bound : BoundRead witness name) :
    Satisfies hash candidate streams witness groups returns ↔
      Satisfies hash {candidate with
        instructions := before ++ [.bits (.reference name) 128] ++ after}
        streams witness groups returns := by
  have equivalent :=
    equivalent_on_bound_read hash candidate streams witness groups name before after instructions bound
  constructor
  · intro satisfies
    have restored := equivalent.mp satisfies.circuit
    exact ⟨restored.instructions, restored.publicInputs, restored.privateInputs, restored.groups, by
      simpa [Program.returns, List.flatMap_append, instructions] using satisfies.outputs⟩
  · intro satisfies
    have removed := equivalent.mpr satisfies.circuit
    exact ⟨removed.instructions, removed.publicInputs, removed.privateInputs, removed.groups, by
      simpa [Program.returns, List.flatMap_append, instructions] using satisfies.outputs⟩

/-- This guarantee applies to the two exact emitted programs. The external
Ledger boundary supplies `bound` for the operation's certified input. -/
theorem emitted_equivalent (operation : Backend.LedgerReadOptimization.Operation)
    (hash : Hash) (streams : InputStreams) (witness : Assignment)
    (groups : List (List Scalar)) (returns : List Scalar)
    (bound : BoundRead witness operation.proofInput) :
    ∃ original optimized,
      NativeRelationJson.decode operation.strict = .ok original ∧
      NativeRelationJson.decode operation.optimized = .ok optimized ∧
      (Satisfies hash optimized streams witness groups returns ↔
        Satisfies hash original streams witness groups returns) := by
  obtain ⟨original, optimized, before, after, strictDecoded, optimizedDecoded, removed, restored⟩ :=
    operation.exactRemoval
  refine ⟨original, optimized, strictDecoded, optimizedDecoded, ?_⟩
  rw [restored]
  exact equivalent_with_returns hash optimized streams witness groups returns
    operation.proofInput before after removed bound

end Noctium.Verification.UInt128ReadBound
