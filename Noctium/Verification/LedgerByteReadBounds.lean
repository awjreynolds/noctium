import Noctium.Backend.LedgerReadOptimization
import Noctium.Verification.RangeDedupKernel
import Noctium.Verification.ScalarTermMeaning

namespace Noctium.Verification.LedgerByteReadBounds

open NativeRelation Backend.LedgerReadOptimization

/-- The authenticated Popeq must supply the bytes for this exact input chunk. -/
def BoundChunk (witness : Assignment) (chunk : String × Nat) : Prop :=
  ∃ bytes : List UInt8, 8 * bytes.length = chunk.2 ∧
    (witness chunk.1).val = Backend.Native.littleEndian (bytes.map UInt8.toNat)

theorem chunk_lt (witness : Assignment) (chunk : String × Nat)
    (bound : BoundChunk witness chunk) : (witness chunk.1).val < 2 ^ chunk.2 := by
  obtain ⟨bytes, width, value⟩ := bound
  have inRange := ScalarTermMeaning.littleEndian_lt_pow_of_bytes (bytes.map UInt8.toNat) (by
    intro value member
    obtain ⟨byte, _, rfl⟩ := List.mem_map.mp member
    exact byte.toFin.isLt)
  rw [List.length_map] at inRange
  rw [value, ← width, Nat.pow_mul]
  exact inRange

private theorem dropped_holds (hash : Hash) (witness : Assignment)
    (chunks : List (String × Nat)) (instruction : Instruction)
    (bounds : ∀ chunk ∈ chunks, BoundChunk witness chunk)
    (dropped : retainRecordInstruction chunks instruction = false) :
    instruction.Holds hash witness := by
  cases instruction <;> try simp [retainRecordInstruction] at dropped
  case bits operand width =>
    cases operand with
    | immediate => simp at dropped
    | reference name =>
      have present : (name, width) ∈ chunks := List.contains_iff_mem.mp (by
        simpa [retainRecordInstruction] using dropped)
      exact chunk_lt witness (name, width) (bounds (name, width) present)

/-- Removing exactly the certified checks preserves ordered inputs, ledger
groups, returns, and satisfaction when the ledger supplies the bounded chunks. -/
theorem equivalent (program : Program) (hash : Hash) (streams : InputStreams)
    (witness : Assignment) (groups : List (List Scalar)) (returns : List Scalar)
    (chunks : List (String × Nat)) (bounds : ∀ chunk ∈ chunks, BoundChunk witness chunk) :
    Satisfies hash program streams witness groups returns ↔
      Satisfies hash {program with instructions :=
        program.instructions.filter (retainRecordInstruction chunks)} streams witness groups returns := by
  apply RangeDedupKernel.satisfies_iff
  · simp only [List.filter_filter]
    congr 1
    funext instruction
    cases instruction <;> simp [retainRecordInstruction, RangeDedup.nonRange]
  · constructor
    · intro holds instruction inFiltered
      exact holds instruction (List.mem_filter.mp inFiltered).1
    · intro holds instruction member
      cases retained : retainRecordInstruction chunks instruction with
      | false => exact dropped_holds hash witness chunks instruction bounds retained
      | true => exact holds instruction (List.mem_filter.mpr ⟨member, retained⟩)

theorem emitted_equivalent (operation : RecordOperation) (hash : Hash)
    (streams : InputStreams) (witness : Assignment)
    (groups : List (List Scalar)) (returns : List Scalar)
    (bounds : ∀ chunk ∈ operation.certificate.chunks, BoundChunk witness chunk) :
    ∃ original optimized,
      NativeRelationJson.decodeScalarCall operation.strict = .ok original ∧
      NativeRelationJson.decodeScalarCall operation.optimized = .ok optimized ∧
      optimized.arguments = original.arguments ∧
      (Satisfies hash original.body streams witness groups returns ↔
        Satisfies hash optimized.body streams witness groups returns) := by
  obtain ⟨original, optimized, strictDecoded, optimizedDecoded, removed⟩ := operation.exactRemoval
  refine ⟨original, optimized, strictDecoded, optimizedDecoded, ?_, ?_⟩
  · rw [removed]
    rfl
  · rw [removed]
    exact equivalent original.body hash streams witness groups returns operation.certificate.chunks bounds

end Noctium.Verification.LedgerByteReadBounds
