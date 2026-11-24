import Noctium.Verification.NativeInputOrdinal

namespace Noctium.Verification.GuardedScalarInput

open Noctium.Verification.NativeRelation

/-- Preprocessing for one guarded Native public input. An active row consumes
the next transcript scalar. An inactive row supplies zero without advancing
the stream. Non-Boolean guards reject. This models transcript preprocessing
only, not the circuit's witness-allocation constraints. -/
def consume (guard : Scalar) (stream : List Scalar) : Option (Scalar × List Scalar) :=
  if guard = one then
    match stream with
    | value :: rest => some (value, rest)
    | [] => none
  else if guard = zero then
    some (zero, stream)
  else
    none

theorem consume_active_cons (value : Scalar) (rest : List Scalar) :
    consume one (value :: rest) = some (value, rest) := by
  simp [consume]

theorem consume_active_empty :
    consume one [] = none := by
  simp [consume]

theorem consume_inactive (stream : List Scalar) :
    consume zero stream = some (zero, stream) := by
  simp [consume, zero_ne_one]

theorem consume_rejects_nonboolean (guard : Scalar) (stream : List Scalar)
    (notZero : guard ≠ zero) (notOne : guard ≠ one) :
    consume guard stream = none := by
  simp [consume, notOne, notZero]

/-- Interpret an ordered sequence of guarded public input rows. The first
component records one witness value per static row, including zero for
inactive rows. The second component is the unconsumed public transcript. -/
def consumeReads : List Scalar → List Scalar → Option (List Scalar × List Scalar)
  | [], stream => some ([], stream)
  | guard :: guards, stream =>
    match consume guard stream with
    | none => none
    | some (value, remaining) =>
      match consumeReads guards remaining with
      | none => none
      | some (values, finalStream) => some (value :: values, finalStream)

/-- Splitting a guarded input schedule preserves the same ordered stream
transition. -/
theorem consumeReads_append (first second : List Scalar) (stream : List Scalar) :
    consumeReads (first ++ second) stream =
      (consumeReads first stream).bind fun (firstValues, remaining) =>
        (consumeReads second remaining).map fun (secondValues, finalStream) =>
          (firstValues ++ secondValues, finalStream) := by
  induction first generalizing stream with
  | nil => simp [consumeReads]
  | cons guard guards ih =>
    cases consumed : consume guard stream with
    | none => simp [List.cons_append, consumeReads, consumed]
    | some pair =>
      rcases pair with ⟨value, remaining⟩
      simp only [List.cons_append, consumeReads, consumed]
      cases tail : consumeReads guards remaining with
      | none =>
        rw [ih remaining]
        simp [tail]
      | some tailPair =>
        rcases tailPair with ⟨values, finalStream⟩
        rw [ih remaining]
        simp only [tail, Option.bind_some]
        cases later : consumeReads second finalStream <;>
          simp [List.cons_append]

/-- If every scheduled row is active, preprocessing rejects when the public
transcript has fewer values than rows. -/
theorem consumeReads_active_stream_exhausted
    (guards : List Scalar) (stream : List Scalar)
    (allActive : ∀ guard ∈ guards, guard = one)
    (tooFew : guards.length > stream.length) :
    consumeReads guards stream = none := by
  induction guards generalizing stream with
  | nil => simp at tooFew
  | cons guard guards ih =>
    have guardActive : guard = one := allActive guard (by simp)
    have tailActive : ∀ item ∈ guards, item = one := by
      intro item member
      exact allActive item (by simp [member])
    cases stream with
    | nil => simp [consumeReads, guardActive, consume]
    | cons value remaining =>
      have tailTooFew : guards.length > remaining.length := by
        simp at tooFew
        omega
      simp [consumeReads, consume, guardActive,
        ih remaining tailActive tailTooFew]

/-- This concrete schedule shows the distinct static-row and transcript
orders: inactive rows contribute zero, while active rows consume values in
order. -/
theorem consumeReads_interleaved_example (first second : Scalar) :
    consumeReads [zero, one, zero, one] [first, second] =
      some ([zero, first, zero, second], []) := by
  simp [consumeReads, consume, zero_ne_one]

/-- The same interleaved schedule rejects if its second active row has no
transcript scalar left. -/
theorem consumeReads_interleaved_exhausted (first : Scalar) :
    consumeReads [zero, one, zero, one] [first] = none := by
  simp [consumeReads, consume, zero_ne_one]

/-- For an accepted ledger read, the independently decoded operand applies
the stream transition selected by the source guard. The false branch has a
zero default and the true branch consumes the next transcript scalar. -/
theorem consume_accepted_public_read
    {hash : Hash} {inputs witness : Assignment} {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Lean.Json}
    {requirement : Backend.Native.InputRequirement}
    {guardTerm : Backend.Native.Term} {guard : Operand}
    (stream : List Scalar)
    (invariant : ScalarValidationMeaning.StateMeaning hash inputs witness state)
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (guarded : requirement.activityGuard = some guardTerm)
    (opcode : Backend.Native.stringField raw "op" = .ok "public_input")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : NativeRelationJson.decodeOperandField raw "guard" = .ok guard) :
    (ScalarNormalization.interpret hash inputs guardTerm = some zero ∧
      consume (guard.read witness) stream = some (zero, stream)) ∨
    (ScalarNormalization.interpret hash inputs guardTerm = some one ∧
      consume (guard.read witness) stream = match stream with
        | value :: rest => some (value, rest)
        | [] => none) := by
  obtain ⟨meaning, inactive | active⟩ :=
    NativeInputOrdinal.accepted_guarded_public_input_guard_meaning
      invariant selected nonforeignInput guarded opcode accepted decoded
  · left
    simpa [inactive, consume_inactive] using meaning
  · right
    rw [active] at meaning ⊢
    exact ⟨meaning, by cases stream <;> simp [consume]⟩

end Noctium.Verification.GuardedScalarInput
