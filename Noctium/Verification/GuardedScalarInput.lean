import Noctium.Verification.NativeInputOrdinal
import Noctium.Verification.GenericStateInputValues
import Noctium.Verification.GuardedEffectPrefix

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

/-- The witness value assigned to one positional public input row, together
with the activity guard that controls transcript consumption. -/
structure ReadObservation where
  guard : Scalar
  value : Scalar
  deriving Repr, DecidableEq

/-- Values consumed from the transcript in public input order. -/
def activeReadValues : List ReadObservation → List Scalar
  | [] => []
  | observation :: rest =>
      if observation.guard = one then
        observation.value :: activeReadValues rest
      else activeReadValues rest

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

private theorem consume_success {guard value : Scalar} {stream remaining : List Scalar}
    (accepted : consume guard stream = some (value, remaining)) :
    (guard = one ∧ stream = value :: remaining) ∨
      (guard = zero ∧ value = zero ∧ stream = remaining) := by
  by_cases active : guard = one
  · subst guard
    cases stream with
    | nil => simp [consume] at accepted
    | cons first rest =>
      simp [consume] at accepted
      rcases accepted with ⟨firstEq, restEq⟩
      subst value
      subst remaining
      exact Or.inl ⟨rfl, rfl⟩
  · by_cases inactive : guard = zero
    · subst guard
      simp [consume, zero_ne_one] at accepted
      rcases accepted with ⟨valueEq, streamEq⟩
      subst value
      exact Or.inr ⟨rfl, rfl, streamEq⟩
    · simp [consume, active, inactive] at accepted

/-- Successful preprocessing assigns one value to every positional row. The
public transcript supplies active row values in order. Inactive rows assign
zero and consume no transcript field. Non-Boolean guards reject. -/
theorem consumeReads_iff (observations : List ReadObservation)
    (transcript remaining : List Scalar) :
    consumeReads (observations.map ReadObservation.guard) transcript =
        some (observations.map ReadObservation.value, remaining) ↔
      transcript = activeReadValues observations ++ remaining ∧
        ∀ observation ∈ observations,
          observation.guard = one ∨
            (observation.guard = zero ∧ observation.value = zero) := by
  induction observations generalizing transcript with
  | nil => simp [consumeReads, activeReadValues]
  | cons observation rest ih =>
    cases observation with
    | mk guard value =>
      constructor
      · intro accepted
        change (match consume guard transcript with
          | none => none
          | some (headValue, nextStream) =>
              match consumeReads (rest.map ReadObservation.guard) nextStream with
              | none => none
              | some (tailValues, finalStream) => some (headValue :: tailValues, finalStream)) =
          some (value :: rest.map ReadObservation.value, remaining) at accepted
        cases head : consume guard transcript with
        | none => simp [head] at accepted
        | some pair =>
          rcases pair with ⟨headValue, nextStream⟩
          cases tail : consumeReads (rest.map ReadObservation.guard) nextStream with
          | none => simp [head, tail] at accepted
          | some tailPair =>
            rcases tailPair with ⟨tailValues, finalStream⟩
            have resultParts := by simpa [head, tail] using accepted
            rcases resultParts with ⟨⟨headEq, tailValuesEq⟩, finalEq⟩
            subst headValue
            have tailAccepted : consumeReads (rest.map ReadObservation.guard) nextStream =
                some (rest.map ReadObservation.value, remaining) := by
              rw [tail]
              simp [tailValuesEq, finalEq]
            have headCase := consume_success head
            have tailFacts := (ih nextStream).mp tailAccepted
            rcases headCase with ⟨guardOne, streamEq⟩ | ⟨guardZero, valueZero, streamEq⟩
            · have guardEq : guard = one := by simpa using guardOne
              subst guard
              have transcriptEq : transcript = value :: (activeReadValues rest ++ remaining) := by
                rw [streamEq, tailFacts.1]
              refine ⟨?_, ?_⟩
              · simpa [activeReadValues] using transcriptEq
              · intro row member
                rcases List.mem_cons.mp member with headMember | tailMember
                · cases headMember
                  exact Or.inl rfl
                · exact tailFacts.2 row tailMember
            · have guardEq : guard = zero := by simpa using guardZero
              have valueEq : value = zero := by simpa using valueZero
              subst guard
              subst value
              have transcriptEq : transcript = activeReadValues rest ++ remaining := by
                rw [streamEq, tailFacts.1]
              refine ⟨?_, ?_⟩
              · simpa [activeReadValues, zero_ne_one] using transcriptEq
              · intro row member
                rcases List.mem_cons.mp member with headMember | tailMember
                · cases headMember
                  exact Or.inr ⟨rfl, rfl⟩
                · exact tailFacts.2 row tailMember
      · rintro ⟨transcriptEq, rowChecks⟩
        have headCheck := rowChecks ⟨guard, value⟩ (by simp)
        have tailChecks : ∀ row ∈ rest,
            row.guard = one ∨ (row.guard = zero ∧ row.value = zero) := by
          intro row member
          exact rowChecks row (List.mem_cons_of_mem _ member)
        cases headCheck with
        | inl guardOne =>
          change guard = one at guardOne
          subst guard
          have tailAccepted := (ih (activeReadValues rest ++ remaining)).mpr
            ⟨rfl, tailChecks⟩
          have transcriptEq' :
              transcript = value :: (activeReadValues rest ++ remaining) := by
            simpa [activeReadValues] using transcriptEq
          rw [transcriptEq']
          simp [consumeReads, consume_active_cons, tailAccepted]
        | inr inactive =>
          rcases inactive with ⟨guardZero, valueZero⟩
          change guard = zero at guardZero
          change value = zero at valueZero
          subst guard
          subst value
          have tailAccepted := (ih (activeReadValues rest ++ remaining)).mpr
            ⟨rfl, tailChecks⟩
          have transcriptEq' : transcript = activeReadValues rest ++ remaining := by
            simpa [activeReadValues, zero_ne_one] using transcriptEq
          rw [transcriptEq']
          simp [consumeReads, consume_inactive, tailAccepted]

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

open ScalarNormalization in
/-- The Boolean value of an admitted source guard determines whether the
accepted public read consumes a scalar. The selected expected input must
carry the normalized term of this source guard. -/
theorem consume_accepted_public_read_source
    {hash : Hash} {inputs witness : Assignment} {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Lean.Json}
    {requirement : Backend.Native.InputRequirement} {guard : Operand}
    (ctx : EvalContext) (types : TypeEnv) (aliases : Backend.Native.AliasEnvironment)
    (values : EvalEnv) (condition : Expr .bool) (normalized : Backend.Native.Normalized)
    (stream : List Scalar)
    (implementation : HashAgreement ctx hash)
    (environment : TypedEnvironment hash inputs aliases values types)
    (admission : ScalarExpression condition)
    (valid : condition.validate Capabilities.scalarFragment types = .ok ())
    (normal : Backend.Native.normalize aliases condition = .ok normalized)
    (requirements : Requirements hash inputs normalized)
    (invariant : ScalarValidationMeaning.StateMeaning hash inputs witness state)
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (guarded : requirement.activityGuard = some normalized.term)
    (opcode : Backend.Native.stringField raw "op" = .ok "public_input")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : NativeRelationJson.decodeOperandField raw "guard" = .ok guard) :
    ∃ active : Bool, condition.eval ctx values = .ok active ∧
      guard.read witness = bit active ∧
      consume (guard.read witness) stream =
        if active then
          match stream with
          | value :: rest => some (value, rest)
          | [] => none
        else some (zero, stream) := by
  obtain ⟨active, evaluated, _, _, meaning⟩ := normalize_sound ctx hash implementation inputs
    types aliases values environment condition admission normalized valid normal requirements
  obtain ⟨guardMeaning, _⟩ := NativeInputOrdinal.accepted_guarded_public_input_guard_meaning
    invariant selected nonforeignInput guarded opcode accepted decoded
  have encoded : sourceScalar? .bool active = some (bit active) := by
    cases active <;> simp [sourceScalar?, bit]
  have same := Option.some.inj (guardMeaning.symm.trans (meaning.trans encoded))
  refine ⟨active, evaluated, same, ?_⟩
  rw [same]
  cases active <;> cases stream <;> simp [bit, consume, zero_ne_one]

open ScalarNormalization in
/-- An active scalar cell read executes the same source transition as an
unconditional read, including when the cell is missing or malformed. -/
theorem run_active_scalarCell_read (ctx : EvalContext) (env : EvalEnv)
    (ledger : LedgerState) (cell destination : String) {ty : Ty}
    (supported : ScalarType ty) (guard : Expr .bool)
    (active : guard.eval ctx env = .ok true) :
    runEffectsWithGuardsAndEnv ctx [.readCell cell destination ty] [some guard] env ledger =
      runEffectWithEnv ctx (.readCell cell destination ty) env ledger := by
  dsimp [runEffectsWithGuardsAndEnv, List.zipIdx, List.all,
    List.isEmpty, List.length, Option.isNone, Option.getD, Option.isSome,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [List.forIn_cons]
  dsimp [List.getElem?_cons_zero, Option.getD, Option.isSome,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [active]
  dsimp [runEffectWithEnv, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases ledger.cells.lookup cell with
  | none => rfl
  | some raw =>
    dsimp only []
    cases raw.as ty with
    | none => rfl
    | some value =>
      dsimp only []
      cases supported with
      | native =>
        by_cases bound : value < ctx.modulus <;> simp [canonical_eq, bound] <;> rfl
      | bool => rfl
      | uint maximum =>
        by_cases invalid : (ScalarPolicy.maxUint < maximum ∨ maximum < value) ∨
            ctx.modulus ≤ value <;> simp [canonical_eq, invalid] <;> rfl

open GenericStateInputValues ScalarNormalization in
/-- The production source evaluator binds the decoded zero for an inactive
scalar cell read. Skipping the read preserves the current ledger state and
does not require the cell to exist. -/
theorem run_inactive_scalarCell_read (ctx : EvalContext) (env : EvalEnv)
    (ledger : LedgerState) (cell destination : String) {ty : Ty}
    (supported : ScalarType ty) (guard : Expr .bool)
    (inactive : guard.eval ctx env = .ok false) :
    runEffectsWithGuardsAndEnv ctx [.readCell cell destination ty] [some guard] env ledger =
      .ok ((destination, Value.pack ty (sourceValue supported zero)) :: env, ledger) := by
  dsimp [runEffectsWithGuardsAndEnv, List.zipIdx, List.all,
    List.isEmpty, List.length, Option.isNone, Option.getD, Option.isSome,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [List.forIn_cons]
  dsimp [List.getElem?_cons_zero, Option.getD, Option.isSome,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [inactive]
  cases supported <;> rfl

open ScalarNormalization in
/-- When its guard is true, a scalar source Map read takes the ordinary step,
with the same typed result or error. -/
theorem run_active_map_read (ctx : EvalContext) (env : EvalEnv)
    (ledger : LedgerState) (name destination : String) {keyTy valueTy : Ty}
    (key : Expr keyTy) (supported : ScalarType valueTy)
    (guard : Expr .bool) (active : guard.eval ctx env = .ok true) :
    runEffectsWithGuardsAndEnv ctx [.readMap name destination keyTy valueTy key] [some guard]
      env ledger = runEffectWithEnv ctx (.readMap name destination keyTy valueTy key) env ledger := by
  dsimp [runEffectsWithGuardsAndEnv, List.zipIdx, List.all,
    List.isEmpty, List.length, Option.isNone, Option.getD, Option.isSome,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [List.forIn_cons]
  dsimp [List.getElem?_cons_zero, Option.getD, Option.isSome,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [active]
  dsimp [runEffectWithEnv, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases keyEval : key.eval ctx env with
  | error message => rfl
  | ok resolved =>
    dsimp only []
    cases ledger.maps.lookup name with
    | none => rfl
    | some entries =>
      dsimp only []
      cases entries.lookup (Value.pack keyTy resolved) with
      | none => rfl
      | some raw =>
        dsimp only []
        cases raw.as valueTy with
        | none => rfl
        | some value =>
          dsimp only []
          cases supported with
          | native =>
            by_cases bound : value < ctx.modulus <;> simp [canonical_eq, bound] <;> rfl
          | bool => rfl
          | uint maximum =>
            by_cases invalid : (ScalarPolicy.maxUint < maximum ∨ maximum < value) ∨
                ctx.modulus ≤ value <;> simp [canonical_eq, invalid] <;> rfl

open GenericStateInputValues ScalarNormalization in
/-- An inactive scalar Map read binds the decoded default and leaves the
ledger intact, without evaluating its key or looking up the map. -/
theorem run_inactive_scalarMap_read (ctx : EvalContext) (env : EvalEnv)
    (ledger : LedgerState) (name destination : String) {keyTy valueTy : Ty}
    (key : Expr keyTy) (supported : ScalarType valueTy) (guard : Expr .bool)
    (inactive : guard.eval ctx env = .ok false) :
    runEffectsWithGuardsAndEnv ctx [.readMap name destination keyTy valueTy key] [some guard]
      env ledger = .ok ((destination, Value.pack valueTy (sourceValue supported zero)) :: env, ledger) := by
  dsimp [runEffectsWithGuardsAndEnv, List.zipIdx, List.all,
    List.isEmpty, List.length, Option.isNone, Option.getD, Option.isSome,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [List.forIn_cons]
  dsimp [List.getElem?_cons_zero, Option.getD, Option.isSome,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [inactive]
  cases supported <;> rfl

open Backend GenericStateInputValues ScalarNormalization in
/-- The compiled read descriptor ties an inactive preprocessing row to the
same typed default bound by the production source evaluator. The source
guard's inactivity and the row's zero guard are supplied by guard agreement. -/
theorem inactive_guardedCell_read_agreement (ctx : EvalContext) (env : EvalEnv)
    (ledger : LedgerState) (state : List StateDecl) (cell destination : String)
    {ty : Ty} (supported : ScalarType ty) (condition : Expr .bool)
    (before after : Impact.Plan) (witness : Assignment) (stream remaining : List Scalar)
    (lowered : Impact.appendEffectWithActivity state (.readCell cell destination ty)
      (some condition) before = .ok after)
    (inactive : condition.eval ctx env = .ok false)
    (observed : consume zero stream =
      some (witness ("%input_" ++ destination), remaining)) :
    ∃ read,
      after.reads = before.reads ++ [read] ∧ read.guard = some condition ∧
      remaining = stream ∧
      decodeRead read witness = .ok (destination, Value.pack ty (sourceValue supported zero)) ∧
      runEffectsWithGuardsAndEnv ctx [.readCell cell destination ty] [some condition] env ledger =
        .ok ((destination, Value.pack ty (sourceValue supported zero)) :: env, ledger) := by
  obtain ⟨_, _, read, named, typed, guarded, reads, _, _⟩ :=
    GuardedEffectPrefix.appendEffectWithActivity_readCell_provenance
      state cell destination ty condition before after lowered
  simp only [consume_inactive, Option.some.injEq, Prod.mk.injEq] at observed
  refine ⟨read, reads, guarded, observed.2.symm, ?_,
    run_inactive_scalarCell_read ctx env ledger cell destination supported condition inactive⟩
  subst destination
  subst ty
  simp [decodeRead, scalarType?_supported supported, ← observed.1]

open Backend GenericStateInputValues ScalarNormalization in
/-- The exact guarded Map-read descriptor and the inactive source step use
the same zero candidate. The row's zero guard leaves the transcript untouched. -/
theorem inactive_guardedMap_read_agreement (ctx : EvalContext) (env : EvalEnv)
    (ledger : LedgerState) (state : List StateDecl) (name destination : String)
    {keyTy valueTy : Ty} (key : Expr keyTy) (supported : ScalarType valueTy)
    (condition : Expr .bool) (before after : Impact.Plan)
    (witness : Assignment) (stream remaining : List Scalar)
    (lowered : Impact.appendEffectWithActivity state (.readMap name destination keyTy valueTy key)
      (some condition) before = .ok after)
    (inactive : condition.eval ctx env = .ok false)
    (observed : consume zero stream =
      some (witness ("%input_" ++ destination), remaining)) :
    let read : Impact.Read := {name := destination, ty := valueTy, guard := some condition}
    after.reads = before.reads ++ [read] ∧ remaining = stream ∧
      decodeRead read witness = .ok (destination, Value.pack valueTy (sourceValue supported zero)) ∧
      runEffectsWithGuardsAndEnv ctx [.readMap name destination keyTy valueTy key] [some condition]
        env ledger = .ok ((destination, Value.pack valueTy (sourceValue supported zero)) :: env, ledger) := by
  dsimp only
  have exactReads := GuardedEffectPrefix.appendEffectWithActivity_readMap_read_suffix
    state name destination keyTy valueTy key condition before after lowered
  simp only [consume_inactive, Option.some.injEq, Prod.mk.injEq] at observed
  refine ⟨exactReads, observed.2.symm, ?_,
    run_inactive_scalarMap_read ctx env ledger name destination key supported condition inactive⟩
  simp [decodeRead, scalarType?_supported supported, ← observed.1]

end Noctium.Verification.GuardedScalarInput
