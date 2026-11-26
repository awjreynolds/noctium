import Noctium.Verification.GuardedSourceReadTranscript

namespace Noctium.Verification.GuardedVmReadObservations

open Lean Backend Backend.Native NativeRelation ScalarNormalization
open GenericStateCircuitParts GuardedInputTranscript GuardedPublicInputMeaning
open GuardedScalarInput (ReadObservation)
open GenericStateInputValues (scalarType?)

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- Evaluate a checked source read descriptor using its original source guard.
An absent guard means an unconditional active read. The public value comes
from the assignment slot named by the descriptor. -/
def evaluateReadObservation (ctx : EvalContext) (assignment : Assignment)
    (values : EvalEnv) (read : Impact.Read) : Except String ReadObservation := do
  let activity ← read.guard.mapM (fun condition => condition.eval ctx values)
  pure ⟨bit (activity.getD true), assignment ("%input_" ++ read.name)⟩

/-- Evaluate read descriptors in their source order. -/
def evaluateReadObservations (ctx : EvalContext) (assignment : Assignment)
    (values : EvalEnv) (reads : List Impact.Read) : Except String (List ReadObservation) :=
  reads.mapM (evaluateReadObservation ctx assignment values)

private def sourceReadRequirement (read : Impact.Read) : InputRequirement := {
  identifier := "%input_" ++ read.name
  visibility := .«public»
  ty := read.ty
}

private theorem sourceReadInputRequirements_singleton (read : Impact.Read)
    (bindings : read.bindings = [(read.name, read.ty)])
    (supported : (scalarType? read.ty).isSome = _root_.Bool.true) :
    sourceReadInputRequirements read = [sourceReadRequirement read] := by
  cases readType : read.ty with
  | native => simp [sourceReadInputRequirements, sourceReadRequirement, bindings, readType]
  | bool => simp [sourceReadInputRequirements, sourceReadRequirement, bindings, readType]
  | uint width => simp [sourceReadInputRequirements, sourceReadRequirement, bindings, readType]
  | bytes width => rw [readType] at supported; simp [scalarType?] at supported
  | opaqueBytes => rw [readType] at supported; simp [scalarType?] at supported
  | opaqueString => rw [readType] at supported; simp [scalarType?] at supported
  | jubjubScalar => rw [readType] at supported; simp [scalarType?] at supported
  | jubjubPoint => rw [readType] at supported; simp [scalarType?] at supported
  | foreign kind => rw [readType] at supported; simp [scalarType?] at supported

private theorem bit_sourceScalar (active : _root_.Bool) :
    sourceScalar? .bool active = some (bit active) := by
  cases active <;> simp [sourceScalar?, sourceNumber?, bit, scalar_zero, scalar_one]

/-- One public requirement generated from a plain scalar descriptor yields
exactly one observation. Its guard is the original source guard's evaluated
bit, interpreted through the same alias environment used by normalization. -/
theorem guardedReadRequirement_observation
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (assignment : Assignment) (aliases : AliasEnvironment) (values : EvalEnv)
    (types : TypeEnv) (environment : TypedEnvironment hash assignment aliases values types)
    (read : Impact.Read)
    (plain : read.components = [])
    (supported : (scalarType? read.ty).isSome = _root_.Bool.true)
    (guardAdmitted : ∀ condition, read.guard = some condition → ScalarExpression condition)
    (guardEvaluates : ∀ condition, read.guard = some condition →
      ∃ active, condition.eval ctx values = .ok active) :
    ∃ requirement observation,
      guardedReadRequirements aliases read = .ok [requirement] ∧
      requirementObservation hash assignment assignment requirement =
        some (some observation) ∧
      evaluateReadObservation ctx assignment values read = .ok observation := by
  have bindings := GenericStateCheckedReadDecode.supported_plain_read_bindings
    read plain supported
  have sourceRequirements := sourceReadInputRequirements_singleton read bindings supported
  cases sourceGuard : read.guard with
  | none =>
    let requirement := sourceReadRequirement read
    let observation : ReadObservation := ⟨one, assignment ("%input_" ++ read.name)⟩
    refine ⟨requirement, observation, ?_, ?_, ?_⟩
    · simp [guardedReadRequirements, sourceRequirements, sourceGuard, requirement,
        Pure.pure, Except.pure]
    · simp [requirementObservation, sourceReadGuard, sourceReadRequirement,
        requirement, observation]
    · simp [evaluateReadObservation, sourceGuard, observation, bit,
        Bind.bind, Except.bind, Pure.pure, Except.pure, Option.mapM]
  | some condition =>
    obtain ⟨active, sourceEvaluation⟩ := guardEvaluates condition sourceGuard
    obtain ⟨normalized, normalizedAccepted, represented⟩ :=
      normalize_success ctx hash implementation assignment aliases values
        environment.aliases condition (guardAdmitted condition sourceGuard) active sourceEvaluation
    let requirement := {sourceReadRequirement read with activityGuard := some normalized.term}
    let observation : ReadObservation :=
      ⟨bit active, assignment ("%input_" ++ read.name)⟩
    have requirementAccepted : guardedReadRequirements aliases read = .ok [requirement] := by
      simp [guardedReadRequirements, sourceRequirements, sourceGuard,
        normalizedAccepted, requirement, Bind.bind, Except.bind, Pure.pure, Except.pure]
    have guardMeaning : interpret hash assignment normalized.term = some (bit active) :=
      represented.2.2.trans (bit_sourceScalar active)
    refine ⟨requirement, observation, requirementAccepted, ?_, ?_⟩
    · simp [requirementObservation, sourceReadGuard, sourceReadRequirement,
        requirement, guardMeaning, observation]
    · simp [evaluateReadObservation, sourceGuard, sourceEvaluation, observation, bit,
        Bind.bind, Except.bind, Pure.pure, Except.pure, Option.mapM,
        Functor.map, Except.map]

private theorem mapM_cons_decompose {α β : Type} (f : α → Except ε β)
    (head : α) (tail : List α) (result : List β)
    (accepted : (head :: tail).mapM f = .ok result) :
    ∃ value rest, f head = .ok value ∧ tail.mapM f = .ok rest ∧
      result = value :: rest := by
  cases first : f head with
  | error message => simp [List.mapM_cons, first, Bind.bind, Except.bind] at accepted
  | ok value =>
    cases later : tail.mapM f with
    | error message => simp [List.mapM_cons, first, later, Bind.bind, Except.bind] at accepted
    | ok rest =>
      have resultShape : result = value :: rest := by
        simpa [List.mapM_cons, first, later, Bind.bind, Except.bind,
          Pure.pure, Except.pure] using accepted.symm
      exact ⟨value, rest, rfl, rfl, resultShape⟩

/-- A successful observation traversal evaluates every selected source guard. -/
theorem read_guard_evaluates_of_observations
    {ctx : EvalContext} {assignment : Assignment} {values : EvalEnv}
    {reads : List Impact.Read} {observations : List ReadObservation}
    (evaluated : evaluateReadObservations ctx assignment values reads = .ok observations) :
    ∀ read ∈ reads, ∀ condition,
      read.guard = some condition → ∃ active, condition.eval ctx values = .ok active := by
  unfold evaluateReadObservations at evaluated
  induction reads generalizing observations with
  | nil => simp
  | cons head rest ih =>
    obtain ⟨_, _, firstEval, tailEval, _⟩ :=
      mapM_cons_decompose (evaluateReadObservation ctx assignment values) head rest
        observations evaluated
    intro read present condition selected
    rcases List.mem_cons.mp present with same | later
    · subst read
      cases evaluation : condition.eval ctx values with
      | error reason =>
        simp [evaluateReadObservation, selected, Option.mapM, evaluation,
          Bind.bind, Except.bind, Functor.map, Except.map] at firstEval
      | ok active => exact ⟨active, rfl⟩
    · exact ih tailEval read later condition selected

private theorem mapM_filterMap_append {α β : Type}
    (f : α → Option (Option β)) (leftItems rightItems : List α)
    (left right : List β)
    (leftAccepted : (leftItems.mapM f).map (List.filterMap id) = some left)
    (rightAccepted : (rightItems.mapM f).map (List.filterMap id) = some right) :
    ((leftItems ++ rightItems).mapM f).map (List.filterMap id) = some (left ++ right) := by
  cases leftResult : leftItems.mapM f with
  | none => simp [leftResult] at leftAccepted
  | some leftSlots =>
    have leftShape : leftSlots.filterMap id = left := by
      simpa [leftResult] using leftAccepted
    cases rightResult : rightItems.mapM f with
    | none => simp [rightResult] at rightAccepted
    | some rightSlots =>
      have rightShape : rightSlots.filterMap id = right := by
        simpa [rightResult] using rightAccepted
      rw [List.mapM_append, leftResult, rightResult]
      simp [leftShape, rightShape, List.filterMap_append]

/-- A source observation with a false guard must carry the canonical zero
public value. The premise comes from the checked artifact's inactive-row rule
after guard normalization identifies source activity. -/
theorem evaluateReadObservation_inactive_zero
    (ctx : EvalContext) (assignment : Assignment) (values : EvalEnv)
    (read : Impact.Read) (observation : ReadObservation)
    (evaluated : evaluateReadObservation ctx assignment values read = .ok observation)
    (inactiveZero : ∀ condition, read.guard = some condition →
      condition.eval ctx values = .ok false → assignment ("%input_" ++ read.name) = zero) :
    observation.guard = one ∨ (observation.guard = zero ∧ observation.value = zero) := by
  cases sourceGuard : read.guard with
  | none =>
    have shape : observation = ⟨bit true, assignment ("%input_" ++ read.name)⟩ := by
      simpa [evaluateReadObservation, sourceGuard, Pure.pure, Except.pure,
        Bind.bind, Except.bind, Option.mapM, Functor.map, Except.map] using evaluated.symm
    subst observation
    exact Or.inl (by simp [bit])
  | some condition =>
    cases sourceEval : condition.eval ctx values with
    | error message =>
      simp [evaluateReadObservation, sourceGuard, sourceEval, Bind.bind, Except.bind,
        Option.mapM, Functor.map, Except.map] at evaluated
    | ok active =>
      have shape : observation = ⟨bit active, assignment ("%input_" ++ read.name)⟩ := by
        simpa [evaluateReadObservation, sourceGuard, sourceEval, Pure.pure,
          Bind.bind, Except.bind, Except.pure, Option.mapM, Functor.map, Except.map] using evaluated.symm
      subst observation
      cases active with
      | true => exact Or.inl (by simp [bit])
      | false =>
        have valueZero := inactiveZero condition sourceGuard sourceEval
        exact Or.inr ⟨by simp [bit], valueZero⟩

/-- Lifting the descriptor theorem preserves source order. The checked
requirement blocks and direct source evaluation return the same observation
list, one slot per plain scalar descriptor. Inactive observations carry zero. -/
theorem guardedReadRequirements_observations
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (assignment : Assignment) (aliases : AliasEnvironment) (values : EvalEnv)
    (types : TypeEnv) (environment : TypedEnvironment hash assignment aliases values types)
    (reads : List Impact.Read) (blocks : List (List InputRequirement))
    (blocksAccepted : reads.mapM (guardedReadRequirements aliases) = .ok blocks)
    (plain : ∀ read ∈ reads, read.components = [])
    (supported : ∀ read ∈ reads,
      (scalarType? read.ty).isSome = _root_.Bool.true)
    (guardAdmitted : ∀ read ∈ reads, ∀ condition,
      read.guard = some condition → ScalarExpression condition)
    (guardEvaluates : ∀ read ∈ reads, ∀ condition,
      read.guard = some condition → ∃ active, condition.eval ctx values = .ok active)
    (inactiveZero : ∀ read ∈ reads, ∀ condition,
      read.guard = some condition → condition.eval ctx values = .ok false →
      assignment ("%input_" ++ read.name) = zero) :
    ∃ observations,
      (blocks.flatten.mapM (requirementObservation hash assignment assignment)).map
        (List.filterMap id) = some observations ∧
      evaluateReadObservations ctx assignment values reads = .ok observations ∧
      ∀ observation ∈ observations,
        observation.guard = one ∨ (observation.guard = zero ∧ observation.value = zero) := by
  induction reads generalizing blocks with
  | nil =>
    simp only [List.mapM_nil] at blocksAccepted
    cases blocksAccepted
    exact ⟨[], by rfl, rfl, by simp⟩
  | cons read rest ih =>
    obtain ⟨block, restBlocks, firstAccepted, restAccepted, blocksEq⟩ :=
      mapM_cons_decompose (guardedReadRequirements aliases) read rest blocks blocksAccepted
    obtain ⟨requirement, observation, requirementAccepted, requirementObserved,
      evaluated⟩ := guardedReadRequirement_observation ctx hash implementation assignment
        aliases values types environment read (plain read (by simp))
        (supported read (by simp))
        (fun condition guarded => guardAdmitted read (by simp) condition guarded)
        (fun condition guarded => guardEvaluates read (by simp) condition guarded)
    have blockShape : block = [requirement] :=
      Except.ok.inj (firstAccepted.symm.trans requirementAccepted)
    have blocksShape : blocks = [requirement] :: restBlocks := by
      rw [blocksEq, blockShape]
    obtain ⟨tailObservations, tailRequirements, tailEvaluated, tailCanonical⟩ :=
      ih restBlocks restAccepted
        (fun next present => plain next (List.mem_cons_of_mem _ present))
        (fun next present => supported next (List.mem_cons_of_mem _ present))
        (fun next present condition guarded =>
          guardAdmitted next (List.mem_cons_of_mem _ present) condition guarded)
        (fun next present condition guarded =>
          guardEvaluates next (List.mem_cons_of_mem _ present) condition guarded)
        (fun next present condition guarded inactive =>
          inactiveZero next (List.mem_cons_of_mem _ present) condition guarded inactive)
    have headCanonical := evaluateReadObservation_inactive_zero ctx assignment values
      read observation evaluated (inactiveZero read (by simp))
    refine ⟨observation :: tailObservations, ?_, ?_, ?_⟩
    · have headRequirements :
          ([requirement].mapM (requirementObservation hash assignment assignment)).map
            (List.filterMap id) = some [observation] := by
        simp [requirementObserved]
      rw [blocksShape]
      simp only [List.flatten_cons]
      exact mapM_filterMap_append (requirementObservation hash assignment assignment)
        [requirement] restBlocks.flatten [observation] tailObservations
        headRequirements tailRequirements
    · have tailMapM : rest.mapM (evaluateReadObservation ctx assignment values) =
          .ok tailObservations := by
        simpa [evaluateReadObservations] using tailEvaluated
      simp [evaluateReadObservations, List.mapM_cons, evaluated, tailMapM,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    · intro found member
      rcases List.mem_cons.mp member with equal | member
      · subst found
        exact headCanonical
      · exact tailCanonical found member

end Noctium.Verification.GuardedVmReadObservations
