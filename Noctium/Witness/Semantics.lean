import Noctium.Witness

namespace Noctium.Witness.Semantics
open Helpers
universe u

/-- All term positions in source order. A branch contributes its condition and
both source arms. A loop contributes its body once. This is a lexical inventory.
The actual host schedule depends on execution. -/
def expressionSchedule : List Statement → List Term
  | [] => []
  | .bind _ _ value :: rest => value :: expressionSchedule rest
  | .evaluate value :: rest => value :: expressionSchedule rest
  | .assert value :: rest => value :: expressionSchedule rest
  | .return value :: _ => value.toList
  | .stage _ _ _ value :: rest => value :: expressionSchedule rest
  | .readCell .. :: rest => expressionSchedule rest
  | .writeCell _ _ value :: rest => value :: expressionSchedule rest
  | .readMap _ _ _ _ key :: rest | .readMember _ _ _ _ key :: rest =>
      key :: expressionSchedule rest
  | .writeMap _ _ _ key value :: rest => key :: value :: expressionSchedule rest
  | .forRange _ _ _ body :: rest => expressionSchedule body ++ expressionSchedule rest
  | .emitEvent _ payload :: rest => payload :: expressionSchedule rest
  | .branch condition yes no :: rest =>
      condition :: expressionSchedule yes ++ expressionSchedule no ++ expressionSchedule rest
termination_by body => sizeOf body

/-- Static witness-call occurrences follow expression child order. This list
preserves call sites; runtime invocation counts still depend on branch choices. -/
def witnessOccurrences : Term → List (String × String)
  | .witnessCall site name arguments =>
      arguments.flatMap witnessOccurrences ++ [(site, name)]
  | .binary _ left right | .boolAnd left right | .boolOr left right | .boolXor left right
  | .eq left right | .poseidon2 _ left right
  | .andThen left right | .orElse left right | .index left right =>
      witnessOccurrences left ++ witnessOccurrences right
  | .curve _ arguments | .bytes _ arguments => arguments.flatMap witnessOccurrences
  | .cast _ value | .disclose _ value | .effect _ _ value | .bytesAt value _
  | .at _ value | .project value _ => witnessOccurrences value
  | .select condition yes no | .ite condition yes no =>
      witnessOccurrences condition ++ witnessOccurrences yes ++ witnessOccurrences no
  | .call _ arguments | .composite _ arguments => arguments.flatMap witnessOccurrences
  | _ => []

def scheduledWitnessOccurrences (body : List Statement) : List (String × String) :=
  (expressionSchedule body).flatMap witnessOccurrences

/-- A proof induction measure counting statements and nested branch bodies. -/
def statementWeight : List Statement → Nat
  | [] => 0
  | .branch _ yes no :: rest => 1 + statementWeight yes + statementWeight no + statementWeight rest
  | .forRange _ _ _ body :: rest => 1 + statementWeight body + statementWeight rest
  | _ :: rest => 1 + statementWeight rest
termination_by body => sizeOf body

/-- Replacing a private stage with evaluation preserves the exact ordered source
term positions, including nested branches and the value used by the stage. -/
theorem eraseStages_preserves_expressionSchedule (body : List Statement) :
    expressionSchedule (eraseStages body) = expressionSchedule body := by
  have helper : ∀ n (body : List Statement), statementWeight body = n →
      expressionSchedule (eraseStages body) = expressionSchedule body := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro body sizeEq
      cases body with
      | nil => simp [eraseStages, expressionSchedule] at sizeEq ⊢
      | cons statement rest =>
        cases statement with
        | bind name type value =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [eraseStages, expressionSchedule] using hr
        | evaluate value =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [eraseStages, expressionSchedule] using hr
        | assert value =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [eraseStages, expressionSchedule] using hr
        | «return» value => cases value <;> simp [eraseStages, expressionSchedule]
        | stage capability key type value =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [eraseStages, expressionSchedule] using hr
        | readCell state destination type =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [eraseStages, expressionSchedule] using hr
        | writeCell state type value =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [eraseStages, expressionSchedule] using hr
        | readMap state destination keyTy valueTy key =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [eraseStages, expressionSchedule] using hr
        | readMember state destination keyTy valueTy key =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [eraseStages, expressionSchedule] using hr
        | writeMap state keyTy valueTy key value =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [eraseStages, expressionSchedule] using hr
        | forRange index start stop loopBody =>
          have hb := ih (statementWeight loopBody)
            (by rw [← sizeEq]; simp [statementWeight]; omega) loopBody rfl
          have hr := ih (statementWeight rest)
            (by rw [← sizeEq]; simp [statementWeight]; omega) rest rfl
          simp [eraseStages, expressionSchedule, hb, hr]
        | emitEvent kind payload =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [eraseStages, expressionSchedule] using hr
        | branch condition yes no =>
          have hy := ih (statementWeight yes) (by rw [← sizeEq]; simp [statementWeight]; omega) yes rfl
          have hn := ih (statementWeight no) (by rw [← sizeEq]; simp [statementWeight]; omega) no rfl
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]; omega) rest rfl
          simp [eraseStages, expressionSchedule, hy, hn, hr, List.append_assoc]
  exact helper (statementWeight body) body rfl

/-- The native compiler receives the program produced by the actual Witness
erasure, declaration by declaration. -/
theorem eraseProgram_uses_eraseStages (program : Program) :
    (Noctium.Witness.eraseProgram program).declarations =
      program.declarations.map fun declaration =>
        {declaration with body := eraseStages declaration.body} := rfl

theorem eraseStages_preserves_witnessOccurrences (body : List Statement) :
    scheduledWitnessOccurrences (eraseStages body) = scheduledWitnessOccurrences body := by
  simp [scheduledWitnessOccurrences, eraseStages_preserves_expressionSchedule]

/-- Applying any deterministic evaluator to the scheduled terms yields the
same ordered observations. In particular, a first failing expression stays at
the same position. The evaluator is an explicit oracle here, not a claim about
the external Control runtime or a proof that the circuit compiler is correct. -/
theorem eraseStages_preserves_oracleObservations
    (body : List Statement) (evaluate : Term → Except ε α) :
    (expressionSchedule (eraseStages body)).map evaluate =
      (expressionSchedule body).map evaluate := by
  rw [eraseStages_preserves_expressionSchedule]

/-- A sequential reference runner stops at the first failed term. This models
ordered evaluation of the schedule only. It does not model branch selection,
state writes, or the compiler's native runtime. -/
def runUntilError (evaluate : Term → Except ε α) : List Term → Except ε (List α)
  | [] => .ok []
  | term :: rest => do
    let value ← evaluate term
    let values ← runUntilError evaluate rest
    pure (value :: values)

theorem eraseStages_preserves_shortCircuitObservations
    (body : List Statement) (evaluate : Term → Except ε α) :
    runUntilError evaluate (expressionSchedule (eraseStages body)) =
      runUntilError evaluate (expressionSchedule body) := by
  rw [eraseStages_preserves_expressionSchedule]

/-- The erasure keeps pure evaluation and removes only write observations. This
small reference projection makes the stage boundary explicit. -/
inductive Observation where
  | evaluate (term : Term)
  | privateWrite (capability key : String) (type : Ty) (value : Term)
  deriving Repr

def evaluatedObservations : List Observation → List Term
  | [] => []
  | .evaluate term :: rest => term :: evaluatedObservations rest
  | .privateWrite .. :: rest => evaluatedObservations rest

theorem evaluatedObservations_append (left right : List Observation) :
    evaluatedObservations (left ++ right) =
      evaluatedObservations left ++ evaluatedObservations right := by
  induction left with
  | nil => rfl
  | cons observation rest ih => cases observation <;>
      simp [evaluatedObservations, ih]

def stageObservations : List Statement → List Observation
  | [] => []
  | .bind _ _ value :: rest => .evaluate value :: stageObservations rest
  | .evaluate value :: rest => .evaluate value :: stageObservations rest
  | .assert value :: rest => .evaluate value :: stageObservations rest
  | .return value :: _ => value.toList.map Observation.evaluate
  | .stage capability key type value :: rest =>
      .evaluate value :: .privateWrite capability key type value :: stageObservations rest
  | .readCell .. :: rest => stageObservations rest
  | .writeCell _ _ value :: rest => .evaluate value :: stageObservations rest
  | .readMap _ _ _ _ key :: rest | .readMember _ _ _ _ key :: rest =>
      .evaluate key :: stageObservations rest
  | .writeMap _ _ _ key value :: rest =>
      .evaluate key :: .evaluate value :: stageObservations rest
  | .forRange _ _ _ body :: rest => stageObservations body ++ stageObservations rest
  | .emitEvent _ payload :: rest => .evaluate payload :: stageObservations rest
  | .branch condition yes no :: rest =>
      .evaluate condition :: stageObservations yes ++ stageObservations no ++ stageObservations rest
termination_by body => sizeOf body

def circuitObservations (body : List Statement) : List Observation :=
  (expressionSchedule body).map Observation.evaluate

theorem evaluatedObservations_map_evaluate (terms : List Term) :
    evaluatedObservations (terms.map Observation.evaluate) = terms := by
  induction terms with
  | nil => rfl
  | cons term rest ih => simp [evaluatedObservations, ih]

theorem stageObservations_preserve_evaluations (body : List Statement) :
    evaluatedObservations (stageObservations body) = expressionSchedule body := by
  have helper : ∀ n (body : List Statement), statementWeight body = n →
      evaluatedObservations (stageObservations body) = expressionSchedule body := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro body sizeEq
      cases body with
      | nil => simp [stageObservations, evaluatedObservations, expressionSchedule] at sizeEq ⊢
      | cons statement rest =>
        cases statement with
        | bind name type value =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [stageObservations, evaluatedObservations, expressionSchedule] using hr
        | evaluate value =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [stageObservations, evaluatedObservations, expressionSchedule] using hr
        | assert value =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [stageObservations, evaluatedObservations, expressionSchedule] using hr
        | «return» value => cases value <;> simp [stageObservations, evaluatedObservations, expressionSchedule]
        | stage capability key type value =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [stageObservations, evaluatedObservations, expressionSchedule] using hr
        | readCell state destination type =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [stageObservations, evaluatedObservations, expressionSchedule] using hr
        | writeCell state type value =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [stageObservations, evaluatedObservations, expressionSchedule] using hr
        | readMap state destination keyTy valueTy key =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [stageObservations, evaluatedObservations, expressionSchedule] using hr
        | readMember state destination keyTy valueTy key =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [stageObservations, evaluatedObservations, expressionSchedule] using hr
        | writeMap state keyTy valueTy key value =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [stageObservations, evaluatedObservations, expressionSchedule] using hr
        | forRange index start stop loopBody =>
          have hb := ih (statementWeight loopBody)
            (by rw [← sizeEq]; simp [statementWeight]; omega) loopBody rfl
          have hr := ih (statementWeight rest)
            (by rw [← sizeEq]; simp [statementWeight]; omega) rest rfl
          simp only [stageObservations, expressionSchedule]
          rw [evaluatedObservations_append, hb, hr]
        | emitEvent kind payload =>
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]) rest rfl
          simpa [stageObservations, evaluatedObservations, expressionSchedule] using hr
        | branch condition yes no =>
          have hy := ih (statementWeight yes) (by rw [← sizeEq]; simp [statementWeight]; omega) yes rfl
          have hn := ih (statementWeight no) (by rw [← sizeEq]; simp [statementWeight]; omega) no rfl
          have hr := ih (statementWeight rest) (by rw [← sizeEq]; simp [statementWeight]; omega) rest rfl
          simp only [stageObservations, expressionSchedule]
          change condition :: evaluatedObservations
              (stageObservations yes ++ stageObservations no ++ stageObservations rest) =
            condition :: (expressionSchedule yes ++ expressionSchedule no ++ expressionSchedule rest)
          congr 1
          rw [evaluatedObservations_append, evaluatedObservations_append, hy, hn, hr]
  exact helper (statementWeight body) body rfl

def privateWrites (observations : List Observation) : List Observation :=
  observations.filter fun observation => match observation with
    | .privateWrite .. => true
    | .evaluate .. => false

theorem privateWrites_append (left right : List Observation) :
    privateWrites (left ++ right) = privateWrites left ++ privateWrites right := by
  induction left with
  | nil => rfl
  | cons observation rest ih => cases observation <;>
      simp [privateWrites]

/-- Ordered private-write events present in the original source. Branches are
walked in lexical order, so this is a source frame inventory, not a runtime
branch trace. -/
def sourceStageEvents : List Statement → List Observation
  | [] => []
  | .return _ :: _ => []
  | .stage capability key type value :: rest =>
      .privateWrite capability key type value :: sourceStageEvents rest
  | .branch _ yes no :: rest =>
      sourceStageEvents yes ++ sourceStageEvents no ++ sourceStageEvents rest
  | .forRange _ _ _ body :: rest => sourceStageEvents body ++ sourceStageEvents rest
  | _ :: rest => sourceStageEvents rest
termination_by body => sizeOf body

theorem stageObservations_preserve_exact_write_frame (body : List Statement) :
    privateWrites (stageObservations body) = sourceStageEvents body := by
  have helper : ∀ n (body : List Statement), statementWeight body = n →
      privateWrites (stageObservations body) = sourceStageEvents body := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro body weightEq
      cases body with
      | nil => simp [stageObservations, privateWrites, sourceStageEvents]
      | cons statement rest =>
        cases statement with
        | bind name type value =>
            have hr := ih (statementWeight rest) (by rw [← weightEq]; simp [statementWeight]) rest rfl
            simpa [stageObservations, privateWrites, sourceStageEvents] using hr
        | evaluate value =>
            have hr := ih (statementWeight rest) (by rw [← weightEq]; simp [statementWeight]) rest rfl
            simpa [stageObservations, privateWrites, sourceStageEvents] using hr
        | assert value =>
            have hr := ih (statementWeight rest) (by rw [← weightEq]; simp [statementWeight]) rest rfl
            simpa [stageObservations, privateWrites, sourceStageEvents] using hr
        | «return» value => simp [stageObservations, privateWrites, sourceStageEvents]
        | stage capability key type value =>
            have hr := ih (statementWeight rest) (by rw [← weightEq]; simp [statementWeight]) rest rfl
            simpa [stageObservations, privateWrites, sourceStageEvents] using hr
        | readCell state destination type =>
            have hr := ih (statementWeight rest) (by rw [← weightEq]; simp [statementWeight]) rest rfl
            simpa [stageObservations, privateWrites, sourceStageEvents] using hr
        | writeCell state type value =>
            have hr := ih (statementWeight rest) (by rw [← weightEq]; simp [statementWeight]) rest rfl
            simpa [stageObservations, privateWrites, sourceStageEvents] using hr
        | readMap state destination keyTy valueTy key =>
            have hr := ih (statementWeight rest) (by rw [← weightEq]; simp [statementWeight]) rest rfl
            simpa [stageObservations, privateWrites, sourceStageEvents] using hr
        | readMember state destination keyTy valueTy key =>
            have hr := ih (statementWeight rest) (by rw [← weightEq]; simp [statementWeight]) rest rfl
            simpa [stageObservations, privateWrites, sourceStageEvents] using hr
        | writeMap state keyTy valueTy key value =>
            have hr := ih (statementWeight rest) (by rw [← weightEq]; simp [statementWeight]) rest rfl
            simpa [stageObservations, privateWrites, sourceStageEvents] using hr
        | forRange index start stop loopBody =>
            have hb := ih (statementWeight loopBody)
              (by rw [← weightEq]; simp [statementWeight]; omega) loopBody rfl
            have hr := ih (statementWeight rest)
              (by rw [← weightEq]; simp [statementWeight]; omega) rest rfl
            simp only [stageObservations, sourceStageEvents]
            rw [privateWrites_append, hb, hr]
        | emitEvent kind payload =>
            have hr := ih (statementWeight rest) (by rw [← weightEq]; simp [statementWeight]) rest rfl
            simpa [stageObservations, privateWrites, sourceStageEvents] using hr
        | branch condition yes no =>
            have hy := ih (statementWeight yes) (by rw [← weightEq]; simp [statementWeight]; omega) yes rfl
            have hn := ih (statementWeight no) (by rw [← weightEq]; simp [statementWeight]; omega) no rfl
            have hr := ih (statementWeight rest) (by rw [← weightEq]; simp [statementWeight]; omega) rest rfl
            simp only [stageObservations, sourceStageEvents]
            change privateWrites
                (stageObservations yes ++ stageObservations no ++ stageObservations rest) =
              sourceStageEvents yes ++ sourceStageEvents no ++ sourceStageEvents rest
            rw [privateWrites_append, privateWrites_append, hy, hn, hr]
  exact helper (statementWeight body) body rfl

/-- The source side retains ordered private writes. The circuit erasure retains
the exact evaluation stream and contributes no private-write observation. -/
theorem stageBoundary (body : List Statement) :
    evaluatedObservations (circuitObservations (eraseStages body)) =
      evaluatedObservations (stageObservations body) := by
  rw [circuitObservations, evaluatedObservations_map_evaluate,
    eraseStages_preserves_expressionSchedule, stageObservations_preserve_evaluations]

theorem circuitErasure_has_no_private_writes (body : List Statement) :
    privateWrites (circuitObservations (eraseStages body)) = [] := by
  simp [privateWrites, circuitObservations]

/- The bounded execution model below accepts this AST fragment only. Control
branches, loops, events, new scalar/curve/byte terms, short-circuit terms, old
untyped witnesses, and effect fixtures need separate host semantics and never
enter the native replay gate. -/
inductive EligibilityNode where
  | term (value : Term)
  | statement (value : Statement)

private def eligibilityChildren : EligibilityNode → Option (List EligibilityNode)
  | .statement statement => match statement with
    | .bind _ _ value | .evaluate value | .assert value | .stage _ _ _ value =>
        some [.term value]
    | .readCell .. | .writeCell .. | .readMap .. | .readMember .. | .writeMap .. => none
    | .return none => some []
    | .return (some value) => some [.term value]
    | .branch .. | .forRange .. | .emitEvent .. => none
  | .term term => match term with
    | .unit | .native _ | .bool _ | .uint _ _ | .ref _ => some []
    | .binary _ left right | .eq left right | .poseidon2 _ left right | .index left right =>
        some [.term left, .term right]
    | .cast _ value | .disclose _ value | .at _ value | .project value _ => some [.term value]
    | .select condition yes no => some [.term condition, .term yes, .term no]
    | .witnessCall _ _ arguments | .call _ arguments | .composite _ arguments =>
        some (arguments.map EligibilityNode.term)
    | .boolAnd .. | .boolOr .. | .boolXor .. | .curve .. | .bytes ..
    | .bytes32Literal .. | .foreignConstant .. | .ite .. | .andThen ..
    | .orElse .. | .witness .. | .effect .. | .bytesAt .. => none

def nativeEligibleNodes : Nat → List EligibilityNode → Bool
  | 0, [] => true
  | 0, _ :: _ => false
  | _ + 1, [] => true
  | fuel + 1, node :: rest =>
      match eligibilityChildren node with
      | none => false
      | some children => nativeEligibleNodes fuel (children ++ rest)

def nativeEligibleBody (fuel : Nat) (body : List Statement) : Bool :=
  nativeEligibleNodes fuel (body.map EligibilityNode.statement)

def nativeEligibleProgram (program : Program) : Bool :=
  program.declarations.all (nativeEligibleBody 16384 ∘ Declaration.body)

inductive RuntimeValue where
  | unit
  | scalar (value : Noctium.Value)
  | aggregate (type : Types.CompositeType) (fingerprint : String) (leaves : List Nat)
  deriving Repr, BEq

inductive WitnessReply where
  | value (value : RuntimeValue)
  | failure (message : String)
  deriving Repr, BEq

structure WitnessInvocation where
  ordinal : Nat
  site : String
  name : String
  path : List DeclarationId
  operation : String
  capability : String
  privateKey : Option String
  resultType : ResultType
  arguments : List RuntimeValue
  reply : WitnessReply
  deriving Repr, BEq

structure ProviderRequest where
  name : String
  operation : String
  capability : String
  privateKey : Option String
  stagedState : List (String × RuntimeValue)
  arguments : List RuntimeValue
  deriving Repr

/-- A provider is an explicit pure host oracle. Replay code stores no provider
authority and consumes only the result recorded by source execution. -/
abbrev Provider := ProviderRequest → WitnessReply

structure ProviderGrant where
  name : String
  operation : String
  capability : String
  privateKey : Option String
  deriving Repr, BEq

structure HostGrants where
  providers : List ProviderGrant := []
  stateWrites : List (String × String) := []
  deriving Repr, BEq

inductive MachineMode where
  | record
  | replay
  deriving Repr, BEq

inductive HostBoundaryRejection where
  | providerCallback
  | stageCast
  | stageWrite
  deriving Repr, BEq

structure MachineState where
  mode : MachineMode := .record
  stagedState : List (String × RuntimeValue) := []
  journal : List (String × RuntimeValue) := []
  tape : List WitnessInvocation := []
  cursor : Nat := 0
  path : List DeclarationId := []
  /-- Append-only source evidence for rejected host-only boundaries. -/
  boundaryRejections : List HostBoundaryRejection := []
  deriving Repr

/-- The source-only rejection log stays outside machine-visible execution data. -/
private structure MachineStateObservable where
  mode : MachineMode
  stagedState : List (String × RuntimeValue)
  journal : List (String × RuntimeValue)
  tape : List WitnessInvocation
  cursor : Nat
  path : List DeclarationId
  deriving Repr, BEq

private def machineStateObservable (state : MachineState) : MachineStateObservable := {
  mode := state.mode, stagedState := state.stagedState, journal := state.journal,
  tape := state.tape, cursor := state.cursor, path := state.path}

/-- Relates a source recorder prefix to a replay cursor over a frozen tape.
Private stores and journals intentionally remain independent. -/
def ReplayStateRelation (frozen : List WitnessInvocation)
    (source replay : MachineState) : Prop :=
  source.mode = .record ∧ replay.mode = .replay ∧
    source.cursor = source.tape.length ∧ replay.cursor = source.cursor ∧
    replay.path = source.path ∧ replay.tape = frozen ∧
    ∃ suffix, frozen = source.tape ++ suffix

/- State-preserving error monad. Failed assertions and providers keep their
consumed witness cursor and source-side journal for audit and replay. -/
abbrev MachineM (α : Type u) := MachineState → (Except String α × MachineState)

instance machineMMonad : Monad MachineM where
  pure value := fun state => (.ok value, state)
  bind computation next := fun state =>
    let (result, state') := computation state
    match result with
    | .ok value => next value state'
    | .error message => (.error message, state')

private def fail {α} (message : String) : MachineM α := fun state => (.error message, state)

private def rejectBoundary {α} (kind : HostBoundaryRejection) (message : String) : MachineM α :=
  fun state => (.error message, {state with boundaryRejections := state.boundaryRejections ++ [kind]})

private def liftResult {α} (result : Except String α) : MachineM α := fun state => (result, state)

private def get : MachineM MachineState := fun state => (.ok state, state)

private def modify (update : MachineState → MachineState) : MachineM Unit :=
  fun state => (.ok (), update state)

inductive ExecutionResult where
  | success (value : RuntimeValue)
  | failure (message : String)
  deriving Repr, BEq

structure ExecutionObservation where
  result : ExecutionResult
  cursor : Nat
  tape : List WitnessInvocation
  journal : List (String × RuntimeValue)
  stagedState : List (String × RuntimeValue)
  deriving Repr

structure RecordedInvocation where
  source : Program
  entryName : String
  originalInputs : List (String × RuntimeValue)
  initialState : List (String × RuntimeValue)
  grants : HostGrants
  observation : ExecutionObservation
  deriving Repr

structure BoundInput where
  name : String
  type : Ty
  visibility : Visibility
  value : RuntimeValue
  deriving Repr, BEq

structure ReplayReport where
  execution : ExecutionObservation
  completeInputs : List BoundInput
  matchesRecordedSource : Bool
  deriving Repr

private def runtimeTy : RuntimeValue → Option Ty
  | .unit => none
  | .scalar (.native _) => some .native
  | .scalar (.bool _) => some .bool
  | .scalar (.uint maximum _) => some (.uint maximum)
  | .scalar (.bytes length _) => some (.bytes length)
  | .scalar (.opaqueBytes _) => some .opaqueBytes
  | .scalar (.opaqueString _) => some .opaqueString
  | .scalar (.jubjubScalar _) => some .jubjubScalar
  | .scalar (.jubjubPoint _ _) => some .jubjubPoint
  | .scalar (.foreignBase curve _) => some (.foreign (.base curve))
  | .scalar (.foreignScalar curve _) => some (.foreign (.scalar curve))
  | .scalar (.foreignPoint curve _) => some (.foreign (.point curve))
  | .aggregate .. => none

private def resultTypeOfRuntime : RuntimeValue → ResultType
  | .unit => .unit
  | .scalar (.native _) => .scalar .native
  | .scalar (.bool _) => .scalar .bool
  | .scalar (.uint maximum _) => .scalar (.uint maximum)
  | .scalar (.bytes length _) => .scalar (.bytes length)
  | .scalar (.opaqueBytes _) => .scalar .opaqueBytes
  | .scalar (.opaqueString _) => .scalar .opaqueString
  | .scalar (.jubjubScalar _) => .scalar .jubjubScalar
  | .scalar (.jubjubPoint _ _) => .scalar .jubjubPoint
  | .scalar (.foreignBase curve _) => .scalar (.foreign (.base curve))
  | .scalar (.foreignScalar curve _) => .scalar (.foreign (.scalar curve))
  | .scalar (.foreignPoint curve _) => .scalar (.foreign (.point curve))
  | .aggregate type _ _ => .composite type

private def canonicalScalar (context : EvalContext) (value : Noctium.Value) : Bool :=
  match value with
  | .native number => number < context.modulus
  | .bool _ => true
  | .uint maximum number =>
      maximum ≤ ScalarPolicy.maxUint && number ≤ maximum && number < context.modulus
  | .bytes .. | .opaqueBytes .. | .opaqueString .. | .jubjubScalar .. | .jubjubPoint ..
  | .foreignBase .. | .foreignScalar .. | .foreignPoint .. => false

private def runtimeMatches (program : Program) (context : EvalContext)
    (expected : ResultType) (value : RuntimeValue) : Bool := Id.run do
  match expected, value with
  | .unit, .unit => return true
  | .scalar ty, .scalar scalar =>
      return runtimeTy (.scalar scalar) == some ty && canonicalScalar context scalar
  | .composite type, .aggregate actual fingerprint leaves =>
      if !(actual == type) then return false
      match Types.compileType program.composites type with
      | .error _ => return false
      | .ok compiled =>
        return compiled.fingerprint == fingerprint &&
          (Types.unflattenChecked compiled leaves).isOk
  | _, _ => return false

private def runtimeScalar (value : RuntimeValue) : Except String Noctium.Value :=
  match value with
  | .scalar scalar => pure scalar
  | _ => .error "native witness execution expected a scalar"

private def scalarPolicyValue (value : Noctium.Value) : Except String ScalarPolicy.Value :=
  match value with
  | .native number => pure ⟨.native, number⟩
  | .bool boolean => pure ⟨.bool, if boolean then 1 else 0⟩
  | .uint maximum number => pure ⟨.uint maximum, number⟩
  | .bytes .. | .opaqueBytes .. | .opaqueString .. | .jubjubScalar .. | .jubjubPoint ..
  | .foreignBase .. | .foreignScalar .. | .foreignPoint .. =>
      .error "native witness arithmetic requires a Native, Bool or UInt scalar"

private def runtimeScalarOfPolicy (value : ScalarPolicy.Value) : RuntimeValue :=
  match value.kind with
  | .native => .scalar (.native value.number)
  | .bool => .scalar (.bool (value.number != 0))
  | .uint maximum => .scalar (.uint maximum value.number)
  | .bytes _ | .opaqueBytes | .jubjubScalar | .jubjubPoint | .foreign _ => .unit

private def castRuntime (context : EvalContext) (target : Ty) (value : RuntimeValue) :
    Except String RuntimeValue := do
  let scalar ← runtimeScalar value
  let policy ← scalarPolicyValue scalar
  let result ← ScalarPolicy.cast policy target.scalarKind
  let result := runtimeScalarOfPolicy result
  let .scalar resultValue := result | throw "native witness execution expected a scalar"
  unless canonicalScalar context resultValue do throw "noncanonical scalar conversion"
  pure result

private def authorizedProvider (grants : HostGrants) (signature : WitnessSignature) : Bool :=
  grants.providers.any fun grant =>
    grant.name == signature.name && grant.operation == signature.operation &&
      grant.capability == signature.capability && grant.privateKey == signature.privateKey

private def authorizedWrite (grants : HostGrants) (capability key : String) : Bool :=
  grants.stateWrites.contains (capability, key)

/-- A typed host read of a staged key is accepted only when the provider
returns the exact staged value. This pure model records a mismatched response
as failure; it does not model the native runtime's pending retry lifecycle. -/
private def providerReply (provider : Provider) (signature : WitnessSignature)
    (request : ProviderRequest) : Except String WitnessReply := do
  if signature.operation == "private_state.read.v1" then
    match signature.privateKey with
    | some key =>
        let reply := provider request
        match request.stagedState.lookup key, reply with
        | some expected, .value actual =>
            if actual == expected then pure reply
            else throw "private state provider result does not match staged state"
        | _, _ => pure reply
    | none => pure (provider request)
  else pure (provider request)

private def writeState (state : List (String × RuntimeValue)) (key : String)
    (value : RuntimeValue) : List (String × RuntimeValue) :=
  (key, value) :: state.filter (·.1 != key)

private def sameRuntimeValues (left right : List RuntimeValue) : Bool :=
  left.length == right.length && (left.zip right).all fun (a, b) => a == b

private def recordEvent (event : WitnessInvocation) : MachineM Unit := do
  modify fun state => {state with tape := state.tape ++ [event], cursor := state.cursor + 1}

private def authorizeSignature (grants : HostGrants) (signature : WitnessSignature) :
    MachineM Unit := do
  unless authorizedProvider grants signature do
    fail "host provider capability was not granted"

private def validateWitnessArguments (program : Program) (context : EvalContext)
    (signature : WitnessSignature) (arguments : List RuntimeValue) : Bool := Id.run do
  if arguments.length != signature.parameters.length then return false
  for (argument, parameter) in arguments.zip signature.parameters do
    if !runtimeMatches program context parameter.type argument then return false
  return true

private def normalizedReply (program : Program) (context : EvalContext)
    (signature : WitnessSignature) (reply : WitnessReply) : WitnessReply :=
  match reply with
  | .failure _ => reply
  | .value value =>
      if runtimeMatches program context signature.result value then reply
      else .failure "host provider returned a value outside its declared type"

private def providerReplyState (program : Program) (context : EvalContext)
    (signature : WitnessSignature) (reply : WitnessReply) (state : MachineState) : MachineState :=
  match reply with
  | .failure _ => state
  | .value value =>
      if runtimeMatches program context signature.result value then state
      else {state with boundaryRejections := state.boundaryRejections ++ [.providerCallback]}

private def sourceProviderReply (program : Program) (context : EvalContext)
    (provider : Provider) (signature : WitnessSignature)
    (request : ProviderRequest) : MachineM WitnessReply := fun state =>
  match providerReply provider signature request with
  | .error message =>
      (.error message,
        {state with boundaryRejections := state.boundaryRejections ++ [.providerCallback]})
  | .ok reply => (.ok reply, providerReplyState program context signature reply state)

private theorem rejectBoundary_observable (kind : HostBoundaryRejection) (message : String)
    (state : MachineState) :
    (rejectBoundary (α := RuntimeValue) kind message state).1 = .error message ∧
      machineStateObservable (rejectBoundary (α := RuntimeValue) kind message state).2 = machineStateObservable state := by
  simp [rejectBoundary, machineStateObservable]

private theorem providerReplyState_observable (program : Program) (context : EvalContext)
    (signature : WitnessSignature) (reply : WitnessReply) (state : MachineState) :
    machineStateObservable (providerReplyState program context signature reply state) =
      machineStateObservable state := by
  cases reply with
  | failure message => rfl
  | value value => by_cases valid : runtimeMatches program context signature.result value = true <;>
      simp [providerReplyState, valid, machineStateObservable]

private theorem sourceProviderReply_projection (program : Program) (context : EvalContext)
    (provider : Provider) (signature : WitnessSignature) (request : ProviderRequest)
    (state : MachineState) :
    (sourceProviderReply program context provider signature request state).1 =
        providerReply provider signature request ∧
      machineStateObservable (sourceProviderReply program context provider signature request state).2 =
        machineStateObservable state := by
  cases reply : providerReply provider signature request with
  | error message => simp [sourceProviderReply, reply, machineStateObservable]
  | ok value =>
      simp [sourceProviderReply, reply, providerReplyState_observable]

private def scalarNumber : Noctium.Value → Except String Nat
  | .native number | .uint _ number => pure number
  | .bool value => pure (if value then 1 else 0)
  | .bytes .. | .opaqueBytes .. | .opaqueString .. | .jubjubScalar .. | .jubjubPoint ..
  | .foreignBase .. | .foreignScalar .. | .foreignPoint .. =>
      .error "native witness index or composite leaf is not numeric"

private def commonScalarType (left right : Ty) : Except String Ty := do
  if Helpers.subtype (.scalar left) (.scalar right) then pure right
  else if Helpers.subtype (.scalar right) (.scalar left) then pure left
  else .error "native witness execution found incompatible scalar types"

private def runtimeEquality (composites : Types.CompositeEnv) (context : EvalContext)
    (left right : RuntimeValue) : Except String Bool := do
  match left, right with
  | .aggregate leftType leftFingerprint leftLeaves,
    .aggregate rightType rightFingerprint rightLeaves => do
      unless leftType == rightType do
        throw "native witness equality found incompatible aggregate types"
      let .structure _ := leftType | throw "native witness record equality requires a flat record"
      let program : Program := {composites}
      discard ((Helpers.nominalFlatStructureLeafTypes program {} leftType).mapError (·.message))
      let compiled ← (Types.compileType composites leftType).mapError (·.message)
      unless leftFingerprint == compiled.fingerprint && rightFingerprint == compiled.fingerprint do
        throw "native witness equality found a noncanonical aggregate fingerprint"
      let leftChecked ← (Types.unflattenChecked compiled leftLeaves).mapError id
      let rightChecked ← (Types.unflattenChecked compiled rightLeaves).mapError id
      pure (leftChecked.leaves == rightChecked.leaves)
  | _, _ => do
      let left ← runtimeScalar left
      let right ← runtimeScalar right
      let leftTy := (runtimeTy (.scalar left)).getD .native
      let rightTy := (runtimeTy (.scalar right)).getD .native
      let ty ← commonScalarType leftTy rightTy
      let left ← castRuntime context ty (.scalar left)
      let right ← castRuntime context ty (.scalar right)
      pure (left == right)

private def equalityPost (composites : Types.CompositeEnv) (context : EvalContext)
    (values : List RuntimeValue) : MachineM RuntimeValue := do
  let some left := values[0]? | fail "equality left operand missing"
  let some right := values[1]? | fail "equality right operand missing"
  let equal ← liftResult (runtimeEquality composites context left right)
  pure (.scalar (.bool equal))

private def makeAggregateRuntime (program : Program) (type : Types.CompositeType)
    (leaves : List Nat) : Except String RuntimeValue := do
  let compiled ← (Types.compileType program.composites type).mapError (·.message)
  let checked ← (Types.unflattenChecked compiled leaves).mapError id
  pure (.aggregate type compiled.fingerprint checked.leaves)

private def fromSomeTypedValue (value : Types.SomeTypedValue) : RuntimeValue := Id.run do
  let compiled := value.1
  let typed := value.2
  match compiled.type with
  | .unit => return .aggregate .unit compiled.fingerprint typed.leaves
  | .scalar .native => return .scalar (.native (typed.leaves.headD 0))
  | .scalar .bool => return .scalar (.bool (typed.leaves.headD 0 != 0))
  | .scalar (.uint maximum) => return .scalar (.uint maximum (typed.leaves.headD 0))
  | type => return .aggregate type compiled.fingerprint typed.leaves

private def aggregateLeaves (program : Program) (type : Types.CompositeType)
    (value : RuntimeValue) : Except String (Types.CompiledType × Types.AggregateValue) := do
  let .aggregate actual fingerprint leaves := value
    | .error "native witness execution expected a checked aggregate"
  unless actual == type do .error "aggregate logical type identity mismatch"
  let compiled ← (Types.compileType program.composites type).mapError (·.message)
  unless compiled.fingerprint == fingerprint do .error "aggregate fingerprint identity mismatch"
  let typed ← (Types.unflattenChecked compiled leaves).mapError id
  pure (compiled, typed.value)

private def coerceRuntime (program : Program) (context : EvalContext)
    (expected : ResultType) (value : RuntimeValue) : Except String RuntimeValue := do
  unless Helpers.subtype (resultTypeOfRuntime value) expected do
    .error "native witness execution type mismatch"
  match expected, value with
  | .unit, .unit => pure .unit
  | .scalar ty, .scalar _ => castRuntime context ty value
  | .composite type, .aggregate _ _ leaves => makeAggregateRuntime program type leaves
  | _, _ => .error "native witness execution type mismatch"

private def coerceArguments (program : Program) (context : EvalContext)
    (parameters : List WitnessParameter) (arguments : List RuntimeValue) :
    Except String (List RuntimeValue) := do
  unless parameters.length == arguments.length do .error "typed witness argument arity mismatch"
  (parameters.zip arguments).mapM fun (parameter, argument) =>
    coerceRuntime program context parameter.type argument

private def compositeInputRuntime (program : Program) (type : Types.CompositeType)
    (inputName : String) (inputs : List (String × RuntimeValue)) :
    Except String RuntimeValue := do
  let compiled ← (Types.compileType program.composites type).mapError (·.message)
  let names := (Helpers.sourceLeafPaths compiled.checked.value "").map (inputName ++ ·)
  let values ← names.mapM fun name => do
    let some (.scalar (.native value)) := inputs.lookup name
      | .error s!"missing or mistyped aggregate input '{name}'"
    pure value
  let typed ← (Types.unflattenChecked compiled values).mapError id
  pure (.aggregate type compiled.fingerprint typed.leaves)

private def sameInvocation (cursor : Nat) (path : List DeclarationId)
    (site : String) (signature : WitnessSignature) (arguments : List RuntimeValue)
    (event : WitnessInvocation) : Bool :=
  event.ordinal == cursor && event.path == path && event.site == site &&
    event.name == signature.name && event.operation == signature.operation &&
    event.capability == signature.capability && event.privateKey == signature.privateKey &&
    event.resultType == signature.result && sameRuntimeValues event.arguments arguments

private def witnessValue (program : Program) (context : EvalContext) (signature : WitnessSignature)
    (reply : WitnessReply) : MachineM RuntimeValue := do
  match normalizedReply program context signature reply with
  | .failure message => fail message
  | .value value => pure value

private def recordWitnessCall (program : Program) (context : EvalContext)
    (provider : Provider) (site name : String) (signature : WitnessSignature)
    (arguments : List RuntimeValue) (state : MachineState) : MachineM RuntimeValue := do
  let request : ProviderRequest := {
    name := signature.name, operation := signature.operation, capability := signature.capability,
    privateKey := signature.privateKey, stagedState := state.stagedState, arguments}
  let reply ← sourceProviderReply program context provider signature request
  let reply := normalizedReply program context signature reply
  let event : WitnessInvocation := {
    ordinal := state.cursor, site, name, path := state.path, operation := signature.operation,
    capability := signature.capability, privateKey := signature.privateKey,
    resultType := signature.result, arguments, reply}
  recordEvent event
  witnessValue program context signature reply

private def replayWitnessCall (program : Program) (context : EvalContext) (site : String)
    (signature : WitnessSignature) (arguments : List RuntimeValue)
    (state : MachineState) : MachineM RuntimeValue := do
  match state.tape[state.cursor]? with
  | none => fail "typed witness replay exhausted its recorded invocation tape"
  | some event =>
      unless sameInvocation state.cursor state.path site signature arguments event do
        fail "typed witness replay invocation did not match its recorded binding"
      modify fun current => {current with cursor := current.cursor + 1}
      witnessValue program context signature event.reply

private def executeWitnessCallMode (program : Program) (context : EvalContext)
    (provider : Provider) (site name : String) (signature : WitnessSignature)
    (arguments : List RuntimeValue) : MachineM RuntimeValue := do
  let state ← get
  match state.mode with
  | .record => recordWitnessCall program context provider site name signature arguments state
  | .replay => replayWitnessCall program context site signature arguments state

private def executeWitnessCall (program : Program) (context : EvalContext) (grants : HostGrants)
    (provider : Provider) (site name : String) (arguments : List RuntimeValue) : MachineM RuntimeValue := do
  let signature ← liftResult ((Helpers.witnessSignature program name).mapError (·.message))
  authorizeSignature grants signature
  let arguments ← liftResult (coerceArguments program context signature.parameters arguments)
  unless validateWitnessArguments program context signature arguments do
    fail "typed witness argument binding mismatch"
  executeWitnessCallMode program context provider site name signature arguments

private def externalInputSchema (program : Program) (entryName : String) :
    Except String (List Input) := do
  let some entry := program.exports.find? (·.name == entryName)
    | .error s!"unknown helper entrypoint '{entryName}'"
  let mut inputs := entry.inputs
  for aggregate in entry.compositeInputs do
    let compiled ← (Types.compileType program.composites aggregate.type).mapError (·.message)
    inputs := inputs ++ (Helpers.sourceLeafPaths compiled.checked.value "").map fun path => {
      name := aggregate.name ++ path, ty := .native, visibility := aggregate.visibility,
      span := aggregate.span : Input}
  unless uniqueNames (inputs.map (·.name)) do .error "duplicate source input name"
  pure inputs

private def sameInput (left right : Input) : Bool :=
  left.name == right.name && left.ty == right.ty && left.visibility == right.visibility

private def sameInputs (left right : List Input) : Bool :=
  left.length == right.length && (left.zip right).all fun (a, b) => sameInput a b

structure NativeAdmission where
  host : Helpers.HostedCircuit
  externalInputs : List Input
  deriving Repr

/-- The gate invokes source control checks, then the real helper compiler on the
exact `Witness.eraseProgram` output consumed by Witness.compile. It binds fresh
leaf names to the compiler-produced call list and rejects unsupported syntax. -/
def admitNativeReplay (limits : Helpers.Limits) (program : Program) (entryName : String) :
    Except String NativeAdmission := do
  unless nativeEligibleProgram program do
    .error "source program is outside the bounded native replay subset"
  discard ((Control.compileTypedWithLimits limits program entryName).mapError (·.message))
  let externalInputs ← externalInputSchema program entryName
  let host ← (Helpers.compileHostedWithLimits limits (Noctium.Witness.eraseProgram program)
    entryName).mapError (·.message)
  unless sameInputs (host.circuit.inputs.take externalInputs.length) externalInputs do
    .error "native compiler changed the ordered external input schema"
  let freshInputs := host.circuit.inputs.drop externalInputs.length
  let freshNames := host.calls.flatMap (·.inputs)
  unless freshInputs.map (·.name) == freshNames do
    .error "native witness call outputs do not match the compiler input suffix"
  unless freshInputs.all (·.visibility == .private) do
    .error "native witness result leaves must be private inputs"
  unless uniqueNames freshNames do
    .error "native witness compiler reused a fresh result leaf"
  for (call, ordinal) in host.calls.zipIdx do
    unless call.ordinal == ordinal do .error "native witness binding ordinal is noncanonical"
  pure {host, externalInputs}

private def resultLeafCount (program : Program) (result : ResultType) :
    Except String Nat := do
  match result with
  | .unit => pure 0
  | .scalar _ => pure 1
  | .composite type => do
      let compiled ← (Types.compileType program.composites type).mapError (·.message)
      pure compiled.checked.expandedLeaves

private def validateCallTape (program : Program) (context : EvalContext)
    (calls : List WitnessCallBinding) (tape : List WitnessInvocation)
    (requireComplete : Bool) : Except String Unit := do
  if tape.length > calls.length then .error "witness tape has excess invocations"
  if requireComplete && tape.length != calls.length then
    .error "successful source execution did not consume every native witness binding"
  for (event, ordinal) in tape.zipIdx do
    let some call := calls[ordinal]? | .error "witness tape has no compiler call binding"
    unless call.ordinal == ordinal && sameInvocation ordinal call.path call.site
        (← (Helpers.witnessSignature program call.name).mapError (·.message)) event.arguments event do
      .error "witness tape does not match the compiler call binding"
    let signature ← (Helpers.witnessSignature program call.name).mapError (·.message)
    unless call.name == signature.name && call.result == signature.result &&
        event.resultType == signature.result do
      .error "witness tape result signature changed"
    unless validateWitnessArguments program context signature event.arguments do
      .error "witness tape arguments do not match the declared signature"
    let expectedLeaves ← resultLeafCount program signature.result
    unless call.inputs.length == expectedLeaves do
      .error "compiler witness leaves do not match the checked result layout"
    match event.reply with
    | .value value =>
        unless runtimeMatches program context signature.result value do
          .error "witness tape contains an invalid typed result"
    | .failure _ =>
        if requireComplete then .error "successful witness tape contains a provider failure"

private def bindTape (program : Program) (context : EvalContext)
    (calls : List WitnessCallBinding) (tape : List WitnessInvocation) :
    Except String (List (String × RuntimeValue)) := do
  validateCallTape program context calls tape true
  let mut result := []
  for (call, event) in calls.zip tape do
    let .value value := event.reply | .error "failed provider call has no circuit result"
    let fresh := match value with
      | .unit => []
      | .scalar scalar => call.inputs.map fun name => (name, .scalar scalar)
      | .aggregate _ _ leaves => call.inputs.zip leaves |>.map fun (name, leaf) =>
          (name, RuntimeValue.scalar (.native leaf))
    unless fresh.length == call.inputs.length do
      .error "typed witness result leaves do not bijectively bind compiler inputs"
    unless uniqueNames (result.map Prod.fst ++ fresh.map Prod.fst) do
      .error "typed witness result leaf name was reused"
    result := result ++ fresh
  pure result

private def sameRuntimeBindings (left right : List (String × RuntimeValue)) : Bool :=
  left.length == right.length && (left.zip right).all fun (a, b) =>
    a.1 == b.1 && a.2 == b.2

private def normalizeExternalInputs (context : EvalContext) (schema : List Input)
    (supplied : List (String × RuntimeValue)) : Except String (List (String × RuntimeValue)) := do
  unless uniqueNames (supplied.map Prod.fst) do .error "duplicate original circuit input"
  unless supplied.length == schema.length do .error "original circuit input map is incomplete"
  let mut ordered := []
  for input in schema do
    let some value := supplied.lookup input.name
      | .error s!"missing original circuit input '{input.name}'"
    unless runtimeMatches {composites := {}} context (.scalar input.ty) value do
      .error s!"original circuit input '{input.name}' has an invalid value"
    ordered := ordered ++ [(input.name, value)]
  unless supplied.all (fun binding => schema.any (·.name == binding.1)) do
    .error "original circuit input map contains an unknown name"
  pure ordered

private def validateCompleteInputMap (context : EvalContext) (admission : NativeAdmission)
    (original : List (String × RuntimeValue)) (fresh : List (String × RuntimeValue)) :
    Except String (List (String × RuntimeValue)) := do
  unless uniqueNames (original.map Prod.fst ++ fresh.map Prod.fst) do
    .error "original and fresh witness inputs overlap"
  let allValues := original ++ fresh
  unless allValues.length == admission.host.circuit.inputs.length do
    .error "complete native input map has the wrong number of leaves"
  let mut canonical := []
  for input in admission.host.circuit.inputs do
    let some value := allValues.lookup input.name
      | .error s!"complete native input map is missing '{input.name}'"
    unless runtimeMatches {composites := {}} context (.scalar input.ty) value do
      .error s!"complete native input '{input.name}' has an invalid canonical value"
    canonical := canonical ++ [(input.name, value)]
  unless allValues.all (fun binding => admission.host.circuit.inputs.any (·.name == binding.1)) do
    .error "complete native input map contains an unknown leaf"
  pure canonical

set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

private theorem input_bind_ok {α β : Type} {first : Except String α}
    {next : α → Except String β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private def InputBindingRows (context : EvalContext)
    (allValues : List (String × RuntimeValue)) :
    List Input → List (String × RuntimeValue) → Prop
  | [], [] => True
  | input :: inputs, binding :: bindings =>
      binding.1 = input.name ∧
      allValues.lookup input.name = some binding.2 ∧
      runtimeMatches {composites := {}} context (.scalar input.ty) binding.2 = true ∧
      InputBindingRows context allValues inputs bindings
  | _, _ => False

private def inputBindingStep (context : EvalContext)
    (allValues : List (String × RuntimeValue)) (input : Input)
    (before : List (String × RuntimeValue)) :
    Except String (ForInStep (List (String × RuntimeValue))) := do
  let some value := allValues.lookup input.name
    | .error s!"complete native input map is missing '{input.name}'"
  unless runtimeMatches {composites := {}} context (.scalar input.ty) value do
    .error s!"complete native input '{input.name}' has an invalid canonical value"
  pure (.yield (before ++ [(input.name, value)]))

private theorem inputBindingLoop_spec (context : EvalContext)
    (allValues : List (String × RuntimeValue)) (inputs : List Input)
    (before after : List (String × RuntimeValue))
    (success : forIn inputs before (inputBindingStep context allValues) = .ok after) :
    ∃ added, after = before ++ added ∧ InputBindingRows context allValues inputs added := by
  induction inputs generalizing before with
  | nil =>
      change Except.ok before = .ok after at success
      cases success
      exact ⟨[], by simp, trivial⟩
  | cons input inputs ih =>
      rw [List.forIn_cons] at success
      cases found : allValues.lookup input.name with
      | none => simp [inputBindingStep, found, bind, Except.bind] at success
      | some value =>
          cases typed : runtimeMatches {composites := {}} context (.scalar input.ty) value with
          | false => simp [inputBindingStep, found, typed, bind, Except.bind] at success
          | true =>
              simp only [inputBindingStep, found, typed, ↓reduceIte,
                bind, Except.bind, pure, Except.pure] at success
              obtain ⟨added, exactResult, rows⟩ := ih _ success
              refine ⟨(input.name, value) :: added, ?_, rfl, found, typed, rows⟩
              simpa only [List.append_assoc, List.singleton_append] using exactResult

private theorem validateCompleteInputMap_spec (context : EvalContext)
    (admission : NativeAdmission) (original fresh canonical : List (String × RuntimeValue))
    (success : validateCompleteInputMap context admission original fresh = .ok canonical) :
    uniqueNames ((original ++ fresh).map Prod.fst) = true ∧
    (original ++ fresh).length = admission.host.circuit.inputs.length ∧
    (original ++ fresh).all (fun binding =>
      admission.host.circuit.inputs.any (·.name == binding.1)) = true ∧
    InputBindingRows context (original ++ fresh) admission.host.circuit.inputs canonical := by
  unfold validateCompleteInputMap at success
  by_cases distinct : uniqueNames (original.map Prod.fst ++ fresh.map Prod.fst) = true
  · simp only [distinct, ↓reduceIte] at success
    by_cases sameLength : ((original ++ fresh).length == admission.host.circuit.inputs.length) = true
    · simp only [sameLength, ↓reduceIte] at success
      change (do
        let values ← forIn admission.host.circuit.inputs []
          (inputBindingStep context (original ++ fresh))
        if (original ++ fresh).all (fun binding =>
            admission.host.circuit.inputs.any (·.name == binding.1)) then
          pure values
        else do
          Except.error "complete native input map contains an unknown leaf"
          pure values) = .ok canonical at success
      obtain ⟨values, loop, finish⟩ := input_bind_ok.mp success
      by_cases allowed : (original ++ fresh).all (fun binding =>
          admission.host.circuit.inputs.any (·.name == binding.1)) = true
      · simp only [allowed, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at finish
        subst values
        obtain ⟨added, exactResult, rows⟩ := inputBindingLoop_spec context
          (original ++ fresh) admission.host.circuit.inputs [] canonical loop
        simp only [List.nil_append] at exactResult
        subst added
        exact ⟨by simpa only [List.map_append] using distinct,
          by simpa only [beq_iff_eq] using sameLength, allowed, rows⟩
      · simp only [allowed, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at finish
        cases finish
    · simp only [sameLength, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at success
      cases success
  · simp only [distinct, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at success
    cases success

private theorem inputBindingRows_names (context : EvalContext)
    (allValues : List (String × RuntimeValue)) (inputs : List Input)
    (bindings : List (String × RuntimeValue))
    (rows : InputBindingRows context allValues inputs bindings) :
    bindings.map Prod.fst = inputs.map (·.name) := by
  induction inputs generalizing bindings with
  | nil => cases bindings <;> simp_all [InputBindingRows]
  | cons input inputs ih =>
      cases bindings with
      | nil => exact False.elim rows
      | cons binding bindings =>
          rcases rows with ⟨name, _, _, tail⟩
          simpa only [List.map_cons, name] using
            congrArg (List.cons input.name) (ih bindings tail)

private theorem inputBindingRows_values (context : EvalContext)
    (allValues : List (String × RuntimeValue)) (inputs : List Input)
    (bindings : List (String × RuntimeValue))
    (rows : InputBindingRows context allValues inputs bindings) :
    ∀ binding ∈ bindings, allValues.lookup binding.1 = some binding.2 := by
  induction inputs generalizing bindings with
  | nil => cases bindings <;> simp_all [InputBindingRows]
  | cons input inputs ih =>
      cases bindings with
      | nil => exact False.elim rows
      | cons binding bindings =>
          rcases rows with ⟨name, found, _, tail⟩
          intro value member
          rcases List.mem_cons.mp member with same | member
          · subst value
            simpa only [name] using found
          · exact ih bindings tail value member

theorem validateCompleteInputMap_preserves_bindings (context : EvalContext)
    (admission : NativeAdmission) (original fresh canonical : List (String × RuntimeValue))
    (success : validateCompleteInputMap context admission original fresh = .ok canonical) :
    uniqueNames ((original ++ fresh).map Prod.fst) = true ∧
    (original ++ fresh).length = admission.host.circuit.inputs.length ∧
    canonical.map Prod.fst = admission.host.circuit.inputs.map (·.name) ∧
    ∀ binding ∈ canonical, (original ++ fresh).lookup binding.1 = some binding.2 := by
  obtain ⟨distinct, count, _, rows⟩ := validateCompleteInputMap_spec context admission
    original fresh canonical success
  exact ⟨distinct, count,
    inputBindingRows_names context (original ++ fresh) _ _ rows,
    inputBindingRows_values context (original ++ fresh) _ _ rows⟩

private def entrypoint (program : Program) (entryName : String) :
    Except String (Export × Declaration) := do
  let some foundEntry := program.exports.find? (·.name == entryName)
    | .error s!"unknown witness entrypoint '{entryName}'"
  let some declaration := program.declarations.find? (·.id == foundEntry.target)
    | .error "witness entrypoint declaration is missing"
  pure (foundEntry, declaration)

private def entryEnvironment (program : Program) (context : EvalContext)
    (entryName : String) (inputs : List (String × RuntimeValue)) :
    Except String (List (String × RuntimeValue)) := do
  let (foundEntry, declaration) ← entrypoint program entryName
  let mut scalarInputs := foundEntry.inputs
  let mut aggregateInputs := foundEntry.compositeInputs
  let mut environment := []
  for parameter in declaration.parameters do
    match declaration.parameterType parameter with
    | .scalar target =>
        let some input := scalarInputs.head? | .error "witness scalar input signature mismatch"
        scalarInputs := scalarInputs.drop 1
        let some value := inputs.lookup input.name | .error s!"missing input '{input.name}'"
        let value ← castRuntime context target value
        environment := environment ++ [(parameter.name, value)]
    | .composite type =>
        let some input := aggregateInputs.head? | .error "witness aggregate input signature mismatch"
        aggregateInputs := aggregateInputs.drop 1
        unless input.type == type do .error "witness aggregate input identity mismatch"
        let value ← compositeInputRuntime program type input.name inputs
        environment := environment ++ [(parameter.name, value)]
    | .unit => .error "witness entry parameters cannot be Unit"
  unless scalarInputs.isEmpty && aggregateInputs.isEmpty do
    .error "witness entry input signature has unused parameters"
  pure environment

private def helperEnvironment (program : Program) (context : EvalContext)
    (target : Declaration) (arguments : List RuntimeValue) :
    Except String (List (String × RuntimeValue)) := do
  unless arguments.length == target.parameters.length do .error "helper call arity mismatch"
  let mut environment := []
  for (parameter, argument) in target.parameters.zip arguments do
    let value ← coerceRuntime program context (target.parameterType parameter) argument
    environment := environment ++ [(parameter.name, value)]
  pure environment

private def withCallPath {α : Type u} (path : List DeclarationId)
    (computation : MachineM α) : MachineM α := fun state =>
  let (result, finalState) := computation {state with path}
  (result, {finalState with path := state.path})

private def stageContinue (grants : HostGrants) (capability key : String)
    (value : RuntimeValue) (state : MachineState) (continuation : MachineM RuntimeValue) :
    MachineM RuntimeValue := do
  match state.mode with
  | .record =>
      unless authorizedWrite grants capability key do
        rejectBoundary .stageWrite "host private-state write capability was not granted"
      modify fun current => {current with
        stagedState := writeState current.stagedState key value,
        journal := current.journal ++ [(key, value)]}
  | .replay => fail "un-erased private-state stage reached circuit replay"
  continuation

private def stageCast (context : EvalContext) (type : Ty) (value : RuntimeValue) :
    MachineM RuntimeValue :=
  match castRuntime context type value with
  | .ok result => pure result
  | .error message => rejectBoundary .stageCast message

private theorem stageCast_projection (context : EvalContext) (type : Ty)
    (value : RuntimeValue) (state : MachineState) :
    (stageCast context type value state).1 = castRuntime context type value ∧
      machineStateObservable (stageCast context type value state).2 = machineStateObservable state := by
  cases cast : castRuntime context type value with
  | error message => simp [stageCast, cast, rejectBoundary, machineStateObservable]
  | ok result => simp [stageCast, cast, machineMMonad, Applicative.toPure, Monad.toApplicative, Pure.pure, machineStateObservable]

private theorem sourceProviderReply_marksPreRecordFailure
    (program : Program) (context : EvalContext) (provider : Provider)
    (signature : WitnessSignature) (request : ProviderRequest) (state : MachineState)
    (message : String)
    (rejected : providerReply provider signature request = .error message) :
    sourceProviderReply program context provider signature request state =
      (.error message, {state with boundaryRejections := state.boundaryRejections ++ [.providerCallback]}) := by
  simp [sourceProviderReply, rejected]

private theorem sourceProviderReply_marksMalformedValue
    (program : Program) (context : EvalContext) (provider : Provider)
    (signature : WitnessSignature) (request : ProviderRequest) (state : MachineState)
    (value : RuntimeValue)
    (received : providerReply provider signature request = .ok (.value value))
    (invalid : runtimeMatches program context signature.result value = false) :
    sourceProviderReply program context provider signature request state =
      (.ok (.value value), {state with boundaryRejections := state.boundaryRejections ++ [.providerCallback]}) := by
  simp [sourceProviderReply, providerReplyState, received, invalid]

private theorem stageCast_marksRejectedCast
    (context : EvalContext) (type : Ty) (value : RuntimeValue) (state : MachineState)
    (message : String) (rejected : castRuntime context type value = .error message) :
    stageCast context type value state =
      (.error message, {state with boundaryRejections := state.boundaryRejections ++ [.stageCast]}) := by
  simp [stageCast, rejected, rejectBoundary]

private theorem stageContinue_marksDeniedWrite
    (grants : HostGrants) (capability key : String) (value : RuntimeValue)
    (continuation : MachineM RuntimeValue) (state : MachineState)
    (recording : state.mode = .record)
    (denied : authorizedWrite grants capability key = false) :
    stageContinue grants capability key value state continuation state =
      (.error "host private-state write capability was not granted",
        {state with boundaryRejections := state.boundaryRejections ++ [.stageWrite]}) := by
  simp [stageContinue, recording, denied, rejectBoundary, machineMMonad, Bind.bind]

mutual
  private def evalTerm : Nat → Program → EvalContext → HostGrants → Provider → Nat →
      List (String × RuntimeValue) → Term → MachineM RuntimeValue
    | 0, _, _, _, _, _, _, _ => fail "native witness execution fuel exhausted"
    | fuel + 1, program, context, grants, provider, scope, environment, term => do
      match term with
      | .unit => pure .unit
      | .native number =>
          if number < context.modulus then pure (.scalar (.native number))
          else fail "noncanonical native constant"
      | .bool value => pure (.scalar (.bool value))
      | .uint maximum number =>
          if canonicalScalar context (.uint maximum number) then pure (.scalar (.uint maximum number))
          else fail "noncanonical bounded unsigned constant"
      | .ref name =>
          match environment.lookup name with
          | some value => pure value
          | none => fail s!"unbound source value '{name}'"
      | .binary operation left right => do
          let values ← evalTerms fuel program context grants provider scope environment [left, right]
          let some left := values[0]? | fail "binary left operand missing"
          let some right := values[1]? | fail "binary right operand missing"
          let left ← liftResult (runtimeScalar left)
          let right ← liftResult (runtimeScalar right)
          let left ← liftResult (scalarPolicyValue left)
          let right ← liftResult (scalarPolicyValue right)
          let result ← liftResult (ScalarPolicy.evaluate operation left right)
          let value := runtimeScalarOfPolicy result
          match value with
          | .scalar scalar =>
              if canonicalScalar context scalar then pure value else fail "noncanonical arithmetic result"
          | _ => fail "invalid arithmetic result"
      | .eq left right => do
          let values ← evalTerms fuel program context grants provider scope environment [left, right]
          equalityPost program.composites context values
      | .cast target value => do
          let value ← evalTerm fuel program context grants provider scope environment value
          liftResult (castRuntime context target value)
      | .disclose _ value | .at _ value =>
          evalTerm fuel program context grants provider scope environment value
      | .select condition yes no => do
          let values ← evalTerms fuel program context grants provider scope environment [condition, yes, no]
          let some condition := values[0]? | fail "selection condition missing"
          let some yes := values[1]? | fail "selection true value missing"
          let some no := values[2]? | fail "selection false value missing"
          let condition ← liftResult (runtimeScalar condition)
          let .bool selected := condition | fail "selection condition is not Bool"
          let yesType := (runtimeTy yes).getD .native
          let noType := (runtimeTy no).getD .native
          let resultType ← liftResult (commonScalarType yesType noType)
          let yes ← liftResult (castRuntime context resultType yes)
          let no ← liftResult (castRuntime context resultType no)
          pure (if selected then yes else no)
      | .witnessCall site name arguments => do
          let arguments ← evalTerms fuel program context grants provider scope environment arguments
          executeWitnessCall program context grants provider site name arguments
      | .call name arguments => do
          let arguments ← evalTerms fuel program context grants provider scope environment arguments
          let types := arguments.map resultTypeOfRuntime
          let target ← liftResult ((Helpers.resolve program scope name types).mapError (·.message))
          let helperEnv ← liftResult (helperEnvironment program context target arguments)
          let state ← get
          withCallPath (state.path ++ [target.id])
            (evalBody fuel program context grants provider target helperEnv target.body)
      | .poseidon2 domain left right => do
          let values ← evalTerms fuel program context grants provider scope environment [left, right]
          let some left := values[0]? | fail "Poseidon left operand missing"
          let some right := values[1]? | fail "Poseidon right operand missing"
          let left ← liftResult (castRuntime context .native left)
          let right ← liftResult (castRuntime context .native right)
          let left ← liftResult (runtimeScalar left)
          let right ← liftResult (runtimeScalar right)
          let .native left := left | fail "Poseidon left operand is not Native"
          let .native right := right | fail "Poseidon right operand is not Native"
          if domain >= context.modulus then fail "noncanonical Poseidon domain"
          else
            match context.poseidon2 domain left right with
            | .error message => fail message
            | .ok result =>
                if result < context.modulus then pure (.scalar (.native result))
                else fail "Poseidon oracle returned noncanonical output"
      | .composite type leaves => do
          let compiled ← liftResult ((Types.compileType program.composites type).mapError (·.message))
          let values ← evalTerms fuel program context grants provider scope environment leaves
          let expected := Helpers.sourceLeafTypes compiled.checked.value
          unless values.length == expected.length do fail "composite source leaf count mismatch"
          let mut numbers := []
          for (expectedTy, value) in expected.zip values do
            let value ← liftResult (castRuntime context expectedTy value)
            let value ← liftResult (runtimeScalar value)
            let number ← liftResult (scalarNumber value)
            numbers := numbers ++ [number]
          liftResult (makeAggregateRuntime program type numbers)
      | .project value projection => do
          let value ← evalTerm fuel program context grants provider scope environment value
          let .aggregate type _ leaves := value | fail "aggregate projection requires a checked value"
          let (compiled, _) ← liftResult (aggregateLeaves program type value)
          let typed ← liftResult ((Types.unflattenChecked compiled leaves).mapError id)
          let selected ← liftResult ((Types.project compiled typed projection).mapError id)
          pure (fromSomeTypedValue selected)
      | .index value index => do
          let values ← evalTerms fuel program context grants provider scope environment [value, index]
          let some parent := values[0]? | fail "aggregate index base missing"
          let some selectedIndex := values[1]? | fail "aggregate index expression missing"
          let .aggregate type _ leaves := parent | fail "dynamic index base is not an aggregate"
          let .vector length _ := type | fail "dynamic index base is not a fixed vector"
          let index ← liftResult (runtimeScalar selectedIndex)
          let position ← liftResult (scalarNumber index)
          if position >= length then fail "aggregate vector index out of bounds"
          else
            let (compiled, _) ← liftResult (aggregateLeaves program type parent)
            let typed ← liftResult ((Types.unflattenChecked compiled leaves).mapError id)
            let selected ← liftResult ((Types.project compiled typed (.vectorIndex position)).mapError id)
            pure (fromSomeTypedValue selected)
      | .boolAnd .. | .boolOr .. | .boolXor .. | .curve .. | .bytes ..
      | .bytes32Literal .. | .foreignConstant .. | .witness _ _ | .ite ..
      | .andThen .. | .orElse .. | .effect .. | .bytesAt .. =>
          fail "source term is outside the bounded native replay semantics"
  termination_by fuel _ _ _ _ _ _ _ => fuel
  decreasing_by all_goals omega

  private def evalTerms : Nat → Program → EvalContext → HostGrants → Provider → Nat →
      List (String × RuntimeValue) → List Term → MachineM (List RuntimeValue)
    | 0, _, _, _, _, _, _, [] => pure []
    | 0, _, _, _, _, _, _, _ :: _ => fail "native witness execution fuel exhausted"
    | _fuel + 1, _program, _context, _grants, _provider, _scope, _environment, [] => pure []
    | fuel + 1, program, context, grants, provider, scope, environment, term :: rest => do
        let value ← evalTerm fuel program context grants provider scope environment term
        let values ← evalTerms fuel program context grants provider scope environment rest
        pure (value :: values)
  termination_by fuel _ _ _ _ _ _ _ => fuel
  decreasing_by all_goals omega

  private def evalBody : Nat → Program → EvalContext → HostGrants → Provider → Declaration →
      List (String × RuntimeValue) → List Statement → MachineM RuntimeValue
    | 0, _, _, _, _, _, _, [] => pure .unit
    | 0, _, _, _, _, _, _, _ :: _ => fail "native witness execution fuel exhausted"
    | _fuel + 1, _, _, _, _, _, _, [] => pure .unit
    | fuel + 1, program, context, grants, provider, declaration, environment, statement :: rest =>
          match statement with
          | .return none => liftResult (coerceRuntime program context declaration.result .unit)
          | .return (some term) => do
              let value ← evalTerm fuel program context grants provider declaration.id.scope environment term
              liftResult (coerceRuntime program context declaration.result value)
          | .bind name ty term => do
              let value ← evalTerm fuel program context grants provider declaration.id.scope environment term
              let value ← liftResult (coerceRuntime program context ty value)
              evalBody fuel program context grants provider declaration ((name, value) :: environment) rest
          | .evaluate term => do
              discard (evalTerm fuel program context grants provider declaration.id.scope environment term)
              evalBody fuel program context grants provider declaration environment rest
          | .assert term => do
              let value ← evalTerm fuel program context grants provider declaration.id.scope environment term
              let value ← liftResult (runtimeScalar value)
              match value with
              | .bool true => evalBody fuel program context grants provider declaration environment rest
              | .bool false => fail "helper assertion failed"
              | _ => fail "helper assertion requires Bool"
          | .stage capability key ty term => do
              let value ← evalTerm fuel program context grants provider declaration.id.scope environment term
              let value ← stageCast context ty value
              let state ← get
              stageContinue grants capability key value state
                (evalBody fuel program context grants provider declaration environment rest)
          | .readCell .. | .writeCell .. =>
              fail "ledger state statements are outside the bounded native replay semantics"
          | .readMap .. | .readMember .. | .writeMap .. =>
              fail "ledger state statements are outside the bounded native replay semantics"
          | .branch .. | .forRange .. =>
              fail "structured control is outside the bounded native replay semantics"
          | .emitEvent .. =>
              fail "event statements are outside the bounded native replay semantics"
  termination_by fuel _ _ _ _ _ _ _ => fuel
  decreasing_by all_goals omega
end

/-- A source evaluator step leaves every previously recorded invocation in
order and appends a finite suffix. The path stays fixed within one call. -/
def RecordStep (before after : MachineState) : Prop :=
  after.mode = .record ∧ after.cursor = after.tape.length ∧
    after.path = before.path ∧ ∃ suffix, after.tape = before.tape ++ suffix ∧
      ∃ rejected, after.boundaryRejections = before.boundaryRejections ++ rejected

/-- A computation preserves the recorder prefix invariant for every valid
recording state, including when the computation returns an error. -/
def RecordSafe {α : Type} (computation : MachineM α) : Prop :=
  ∀ state, state.mode = .record → state.cursor = state.tape.length →
    RecordStep state (computation state).2

/-- Pure evaluator work leaves the recorder state byte-for-byte unchanged. -/
def StatePreserving {α : Type} (computation : MachineM α) : Prop :=
  ∀ state, (computation state).2 = state

theorem RecordStep.refl (state : MachineState)
    (mode : state.mode = .record) (cursor : state.cursor = state.tape.length) :
    RecordStep state state := by
  exact ⟨mode, cursor, rfl, ⟨[], by simp, ⟨[], by simp⟩⟩⟩

private theorem recordStep_providerReplyState (program : Program) (context : EvalContext)
    (signature : WitnessSignature) (reply : WitnessReply) (state : MachineState)
    (mode : state.mode = .record) (cursor : state.cursor = state.tape.length) :
    RecordStep state (providerReplyState program context signature reply state) := by
  cases reply with
  | failure message =>
      simp only [providerReplyState]
      exact RecordStep.refl state mode cursor
  | value value =>
      by_cases valid : runtimeMatches program context signature.result value
      · simp [providerReplyState, valid]
        exact RecordStep.refl state mode cursor
      · simp only [providerReplyState, valid]
        exact ⟨mode, cursor, rfl, ⟨[], by simp, ⟨[.providerCallback], by simp⟩⟩⟩

theorem RecordStep.trans {first middle last : MachineState}
    (hm : RecordStep first middle) (hl : RecordStep middle last) :
    RecordStep first last := by
  rcases hm with ⟨hmMode, hmCursor, hmPath, ⟨middleSuffix, hmTape, ⟨middleRejected, hmRejected⟩⟩⟩
  rcases hl with ⟨hlMode, hlCursor, hlPath, ⟨lastSuffix, hlTape, ⟨lastRejected, hlRejected⟩⟩⟩
  refine ⟨hlMode, hlCursor, ?_, ⟨middleSuffix ++ lastSuffix, ?_,
    ⟨middleRejected ++ lastRejected, ?_⟩⟩⟩
  · exact hlPath.trans hmPath
  · rw [hlTape, hmTape, List.append_assoc]
  · rw [hlRejected, hmRejected, List.append_assoc]

theorem recordSafe_bind {α β : Type} (first : MachineM α) (next : α → MachineM β)
    (hfirst : RecordSafe first) (hnext : ∀ value, RecordSafe (next value)) :
    RecordSafe (first >>= next) := by
  intro state hmode hcursor
  cases firstResult : first state with
  | mk result middle =>
      have hmiddle : RecordStep state middle := by
        simpa [firstResult] using hfirst state hmode hcursor
      cases result with
      | error message =>
          simpa [machineMMonad, Monad.toBind, Bind.bind, firstResult] using hmiddle
      | ok value =>
          have hlast := hnext value middle hmiddle.1 hmiddle.2.1
          simpa [machineMMonad, Monad.toBind, Bind.bind, firstResult] using
            RecordStep.trans hmiddle hlast

@[simp] theorem recordSafe_pure {α : Type} (value : α) : RecordSafe (pure value : MachineM α) := by
  intro state hmode hcursor
  exact RecordStep.refl state hmode hcursor

@[simp] theorem recordSafe_fail {α : Type} (message : String) : RecordSafe (fail message : MachineM α) := by
  intro state hmode hcursor
  exact RecordStep.refl state hmode hcursor

@[simp] theorem recordSafe_liftResult {α : Type} (result : Except String α) :
    RecordSafe (liftResult result) := by
  intro state hmode hcursor
  exact RecordStep.refl state hmode hcursor

theorem recordSafe_get : RecordSafe get := by
  intro state hmode hcursor
  exact RecordStep.refl state hmode hcursor

@[simp] theorem statePreserving_bind {α β : Type} (first : MachineM α) (next : α → MachineM β)
    (hfirst : StatePreserving first) (hnext : ∀ value, StatePreserving (next value)) :
    StatePreserving (first >>= next) := by
  intro state
  cases hrun : first state with
  | mk result middle =>
      have hmiddle : middle = state := by simpa [hrun] using hfirst state
      cases result with
      | error message => simpa [machineMMonad, Monad.toBind, Bind.bind, hrun] using hmiddle
      | ok value =>
          simpa [machineMMonad, Monad.toBind, Bind.bind, hrun, hmiddle] using hnext value state

@[simp] theorem statePreserving_pure {α : Type} (value : α) : StatePreserving (pure value : MachineM α) := by
  intro state
  rfl

@[simp] theorem statePreserving_fail {α : Type} (message : String) : StatePreserving (fail message : MachineM α) := by
  intro state
  rfl

@[simp] theorem statePreserving_liftResult {α : Type} (result : Except String α) :
    StatePreserving (liftResult result) := by
  intro state
  rfl

@[simp] theorem statePreserving_get : StatePreserving get := by
  intro state
  rfl

@[simp] theorem recordSafe_ofStatePreserving {α : Type} (computation : MachineM α)
    (preserving : StatePreserving computation) : RecordSafe computation := by
  intro state hmode hcursor
  rw [preserving state]
  exact RecordStep.refl state hmode hcursor

@[simp] theorem recordSafe_if {α : Type} (condition : Bool)
    (yes no : MachineM α) (hy : RecordSafe yes) (hn : RecordSafe no) :
    RecordSafe (if condition then yes else no) := by
  cases condition <;> simp_all

@[simp] theorem statePreserving_if {α : Type} (condition : Bool)
    (yes no : MachineM α) (hy : StatePreserving yes) (hn : StatePreserving no) :
    StatePreserving (if condition then yes else no) := by
  cases condition <;> simp_all

private theorem statePreserving_ite {α : Type} (condition : Prop) [Decidable condition]
    (yes no : MachineM α) (hy : StatePreserving yes) (hn : StatePreserving no) :
    StatePreserving (if condition then yes else no) := by
  by_cases h : condition <;> simp [h, hy, hn]

private theorem statePreserving_exceptMatch {α β : Type} (result : Except String α)
    (onError : String → MachineM β) (onOk : α → MachineM β)
    (herror : ∀ message, StatePreserving (onError message))
    (hok : ∀ value, StatePreserving (onOk value)) :
    StatePreserving (match result with
      | .error message => onError message
      | .ok value => onOk value) := by
  cases result with
  | error message => exact herror message
  | ok value => exact hok value

private theorem statePreserving_optionMatch {α β : Type} (result : Option α)
    (onNone : MachineM β) (onSome : α → MachineM β)
    (hnone : StatePreserving onNone) (hsome : ∀ value, StatePreserving (onSome value)) :
    StatePreserving (match result with
      | none => onNone
      | some value => onSome value) := by
  cases result with
  | none => exact hnone
  | some value => exact hsome value

private theorem recordSafe_poseidonTail (context : EvalContext) (domain : Nat)
    (leftValue rightValue : RuntimeValue) :
    RecordSafe (do
      let left ← liftResult (castRuntime context .native leftValue)
      let right ← liftResult (castRuntime context .native rightValue)
      let left ← liftResult (runtimeScalar left)
      let right ← liftResult (runtimeScalar right)
      let .native left := left | fail "Poseidon left operand is not Native"
      let .native right := right | fail "Poseidon right operand is not Native"
      if domain >= context.modulus then fail "noncanonical Poseidon domain"
      else
        match context.poseidon2 domain left right with
        | .error message => fail message
        | .ok result =>
            if result < context.modulus then pure (RuntimeValue.scalar (Value.native result))
            else fail "Poseidon oracle returned noncanonical output") := by
  apply recordSafe_bind
  · exact recordSafe_liftResult _
  · intro left
    apply recordSafe_bind
    · exact recordSafe_liftResult _
    · intro right
      apply recordSafe_bind
      · exact recordSafe_liftResult (runtimeScalar left)
      · intro leftScalar
        apply recordSafe_bind
        · exact recordSafe_liftResult (runtimeScalar right)
        · intro rightScalar
          cases leftScalar with
          | native leftNumber =>
              cases rightScalar with
              | native rightNumber =>
                  by_cases hdomain : domain >= context.modulus
                  · simp only [if_pos hdomain]
                    exact recordSafe_fail _
                  · simp only [if_neg hdomain]
                    cases horacle : context.poseidon2 domain leftNumber rightNumber with
                    | error message =>
                        simp only [horacle]
                        exact recordSafe_fail message
                    | ok result =>
                        simp only [horacle]
                        by_cases hcanonical : result < context.modulus
                        · simp only [if_pos hcanonical]
                          exact recordSafe_pure _
                        · simp only [if_neg hcanonical]
                          exact recordSafe_fail _
              | bool _ => exact recordSafe_fail _
              | uint _ _ => exact recordSafe_fail _
              | bytes _ _ | opaqueBytes _ | opaqueString _ | jubjubScalar _ | jubjubPoint _ _
              | foreignBase _ _ | foreignScalar _ _ | foreignPoint _ _ => exact recordSafe_fail _
          | bool _ => exact recordSafe_fail _
          | uint _ _ => exact recordSafe_fail _
          | bytes _ _ | opaqueBytes _ | opaqueString _ | jubjubScalar _ | jubjubPoint _ _
          | foreignBase _ _ | foreignScalar _ _ | foreignPoint _ _ => exact recordSafe_fail _

private theorem statePreserving_listForIn {α β : Type}
    (values : List α) (initial : β)
    (step : α → β → MachineM (ForInStep β))
    (safeStep : ∀ value accumulator, StatePreserving (step value accumulator)) :
    StatePreserving (forIn values initial step) := by
  induction values generalizing initial with
  | nil => simp only [List.forIn_nil]; exact statePreserving_pure initial
  | cons head tail ih =>
      simp only [List.forIn_cons]
      apply statePreserving_bind
      · exact safeStep head initial
      · intro result
        cases result with
        | done final => exact statePreserving_pure final
        | yield next => exact ih next

theorem recordSafe_modify (update : MachineState → MachineState)
    (preserves : ∀ state, state.mode = .record → state.cursor = state.tape.length →
      RecordStep state (update state)) :
    RecordSafe (modify update) := by
  intro state hmode hcursor
  simpa [modify] using preserves state hmode hcursor

private theorem recordEvent_recordSafe (event : WitnessInvocation) :
    RecordSafe (recordEvent event) := by
  intro state hmode hcursor
  unfold recordEvent
  simp only [machineMMonad, modify]
  refine ⟨?_, ?_, rfl, ⟨[event], ?_, ⟨[], ?_⟩⟩⟩
  · exact hmode
  · simp [hcursor]
  · simp
  · simp

private theorem recordEvent_finalState (event : WitnessInvocation) (state : MachineState) :
    (recordEvent event state).2 =
      {state with tape := state.tape ++ [event], cursor := state.cursor + 1} := by
  rfl

private theorem recordEvent_resultPair (event : WitnessInvocation) (state : MachineState) :
    recordEvent event state =
      (.ok (), {state with tape := state.tape ++ [event], cursor := state.cursor + 1}) := by
  rfl

private theorem witnessValue_finalState (program : Program) (context : EvalContext)
    (signature : WitnessSignature) (reply : WitnessReply) (state : MachineState) :
    (witnessValue program context signature reply state).2 = state := by
  cases h : normalizedReply program context signature reply <;>
    simp [witnessValue, h, fail, machineMMonad, Monad.toApplicative,
      Applicative.toPure, Pure.pure]

private theorem recordStep_recordWitnessCall (program : Program) (context : EvalContext)
    (provider : Provider) (site name : String) (signature : WitnessSignature)
    (arguments : List RuntimeValue) (state : MachineState)
    (hmode : state.mode = .record) (hcursor : state.cursor = state.tape.length) :
    RecordStep state (recordWitnessCall program context provider site name signature arguments state state).2 := by
  let request : ProviderRequest := {
    name := signature.name, operation := signature.operation, capability := signature.capability,
    privateKey := signature.privateKey, stagedState := state.stagedState, arguments}
  cases hprovider : providerReply provider signature request with
  | error message =>
      have hrun :
          (recordWitnessCall program context provider site name signature arguments state state).2 =
            {state with boundaryRejections := state.boundaryRejections ++ [.providerCallback]} := by
        simp [recordWitnessCall, sourceProviderReply, request, hprovider, liftResult,
          machineMMonad, Monad.toBind, Bind.bind]
      rw [hrun]
      exact ⟨hmode, hcursor, rfl, ⟨[], by simp, ⟨[.providerCallback], by simp⟩⟩⟩
  | ok reply =>
      let normalized := normalizedReply program context signature reply
      let replyState := providerReplyState program context signature reply state
      let event : WitnessInvocation := {
        ordinal := state.cursor, site, name, path := state.path,
        operation := signature.operation, capability := signature.capability,
        privateKey := signature.privateKey, resultType := signature.result, arguments,
        reply := normalized}
      have hcall :
          (recordWitnessCall program context provider site name signature arguments state state).2 =
            (recordEvent event replyState).2 := by
        simp [recordWitnessCall, sourceProviderReply, request, event, normalized, replyState,
          hprovider,
          MachineM, liftResult, machineMMonad, Monad.toBind, Bind.bind,
          recordEvent_resultPair, witnessValue_finalState]
      rw [hcall]
      have replyStateMode : replyState.mode = .record := by
        cases reply with
        | failure message => simpa [replyState, providerReplyState] using hmode
        | value value =>
            by_cases valid : runtimeMatches program context signature.result value = true
            · simp [replyState, providerReplyState, valid, hmode]
            · simp [replyState, providerReplyState, valid, hmode]
      have replyStateCursor : replyState.cursor = replyState.tape.length := by
        cases reply with
        | failure message => simpa [replyState, providerReplyState] using hcursor
        | value value =>
            by_cases valid : runtimeMatches program context signature.result value = true
            · simp [replyState, providerReplyState, valid, hcursor]
            · simp [replyState, providerReplyState, valid, hcursor]
      exact RecordStep.trans
        (recordStep_providerReplyState program context signature reply state hmode hcursor)
        (recordEvent_recordSafe event replyState replyStateMode replyStateCursor)

private theorem recordSafe_authorizeSignature (grants : HostGrants) (signature : WitnessSignature) :
    RecordSafe (authorizeSignature grants signature) := by
  intro state hmode hcursor
  cases hallowed : authorizedProvider grants signature <;>
    simp [authorizeSignature, hallowed, hmode, hcursor, RecordStep, fail, machineMMonad,
      Monad.toBind, Bind.bind, Pure.pure, Applicative.toPure, Monad.toApplicative]

private theorem recordSafe_witnessValue (program : Program) (context : EvalContext)
    (signature : WitnessSignature) (reply : WitnessReply) :
    RecordSafe (witnessValue program context signature reply) := by
  intro state hmode hcursor
  cases hnormalized : normalizedReply program context signature reply <;>
    simp [witnessValue, hnormalized, hmode, hcursor, RecordStep, fail, machineMMonad,
      Monad.toBind, Bind.bind, Pure.pure, Applicative.toPure, Monad.toApplicative]

private theorem recordSafe_withCallPath {α : Type} (path : List DeclarationId)
    (computation : MachineM α) (safe : RecordSafe computation) :
    RecordSafe (withCallPath path computation) := by
  intro state hmode hcursor
  let entered := {state with path := path}
  have henteredMode : entered.mode = .record := by simp [entered, hmode]
  have henteredCursor : entered.cursor = entered.tape.length := by simp [entered, hcursor]
  rcases safe entered henteredMode henteredCursor with
    ⟨hmode', hcursor', hpath', ⟨suffix, htape⟩⟩
  refine ⟨hmode', hcursor', rfl, ⟨suffix, ?_⟩⟩
  simpa [withCallPath, entered] using htape

private theorem recordSafe_bind_get {α : Type} (next : MachineState → MachineM α)
    (safe : ∀ state, state.mode = .record → state.cursor = state.tape.length →
      RecordStep state (next state state).2) :
    RecordSafe (get >>= next) := by
  intro state hmode hcursor
  change RecordStep state ((next state) state).2
  exact safe state hmode hcursor

private theorem recordStep_stageContinue (grants : HostGrants) (capability key : String)
    (value : RuntimeValue) (state : MachineState) (continuation : MachineM RuntimeValue)
    (hmode : state.mode = .record) (hcursor : state.cursor = state.tape.length)
    (hcontinuation : RecordSafe continuation) :
    RecordStep state (stageContinue grants capability key value state continuation state).2 := by
  let updated : MachineState := {state with
    stagedState := writeState state.stagedState key value,
    journal := state.journal ++ [(key, value)]}
  have hupdated : RecordStep state updated := by
    refine ⟨?_, ?_, rfl, ⟨[], ?_, ⟨[], ?_⟩⟩⟩
    · simpa [updated] using hmode
    · simpa [updated] using hcursor
    · simp [updated]
    · simp [updated]
  cases hstateMode : state.mode with
  | replay => cases hmode.symm.trans hstateMode
  | record =>
      by_cases hauthorised : authorizedWrite grants capability key
      · have hcontinued := hcontinuation updated hupdated.1 hupdated.2.1
        have hrun :
            (stageContinue grants capability key value state continuation state).2 =
              (continuation updated).2 := by
          simp [stageContinue, hstateMode, hauthorised, updated, modify,
            machineMMonad, Monad.toBind, Bind.bind]
        rw [hrun]
        exact RecordStep.trans hupdated hcontinued
      · have hrun :
            (stageContinue grants capability key value state continuation state).2 =
              {state with boundaryRejections := state.boundaryRejections ++ [.stageWrite]} := by
          simp [stageContinue, hstateMode, hauthorised, rejectBoundary, modify,
            machineMMonad, Monad.toBind, Bind.bind]
        rw [hrun]
        exact ⟨hmode, hcursor, rfl, ⟨[], by simp, ⟨[.stageWrite], by simp⟩⟩⟩

private theorem recordSafe_getStageContinue (grants : HostGrants) (capability key : String)
    (value : RuntimeValue) (continuation : MachineM RuntimeValue)
    (hcontinuation : RecordSafe continuation) :
    RecordSafe (get >>= fun state => stageContinue grants capability key value state continuation) := by
  apply recordSafe_bind_get
  intro state hmode hcursor
  exact recordStep_stageContinue grants capability key value state continuation
    hmode hcursor hcontinuation

private theorem recordSafe_stageCast (context : EvalContext) (type : Ty)
    (value : RuntimeValue) : RecordSafe (stageCast context type value) := by
  intro state hmode hcursor
  cases hcast : castRuntime context type value with
  | ok result =>
      simp only [stageCast, hcast]
      exact RecordStep.refl state hmode hcursor
  | error message =>
      simp only [stageCast, hcast, rejectBoundary]
      exact ⟨hmode, hcursor, rfl, ⟨[], by simp, ⟨[.stageCast], by simp⟩⟩⟩

private theorem recordSafe_executeWitnessCallMode (program : Program) (context : EvalContext)
    (provider : Provider) (site name : String) (signature : WitnessSignature)
    (arguments : List RuntimeValue) :
    RecordSafe (executeWitnessCallMode program context provider site name signature arguments) := by
  unfold executeWitnessCallMode
  apply recordSafe_bind_get
  intro current hcurrentMode hcurrentCursor
  simp only [hcurrentMode]
  exact recordStep_recordWitnessCall program context provider site name
    signature arguments current hcurrentMode hcurrentCursor

private theorem recordSafe_executeWitnessCall (program : Program) (context : EvalContext)
    (grants : HostGrants) (provider : Provider) (site name : String)
    (arguments : List RuntimeValue) :
    RecordSafe (executeWitnessCall program context grants provider site name arguments) := by
  unfold executeWitnessCall
  apply recordSafe_bind
  · exact recordSafe_liftResult ((Helpers.witnessSignature program name).mapError (·.message))
  · intro signature
    apply recordSafe_bind
    · exact recordSafe_authorizeSignature grants signature
    · intro _
      apply recordSafe_bind
      · exact recordSafe_liftResult (coerceArguments program context signature.parameters arguments)
      · intro coerced
        by_cases hvalid : validateWitnessArguments program context signature coerced
        · simp only [hvalid]
          exact recordSafe_executeWitnessCallMode program context provider site name signature coerced
        · simp only [hvalid]
          exact recordSafe_fail "typed witness argument binding mismatch"

private theorem recordSafe_testMonad (input : Except String Nat) :
    RecordSafe (do
      let value ← liftResult input
      pure value) := by
  repeat' first
  | exact recordSafe_pure _
  | exact recordSafe_fail _
  | exact recordSafe_liftResult _
  | apply recordSafe_bind
  | intro _

macro "recorder_safe" : tactic => `(tactic|
  repeat' first
  | assumption
  | exact recordSafe_pure _
  | exact recordSafe_fail _
  | exact recordSafe_liftResult _
  | apply termSafe
  | apply termsSafe
  | apply bodySafe
  | apply recordSafe_bind
  | apply recordSafe_if
  | apply recordSafe_executeWitnessCall
  | apply recordSafe_withCallPath
  | apply recordSafe_getStageContinue)

macro "state_preserving" : tactic => `(tactic|
  repeat' first
  | exact statePreserving_pure _
  | exact statePreserving_fail _
  | exact statePreserving_liftResult _
  | exact statePreserving_get
  | apply statePreserving_bind
  | apply statePreserving_if
  | apply statePreserving_ite
  | apply statePreserving_exceptMatch
  | apply statePreserving_optionMatch
  | apply statePreserving_listForIn
  | intro _
  | split
  | simp [fail, machineMMonad, runtimeScalarOfPolicy])

private theorem equalityPost_frame (composites : Types.CompositeEnv) (context : EvalContext)
    (values : List RuntimeValue) : StatePreserving (equalityPost composites context values) := by
  intro state
  unfold equalityPost
  cases hleft : values[0]? with
  | none => simp [hleft, fail]
  | some left =>
    cases hright : values[1]? with
    | none => simp [hleft, hright, fail]
    | some right =>
      simp only [hleft, hright]
      state_preserving

private theorem body_recordSafe_step (fuel : Nat)
    (termSafe : ∀ program context grants provider scope environment term,
      RecordSafe (evalTerm fuel program context grants provider scope environment term))
    (bodySafe : ∀ program context grants provider declaration environment body,
      RecordSafe (evalBody fuel program context grants provider declaration environment body)) :
    ∀ program context grants provider declaration environment body,
      RecordSafe (evalBody (fuel + 1) program context grants provider declaration environment body) := by
  intro program context grants provider declaration environment body
  cases body with
  | nil => simp only [evalBody]; exact recordSafe_pure RuntimeValue.unit
  | cons statement rest =>
    cases statement with
    | bind name type term =>
      simp only [evalBody]
      apply recordSafe_bind
      · exact termSafe program context grants provider declaration.id.scope environment term
      · intro value
        apply recordSafe_bind
        · exact recordSafe_liftResult _
        · intro value
          exact bodySafe program context grants provider declaration ((name,value)::environment) rest
    | evaluate term =>
      simp only [evalBody]
      apply recordSafe_bind
      · change RecordSafe ((evalTerm fuel program context grants provider declaration.id.scope environment term) >>= fun _ => pure ())
        exact recordSafe_bind _ _ (termSafe program context grants provider declaration.id.scope environment term)
          (fun _ => recordSafe_pure ())
      · intro _
        exact bodySafe program context grants provider declaration environment rest
    | assert term =>
      simp only [evalBody]
      apply recordSafe_bind
      · exact termSafe program context grants provider declaration.id.scope environment term
      · intro value
        apply recordSafe_bind
        · exact recordSafe_liftResult _
        · intro value
          cases value with
          | bool selected =>
            cases selected with
            | true => exact bodySafe program context grants provider declaration environment rest
            | false => exact recordSafe_fail _
          | native _ => exact recordSafe_fail _
          | uint _ _ => exact recordSafe_fail _
          | bytes _ _ | opaqueBytes _ | opaqueString _ | jubjubScalar _ | jubjubPoint _ _
          | foreignBase _ _ | foreignScalar _ _ | foreignPoint _ _ => exact recordSafe_fail _
    | «return» term =>
      cases term with
      | none => simp only [evalBody]; exact recordSafe_liftResult _
      | some term =>
        simp only [evalBody]
        apply recordSafe_bind
        · exact termSafe program context grants provider declaration.id.scope environment term
        · intro value
          exact recordSafe_liftResult _
    | stage capability key type term =>
      simp only [evalBody]
      apply recordSafe_bind
      · exact termSafe program context grants provider declaration.id.scope environment term
      · intro value
        apply recordSafe_bind
        · exact recordSafe_stageCast context type value
        · intro value
          exact recordSafe_getStageContinue grants capability key value _
            (bodySafe program context grants provider declaration environment rest)
    | branch condition yes no =>
      simp only [evalBody]
      exact recordSafe_fail _
    | forRange index start stop loopBody =>
      simp only [evalBody]
      exact recordSafe_fail _
    | emitEvent kind payload =>
      simp only [evalBody]
      exact recordSafe_fail _
    | readCell state destination ty =>
      simp only [evalBody]
      exact recordSafe_fail _
    | writeCell state ty value =>
      simp only [evalBody]
      exact recordSafe_fail _
    | readMap state destination keyTy valueTy key =>
      simp only [evalBody]
      exact recordSafe_fail _
    | readMember state destination keyTy valueTy key =>
      simp only [evalBody]
      exact recordSafe_fail _
    | writeMap state keyTy valueTy key value =>
      simp only [evalBody]
      exact recordSafe_fail _

set_option maxHeartbeats 1000000 in
private theorem evaluator_recordSafe (fuel : Nat) :
    (∀ program context grants provider scope environment term,
      RecordSafe (evalTerm fuel program context grants provider scope environment term)) ∧
    (∀ program context grants provider scope environment terms,
      RecordSafe (evalTerms fuel program context grants provider scope environment terms)) ∧
    (∀ program context grants provider declaration environment body,
      RecordSafe (evalBody fuel program context grants provider declaration environment body)) := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro program context grants provider scope environment term
        simp only [evalTerm]
        exact recordSafe_fail "native witness execution fuel exhausted"
      · intro program context grants provider scope environment terms
        cases terms with
        | nil => simp only [evalTerms]; exact recordSafe_pure []
        | cons term rest => simp only [evalTerms]; exact recordSafe_fail "native witness execution fuel exhausted"
      · intro program context grants provider declaration environment body
        cases body with
        | nil => simp only [evalBody]; exact recordSafe_pure RuntimeValue.unit
        | cons statement rest => simp only [evalBody]; exact recordSafe_fail "native witness execution fuel exhausted"
  | succ fuel ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro program context grants provider scope environment term
        have termSafe : ∀ term, RecordSafe
            (evalTerm fuel program context grants provider scope environment term) :=
          ih.1 program context grants provider scope environment
        have termsSafe : ∀ terms, RecordSafe
            (evalTerms fuel program context grants provider scope environment terms) :=
          ih.2.1 program context grants provider scope environment
        have bodySafe : ∀ declaration environment body, RecordSafe
            (evalBody fuel program context grants provider declaration environment body) :=
          ih.2.2 program context grants provider
        cases term with
        | unit => simp only [evalTerm]; exact recordSafe_pure RuntimeValue.unit
        | native number =>
            simp only [evalTerm]
            by_cases h : number < context.modulus
            · simp only [if_pos h]
              exact recordSafe_pure _
            · simp only [if_neg h]
              exact recordSafe_fail _
        | bool value => simp only [evalTerm]; exact recordSafe_pure _
        | uint maximum number =>
            simp only [evalTerm]
            by_cases h : canonicalScalar context (Value.uint maximum number) = true
            · simp only [if_pos h]
              exact recordSafe_pure _
            · simp only [if_neg h]
              exact recordSafe_fail _
        | ref name =>
            simp only [evalTerm]
            cases hlookup : environment.lookup name with
            | some value => simp only [hlookup]; exact recordSafe_pure value
            | none => simp only [hlookup]; exact recordSafe_fail _
        | binary operation left right =>
            simp only [evalTerm]
            apply recordSafe_bind
            · exact termsSafe [left, right]
            · intro values
              cases hleft : values[0]? with
              | none => simp only [hleft]; exact recordSafe_fail _
              | some leftValue =>
                  cases hright : values[1]? with
                  | none => simp only [hleft, hright]; exact recordSafe_fail _
                  | some rightValue =>
                      simp only [hleft, hright]
                      apply recordSafe_ofStatePreserving
                      state_preserving
        | eq left right =>
            simp only [evalTerm]
            apply recordSafe_bind
            · exact termsSafe [left, right]
            · intro values
              exact recordSafe_ofStatePreserving _ (equalityPost_frame program.composites context values)
        | cast target value =>
            simp only [evalTerm]
            apply recordSafe_bind
            · exact termSafe value
            · intro result
              exact recordSafe_liftResult (castRuntime context target result)
        | disclose span value => simp only [evalTerm]; exact termSafe value
        | select condition yes no =>
            simp only [evalTerm]
            apply recordSafe_bind
            · exact termsSafe [condition, yes, no]
            · intro values
              cases hcondition : values[0]? with
              | none => simp only [hcondition]; exact recordSafe_fail _
              | some conditionValue =>
                cases hyes : values[1]? with
                | none => simp only [hcondition, hyes]; exact recordSafe_fail _
                | some yesValue =>
                  cases hno : values[2]? with
                  | none => simp only [hcondition, hyes, hno]; exact recordSafe_fail _
                  | some noValue =>
                    simp only [hcondition, hyes, hno]
                    apply recordSafe_bind
                    · exact recordSafe_liftResult (runtimeScalar conditionValue)
                    · intro conditionScalar
                      cases conditionScalar with
                      | bool selected =>
                          apply recordSafe_ofStatePreserving
                          state_preserving
                      | native _ => exact recordSafe_fail _
                      | uint _ _ => exact recordSafe_fail _
                      | bytes _ _ | opaqueBytes _ | opaqueString _ | jubjubScalar _ | jubjubPoint _ _
                      | foreignBase _ _ | foreignScalar _ _ | foreignPoint _ _ => exact recordSafe_fail _
        | boolAnd _ _ | boolOr _ _ | boolXor _ _ =>
            simp only [evalTerm]; exact recordSafe_fail _
        | curve _ _ | bytes _ _ | bytes32Literal _ | foreignConstant _ _ | bytesAt _ _ =>
            simp only [evalTerm]; exact recordSafe_fail _
        | ite _ _ _ => simp only [evalTerm]; exact recordSafe_fail _
        | andThen _ _ => simp only [evalTerm]; exact recordSafe_fail _
        | orElse _ _ => simp only [evalTerm]; exact recordSafe_fail _
        | witness _ _ => simp only [evalTerm]; exact recordSafe_fail _
        | witnessCall site name arguments =>
            simp only [evalTerm]
            apply recordSafe_bind
            · exact termsSafe arguments
            · intro values
              exact recordSafe_executeWitnessCall program context grants provider site name values
        | poseidon2 domain left right =>
            simp only [evalTerm]
            apply recordSafe_bind
            · exact termsSafe [left, right]
            · intro values
              cases hleft : values[0]? with
              | none => simp only [hleft]; exact recordSafe_fail _
              | some leftValue =>
                cases hright : values[1]? with
                | none => simp only [hleft, hright]; exact recordSafe_fail _
                | some rightValue =>
                  simp only [hleft, hright]
                  exact recordSafe_poseidonTail context domain leftValue rightValue
        | call name arguments =>
            simp only [evalTerm]
            apply recordSafe_bind
            · exact termsSafe arguments
            · intro values
              apply recordSafe_bind
              · exact recordSafe_liftResult
                  ((Helpers.resolve program scope name (values.map resultTypeOfRuntime)).mapError (·.message))
              · intro target
                apply recordSafe_bind
                · exact recordSafe_liftResult (helperEnvironment program context target values)
                · intro helperEnv
                  apply recordSafe_bind
                  · exact recordSafe_get
                  · intro state
                    exact recordSafe_withCallPath (state.path ++ [target.id])
                      (evalBody fuel program context grants provider target helperEnv target.body)
                      (bodySafe target helperEnv target.body)
        | composite type leaves =>
            simp only [evalTerm]
            apply recordSafe_bind
            · exact recordSafe_liftResult
                ((Types.compileType program.composites type).mapError (·.message))
            · intro compiled
              apply recordSafe_bind
              · exact termsSafe leaves
              · intro values
                apply recordSafe_ofStatePreserving
                state_preserving
        | project value projection =>
            simp only [evalTerm]
            apply recordSafe_bind
            · exact termSafe value
            · intro aggregate
              cases aggregate with
              | unit => exact recordSafe_fail _
              | scalar _ => exact recordSafe_fail _
              | aggregate type fingerprint leaves =>
                  apply recordSafe_ofStatePreserving
                  state_preserving
        | index value index =>
            simp only [evalTerm]
            apply recordSafe_bind
            · exact termsSafe [value, index]
            · intro values
              cases hvalue : values[0]? with
              | none => simp only [hvalue]; exact recordSafe_fail _
              | some parent =>
                cases hindex : values[1]? with
                | none => simp only [hvalue, hindex]; exact recordSafe_fail _
                | some selectedIndex =>
                    simp only [hvalue, hindex]
                    cases parent with
                    | unit => exact recordSafe_fail _
                    | scalar _ => exact recordSafe_fail _
                    | aggregate type fingerprint leaves =>
                        cases type with
                        | unit => exact recordSafe_fail _
                        | scalar _ => exact recordSafe_fail _
                        | tuple _ => exact recordSafe_fail _
                        | «structure» _ => exact recordSafe_fail _
                        | vector length element =>
                            apply recordSafe_ofStatePreserving
                            state_preserving
                        | bytes _ => exact recordSafe_fail _
                        | enumeration _ => exact recordSafe_fail _
        | effect _ _ _ => simp only [evalTerm]; exact recordSafe_fail _
        | «at» span value => simp only [evalTerm]; exact termSafe value
      · intro program context grants provider scope environment terms
        have termSafe : ∀ term, RecordSafe
            (evalTerm fuel program context grants provider scope environment term) :=
          ih.1 program context grants provider scope environment
        have termsSafe : ∀ terms, RecordSafe
            (evalTerms fuel program context grants provider scope environment terms) :=
          ih.2.1 program context grants provider scope environment
        have bodySafe : ∀ declaration environment body, RecordSafe
            (evalBody fuel program context grants provider declaration environment body) :=
          ih.2.2 program context grants provider
        cases terms with
        | nil => simp only [evalTerms]; exact recordSafe_pure []
        | cons term rest =>
            simp only [evalTerms]
            apply recordSafe_bind
            · exact termSafe term
            · intro value
              apply recordSafe_bind
              · exact termsSafe rest
              · intro values
                exact recordSafe_pure (value :: values)
      · intro program context grants provider declaration environment body
        exact body_recordSafe_step fuel
          (fun program context grants provider scope environment term =>
            ih.1 program context grants provider scope environment term)
          (fun program context grants provider declaration environment body =>
            ih.2.2 program context grants provider declaration environment body)
          program context grants provider declaration environment body

private def executionObservation (result : Except String RuntimeValue)
    (state : MachineState) : ExecutionObservation := {
  result := match result with
    | .ok value => .success value
    | .error message => .failure message
  cursor := state.cursor
  tape := state.tape
  journal := state.journal
  stagedState := state.stagedState
}

private theorem executionObservation_ignoresBoundaryRejections
    (result : Except String RuntimeValue) (state : MachineState)
    (rejections : List HostBoundaryRejection) :
    executionObservation result {state with boundaryRejections := rejections} =
      executionObservation result state := by
  rfl

private def canonicalInitialState (program : Program) (context : EvalContext)
    (state : List (String × RuntimeValue)) : Bool :=
  uniqueNames (state.map Prod.fst) && state.all fun (_, value) =>
    runtimeMatches program context (resultTypeOfRuntime value) value

/-- Run source once. Stage writes update the provider-visible source store.
Every typed witness call records its exact declaration, call path, typed
arguments, reply, and ordinal, including provider failures and zero-leaf Unit
calls. -/
def recordInvocation (limits : Helpers.Limits) (fuel : Nat) (context : EvalContext)
    (program : Program) (entryName : String) (originalInputs initialState : List (String × RuntimeValue))
    (grants : HostGrants) (provider : Provider) : Except String RecordedInvocation := do
  unless context.modulus == Field.modulus do .error "execution context uses an unpinned field modulus"
  if fuel > limits.maxExecutionSteps then .error "execution fuel exceeds the configured limit"
  let admission ← admitNativeReplay limits program entryName
  let originalInputs ← normalizeExternalInputs context admission.externalInputs originalInputs
  unless canonicalInitialState program context initialState do
    .error "initial private state contains duplicate keys or invalid canonical values"
  let environment ← entryEnvironment program context entryName originalInputs
  let (_, declaration) ← entrypoint program entryName
  let initial : MachineState := {
    mode := .record, stagedState := initialState, path := [declaration.id]}
  let (result, finalState) :=
    (evalBody fuel program context grants provider declaration environment declaration.body) initial
  pure {
    source := program, entryName, originalInputs, initialState, grants,
    observation := executionObservation result finalState}

/-- Replay uses the stored source object, recompiles its exact erased program,
validates actual compiler call bindings, and consumes the frozen tape. The
provider callback is deliberately unreachable in replay mode. -/
def replayInvocation (limits : Helpers.Limits) (fuel : Nat) (context : EvalContext)
    (invocation : RecordedInvocation) (suppliedInputs : List (String × RuntimeValue)) :
    Except String ReplayReport := do
  unless context.modulus == Field.modulus do .error "execution context uses an unpinned field modulus"
  if fuel > limits.maxExecutionSteps then .error "execution fuel exceeds the configured limit"
  let admission ← admitNativeReplay limits invocation.source invocation.entryName
  let suppliedInputs ← normalizeExternalInputs context admission.externalInputs suppliedInputs
  unless sameRuntimeBindings suppliedInputs invocation.originalInputs do
    .error "replay inputs differ from the recorded proof invocation"
  let requireComplete := match invocation.observation.result with
    | .success _ => true
    | .failure _ => false
  validateCallTape invocation.source context admission.host.calls
    invocation.observation.tape requireComplete
  let completeValues ← match invocation.observation.result with
    | .success _ => do
        let fresh ← bindTape invocation.source context admission.host.calls invocation.observation.tape
        validateCompleteInputMap context admission invocation.originalInputs fresh
    | .failure _ => pure []
  let completeInputs := match invocation.observation.result with
    | .success _ =>
        (admission.host.circuit.inputs.zip completeValues).map fun (input, (name, value)) => {
          name, type := input.ty, visibility := input.visibility, value}
    | .failure _ => []
  let erased := Noctium.Witness.eraseProgram invocation.source
  let (_, declaration) ← entrypoint erased invocation.entryName
  let environment ← entryEnvironment erased context invocation.entryName invocation.originalInputs
  let replayState : MachineState := {
    mode := .replay, stagedState := invocation.initialState,
    tape := invocation.observation.tape, path := [declaration.id]}
  let neverRunProvider : Provider := fun _ => .failure "replay attempted to rerun a host provider"
  let (rawResult, finalState) :=
    (evalBody fuel erased context invocation.grants neverRunProvider declaration
      environment declaration.body) replayState
  let replayResult :=
    if finalState.cursor == invocation.observation.tape.length then rawResult
    else .error "native witness replay left unused invocation records"
  let execution := executionObservation replayResult finalState
  let matchesRecordedSource :=
    execution.result == invocation.observation.result &&
      execution.cursor == invocation.observation.cursor &&
      execution.tape == invocation.observation.tape
  pure {execution, completeInputs, matchesRecordedSource}

end Noctium.Witness.Semantics







namespace Noctium.Witness.Semantics

open Helpers

private theorem resolve_eraseProgram (limits : Helpers.Limits) (program : Program)
    (scope : Nat) (name : String) (arguments : List ResultType) (span : SourceSpan)
    (sourceAdmitted : Helpers.syntacticPreflight limits program = .ok ())
    (mappedAdmitted : Helpers.syntacticPreflight limits (Noctium.Witness.eraseProgram program) = .ok ()) :
    Helpers.resolveWithLimits limits (Noctium.Witness.eraseProgram program) scope name arguments span =
      (Helpers.resolveWithLimits limits program scope name arguments span).map
        (fun declaration => {declaration with body := Noctium.Witness.eraseStages declaration.body}) := by
  simpa [Noctium.Witness.eraseProgram] using
    Helpers.resolveWithLimits_mapDeclarationBodies limits Noctium.Witness.eraseStages
      program scope name arguments span sourceAdmitted mappedAdmitted

private theorem helperEnvironment_eraseProgram (program : Program) (context : EvalContext)
    (declaration : Declaration) (arguments : List RuntimeValue) :
    helperEnvironment (Noctium.Witness.eraseProgram program) context
      {declaration with body := Noctium.Witness.eraseStages declaration.body} arguments =
    helperEnvironment program context declaration arguments := by
  cases declaration <;> rfl

private theorem entrypoint_eraseProgram (program : Program) (entryName : String) :
    entrypoint (Noctium.Witness.eraseProgram program) entryName =
      (entrypoint program entryName).map fun (exportItem, declaration) =>
        (exportItem, {declaration with body := Noctium.Witness.eraseStages declaration.body}) := by
  unfold entrypoint Noctium.Witness.eraseProgram
  have hExports : (Helpers.mapDeclarationBodies Noctium.Witness.eraseStages program).exports =
      program.exports := rfl
  rw [hExports]
  cases hExport : program.exports.find? (·.name == entryName) with
  | none => simp [Except.map]
  | some foundEntry =>
      simp only [Helpers.mapDeclarationBodies_findDeclarationById]
      cases hDeclaration : program.declarations.find? (fun declaration => declaration.id == foundEntry.target) with
      | none => simp [hDeclaration, Except.map]
      | some declaration => rfl

private theorem executeWitnessCall_eraseProgram (program : Program) (context : EvalContext)
    (grants : HostGrants) (provider : Provider) (site name : String)
    (arguments : List RuntimeValue) :
    executeWitnessCall (Noctium.Witness.eraseProgram program) context grants provider site name arguments =
      executeWitnessCall program context grants provider site name arguments := by
  rfl

private theorem executeWitnessCallMode_eraseProgram (program : Program) (context : EvalContext)
    (provider : Provider) (site name : String) (signature : WitnessSignature)
    (arguments : List RuntimeValue) :
    executeWitnessCallMode (Noctium.Witness.eraseProgram program) context provider site name signature arguments =
      executeWitnessCallMode program context provider site name signature arguments := by
  rfl

private theorem entryEnvironment_eraseProgram (program : Program) (context : EvalContext)
    (entryName : String) (inputs : List (String × RuntimeValue)) :
    entryEnvironment (Noctium.Witness.eraseProgram program) context entryName inputs =
      entryEnvironment program context entryName inputs := by
  unfold entryEnvironment
  rw [entrypoint_eraseProgram]
  cases h : entrypoint program entryName with
  | error message =>
      simp [h, Except.map, Except.bind, Monad.toBind, Bind.bind]
  | ok result =>
      cases result with
      | mk exportItem declaration =>
          simp only [h, Except.map]
          cases declaration <;> rfl

end Noctium.Witness.Semantics

set_option pp.explicit true in
#print axioms Noctium.Witness.Semantics.evaluator_recordSafe

set_option pp.explicit true in
#print Noctium.Witness.Semantics.authorizeSignature
set_option pp.explicit true in
#print Noctium.Witness.Semantics.executeWitnessCall

namespace Noctium.Witness.Semantics

open Helpers

/-- Successful source computation replays over one frozen extension of its tape.
Private writes belong only to the source machine. -/
def SuccessSim {α : Type} (sourceComputation replayComputation : MachineM α) : Prop :=
  ∀ source replay value sourceFinal frozen,
    ReplayStateRelation frozen source replay →
    sourceComputation source = (.ok value, sourceFinal) →
    (∃ tail, frozen = sourceFinal.tape ++ tail) →
    ∃ replayFinal, replayComputation replay = (.ok value, replayFinal) ∧
      ReplayStateRelation frozen sourceFinal replayFinal ∧
      replayFinal.stagedState = replay.stagedState ∧
      replayFinal.journal = replay.journal

private theorem successSim_bind {α β : Type}
    (c d : MachineM α) (k l : α → MachineM β)
    (firstSafe : RecordSafe c) (nextSafe : ∀ value, RecordSafe (k value))
    (firstSim : SuccessSim c d) (nextSim : ∀ value, SuccessSim (k value) (l value)) :
    SuccessSim (c >>= k) (d >>= l) := by
  intro source replay value sourceFinal frozen relation sourceRun finalPrefix
  cases firstRun : c source with
  | mk firstResult middle =>
    cases firstResult with
    | error message =>
      simp [Bind.bind, firstRun] at sourceRun
    | ok initialValue =>
      have middleRecord : RecordStep source middle := by
        simpa [firstRun] using firstSafe source relation.1 relation.2.2.1
      have nextRun : k initialValue middle = (.ok value, sourceFinal) := by
        simpa [machineMMonad, Monad.toBind, Bind.bind, firstRun] using sourceRun
      have finalRecord : RecordStep middle sourceFinal := by
        simpa [nextRun] using nextSafe initialValue middle middleRecord.1 middleRecord.2.1
      have middlePrefix : ∃ tail, frozen = middle.tape ++ tail := by
        rcases finalRecord.2.2.2 with ⟨suffix, ⟨appended, _⟩⟩
        rcases finalPrefix with ⟨tail, frozenAppend⟩
        refine ⟨suffix ++ tail, ?_⟩
        rw [frozenAppend, appended, List.append_assoc]
      obtain ⟨middleReplay, replayFirst, middleRelation, middleStore, middleJournal⟩ :=
        firstSim source replay initialValue middle frozen relation firstRun middlePrefix
      obtain ⟨replayFinal, replayNext, finalRelation, finalStore, finalJournal⟩ :=
        nextSim initialValue middle middleReplay value sourceFinal frozen
          middleRelation nextRun finalPrefix
      refine ⟨replayFinal, ?_, finalRelation, finalStore.trans middleStore,
        finalJournal.trans middleJournal⟩
      simp [Bind.bind, replayFirst, replayNext]


@[simp] private theorem successSim_pure {α : Type} (value : α) :
    SuccessSim (pure value : MachineM α) (pure value : MachineM α) := by
  intro source replay returned sourceFinal frozen relation sourceRun _
  change ((Except.ok value : Except String α), source) = (.ok returned, sourceFinal) at sourceRun
  cases sourceRun
  exact ⟨replay, rfl, relation, rfl, rfl⟩

@[simp] private theorem successSim_fail {α : Type} (message : String) :
    SuccessSim (fail message : MachineM α) (fail message : MachineM α) := by
  intro source replay returned sourceFinal frozen relation sourceRun _
  change ((Except.error message : Except String α), source) = (.ok returned, sourceFinal) at sourceRun
  cases sourceRun

@[simp] private theorem successSim_liftResult {α : Type} (result : Except String α) :
    SuccessSim (liftResult result) (liftResult result) := by
  cases result with
  | ok value => exact successSim_pure value
  | error message => exact successSim_fail message


private theorem successSim_withCallPath {α : Type} (path : List DeclarationId)
    (c d : MachineM α) (simulation : SuccessSim c d) :
    SuccessSim (withCallPath path c) (withCallPath path d) := by
  intro source replay returned sourceFinal frozen relation sourceRun finalPrefix
  rcases relation with ⟨sourceMode, replayMode, sourceCursor, replayCursor,
    originalPath, replayTape, initialPrefix⟩
  have enteredRelation : ReplayStateRelation frozen
      {source with path} {replay with path} :=
    ⟨sourceMode, replayMode, sourceCursor, replayCursor, rfl, replayTape, initialPrefix⟩
  cases enteredRun : c {source with path} with
  | mk result sourceAfter =>
    cases result with
    | error message =>
      simp [withCallPath, enteredRun] at sourceRun
    | ok value =>
      simp only [withCallPath, enteredRun, Prod.mk.injEq, Except.ok.injEq] at sourceRun
      rcases sourceRun with ⟨rfl, rfl⟩
      obtain ⟨replayAfter, replayRun, finalRelation, replayStore, replayJournal⟩ :=
        simulation {source with path} {replay with path} value sourceAfter frozen
          enteredRelation enteredRun finalPrefix
      refine ⟨{replayAfter with path := replay.path}, ?_, ?_, replayStore, replayJournal⟩
      · simp [withCallPath, replayRun]
      · rcases finalRelation with ⟨finalSourceMode, finalReplayMode, finalSourceCursor,
          finalReplayCursor, _, finalReplayTape, finalPrefix⟩
        exact ⟨finalSourceMode, finalReplayMode, finalSourceCursor, finalReplayCursor,
          originalPath, finalReplayTape, finalPrefix⟩

private theorem successSim_getWithCallPath {α : Type} (id : DeclarationId)
    (sourceBody replayBody : MachineM α) (simulation : SuccessSim sourceBody replayBody) :
    SuccessSim
      (get >>= fun state => withCallPath (state.path ++ [id]) sourceBody)
      (get >>= fun state => withCallPath (state.path ++ [id]) replayBody) := by
  intro source replay value sourceFinal frozen relation sourceRun finalPrefix
  have relationOriginal := relation
  rcases relation with ⟨sourceMode, replayMode, sourceCursor, replayCursor,
    pathEq, replayTape, initialPrefix⟩
  let callPath := source.path ++ [id]
  have sourceCallRun : withCallPath callPath sourceBody source = (.ok value, sourceFinal) := by
    simpa [callPath, get, machineMMonad, Monad.toBind, Bind.bind] using sourceRun
  have enteredRelation : ReplayStateRelation frozen {source with path := callPath}
      {replay with path := callPath} := by
    exact ⟨sourceMode, replayMode, sourceCursor, replayCursor, rfl, replayTape, initialPrefix⟩
  obtain ⟨replayFinal, replayCallRun, finalRelation, storeFrame, journalFrame⟩ :=
    successSim_withCallPath callPath sourceBody replayBody simulation
      source replay value sourceFinal frozen relationOriginal sourceCallRun finalPrefix
  have replayRun :
      (get >>= fun state => withCallPath (state.path ++ [id]) replayBody) replay =
        (.ok value, replayFinal) := by
    simpa [callPath, pathEq, get, machineMMonad, Monad.toBind, Bind.bind] using replayCallRun
  exact ⟨replayFinal, replayRun, finalRelation, storeFrame, journalFrame⟩


end Noctium.Witness.Semantics

namespace Noctium.Witness.Semantics

def SuccessRelSim {α β : Type} (related : α → β → Prop)
    (c : MachineM α) (d : MachineM β) : Prop :=
  ∀ source replay value sourceFinal frozen,
    ReplayStateRelation frozen source replay →
    c source = (.ok value, sourceFinal) →
    (∃ tail, frozen = sourceFinal.tape ++ tail) →
    ∃ replayValue replayFinal, related value replayValue ∧
      d replay = (.ok replayValue, replayFinal) ∧
      ReplayStateRelation frozen sourceFinal replayFinal ∧
      replayFinal.stagedState = replay.stagedState ∧
      replayFinal.journal = replay.journal

private theorem successRelSim_bind {α β γ : Type}
    (related : α → β → Prop) (c : MachineM α) (d : MachineM β)
    (k : α → MachineM γ) (l : β → MachineM γ)
    (firstSafe : RecordSafe c) (nextSafe : ∀ value, RecordSafe (k value))
    (firstSim : SuccessRelSim related c d)
    (nextSim : ∀ x y, related x y → SuccessSim (k x) (l y)) :
    SuccessSim (c >>= k) (d >>= l) := by
  intro source replay value sourceFinal frozen relation sourceRun finalPrefix
  cases firstRun : c source with
  | mk firstResult middle =>
    cases firstResult with
    | error message =>
      simp [Bind.bind, firstRun] at sourceRun
    | ok initialValue =>
      have middleRecord : RecordStep source middle := by
        simpa [firstRun] using firstSafe source relation.1 relation.2.2.1
      have nextRun : k initialValue middle = (.ok value, sourceFinal) := by
        simpa [machineMMonad, Monad.toBind, Bind.bind, firstRun] using sourceRun
      have finalRecord : RecordStep middle sourceFinal := by
        simpa [nextRun] using nextSafe initialValue middle middleRecord.1 middleRecord.2.1
      have middlePrefix : ∃ tail, frozen = middle.tape ++ tail := by
        rcases finalRecord.2.2.2 with ⟨suffix, ⟨appended, _⟩⟩
        rcases finalPrefix with ⟨tail, frozenAppend⟩
        refine ⟨suffix ++ tail, ?_⟩
        rw [frozenAppend, appended, List.append_assoc]
      obtain ⟨relatedValue, middleReplay, relatedValues, replayFirst,
          middleRelation, middleStore, middleJournal⟩ :=
        firstSim source replay initialValue middle frozen relation firstRun middlePrefix
      obtain ⟨replayFinal, replayNext, finalRelation, finalStore, finalJournal⟩ :=
        nextSim initialValue relatedValue relatedValues middle middleReplay value sourceFinal frozen
          middleRelation nextRun finalPrefix
      refine ⟨replayFinal, ?_, finalRelation, finalStore.trans middleStore,
        finalJournal.trans middleJournal⟩
      simp [Bind.bind, replayFirst, replayNext]


end Noctium.Witness.Semantics

namespace Noctium.Witness.Semantics

open Helpers

deriving instance ReflBEq for Foreign.Curve, Foreign.Kind, Foreign.Point
deriving instance ReflBEq for Ty, Noctium.Value, Helpers.DeclarationId, Helpers.ResultType, RuntimeValue

private theorem sameRuntimeValues_refl (arguments : List RuntimeValue) :
    sameRuntimeValues arguments arguments = true := by
  induction arguments with
  | nil => rfl
  | cons head tail ih => simpa [sameRuntimeValues] using ih

private theorem sameInvocation_record (ordinal : Nat) (path : List DeclarationId)
    (site : String) (signature : WitnessSignature) (arguments : List RuntimeValue)
    (reply : WitnessReply) :
    sameInvocation ordinal path site signature arguments {
      ordinal, site, name := signature.name, path, operation := signature.operation,
      capability := signature.capability, privateKey := signature.privateKey,
      resultType := signature.result, arguments, reply} = true := by
  simp [sameInvocation, sameRuntimeValues_refl]

private theorem frozen_recorded_event_lookup (source : MachineState)
    (event : WitnessInvocation) (tail frozen : List WitnessInvocation)
    (cursor : source.cursor = source.tape.length)
    (hfrozen : frozen = (source.tape ++ [event]) ++ tail) :
    frozen[source.cursor]? = some event := by
  rw [hfrozen, cursor, List.append_assoc]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

private theorem witnessSignature_name (program : Program) (name : String)
    (signature : WitnessSignature)
    (found : Helpers.witnessSignature program name = .ok signature) :
    signature.name = name := by
  unfold Helpers.witnessSignature at found
  cases lookup : program.witnesses.find? (fun candidate => candidate.name == name) with
  | none =>
    simp only [lookup] at found
    change (Except.error _ : Except Diagnostic WitnessSignature) = .ok signature at found
    cases found
  | some candidate =>
    simp only [lookup] at found
    change Except.ok candidate = Except.ok signature at found
    cases found
    have matched : (signature.name == name) = true :=
      List.find?_some (p := fun (candidate : WitnessSignature) => candidate.name == name) lookup
    exact eq_of_beq matched


private theorem sameInvocation_actual_record (program : Program)
    (name : String) (signature : WitnessSignature)
    (found : Helpers.witnessSignature program name = .ok signature)
    (ordinal : Nat) (path : List DeclarationId) (site : String)
    (arguments : List RuntimeValue) (reply : WitnessReply) :
    sameInvocation ordinal path site signature arguments {
      ordinal, site, name, path, operation := signature.operation,
      capability := signature.capability, privateKey := signature.privateKey,
      resultType := signature.result, arguments, reply} = true := by
  have matchingName := witnessSignature_name program name signature found
  subst name
  exact sameInvocation_record ordinal path site signature arguments reply


end Noctium.Witness.Semantics

namespace Noctium.Witness.Semantics

open Helpers

private theorem recordWitnessCall_success (program : Program) (context : EvalContext)
    (provider : Provider) (site name : String) (signature : WitnessSignature)
    (arguments : List RuntimeValue) (state : MachineState) (rawReply : WitnessReply)
    (providerOk : providerReply provider signature {
      name := signature.name, operation := signature.operation, capability := signature.capability,
      privateKey := signature.privateKey, stagedState := state.stagedState, arguments} = .ok rawReply)
    (providerValid : ∀ value, rawReply = .value value →
      runtimeMatches program context signature.result value = true) :
    let event : WitnessInvocation := WitnessInvocation.mk state.cursor site name state.path
      signature.operation signature.capability signature.privateKey signature.result arguments
      (normalizedReply program context signature rawReply);
    (recordWitnessCall program context provider site name signature arguments state) state =
      (witnessValue program context signature (normalizedReply program context signature rawReply))
        {state with tape := state.tape ++ [event], cursor := state.cursor + 1} := by
  cases rawReply with
  | failure message =>
      simp [recordWitnessCall, sourceProviderReply, providerReplyState, providerOk,
        recordEvent, modify, liftResult, witnessValue, machineMMonad, Monad.toBind, Bind.bind]
  | value value =>
      have valid := providerValid value rfl
      simp [recordWitnessCall, sourceProviderReply, providerReplyState, providerOk, valid,
        recordEvent, modify, liftResult, witnessValue, machineMMonad, Monad.toBind, Bind.bind]

end Noctium.Witness.Semantics

namespace Noctium.Witness.Semantics

open Helpers

private theorem review_relation_consume (frozen : List WitnessInvocation)
    (source replay : MachineState) (event : WitnessInvocation)
    (relation : ReplayStateRelation frozen source replay)
    (frozenPrefix : ∃ tail, frozen = (source.tape ++ [event]) ++ tail) :
    ReplayStateRelation frozen
      {source with tape := source.tape ++ [event], cursor := source.cursor + 1}
      {replay with cursor := replay.cursor + 1} := by
  rcases relation with ⟨sourceMode, replayMode, sourceCursor, replayCursor,
    path, replayTape, _⟩
  exact ⟨sourceMode, replayMode, by simp [sourceCursor], congrArg (fun cursor => cursor + 1) replayCursor,
    path, replayTape, frozenPrefix⟩

private theorem executeWitnessCallMode_successSim (program : Program) (context : EvalContext)
    (sourceProvider replayProvider : Provider) (site name : String)
    (signature : WitnessSignature) (arguments : List RuntimeValue)
    (signatureName : signature.name = name) :
    SuccessSim
      (executeWitnessCallMode program context sourceProvider site name signature arguments)
      (executeWitnessCallMode program context replayProvider site name signature arguments) := by
  intro source replay value sourceFinal frozen relation sourceRun finalPrefix
  have relationOriginal := relation
  rcases relation with ⟨sourceMode, replayMode, sourceCursor, replayCursor,
    path, replayTape, initialPrefix⟩
  have sourceRunRecord :
      (recordWitnessCall program context sourceProvider site name signature arguments source) source =
        (.ok value, sourceFinal) := by
    simpa [executeWitnessCallMode, get, sourceMode, machineMMonad, Monad.toBind, Bind.bind] using sourceRun
  let request : ProviderRequest := {
    name := signature.name, operation := signature.operation, capability := signature.capability,
    privateKey := signature.privateKey, stagedState := source.stagedState, arguments}
  cases providerResult : providerReply sourceProvider signature request with
  | error providerError =>
      have impossible : False := by
        have resultEq := congrArg Prod.fst sourceRunRecord
        simp [recordWitnessCall, sourceProviderReply, providerResult, request, liftResult, machineMMonad,
          Monad.toBind, Bind.bind] at resultEq
      exact impossible.elim
  | ok rawReply =>
      let normalized := normalizedReply program context signature rawReply
      let event : WitnessInvocation := WitnessInvocation.mk source.cursor site name source.path
        signature.operation signature.capability signature.privateKey signature.result arguments normalized
      let sourceAfter : MachineState := {
        source with tape := source.tape ++ [event], cursor := source.cursor + 1}
      have providerValid : ∀ value, rawReply = .value value →
          runtimeMatches program context signature.result value = true := by
        intro rawValue rawEq
        subst rawReply
        by_cases valid : runtimeMatches program context signature.result rawValue = true
        · exact valid
        · have impossible := congrArg Prod.fst sourceRunRecord
          simp [recordWitnessCall, sourceProviderReply, providerReplyState, providerResult,
            request, valid, normalizedReply, recordEvent, modify, witnessValue,
            machineMMonad, Monad.toBind, Bind.bind] at impossible
          cases impossible
      have recordedStep := recordWitnessCall_success program context sourceProvider site name signature
        arguments source rawReply providerResult providerValid
      have normalizedRun :
          (witnessValue program context signature normalized) sourceAfter = (.ok value, sourceFinal) := by
        rw [recordedStep] at sourceRunRecord
        simpa [event, normalized, sourceAfter] using sourceRunRecord
      cases normalizedAgain : normalizedReply program context signature normalized with
      | failure message =>
          simp [witnessValue, normalizedAgain, fail] at normalizedRun
      | value normalizedValue =>
          simp [witnessValue, normalizedAgain] at normalizedRun
          have pairEq := Prod.mk.inj normalizedRun
          have outputEq : normalizedValue = value := by injection pairEq.1
          subst normalizedValue
          have finalStateEq : sourceFinal = sourceAfter := pairEq.2.symm
          subst sourceFinal
          rcases finalPrefix with ⟨tail, frozenAppend⟩
          have frozenEvent : frozen = (source.tape ++ [event]) ++ tail := by
            simpa [sourceAfter] using frozenAppend
          have eventAtCursor := frozen_recorded_event_lookup source event tail frozen sourceCursor frozenEvent
          have eventAtReplayCursor : replay.tape[replay.cursor]? = some event := by
            rw [replayTape, replayCursor]
            exact eventAtCursor
          have invocationMatches :
              sameInvocation replay.cursor replay.path site signature arguments event = true := by
            rw [replayCursor, path]
            subst name
            simpa [event, normalized] using
              sameInvocation_record source.cursor source.path site signature arguments normalized
          have replayRun :
              (executeWitnessCallMode program context replayProvider site name signature arguments) replay =
                (.ok value, {replay with cursor := replay.cursor + 1}) := by
            simp [executeWitnessCallMode, replayWitnessCall, get, replayMode,
              eventAtReplayCursor, invocationMatches, modify, witnessValue, normalizedAgain,
              event, normalized,
              machineMMonad, Monad.toBind, Bind.bind] <;> rfl
          have finalRelation := review_relation_consume frozen source replay event relationOriginal ⟨tail, frozenEvent⟩
          exact ⟨{replay with cursor := replay.cursor + 1}, by simpa [event, normalized, normalizedAgain] using replayRun,
            finalRelation, rfl, rfl⟩

private theorem authorizeSignature_successSim (grants : HostGrants)
    (signature : WitnessSignature) :
    SuccessSim (authorizeSignature grants signature) (authorizeSignature grants signature) := by
  intro source replay value sourceFinal frozen relation sourceRun _
  cases authorized : authorizedProvider grants signature with
  | false => simp [authorizeSignature, authorized, fail, Bind.bind] at sourceRun
  | true =>
      simp [authorizeSignature, authorized, fail, Bind.bind] at sourceRun
      cases sourceRun
      cases value
      exact ⟨replay, by simp [authorizeSignature, authorized, fail, Bind.bind,
        machineMMonad, Pure.pure],
        relation, rfl, rfl⟩

private def executeWitnessCallAfterSignature (program : Program) (context : EvalContext)
    (grants : HostGrants) (provider : Provider) (site name : String)
    (signature : WitnessSignature) (arguments : List RuntimeValue) : MachineM RuntimeValue := do
  authorizeSignature grants signature
  let coerced ← liftResult (coerceArguments program context signature.parameters arguments)
  unless validateWitnessArguments program context signature coerced do
    fail "typed witness argument binding mismatch"
  executeWitnessCallMode program context provider site name signature coerced

private def witnessSignatureBinding (name : String)
    (source replay : WitnessSignature) : Prop := source = replay ∧ source.name = name

private theorem witnessSignatureLookup_relSim (program : Program) (name : String) :
    SuccessRelSim (witnessSignatureBinding name)
      (liftResult ((Helpers.witnessSignature program name).mapError (·.message)))
      (liftResult ((Helpers.witnessSignature (Noctium.Witness.eraseProgram program) name).mapError (·.message))) := by
  intro source replay value sourceFinal frozen relation sourceRun _
  cases found : Helpers.witnessSignature program name with
  | error diagnostic =>
      unfold liftResult at sourceRun
      rw [found] at sourceRun
      simp [Except.mapError] at sourceRun
  | ok signature =>
      unfold liftResult at sourceRun
      rw [found] at sourceRun
      simp [Except.mapError] at sourceRun
      have signatureEq : signature = value := by
        exact sourceRun.1
      have finalEq : source = sourceFinal := by
        exact sourceRun.2
      subst value
      subst sourceFinal
      have signatureName := witnessSignature_name program name signature found
      refine ⟨signature, replay, ⟨rfl, signatureName⟩, ?_, relation, rfl, rfl⟩
      have sameLookup : Helpers.witnessSignature (Noctium.Witness.eraseProgram program) name =
          Helpers.witnessSignature program name := rfl
      rw [sameLookup, found]
      simp [liftResult, Except.mapError]

private theorem validateWitnessArguments_eraseProgram (program : Program) (context : EvalContext)
    (signature : WitnessSignature) (arguments : List RuntimeValue) :
    validateWitnessArguments (Noctium.Witness.eraseProgram program) context signature arguments =
      validateWitnessArguments program context signature arguments := by
  unfold validateWitnessArguments
  simp [Noctium.Witness.eraseProgram, Helpers.mapDeclarationBodies, runtimeMatches]

private theorem recordSafe_executeWitnessCallAfterSignature (program : Program)
    (context : EvalContext) (grants : HostGrants) (provider : Provider)
    (site name : String) (signature : WitnessSignature) (arguments : List RuntimeValue) :
    RecordSafe (executeWitnessCallAfterSignature program context grants provider site name signature arguments) := by
  unfold executeWitnessCallAfterSignature
  apply recordSafe_bind
  · exact recordSafe_authorizeSignature grants signature
  · intro _
    apply recordSafe_bind
    · exact recordSafe_liftResult (coerceArguments program context signature.parameters arguments)
    · intro coerced
      cases hvalid : validateWitnessArguments program context signature coerced with
      | false =>
          simp only [hvalid, Bool.false_eq_true, if_false]
          change RecordSafe (fail "typed witness argument binding mismatch")
          exact recordSafe_fail _
      | true =>
          simp only [hvalid, if_pos rfl]
          exact recordSafe_executeWitnessCallMode program context provider site name signature coerced

private theorem executeWitnessCallAfterSignature_successSim (program : Program)
    (context : EvalContext) (grants : HostGrants)
    (sourceProvider replayProvider : Provider) (site name : String)
    (signature : WitnessSignature) (arguments : List RuntimeValue)
    (signatureName : signature.name = name) :
    SuccessSim
      (executeWitnessCallAfterSignature program context grants sourceProvider site name signature arguments)
      (executeWitnessCallAfterSignature (Noctium.Witness.eraseProgram program) context grants replayProvider site name signature arguments) := by
  unfold executeWitnessCallAfterSignature
  simp only [validateWitnessArguments_eraseProgram]
  apply successSim_bind
  · exact recordSafe_authorizeSignature grants signature
  · intro _
    apply recordSafe_bind
    · exact recordSafe_liftResult (coerceArguments program context signature.parameters arguments)
    · intro coerced
      cases valid : validateWitnessArguments program context signature coerced with
      | false =>
          change RecordSafe (fail "typed witness argument binding mismatch")
          exact recordSafe_fail _
      | true =>
          simp [valid]
          exact recordSafe_executeWitnessCallMode program context sourceProvider site name signature coerced
  · exact authorizeSignature_successSim grants signature
  · intro _
    apply successSim_bind
    · exact recordSafe_liftResult (coerceArguments program context signature.parameters arguments)
    · intro coerced
      cases valid : validateWitnessArguments program context signature coerced with
      | false =>
          simp only [valid, Bool.false_eq_true, if_false]
          apply recordSafe_bind
          · exact recordSafe_fail _
          · intro _
            exact recordSafe_executeWitnessCallMode program context sourceProvider site name signature coerced
      | true =>
          simp only [valid, if_pos rfl]
          exact recordSafe_executeWitnessCallMode program context sourceProvider site name signature coerced
    · change SuccessSim
        (liftResult (coerceArguments program context signature.parameters arguments))
        (liftResult (coerceArguments program context signature.parameters arguments))
      exact successSim_liftResult _
    · intro coerced
      cases valid : validateWitnessArguments program context signature coerced with
      | false =>
          simp only [valid, Bool.false_eq_true, if_false]
          apply successSim_bind
          · exact recordSafe_fail _
          · intro _
            exact recordSafe_executeWitnessCallMode program context sourceProvider site name signature coerced
          · exact successSim_fail _
          · intro _
            simpa only [executeWitnessCallMode_eraseProgram] using
              executeWitnessCallMode_successSim program context sourceProvider replayProvider site name
                signature coerced signatureName
      | true =>
          simp [valid, eq_self_iff_true]
          simpa only [executeWitnessCallMode_eraseProgram] using
            executeWitnessCallMode_successSim program context sourceProvider replayProvider site name
              signature coerced signatureName

private theorem executeWitnessCall_successSim (program : Program) (context : EvalContext)
    (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (site name : String) (arguments : List RuntimeValue) :
    SuccessSim
      (executeWitnessCall program context grants sourceProvider site name arguments)
      (executeWitnessCall (Noctium.Witness.eraseProgram program) context grants replayProvider site name arguments) := by
  change SuccessSim
    (liftResult ((Helpers.witnessSignature program name).mapError (·.message)) >>= fun signature =>
      executeWitnessCallAfterSignature program context grants sourceProvider site name signature arguments)
    (liftResult ((Helpers.witnessSignature (Noctium.Witness.eraseProgram program) name).mapError (·.message)) >>= fun signature =>
      executeWitnessCallAfterSignature (Noctium.Witness.eraseProgram program) context grants replayProvider site name signature arguments)
  apply successRelSim_bind (witnessSignatureBinding name)
  · exact recordSafe_liftResult _
  · intro signature
    exact recordSafe_executeWitnessCallAfterSignature program context grants sourceProvider site name signature arguments
  · exact witnessSignatureLookup_relSim program name
  · intro signature replaySignature related
    rcases related with ⟨rfl, signatureName⟩
    exact executeWitnessCallAfterSignature_successSim program context grants sourceProvider replayProvider
      site name signature arguments signatureName

def ResultStable {α : Type} (computation : MachineM α) : Prop :=
  ∀ left right, (computation left).1 = (computation right).1

def ResultsStableTogether {α : Type} (left right : MachineM α) : Prop :=
  ∀ leftState rightState, (left leftState).1 = (right rightState).1

private theorem resultsStableTogether_of_frames {α : Type}
    (left right : MachineM α) (leftFrame : StatePreserving left)
    (rightFrame : StatePreserving right)
    (stable : ResultsStableTogether left right) : SuccessSim left right := by
  intro source replay value sourceFinal frozen relation sourceRun _
  have sourceFinalEq : sourceFinal = source := by
    have h := congrArg Prod.snd sourceRun
    simpa [leftFrame source] using h.symm
  subst sourceFinal
  have resultEq := stable source replay
  have replayResult : (right replay).1 = .ok value := by
    simpa [sourceRun] using resultEq.symm
  refine ⟨replay, ?_, relation, rfl, rfl⟩
  exact Prod.ext replayResult (rightFrame replay)

private theorem resultStable_bind {α β : Type} (first : MachineM α)
    (next : α → MachineM β) (firstStable : ResultStable first)
    (nextStable : ∀ value, ResultStable (next value)) :
    ResultStable (first >>= next) := by
  intro left right
  cases leftRun : first left with
  | mk leftResult leftState =>
    cases rightRun : first right with
    | mk rightResult rightState =>
      have resultEq : leftResult = rightResult := by
        have h := firstStable left right
        simpa [leftRun, rightRun] using h
      subst rightResult
      cases leftResult with
      | error message => simp [machineMMonad, Monad.toBind, Bind.bind, leftRun, rightRun]
      | ok value =>
        have h := nextStable value leftState rightState
        simpa [machineMMonad, Monad.toBind, Bind.bind, leftRun, rightRun] using h

private theorem successSim_of_frameResultStable {α : Type} (computation : MachineM α)
    (frame : StatePreserving computation) (stable : ResultStable computation) :
    SuccessSim computation computation := by
  intro source replay value sourceFinal frozen relation sourceRun _
  have sourceFrame := frame source
  have sourceResult := congrArg Prod.fst sourceRun
  have finalEq : sourceFinal = source := by
    have h := congrArg Prod.snd sourceRun
    simpa [sourceFrame] using h.symm
  subst sourceFinal
  have replayResult := stable replay source
  have replayOutput : (computation replay).1 = .ok value := by
    simpa [sourceRun] using replayResult
  refine ⟨replay, ?_, relation, rfl, rfl⟩
  exact Prod.ext replayOutput (frame replay)

@[simp] private theorem resultStable_pure {α : Type} (value : α) :
    ResultStable (pure value : MachineM α) := by intro _ _; rfl

@[simp] private theorem resultStable_fail {α : Type} (message : String) :
    ResultStable (fail message : MachineM α) := by intro _ _; rfl

@[simp] private theorem resultStable_liftResult {α : Type} (result : Except String α) :
    ResultStable (liftResult result) := by intro _ _; rfl

private theorem resultStable_if {α : Type} (condition : Bool)
    (yes no : MachineM α) (hy : ResultStable yes) (hn : ResultStable no) :
    ResultStable (if condition then yes else no) := by
  cases condition <;> simp [hy, hn]

private theorem resultStable_ite {α : Type} (condition : Prop) [Decidable condition]
    (yes no : MachineM α) (hy : ResultStable yes) (hn : ResultStable no) :
    ResultStable (if condition then yes else no) := by
  by_cases h : condition <;> simp [h, hy, hn]

private theorem resultStable_exceptMatch {α β : Type} (result : Except String α)
    (onError : String → MachineM β) (onOk : α → MachineM β)
    (herror : ∀ message, ResultStable (onError message))
    (hok : ∀ value, ResultStable (onOk value)) :
    ResultStable (match result with
      | .error message => onError message
      | .ok value => onOk value) := by
  cases result with
  | error message => exact herror message
  | ok value => exact hok value

private theorem resultStable_optionMatch {α β : Type} (result : Option α)
    (onNone : MachineM β) (onSome : α → MachineM β)
    (hnone : ResultStable onNone) (hsome : ∀ value, ResultStable (onSome value)) :
    ResultStable (match result with
      | none => onNone
      | some value => onSome value) := by
  cases result with
  | none => exact hnone
  | some value => exact hsome value

macro "result_stable" : tactic => `(tactic|
  repeat' first
  | assumption
  | rfl
  | exact resultStable_pure _
  | exact resultStable_fail _
  | exact resultStable_liftResult _
  | apply resultStable_bind
  | apply resultStable_if
  | apply resultStable_ite
  | apply resultStable_exceptMatch
  | apply resultStable_optionMatch
  | intro _
  | split
  | simp [fail, liftResult, machineMMonad, runtimeScalarOfPolicy])

private def binaryPost (context : EvalContext) (operation : ScalarPolicy.Binary)
    (values : List RuntimeValue) : MachineM RuntimeValue := do
  let some left := values[0]? | fail "binary left operand missing"
  let some right := values[1]? | fail "binary right operand missing"
  let left ← liftResult (runtimeScalar left)
  let right ← liftResult (runtimeScalar right)
  let left ← liftResult (scalarPolicyValue left)
  let right ← liftResult (scalarPolicyValue right)
  let result ← liftResult (ScalarPolicy.evaluate operation left right)
  let value := runtimeScalarOfPolicy result
  match value with
  | .scalar scalar =>
      if canonicalScalar context scalar then pure value else fail "noncanonical arithmetic result"
  | _ => fail "invalid arithmetic result"

private theorem binaryPost_frame (context : EvalContext) (operation : ScalarPolicy.Binary)
    (values : List RuntimeValue) : StatePreserving (binaryPost context operation values) := by
  intro state
  unfold binaryPost
  cases hleft : values[0]? with
  | none => simp [hleft, fail]
  | some left =>
    cases hright : values[1]? with
    | none => simp [hleft, hright, fail]
    | some right =>
      simp only [hleft, hright]
      state_preserving
      all_goals
        split
        · exact statePreserving_fail _
        · apply statePreserving_ite
          · exact statePreserving_pure _
          · exact statePreserving_fail _

private theorem binaryPost_stable (context : EvalContext) (operation : ScalarPolicy.Binary)
    (values : List RuntimeValue) : ResultStable (binaryPost context operation values) := by
  intro leftState rightState
  unfold binaryPost
  cases hleft : values[0]? with
  | none => simp [hleft, fail]
  | some left =>
    cases hright : values[1]? with
    | none => simp [hleft, hright, fail]
    | some right =>
      simp only [hleft, hright]
      result_stable
      all_goals
        split
        · exact resultStable_fail _
        · apply resultStable_ite
          · exact resultStable_pure _
          · exact resultStable_fail _

private theorem evalTerm_unit_successSim (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (scope : Nat) (environment : List (String × RuntimeValue)) :
    SuccessSim (evalTerm (fuel + 1) program context grants sourceProvider scope environment .unit)
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment .unit) := by
  simp only [evalTerm]
  exact successSim_pure RuntimeValue.unit

private theorem evalTerm_native_successSim (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (scope number : Nat) (environment : List (String × RuntimeValue)) :
    SuccessSim (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.native number))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.native number)) := by
  simp only [evalTerm]
  by_cases h : number < context.modulus
  · simp only [if_pos h]
    exact successSim_pure _
  · simp only [if_neg h]
    exact successSim_fail _

private theorem evalTerm_bool_successSim (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (scope : Nat) (value : Bool) (environment : List (String × RuntimeValue)) :
    SuccessSim (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.bool value))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.bool value)) := by
  simp only [evalTerm]
  exact successSim_pure _

private theorem evalTerm_uint_successSim (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (scope maximum number : Nat) (environment : List (String × RuntimeValue)) :
    SuccessSim (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.uint maximum number))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.uint maximum number)) := by
  simp only [evalTerm]
  by_cases h : canonicalScalar context (.uint maximum number) = true
  · simp only [if_pos h]
    exact successSim_pure _
  · simp only [if_neg h]
    exact successSim_fail _

private theorem evalTerm_ref_successSim (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (scope : Nat) (environment : List (String × RuntimeValue)) (name : String) :
    SuccessSim (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.ref name))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.ref name)) := by
  simp only [evalTerm]
  cases found : environment.lookup name with
  | some value => simp only [found]; exact successSim_pure value
  | none => simp only [found]; exact successSim_fail s!"unbound source value '{name}'"

private theorem evalTerm_cast_successSim_step (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (scope : Nat) (environment : List (String × RuntimeValue))
    (term : Term) (target : Ty)
    (termSafe : RecordSafe (evalTerm fuel program context grants sourceProvider scope environment term))
    (termSim : SuccessSim
      (evalTerm fuel program context grants sourceProvider scope environment term)
      (evalTerm fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment term)) :
    SuccessSim (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.cast target term))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.cast target term)) := by
  simp only [evalTerm]
  apply successSim_bind
  · exact termSafe
  · intro _
    exact recordSafe_liftResult _
  · exact termSim
  · intro value
    exact successSim_liftResult (castRuntime context target value)

private theorem evalTerm_binary_successSim_step (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (scope : Nat) (environment : List (String × RuntimeValue))
    (left right : Term) (operation : ScalarPolicy.Binary)
    (termsSafe : ∀ terms, RecordSafe (evalTerms fuel program context grants sourceProvider scope environment terms))
    (termsSim : ∀ terms, SuccessSim
      (evalTerms fuel program context grants sourceProvider scope environment terms)
      (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms)) :
    SuccessSim (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.binary operation left right))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.binary operation left right)) := by
  simp only [evalTerm]
  apply successSim_bind
  · exact termsSafe [left, right]
  · intro values
    exact recordSafe_ofStatePreserving _ (binaryPost_frame context operation values)
  · exact termsSim [left, right]
  · intro values
    change SuccessSim (binaryPost context operation values) (binaryPost context operation values)
    apply successSim_of_frameResultStable
    · exact binaryPost_frame context operation values
    · exact binaryPost_stable context operation values

private theorem equalityPost_resultStable (composites : Types.CompositeEnv) (context : EvalContext)
    (values : List RuntimeValue) : ResultStable (equalityPost composites context values) := by
  intro left right
  unfold equalityPost
  cases hleft : values[0]? with
  | none => simp [hleft, fail]
  | some left =>
    cases hright : values[1]? with
    | none => simp [hleft, hright, fail]
    | some right =>
      simp only [hleft, hright]
      result_stable

private theorem equalityPost_successSim (composites : Types.CompositeEnv) (context : EvalContext)
    (values : List RuntimeValue) :
    SuccessSim (equalityPost composites context values) (equalityPost composites context values) := by
  apply successSim_of_frameResultStable
  · exact equalityPost_frame composites context values
  · exact equalityPost_resultStable composites context values

private def selectPost (context : EvalContext) (values : List RuntimeValue) : MachineM RuntimeValue := do
  let some condition := values[0]? | fail "selection condition missing"
  let some yes := values[1]? | fail "selection true value missing"
  let some no := values[2]? | fail "selection false value missing"
  let condition ← liftResult (runtimeScalar condition)
  let .bool selected := condition | fail "selection condition is not Bool"
  let yesType := (runtimeTy yes).getD .native
  let noType := (runtimeTy no).getD .native
  let resultType ← liftResult (commonScalarType yesType noType)
  let yes ← liftResult (castRuntime context resultType yes)
  let no ← liftResult (castRuntime context resultType no)
  pure (if selected then yes else no)

private theorem selectPost_frame (context : EvalContext) (values : List RuntimeValue) :
    StatePreserving (selectPost context values) := by
  intro state
  unfold selectPost
  cases hcondition : values[0]? with
  | none => simp [hcondition, fail]
  | some condition =>
    cases hy : values[1]? with
    | none => simp [hcondition, hy, fail]
    | some yes =>
      cases hn : values[2]? with
      | none => simp [hcondition, hy, hn, fail]
      | some no =>
        simp only [hcondition, hy, hn]
        state_preserving

private theorem selectPost_resultStable (context : EvalContext) (values : List RuntimeValue) :
    ResultStable (selectPost context values) := by
  intro left right
  unfold selectPost
  cases hcondition : values[0]? with
  | none => simp [hcondition, fail]
  | some condition =>
    cases hy : values[1]? with
    | none => simp [hcondition, hy, fail]
    | some yes =>
      cases hn : values[2]? with
      | none => simp [hcondition, hy, hn, fail]
      | some no =>
        simp only [hcondition, hy, hn]
        result_stable

private theorem selectPost_successSim (context : EvalContext) (values : List RuntimeValue) :
    SuccessSim (selectPost context values) (selectPost context values) := by
  apply successSim_of_frameResultStable
  · exact selectPost_frame context values
  · exact selectPost_resultStable context values

private theorem evalTerm_eq_successSim_step (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (scope : Nat) (environment : List (String × RuntimeValue))
    (left right : Term)
    (termsSafe : ∀ terms, RecordSafe (evalTerms fuel program context grants sourceProvider scope environment terms))
    (termsSim : ∀ terms, SuccessSim
      (evalTerms fuel program context grants sourceProvider scope environment terms)
      (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms)) :
    SuccessSim (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.eq left right))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.eq left right)) := by
  have compositesEq : (Noctium.Witness.eraseProgram program).composites = program.composites := rfl
  simp only [evalTerm]
  apply successSim_bind
  · exact termsSafe [left, right]
  · intro values
    exact recordSafe_ofStatePreserving _ (equalityPost_frame program.composites context values)
  · exact termsSim [left, right]
  · intro values
    change SuccessSim (equalityPost program.composites context values)
      (equalityPost (Noctium.Witness.eraseProgram program).composites context values)
    rw [compositesEq]
    exact equalityPost_successSim program.composites context values

private theorem evalTerm_select_successSim_step (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (scope : Nat) (environment : List (String × RuntimeValue))
    (condition yes no : Term)
    (termsSafe : ∀ terms, RecordSafe (evalTerms fuel program context grants sourceProvider scope environment terms))
    (termsSim : ∀ terms, SuccessSim
      (evalTerms fuel program context grants sourceProvider scope environment terms)
      (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms)) :
    SuccessSim (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.select condition yes no))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.select condition yes no)) := by
  simp only [evalTerm]
  apply successSim_bind
  · exact termsSafe [condition, yes, no]
  · intro values
    exact recordSafe_ofStatePreserving _ (selectPost_frame context values)
  · exact termsSim [condition, yes, no]
  · intro values
    change SuccessSim (selectPost context values) (selectPost context values)
    exact selectPost_successSim context values

private theorem evalTerm_witnessCall_successSim_step (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants)
    (sourceProvider replayProvider : Provider) (scope : Nat)
    (environment : List (String × RuntimeValue)) (site name : String)
    (arguments : List Term)
    (termsSafe : ∀ terms, RecordSafe (evalTerms fuel program context grants sourceProvider scope environment terms))
    (termsSim : ∀ terms, SuccessSim
      (evalTerms fuel program context grants sourceProvider scope environment terms)
      (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms)) :
    SuccessSim
      (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.witnessCall site name arguments))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.witnessCall site name arguments)) := by
  simp only [evalTerm]
  apply successSim_bind
  · exact termsSafe arguments
  · intro values
    exact recordSafe_executeWitnessCall program context grants sourceProvider site name values
  · exact termsSim arguments
  · intro values
    exact executeWitnessCall_successSim program context grants sourceProvider replayProvider site name values

private def poseidonFinish (context : EvalContext) (domain left right : Nat) : MachineM RuntimeValue :=
  if domain >= context.modulus then fail "noncanonical Poseidon domain"
  else
    match context.poseidon2 domain left right with
    | .error message => fail message
    | .ok result =>
        if result < context.modulus then pure (.scalar (.native result))
        else fail "Poseidon oracle returned noncanonical output"

private theorem poseidonFinish_frame (context : EvalContext) (domain left right : Nat) :
    StatePreserving (poseidonFinish context domain left right) := by
  intro state
  by_cases hdomain : domain >= context.modulus
  · simp [poseidonFinish, hdomain, fail]
  · cases horacle : context.poseidon2 domain left right with
    | error message => simp [poseidonFinish, hdomain, horacle, fail]
    | ok result =>
        by_cases hresult : result < context.modulus
        · simp [poseidonFinish, hdomain, horacle, hresult, Pure.pure, machineMMonad]
        · simp [poseidonFinish, hdomain, horacle, hresult, fail]

private theorem poseidonFinish_resultStable (context : EvalContext) (domain left right : Nat) :
    ResultStable (poseidonFinish context domain left right) := by
  intro leftState rightState
  by_cases hdomain : domain >= context.modulus
  · simp [poseidonFinish, hdomain, fail]
  · cases horacle : context.poseidon2 domain left right with
    | error message => simp [poseidonFinish, hdomain, horacle, fail]
    | ok result =>
        by_cases hresult : result < context.modulus
        · simp [poseidonFinish, hdomain, horacle, hresult, Pure.pure, machineMMonad]
        · simp [poseidonFinish, hdomain, horacle, hresult, fail]

private def poseidonPost (context : EvalContext) (domain : Nat)
    (values : List RuntimeValue) : MachineM RuntimeValue := do
  let some left := values[0]? | fail "Poseidon left operand missing"
  let some right := values[1]? | fail "Poseidon right operand missing"
  let left ← liftResult (castRuntime context .native left)
  let right ← liftResult (castRuntime context .native right)
  let left ← liftResult (runtimeScalar left)
  let right ← liftResult (runtimeScalar right)
  let .native left := left | fail "Poseidon left operand is not Native"
  let .native right := right | fail "Poseidon right operand is not Native"
  poseidonFinish context domain left right

private theorem poseidonPost_frame (context : EvalContext) (domain : Nat)
    (values : List RuntimeValue) : StatePreserving (poseidonPost context domain values) := by
  intro state
  unfold poseidonPost
  cases hleft : values[0]? with
  | none => simp [hleft, fail]
  | some left =>
    cases hright : values[1]? with
    | none => simp [hleft, hright, fail]
    | some right =>
      simp only [hleft, hright]
      apply statePreserving_bind
      · exact statePreserving_liftResult _
      · intro leftCast
        apply statePreserving_bind
        · exact statePreserving_liftResult _
        · intro rightCast
          apply statePreserving_bind
          · exact statePreserving_liftResult _
          · intro leftScalar
            apply statePreserving_bind
            · exact statePreserving_liftResult _
            · intro rightScalar
              cases leftScalar with
              | native leftNumber =>
                  cases rightScalar with
                  | native rightNumber => exact poseidonFinish_frame context domain leftNumber rightNumber
                  | bool _ => exact statePreserving_fail _
                  | uint _ _ => exact statePreserving_fail _
                  | bytes _ _ | opaqueBytes _ | opaqueString _ | jubjubScalar _ | jubjubPoint _ _
                  | foreignBase _ _ | foreignScalar _ _ | foreignPoint _ _ => exact statePreserving_fail _
              | bool _ => exact statePreserving_fail _
              | uint _ _ => exact statePreserving_fail _
              | bytes _ _ | opaqueBytes _ | opaqueString _ | jubjubScalar _ | jubjubPoint _ _
              | foreignBase _ _ | foreignScalar _ _ | foreignPoint _ _ => exact statePreserving_fail _

private theorem poseidonPost_resultStable (context : EvalContext) (domain : Nat)
    (values : List RuntimeValue) : ResultStable (poseidonPost context domain values) := by
  intro leftState rightState
  unfold poseidonPost
  cases hleft : values[0]? with
  | none => simp [hleft, fail]
  | some left =>
    cases hright : values[1]? with
    | none => simp [hleft, hright, fail]
    | some right =>
      simp only [hleft, hright]
      apply resultStable_bind
      · exact resultStable_liftResult _
      · intro leftCast
        apply resultStable_bind
        · exact resultStable_liftResult _
        · intro rightCast
          apply resultStable_bind
          · exact resultStable_liftResult _
          · intro leftScalar
            apply resultStable_bind
            · exact resultStable_liftResult _
            · intro rightScalar
              cases leftScalar with
              | native leftNumber =>
                  cases rightScalar with
                  | native rightNumber => exact poseidonFinish_resultStable context domain leftNumber rightNumber
                  | bool _ => exact resultStable_fail _
                  | uint _ _ => exact resultStable_fail _
                  | bytes _ _ | opaqueBytes _ | opaqueString _ | jubjubScalar _ | jubjubPoint _ _
                  | foreignBase _ _ | foreignScalar _ _ | foreignPoint _ _ => exact resultStable_fail _
              | bool _ => exact resultStable_fail _
              | uint _ _ => exact resultStable_fail _
              | bytes _ _ | opaqueBytes _ | opaqueString _ | jubjubScalar _ | jubjubPoint _ _
              | foreignBase _ _ | foreignScalar _ _ | foreignPoint _ _ => exact resultStable_fail _

private theorem poseidonPost_successSim (context : EvalContext) (domain : Nat)
    (values : List RuntimeValue) : SuccessSim (poseidonPost context domain values) (poseidonPost context domain values) := by
  apply successSim_of_frameResultStable
  · exact poseidonPost_frame context domain values
  · exact poseidonPost_resultStable context domain values

private theorem evalTerm_poseidon_successSim_step (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (scope : Nat) (environment : List (String × RuntimeValue))
    (domain : Nat) (left right : Term)
    (termsSafe : ∀ terms, RecordSafe (evalTerms fuel program context grants sourceProvider scope environment terms))
    (termsSim : ∀ terms, SuccessSim
      (evalTerms fuel program context grants sourceProvider scope environment terms)
      (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms)) :
    SuccessSim
      (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.poseidon2 domain left right))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.poseidon2 domain left right)) := by
  simp only [evalTerm]
  apply successSim_bind
  · exact termsSafe [left, right]
  · intro values
    exact recordSafe_ofStatePreserving _ (poseidonPost_frame context domain values)
  · exact termsSim [left, right]
  · intro values
    change SuccessSim (poseidonPost context domain values) (poseidonPost context domain values)
    exact poseidonPost_successSim context domain values

private def projectPost (program : Program) (value : RuntimeValue)
    (projection : Types.Projection) : MachineM RuntimeValue := do
  let .aggregate type _ leaves := value | fail "aggregate projection requires a checked value"
  let (compiled, _) ← liftResult (aggregateLeaves program type value)
  let typed ← liftResult ((Types.unflattenChecked compiled leaves).mapError id)
  let selected ← liftResult ((Types.project compiled typed projection).mapError id)
  pure (fromSomeTypedValue selected)

private theorem projectPost_frame (program : Program) (value : RuntimeValue)
    (projection : Types.Projection) : StatePreserving (projectPost program value projection) := by
  intro state
  cases value with
  | unit => simp [projectPost, fail]
  | scalar scalar => simp [projectPost, fail]
  | aggregate type fingerprint leaves =>
      unfold projectPost
      state_preserving

private theorem projectPost_resultStable (program : Program) (value : RuntimeValue)
    (projection : Types.Projection) : ResultStable (projectPost program value projection) := by
  intro leftState rightState
  cases value with
  | unit => simp [projectPost, fail]
  | scalar scalar => simp [projectPost, fail]
  | aggregate type fingerprint leaves =>
      unfold projectPost
      result_stable

private theorem projectPost_eraseProgram (program : Program) (value : RuntimeValue)
    (projection : Types.Projection) :
    projectPost (Noctium.Witness.eraseProgram program) value projection = projectPost program value projection := by
  rfl

private theorem projectPost_successSim (program : Program) (value : RuntimeValue)
    (projection : Types.Projection) :
    SuccessSim (projectPost program value projection)
      (projectPost (Noctium.Witness.eraseProgram program) value projection) := by
  rw [projectPost_eraseProgram]
  apply successSim_of_frameResultStable
  · exact projectPost_frame program value projection
  · exact projectPost_resultStable program value projection

private theorem evalTerm_project_successSim_step (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (scope : Nat) (environment : List (String × RuntimeValue))
    (value : Term) (projection : Types.Projection)
    (termSafe : RecordSafe (evalTerm fuel program context grants sourceProvider scope environment value))
    (termSim : SuccessSim
      (evalTerm fuel program context grants sourceProvider scope environment value)
      (evalTerm fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment value)) :
    SuccessSim
      (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.project value projection))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.project value projection)) := by
  simp only [evalTerm]
  apply successSim_bind
  · exact termSafe
  · intro result
    exact recordSafe_ofStatePreserving _ (projectPost_frame program result projection)
  · exact termSim
  · intro result
    change SuccessSim (projectPost program result projection)
      (projectPost (Noctium.Witness.eraseProgram program) result projection)
    exact projectPost_successSim program result projection

private def indexPost (program : Program) (values : List RuntimeValue) : MachineM RuntimeValue := do
  let some parent := values[0]? | fail "aggregate index base missing"
  let some selectedIndex := values[1]? | fail "aggregate index expression missing"
  let .aggregate type _ leaves := parent | fail "dynamic index base is not an aggregate"
  let .vector length _ := type | fail "dynamic index base is not a fixed vector"
  let index ← liftResult (runtimeScalar selectedIndex)
  let position ← liftResult (scalarNumber index)
  if position >= length then fail "aggregate vector index out of bounds"
  else
    let (compiled, _) ← liftResult (aggregateLeaves program type parent)
    let typed ← liftResult ((Types.unflattenChecked compiled leaves).mapError id)
    let selected ← liftResult ((Types.project compiled typed (.vectorIndex position)).mapError id)
    pure (fromSomeTypedValue selected)

private theorem indexPost_frame (program : Program) (values : List RuntimeValue) :
    StatePreserving (indexPost program values) := by
  intro state
  unfold indexPost
  cases hparent : values[0]? with
  | none => simp [hparent, fail]
  | some parent =>
    cases hindex : values[1]? with
    | none => simp [hparent, hindex, fail]
    | some selectedIndex =>
      cases parent with
      | unit => simp [hparent, hindex, fail]
      | scalar scalar => simp [hparent, hindex, fail]
      | aggregate type fingerprint leaves =>
        cases type with
        | unit => simp [hparent, hindex, fail]
        | scalar ty => simp [hparent, hindex, fail]
        | tuple items => simp [hparent, hindex, fail]
        | «structure» id => simp [hparent, hindex, fail]
        | enumeration id => simp [hparent, hindex, fail]
        | bytes length => simp [hparent, hindex, fail]
        | vector length element =>
          simp only [hparent, hindex]
          state_preserving

private theorem indexPost_resultStable (program : Program) (values : List RuntimeValue) :
    ResultStable (indexPost program values) := by
  intro leftState rightState
  unfold indexPost
  cases hparent : values[0]? with
  | none => simp [hparent, fail]
  | some parent =>
    cases hindex : values[1]? with
    | none => simp [hparent, hindex, fail]
    | some selectedIndex =>
      cases parent with
      | unit => simp [hparent, hindex, fail]
      | scalar scalar => simp [hparent, hindex, fail]
      | aggregate type fingerprint leaves =>
        cases type with
        | unit => simp [hparent, hindex, fail]
        | scalar ty => simp [hparent, hindex, fail]
        | tuple items => simp [hparent, hindex, fail]
        | «structure» id => simp [hparent, hindex, fail]
        | enumeration id => simp [hparent, hindex, fail]
        | bytes length => simp [hparent, hindex, fail]
        | vector length element =>
          simp only [hparent, hindex]
          result_stable

private theorem indexPost_eraseProgram (program : Program) (values : List RuntimeValue) :
    indexPost (Noctium.Witness.eraseProgram program) values = indexPost program values := by
  rfl

private theorem indexPost_successSim (program : Program) (values : List RuntimeValue) :
    SuccessSim (indexPost program values)
      (indexPost (Noctium.Witness.eraseProgram program) values) := by
  rw [indexPost_eraseProgram]
  apply successSim_of_frameResultStable
  · exact indexPost_frame program values
  · exact indexPost_resultStable program values

private theorem evalTerm_index_successSim_step (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (scope : Nat) (environment : List (String × RuntimeValue))
    (value index : Term)
    (termsSafe : ∀ terms, RecordSafe (evalTerms fuel program context grants sourceProvider scope environment terms))
    (termsSim : ∀ terms, SuccessSim
      (evalTerms fuel program context grants sourceProvider scope environment terms)
      (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms)) :
    SuccessSim
      (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.index value index))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.index value index)) := by
  simp only [evalTerm]
  apply successSim_bind
  · exact termsSafe [value, index]
  · intro values
    exact recordSafe_ofStatePreserving _ (indexPost_frame program values)
  · exact termsSim [value, index]
  · intro values
    change SuccessSim (indexPost program values)
      (indexPost (Noctium.Witness.eraseProgram program) values)
    exact indexPost_successSim program values

private theorem evalTerm_successSim_step (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (termSafe : ∀ scope environment term, RecordSafe
      (evalTerm fuel program context grants sourceProvider scope environment term))
    (termsSafe : ∀ scope environment terms, RecordSafe
      (evalTerms fuel program context grants sourceProvider scope environment terms))
    (termSim : ∀ scope environment term, SuccessSim
      (evalTerm fuel program context grants sourceProvider scope environment term)
      (evalTerm fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment term))
    (termsSim : ∀ scope environment terms, SuccessSim
      (evalTerms fuel program context grants sourceProvider scope environment terms)
      (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms))
    (callSim : ∀ scope environment name arguments, SuccessSim
      (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.call name arguments))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.call name arguments)))
    (compositeSim : ∀ scope environment type leaves, SuccessSim
      (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.composite type leaves))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.composite type leaves))) :
    ∀ scope environment term, SuccessSim
      (evalTerm (fuel + 1) program context grants sourceProvider scope environment term)
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment term) := by
  intro scope environment term
  cases term with
  | unit => exact evalTerm_unit_successSim fuel program context grants sourceProvider replayProvider scope environment
  | native number => exact evalTerm_native_successSim fuel program context grants sourceProvider replayProvider scope number environment
  | bool value => exact evalTerm_bool_successSim fuel program context grants sourceProvider replayProvider scope value environment
  | uint maximum number => exact evalTerm_uint_successSim fuel program context grants sourceProvider replayProvider scope maximum number environment
  | ref name => exact evalTerm_ref_successSim fuel program context grants sourceProvider replayProvider scope environment name
  | binary operation left right =>
      exact evalTerm_binary_successSim_step fuel program context grants sourceProvider replayProvider scope environment
        left right operation (termsSafe scope environment) (termsSim scope environment)
  | eq left right =>
      exact evalTerm_eq_successSim_step fuel program context grants sourceProvider replayProvider scope environment
        left right (termsSafe scope environment) (termsSim scope environment)
  | cast target value =>
      exact evalTerm_cast_successSim_step fuel program context grants sourceProvider replayProvider scope environment
        value target (termSafe scope environment value) (termSim scope environment value)
  | disclose span value =>
      simp only [evalTerm]
      exact termSim scope environment value
  | select condition yes no =>
      exact evalTerm_select_successSim_step fuel program context grants sourceProvider replayProvider scope environment
        condition yes no (termsSafe scope environment) (termsSim scope environment)
  | ite condition yes no =>
      simp only [evalTerm]
      exact successSim_fail _
  | andThen left right =>
      simp only [evalTerm]
      exact successSim_fail _
  | orElse left right =>
      simp only [evalTerm]
      exact successSim_fail _
  | witness name type =>
      simp only [evalTerm]
      exact successSim_fail _
  | witnessCall site name arguments =>
      exact evalTerm_witnessCall_successSim_step fuel program context grants sourceProvider replayProvider
        scope environment site name arguments (termsSafe scope environment) (termsSim scope environment)
  | poseidon2 domain left right =>
      exact evalTerm_poseidon_successSim_step fuel program context grants sourceProvider replayProvider scope environment
        domain left right (termsSafe scope environment) (termsSim scope environment)
  | boolAnd _ _ | boolOr _ _ | boolXor _ _ | curve _ _ | bytes _ _ | bytes32Literal _
  | foreignConstant _ _ | bytesAt _ _ =>
      simp only [evalTerm]
      exact successSim_fail _
  | call name arguments => exact callSim scope environment name arguments
  | composite type leaves => exact compositeSim scope environment type leaves
  | project value projection =>
      exact evalTerm_project_successSim_step fuel program context grants sourceProvider replayProvider scope environment
        value projection (termSafe scope environment value) (termSim scope environment value)
  | index value selectedIndex =>
      exact evalTerm_index_successSim_step fuel program context grants sourceProvider replayProvider scope environment
        value selectedIndex (termsSafe scope environment) (termsSim scope environment)
  | effect kind label result =>
      simp only [evalTerm]
      exact successSim_fail _
  | «at» span value =>
      simp only [evalTerm]
      exact termSim scope environment value

private theorem evalTerms_successSim_step (fuel : Nat) (program replayProgram : Program)
    (context : EvalContext) (grants : HostGrants)
    (sourceProvider replayProvider : Provider)
    (scope : Nat) (environment : List (String × RuntimeValue))
    (termSafe : ∀ term, RecordSafe
      (evalTerm fuel program context grants sourceProvider scope environment term))
    (termsSafe : ∀ terms, RecordSafe
      (evalTerms fuel program context grants sourceProvider scope environment terms))
    (termSim : ∀ term, SuccessSim
      (evalTerm fuel program context grants sourceProvider scope environment term)
      (evalTerm fuel replayProgram context grants replayProvider scope environment term))
    (termsSim : ∀ terms, SuccessSim
      (evalTerms fuel program context grants sourceProvider scope environment terms)
      (evalTerms fuel replayProgram context grants replayProvider scope environment terms)) :
    ∀ terms, SuccessSim
      (evalTerms (fuel + 1) program context grants sourceProvider scope environment terms)
      (evalTerms (fuel + 1) replayProgram context grants replayProvider scope environment terms) := by
  intro terms
  cases terms with
  | nil =>
    simp only [evalTerms]
    exact successSim_pure []
  | cons term rest =>
    simp only [evalTerms]
    apply successSim_bind
    · exact termSafe term
    · intro value
      exact recordSafe_bind _ _ (termsSafe rest) (fun values => recordSafe_pure (value :: values))
    · exact termSim term
    · intro value
      apply successSim_bind
      · exact termsSafe rest
      · intro values
        exact recordSafe_pure (value :: values)
      · exact termsSim rest
      · intro values
        exact successSim_pure (value :: values)

private theorem successSim_sourceStage (grants : HostGrants)
    (capability key : String) (value : RuntimeValue)
    (c d : MachineM RuntimeValue) (simulation : SuccessSim c d) :
    SuccessSim
      (get >>= fun state => stageContinue grants capability key value state c) d := by
  intro source replay returned sourceFinal frozen relation sourceRun finalPrefix
  have sourceMode := relation.1
  change stageContinue grants capability key value source c source =
    (.ok returned, sourceFinal) at sourceRun
  cases granted : authorizedWrite grants capability key with
  | false =>
      simp [stageContinue, sourceMode, granted, rejectBoundary, Bind.bind] at sourceRun
  | true =>
      let written : MachineState := {source with
        stagedState := writeState source.stagedState key value,
        journal := source.journal ++ [(key, value)]}
      have writtenRelation : ReplayStateRelation frozen written replay := by
        rcases relation with ⟨sourceMode, replayMode, sourceCursor, replayCursor,
          path, replayTape, initialPrefix⟩
        exact ⟨sourceMode, replayMode, sourceCursor, replayCursor,
          path, replayTape, initialPrefix⟩
      have continuationRun : c written = (.ok returned, sourceFinal) := by
        simpa [stageContinue, sourceMode, granted, modify, Bind.bind, written] using sourceRun
      exact simulation written replay returned sourceFinal frozen
        writtenRelation continuationRun finalPrefix

private theorem successSim_stageCast (context : EvalContext) (type : Ty)
    (value : RuntimeValue) (next : RuntimeValue → MachineM RuntimeValue)
    (replay : MachineM RuntimeValue)
    (simulation : ∀ castValue,
      castRuntime context type value = .ok castValue → SuccessSim (next castValue) replay) :
    SuccessSim (stageCast context type value >>= next) replay := by
  cases castResult : castRuntime context type value with
  | error message =>
      intro source replayState returned sourceFinal frozen relation sourceRun _
      simp [stageCast, castResult, rejectBoundary, Bind.bind] at sourceRun
  | ok castValue =>
      intro source replayState returned sourceFinal frozen relation sourceRun finalPrefix
      simp [stageCast, castResult, machineMMonad, Monad.toBind, Bind.bind] at sourceRun
      exact simulation castValue castResult source replayState returned sourceFinal frozen
        relation sourceRun finalPrefix

private theorem successSim_liftResult_left {α β : Type} (result : Except String α)
    (k : α → MachineM β) (d : MachineM β)
    (simulation : ∀ value, result = .ok value → SuccessSim (k value) d) :
    SuccessSim (liftResult result >>= k) d := by
  cases result with
  | error message =>
      intro source replay returned sourceFinal frozen relation sourceRun _
      change ((Except.error message : Except String β), source) =
        (.ok returned, sourceFinal) at sourceRun
      cases sourceRun
  | ok value =>
      intro source replay returned sourceFinal frozen relation sourceRun finalPrefix
      change k value source = (.ok returned, sourceFinal) at sourceRun
      exact simulation value rfl source replay returned sourceFinal frozen
        relation sourceRun finalPrefix

end Noctium.Witness.Semantics

namespace Noctium.Witness.Semantics
open Helpers
private theorem discard_then_eq {α β : Type} (first : MachineM α) (next : MachineM β) :
    (do discard first; next) = (first >>= fun _ => next) := by
  funext state
  cases firstRun : first state with
  | mk result middle =>
    cases result <;> simp [Functor.discard, Functor.mapConst, Bind.bind, firstRun]

private theorem coerceRuntime_eraseProgram_body (program : Program) (context : EvalContext)
    (type : ResultType) (value : RuntimeValue) :
    coerceRuntime (Noctium.Witness.eraseProgram program) context type value =
      coerceRuntime program context type value := by
  rfl

private theorem evalBody_successSim_step (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (termSafe : ∀ scope environment term, RecordSafe
      (evalTerm fuel program context grants sourceProvider scope environment term))
    (bodySafe : ∀ declaration environment body, RecordSafe
      (evalBody fuel program context grants sourceProvider declaration environment body))
    (termSim : ∀ scope environment term, SuccessSim
      (evalTerm fuel program context grants sourceProvider scope environment term)
      (evalTerm fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment term))
    (bodySim : ∀ declaration environment body, SuccessSim
      (evalBody fuel program context grants sourceProvider declaration environment body)
      (evalBody fuel (Noctium.Witness.eraseProgram program) context grants replayProvider
        {declaration with body := Noctium.Witness.eraseStages declaration.body}
        environment (Noctium.Witness.eraseStages body))) :
    ∀ declaration environment body, SuccessSim
      (evalBody (fuel + 1) program context grants sourceProvider declaration environment body)
      (evalBody (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider
        {declaration with body := Noctium.Witness.eraseStages declaration.body}
        environment (Noctium.Witness.eraseStages body)) := by
  intro declaration environment body
  cases body with
  | nil =>
    simp only [evalBody, Noctium.Witness.eraseStages]
    exact successSim_pure RuntimeValue.unit
  | cons statement rest =>
    cases statement with
    | bind name type term =>
      simp only [Noctium.Witness.eraseStages, evalBody, coerceRuntime_eraseProgram_body]
      apply successSim_bind
      · exact termSafe declaration.id.scope environment term
      · intro value
        exact recordSafe_bind _ _ (recordSafe_liftResult _)
          (fun value => bodySafe declaration ((name, value) :: environment) rest)
      · exact termSim declaration.id.scope environment term
      · intro value
        apply successSim_bind
        · exact recordSafe_liftResult _
        · intro value
          exact bodySafe declaration ((name, value) :: environment) rest
        · exact successSim_liftResult _
        · intro value
          exact bodySim declaration ((name, value) :: environment) rest
    | evaluate term =>
      simp only [Noctium.Witness.eraseStages, evalBody, discard_then_eq]
      apply successSim_bind
      · exact termSafe declaration.id.scope environment term
      · intro value
        exact bodySafe declaration environment rest
      · exact termSim declaration.id.scope environment term
      · intro value
        exact bodySim declaration environment rest
    | assert term =>
      simp only [Noctium.Witness.eraseStages, evalBody]
      apply successSim_bind
      · exact termSafe declaration.id.scope environment term
      · intro value
        apply recordSafe_bind
        · exact recordSafe_liftResult _
        · intro scalar
          cases scalar with
          | bool selected => cases selected
                             · exact recordSafe_fail _
                             · exact bodySafe declaration environment rest
          | native _ => exact recordSafe_fail _
          | uint _ _ => exact recordSafe_fail _
          | bytes _ _ | opaqueBytes _ | opaqueString _ | jubjubScalar _ | jubjubPoint _ _
          | foreignBase _ _ | foreignScalar _ _ | foreignPoint _ _ => exact recordSafe_fail _
      · exact termSim declaration.id.scope environment term
      · intro value
        apply successSim_bind
        · exact recordSafe_liftResult _
        · intro scalar
          cases scalar with
          | bool selected => cases selected
                             · exact recordSafe_fail _
                             · exact bodySafe declaration environment rest
          | native _ => exact recordSafe_fail _
          | uint _ _ => exact recordSafe_fail _
          | bytes _ _ | opaqueBytes _ | opaqueString _ | jubjubScalar _ | jubjubPoint _ _
          | foreignBase _ _ | foreignScalar _ _ | foreignPoint _ _ => exact recordSafe_fail _
        · exact successSim_liftResult _
        · intro scalar
          cases scalar with
          | bool selected => cases selected
                             · exact successSim_fail _
                             · exact bodySim declaration environment rest
          | native _ => exact successSim_fail _
          | uint _ _ => exact successSim_fail _
          | bytes _ _ | opaqueBytes _ | opaqueString _ | jubjubScalar _ | jubjubPoint _ _
          | foreignBase _ _ | foreignScalar _ _ | foreignPoint _ _ => exact successSim_fail _
    | «return» term =>
      cases term with
      | none =>
          simp only [Noctium.Witness.eraseStages, evalBody, coerceRuntime_eraseProgram_body]
          exact successSim_liftResult _
      | some term =>
          simp only [Noctium.Witness.eraseStages, evalBody, coerceRuntime_eraseProgram_body]
          apply successSim_bind
          · exact termSafe declaration.id.scope environment term
          · intro value
            exact recordSafe_liftResult _
          · exact termSim declaration.id.scope environment term
          · intro value
            exact successSim_liftResult _
    | stage capability key type term =>
      simp only [Noctium.Witness.eraseStages, evalBody, discard_then_eq]
      apply successSim_bind
      · exact termSafe declaration.id.scope environment term
      · intro value
        exact recordSafe_bind _ _ (recordSafe_stageCast context type value)
          (fun value => recordSafe_getStageContinue grants capability key value _
            (bodySafe declaration environment rest))
      · exact termSim declaration.id.scope environment term
      · intro value
        apply successSim_stageCast
        intro castValue castSucceeded
        exact successSim_sourceStage grants capability key castValue _ _
          (bodySim declaration environment rest)
    | branch condition yes no =>
      simp only [Noctium.Witness.eraseStages, evalBody]
      exact successSim_fail _
    | forRange index start stop loopBody =>
      simp only [Noctium.Witness.eraseStages, evalBody]
      exact successSim_fail _
    | emitEvent kind payload =>
      simp only [Noctium.Witness.eraseStages, evalBody]
      exact successSim_fail _
    | readCell state destination ty =>
      simp only [Noctium.Witness.eraseStages, evalBody]
      exact successSim_fail _
    | writeCell state ty value =>
      simp only [Noctium.Witness.eraseStages, evalBody]
      exact successSim_fail _
    | readMap state destination keyTy valueTy key =>
      simp only [Noctium.Witness.eraseStages, evalBody]
      exact successSim_fail _
    | readMember state destination keyTy valueTy key =>
      simp only [Noctium.Witness.eraseStages, evalBody]
      exact successSim_fail _
    | writeMap state keyTy valueTy key value =>
      simp only [Noctium.Witness.eraseStages, evalBody]
      exact successSim_fail _

end Noctium.Witness.Semantics

namespace Noctium.Witness.Semantics
open Helpers

private theorem resultStable_listForIn {α β : Type}
    (values : List α) (initial : β) (step : α → β → MachineM (ForInStep β))
    (stepStable : ∀ value accumulator, ResultStable (step value accumulator)) :
    ResultStable (forIn values initial step) := by
  induction values generalizing initial with
  | nil => simp only [List.forIn_nil]; exact resultStable_pure initial
  | cons head tail ih =>
      simp only [List.forIn_cons]
      apply resultStable_bind
      · exact stepStable head initial
      · intro result
        cases result with
        | done final => exact resultStable_pure final
        | yield next => exact ih next

private def compositePost (program : Program) (context : EvalContext)
    (type : Types.CompositeType) (compiled : Types.CompiledType)
    (values : List RuntimeValue) : MachineM RuntimeValue := do
  let expected := Helpers.sourceLeafTypes compiled.checked.value
  unless values.length == expected.length do fail "composite source leaf count mismatch"
  let mut numbers := []
  for (expectedTy, value) in expected.zip values do
    let value ← liftResult (castRuntime context expectedTy value)
    let value ← liftResult (runtimeScalar value)
    let number ← liftResult (scalarNumber value)
    numbers := numbers ++ [number]
  liftResult (makeAggregateRuntime program type numbers)

private theorem compositePost_frame (program : Program) (context : EvalContext)
    (type : Types.CompositeType) (compiled : Types.CompiledType)
    (values : List RuntimeValue) : StatePreserving (compositePost program context type compiled values) := by
  intro state
  unfold compositePost
  state_preserving

private theorem compositePost_resultsStable (program : Program) (context : EvalContext)
    (type : Types.CompositeType) (compiled : Types.CompiledType)
    (values : List RuntimeValue) :
    ResultsStableTogether (compositePost program context type compiled values)
      (compositePost program context type compiled values) := by
  change ResultStable (compositePost program context type compiled values)
  unfold compositePost
  apply resultStable_ite
  · apply resultStable_bind
    · apply resultStable_listForIn
      intro pair numbers
      cases pair with
      | mk expectedTy value => result_stable
    · intro numbers
      exact resultStable_liftResult _
  · exact resultStable_fail _

private theorem compositePost_successSim (program : Program) (context : EvalContext)
    (type : Types.CompositeType) (compiled : Types.CompiledType)
    (values : List RuntimeValue) :
    SuccessSim (compositePost program context type compiled values)
      (compositePost program context type compiled values) := by
  apply resultsStableTogether_of_frames
  · exact compositePost_frame program context type compiled values
  · exact compositePost_frame program context type compiled values
  · exact compositePost_resultsStable program context type compiled values

private theorem evalComposite_successSim (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants)
    (sourceProvider replayProvider : Provider)
    (scope : Nat) (environment : List (String × RuntimeValue))
    (type : Types.CompositeType) (leaves : List Term)
    (leavesSafe : RecordSafe
      (evalTerms fuel program context grants sourceProvider scope environment leaves))
    (leavesSim : SuccessSim
      (evalTerms fuel program context grants sourceProvider scope environment leaves)
      (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment leaves)) :
    SuccessSim
      (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.composite type leaves))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program)
        context grants replayProvider scope environment (.composite type leaves)) := by
  have compositesEq : (Noctium.Witness.eraseProgram program).composites = program.composites := rfl
  simp only [evalTerm]
  rw [compositesEq]
  apply successSim_bind
  · exact recordSafe_liftResult _
  · intro compiled
    apply recordSafe_bind
    · exact leavesSafe
    · intro values
      exact recordSafe_ofStatePreserving _
        (compositePost_frame program context type compiled values)
  · exact successSim_liftResult _
  · intro compiled
    apply successSim_bind
    · exact leavesSafe
    · intro values
      exact recordSafe_ofStatePreserving _
        (compositePost_frame program context type compiled values)
    · exact leavesSim
    · intro values
      exact compositePost_successSim program context type compiled values


end Noctium.Witness.Semantics

namespace Noctium.Witness.Semantics
open Helpers

private theorem resolveCall_eraseProgram_relSim (program : Program) (scope : Nat)
    (name : String) (arguments : List ResultType)
    (sourceAdmitted : Helpers.syntacticPreflight {} program = .ok ())
    (replayAdmitted : Helpers.syntacticPreflight {} (Noctium.Witness.eraseProgram program) = .ok ()) :
    SuccessRelSim (fun source replay =>
        replay = {source with body := Noctium.Witness.eraseStages source.body})
      (liftResult ((Helpers.resolve program scope name arguments).mapError (·.message)))
      (liftResult ((Helpers.resolve (Noctium.Witness.eraseProgram program) scope name arguments).mapError (·.message))) := by
  intro source replay target sourceFinal frozen relation sourceRun _
  cases resolved : Helpers.resolve program scope name arguments with
  | error diagnostic =>
      simp [liftResult, resolved] at sourceRun
      cases sourceRun.1
  | ok declaration =>
      have mappedResolved : Helpers.resolve (Noctium.Witness.eraseProgram program)
          scope name arguments = .ok
            {declaration with body := Noctium.Witness.eraseStages declaration.body} := by
        have h := resolve_eraseProgram {} program scope name arguments {}
          sourceAdmitted replayAdmitted
        change Helpers.resolve (Noctium.Witness.eraseProgram program) scope name arguments =
          (Helpers.resolve program scope name arguments).map
            (fun value => {value with body := Noctium.Witness.eraseStages value.body}) at h
        rw [resolved] at h
        simp only [Except.map] at h
        exact h
      have sourcePair : ((Except.ok declaration : Except String Declaration), source) =
          ((Except.ok target : Except String Declaration), sourceFinal) := by
        simpa [liftResult, resolved, Except.mapError] using sourceRun
      have targetEq : target = declaration := by
        have h := Except.ok.inj (congrArg Prod.fst sourcePair)
        exact h.symm
      have finalEq : sourceFinal = source := (congrArg Prod.snd sourcePair).symm
      subst target
      subst sourceFinal
      refine ⟨{declaration with body := Noctium.Witness.eraseStages declaration.body},
        replay, rfl, ?_, relation, rfl, rfl⟩
      simp [liftResult, mappedResolved, Except.mapError]

end Noctium.Witness.Semantics

namespace Noctium.Witness.Semantics

open Helpers

private theorem evalTerm_call_successSim_step (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants)
    (sourceProvider replayProvider : Provider) (scope : Nat)
    (environment : List (String × RuntimeValue)) (name : String) (arguments : List Term)
    (sourceAdmitted : Helpers.syntacticPreflight {} program = .ok ())
    (replayAdmitted : Helpers.syntacticPreflight {} (Noctium.Witness.eraseProgram program) = .ok ())
    (termsSafe : ∀ terms, RecordSafe
      (evalTerms fuel program context grants sourceProvider scope environment terms))
    (termsSim : ∀ terms, SuccessSim
      (evalTerms fuel program context grants sourceProvider scope environment terms)
      (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms))
    (bodySafe : ∀ declaration callEnvironment body, RecordSafe
      (evalBody fuel program context grants sourceProvider declaration callEnvironment body))
    (bodySim : ∀ declaration callEnvironment body, SuccessSim
      (evalBody fuel program context grants sourceProvider declaration callEnvironment body)
      (evalBody fuel (Noctium.Witness.eraseProgram program) context grants replayProvider
        {declaration with body := Noctium.Witness.eraseStages declaration.body}
        callEnvironment (Noctium.Witness.eraseStages body))) :
    SuccessSim
      (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.call name arguments))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program)
        context grants replayProvider scope environment (.call name arguments)) := by
  simp only [evalTerm]
  apply successSim_bind
  · exact termsSafe arguments
  · intro values
    apply recordSafe_bind
    · exact recordSafe_liftResult
        ((Helpers.resolve program scope name (values.map resultTypeOfRuntime)).mapError (·.message))
    · intro target
      apply recordSafe_bind
      · exact recordSafe_liftResult (helperEnvironment program context target values)
      · intro helperEnv
        apply recordSafe_bind
        · exact recordSafe_get
        · intro state
          exact recordSafe_withCallPath (state.path ++ [target.id])
            (evalBody fuel program context grants sourceProvider target helperEnv target.body)
            (bodySafe target helperEnv target.body)
  · exact termsSim arguments
  · intro values
    apply successRelSim_bind
      (fun sourceTarget replayTarget =>
        replayTarget = {sourceTarget with body := Noctium.Witness.eraseStages sourceTarget.body})
    · exact recordSafe_liftResult
        ((Helpers.resolve program scope name (values.map resultTypeOfRuntime)).mapError (·.message))
    · intro target
      apply recordSafe_bind
      · exact recordSafe_liftResult (helperEnvironment program context target values)
      · intro helperEnv
        apply recordSafe_bind
        · exact recordSafe_get
        · intro state
          exact recordSafe_withCallPath (state.path ++ [target.id])
            (evalBody fuel program context grants sourceProvider target helperEnv target.body)
            (bodySafe target helperEnv target.body)
    · exact resolveCall_eraseProgram_relSim program scope name
        (values.map resultTypeOfRuntime) sourceAdmitted replayAdmitted
    · intro target replayTarget targetRelated
      subst replayTarget
      have helperEnvEq := helperEnvironment_eraseProgram program context target values
      rw [helperEnvEq]
      apply successSim_bind
      · exact recordSafe_liftResult (helperEnvironment program context target values)
      · intro helperEnv
        apply recordSafe_bind
        · exact recordSafe_get
        · intro state
          exact recordSafe_withCallPath (state.path ++ [target.id])
            (evalBody fuel program context grants sourceProvider target helperEnv target.body)
            (bodySafe target helperEnv target.body)
      · exact successSim_liftResult (helperEnvironment program context target values)
      · intro helperEnv
        exact successSim_getWithCallPath target.id
          (evalBody fuel program context grants sourceProvider target helperEnv target.body)
          (evalBody fuel (Noctium.Witness.eraseProgram program) context grants replayProvider
            {target with body := Noctium.Witness.eraseStages target.body}
            helperEnv (Noctium.Witness.eraseStages target.body))
          (bodySim target helperEnv target.body)


end Noctium.Witness.Semantics

namespace Noctium.Witness.Semantics
open Helpers

private theorem evaluator_successSim_of_termRules (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (sourceAdmitted : Helpers.syntacticPreflight {} program = .ok ())
    (replayAdmitted : Helpers.syntacticPreflight {} (Noctium.Witness.eraseProgram program) = .ok ())
    (callRule : ∀ fuel
      (termSafe : ∀ scope environment term, RecordSafe
        (evalTerm fuel program context grants sourceProvider scope environment term))
      (termsSafe : ∀ scope environment terms, RecordSafe
        (evalTerms fuel program context grants sourceProvider scope environment terms))
      (bodySafe : ∀ declaration environment body, RecordSafe
        (evalBody fuel program context grants sourceProvider declaration environment body))
      (termSim : ∀ scope environment term, SuccessSim
        (evalTerm fuel program context grants sourceProvider scope environment term)
        (evalTerm fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment term))
      (termsSim : ∀ scope environment terms, SuccessSim
        (evalTerms fuel program context grants sourceProvider scope environment terms)
        (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms))
      (bodySim : ∀ declaration environment body, SuccessSim
        (evalBody fuel program context grants sourceProvider declaration environment body)
        (evalBody fuel (Noctium.Witness.eraseProgram program) context grants replayProvider
          {declaration with body := Noctium.Witness.eraseStages declaration.body}
          environment (Noctium.Witness.eraseStages body))),
      ∀ scope environment name arguments, SuccessSim
        (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.call name arguments))
        (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.call name arguments)))
    (compositeRule : ∀ fuel
      (termSafe : ∀ scope environment term, RecordSafe
        (evalTerm fuel program context grants sourceProvider scope environment term))
      (termsSafe : ∀ scope environment terms, RecordSafe
        (evalTerms fuel program context grants sourceProvider scope environment terms))
      (termSim : ∀ scope environment term, SuccessSim
        (evalTerm fuel program context grants sourceProvider scope environment term)
        (evalTerm fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment term))
      (termsSim : ∀ scope environment terms, SuccessSim
        (evalTerms fuel program context grants sourceProvider scope environment terms)
        (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms)),
      ∀ scope environment type leaves, SuccessSim
        (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.composite type leaves))
        (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.composite type leaves))) :
    ∀ fuel,
      (∀ scope environment term, SuccessSim
        (evalTerm fuel program context grants sourceProvider scope environment term)
        (evalTerm fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment term)) ∧
      (∀ scope environment terms, SuccessSim
        (evalTerms fuel program context grants sourceProvider scope environment terms)
        (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms)) ∧
      (∀ declaration environment body, SuccessSim
        (evalBody fuel program context grants sourceProvider declaration environment body)
        (evalBody fuel (Noctium.Witness.eraseProgram program) context grants replayProvider
          {declaration with body := Noctium.Witness.eraseStages declaration.body}
          environment (Noctium.Witness.eraseStages body))) := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro scope environment term
        simp only [evalTerm]
        exact successSim_fail _
      · intro scope environment terms
        cases terms with
        | nil => simp only [evalTerms]; exact successSim_pure []
        | cons term rest => simp only [evalTerms]; exact successSim_fail _
      · intro declaration environment body
        cases body with
        | nil => simp only [evalBody, Noctium.Witness.eraseStages]; exact successSim_pure RuntimeValue.unit
        | cons statement rest =>
            cases statement <;> simp only [evalBody, Noctium.Witness.eraseStages] <;> exact successSim_fail _
  | succ fuel ih =>
      have recorder := evaluator_recordSafe fuel
      have termSafe : ∀ scope environment term, RecordSafe
          (evalTerm fuel program context grants sourceProvider scope environment term) :=
        fun scope environment term => recorder.1 program context grants sourceProvider scope environment term
      have termsSafe : ∀ scope environment terms, RecordSafe
          (evalTerms fuel program context grants sourceProvider scope environment terms) :=
        fun scope environment terms => recorder.2.1 program context grants sourceProvider scope environment terms
      have bodySafe : ∀ declaration environment body, RecordSafe
          (evalBody fuel program context grants sourceProvider declaration environment body) :=
        fun declaration environment body => recorder.2.2 program context grants sourceProvider declaration environment body
      have callSim := callRule fuel termSafe termsSafe bodySafe ih.1 ih.2.1 ih.2.2
      have compositeSim := compositeRule fuel termSafe termsSafe ih.1 ih.2.1
      refine ⟨?_, ?_, ?_⟩
      · exact evalTerm_successSim_step fuel program context grants sourceProvider replayProvider
          termSafe termsSafe ih.1 ih.2.1 callSim compositeSim
      · intro scope environment terms
        exact evalTerms_successSim_step fuel program (Noctium.Witness.eraseProgram program)
          context grants sourceProvider replayProvider scope environment
          (fun term => termSafe scope environment term)
          (fun values => termsSafe scope environment values)
          (fun term => ih.1 scope environment term)
          (fun values => ih.2.1 scope environment values) terms
      · intro declaration environment body
        exact evalBody_successSim_step fuel program context grants sourceProvider replayProvider
          termSafe bodySafe ih.1 ih.2.2 declaration environment body

end Noctium.Witness.Semantics

namespace Noctium.Witness.Semantics
open Helpers

theorem eraseProgram_evaluator_successSim (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (sourceAdmitted : Helpers.syntacticPreflight {} program = .ok ())
    (replayAdmitted : Helpers.syntacticPreflight {} (Noctium.Witness.eraseProgram program) = .ok ()) :
    ∀ fuel,
      (∀ scope environment term, SuccessSim
        (evalTerm fuel program context grants sourceProvider scope environment term)
        (evalTerm fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment term)) ∧
      (∀ scope environment terms, SuccessSim
        (evalTerms fuel program context grants sourceProvider scope environment terms)
        (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms)) ∧
      (∀ declaration environment body, SuccessSim
        (evalBody fuel program context grants sourceProvider declaration environment body)
        (evalBody fuel (Noctium.Witness.eraseProgram program) context grants replayProvider
          {declaration with body := Noctium.Witness.eraseStages declaration.body}
          environment (Noctium.Witness.eraseStages body))) := by
  apply evaluator_successSim_of_termRules program context grants sourceProvider replayProvider
    sourceAdmitted replayAdmitted
  · intro fuel termSafe termsSafe bodySafe termSim termsSim bodySim scope environment name arguments
    exact evalTerm_call_successSim_step fuel program context grants sourceProvider replayProvider
      scope environment name arguments sourceAdmitted replayAdmitted
      (fun terms => termsSafe scope environment terms)
      (fun terms => termsSim scope environment terms)
      bodySafe bodySim
  · intro fuel termSafe termsSafe termSim termsSim scope environment type leaves
    exact evalComposite_successSim fuel program context grants sourceProvider replayProvider
      scope environment type leaves
      (termsSafe scope environment leaves)
      (termsSim scope environment leaves)

set_option pp.explicit true in
#print axioms eraseProgram_evaluator_successSim

end Noctium.Witness.Semantics

namespace Noctium.Witness.Semantics
open Helpers

/-- A failed source computation replays the same error against a frozen tape.
The relation deliberately leaves source private state and journals independent. -/
def FailureSim {α : Type} (sourceComputation replayComputation : MachineM α) : Prop :=
  ∀ source replay message sourceFinal frozen,
    ReplayStateRelation frozen source replay →
    source.boundaryRejections = [] →
    sourceComputation source = (.error message, sourceFinal) →
    sourceFinal.boundaryRejections = [] →
    (∃ tail, frozen = sourceFinal.tape ++ tail) →
    ∃ replayFinal, replayComputation replay = (.error message, replayFinal) ∧
      ReplayStateRelation frozen sourceFinal replayFinal ∧
      replayFinal.stagedState = replay.stagedState ∧
      replayFinal.journal = replay.journal

private theorem failureSim_bind {α β : Type}
    (first second : MachineM α) (next nextReplay : α → MachineM β)
    (firstSafe : RecordSafe first) (nextSafe : ∀ value, RecordSafe (next value))
    (firstFailure : FailureSim first second) (firstSuccess : SuccessSim first second)
    (nextFailure : ∀ value, FailureSim (next value) (nextReplay value)) :
    FailureSim (first >>= next) (second >>= nextReplay) := by
  intro source replay message sourceFinal frozen relation initialAdmitted sourceRun finalAdmitted finalPrefix
  cases firstRun : first source with
  | mk firstResult middle =>
    cases firstResult with
    | error firstMessage =>
      simp only [machineMMonad, Monad.toBind, Bind.bind, firstRun,
        Prod.mk.injEq, Except.error.injEq] at sourceRun
      rcases sourceRun with ⟨rfl, rfl⟩
      obtain ⟨replayFinal, replayRun, finalRelation, finalStore, finalJournal⟩ :=
        firstFailure source replay firstMessage middle frozen relation initialAdmitted firstRun
          finalAdmitted finalPrefix
      refine ⟨replayFinal, ?_, finalRelation, finalStore, finalJournal⟩
      simp [Bind.bind, replayRun]
    | ok value =>
      have middleRecord : RecordStep source middle := by
        simpa [firstRun] using firstSafe source relation.1 relation.2.2.1
      have nextRun : next value middle = (.error message, sourceFinal) := by
        simpa [machineMMonad, Monad.toBind, Bind.bind, firstRun] using sourceRun
      have finalRecord : RecordStep middle sourceFinal := by
        simpa [nextRun] using nextSafe value middle middleRecord.1 middleRecord.2.1
      have middlePrefix : ∃ tail, frozen = middle.tape ++ tail := by
        rcases finalRecord.2.2.2 with ⟨suffix, ⟨appended, trace⟩⟩
        rcases finalPrefix with ⟨tail, frozenAppend⟩
        refine ⟨suffix ++ tail, ?_⟩
        rw [frozenAppend, appended, List.append_assoc]
      have middleAdmitted : middle.boundaryRejections = [] := by
        rcases finalRecord.2.2.2 with ⟨_, ⟨_, ⟨rejected, rejectedAppend⟩⟩⟩
        have emptyAppend : middle.boundaryRejections ++ rejected = [] := by
          rw [← rejectedAppend]
          exact finalAdmitted
        cases rejectedBefore : middle.boundaryRejections with
        | nil => rfl
        | cons head tail => simp [rejectedBefore] at emptyAppend
      obtain ⟨middleReplay, replayFirst, middleRelation, middleStore, middleJournal⟩ :=
        firstSuccess source replay value middle frozen relation firstRun middlePrefix
      obtain ⟨replayFinal, replayNext, finalRelation, finalStore, finalJournal⟩ :=
        nextFailure value middle middleReplay message sourceFinal frozen
          middleRelation middleAdmitted nextRun finalAdmitted finalPrefix
      refine ⟨replayFinal, ?_, finalRelation, finalStore.trans middleStore,
        finalJournal.trans middleJournal⟩
      simp [Bind.bind, replayFirst, replayNext]

private theorem failureSim_fail {α : Type} (message : String) :
    FailureSim (fail message : MachineM α) (fail message) := by
  intro source replay target sourceFinal frozen relation _ sourceRun _ _
  change ((Except.error message : Except String α), source) =
    (.error target, sourceFinal) at sourceRun
  have targetEq : target = message := (Except.error.inj (congrArg Prod.fst sourceRun)).symm
  have stateEq : sourceFinal = source := (congrArg Prod.snd sourceRun).symm
  subst target
  subst sourceFinal
  exact ⟨replay, rfl, relation, rfl, rfl⟩

private theorem failureSim_pure {α : Type} (value : α) :
    FailureSim (pure value : MachineM α) (pure value) := by
  intro source replay message sourceFinal frozen relation _ sourceRun _ _
  change ((Except.ok value : Except String α), source) =
    (.error message, sourceFinal) at sourceRun
  cases sourceRun

private theorem failureSim_of_frames {α : Type} (left right : MachineM α)
    (leftFrame : StatePreserving left) (rightFrame : StatePreserving right)
    (stable : ResultsStableTogether left right) : FailureSim left right := by
  intro source replay message sourceFinal frozen relation initialAdmitted sourceRun finalAdmitted _
  have sourceFinalEq : sourceFinal = source := by
    have stateEq := congrArg Prod.snd sourceRun
    simpa [leftFrame source] using stateEq.symm
  subst sourceFinal
  have resultEq := stable source replay
  have replayResult : (right replay).1 = .error message := by
    simpa [sourceRun] using resultEq.symm
  refine ⟨replay, ?_, relation, rfl, rfl⟩
  exact Prod.ext replayResult (rightFrame replay)

private theorem failureSim_liftResult {α : Type} (result : Except String α) :
    FailureSim (liftResult result) (liftResult result) := by
  cases result with
  | error message => exact failureSim_fail message
  | ok value => exact failureSim_pure value

private theorem failureSim_liftResult_left {α β : Type} (result : Except String α)
    (k : α → MachineM β) (d : MachineM β)
    (simulation : ∀ value, result = .ok value → FailureSim (k value) d)
    (success : ∃ value, result = .ok value) :
    FailureSim (liftResult result >>= k) d := by
  cases result with
  | error message =>
      rcases success with ⟨value, impossible⟩
      cases impossible
  | ok value =>
      intro source replay message sourceFinal frozen relation initialAdmitted sourceRun finalAdmitted finalPrefix
      change k value source = (.error message, sourceFinal) at sourceRun
      exact simulation value rfl source replay message sourceFinal frozen
        relation initialAdmitted sourceRun finalAdmitted finalPrefix

private theorem failureSim_sourceStage (grants : HostGrants)
    (capability key : String) (value : RuntimeValue)
    (c d : MachineM RuntimeValue)
    (authorized : authorizedWrite grants capability key = true)
    (simulation : FailureSim c d) :
    FailureSim (get >>= fun state => stageContinue grants capability key value state c) d := by
  intro source replay message sourceFinal frozen relation initialAdmitted sourceRun finalAdmitted finalPrefix
  have sourceMode := relation.1
  let written : MachineState := {source with
    stagedState := writeState source.stagedState key value,
    journal := source.journal ++ [(key, value)]}
  have writtenRelation : ReplayStateRelation frozen written replay := by
    rcases relation with ⟨sourceMode, replayMode, sourceCursor, replayCursor,
      path, replayTape, initialPrefix⟩
    exact ⟨sourceMode, replayMode, sourceCursor, replayCursor,
      path, replayTape, initialPrefix⟩
  have continuationRun : c written = (.error message, sourceFinal) := by
    change stageContinue grants capability key value source c source =
      (.error message, sourceFinal) at sourceRun
    simpa [stageContinue, sourceMode, authorized, modify, Bind.bind, written] using sourceRun
  exact simulation written replay message sourceFinal frozen writtenRelation
    (by simpa [written] using initialAdmitted) continuationRun finalAdmitted finalPrefix

private theorem failureSim_stageContinue (grants : HostGrants)
    (capability key : String) (value : RuntimeValue)
    (c d : MachineM RuntimeValue) (simulation : FailureSim c d) :
    FailureSim (get >>= fun state => stageContinue grants capability key value state c) d := by
  intro source replay message sourceFinal frozen relation initialAdmitted sourceRun finalAdmitted finalPrefix
  cases authorized : authorizedWrite grants capability key with
  | true =>
      exact failureSim_sourceStage grants capability key value c d authorized simulation
        source replay message sourceFinal frozen relation initialAdmitted sourceRun
        finalAdmitted finalPrefix
  | false =>
      have stateEquality :
          {source with boundaryRejections := source.boundaryRejections ++ [.stageWrite]} = sourceFinal := by
        have stateEquality := congrArg Prod.snd sourceRun
        simpa [get, stageContinue, relation.1, authorized, rejectBoundary, modify,
          machineMMonad, Monad.toBind, Bind.bind] using stateEquality
      have impossibleTrace : source.boundaryRejections ++ [.stageWrite] = [] := by
        have traceEquality : source.boundaryRejections ++ [.stageWrite] = sourceFinal.boundaryRejections := by
          simpa using congrArg (fun state => state.boundaryRejections) stateEquality
        rw [traceEquality]
        exact finalAdmitted
      simp at impossibleTrace

private theorem failureSim_stageCast (context : EvalContext) (type : Ty)
    (value : RuntimeValue) (next : RuntimeValue → MachineM RuntimeValue)
    (replay : MachineM RuntimeValue)
    (simulation : ∀ castValue, castRuntime context type value = .ok castValue →
      FailureSim (next castValue) replay) :
    FailureSim (stageCast context type value >>= next) replay := by
  cases castResult : castRuntime context type value with
  | error castMessage =>
      intro source replayState message sourceFinal frozen relation initialAdmitted sourceRun finalAdmitted finalPrefix
      have stateEquality :
          {source with boundaryRejections := source.boundaryRejections ++ [.stageCast]} = sourceFinal := by
        have stateEquality := congrArg Prod.snd sourceRun
        simpa [stageCast, castResult, rejectBoundary, machineMMonad,
          Monad.toBind, Bind.bind] using stateEquality
      have impossibleTrace : source.boundaryRejections ++ [.stageCast] = [] := by
        have traceEquality : source.boundaryRejections ++ [.stageCast] = sourceFinal.boundaryRejections := by
          simpa using congrArg (fun state => state.boundaryRejections) stateEquality
        rw [traceEquality]
        exact finalAdmitted
      simp at impossibleTrace
  | ok castValue =>
      intro source replayState message sourceFinal frozen relation initialAdmitted sourceRun finalAdmitted finalPrefix
      simp [stageCast, castResult, machineMMonad, Monad.toBind, Bind.bind] at sourceRun
      exact simulation castValue castResult source replayState message sourceFinal frozen relation
        initialAdmitted sourceRun finalAdmitted finalPrefix

private theorem evalTerms_failureSim_step (fuel : Nat) (program replayProgram : Program)
    (context : EvalContext) (grants : HostGrants)
    (sourceProvider replayProvider : Provider)
    (scope : Nat) (environment : List (String × RuntimeValue))
    (termSafe : ∀ term, RecordSafe
      (evalTerm fuel program context grants sourceProvider scope environment term))
    (termsSafe : ∀ terms, RecordSafe
      (evalTerms fuel program context grants sourceProvider scope environment terms))
    (termSuccess : ∀ term, SuccessSim
      (evalTerm fuel program context grants sourceProvider scope environment term)
      (evalTerm fuel replayProgram context grants replayProvider scope environment term))
    (termsSuccess : ∀ terms, SuccessSim
      (evalTerms fuel program context grants sourceProvider scope environment terms)
      (evalTerms fuel replayProgram context grants replayProvider scope environment terms))
    (termFailure : ∀ term, FailureSim
      (evalTerm fuel program context grants sourceProvider scope environment term)
      (evalTerm fuel replayProgram context grants replayProvider scope environment term))
    (termsFailure : ∀ terms, FailureSim
      (evalTerms fuel program context grants sourceProvider scope environment terms)
      (evalTerms fuel replayProgram context grants replayProvider scope environment terms)) :
    ∀ terms, FailureSim
      (evalTerms (fuel + 1) program context grants sourceProvider scope environment terms)
      (evalTerms (fuel + 1) replayProgram context grants replayProvider scope environment terms) := by
  intro terms
  cases terms with
  | nil =>
      simp only [evalTerms]
      exact failureSim_pure []
  | cons term rest =>
      simp only [evalTerms]
      apply failureSim_bind
      · exact termSafe term
      · intro value
        exact recordSafe_bind _ _ (termsSafe rest)
          (fun values => recordSafe_pure (value :: values))
      · exact termFailure term
      · exact termSuccess term
      · intro value
        apply failureSim_bind
        · exact termsSafe rest
        · intro values
          exact recordSafe_pure (value :: values)
        · exact termsFailure rest
        · exact termsSuccess rest
        · intro values
          exact failureSim_pure (value :: values)

end Noctium.Witness.Semantics

namespace Noctium.Witness.Semantics
open Helpers

private theorem evalBody_failureSim_step (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (termSafe : ∀ scope environment term, RecordSafe
      (evalTerm fuel program context grants sourceProvider scope environment term))
    (bodySafe : ∀ declaration environment body, RecordSafe
      (evalBody fuel program context grants sourceProvider declaration environment body))
    (termSuccess : ∀ scope environment term, SuccessSim
      (evalTerm fuel program context grants sourceProvider scope environment term)
      (evalTerm fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment term))
    (termFailure : ∀ scope environment term, FailureSim
      (evalTerm fuel program context grants sourceProvider scope environment term)
      (evalTerm fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment term))
    (bodyFailure : ∀ declaration environment body, FailureSim
      (evalBody fuel program context grants sourceProvider declaration environment body)
      (evalBody fuel (Noctium.Witness.eraseProgram program) context grants replayProvider
        {declaration with body := Noctium.Witness.eraseStages declaration.body}
        environment (Noctium.Witness.eraseStages body))) :
    ∀ declaration environment body, FailureSim
      (evalBody (fuel + 1) program context grants sourceProvider declaration environment body)
      (evalBody (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider
        {declaration with body := Noctium.Witness.eraseStages declaration.body}
        environment (Noctium.Witness.eraseStages body)) := by
  intro declaration environment body
  cases body with
  | nil =>
      simp only [evalBody, Noctium.Witness.eraseStages]
      exact failureSim_pure RuntimeValue.unit
  | cons statement rest =>
    cases statement with
    | bind name type term =>
      simp only [Noctium.Witness.eraseStages, evalBody, coerceRuntime_eraseProgram_body]
      apply failureSim_bind
      · exact termSafe declaration.id.scope environment term
      · intro value
        exact recordSafe_bind _ _ (recordSafe_liftResult _)
          (fun castValue => bodySafe declaration ((name, castValue) :: environment) rest)
      · exact termFailure declaration.id.scope environment term
      · exact termSuccess declaration.id.scope environment term
      · intro value
        apply failureSim_bind
        · exact recordSafe_liftResult _
        · intro castValue
          exact bodySafe declaration ((name, castValue) :: environment) rest
        · exact failureSim_liftResult (coerceRuntime program context type value)
        · exact successSim_liftResult (coerceRuntime program context type value)
        · intro castValue
          exact bodyFailure declaration ((name, castValue) :: environment) rest
    | evaluate term =>
      simp only [Noctium.Witness.eraseStages, evalBody, discard_then_eq]
      apply failureSim_bind
      · exact termSafe declaration.id.scope environment term
      · intro _
        exact bodySafe declaration environment rest
      · exact termFailure declaration.id.scope environment term
      · exact termSuccess declaration.id.scope environment term
      · intro _
        exact bodyFailure declaration environment rest
    | assert term =>
      simp only [Noctium.Witness.eraseStages, evalBody]
      apply failureSim_bind
      · exact termSafe declaration.id.scope environment term
      · intro value
        apply recordSafe_bind
        · exact recordSafe_liftResult (runtimeScalar value)
        · intro scalar
          cases scalar with
          | bool selected => cases selected
                             · exact recordSafe_fail _
                             · exact bodySafe declaration environment rest
          | native _ => exact recordSafe_fail _
          | uint _ _ => exact recordSafe_fail _
          | bytes _ _ | opaqueBytes _ | opaqueString _ | jubjubScalar _ | jubjubPoint _ _
          | foreignBase _ _ | foreignScalar _ _ | foreignPoint _ _ => exact recordSafe_fail _
      · exact termFailure declaration.id.scope environment term
      · exact termSuccess declaration.id.scope environment term
      · intro value
        apply failureSim_bind
        · exact recordSafe_liftResult (runtimeScalar value)
        · intro scalar
          cases scalar with
          | bool selected => cases selected
                             · exact recordSafe_fail _
                             · exact bodySafe declaration environment rest
          | native _ => exact recordSafe_fail _
          | uint _ _ => exact recordSafe_fail _
          | bytes _ _ | opaqueBytes _ | opaqueString _ | jubjubScalar _ | jubjubPoint _ _
          | foreignBase _ _ | foreignScalar _ _ | foreignPoint _ _ => exact recordSafe_fail _
        · exact failureSim_liftResult (runtimeScalar value)
        · exact successSim_liftResult (runtimeScalar value)
        · intro scalar
          cases scalar with
          | bool selected => cases selected
                             · exact failureSim_fail _
                             · exact bodyFailure declaration environment rest
          | native _ => exact failureSim_fail _
          | uint _ _ => exact failureSim_fail _
          | bytes _ _ | opaqueBytes _ | opaqueString _ | jubjubScalar _ | jubjubPoint _ _
          | foreignBase _ _ | foreignScalar _ _ | foreignPoint _ _ => exact failureSim_fail _
    | «return» term =>
      cases term with
      | none =>
          simp only [Noctium.Witness.eraseStages, evalBody, coerceRuntime_eraseProgram_body]
          exact failureSim_liftResult (coerceRuntime program context declaration.result .unit)
      | some term =>
          simp only [Noctium.Witness.eraseStages, evalBody, coerceRuntime_eraseProgram_body]
          apply failureSim_bind
          · exact termSafe declaration.id.scope environment term
          · intro _
            exact recordSafe_liftResult _
          · exact termFailure declaration.id.scope environment term
          · exact termSuccess declaration.id.scope environment term
          · intro value
            exact failureSim_liftResult (coerceRuntime program context declaration.result value)
    | stage capability key type term =>
      simp only [Noctium.Witness.eraseStages, evalBody, discard_then_eq]
      intro source replay message sourceFinal frozen relation initialAdmitted sourceRun finalAdmitted finalPrefix
      let sourceContinuation : RuntimeValue → MachineM RuntimeValue := fun value => do
        let castValue ← stageCast context type value
        let state ← get
        stageContinue grants capability key castValue state
          (evalBody fuel program context grants sourceProvider declaration environment rest)
      let replayContinuation : MachineM RuntimeValue :=
        evalBody fuel (Noctium.Witness.eraseProgram program) context grants replayProvider
          {declaration with body := Noctium.Witness.eraseStages declaration.body}
          environment (Noctium.Witness.eraseStages rest)
      have sourceShape :
          (evalTerm fuel program context grants sourceProvider declaration.id.scope environment term >>= fun value =>
            stageCast context type value >>= fun castValue =>
              get >>= fun state => stageContinue grants capability key castValue state
                (evalBody fuel program context grants sourceProvider declaration environment rest)) =
          (evalTerm fuel program context grants sourceProvider declaration.id.scope environment term >>= fun value =>
            sourceContinuation value) := by
        rfl
      have replayShape :
          evalBody (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider
            {declaration with body := Noctium.Witness.eraseStages declaration.body}
            environment (Noctium.Witness.eraseStages (Statement.stage capability key type term :: rest)) =
          (evalTerm fuel (Noctium.Witness.eraseProgram program) context grants replayProvider
            declaration.id.scope environment term >>= fun _ => replayContinuation) := by
        simp [Noctium.Witness.eraseStages, evalBody, discard_then_eq, replayContinuation]
      cases termRun : evalTerm fuel program context grants sourceProvider
          declaration.id.scope environment term source with
      | mk termResult afterTerm =>
        cases termResult with
        | error termMessage =>
            have sourceRun' : ((Except.error termMessage : Except String RuntimeValue), afterTerm) =
                (.error message, sourceFinal) := by
              simpa [sourceShape, termRun, machineMMonad, Monad.toBind, Bind.bind] using sourceRun
            have messageEq : termMessage = message := by
              exact Except.error.inj (congrArg Prod.fst sourceRun')
            have finalEq : afterTerm = sourceFinal := congrArg Prod.snd sourceRun'
            subst message
            subst sourceFinal
            obtain ⟨replayFinal, replayTermRun, finalRelation, storeFrame, journalFrame⟩ :=
              termFailure declaration.id.scope environment term
                source replay termMessage afterTerm frozen relation initialAdmitted termRun
                finalAdmitted finalPrefix
            refine ⟨replayFinal, ?_, finalRelation, storeFrame, journalFrame⟩
            simpa [replayShape, replayTermRun, machineMMonad, Monad.toBind, Bind.bind]
        | ok value =>
            have sourceRun' : sourceContinuation value afterTerm = (.error message, sourceFinal) := by
              simpa [sourceShape, sourceContinuation, termRun, machineMMonad, Monad.toBind, Bind.bind] using sourceRun
            have continuationSafe : RecordSafe (sourceContinuation value) := by
              apply recordSafe_bind
              · exact recordSafe_stageCast context type value
              · intro castValue
                exact recordSafe_getStageContinue grants capability key castValue
                  (evalBody fuel program context grants sourceProvider declaration environment rest)
                  (bodySafe declaration environment rest)
            have termRecord : RecordStep source afterTerm := by
              simpa [termRun] using termSafe declaration.id.scope environment term
                source relation.1 relation.2.2.1
            have finalRecord : RecordStep afterTerm sourceFinal := by
              simpa [sourceRun'] using continuationSafe afterTerm termRecord.1 termRecord.2.1
            have intermediatePrefix : ∃ tail, frozen = afterTerm.tape ++ tail := by
              rcases finalRecord.2.2.2 with ⟨suffix, ⟨appended, _⟩⟩
              rcases finalPrefix with ⟨tail, frozenAppend⟩
              refine ⟨suffix ++ tail, ?_⟩
              rw [frozenAppend, appended, List.append_assoc]
            have intermediateAdmitted : afterTerm.boundaryRejections = [] := by
              rcases finalRecord.2.2.2 with ⟨_, ⟨_, ⟨rejected, rejectedAppend⟩⟩⟩
              have emptyAppend : afterTerm.boundaryRejections ++ rejected = [] := by
                rw [← rejectedAppend]
                exact finalAdmitted
              cases traceBefore : afterTerm.boundaryRejections with
              | nil => rfl
              | cons head tail => simp [traceBefore] at emptyAppend
            obtain ⟨replayAfterTerm, replayTermRun, intermediateRelation, termStore, termJournal⟩ :=
              termSuccess declaration.id.scope environment term source replay value afterTerm frozen
                relation termRun intermediatePrefix
            have continuationFailure : FailureSim (sourceContinuation value) replayContinuation := by
              apply failureSim_stageCast context type value
                (fun castValue => get >>= fun state => stageContinue grants capability key castValue state
                  (evalBody fuel program context grants sourceProvider declaration environment rest))
                replayContinuation
              intro castValue castSucceeded
              exact failureSim_stageContinue grants capability key castValue
                (evalBody fuel program context grants sourceProvider declaration environment rest)
                replayContinuation (bodyFailure declaration environment rest)
            obtain ⟨replayFinal, replayContinuationRun, finalRelation, storeFrame, journalFrame⟩ :=
              continuationFailure afterTerm replayAfterTerm message sourceFinal frozen
                intermediateRelation intermediateAdmitted sourceRun' finalAdmitted finalPrefix
            refine ⟨replayFinal, ?_, finalRelation, storeFrame.trans termStore,
              journalFrame.trans termJournal⟩
            simpa [replayShape, replayTermRun, replayContinuationRun,
              machineMMonad, Monad.toBind, Bind.bind]
    | branch condition yes no =>
      simp only [Noctium.Witness.eraseStages, evalBody]
      exact failureSim_fail _
    | forRange index start stop loopBody =>
      simp only [Noctium.Witness.eraseStages, evalBody]
      exact failureSim_fail _
    | emitEvent kind payload =>
      simp only [Noctium.Witness.eraseStages, evalBody]
      exact failureSim_fail _
    | readCell state destination ty =>
      simp only [Noctium.Witness.eraseStages, evalBody]
      exact failureSim_fail _
    | writeCell state ty value =>
      simp only [Noctium.Witness.eraseStages, evalBody]
      exact failureSim_fail _
    | readMap state destination keyTy valueTy key =>
      simp only [Noctium.Witness.eraseStages, evalBody]
      exact failureSim_fail _
    | readMember state destination keyTy valueTy key =>
      simp only [Noctium.Witness.eraseStages, evalBody]
      exact failureSim_fail _
    | writeMap state keyTy valueTy key value =>
      simp only [Noctium.Witness.eraseStages, evalBody]
      exact failureSim_fail _

private theorem failureSim_withCallPath {α : Type} (path : List DeclarationId)
    (c d : MachineM α) (simulation : FailureSim c d) :
    FailureSim (withCallPath path c) (withCallPath path d) := by
  intro source replay message sourceFinal frozen relation initialAdmitted sourceRun finalAdmitted finalPrefix
  rcases relation with ⟨sourceMode, replayMode, sourceCursor, replayCursor,
    originalPath, replayTape, initialPrefix⟩
  have enteredRelation : ReplayStateRelation frozen
      {source with path} {replay with path} :=
    ⟨sourceMode, replayMode, sourceCursor, replayCursor, rfl, replayTape, initialPrefix⟩
  cases enteredRun : c {source with path} with
  | mk result sourceAfter =>
    cases result with
    | ok value =>
      simp [withCallPath, enteredRun] at sourceRun
    | error errorMessage =>
      simp only [withCallPath, enteredRun, Prod.mk.injEq, Except.error.injEq] at sourceRun
      rcases sourceRun with ⟨rfl, rfl⟩
      obtain ⟨replayAfter, replayRun, finalRelation, replayStore, replayJournal⟩ :=
        simulation {source with path} {replay with path} errorMessage sourceAfter frozen
          enteredRelation initialAdmitted enteredRun finalAdmitted finalPrefix
      refine ⟨{replayAfter with path := replay.path}, ?_, ?_, replayStore, replayJournal⟩
      · simp [withCallPath, replayRun]
      · rcases finalRelation with ⟨finalSourceMode, finalReplayMode, finalSourceCursor,
          finalReplayCursor, _, finalReplayTape, finalPrefix⟩
        exact ⟨finalSourceMode, finalReplayMode, finalSourceCursor, finalReplayCursor,
          originalPath, finalReplayTape, finalPrefix⟩

private theorem failureSim_getWithCallPath {α : Type} (extraPath : List DeclarationId)
    (c d : MachineM α) (simulation : FailureSim c d) :
    FailureSim
      (get >>= fun state => withCallPath (state.path ++ extraPath) c)
      (get >>= fun state => withCallPath (state.path ++ extraPath) d) := by
  intro source replay message sourceFinal frozen relation initialAdmitted sourceRun finalAdmitted finalPrefix
  have pathEq := relation.2.2.2.2.1
  change withCallPath (source.path ++ extraPath) c source = (.error message, sourceFinal) at sourceRun
  obtain ⟨replayFinal, replayRun, finalRelation, replayStore, replayJournal⟩ :=
    failureSim_withCallPath (source.path ++ extraPath) c d simulation
      source replay message sourceFinal frozen relation initialAdmitted sourceRun finalAdmitted finalPrefix
  refine ⟨replayFinal, ?_, finalRelation, replayStore, replayJournal⟩
  change withCallPath (replay.path ++ extraPath) d replay = (.error message, replayFinal)
  rw [pathEq]
  exact replayRun


private theorem failureRelSim_bind {α γ : Type}
    (related : α → α → Prop)
    (first second : MachineM α)
    (next nextReplay : α → MachineM γ)
    (firstSafe : RecordSafe first) (nextSafe : ∀ value, RecordSafe (next value))
    (firstFailure : FailureSim first second)
    (firstSuccess : SuccessRelSim related first second)
    (nextFailure : ∀ value replayValue, related value replayValue →
      FailureSim (next value) (nextReplay replayValue)) :
    FailureSim (first >>= next) (second >>= nextReplay) := by
  intro source replay message sourceFinal frozen relation initialAdmitted sourceRun finalAdmitted finalPrefix
  cases firstRun : first source with
  | mk firstResult middle =>
    cases firstResult with
    | error firstMessage =>
      simp only [machineMMonad, Monad.toBind, Bind.bind, firstRun,
        Prod.mk.injEq, Except.error.injEq] at sourceRun
      rcases sourceRun with ⟨rfl, rfl⟩
      obtain ⟨replayFinal, replayFirst, finalRelation, finalStore, finalJournal⟩ :=
        firstFailure source replay firstMessage middle frozen relation initialAdmitted firstRun
          finalAdmitted finalPrefix
      refine ⟨replayFinal, ?_, finalRelation, finalStore, finalJournal⟩
      simp [Bind.bind, replayFirst]
    | ok value =>
      have middleRecord : RecordStep source middle := by
        simpa [firstRun] using firstSafe source relation.1 relation.2.2.1
      have nextRun : next value middle = (.error message, sourceFinal) := by
        simpa [machineMMonad, Monad.toBind, Bind.bind, firstRun] using sourceRun
      have finalRecord : RecordStep middle sourceFinal := by
        simpa [nextRun] using nextSafe value middle middleRecord.1 middleRecord.2.1
      have middlePrefix : ∃ tail, frozen = middle.tape ++ tail := by
        rcases finalRecord.2.2.2 with ⟨suffix, ⟨appended, _⟩⟩
        rcases finalPrefix with ⟨tail, frozenAppend⟩
        refine ⟨suffix ++ tail, ?_⟩
        rw [frozenAppend, appended, List.append_assoc]
      have middleAdmitted : middle.boundaryRejections = [] := by
        rcases finalRecord.2.2.2 with ⟨_, ⟨_, ⟨rejected, rejectedAppend⟩⟩⟩
        have emptyAppend : middle.boundaryRejections ++ rejected = [] := by
          rw [← rejectedAppend]
          exact finalAdmitted
        cases rejectedBefore : middle.boundaryRejections with
        | nil => rfl
        | cons head tail => simp [rejectedBefore] at emptyAppend
      obtain ⟨replayValue, middleReplay, relatedValues, replayFirst,
        middleRelation, middleStore, middleJournal⟩ :=
        firstSuccess source replay value middle frozen relation firstRun middlePrefix
      obtain ⟨replayFinal, replayNext, finalRelation, finalStore, finalJournal⟩ :=
        nextFailure value replayValue relatedValues middle middleReplay message sourceFinal frozen
          middleRelation middleAdmitted nextRun finalAdmitted finalPrefix
      refine ⟨replayFinal, ?_, finalRelation, finalStore.trans middleStore,
        finalJournal.trans middleJournal⟩
      simp [Bind.bind, replayFirst, replayNext]

private theorem mapError_error {ε ε' α : Type} (f : ε → ε') (error : ε) :
    Except.mapError f (Except.error error : Except ε α) = Except.error (f error) := rfl

private theorem mapError_ok {ε ε' α : Type} (f : ε → ε') (value : α) :
    Except.mapError f (Except.ok value : Except ε α) = Except.ok value := rfl

private theorem failureSim_resolveCall (program : Program) (scope : Nat)
    (name : String) (arguments : List ResultType)
    (sourceAdmitted : Helpers.syntacticPreflight {} program = .ok ())
    (replayAdmitted : Helpers.syntacticPreflight {} (Noctium.Witness.eraseProgram program) = .ok ()) :
    FailureSim
      (liftResult ((Helpers.resolve program scope name arguments).mapError (·.message)))
      (liftResult ((Helpers.resolve (Noctium.Witness.eraseProgram program) scope name arguments).mapError (·.message))) := by
  intro source replay message sourceFinal frozen relation initialAdmitted sourceRun finalAdmitted finalPrefix
  have mappedResolve :
      Helpers.resolve (Noctium.Witness.eraseProgram program) scope name arguments =
        (Helpers.resolve program scope name arguments).map
          (fun declaration => {declaration with body := Noctium.Witness.eraseStages declaration.body}) := by
    have h := resolve_eraseProgram {} program scope name arguments {}
      sourceAdmitted replayAdmitted
    change Helpers.resolve (Noctium.Witness.eraseProgram program) scope name arguments =
      (Helpers.resolve program scope name arguments).map
        (fun declaration => {declaration with body := Noctium.Witness.eraseStages declaration.body}) at h
    exact h
  cases resolved : Helpers.resolve program scope name arguments with
  | error diagnostic =>
    have replayResolved : Helpers.resolve (Noctium.Witness.eraseProgram program)
        scope name arguments = .error diagnostic := by
      rw [mappedResolve, resolved]
      rfl
    have sourceResolveRun :
        liftResult ((Helpers.resolve program scope name arguments).mapError (·.message)) source =
          (.error diagnostic.message, source) := by
      rw [resolved]
      unfold liftResult
      exact congrArg (fun result : Except String Declaration => (result, source))
        (mapError_error (fun x : Noctium.Diagnostic => x.message) diagnostic)
    rw [sourceResolveRun] at sourceRun
    simp only [Prod.mk.injEq, Except.error.injEq] at sourceRun
    rcases sourceRun with ⟨rfl, rfl⟩
    refine ⟨replay, ?_, relation, rfl, rfl⟩
    rw [replayResolved]
    unfold liftResult
    exact congrArg (fun result : Except String Declaration => (result, replay))
      (mapError_error (fun x : Noctium.Diagnostic => x.message) diagnostic)
  | ok declaration =>
    have sourceResolveRun :
        liftResult ((Helpers.resolve program scope name arguments).mapError (·.message)) source =
          (.ok declaration, source) := by
      rw [resolved]
      unfold liftResult
      exact congrArg (fun result : Except String Declaration => (result, source))
        (mapError_ok (fun x : Noctium.Diagnostic => x.message) declaration)
    rw [sourceResolveRun] at sourceRun
    simp only [Prod.mk.injEq] at sourceRun
    cases sourceRun.1

private theorem failureSim_callTail (program : Program) (context : EvalContext)
    (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (scope : Nat) (arguments : List RuntimeValue) (name : String)
    (sourceAdmitted : Helpers.syntacticPreflight {} program = .ok ())
    (replayAdmitted : Helpers.syntacticPreflight {} (Noctium.Witness.eraseProgram program) = .ok ())
    (bodySafe : ∀ declaration callEnvironment body, RecordSafe
      (evalBody fuel program context grants sourceProvider declaration callEnvironment body))
    (bodyFailure : ∀ declaration callEnvironment body, FailureSim
      (evalBody fuel program context grants sourceProvider declaration callEnvironment body)
      (evalBody fuel (Noctium.Witness.eraseProgram program) context grants replayProvider
        {declaration with body := Noctium.Witness.eraseStages declaration.body}
        callEnvironment (Noctium.Witness.eraseStages body))) :
    FailureSim
      (do
        let target ← liftResult ((Helpers.resolve program scope name (arguments.map resultTypeOfRuntime)).mapError (·.message))
        let helperEnv ← liftResult (helperEnvironment program context target arguments)
        let state ← get
        withCallPath (state.path ++ [target.id])
          (evalBody fuel program context grants sourceProvider target helperEnv target.body))
      (do
        let target ← liftResult ((Helpers.resolve (Noctium.Witness.eraseProgram program) scope name
          (arguments.map resultTypeOfRuntime)).mapError (·.message))
        let helperEnv ← liftResult
          (helperEnvironment (Noctium.Witness.eraseProgram program) context target arguments)
        let state ← get
        withCallPath (state.path ++ [target.id])
          (evalBody fuel (Noctium.Witness.eraseProgram program) context grants replayProvider
            target helperEnv target.body)) := by
  apply failureRelSim_bind
    (related := fun sourceTarget replayTarget =>
      replayTarget = {sourceTarget with body := Noctium.Witness.eraseStages sourceTarget.body})
  · exact recordSafe_liftResult
      ((Helpers.resolve program scope name (arguments.map resultTypeOfRuntime)).mapError (·.message))
  · intro target
    apply recordSafe_bind
    · exact recordSafe_liftResult (helperEnvironment program context target arguments)
    · intro helperEnv
      apply recordSafe_bind
      · exact recordSafe_get
      · intro state
        exact recordSafe_withCallPath (state.path ++ [target.id])
          (evalBody fuel program context grants sourceProvider target helperEnv target.body)
          (bodySafe target helperEnv target.body)
  · exact failureSim_resolveCall program scope name
      (arguments.map resultTypeOfRuntime) sourceAdmitted replayAdmitted
  · exact resolveCall_eraseProgram_relSim program scope name
      (arguments.map resultTypeOfRuntime) sourceAdmitted replayAdmitted
  · intro target replayTarget targetRelated
    subst replayTarget
    have helperEnvEq := helperEnvironment_eraseProgram program context target arguments
    apply failureSim_bind
    · exact recordSafe_liftResult (helperEnvironment program context target arguments)
    · intro helperEnv
      apply recordSafe_bind
      · exact recordSafe_get
      · intro state
        exact recordSafe_withCallPath (state.path ++ [target.id])
          (evalBody fuel program context grants sourceProvider target helperEnv target.body)
          (bodySafe target helperEnv target.body)
    · simpa [helperEnvEq] using failureSim_liftResult
        (helperEnvironment program context target arguments)
    · simpa [helperEnvEq] using successSim_liftResult
        (helperEnvironment program context target arguments)
    · intro helperEnv
      exact failureSim_getWithCallPath [target.id]
        (evalBody fuel program context grants sourceProvider target helperEnv target.body)
        (evalBody fuel (Noctium.Witness.eraseProgram program) context grants replayProvider
          {target with body := Noctium.Witness.eraseStages target.body}
          helperEnv (Noctium.Witness.eraseStages target.body))
        (bodyFailure target helperEnv target.body)

private theorem evalTerm_call_failureSim_step (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants)
    (sourceProvider replayProvider : Provider) (scope : Nat)
    (environment : List (String × RuntimeValue)) (name : String) (arguments : List Term)
    (sourceAdmitted : Helpers.syntacticPreflight {} program = .ok ())
    (replayAdmitted : Helpers.syntacticPreflight {} (Noctium.Witness.eraseProgram program) = .ok ())
    (termsSafe : ∀ terms, RecordSafe
      (evalTerms fuel program context grants sourceProvider scope environment terms))
    (termsSuccess : ∀ terms, SuccessSim
      (evalTerms fuel program context grants sourceProvider scope environment terms)
      (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms))
    (termsFailure : ∀ terms, FailureSim
      (evalTerms fuel program context grants sourceProvider scope environment terms)
      (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms))
    (bodySafe : ∀ declaration callEnvironment body, RecordSafe
      (evalBody fuel program context grants sourceProvider declaration callEnvironment body))
    (bodyFailure : ∀ declaration callEnvironment body, FailureSim
      (evalBody fuel program context grants sourceProvider declaration callEnvironment body)
      (evalBody fuel (Noctium.Witness.eraseProgram program) context grants replayProvider
        {declaration with body := Noctium.Witness.eraseStages declaration.body}
        callEnvironment (Noctium.Witness.eraseStages body))) :
    FailureSim
      (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.call name arguments))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program)
        context grants replayProvider scope environment (.call name arguments)) := by
  simp only [evalTerm]
  apply failureSim_bind
  · exact termsSafe arguments
  · intro values
    apply recordSafe_bind
    · exact recordSafe_liftResult
        ((Helpers.resolve program scope name (values.map resultTypeOfRuntime)).mapError (·.message))
    · intro target
      apply recordSafe_bind
      · exact recordSafe_liftResult (helperEnvironment program context target values)
      · intro helperEnv
        apply recordSafe_bind
        · exact recordSafe_get
        · intro state
          exact recordSafe_withCallPath (state.path ++ [target.id])
            (evalBody fuel program context grants sourceProvider target helperEnv target.body)
            (bodySafe target helperEnv target.body)
  · exact termsFailure arguments
  · exact termsSuccess arguments
  · intro values
    exact failureSim_callTail program context grants sourceProvider replayProvider
      scope values name sourceAdmitted replayAdmitted bodySafe bodyFailure





private theorem terminalProviderFailure_replays
    (program replayProgram : Program) (context : EvalContext)
    (sourceProvider replayProvider : Provider) (site name : String)
    (signature : WitnessSignature) (arguments : List RuntimeValue)
    (signatureName : signature.name = name)
    (source replay : MachineState) (message : String)
    (event : WitnessInvocation)
    (eventDefinition : event = WitnessInvocation.mk source.cursor site name source.path
      signature.operation signature.capability signature.privateKey signature.result arguments
      (.failure message))
    (frozen tail : List WitnessInvocation)
    (relation : ReplayStateRelation frozen source replay)
    (providerAccepted : providerReply sourceProvider signature {
      name := signature.name, operation := signature.operation, capability := signature.capability,
      privateKey := signature.privateKey, stagedState := source.stagedState, arguments} =
      .ok (.failure message))
    (frozenPrefix : frozen = (source.tape ++ [event]) ++ tail) :
    let sourceAfter := {source with tape := source.tape ++ [event], cursor := source.cursor + 1};
    let replayAfter := {replay with cursor := replay.cursor + 1};
    executeWitnessCallMode program context sourceProvider site name signature arguments source =
        (.error message, sourceAfter) ∧
      executeWitnessCallMode replayProgram context replayProvider site name signature arguments replay =
        (.error message, replayAfter) ∧
      ReplayStateRelation frozen sourceAfter replayAfter ∧
      replayAfter.stagedState = replay.stagedState ∧ replayAfter.journal = replay.journal := by
  dsimp only
  have relationOriginal := relation
  rcases relation with ⟨sourceMode, replayMode, sourceCursor, replayCursor,
    path, replayTape, initialPrefix⟩
  have recorded :
      recordWitnessCall program context sourceProvider site name signature arguments source source =
        (.error message, {source with tape := source.tape ++ [event], cursor := source.cursor + 1}) := by
    simp [recordWitnessCall, sourceProviderReply, providerReplyState, providerAccepted,
      recordEvent, modify, witnessValue, normalizedReply, fail, Bind.bind, eventDefinition]
  have lookup : replay.tape[replay.cursor]? = some event := by
    rw [replayTape, replayCursor]
    exact frozen_recorded_event_lookup source event tail frozen sourceCursor frozenPrefix
  have matching : sameInvocation replay.cursor replay.path site signature arguments event = true := by
    rw [eventDefinition, replayCursor, path]
    simpa only [signatureName] using
      sameInvocation_record source.cursor source.path site signature arguments (.failure message)
  have matchingRecord := matching
  rw [eventDefinition] at matchingRecord
  refine ⟨?_, ?_, review_relation_consume frozen source replay event relationOriginal
    ⟨tail, frozenPrefix⟩, rfl, rfl⟩
  · simpa [executeWitnessCallMode, get, sourceMode, Bind.bind] using recorded
  · simp [executeWitnessCallMode, get, replayMode, replayWitnessCall, lookup, matchingRecord,
      eventDefinition, normalizedReply, witnessValue, fail, modify, Bind.bind]

private theorem executeWitnessCallMode_failureSim (program replayProgram : Program)
    (context : EvalContext) (sourceProvider replayProvider : Provider)
    (site name : String) (signature : WitnessSignature) (arguments : List RuntimeValue)
    (signatureName : signature.name = name) :
    FailureSim
      (executeWitnessCallMode program context sourceProvider site name signature arguments)
      (executeWitnessCallMode replayProgram context replayProvider site name signature arguments) := by
  intro source replay message sourceFinal frozen relation initialAdmitted sourceRun finalAdmitted finalPrefix
  have sourceMode := relation.1
  have sourceRunRecord :
      recordWitnessCall program context sourceProvider site name signature arguments source source =
        (.error message, sourceFinal) := by
    simpa [executeWitnessCallMode, get, sourceMode, Bind.bind] using sourceRun
  let request : ProviderRequest := {
    name := signature.name, operation := signature.operation, capability := signature.capability,
    privateKey := signature.privateKey, stagedState := source.stagedState, arguments}
  cases providerResult : providerReply sourceProvider signature request with
  | error callbackError =>
      have resultState := congrArg Prod.snd sourceRunRecord
      have rejected := congrArg MachineState.boundaryRejections resultState
      simp [recordWitnessCall, sourceProviderReply, providerResult, request, Bind.bind,
        finalAdmitted] at rejected
  | ok rawReply =>
      cases rawReply with
      | value value =>
          cases valid : runtimeMatches program context signature.result value with
          | true =>
              have impossible := congrArg Prod.fst sourceRunRecord
              simp [recordWitnessCall, sourceProviderReply, providerReplyState, providerResult,
                request, valid, normalizedReply, recordEvent, modify, witnessValue, Bind.bind] at impossible
          | false =>
              have resultState := congrArg Prod.snd sourceRunRecord
              have rejected := congrArg MachineState.boundaryRejections resultState
              simp [recordWitnessCall, sourceProviderReply, providerReplyState, providerResult,
                request, valid, normalizedReply, recordEvent, modify, witnessValue, fail,
                Bind.bind, finalAdmitted] at rejected
      | failure providerMessage =>
          let event : WitnessInvocation := WitnessInvocation.mk source.cursor site name source.path
            signature.operation signature.capability signature.privateKey signature.result arguments
            (.failure providerMessage)
          let sourceAfter : MachineState := {
            source with tape := source.tape ++ [event], cursor := source.cursor + 1}
          have exactRecord :
              recordWitnessCall program context sourceProvider site name signature arguments source source =
                (.error providerMessage, sourceAfter) := by
            simp [recordWitnessCall, sourceProviderReply, providerReplyState, providerResult,
              request, normalizedReply, recordEvent, modify, witnessValue, fail, Bind.bind,
              event, sourceAfter]
          rw [exactRecord] at sourceRunRecord
          have matchedMessage := Except.error.inj (Prod.mk.inj sourceRunRecord).1
          have matchedState := (Prod.mk.inj sourceRunRecord).2
          subst message
          subst sourceFinal
          rcases finalPrefix with ⟨tail, frozenPrefix⟩
          obtain ⟨_, replayRun, finalRelation, frameStore, frameJournal⟩ :=
            terminalProviderFailure_replays program replayProgram context sourceProvider replayProvider
              site name signature arguments signatureName source replay providerMessage event rfl
              frozen tail relation providerResult frozenPrefix
          exact ⟨{replay with cursor := replay.cursor + 1}, replayRun, finalRelation,
            frameStore, frameJournal⟩

private theorem coerceArguments_eraseProgram_failure (program : Program) (context : EvalContext)
    (parameters : List WitnessParameter) (arguments : List RuntimeValue) :
    coerceArguments (Noctium.Witness.eraseProgram program) context parameters arguments =
      coerceArguments program context parameters arguments := by
  rfl

private theorem executeWitnessCallAfterSignature_failureSim (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (site name : String) (signature : WitnessSignature) (arguments : List RuntimeValue)
    (signatureName : signature.name = name) :
    FailureSim
      (executeWitnessCallAfterSignature program context grants sourceProvider site name signature arguments)
      (executeWitnessCallAfterSignature (Noctium.Witness.eraseProgram program) context grants
        replayProvider site name signature arguments) := by
  unfold executeWitnessCallAfterSignature
  rw [coerceArguments_eraseProgram_failure]
  simp only [validateWitnessArguments_eraseProgram]
  cases allowed : authorizedProvider grants signature with
  | false =>
      simp only [authorizeSignature, allowed, Bool.false_eq_true, ite_false]
      change FailureSim (fail "host provider capability was not granted")
        (fail "host provider capability was not granted")
      exact failureSim_fail _
  | true =>
      simp only [authorizeSignature, allowed, eq_self_iff_true, ite_true]
      cases argumentResult : coerceArguments program context signature.parameters arguments with
      | error message =>
          change FailureSim (fail message) (fail message)
          exact failureSim_fail _
      | ok coerced =>
          cases valid : validateWitnessArguments program context signature coerced with
          | false =>
              simp only [liftResult, fail, machineMMonad, Monad.toApplicative, Applicative.toPure,
                Pure.pure, Bind.bind, valid, Bool.false_eq_true, ite_false]
              change FailureSim (fail "typed witness argument binding mismatch")
                (fail "typed witness argument binding mismatch")
              exact failureSim_fail _
          | true =>
              simpa [liftResult, fail, machineMMonad, Monad.toApplicative, Applicative.toPure, Pure.pure, Bind.bind, valid] using
                (executeWitnessCallMode_failureSim program (Noctium.Witness.eraseProgram program)
                  context sourceProvider replayProvider site name signature coerced signatureName)

private theorem executeWitnessCall_failureSim (program : Program) (context : EvalContext)
    (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (site name : String) (arguments : List RuntimeValue) :
    FailureSim
      (executeWitnessCall program context grants sourceProvider site name arguments)
      (executeWitnessCall (Noctium.Witness.eraseProgram program) context grants replayProvider site name arguments) := by
  change FailureSim
    (liftResult ((Helpers.witnessSignature program name).mapError (·.message)) >>= fun signature =>
      executeWitnessCallAfterSignature program context grants sourceProvider site name signature arguments)
    (liftResult ((Helpers.witnessSignature (Noctium.Witness.eraseProgram program) name).mapError (·.message)) >>= fun signature =>
      executeWitnessCallAfterSignature (Noctium.Witness.eraseProgram program) context grants replayProvider
        site name signature arguments)
  have sameLookup : Helpers.witnessSignature (Noctium.Witness.eraseProgram program) name =
      Helpers.witnessSignature program name := rfl
  rw [sameLookup]
  cases lookup : Helpers.witnessSignature program name with
  | error diagnostic =>
      change FailureSim (fail diagnostic.message) (fail diagnostic.message)
      exact failureSim_fail _
  | ok signature =>
      change FailureSim
        (executeWitnessCallAfterSignature program context grants sourceProvider site name signature arguments)
        (executeWitnessCallAfterSignature (Noctium.Witness.eraseProgram program) context grants
          replayProvider site name signature arguments)
      exact executeWitnessCallAfterSignature_failureSim program context grants sourceProvider replayProvider
        site name signature arguments (witnessSignature_name program name signature lookup)

private theorem evalTerm_witnessCall_failureSim_step (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (scope : Nat) (environment : List (String × RuntimeValue)) (site name : String)
    (arguments : List Term)
    (termsSafe : RecordSafe (evalTerms fuel program context grants sourceProvider scope environment arguments))
    (termsSuccess : SuccessSim
      (evalTerms fuel program context grants sourceProvider scope environment arguments)
      (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment arguments))
    (termsFailure : FailureSim
      (evalTerms fuel program context grants sourceProvider scope environment arguments)
      (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment arguments)) :
    FailureSim
      (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.witnessCall site name arguments))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment
        (.witnessCall site name arguments)) := by
  simp only [evalTerm]
  apply failureSim_bind
  · exact termsSafe
  · intro values
    exact recordSafe_executeWitnessCall program context grants sourceProvider site name values
  · exact termsFailure
  · exact termsSuccess
  · intro values
    exact executeWitnessCall_failureSim program context grants sourceProvider replayProvider site name values

private theorem evalTerm_failureSim_step (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (termSafe : ∀ scope environment term, RecordSafe
      (evalTerm fuel program context grants sourceProvider scope environment term))
    (termsSafe : ∀ scope environment terms, RecordSafe
      (evalTerms fuel program context grants sourceProvider scope environment terms))
    (termSuccess : ∀ scope environment term, SuccessSim
      (evalTerm fuel program context grants sourceProvider scope environment term)
      (evalTerm fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment term))
    (termsSuccess : ∀ scope environment terms, SuccessSim
      (evalTerms fuel program context grants sourceProvider scope environment terms)
      (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms))
    (termFailure : ∀ scope environment term, FailureSim
      (evalTerm fuel program context grants sourceProvider scope environment term)
      (evalTerm fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment term))
    (termsFailure : ∀ scope environment terms, FailureSim
      (evalTerms fuel program context grants sourceProvider scope environment terms)
      (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms))
    (callFailure : ∀ scope environment name arguments, FailureSim
      (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.call name arguments))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.call name arguments)))
    (witnessCallFailure : ∀ scope environment site name arguments, FailureSim
      (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.witnessCall site name arguments))
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.witnessCall site name arguments))) :
    ∀ scope environment term, FailureSim
      (evalTerm (fuel + 1) program context grants sourceProvider scope environment term)
      (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment term) := by
  intro scope environment term
  cases term with
  | unit =>
      simp only [evalTerm]
      exact failureSim_pure RuntimeValue.unit
  | native number =>
      simp only [evalTerm]
      by_cases canonical : number < context.modulus
      · simp [canonical]
        exact failureSim_pure (RuntimeValue.scalar (Noctium.Value.native number))
      · simp [canonical]
        exact failureSim_fail "noncanonical native constant"
  | bool value =>
      simp only [evalTerm]
      exact failureSim_pure (RuntimeValue.scalar (Noctium.Value.bool value))
  | uint maximum number =>
      simp only [evalTerm]
      cases canonical : canonicalScalar context (.uint maximum number) with
      | false => simp [canonical]; exact failureSim_fail "noncanonical bounded unsigned constant"
      | true => simp [canonical]; exact failureSim_pure (RuntimeValue.scalar (Noctium.Value.uint maximum number))
  | ref name =>
      simp only [evalTerm]
      cases found : environment.lookup name with
      | some value => simp [found]; exact failureSim_pure value
      | none => simp [found]; exact failureSim_fail s!"unbound source value '{name}'"
  | binary operation left right =>
      simp only [evalTerm]
      apply failureSim_bind
      · exact termsSafe scope environment [left, right]
      · intro values
        exact recordSafe_ofStatePreserving _ (binaryPost_frame context operation values)
      · exact termsFailure scope environment [left, right]
      · exact termsSuccess scope environment [left, right]
      · intro values
        have stable : ResultsStableTogether (binaryPost context operation values)
            (binaryPost context operation values) := by
          intro sourceState replayState
          exact binaryPost_stable context operation values sourceState replayState
        exact failureSim_of_frames (binaryPost context operation values)
          (binaryPost context operation values) (binaryPost_frame context operation values)
          (binaryPost_frame context operation values) stable
  | eq left right =>
      have compositesEq : (Noctium.Witness.eraseProgram program).composites = program.composites := rfl
      simp only [evalTerm]
      apply failureSim_bind
      · exact termsSafe scope environment [left, right]
      · intro values
        exact recordSafe_ofStatePreserving _ (equalityPost_frame program.composites context values)
      · exact termsFailure scope environment [left, right]
      · exact termsSuccess scope environment [left, right]
      · intro values
        have stable : ResultsStableTogether (equalityPost program.composites context values)
            (equalityPost (Noctium.Witness.eraseProgram program).composites context values) := by
          intro sourceState replayState
          rw [compositesEq]
          exact equalityPost_resultStable program.composites context values sourceState replayState
        exact failureSim_of_frames (equalityPost program.composites context values)
          (equalityPost (Noctium.Witness.eraseProgram program).composites context values)
          (equalityPost_frame program.composites context values)
          (by rw [compositesEq]; exact equalityPost_frame program.composites context values) stable
  | cast target value =>
      simp only [evalTerm]
      apply failureSim_bind
      · exact termSafe scope environment value
      · intro _
        exact recordSafe_liftResult _
      · exact termFailure scope environment value
      · exact termSuccess scope environment value
      · intro result
        exact failureSim_liftResult (castRuntime context target result)
  | disclose span value | «at» span value =>
      simp only [evalTerm]
      exact termFailure scope environment value
  | select condition yes no =>
      simp only [evalTerm]
      apply failureSim_bind
      · exact termsSafe scope environment [condition, yes, no]
      · intro values
        exact recordSafe_ofStatePreserving _ (selectPost_frame context values)
      · exact termsFailure scope environment [condition, yes, no]
      · exact termsSuccess scope environment [condition, yes, no]
      · intro values
        have stable : ResultsStableTogether (selectPost context values)
            (selectPost context values) := by
          intro sourceState replayState
          exact selectPost_resultStable context values sourceState replayState
        exact failureSim_of_frames (selectPost context values) (selectPost context values)
          (selectPost_frame context values) (selectPost_frame context values) stable
  | ite condition yes no | andThen condition yes | orElse condition yes =>
      simp only [evalTerm]
      exact failureSim_fail "source term is outside the bounded native replay semantics"
  | witness name type =>
      simp only [evalTerm]
      exact failureSim_fail "source term is outside the bounded native replay semantics"
  | witnessCall site name arguments =>
      exact witnessCallFailure scope environment site name arguments
  | poseidon2 domain left right =>
      simp only [evalTerm]
      apply failureSim_bind
      · exact termsSafe scope environment [left, right]
      · intro values
        exact recordSafe_ofStatePreserving _ (poseidonPost_frame context domain values)
      · exact termsFailure scope environment [left, right]
      · exact termsSuccess scope environment [left, right]
      · intro values
        have stable : ResultsStableTogether (poseidonPost context domain values)
            (poseidonPost context domain values) := by
          intro sourceState replayState
          exact poseidonPost_resultStable context domain values sourceState replayState
        exact failureSim_of_frames (poseidonPost context domain values)
          (poseidonPost context domain values) (poseidonPost_frame context domain values)
          (poseidonPost_frame context domain values) stable
  | call name arguments =>
      exact callFailure scope environment name arguments
  | composite type leaves =>
      simp only [evalTerm]
      have compositesEq : (Noctium.Witness.eraseProgram program).composites = program.composites := rfl
      rw [compositesEq]
      apply failureSim_bind
      · exact recordSafe_liftResult ((Types.compileType program.composites type).mapError (·.message))
      · intro compiled
        exact recordSafe_bind _ _ (termsSafe scope environment leaves)
          (fun values => recordSafe_ofStatePreserving _ (compositePost_frame program context type compiled values))
      · exact failureSim_liftResult ((Types.compileType program.composites type).mapError (·.message))
      · exact successSim_liftResult ((Types.compileType program.composites type).mapError (·.message))
      · intro compiled
        apply failureSim_bind
        · exact termsSafe scope environment leaves
        · intro values
          exact recordSafe_ofStatePreserving _ (compositePost_frame program context type compiled values)
        · exact termsFailure scope environment leaves
        · exact termsSuccess scope environment leaves
        · intro values
          change FailureSim (compositePost program context type compiled values)
            (compositePost (Noctium.Witness.eraseProgram program) context type compiled values)
          have erasedPost : compositePost (Noctium.Witness.eraseProgram program)
              context type compiled values = compositePost program context type compiled values := rfl
          rw [erasedPost]
          have stable : ResultsStableTogether (compositePost program context type compiled values)
              (compositePost program context type compiled values) := by
            intro sourceState replayState
            exact compositePost_resultsStable program context type compiled values sourceState replayState
          exact failureSim_of_frames (compositePost program context type compiled values)
            (compositePost program context type compiled values)
            (compositePost_frame program context type compiled values)
            (compositePost_frame program context type compiled values) stable
  | project value projection =>
      simp only [evalTerm]
      apply failureSim_bind
      · exact termSafe scope environment value
      · intro result
        exact recordSafe_ofStatePreserving _ (projectPost_frame program result projection)
      · exact termFailure scope environment value
      · exact termSuccess scope environment value
      · intro result
        change FailureSim (projectPost program result projection)
          (projectPost (Noctium.Witness.eraseProgram program) result projection)
        rw [projectPost_eraseProgram]
        have stable : ResultsStableTogether (projectPost program result projection)
            (projectPost program result projection) := by
          intro sourceState replayState
          exact projectPost_resultStable program result projection sourceState replayState
        exact failureSim_of_frames (projectPost program result projection)
          (projectPost program result projection) (projectPost_frame program result projection)
          (projectPost_frame program result projection) stable
  | index value selectedIndex =>
      simp only [evalTerm]
      apply failureSim_bind
      · exact termsSafe scope environment [value, selectedIndex]
      · intro values
        exact recordSafe_ofStatePreserving _ (indexPost_frame program values)
      · exact termsFailure scope environment [value, selectedIndex]
      · exact termsSuccess scope environment [value, selectedIndex]
      · intro values
        change FailureSim (indexPost program values)
          (indexPost (Noctium.Witness.eraseProgram program) values)
        rw [indexPost_eraseProgram]
        have stable : ResultsStableTogether (indexPost program values) (indexPost program values) := by
          intro sourceState replayState
          exact indexPost_resultStable program values sourceState replayState
        exact failureSim_of_frames (indexPost program values) (indexPost program values)
          (indexPost_frame program values) (indexPost_frame program values) stable
  | effect kind label result =>
      simp only [evalTerm]
      exact failureSim_fail "source term is outside the bounded native replay semantics"
  | boolAnd _ _ | boolOr _ _ | boolXor _ _ | curve _ _ | bytes _ _ | bytes32Literal _
  | foreignConstant _ _ | bytesAt _ _ =>
      simp only [evalTerm]
      exact failureSim_fail "source term is outside the bounded native replay semantics"

/-- Failed source executions replay the same error and ordered witness cursor after
stage erasure, provided both programs pass syntactic preflight and the actual
source execution starts and ends with an empty rejected-boundary trace. The proof
relates interpreter semantics. It does not prove provider honesty or host state
transitions. -/
theorem eraseProgram_evaluator_failureSim (program : Program)
    (context : EvalContext) (grants : HostGrants) (sourceProvider replayProvider : Provider)
    (sourceAdmitted : Helpers.syntacticPreflight {} program = .ok ())
    (replayAdmitted : Helpers.syntacticPreflight {} (Noctium.Witness.eraseProgram program) = .ok ()) :
    ∀ fuel,
      (∀ scope environment term, FailureSim
        (evalTerm fuel program context grants sourceProvider scope environment term)
        (evalTerm fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment term)) ∧
      (∀ scope environment terms, FailureSim
        (evalTerms fuel program context grants sourceProvider scope environment terms)
        (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms)) ∧
      (∀ declaration environment body, FailureSim
        (evalBody fuel program context grants sourceProvider declaration environment body)
        (evalBody fuel (Noctium.Witness.eraseProgram program) context grants replayProvider
          {declaration with body := Noctium.Witness.eraseStages declaration.body}
          environment (Noctium.Witness.eraseStages body))) := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro scope environment term
        simp only [evalTerm]
        exact failureSim_fail "native witness execution fuel exhausted"
      · intro scope environment terms
        cases terms with
        | nil => simp only [evalTerms]; exact failureSim_pure []
        | cons term rest => simp only [evalTerms]; exact failureSim_fail "native witness execution fuel exhausted"
      · intro declaration environment body
        cases body with
        | nil => simp only [evalBody, Noctium.Witness.eraseStages]; exact failureSim_pure RuntimeValue.unit
        | cons statement rest =>
            cases statement <;> simp [evalBody, Noctium.Witness.eraseStages] <;>
              exact failureSim_fail "native witness execution fuel exhausted"
  | succ fuel ih =>
      have recorder := evaluator_recordSafe fuel
      have termSafe : ∀ scope environment term, RecordSafe
          (evalTerm fuel program context grants sourceProvider scope environment term) :=
        fun scope environment term => recorder.1 program context grants sourceProvider scope environment term
      have termsSafe : ∀ scope environment terms, RecordSafe
          (evalTerms fuel program context grants sourceProvider scope environment terms) :=
        fun scope environment terms => recorder.2.1 program context grants sourceProvider scope environment terms
      have bodySafe : ∀ declaration environment body, RecordSafe
          (evalBody fuel program context grants sourceProvider declaration environment body) :=
        fun declaration environment body => recorder.2.2 program context grants sourceProvider declaration environment body
      have lowerSuccess := eraseProgram_evaluator_successSim program context grants
        sourceProvider replayProvider sourceAdmitted replayAdmitted fuel
      have termsFailure : ∀ scope environment terms, FailureSim
          (evalTerms fuel program context grants sourceProvider scope environment terms)
          (evalTerms fuel (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms) :=
        fun scope environment terms => ih.2.1 scope environment terms
      have callFailure : ∀ scope environment name arguments, FailureSim
          (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.call name arguments))
          (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.call name arguments)) := by
        intro scope environment name arguments
        exact evalTerm_call_failureSim_step fuel program context grants sourceProvider replayProvider
          scope environment name arguments sourceAdmitted replayAdmitted
          (fun terms => termsSafe scope environment terms)
          (fun terms => lowerSuccess.2.1 scope environment terms)
          (fun terms => termsFailure scope environment terms)
          bodySafe (fun declaration callEnvironment body => ih.2.2 declaration callEnvironment body)
      have witnessCallFailure : ∀ scope environment site name arguments, FailureSim
          (evalTerm (fuel + 1) program context grants sourceProvider scope environment (.witnessCall site name arguments))
          (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment (.witnessCall site name arguments)) := by
        intro scope environment site name arguments
        exact evalTerm_witnessCall_failureSim_step fuel program context grants sourceProvider replayProvider
          scope environment site name arguments
          (termsSafe scope environment arguments)
          (lowerSuccess.2.1 scope environment arguments)
          (termsFailure scope environment arguments)
      have termFailureNow : ∀ scope environment term, FailureSim
          (evalTerm (fuel + 1) program context grants sourceProvider scope environment term)
          (evalTerm (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment term) := by
        intro scope environment term
        exact evalTerm_failureSim_step fuel program context grants sourceProvider replayProvider
          termSafe termsSafe lowerSuccess.1 lowerSuccess.2.1 ih.1 termsFailure
          callFailure witnessCallFailure scope environment term
      have termsFailureNow : ∀ scope environment terms, FailureSim
          (evalTerms (fuel + 1) program context grants sourceProvider scope environment terms)
          (evalTerms (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider scope environment terms) := by
        intro scope environment terms
        exact evalTerms_failureSim_step fuel program (Noctium.Witness.eraseProgram program)
          context grants sourceProvider replayProvider scope environment
          (fun term => termSafe scope environment term)
          (fun items => termsSafe scope environment items)
          (fun term => lowerSuccess.1 scope environment term)
          (fun items => lowerSuccess.2.1 scope environment items)
          (fun term => ih.1 scope environment term)
          (fun items => ih.2.1 scope environment items) terms
      have bodyFailureNow : ∀ declaration environment body, FailureSim
          (evalBody (fuel + 1) program context grants sourceProvider declaration environment body)
          (evalBody (fuel + 1) (Noctium.Witness.eraseProgram program) context grants replayProvider
            {declaration with body := Noctium.Witness.eraseStages declaration.body}
            environment (Noctium.Witness.eraseStages body)) := by
        intro declaration environment body
        exact evalBody_failureSim_step fuel program context grants sourceProvider replayProvider
          termSafe bodySafe lowerSuccess.1 (fun scope environment term => ih.1 scope environment term)
          (fun declaration environment body => ih.2.2 declaration environment body)
          declaration environment body
      exact ⟨termFailureNow, termsFailureNow, bodyFailureNow⟩

set_option pp.explicit true in
#print axioms eraseProgram_evaluator_failureSim


end Noctium.Witness.Semantics


namespace Noctium.Witness.Semantics
open Helpers

deriving instance ReflBEq for WitnessReply, WitnessInvocation, ExecutionResult

/-- Admission is a property of the actual source run selected by the existing
compiler/input/entrypoint checks. It mentions no replay result. -/
def InvocationBoundaryAdmission (limits : Helpers.Limits) (fuel : Nat)
    (context : EvalContext) (program : Program) (entryName : String)
    (originalInputs initialState : List (String × RuntimeValue))
    (grants : HostGrants) (provider : Provider) : Prop :=
  ∀ admission normalized exportItem declaration environment,
    admitNativeReplay limits program entryName = .ok admission →
    normalizeExternalInputs context admission.externalInputs originalInputs = .ok normalized →
    entrypoint program entryName = .ok (exportItem, declaration) →
    entryEnvironment program context entryName normalized = .ok environment →
    ((evalBody fuel program context grants provider declaration environment declaration.body)
      {mode := .record, stagedState := initialState, path := [declaration.id]}).2.boundaryRejections = []

private theorem replay_recorded_body (fuel : Nat) (program : Program)
    (context : EvalContext) (grants : HostGrants) (provider : Provider)
    (declaration : Declaration) (environment : List (String × RuntimeValue))
    (initialState : List (String × RuntimeValue))
    (sourceResult : Except String RuntimeValue) (sourceFinal : MachineState)
    (sourcePreflight : Helpers.syntacticPreflight {} program = .ok ())
    (erasedPreflight : Helpers.syntacticPreflight {} (Noctium.Witness.eraseProgram program) = .ok ())
    (sourceRun : evalBody fuel program context grants provider declaration environment declaration.body
      {mode := .record, stagedState := initialState, path := [declaration.id]} = (sourceResult, sourceFinal))
    (admitted : sourceFinal.boundaryRejections = []) :
    ∃ replayFinal,
      evalBody fuel (Noctium.Witness.eraseProgram program) context grants
        (fun _ => .failure "replay attempted to rerun a host provider")
        {declaration with body := Noctium.Witness.eraseStages declaration.body}
        environment (Noctium.Witness.eraseStages declaration.body)
        {mode := .replay, stagedState := initialState, tape := sourceFinal.tape,
          path := [declaration.id]} = (sourceResult, replayFinal) ∧
      ReplayStateRelation sourceFinal.tape sourceFinal replayFinal ∧
      replayFinal.stagedState = initialState ∧ replayFinal.journal = [] := by
  let initial : MachineState := {mode := .record, stagedState := initialState, path := [declaration.id]}
  let replay : MachineState := {mode := .replay, stagedState := initialState, tape := sourceFinal.tape, path := [declaration.id]}
  have initialRelation : ReplayStateRelation sourceFinal.tape initial replay := by
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨sourceFinal.tape, rfl⟩⟩
  cases sourceResult with
  | ok value =>
      exact (eraseProgram_evaluator_successSim program context grants provider
        (fun _ => .failure "replay attempted to rerun a host provider") sourcePreflight erasedPreflight
        fuel).2.2 declaration environment declaration.body initial replay value sourceFinal sourceFinal.tape
          initialRelation sourceRun ⟨[], by simp⟩
  | error message =>
      exact (eraseProgram_evaluator_failureSim program context grants provider
        (fun _ => .failure "replay attempted to rerun a host provider") sourcePreflight erasedPreflight
        fuel).2.2 declaration environment declaration.body initial replay message sourceFinal sourceFinal.tape
          initialRelation rfl sourceRun admitted ⟨[], by simp⟩

#print axioms replay_recorded_body

private theorem recordInvocation_body (limits : Helpers.Limits) (fuel : Nat)
    (context : EvalContext) (program : Program) (entryName : String)
    (originalInputs initialState : List (String × RuntimeValue))
    (grants : HostGrants) (provider : Provider) (invocation : RecordedInvocation)
    (recorded : recordInvocation limits fuel context program entryName originalInputs initialState grants provider = .ok invocation) :
    ∃ admission normalized exportItem declaration environment result finalState,
      admitNativeReplay limits program entryName = .ok admission ∧
      normalizeExternalInputs context admission.externalInputs originalInputs = .ok normalized ∧
      entrypoint program entryName = .ok (exportItem, declaration) ∧
      entryEnvironment program context entryName normalized = .ok environment ∧
      evalBody fuel program context grants provider declaration environment declaration.body
        {mode := .record, stagedState := initialState, path := [declaration.id]} = (result, finalState) ∧
      invocation = {source := program, entryName, originalInputs := normalized, initialState, grants, observation := executionObservation result finalState} := by
  cases modulus : context.modulus == Field.modulus with
  | false => simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, recordInvocation, modulus] at recorded
  | true =>
    by_cases bounded : fuel > limits.maxExecutionSteps
    · simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, recordInvocation, modulus, bounded] at recorded
    · cases admissionResult : admitNativeReplay limits program entryName with
      | error message => simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, recordInvocation, modulus, bounded, admissionResult] at recorded
      | ok admission =>
        cases normalizedResult : normalizeExternalInputs context admission.externalInputs originalInputs with
        | error message => simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, recordInvocation, modulus, bounded, admissionResult, normalizedResult] at recorded
        | ok normalized =>
          cases canonical : canonicalInitialState program context initialState with
          | false => simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, recordInvocation, modulus, bounded, admissionResult, normalizedResult, canonical] at recorded
          | true =>
            cases environmentResult : entryEnvironment program context entryName normalized with
            | error message => simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, recordInvocation, modulus, bounded, admissionResult, normalizedResult, canonical, environmentResult] at recorded
            | ok environment =>
              cases entryResult : entrypoint program entryName with
              | error message => simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, recordInvocation, modulus, bounded, admissionResult, normalizedResult, canonical, environmentResult, entryResult] at recorded
              | ok pair =>
                rcases pair with ⟨exportItem, declaration⟩
                cases bodyResult : evalBody fuel program context grants provider declaration environment declaration.body
                    {mode := .record, stagedState := initialState, path := [declaration.id]} with
                | mk result finalState =>
                  refine ⟨admission, normalized, exportItem, declaration, environment, result, finalState,
                    (by first | rfl | exact admissionResult), (by first | rfl | exact normalizedResult), (by first | rfl | exact entryResult), (by first | rfl | exact environmentResult), (by first | rfl | exact bodyResult), ?_⟩
                  simpa [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, recordInvocation, modulus, bounded, admissionResult, normalizedResult, canonical, environmentResult, entryResult, bodyResult] using recorded.symm

#print axioms recordInvocation_body


/-- Accepted record/replay invocations reproduce the exact source result and
ordered tape cursor. Erased replay leaves the private store and journal framed.
The source admission condition excludes only diagnosed host-boundary rejection.
It asserts no equality with replay and does not assume the desired match flag. -/
theorem recordInvocation_replayInvocation_matches (limits : Helpers.Limits) (fuel : Nat)
    (context : EvalContext) (program : Program) (entryName : String)
    (originalInputs suppliedInputs initialState : List (String × RuntimeValue))
    (grants : HostGrants) (provider : Provider)
    (invocation : RecordedInvocation) (report : ReplayReport)
    (sourcePreflight : Helpers.syntacticPreflight {} program = .ok ())
    (erasedPreflight : Helpers.syntacticPreflight {} (Noctium.Witness.eraseProgram program) = .ok ())
    (admitted : InvocationBoundaryAdmission limits fuel context program entryName originalInputs initialState grants provider)
    (recorded : recordInvocation limits fuel context program entryName originalInputs initialState grants provider = .ok invocation)
    (replayed : replayInvocation limits fuel context invocation suppliedInputs = .ok report) :
    report.matchesRecordedSource = true ∧
      report.execution.result = invocation.observation.result ∧
      report.execution.cursor = invocation.observation.cursor ∧
      report.execution.tape = invocation.observation.tape ∧
      report.execution.stagedState = initialState ∧ report.execution.journal = [] := by
  obtain ⟨admission, normalized, exportItem, declaration, environment, result, finalState,
    hAdmission, hNormalized, hEntry, hEnvironment, hBody, hInvocation⟩ :=
    recordInvocation_body limits fuel context program entryName originalInputs initialState grants provider invocation recorded
  have boundary : finalState.boundaryRejections = [] := by
    have accepted := admitted admission normalized exportItem declaration environment hAdmission hNormalized hEntry hEnvironment
    rw [hBody] at accepted
    exact accepted
  obtain ⟨replayFinal, hReplayBody, relation, storeFrame, journalFrame⟩ :=
    replay_recorded_body fuel program context grants provider declaration environment initialState result finalState
      sourcePreflight erasedPreflight hBody boundary
  have sourceCursor : finalState.cursor = finalState.tape.length := relation.2.2.1
  have cursorEq : replayFinal.cursor = finalState.cursor := relation.2.2.2.1
  have tapeEq : replayFinal.tape = finalState.tape := relation.2.2.2.2.2.1
  have completeCursor : replayFinal.cursor = finalState.tape.length := cursorEq.trans sourceCursor
  have hErasedEntry : entrypoint (Noctium.Witness.eraseProgram program) entryName =
      .ok (exportItem, {declaration with body := Noctium.Witness.eraseStages declaration.body}) := by
    rw [entrypoint_eraseProgram, hEntry]
    rfl
  have hErasedEnvironment : entryEnvironment (Noctium.Witness.eraseProgram program) context entryName normalized = .ok environment := by
    rw [entryEnvironment_eraseProgram, hEnvironment]
  subst invocation
  cases modulus : context.modulus == Field.modulus with
  | false => simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, replayInvocation, modulus] at replayed
  | true =>
    by_cases bounded : fuel > limits.maxExecutionSteps
    · simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, replayInvocation, modulus, bounded] at replayed
    · cases supplied : normalizeExternalInputs context admission.externalInputs suppliedInputs with
      | error message => simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, replayInvocation, modulus, bounded, hAdmission, supplied] at replayed
      | ok suppliedValues =>
        cases same : sameRuntimeBindings suppliedValues normalized with
        | false => simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, replayInvocation, modulus, bounded, hAdmission, supplied, same] at replayed
        | true =>
          cases result with
          | error message =>
            cases callTape : validateCallTape program context admission.host.calls finalState.tape false with
            | error message => simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, replayInvocation, executionObservation, modulus, bounded, hAdmission, supplied, same, callTape] at replayed
            | ok unit =>
              cases unit
              simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, replayInvocation, executionObservation, modulus, bounded, hAdmission, supplied, same, callTape,
                hErasedEntry, hErasedEnvironment, hReplayBody, completeCursor, cursorEq, tapeEq] at replayed
              cases replayed
              simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, executionObservation, cursorEq, tapeEq, sourceCursor, storeFrame, journalFrame]
          | ok value =>
            cases callTape : validateCallTape program context admission.host.calls finalState.tape true with
            | error message => simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, replayInvocation, executionObservation, modulus, bounded, hAdmission, supplied, same, callTape] at replayed
            | ok unit =>
              cases unit
              cases boundTape : bindTape program context admission.host.calls finalState.tape with
              | error message => simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, replayInvocation, executionObservation, modulus, bounded, hAdmission, supplied, same, callTape, boundTape] at replayed
              | ok fresh =>
                cases completeMap : validateCompleteInputMap context admission normalized fresh with
                | error message => simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, replayInvocation, executionObservation, modulus, bounded, hAdmission, supplied, same, callTape, boundTape, completeMap] at replayed
                | ok completeValues =>
                  simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, replayInvocation, executionObservation, modulus, bounded, hAdmission, supplied, same, callTape,
                    boundTape, completeMap, hErasedEntry, hErasedEnvironment, hReplayBody, completeCursor, cursorEq, tapeEq] at replayed
                  cases replayed
                  simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, executionObservation, cursorEq, tapeEq, sourceCursor, storeFrame, journalFrame]

#print axioms recordInvocation_replayInvocation_matches

end Noctium.Witness.Semantics

namespace Noctium.Witness.Semantics
open Helpers

private def boundaryExampleContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused"
}

private def boundaryReadSignature : WitnessSignature := {
  name := "cache", operation := "private_state.read.v1", capability := "private",
  privateKey := some "cache", result := .scalar .native
}

private def boundaryExampleDeclaration : Declaration := {
  id := ⟨0, 0⟩, name := "example", result := .scalar .native,
  body := [
    .stage "private" "cache" .native (.native 1),
    .return (some (.witnessCall "read-cache" "cache" []))
  ]
}

private def boundaryExampleProgram : Program := {
  witnesses := [boundaryReadSignature], declarations := [boundaryExampleDeclaration]
}

#guard match Helpers.syntacticPreflight {} boundaryExampleProgram with
  | .ok _ => true
  | .error _ => false
#guard match Helpers.syntacticPreflight {} (Noctium.Witness.eraseProgram boundaryExampleProgram) with
  | .ok _ => true
  | .error _ => false

private def boundaryExampleGrants : HostGrants := {
  providers := [{name := "cache", operation := "private_state.read.v1", capability := "private", privateKey := some "cache"}],
  stateWrites := [("private", "cache")]
}

private def boundaryExampleRun (grants : HostGrants) (reply : WitnessReply) :=
  evalBody 12 boundaryExampleProgram boundaryExampleContext grants (fun _ => reply)
    boundaryExampleDeclaration [] boundaryExampleDeclaration.body
    {mode := .record, path := [boundaryExampleDeclaration.id]}

-- An admitted source run stages a value and receives the same value through READ.
#guard match (boundaryExampleRun boundaryExampleGrants (.value (.scalar (.native 1)))).1 with
  | .ok (.scalar (.native 1)) => true
  | _ => false
#guard (boundaryExampleRun boundaryExampleGrants (.value (.scalar (.native 1)))).2.boundaryRejections == []
#guard (boundaryExampleRun boundaryExampleGrants (.value (.scalar (.native 1)))).2.cursor == 1
#guard (boundaryExampleRun boundaryExampleGrants (.value (.scalar (.native 1)))).2.journal ==
  [("cache", .scalar (.native 1))]

-- Terminal provider failure consumes a record and stays inside failure admission.
#guard match (boundaryExampleRun boundaryExampleGrants (.failure "terminal")).1 with
  | .error message => message == "terminal"
  | .ok _ => false
#guard (boundaryExampleRun boundaryExampleGrants (.failure "terminal")).2.boundaryRejections == []
#guard (boundaryExampleRun boundaryExampleGrants (.failure "terminal")).2.cursor == 1

-- A rejected staged READ records no provider event and excludes the one-shot run.
#guard (boundaryExampleRun boundaryExampleGrants (.value (.scalar (.native 2)))).2.boundaryRejections ==
  [.providerCallback]
#guard (boundaryExampleRun boundaryExampleGrants (.value (.scalar (.native 2)))).2.cursor == 0
#guard (boundaryExampleRun boundaryExampleGrants (.value (.scalar (.native 2)))).2.tape.length == 0

-- Denied writes and stage-only casts have explicit nonempty rejection traces.
#guard (boundaryExampleRun {boundaryExampleGrants with stateWrites := []}
  (.value (.scalar (.native 1)))).2.boundaryRejections == [.stageWrite]
#guard (stageCast boundaryExampleContext .native .unit {}).2.boundaryRejections == [.stageCast]

-- Malformed typed callbacks are distinct from accepted terminal provider failures.
private def boundaryMalformedReplyRun :=
  sourceProviderReply {} boundaryExampleContext (fun _ => .value .unit)
    {name := "malformed", operation := "example.lookup.v1", capability := "lookup",
      result := .scalar .native}
    {name := "malformed", operation := "example.lookup.v1", capability := "lookup",
      privateKey := none, stagedState := [], arguments := []} {}

#guard match boundaryMalformedReplyRun.1 with | .ok (.value .unit) => true | _ => false
#guard boundaryMalformedReplyRun.2.boundaryRejections == [.providerCallback]
#guard boundaryMalformedReplyRun.2.cursor == 0
#guard boundaryMalformedReplyRun.2.tape.length == 0

private def boundaryNestedAssertionRun := Id.run do
  let child : Declaration := {
    id := ⟨0, 0⟩, name := "child", body := [.assert (.bool false)]}
  let parent : Declaration := {
    id := ⟨0, 1⟩, name := "parent", body := [.evaluate (.call "child" [])]}
  let program : Program := {declarations := [child, parent]}
  return evalBody 12 program boundaryExampleContext {} (fun _ => .failure "unused")
    parent [] parent.body {mode := .record, path := [parent.id]}

#guard match boundaryNestedAssertionRun.1 with | .error _ => true | .ok _ => false
#guard boundaryNestedAssertionRun.2.boundaryRejections == []
#guard boundaryNestedAssertionRun.2.cursor == 0

end Noctium.Witness.Semantics
