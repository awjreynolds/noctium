import Noctium.Witness.Semantics

open Noctium.Helpers
open Noctium.Witness
open Noctium.Witness.Semantics
open Noctium

namespace WitnessSemanticsTest

/-- Covers direct stages, nested branches, ordered witness calls, and a return. -/
def sourceFixture : List Statement := [
  .stage "private" "claim/first" .native (.witnessCall "first" "lookup" []),
  .branch (.witnessCall "condition" "eligible" [])
    [.stage "private" "claim/yes" .bool (.witnessCall "yes" "lookup" [])]
    [.evaluate (.witnessCall "no" "lookup" [])],
  .evaluate (.witnessCall "before-return" "lookup" []),
  .return (some (.witnessCall "return" "lookup" [])),
  .stage "private" "claim/after-return" .native (.native 9)
]

example : expressionSchedule (eraseStages sourceFixture) = expressionSchedule sourceFixture :=
  eraseStages_preserves_expressionSchedule sourceFixture

example : scheduledWitnessOccurrences (eraseStages sourceFixture) =
    scheduledWitnessOccurrences sourceFixture :=
  eraseStages_preserves_witnessOccurrences sourceFixture

example : evaluatedObservations (circuitObservations (eraseStages sourceFixture)) =
    evaluatedObservations (stageObservations sourceFixture) :=
  stageBoundary sourceFixture

example : privateWrites (stageObservations sourceFixture) = sourceStageEvents sourceFixture :=
  stageObservations_preserve_exact_write_frame sourceFixture

def writeKeys (observations : List Observation) : List String :=
  observations.filterMap fun observation => match observation with
    | .privateWrite _ key _ _ => some key
    | .evaluate _ => none

def sourceWriteKeys : List String := writeKeys (stageObservations sourceFixture)

#guard decide (sourceWriteKeys = ["claim/first", "claim/yes"])
#guard decide (writeKeys (sourceStageEvents sourceFixture) = ["claim/first", "claim/yes"])
#guard decide ((privateWrites (circuitObservations (eraseStages sourceFixture))).length = 0)

#guard decide (scheduledWitnessOccurrences sourceFixture = [
  ("first", "lookup"),
  ("condition", "eligible"),
  ("yes", "lookup"),
  ("no", "lookup"),
  ("before-return", "lookup"),
  ("return", "lookup")
])

def failingFixture : List Statement := [
  .stage "private" "claim/value" .native (.witnessCall "stage-value" "lookup" []),
  .evaluate (.witnessCall "failure" "lookup" []),
  .return (some (.witnessCall "after-failure" "lookup" []))
]

def providerOracle : Term → Except String String
  | .witnessCall "failure" _ _ => .error "provider failed"
  | .witnessCall site _ _ => .ok site
  | _ => .ok "pure"

#guard (match runUntilError providerOracle (expressionSchedule failingFixture) with
  | .error message => message == "provider failed"
  | .ok _ => false)

example : runUntilError providerOracle (expressionSchedule (eraseStages failingFixture)) =
    runUntilError providerOracle (expressionSchedule failingFixture) :=
  eraseStages_preserves_shortCircuitObservations failingFixture providerOracle

def nativeContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused Poseidon oracle"
}

def cachedClaim : Program := {
  witnesses := [
    {name := "cache", operation := "private_state.read.v1", capability := "private",
      privateKey := some "claim/cache", result := .scalar .native},
    {name := "lookup", operation := "noctium.lookup.v1", capability := "lookup",
      parameters := [{name := "seed", type := .scalar .native}], result := .scalar .native}
  ]
  declarations := [
    {id := ⟨0, 0⟩, name := "fetch", parameters := [{name := "seed", ty := .native}],
      result := .scalar .native, body := [
        .bind "previous" (.scalar .native) (.witnessCall "fetch-cache" "cache" []),
        .assert (.eq (.ref "previous") (.native 1)),
        .return (some (.witnessCall "fetch-value" "lookup" [.ref "seed"]))
      ]},
    {id := ⟨0, 1⟩, name := "claim",
      parameters := [{name := "expected", ty := .native}, {name := "seed", ty := .native}],
      result := .scalar .native, body := [
        .stage "private" "claim/cache" .native (.native 1),
        .bind "afterStage" (.scalar .native) (.witnessCall "after-stage" "cache" []),
        .assert (.eq (.ref "afterStage") (.native 1)),
        .bind "first" (.scalar .native) (.call "fetch" [.ref "seed"]),
        .bind "second" (.scalar .native) (.call "fetch" [.ref "seed"]),
        .assert (.eq (.ref "first") (.ref "expected")),
        .assert (.eq (.ref "second") (.ref "expected")),
        .stage "private" "claim/cache" .native (.ref "second"),
        .return (some (.ref "expected"))
      ]}
  ]
  exports := [{name := "claim", target := ⟨0, 1⟩, inputs := [
    {name := "expected", ty := .native, visibility := .public},
    {name := "seed", ty := .native, visibility := .private}
  ]}]
}

def claimInputs : List (String × RuntimeValue) := [
  ("expected", .scalar (.native 14)),
  ("seed", .scalar (.native 7))
]

def claimInitialState : List (String × RuntimeValue) := [
  ("claim/cache", .scalar (.native 0))
]

def claimGrants : HostGrants := {
  providers := [
    {name := "cache", operation := "private_state.read.v1", capability := "private",
      privateKey := some "claim/cache"},
    {name := "lookup", operation := "noctium.lookup.v1", capability := "lookup",
      privateKey := none}
  ]
  stateWrites := [("private", "claim/cache")]
}

def cacheLookupProvider : Provider := fun request =>
  if request.operation == "private_state.read.v1" then
    (request.stagedState.lookup "claim/cache").map WitnessReply.value
      |>.getD (.failure "cache key missing")
  else if request.operation == "noctium.lookup.v1" then
    match request.arguments with
    | [.scalar (.native 7)] => .value (.scalar (.native 14))
    | _ => .failure "lookup rejected its source input"
  else .failure "unknown operation"

def failingCacheProvider : Provider := fun request =>
  if request.operation == "private_state.read.v1" then .value (.scalar (.native 0))
  else cacheLookupProvider request

def wrongLookupProvider : Provider := fun request =>
  if request.operation == "noctium.lookup.v1" then .value (.scalar (.native 13))
  else cacheLookupProvider request

def failingLookupProvider : Provider := fun request =>
  if request.operation == "noctium.lookup.v1" then .failure "lookup unavailable"
  else cacheLookupProvider request

def recordCachedClaim (provider : Provider) : Except String RecordedInvocation :=
  recordInvocation {} 4096 nativeContext cachedClaim "claim" claimInputs claimInitialState
    claimGrants provider

def successfulReplay : Bool := Id.run do
  let .ok source := recordCachedClaim cacheLookupProvider | return false
  let .ok report := replayInvocation {} 4096 nativeContext source claimInputs | return false
  return report.matchesRecordedSource &&
    report.execution.result == .success (.scalar (.native 14)) &&
    source.observation.cursor == 5 && source.observation.tape.length == 5 &&
    source.observation.journal.length == 2 && report.execution.journal.isEmpty &&
    report.completeInputs.length == 7 &&
    report.completeInputs.any (fun input => input.name == "seed" &&
      input.visibility == .private && input.value == .scalar (.native 7))

#guard successfulReplay

def successfulReplayUsesOrderedCompleteInputs : Bool := Id.run do
  let .ok source := recordCachedClaim cacheLookupProvider | return false
  let .ok report := replayInvocation {} 4096 nativeContext source claimInputs | return false
  let .ok admission := admitNativeReplay {} cachedClaim "claim" | return false
  return report.completeInputs.map (·.name) == admission.host.circuit.inputs.map (·.name) &&
    report.completeInputs.map (·.value) == [
      .scalar (.native 14), .scalar (.native 7),
      .scalar (.native 1), .scalar (.native 1), .scalar (.native 14),
      .scalar (.native 1), .scalar (.native 14)
    ]

#guard successfulReplayUsesOrderedCompleteInputs

def providerFailureReplay : Bool := Id.run do
  let .ok source := recordCachedClaim failingLookupProvider | return false
  let .ok report := replayInvocation {} 4096 nativeContext source claimInputs | return false
  return report.matchesRecordedSource &&
    report.execution.result == .failure "lookup unavailable" &&
    source.observation.cursor == 3 && report.execution.cursor == 3 &&
    report.execution.journal.isEmpty

#guard providerFailureReplay

def assertionFailureReplay : Bool := Id.run do
  let .ok source := recordCachedClaim wrongLookupProvider | return false
  let .ok report := replayInvocation {} 4096 nativeContext source claimInputs | return false
  return report.matchesRecordedSource &&
    report.execution.result == .failure "helper assertion failed" &&
    source.observation.cursor == 5 && report.execution.cursor == 5 &&
    source.observation.journal.length == 1 && report.execution.journal.isEmpty

#guard assertionFailureReplay

def mismatchedPrivateReadRejected : Bool := Id.run do
  let .ok source := recordCachedClaim failingCacheProvider | return false
  return source.observation.cursor == 0 && source.observation.tape.isEmpty &&
    source.observation.result == .failure "private state provider result does not match staged state" &&
    source.observation.journal.length == 1

#guard mismatchedPrivateReadRejected

def deniedStageWrite : Bool := Id.run do
  let grants := {claimGrants with stateWrites := []}
  let .ok source := recordInvocation {} 4096 nativeContext cachedClaim "claim"
    claimInputs claimInitialState grants cacheLookupProvider | return false
  return source.observation.result == .failure "host private-state write capability was not granted" &&
    source.observation.cursor == 0 && source.observation.tape.isEmpty &&
    source.observation.journal.isEmpty && source.observation.stagedState == claimInitialState

#guard deniedStageWrite

def changedInputRejected : Bool := Id.run do
  let .ok source := recordCachedClaim cacheLookupProvider | return false
  let changed := [("expected", .scalar (.native 13)), ("seed", .scalar (.native 7))]
  return match replayInvocation {} 4096 nativeContext source changed with
    | .error _ => true
    | .ok _ => false

#guard changedInputRejected

def pairType : Types.CompositeType := .structure "WitnessSemanticsTest.Pair"
def pairProgram : Program := {
  composites := {structures := [{id := "WitnessSemanticsTest.Pair", fields := [
    {name := "amount", type := .scalar (.uint 255)},
    {name := "okay", type := .scalar .bool}
  ]}]}
  witnesses := [{
    name := "pair", operation := "noctium.pair.v1", capability := "pair",
    parameters := [{name := "request", type := .composite pairType}],
    result := .composite pairType
  }]
  declarations := [
    {id := ⟨0, 0⟩, name := "fetchPair", parameters := [{name := "request", ty := .native}],
      compositeParameters := [("request", pairType)], result := .composite pairType,
      body := [.return (some (.witnessCall "pair-result" "pair" [.ref "request"]))]},
    {id := ⟨0, 1⟩, name := "claimPair",
      parameters := [{name := "expected", ty := .uint 255}, {name := "request", ty := .native}],
      compositeParameters := [("request", pairType)], result := .composite pairType,
      body := [
        .bind "answer" (.composite pairType) (.call "fetchPair" [.ref "request"]),
        .assert (.eq (.project (.ref "answer") (.field "amount")) (.ref "expected")),
        .assert (.project (.ref "answer") (.field "okay")),
        .stage "private" "pair/amount" (.uint 255)
          (.project (.ref "answer") (.field "amount")),
        .return (some (.disclose {} (.ref "answer")))
      ]}
  ]
  exports := [{
    name := "pair", target := ⟨0, 1⟩,
    inputs := [{name := "expected", ty := .uint 255, visibility := .public}],
    compositeInputs := [{name := "request", type := pairType, visibility := .private}]
  }]
}

def pairRuntime (amount : Nat) (okay : Bool) : RuntimeValue := Id.run do
  let .ok compiled := Types.compileType pairProgram.composites pairType | return .unit
  let aggregate : Types.AggregateValue := .structure "WitnessSemanticsTest.Pair" [
    ("amount", .scalar (.uint 255) amount),
    ("okay", .scalar .bool (if okay then 1 else 0))
  ]
  let .ok leaves := Types.flatten compiled aggregate | return .unit
  return .aggregate pairType compiled.fingerprint leaves

def pairProvider : Provider := fun _ => .value (pairRuntime 14 true)

def pairInputs : List (String × RuntimeValue) := [
  ("expected", .scalar (.uint 255 14)),
  ("request.amount", .scalar (.native 7)),
  ("request.okay", .scalar (.native 1))
]

def pairReplay : Bool := Id.run do
  let grants : HostGrants := {
    providers := [{
      name := "pair"
      operation := "noctium.pair.v1"
      capability := "pair"
      privateKey := none
    }]
    stateWrites := [("private", "pair/amount")]
  }
  let .ok source ← recordInvocation {} 4096 nativeContext pairProgram "pair" pairInputs [] grants pairProvider
    | return false
  let .ok report ← replayInvocation {} 4096 nativeContext source pairInputs | return false
  return report.matchesRecordedSource && report.completeInputs.length == 5 &&
    source.observation.tape.length == 1 &&
    (source.observation.tape[0]?.map (·.arguments.length) == some 1)

#guard pairReplay

private def aggregateEqualityReplay (leftType rightType : Types.CompositeType) (left right : List Term)
    (expected : Bool) : Bool := Id.run do
  let program : Program := {
    composites := pairProgram.composites
    declarations := [{
      id := ⟨0, 0⟩
      name := "equalPair"
      result := .scalar .bool
      body := [.return (some (.eq
        (.composite leftType left) (.composite rightType right)))]
    }]
    exports := [{name := "equal", target := ⟨0, 0⟩}]
  }
  let .ok source ← recordInvocation {} 256 nativeContext program "equal" [] [] {}
      (fun _ => .failure "record comparison has no witnesses") | return false
  let .ok report ← replayInvocation {} 256 nativeContext source [] | return false
  return report.matchesRecordedSource && report.execution.result == .success (.scalar (.bool expected))

#guard aggregateEqualityReplay pairType pairType [.uint 255 7, .bool true] [.uint 255 7, .bool true] true
#guard aggregateEqualityReplay pairType pairType [.uint 255 7, .bool true] [.uint 255 8, .bool true] false

private def nestedEqualityType : Types.CompositeType :=
  .tuple [pairType, .bytes 2, .vector 2 (.scalar .native)]

private def nestedEqualityLeaves (byte : Nat) : List Term :=
  [.uint 255 7, .bool true, .native 0, .native byte, .native 11, .native 12]

#guard aggregateEqualityReplay nestedEqualityType nestedEqualityType
  (nestedEqualityLeaves 2) (nestedEqualityLeaves 2) true
#guard aggregateEqualityReplay nestedEqualityType nestedEqualityType
  (nestedEqualityLeaves 2) (nestedEqualityLeaves 3) false

#guard aggregateEqualityReplay (.vector 2 (.scalar (.uint 255))) (.vector 2 (.scalar (.uint 65535)))
  [.uint 255 1, .uint 255 2] [.uint 65535 1, .uint 65535 2] true
#guard aggregateEqualityReplay (.tuple [.scalar (.uint 255), .scalar .native])
  (.tuple [.scalar (.uint 65535), .scalar .native])
  [.uint 255 1, .native 11] [.uint 65535 1, .native 12] false

def unitWitnessProgram : Program := {
  witnesses := [{
    name := "unitResult"
    operation := "noctium.unit.v1"
    capability := "unit"
    result := .unit
  }]
  declarations := [{
    id := ⟨0, 0⟩
    name := "runUnit"
    result := .unit
    body := [.return (some (.witnessCall "unit-site" "unitResult" []))]
  }]
  exports := [{name := "unit", target := ⟨0, 0⟩}]
}

def unitWitnessReplay : Bool := Id.run do
  let grants : HostGrants := {
    providers := [{
      name := "unitResult"
      operation := "noctium.unit.v1"
      capability := "unit"
      privateKey := none
    }]
  }
  let .ok source ← recordInvocation {} 128 nativeContext unitWitnessProgram "unit" [] [] grants
      (fun _ => .value .unit) | return false
  let .ok report ← replayInvocation {} 128 nativeContext source [] | return false
  return report.matchesRecordedSource && source.observation.tape.length == 1 &&
    source.observation.cursor == 1 && source.observation.tape[0]?.map (·.site) == some "unit-site" &&
    source.observation.tape[0]?.map (·.reply) == some (.value .unit) &&
    report.completeInputs.isEmpty && report.execution.cursor == 1

#guard unitWitnessReplay

def emptyType : Types.CompositeType := .structure "WitnessSemanticsTest.Empty"
def emptyProgram : Program := {
  composites := {structures := [{id := "WitnessSemanticsTest.Empty", fields := []}]}
  witnesses := [{
    name := "emptyResult"
    operation := "noctium.empty.v1"
    capability := "empty"
    result := .composite emptyType
  }]
  declarations := [{
    id := ⟨0, 0⟩
    name := "runEmpty"
    result := .composite emptyType
    body := [.return (some (.witnessCall "empty-site" "emptyResult" []))]
  }]
  exports := [{name := "empty", target := ⟨0, 0⟩}]
}

def emptyAggregate : RuntimeValue := Id.run do
  let .ok compiled := Types.compileType emptyProgram.composites emptyType | return .unit
  return .aggregate emptyType compiled.fingerprint []

def emptyNominalReplay : Bool := Id.run do
  let grants : HostGrants := {
    providers := [{
      name := "emptyResult"
      operation := "noctium.empty.v1"
      capability := "empty"
      privateKey := none
    }]
  }
  let .ok source ← recordInvocation {} 128 nativeContext emptyProgram "empty" [] [] grants
      (fun _ => .value emptyAggregate) | return false
  let .ok report ← replayInvocation {} 128 nativeContext source [] | return false
  return report.matchesRecordedSource && source.observation.tape.length == 1 &&
    source.observation.tape[0]?.map (·.resultType) == some (.composite emptyType) &&
    source.observation.tape[0]?.map (·.reply) == some (.value emptyAggregate) &&
    report.completeInputs.isEmpty && report.execution.cursor == 1

#guard emptyNominalReplay

def vectorType : Types.CompositeType := .vector 2 (.scalar (.uint 255))
def vectorIndexProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩, name := "selectVector", result := .scalar (.uint 255),
    body := [.return (some (.index
      (.composite vectorType [.uint 255 3, .uint 255 8]) (.uint 255 1)))]
  }]
  exports := [{name := "vector", target := ⟨0, 0⟩}]
}

def vectorIndexReplay : Bool := Id.run do
  let .ok source ← recordInvocation {} 256 nativeContext vectorIndexProgram "vector" [] [] {}
      (fun _ => .failure "vector program has no witness calls") | return false
  let .ok report ← replayInvocation {} 256 nativeContext source [] | return false
  return report.matchesRecordedSource && report.execution.result == .success (.scalar (.uint 255 8))

#guard vectorIndexReplay

/-- The recorder preserves private lookup arguments even when the provider's
response, public result, and staged write agree. -/
private def providerObservesPrivateArguments : Bool := Id.run do
  let lookup : Provider := fun request =>
    if request.operation == "noctium.lookup.v1" then .value (.scalar (.native 14))
    else cacheLookupProvider request
  let record (seed : Nat) :=
    recordInvocation {} 4096 nativeContext cachedClaim "claim"
      [("expected", .scalar (.native 14)), ("seed", .scalar (.native seed))]
      claimInitialState claimGrants lookup
  let .ok left := record 7 | return false
  let .ok right := record 11 | return false
  let lookupArguments (invocation : RecordedInvocation) :=
    (invocation.observation.tape.filter (·.operation == "noctium.lookup.v1")).map
      WitnessInvocation.arguments
  return left.observation.result == .success (.scalar (.native 14)) &&
    left.observation.result == right.observation.result &&
    left.observation.journal == right.observation.journal &&
    left.observation.stagedState == right.observation.stagedState &&
    lookupArguments left == [[.scalar (.native 7)], [.scalar (.native 7)]] &&
    lookupArguments right == [[.scalar (.native 11)], [.scalar (.native 11)]]

#guard providerObservesPrivateArguments

end WitnessSemanticsTest
