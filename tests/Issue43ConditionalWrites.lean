import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend
import Noctium.Verification.GuardedPlanExecution
import Noctium.Verification.GenericStateEncoding

open scoped Noctium
open Noctium

noctium_circuit issue43ConditionalWrites where
  private enabled : Bool
  public account : Native
end

noctium_contract Issue43ConditionalWrites where
  cell current : Native
  map allowances : Native => Native
  entry apply uses issue43ConditionalWrites where
    when disclose(enabled) write current := 21
    when disclose(enabled) insert allowances[account] := 9
  end
end

private def issue43Entry : Entrypoint :=
  match Issue43ConditionalWrites.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

private def issue43Context : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

private def issue43Inputs (enabled : _root_.Bool) : EvalEnv := [
  ("enabled", .bool enabled), ("account", .native 7)]

private def issue43Initial : LedgerState := {
  cells := [("current", .native 4)]
  maps := [("allowances", [])]
}

#guard match issue43Entry.run issue43Context (issue43Inputs Bool.true) issue43Initial with
  | .ok (outputs, after) => outputs.isEmpty &&
      after.cells.lookup "current" == some (.native 21) &&
      after.maps.lookup "allowances" == some [(.native 7, .native 9)]
  | .error _ => Bool.false

#guard match issue43Entry.run issue43Context (issue43Inputs Bool.false) issue43Initial with
  | .ok (outputs, after) => outputs.isEmpty && after == issue43Initial
  | .error _ => Bool.false

private def issue43Undisclosed : Entrypoint :=
  {issue43Entry with effectGuards := [
    some (.ref "enabled" : Expr .bool),
    some (.disclose {} (.ref "enabled" : Expr .bool))]}

#guard match Disclosure.entrypoint issue43Undisclosed with
  | .error _ => Bool.true
  | .ok _ => Bool.false

private def issue43Partial : Entrypoint :=
  {issue43Entry with
    effects := [.writeCell "current" .native
      (.cast .native (.usub (.uint 3 1) (.uint 3 2)))]
    effectGuards := [some (.disclose {} (.ref "enabled" : Expr .bool))]}

#guard match issue43Partial.validate
    {poseidon2 := Bool.true, stateCells := Bool.true, stateMaps := Bool.true}
    Issue43ConditionalWrites.state with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint
    Issue43ConditionalWrites.state issue43Entry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

private def guardedFoldEntry : Entrypoint := { issue43Entry with
  effects := issue43Entry.effects ++ [
    .readMap "allowances" "readBack" .native .native (.ref "account"),
    .readCell "current" "observed" .native]
  effectSpans := issue43Entry.effectSpans ++ [issue43Entry.span, issue43Entry.span]
  effectGuards := issue43Entry.effectGuards ++
    [some (.disclose {} (.ref "enabled")), none] }

/-- The active read sees the preceding write. The missing map entry never
reaches the VM on the inactive path. The unguarded read runs in both cases. -/
private def guardedFoldCheck (enabled : _root_.Bool) : Except String _root_.Bool := do
  let state := Issue43ConditionalWrites.state
  let env := issue43Inputs enabled
  let plan ← (Backend.Impact.lower state guardedFoldEntry).mapError (·.message)
  let (sourceEnv, after) ← runEffectsWithGuardsAndEnv issue43Context guardedFoldEntry.effects
    guardedFoldEntry.effectGuards env issue43Initial
  let complete := env ++ [("readBack", .native (if enabled then 9 else 0)),
    ("observed", .native (if enabled then 21 else 4))]
  let some slots := Verification.GenericStateEncoding.encodeState state issue43Initial
    | throw "initial state does not encode"
  let some finalSlots := Verification.GenericStateEncoding.encodeState state after
    | throw "source result does not encode"
  let native ← Verification.GuardedPlanExecution.evalPlan issue43Context complete plan
  let some machine := Verification.NativeState.run native ⟨[.vector slots], []⟩
    | throw "checked native state rejected"
  let scalarCell := Verification.NativeState.field ∘ Verification.NativeRelation.scalar
  let expectedReads := if enabled then [scalarCell 7, scalarCell 9, scalarCell 21]
    else [scalarCell 7, scalarCell 4]
  let badEnv := if enabled then ("readBack", .native 8) :: complete
    else complete.filter (fun binding => binding.1 != "readBack")
  let bad ← Verification.GuardedPlanExecution.evalPlan issue43Context badEnv plan
  let malformed := Verification.GuardedPlanExecution.evalPlan issue43Context complete
    {plan with activityGuards := [none]}
  return !malformed.isOk && decide (machine = ⟨[.vector finalSlots], expectedReads⟩ ∧
    sourceEnv.lookup "readBack" = complete.lookup "readBack" ∧
    sourceEnv.lookup "observed" = complete.lookup "observed" ∧
    (if enabled then Verification.NativeState.run bad ⟨[.vector slots], []⟩ = none
      else bad = native))

#guard (guardedFoldCheck Bool.true).toOption == some Bool.true
#guard (guardedFoldCheck Bool.false).toOption == some Bool.true
