import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit timeInputs where
  public cutoff : UInt 64
  public enabled : Bool
end

noctium_contract NativeBlockTime where
  entry checkTime uses timeInputs where
    if enabled then {
      when eq(enabled, false) blockTimeAtOrAfter(cutoff) as skipped
      require eq(skipped, false)
    } else {}
    when enabled blockTimeBefore(cutoff) as before
    when enabled blockTimeAfter(cutoff) as after
    when enabled blockTimeAtOrAfter(cutoff) as atOrAfter
    when enabled blockTimeAtOrBefore(cutoff) as atOrBefore
    return beforeDeadline : Bool := before
    return afterDeadline : Bool := after
    return atOrAfterDeadline : Bool := atOrAfter
    return atOrBeforeDeadline : Bool := atOrBefore
  end
end

private def nativeBlockTimeContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

#guard match NativeBlockTime.entrypoints with
  | [ep] =>
    let inputs := [
      ("cutoff", Value.uint (2 ^ 64 - 1) 10),
      ("enabled", Value.bool Bool.true)]
    match ep.run {nativeBlockTimeContext with blockTimeSeconds := some 9} inputs {},
        ep.run {nativeBlockTimeContext with blockTimeSeconds := some 10} inputs {},
        ep.run {nativeBlockTimeContext with blockTimeSeconds := some 11} inputs {} with
    | .ok (before, _), .ok (equal, _), .ok (after, _) =>
      before == [("beforeDeadline", .bool Bool.true), ("afterDeadline", .bool Bool.false),
        ("atOrAfterDeadline", .bool Bool.false), ("atOrBeforeDeadline", .bool Bool.true)] &&
      equal == [("beforeDeadline", .bool Bool.false), ("afterDeadline", .bool Bool.false),
        ("atOrAfterDeadline", .bool Bool.true), ("atOrBeforeDeadline", .bool Bool.true)] &&
      after == [("beforeDeadline", .bool Bool.false), ("afterDeadline", .bool Bool.true),
        ("atOrAfterDeadline", .bool Bool.true), ("atOrBeforeDeadline", .bool Bool.false)]
    | _, _, _ => Bool.false
  | _ => Bool.false

#guard match NativeBlockTime.entrypoints with
  | [ep] =>
    let disabled := [
      ("cutoff", Value.uint (2 ^ 64 - 1) 10),
      ("enabled", Value.bool Bool.false)]
    let enabled := [
      ("cutoff", Value.uint (2 ^ 64 - 1) 10),
      ("enabled", Value.bool Bool.true)]
    match ep.run nativeBlockTimeContext disabled {}, ep.run nativeBlockTimeContext enabled {} with
    | .ok (outputs, _), .error message =>
      outputs == [("beforeDeadline", .bool Bool.false), ("afterDeadline", .bool Bool.false),
        ("atOrAfterDeadline", .bool Bool.false), ("atOrBeforeDeadline", .bool Bool.false)] &&
      message == "missing execution block time"
    | _, _ => Bool.false
  | _ => Bool.false

private def privateCutoffEntry : Entrypoint := {
  name := "privateCutoff"
  circuit := {name := "privateCutoff", inputs := [
    {name := "cutoff", ty := .uint (2 ^ 64 - 1), visibility := .«private»}]}
  effects := [.blockTimeCompare "before" Bool.true (.ref "cutoff")]
}

#guard match Disclosure.entrypoint privateCutoffEntry with
  | .error diagnostic => diagnostic.message.contains "undisclosed private parameter 'cutoff'"
  | .ok _ => Bool.false

private def privateGuardEntry : Entrypoint := {
  name := "privateGuard"
  circuit := {name := "privateGuard", inputs := [
    {name := "cutoff", ty := .uint (2 ^ 64 - 1), visibility := .«public»},
    {name := "enabled", ty := .bool, visibility := .«private»}]}
  effects := [.blockTimeCompare "before" Bool.true (.ref "cutoff")]
  effectGuards := [some (.ref "enabled")]
}

#guard match Disclosure.entrypoint privateGuardEntry with
  | .error diagnostic => diagnostic.message.contains "undisclosed private control"
  | .ok _ => Bool.false
