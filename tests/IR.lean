import Noctium.Semantics

open Noctium

private def caps : Capabilities := {stateCells := true, stateMaps := true}
private def ctx : EvalContext := {
  modulus := 17
  poseidon2 := fun _ _ _ => .error "unqualified hash"
}
private def publicInput : Input := ⟨"root", .native, .«public», {}⟩
private def secretInput : Input := ⟨"secret", .native, .«private», {}⟩
private def circuit : Circuit := {
  name := "relation"
  inputs := [publicInput, secretInput]
  outputs := [⟨"result", .native, .add (.ref "root") (.native 1), {}⟩]
  constraints := [.bool true]
}
private def entry : Entrypoint := {
  name := "call"
  circuit
  effects := [.requireAbsent "spent" .native (.ref "result"),
    .writeMap "spent" .native .bool (.ref "result") (.bool true)]
}
private def contract : Contract := {
  name := "sample"
  state := [{name := "spent", kind := .map .native .bool}]
  entrypoints := [entry]
}

-- Typed relation and public state effect validation succeeds.
#guard match contract.validate caps with | .ok _ => true | _ => false
-- Wrong reference types are rejected despite well-typed AST constructors.
#guard match (Expr.ref "secret" : Expr .bool).validate caps [("secret", .native)] with
  | .error _ => true | _ => false
-- Direct private witness access from a state write is forbidden.
private def leakingEntry : Entrypoint := {entry with effects := [
  .writeMap "spent" .native .bool (.ref "secret") (.bool true)]}
#guard match Disclosure.entrypoint leakingEntry with | .error _ => true | _ => false
-- Public output binding must not shadow an input.
#guard match ({entry with circuit := {circuit with outputs := [
  ⟨"root", .native, .native 3, {}⟩]}} : Entrypoint).validate caps contract.state with
  | .error _ => true | _ => false

private def inputs : EvalEnv := [("root", .native 4), ("secret", .native 9)]
private def emptyState : LedgerState := {maps := [("spent", [])]}
#guard match entry.run ctx inputs emptyState with
  | .ok ([("result", .native 5)], state) =>
    state.maps.lookup "spent" == some [(.native 5, .bool true)]
  | _ => false
-- Replay is rejected by the reference state transition.
#guard match entry.run ctx inputs emptyState with
  | .ok (_, state) => match entry.run ctx inputs state with | .error _ => true | _ => false
  | _ => false
-- Private-state leakage also fails when bypassing static validation.
#guard match leakingEntry.run ctx inputs emptyState with | .error _ => true | _ => false
-- Noncanonical field constants must not silently alias canonical values.
#guard match (Expr.native 17).eval ctx [] with | .error _ => true | _ => false
-- Missing hash implementation fails, preventing a fake cryptographic success.
#guard match (Expr.poseidon2 1 (.native 2) (.native 3)).eval ctx [] with
  | .error _ => true | _ => false
-- Unused invalid branches still lower to circuit operations and must evaluate.
#guard match (Expr.select (.bool true) (.native 1)
    (.poseidon2 1 (.native 2) (.native 3))).eval ctx [] with
  | .error _ => true | _ => false
-- Extra caller values cannot supply undeclared relation references.
#guard match ({circuit with constraints := [.eq (.ref "extra" : Expr .native) (Expr.native 1)]} : Circuit).run
    ctx (inputs ++ [("extra", Value.native 1)]) with
  | .error _ => true | _ => false
#guard match circuit.run ctx (inputs ++ [("extra", Value.native 1)]) with
  | .error _ => true | _ => false
-- Public evaluator does not create uninitialized cells or maps on writes.
#guard match runEffects ctx [.writeCell "missing" .native (.native 1)] [] {} with
  | .error _ => true | _ => false
#guard match runEffects ctx [.writeMap "missing" .native .bool (.native 1) (.bool true)] [] {} with
  | .error _ => true | _ => false
