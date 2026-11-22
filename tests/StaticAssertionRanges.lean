import Noctium.Frontend

open Noctium.Helpers

private abbrev Ty := Noctium.Ty
private abbrev Expr := Noctium.Expr
private abbrev Effect := Noctium.Effect
private abbrev Visibility := Noctium.Visibility

private def assertionProgram (stop : Nat) (body : List Statement)
    (visibility : Visibility := .private) : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "main"
    parameters := [⟨"amount", .native⟩]
    result := .unit
    body := [.forRange "index" 0 stop body, .return none]
  }]
  exports := [{name := "main", target := ⟨0, 0⟩, inputs := [
    {name := "amount", ty := .native, visibility}]}]
}

private def varyingCondition : Term :=
  .eq (.binary .add (.ref "index") (.ref "amount")) (.native 0)

private def positiveProgram : Program :=
  assertionProgram 1200 [.assert varyingCondition]

private def staticAssertionConstraintIndex : Expr .bool → Option (String × Nat)
  | .letE inputLocal (.ref "amount")
      (.letE indexLocal (.native index)
        (.eq (.eq (.add (.ref indexRef) (.ref amountRef)) (.native 0)) (.bool true))) =>
      if inputLocal == amountRef && indexLocal == indexRef then some (inputLocal, index)
      else none
  | _ => none

private def constraintsAreOrdered (constraints : List (Expr .bool)) : Bool :=
  match constraints.take 1200 with
  | first :: rest =>
    match staticAssertionConstraintIndex first with
    | some (inputLocal, 0) => rest.zipIdx.all fun (constraint, expectedIndex) =>
      match staticAssertionConstraintIndex constraint with
      | some (actualInput, actualIndex) =>
        actualInput == inputLocal && actualIndex == expectedIndex + 1
      | none => false
    | _ => false
  | _ => false

private def ledgerRequirementIndex : Effect → Option (String × Nat)
  | .require (.letE inputLocal (.ref "amount")
      (.letE indexLocal (.native index)
        (.eq (.add (.ref indexRef) (.ref amountRef)) (.native 0)))) =>
      if inputLocal == amountRef && indexLocal == indexRef then some (inputLocal, index)
      else none
  | _ => none

private def ledgerRequirementsAreOrdered (effects : List Effect) : Bool :=
  match effects.take 1200 with
  | first :: rest =>
    match ledgerRequirementIndex first with
    | some (inputLocal, 0) => rest.zipIdx.all fun (effect, expectedIndex) =>
      match ledgerRequirementIndex effect with
      | some (actualInput, actualIndex) =>
        actualInput == inputLocal && actualIndex == expectedIndex + 1
      | none => false
    | _ => false
  | _ => false

#guard match compile positiveProgram "main" with
  | .ok circuit =>
    circuit.constraints.length == 1201 && constraintsAreOrdered circuit.constraints &&
      circuit.outputs.isEmpty && circuit.inputs.length == 1 &&
      circuit.inputs.head?.map (·.visibility == .private) == some true
  | .error _ => _root_.Bool.false

#guard (compile (assertionProgram 1025 [.assert varyingCondition]) "main").isOk

#guard match compileEntrypoint positiveProgram "main" with
  | .ok entry => entry.effects.length == 1200 &&
      ledgerRequirementsAreOrdered entry.effects && entry.circuit.constraints.isEmpty
  | .error _ => _root_.Bool.false

private def overBudgetProgram : Program := assertionProgram 1100 [
  .assert varyingCondition,
  .assert varyingCondition,
  .assert varyingCondition]

#guard match prepareProgramWithLimits {} overBudgetProgram with
  | .error diagnostic => diagnostic.message == "helper resource limit exceeded: expanded source nodes"
  | .ok _ => _root_.Bool.false

private def repeatedCalleeProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "manyAssertions"
    parameters := [⟨"amount", .native⟩]
    result := .unit
    body := [.forRange "index" 0 1200 [.assert varyingCondition], .return none]
  }, {
    id := ⟨0, 1⟩
    name := "main"
    parameters := [⟨"amount", .native⟩]
    result := .unit
    body := [
      .evaluate (.call "manyAssertions" [.ref "amount"]),
      .evaluate (.call "manyAssertions" [.ref "amount"]),
      .evaluate (.call "manyAssertions" [.ref "amount"]),
      .return none]
  }]
  exports := [{name := "main", target := ⟨0, 1⟩, inputs := [
    {name := "amount", ty := .native, visibility := .private}]}]
}

#guard match analyze repeatedCalleeProgram with
  | .error diagnostic => diagnostic.message == "helper resource limit exceeded: expanded nodes"
  | .ok _ => _root_.Bool.false

private def deepCondition : Term :=
  .eq ((List.range 130).foldl (fun value _ => .cast .native value) (.ref "amount"))
    (.ref "amount")

#guard match prepareProgramWithLimits {} (assertionProgram 1 [.assert deepCondition]) with
  | .error diagnostic => diagnostic.message == "helper resource limit exceeded: source depth"
  | .ok _ => _root_.Bool.false

private def effectfulProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "main"
    result := .unit
    body := [
      .forRange "index" 0 3 [
        .evaluate (.effect .witness "witness-before" .unit),
        .evaluate (.effect .privateState "private-after" .unit)],
      .return none]
  }]
  exports := [{name := "main", target := ⟨0, 0⟩}]
}

private def traceContext : Noctium.EvalContext := {
  modulus := Noctium.Field.modulus
  poseidon2 := fun _ _ _ => .error "unused"
}

#guard match trace effectfulProgram traceContext "main" [] with
  | .ok (_, events) =>
    events == ["witness-before", "private-after", "witness-before", "private-after",
      "witness-before", "private-after"]
  | .error _ => _root_.Bool.false

#guard match compile effectfulProgram "main" with
  | .error diagnostic =>
    diagnostic.message == "native helper capability unavailable: witness-dependent guarded control (CF-02)"
  | .ok _ => _root_.Bool.false

#guard match trace (assertionProgram 1 [.assert varyingCondition]) traceContext "main"
    [⟨.native, 0⟩] with
  | .ok _ => true
  | .error _ => _root_.Bool.false

#guard match trace (assertionProgram 1 [.assert varyingCondition]) traceContext "main"
    [⟨.native, 1⟩] with
  | .error diagnostic => diagnostic.message == "helper assertion failed"
  | .ok _ => _root_.Bool.false

#guard match prepareProgramWithLimits {} (assertionProgram 1200 [.evaluate (.native 1)]) with
  | .error diagnostic => diagnostic.message == "helper resource limit exceeded: finite range length"
  | .ok _ => _root_.Bool.false

#guard match prepareProgramWithLimits {}
    (assertionProgram 1024 [.forRange "inner" 0 1024 [.assert varyingCondition]]) with
  | .error diagnostic => diagnostic.message == "helper resource limit exceeded: expanded source nodes"
  | .ok _ => _root_.Bool.false
