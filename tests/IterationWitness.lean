import Noctium.Frontend

open scoped Noctium
open Noctium Noctium.Helpers

private def iterationSource : Except Diagnostic Program := do
  let sequenceType := Types.CompositeType.tuple [
    .tuple [.scalar (.uint 3), .scalar .native],
    .tuple [.scalar .native, .scalar (.uint 3)],
    .tuple [.scalar (.uint 7), .scalar (.uint 3)]]
  let item := Types.CompositeType.structure "Iteration.Item"
  let amount := Types.CompositeType.enumeration "Iteration.Amount"
  let receipt := Types.CompositeType.structure "Iteration.Receipt"
  let receiptValue := fun total : Term => Term.composite receipt [
    total, .bool Bool.true, .bool Bool.false,
    .select (.eq total (.native 0)) (.native 0) (.native 1),
    .cast (.uint 31) total, .uint 255 7, .uint 255 9,
    .disclose {} (.ref "offset")]
  let base : Program := {
    composites := {
      structures := [{id := "Iteration.Item", fields := [
        {name := "amount", type := amount},
        {name := "metadata", type := .vector 2 (.scalar .native)}]},
        {id := "Iteration.Receipt", fields := [
          {name := "total", type := .scalar .native},
          {name := "flags", type := .vector 2 (.scalar .bool)},
          {name := "claim", type := .enumeration "Iteration.Claim"},
          {name := "audit", type := .tuple [.bytes 2, .unit]},
          {name := "releasedOffset", type := .scalar .native}]}]
      enumerations := [{id := "Iteration.Amount", variants := [
        {name := "Empty"}, {name := "Full", fields := [
          {name := "value", type := .scalar .native}]}]},
        {id := "Iteration.Claim", variants := [
          {name := "Empty"}, {name := "Applied", fields := [
            {name := "amount", type := .scalar (.uint 31)}]}]}]}
    ledger := [{name := "total", kind := .cell .native}]
    witnesses := [
      {name := "touch", operation := "noctium.iteration-touch.v1", capability := "touch",
        result := .unit},
      {name := "seed", operation := "noctium.iteration-seed.v1", capability := "seed",
        result := .scalar .native},
      {name := "values", operation := "noctium.iteration-values.v1", capability := "values",
        result := .composite sequenceType},
      {name := "double", operation := "noctium.iteration-double.v1", capability := "double",
        parameters := [{name := "value", type := .scalar .native}], result := .scalar .native}]
    declarations := [{
      id := ⟨0, 0⟩, name := "update",
      parameters := [⟨"enabled", .bool⟩, ⟨"expected", .native⟩, ⟨"offset", .native⟩,
        ⟨"rootUnit", .native⟩],
      compositeParameters := [("rootUnit", .unit)],
      result := .composite receipt, body := [.return (some (receiptValue (.native 0)))]}]
    exports := [{
      name := "update", target := ⟨0, 0⟩
      inputs := [
        {name := "enabled", ty := .bool, visibility := .private},
        {name := "expected", ty := .native, visibility := .public},
        {name := "offset", ty := .native, visibility := .private}]
      compositeInputs := [{name := "rootUnit", type := .unit, visibility := .private}]}]
  }
  let env : Environment := [
    ("enabled", .scalar .bool), ("expected", .scalar .native), ("offset", .scalar .native),
    ("u", .unit), ("rootUnit", .unit)]
  let (seedProgram, initial) ← Iteration.applyWithLimits {} base 0 env {}
    (.anonymous [{name := "unitArg"}] none [
      .evaluate (.ref "unitArg"),
      .return (some (.witnessCall "initial-seed" "seed" []))]) [.ref "u"]
  let (mappedProgram, mapped) ← Iteration.mapWithLimits {} seedProgram 0 env {}
    [.witnessCall "input-values" "values" []]
    (.anonymous [{name := "pair"}] none [
      .evaluate (.ref "u"),
      .evaluate (.ref "rootUnit"),
      .bind "value" (.scalar .native) (.binary .add
        (.project (.ref "pair") (.tupleIndex 0))
        (.project (.ref "pair") (.tupleIndex 1))),
      .bind "shifted" (.scalar .native) (.binary .add (.ref "value") (.ref "offset")),
      .bind "doubled" (.scalar .native) (.witnessCall "double-value" "double" [.ref "shifted"]),
      .bind "amount" (.composite amount) (.composite amount [
        .select (.eq (.ref "value") (.native 2)) (.native 0) (.native 1),
        .select (.eq (.ref "value") (.native 2)) (.native 0) (.ref "doubled")]),
      .return (some (.composite item [
        .project (.ref "amount") .enumTag,
        .ite (.eq (.project (.ref "amount") .enumTag) (.native 1))
          (.project (.ref "amount") (.enumField "Full" "value")) (.native 0),
        .ref "shifted", .ref "value"]))])
  let (foldedProgram, folded) ← Iteration.foldWithLimits {} mappedProgram 0 env {}
    initial [mapped, .bytes (.bytesLiteral 3 [1, 2, 3]) []]
    (.anonymous [{name := "acc"}, {name := "value"}, {name := "fee"}] none [
      .bind "amount" (.composite amount) (.project (.ref "value") (.field "amount")),
      .return (some (.binary .add
        (.binary .add (.ref "acc")
          (.ite (.eq (.project (.ref "amount") .enumTag) (.native 1))
            (.project (.ref "amount") (.enumField "Full" "value")) (.native 0)))
        (.cast .native (.ref "fee"))))])
  pure {foldedProgram with declarations := foldedProgram.declarations.map fun declaration =>
    if declaration.id == ⟨0, 0⟩ then {declaration with body := [
      .branch (.disclose {} (.ref "enabled")) [
        .bind "u" .unit (.witnessCall "unit-touch" "touch" []),
        .bind "sum" (.scalar .native) folded,
        .assert (.eq (.ref "sum") (.ref "expected")),
        .writeCell "total" .native (.disclose {} (.ref "sum")),
        .stage "private" "iteration/last" (.scalar .native) (.ref "sum")] [],
      .readCell "total" "after" .native,
      .return (some (receiptValue (.ref "after")))]}
    else declaration}

#guard iterationSource.isOk

private def iterationProgram : Program :=
  match iterationSource with
  | .ok program => program
  | .error _ => {}

noctium_contract IterationWitness where
  cell total : Native
  entry update from iterationProgram entry "update" end
end

private def withoutWriteReleases : List Statement → List Statement
  | [] => []
  | .writeCell state ty (.disclose _ value) :: rest =>
    .writeCell state ty value :: withoutWriteReleases rest
  | .branch condition yes no :: rest =>
    .branch condition (withoutWriteReleases yes) (withoutWriteReleases no) :: withoutWriteReleases rest
  | statement :: rest => statement :: withoutWriteReleases rest
termination_by body => sizeOf body

#guard match Witness.compileStateEntrypoint
    (Helpers.mapDeclarationBodies withoutWriteReleases iterationProgram) "update" iterationProgram.ledger with
  | .error diagnostic => (diagnostic.message.splitOn "private").length > 1
  | .ok _ => Bool.false

private def withoutReturnReleases (body : List Statement) : List Statement :=
  body.map fun
    | .return (some (.composite type leaves)) =>
      .return (some (.composite type (leaves.map fun
        | .disclose _ value => value
        | value => value)))
    | statement => statement

#guard match Witness.compileStateEntrypoint
    (Helpers.mapDeclarationBodies withoutReturnReleases iterationProgram) "update" iterationProgram.ledger with
  | .error diagnostic => (diagnostic.message.splitOn "private").length > 1
  | .ok _ => Bool.false

#guard IterationWitness.entrypoints.length == 1
