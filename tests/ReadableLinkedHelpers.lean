import Noctium.Frontend

open scoped Noctium
open Noctium Noctium.Helpers

private def linkedOuter : Helpers.Program := {
  scopes := [{id := 0}, {id := 1, parent := some 0}]
  declarations := [
    {id := ⟨0, 0⟩, name := "calculate",
      parameters := [⟨"x", .native⟩, ⟨"y", .native⟩], result := .scalar .native,
      body := [.return (some (.call "combine" [.ref "x", .ref "y"]))]},
    {id := ⟨1, 0⟩, name := "privateOuter", parameters := [⟨"x", .native⟩],
      result := .scalar .native, body := [.return (some (.ref "x"))]}]
  exports := [{name := "outer", target := ⟨0, 0⟩}]
}

private def linkedCombine : Helpers.Program := {
  scopes := [{id := 0}]
  declarations := [{
    id := ⟨0, 0⟩, name := "combine",
    parameters := [⟨"left", .native⟩, ⟨"right", .native⟩], result := .scalar .native,
    body := [.return (some (.call "weighted" [.ref "right", .ref "left"]))]}]
  exports := [{name := "combine", target := ⟨0, 0⟩}]
}

private def linkedWeighted : Helpers.Program := {
  scopes := [{id := 0}, {id := 1, parent := some 0}]
  declarations := [
    {id := ⟨0, 0⟩, name := "weighted",
      parameters := [⟨"left", .native⟩, ⟨"right", .native⟩], result := .scalar .native,
      body := [.return (some (.binary .add
        (.binary .mul (.ref "left") (.native 100)) (.ref "right")))]},
    {id := ⟨1, 0⟩, name := "privateWeighted", parameters := [⟨"x", .native⟩],
      result := .scalar .native, body := [.return (some (.ref "x"))]}]
  exports := [{name := "weighted", target := ⟨0, 0⟩}]
}

noctium_witness_circuit linkedHelpers with linkedOuter, linkedCombine, linkedWeighted where
  public x : Native
  public y : Native
  output answer : Native := disclose(invoke(calculate, [x, y]))
end

noctium_contract LinkedHelperContract where
  entry calculate uses linkedHelpers where
    return result : Native := answer
  end
end

private def duplicateWeighted : Helpers.Program := {
  scopes := [{id := 0}]
  declarations := [{
    id := ⟨0, 0⟩, name := "weighted",
    parameters := [⟨"left", .native⟩, ⟨"right", .native⟩], result := .scalar .native,
    body := [.return (some (.ref "left"))]}]
  exports := [{name := "weighted", target := ⟨0, 0⟩}]
}

/- error: ambiguous helper overload 'weighted' -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsAmbiguousHelper with linkedOuter, linkedCombine,
    linkedWeighted, duplicateWeighted where
  public x : Native
  public y : Native
  output answer : Native := disclose(invoke(calculate, [x, y]))
end

#guard LinkedHelperContract.entrypoints.length == 1
#guard linkedHelpers.__program.declarations.map (·.id) ==
  [⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨2, 0⟩, ⟨0, 3⟩]
