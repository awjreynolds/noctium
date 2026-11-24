import Noctium.Frontend

open Noctium.Helpers
open scoped Noctium

private def declaredPureProgram : Program := {
  declarations := [
    {id := ⟨0, 0⟩, name := "calculate", declaredPure := Bool.true,
      parameters := [⟨"value", .native⟩, ⟨"expected", .native⟩],
      result := .scalar .native,
      body := [
        .bind "small" (.scalar (.uint 255)) (.cast (.uint 255) (.ref "value")),
        .assert (.eq (.cast .native (.ref "small")) (.ref "expected")),
        .return (some (.call "increment" [.cast .native (.ref "small")]))]},
    {id := ⟨0, 1⟩, name := "increment", parameters := [⟨"value", .native⟩],
      result := .scalar .native,
      body := [.return (some (.binary .add (.ref "value") (.native 1)))]}]
  exports := [{name := "calculate", target := ⟨0, 0⟩, inputs := [
    {name := "value", ty := .native, visibility := .public},
    {name := "expected", ty := .native, visibility := .public}]}]
}

noctium_helper_circuit checkedPureHelper from declaredPureProgram entry "calculate"

noctium_contract PureHelpers where
  entry calculate uses checkedPureHelper where
    return answer : Native := result
  end
end
