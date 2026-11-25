import Noctium.Verification.ImpactWireSoundness

namespace Noctium.Verification.ImpactTranscriptWidth

open Backend ImpactWireDecoder ImpactWireSoundness

/-- Scalar map lookups use the declared key alignment in Rust's plan. This
lookup records the width of that declaration for each state slot. -/
def ScalarKeyWidths (keyWidth : Nat → Option Nat) : Impact.Op → Prop
  | .mapIndex slot _ => keyWidth slot = some 3
  | _ => True

private def scalarAlignmentWidth : String → Option Nat
  | "field" | "bit" => some 1
  | _ => none

/-- Rust's skipped field count for one decoded scalar operation. A successful
key lookup supplies the width declared for that slot's map key. -/
def operationWidth (keyWidth : Nat → Option Nat) : Operation → Option Nat
  | .dup | .member => some 1
  | .index slot _ none =>
      if slot < 2 ^ 32 then some 4 else none
  | .index slot Bool.false (some _) =>
      if slot < 2 ^ 32 then (keyWidth slot).map (fun width => 4 + width) else none
  | .index _ Bool.true (some _) => none
  | .push _ alignment _ =>
      (scalarAlignmentWidth alignment).map (fun width => 4 + width)
  | .popeq alignment _ =>
      (scalarAlignmentWidth alignment).map (fun width => 3 + width)
  | .insert depth => if depth < 2 ^ 8 then some 1 else none

/-- The modeled skip width equals the single emitted Impact field group for
every operation recovered by `ImpactWireSoundness`, when keyed lookups use the
declared scalar key width. -/
theorem operationWidth_projects {keyWidth : Nat → Option Nat}
    {op : Impact.Op} {wire : Operation}
    (projects : ImpactWireSoundness.Projects op wire)
    (keyWidths : ScalarKeyWidths keyWidth op) :
    (operationWidth keyWidth wire).map List.singleton =
      some (op.fieldGroups.map List.length) := by
  cases projects with
  | dup => simp [operationWidth, Impact.Op.fieldGroups, Impact.Op.fields, List.singleton]
  | index slot path fits =>
      simp [operationWidth, fits, Impact.Op.fieldGroups, Impact.Op.fields,
        Impact.Aligned.fields, List.singleton]
  | mapIndex slot key fits nonNull =>
      have width : keyWidth slot = some 3 := keyWidths
      simp [operationWidth, fits, width, Impact.Op.fieldGroups, Impact.Op.fields,
        Impact.Aligned.fields, List.singleton]
  | pushField value storage =>
      simp [operationWidth, scalarAlignmentWidth, Impact.Op.fieldGroups,
        Impact.Op.fields, Impact.Aligned.fields, List.singleton]
  | pushBit value storage =>
      simp [operationWidth, scalarAlignmentWidth, Impact.Op.fieldGroups,
        Impact.Op.fields, Impact.Aligned.fields, List.singleton]
  | pushBitExpr value storage =>
      simp [operationWidth, scalarAlignmentWidth, Impact.Op.fieldGroups,
        Impact.Op.fields, Impact.Aligned.fields, List.singleton]
  | popeqField value =>
      simp [operationWidth, scalarAlignmentWidth, Impact.Op.fieldGroups,
        Impact.Op.fields, Impact.Aligned.fields, List.singleton]
  | popeqBit value =>
      simp [operationWidth, scalarAlignmentWidth, Impact.Op.fieldGroups,
        Impact.Op.fields, Impact.Aligned.fields, List.singleton]
  | popeqBitExpr value =>
      simp [operationWidth, scalarAlignmentWidth, Impact.Op.fieldGroups,
        Impact.Op.fields, Impact.Aligned.fields, List.singleton]
  | «member» => simp [operationWidth, Impact.Op.fieldGroups, Impact.Op.fields,
      List.singleton]
  | «insert» depth fits =>
      simp [operationWidth, fits, Impact.Op.fieldGroups, Impact.Op.fields,
        List.singleton]

/-- Every projected scalar operation skips a positive number of fields, with
seven as the largest width in this fragment. -/
theorem operationWidth_projects_bounds {keyWidth : Nat → Option Nat}
    {op : Impact.Op} {wire : Operation}
    (projects : ImpactWireSoundness.Projects op wire)
    (keyWidths : ScalarKeyWidths keyWidth op) :
    ∃ width, operationWidth keyWidth wire = some width ∧ 0 < width ∧ width ≤ 7 := by
  have exact := operationWidth_projects projects keyWidths
  cases result : operationWidth keyWidth wire with
  | none => simp [result] at exact
  | some width =>
      have widths := congrArg (Option.map List.sum) exact
      have widthEq : width = (op.fieldGroups.map List.length).sum := by
        simpa [result, List.singleton] using widths
      refine ⟨width, rfl, ?_⟩
      cases projects <;>
        simp [Impact.Op.fieldGroups, Impact.Op.fields, Impact.Aligned.fields] at widthEq <;>
        omega

end Noctium.Verification.ImpactTranscriptWidth
