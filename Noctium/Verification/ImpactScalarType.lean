import Noctium.NativeExpression
import Noctium.ScalarPolicy
import Noctium.Verification.ImpactDecimal

namespace Noctium.Verification.ImpactScalarType

open Noctium

private def uintRangePrefix : String := "UIntRange<"

private theorem renderedUIntRange_prefix (text : String) :
    ((uintRangePrefix ++ text ++ ">").toList.take uintRangePrefix.length) =
      uintRangePrefix.toList := by
  rw [String.toList_append, String.toList_append, List.append_assoc,
    ← String.length_toList]
  simp

private theorem renderedUIntRange_last (text : String) :
    (uintRangePrefix ++ text ++ ">").toList.getLast? = some '>' := by
  rw [String.toList_append, String.toList_append, List.append_assoc]
  simp

private theorem renderedUIntRange_payload (text : String) :
    String.ofList (((uintRangePrefix ++ text ++ ">").toList.drop
      uintRangePrefix.length).dropLast) = text := by
  rw [String.toList_append, String.toList_append, List.append_assoc,
    ← String.length_toList]
  change String.ofList (List.dropLast
    ((uintRangePrefix.toList ++ text.toList ++ ['>']).drop
      uintRangePrefix.toList.length)) = _
  simp [List.append_assoc]

/-- Parse the exclusive bound from Rust's `UIntRange<n>` scalar type name.
The wire spelling must be canonical and the inclusive maximum must fit Rust's
248-bit unsigned range. -/
private def parseUIntExclusive (name : String) : Option Nat := do
  let characters := name.toList
  if characters.take uintRangePrefix.length != uintRangePrefix.toList ||
      characters.getLast? != some '>' then none else
  let exclusive ← ImpactDecimal.parseCanonical (String.ofList
    ((characters.drop uintRangePrefix.length).dropLast))
  if exclusive == 0 || exclusive > ScalarPolicy.maxUint + 1 then none
  some exclusive

/-- Parse the scalar type names emitted by `NativeExpression.typeName` for the
scalar forms used by the Impact expression decoder. -/
def parseScalarTypeName (name : String) : Option Ty :=
  match name.toList with
  | 'N' :: _ => if name == "Native" then some .native else none
  | 'B' :: _ => if name == "Bool" then some .bool else none
  | _ => do
      let exclusive ← parseUIntExclusive name
      some (.uint (exclusive - 1))

private theorem parseUIntExclusive_rendered (exclusive : Nat)
    (withinRustBound : exclusive ≤ ScalarPolicy.maxUint + 1)
    (positive : 0 < exclusive) :
    parseUIntExclusive (uintRangePrefix ++ exclusive.repr ++ ">") =
      some exclusive := by
  unfold parseUIntExclusive
  dsimp
  rw [renderedUIntRange_prefix, renderedUIntRange_last,
    renderedUIntRange_payload]
  have canonical : ImpactDecimal.parseCanonical exclusive.repr = some exclusive := by
    simpa using ImpactDecimal.parseCanonical_toString exclusive
  simp [canonical, Nat.ne_of_gt positive,
    Nat.not_lt_of_ge withinRustBound]

theorem parseScalarTypeName_native :
    parseScalarTypeName (NativeExpression.typeName .native) = some .native := by
  rfl

theorem parseScalarTypeName_bool :
    parseScalarTypeName (NativeExpression.typeName .bool) = some .bool := by
  rfl

theorem parseScalarTypeName_uint (maximum : Nat)
    (withinRustBound : maximum ≤ ScalarPolicy.maxUint) :
    parseScalarTypeName (NativeExpression.typeName (.uint maximum)) =
      some (.uint maximum) := by
  change parseScalarTypeName (uintRangePrefix ++ (maximum + 1).repr ++ ">") =
    some (.uint maximum)
  have chars : (uintRangePrefix ++ (maximum + 1).repr ++ ">").toList =
      'U' :: (['I','n','t','R','a','n','g','e','<'] ++
        (maximum + 1).repr.toList ++ ['>']) := by
    rw [String.toList_append, String.toList_append]
    rfl
  unfold parseScalarTypeName
  rw [chars]
  change (parseUIntExclusive (uintRangePrefix ++ (maximum + 1).repr ++ ">") >>= _) = _
  rw [parseUIntExclusive_rendered (maximum + 1) (by omega) (by omega)]
  rfl

/-- A single equation covering every emitted scalar type within Rust's
unsigned bound. Other `Ty` forms remain outside this parser's domain. -/
theorem parseScalarTypeName_typeName (ty : Ty)
    (supported : ty = .native ∨ ty = .bool ∨
      ∃ maximum, ty = .uint maximum ∧ maximum ≤ ScalarPolicy.maxUint) :
    parseScalarTypeName (NativeExpression.typeName ty) = some ty := by
  rcases supported with native | bool | ⟨maximum, rfl, bound⟩
  · subst ty
    exact parseScalarTypeName_native
  · subst ty
    exact parseScalarTypeName_bool
  · exact parseScalarTypeName_uint maximum bound

end Noctium.Verification.ImpactScalarType
