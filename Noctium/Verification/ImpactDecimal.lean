import Lean

namespace Noctium.Verification.ImpactDecimal

/-- Parse an unsigned decimal string only when its spelling is canonical.
Leading zeros and non-decimal forms are rejected. Callers apply field-specific
upper bounds after parsing. -/
def parseCanonical (text : String) : Option Nat := do
  let value ← text.toNat?
  if toString value == text then some value else none

/-- Every natural number's decimal rendering is accepted as itself. -/
theorem parseCanonical_toString (value : Nat) :
    parseCanonical (toString value) = some value := by
  simp [parseCanonical]

end Noctium.Verification.ImpactDecimal
