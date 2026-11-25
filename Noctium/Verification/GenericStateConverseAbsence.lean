import Noctium.Verification.GenericStateSourceTrace
import Noctium.Verification.GenericStateAbsenceAuthentication

namespace Noctium.Verification.GenericStateConverseAbsence
open Backend NativeRelation ScalarNormalization NativeState GenericStateEncoding

private theorem encoded_map_slot (declarations : List StateDecl)
    (current : LedgerState) (slots : List Slot) (slot : Nat)
    (declaration : StateDecl) (name : String) (keyTy valueTy : Ty)
    (entries : List (Value × Value))
    (declared : declarations[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .map keyTy valueTy)
    (encoded : encodeState declarations current = some slots)
    (lookup : current.maps.lookup name = some entries) :
    ∃ nativeEntries, entries.mapM (encodeMapEntry keyTy valueTy) = some nativeEntries ∧
      slots[slot]? = some (.map nativeEntries) := by
  have inRange : slot < declarations.length := List.getElem?_eq_some_iff.mp declared |>.1
  have slotsRange : slot < slots.length := by
    rw [encodeState_length declarations current slots encoded]
    exact inRange
  have slotEncoding := encodeState_slot declarations current slots slot encoded
  rw [declared] at slotEncoding
  simp only [Option.bind_some] at slotEncoding
  cases mapped : entries.mapM (encodeMapEntry keyTy valueTy) with
  | none =>
    have absent : slots[slot]? = none := by
      simpa [encodeDeclaration, named, kind, lookup, mapped] using slotEncoding
    exact False.elim (Nat.not_le_of_gt slotsRange (List.getElem?_eq_none_iff.mp absent))
  | some nativeEntries =>
    by_cases unique : (nativeEntries.map Prod.fst).eraseDups.length = nativeEntries.length
    · refine ⟨nativeEntries, rfl, ?_⟩
      simpa [encodeDeclaration, named, kind, lookup, mapped, unique] using slotEncoding
    · have absent : slots[slot]? = none := by
        simpa [encodeDeclaration, named, kind, lookup, mapped, unique] using slotEncoding
      exact False.elim (Nat.not_le_of_gt slotsRange (List.getElem?_eq_none_iff.mp absent))

/-- Original source absence drives the exact compiled segment and a successful
native missing-key check, with arbitrary source declaration spans. -/
theorem source_requireAbsent_native (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List Slot)
    (name : String) (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (admission : ScalarExpression keyExpr)
    (sourceAfter : SourceEffects.Frame) (base : Impact.Plan) (reads : List Cell)
    (sourceStep : SourceEffects.step ctx (.requireAbsent name keyTy keyExpr)
      (sourceEnv, current) = .ok sourceAfter)
    (candidateAgreement : keyExpr.eval ctx candidateEnv = keyExpr.eval ctx sourceEnv)
    (declaration : StateDecl)
    (declared : state.find? (·.name == name) = some declaration)
    (named : declaration.name = name) (kind : declaration.kind = .map keyTy valueTy)
    (compiled : Impact.appendEffect state (.requireAbsent name keyTy keyExpr) {} = .ok base)
    (encoded : encodeState state current = some slots)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ slot key, state.findIdx? (·.name == name) = some slot ∧
      base.operations.mapM (GenericStateOps.evalOp ctx candidateEnv) =
        .ok (GenericStateVM.requireAbsentOps slot (scalar (number keyTy key))) ∧
      run (GenericStateVM.requireAbsentOps slot (scalar (number keyTy key)))
        ⟨[.vector slots], reads⟩ = some ⟨[.vector slots], reads ++ [boolean false]⟩ ∧
      sourceAfter = (sourceEnv, current) := by
  obtain ⟨key, entries, keyEval, canonical, lookup, missing, sourceShape⟩ :=
    GenericStateSourceTrace.requireAbsent_step_key ctx sourceEnv current name keyTy keyExpr
      admission sourceAfter modulus sourceStep
  have candidateEval : keyExpr.eval ctx candidateEnv = .ok key := by
    rw [candidateAgreement]
    exact keyEval
  obtain ⟨slot, located, segmentEval⟩ :=
    GenericStateAbsenceAuthentication.requireAbsent_candidate_eval state name keyTy keyExpr
      base ctx candidateEnv key compiled modulus candidateEval canonical
  have declarationAt : state[slot]? = some declaration := by
    rw [List.find?_eq_bind_findIdx?_getElem?, located] at declared
    exact declared
  obtain ⟨nativeEntries, mapped, slotFound⟩ := encoded_map_slot state current slots slot
    declaration name keyTy valueTy entries declarationAt named kind encoded lookup
  have absent := sourceMap_absent keyTy valueTy entries nativeEntries key canonical mapped missing
  exact ⟨slot, key, located, segmentEval,
    GenericStateVM.requireAbsent_exact slots slot nativeEntries (scalar (number keyTy key))
      reads slotFound absent, sourceShape⟩

end Noctium.Verification.GenericStateConverseAbsence
