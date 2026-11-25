import Noctium.Verification.GenericStateReadCellEvaluation
import Noctium.Verification.GenericStateInputValues
import Noctium.Verification.GenericStateSchemaSpans
import Noctium.Verification.ScalarValidationMeaning

namespace Noctium.Verification.GenericStateReadAuthentication
open Backend NativeRelation ScalarNormalization NativeState
open GenericStateCellAdmission GenericStateInputValues

private theorem sourceCanonical (ctx : EvalContext) (ty : Ty)
    (value : ty.Denote) (modulus : ctx.modulus = Field.modulus)
    (canonical : Canonical ty value) :
    SourceEffects.canonicalValue ctx ty value = true := by
  cases ty with
  | native =>
    simpa [SourceEffects.canonicalValue, Canonical, sourceNumber?, modulus] using canonical.1
  | bool => rfl
  | uint maximum =>
    rcases canonical with ⟨bound, maximumBound, valueBound⟩
    have fieldBound : value < Field.modulus := by simpa [number] using bound
    simp [SourceEffects.canonicalValue, modulus, fieldBound,
      maximumBound, valueBound]
  | _ => simp [Canonical, sourceNumber?] at canonical

private theorem scalarCellType_of_canonical {ty : Ty} {value : ty.Denote}
    (canonical : Canonical ty value) : Nonempty (ScalarCellType ty) := by
  cases ty with
  | native => exact ⟨.native⟩
  | bool => exact ⟨.bool⟩
  | uint maximum => exact ⟨.uint maximum canonical.2.1⟩
  | _ => simp [Canonical, sourceNumber?] at canonical

/-- A checked production cell-read segment authenticates the typed relation
candidate against the current source ledger slot. Earlier writes are allowed,
since the premise encodes the current tentative source state. -/
theorem readCell_candidate_source_step (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name destination : String) (ty : Ty)
    (base : Impact.Plan) (segment : List NativeState.Op)
    (slot : Nat) (candidate : ty.Denote)
    (reads : List NativeState.Cell) (after : NativeState.Machine)
    (compiled : Impact.appendEffect state (.readCell name destination ty) {} = .ok base)
    (found : state.findIdx? (·.name == name) = some slot)
    (declaration : StateDecl)
    (declarationAt : state[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .cell ty)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (lookup : candidateEnv.lookup destination = some (Value.pack ty candidate))
    (canonical : Canonical ty candidate)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : base.operations.mapM (GenericStateOps.evalOp ctx candidateEnv) =
      .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after) :
    SourceEffects.step ctx (.readCell name destination ty) (sourceEnv, current) =
      .ok ((destination, Value.pack ty candidate) :: sourceEnv, current) ∧
    after = ⟨[.vector slots], reads ++
      [NativeState.field (scalar (GenericStateEncoding.number ty candidate))]⟩ := by
  obtain ⟨scalarType⟩ := scalarCellType_of_canonical canonical
  have alignment := GenericStateSchemaSpans.encoded_cell_alignment_none state current slots
    slot declaration ty declarationAt kind encoded
  have sourceFound : state.find? (·.name == name) = some declaration := by
    rw [List.find?_eq_bind_findIdx?_getElem?, found]
    exact declarationAt
  have scalarDeclaration : ScalarCellDeclaration state name ty :=
    ⟨declaration, sourceFound, kind, alignment⟩
  obtain ⟨actualSlot, actualFound, actualEval⟩ :=
    GenericStateReadCellEvaluation.readCell_candidate_eval state name destination
      ty base ctx candidateEnv candidate scalarType scalarDeclaration compiled lookup modulus canonical
  rw [found] at actualFound
  have sameSlot : actualSlot = slot := (Option.some.inj actualFound).symm
  subst actualSlot
  rw [actualEval] at evaluated
  cases evaluated
  obtain ⟨value, sourceLookup, sourceCanonicalValue, sameCell, final⟩ :=
    GenericStateSchemaSpans.readCell_source_typed state current slots slot
      declaration name ty
      (NativeState.field (scalar (GenericStateEncoding.number ty candidate))) reads after
      declarationAt named kind encoded checked
  have sameEncoding :
      GenericStateEncoding.encodeValue ty (Value.pack ty candidate) =
        GenericStateEncoding.encodeValue ty (Value.pack ty value) := by
    rw [GenericStateEncoding.encodeValue_pack ty candidate canonical,
      GenericStateEncoding.encodeValue_pack ty value sourceCanonicalValue]
    exact congrArg some sameCell
  have equal := GenericStateEncoding.encodeValue_pack_injective ty
    candidate value canonical sourceCanonicalValue sameEncoding
  subst value
  have checkedCanonical := sourceCanonical ctx ty candidate modulus canonical
  unfold SourceEffects.canonicalValue at checkedCanonical
  constructor
  · cases scalarType <;>
      simp [SourceEffects.step, runEffectWithEnv, sourceLookup,
        number_pack_as _ candidate canonical, canonical_eq, checkedCanonical] <;> rfl
  · exact final

private theorem append_readCell_readIdentity (state : List StateDecl)
    (name destination : String) (ty : Ty) (base : Impact.Plan)
    (compiled : Impact.appendEffect state (.readCell name destination ty) {} = .ok base) :
    ∃ read, base.reads = [read] ∧ read.name = destination ∧ read.ty = ty := by
  simp only [Impact.appendEffect, ScalarValidationMeaning.bind_ok] at compiled
  rcases compiled with ⟨slot, _, value, _, result⟩
  have same := Except.ok.inj result
  subst base
  exact ⟨_, rfl, rfl, rfl⟩

private theorem sourceScalar_eq_field {ty : Ty} (scalarType : ScalarType ty)
    (value : ty.Denote) :
    sourceScalar? ty value = some (scalar (GenericStateEncoding.number ty value)) := by
  cases scalarType <;> rfl

/-- The read segment authenticates the exact witness scalar decoded from its
sole produced read descriptor. The VM consumes the current ledger encoding,
so this result also applies after an earlier source effect changes the cell. -/
theorem readCell_decoded_source_step (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name destination : String) (ty : Ty) (base : Impact.Plan)
    (segment : List NativeState.Op) (slot : Nat)
    (reads : List NativeState.Cell) (after : NativeState.Machine)
    (witness : Assignment)
    (compiled : Impact.appendEffect state (.readCell name destination ty) {} = .ok base)
    (found : state.findIdx? (·.name == name) = some slot)
    (declaration : StateDecl)
    (declarationAt : state[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .cell ty)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (decoded : decodeReads base.reads witness = .ok candidateEnv)
    (typed : ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (bounded : (witness ("%input_" ++ destination)).val ≤ Native.sourceMaximum ty)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : base.operations.mapM (GenericStateOps.evalOp ctx candidateEnv) = .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after) :
    ∃ candidate : ty.Denote,
      SourceEffects.step ctx (.readCell name destination ty) (sourceEnv, current) =
        .ok ((destination, Value.pack ty candidate) :: sourceEnv, current) ∧
      sourceScalar? ty candidate = some (witness ("%input_" ++ destination)) ∧
      after = ⟨[.vector slots], reads ++ [field (witness ("%input_" ++ destination))]⟩ := by
  obtain ⟨read, singleton, readName, readType⟩ :=
    append_readCell_readIdentity state name destination ty base compiled
  subst destination
  subst ty
  rw [singleton] at decoded
  obtain ⟨first, tail, headDecoded, tailDecoded, environment⟩ :=
    decodeReads_cons_success read [] witness candidateEnv decoded
  have tailEmpty : tail = [] := by
    change Except.ok [] = .ok tail at tailDecoded
    exact (Except.ok.inj tailDecoded).symm
  subst tail
  obtain ⟨scalarType, firstValue⟩ := decodeRead_success read witness first headDecoded
  subst first
  let input := witness ("%input_" ++ read.name)
  let candidate := sourceValue scalarType input
  have lookup : candidateEnv.lookup read.name = some (Value.pack read.ty candidate) := by
    rw [environment]
    simp [candidate, input]
  obtain ⟨canonical, exactValue⟩ := sourceValue_canonical scalarType input typed bounded
  obtain ⟨sourceStep, final⟩ := readCell_candidate_source_step ctx sourceEnv candidateEnv state
    current slots name read.name read.ty base segment slot candidate reads after compiled
    found declaration declarationAt named kind encoded lookup canonical modulus evaluated checked
  have numberMatches := Option.some.inj
    ((sourceScalar_eq_field scalarType candidate).symm.trans exactValue)
  exact ⟨candidate, sourceStep, exactValue, by rw [final, numberMatches]⟩

end Noctium.Verification.GenericStateReadAuthentication
