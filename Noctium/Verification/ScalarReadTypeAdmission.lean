import Noctium.Verification.GenericStateCheckedReadTrace
import Noctium.Verification.GenericStateInputValues
import Noctium.Verification.ScalarGuardedPlanAdmission

namespace Noctium.Verification.ScalarReadTypeAdmission

open Backend
open GenericStateCellAdmission (ScalarCellType)
open GenericStateCheckedReadTrace (ReadMetadata readChunks)
open ScalarGuardedPlanAdmission (ScalarEffect)

/-- Every read emitted by an admitted guarded scalar effect has a source type
supported by the scalar cell decoder. Cell and map reads retain their exact
value type. An absence check emits its production Boolean descriptor. -/
theorem readChunks_scalar_type (state : List StateDecl) (effects : List Effect)
    (ordinal : Nat)
    (admitted : ∀ effect ∈ effects, ScalarEffect state effect)
    (metadata : ReadMetadata)
    (present : metadata ∈ (readChunks effects ordinal).flatten) :
    Nonempty (ScalarCellType metadata.2) := by
  induction effects generalizing ordinal metadata with
  | nil => simp [readChunks] at present
  | cons effect rest ih =>
    have head := admitted effect (by simp)
    have restAdmitted : ∀ item ∈ rest, ScalarEffect state item := by
      intro item member
      exact admitted item (List.mem_cons_of_mem effect member)
    cases head with
    | cell _ cellSource _ =>
      cases cellSource with
      | readCell name destination ty scalar _ =>
        simp only [readChunks, GenericStateCheckedReadTrace.effectReadChunk,
          List.flatten_cons] at present
        rcases List.mem_append.mp present with first | later
        · simp only [List.mem_singleton] at first
          cases first
          exact ⟨scalar⟩
        · exact ih (ordinal + 1) restAdmitted metadata later
      | writeCell name ty value scalar _ =>
        simp only [readChunks, GenericStateCheckedReadTrace.effectReadChunk,
          List.flatten_cons, List.nil_append] at present
        exact ih ordinal restAdmitted metadata present
    | readMap name destination keyTy valueTy key keyScalar valueScalar _ =>
      simp only [readChunks, GenericStateCheckedReadTrace.effectReadChunk,
        List.flatten_cons] at present
      rcases List.mem_append.mp present with first | later
      · simp only [List.mem_singleton] at first
        cases first
        exact ⟨valueScalar⟩
      · exact ih (ordinal + 1) restAdmitted metadata later
    | writeMap name keyTy valueTy key value keyScalar valueScalar _ _ =>
      simp only [readChunks, GenericStateCheckedReadTrace.effectReadChunk,
        List.flatten_cons, List.nil_append] at present
      exact ih ordinal restAdmitted metadata present
    | require condition _ =>
      simp only [readChunks, GenericStateCheckedReadTrace.effectReadChunk,
        List.flatten_cons, List.nil_append] at present
      exact ih ordinal restAdmitted metadata present
    | requireAbsent name keyTy key keyScalar _ =>
      simp only [readChunks, GenericStateCheckedReadTrace.effectReadChunk,
        List.flatten_cons] at present
      rcases List.mem_append.mp present with first | later
      · simp only [List.mem_singleton] at first
        cases first
        exact ⟨.bool⟩
      · exact ih (ordinal + 1) restAdmitted metadata later

/-- A type admitted as a generic scalar cell has both a decoder and valid
target type metadata, including the bounded UInt maximum. -/
theorem scalarCellType_decoder_and_validation {ty : Ty}
    (admitted : ScalarCellType ty) :
    (GenericStateInputValues.scalarType? ty).isSome = true ∧
      ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok () := by
  cases admitted with
  | native =>
    constructor
    · rfl
    · simp [Ty.validate, Ty.scalarKind, ScalarPolicy.validate, pure, Except.pure]
  | bool =>
    constructor
    · rfl
    · simp [Ty.validate, Ty.scalarKind, ScalarPolicy.validate, pure, Except.pure]
  | uint maximum bound =>
    have belowModulus : maximum < Field.modulus :=
      Nat.lt_of_le_of_lt bound ScalarPolicy.maxUint_lt_native
    constructor
    · rfl
    · simp [Ty.validate, Ty.scalarKind, ScalarPolicy.validate, bound, belowModulus,
        pure, Except.pure, bind, Except.bind]

end Noctium.Verification.ScalarReadTypeAdmission
