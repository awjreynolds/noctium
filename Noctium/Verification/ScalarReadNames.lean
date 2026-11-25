import Noctium.Verification.GenericStateEffectValidation
import Noctium.Verification.GenericStateCheckedReadTrace
import Std.Data.String.ToNat

namespace Noctium.Verification.ScalarReadNames

open Backend
open GenericStateCheckedReadTrace
open GenericStateEffectValidation

/-- This is the generated alias spelling used for absent Map reads. -/
def absenceName (ordinal : Nat) : String := "_noctium_absence_" ++ toString ordinal

theorem absenceName_injective {left right : Nat}
    (same : absenceName left = absenceName right) : left = right := by
  apply Nat.repr_injective
  exact (String.append_right_inj "_noctium_absence_").mp same

/-- Generated absence aliases occupy the reserved native name prefix. -/
theorem absenceName_reserved (ordinal : Nat) :
    (absenceName ordinal).startsWith "_noctium_" = true := by
  rw [String.startsWith_string_iff]
  change "_noctium_".toList <+:
    ("_noctium_" ++ "absence_" ++ toString ordinal).toList
  rw [String.toList_append, String.toList_append]
  exact ⟨"absence_".toList ++ (toString ordinal).toList, by simp⟩

private def generatedAbsenceOrdinals : List Effect → Nat → List Nat
  | [], _ => []
  | .readCell _ _ _ :: rest, ordinal => generatedAbsenceOrdinals rest (ordinal + 1)
  | .readMap _ _ _ _ _ :: rest, ordinal => generatedAbsenceOrdinals rest (ordinal + 1)
  | .requireAbsent _ _ _ :: rest, ordinal =>
      ordinal :: generatedAbsenceOrdinals rest (ordinal + 1)
  | _ :: rest, ordinal => generatedAbsenceOrdinals rest ordinal

private theorem generatedAbsenceOrdinals_properties (effects : List Effect)
    (ordinal : Nat) (scope : ScalarStateEffects effects) :
    (generatedAbsenceOrdinals effects ordinal).Nodup ∧
      ∀ position ∈ generatedAbsenceOrdinals effects ordinal, ordinal ≤ position := by
  induction scope generalizing ordinal with
  | nil => simp [generatedAbsenceOrdinals]
  | cons head tail ih =>
    cases head with
    | readCell name destination ty =>
      have rest := ih (ordinal + 1)
      constructor
      · simpa [generatedAbsenceOrdinals] using rest.1
      · intro position member
        have lower := rest.2 position (by simpa [generatedAbsenceOrdinals] using member)
        omega
    | readMap name destination keyTy valueTy key =>
      have rest := ih (ordinal + 1)
      constructor
      · simpa [generatedAbsenceOrdinals] using rest.1
      · intro position member
        have lower := rest.2 position (by simpa [generatedAbsenceOrdinals] using member)
        omega
    | requireAbsent name keyTy key =>
      have rest := ih (ordinal + 1)
      constructor
      · apply List.nodup_cons.mpr
        refine ⟨?_, rest.1⟩
        intro member
        have lower := rest.2 ordinal member
        omega
      · intro position member
        simp only [generatedAbsenceOrdinals, List.mem_cons] at member
        rcases member with same | later
        · cases same
          omega
        · have lower := rest.2 position later
          omega
    | require condition =>
      simpa [generatedAbsenceOrdinals] using ih ordinal
    | writeCell name ty value =>
      simpa [generatedAbsenceOrdinals] using ih ordinal
    | writeMap name keyTy valueTy key value =>
      simpa [generatedAbsenceOrdinals] using ih ordinal

private theorem readChunks_names (effects : List Effect) (ordinal : Nat)
    (scope : ScalarStateEffects effects) :
    List.Perm ((readChunks effects ordinal).flatten.map Prod.fst)
      (scalarReadDestinations effects ++
        (generatedAbsenceOrdinals effects ordinal).map absenceName) := by
  induction scope generalizing ordinal with
  | nil => simp [readChunks, scalarReadDestinations, generatedAbsenceOrdinals]
  | cons head tail ih =>
    cases head with
    | readCell name destination ty =>
      simpa [readChunks, effectReadChunk, scalarReadDestinations, generatedAbsenceOrdinals]
        using List.Perm.cons destination (ih (ordinal + 1))
    | readMap name destination keyTy valueTy key =>
      simpa [readChunks, effectReadChunk, scalarReadDestinations, generatedAbsenceOrdinals]
        using List.Perm.cons destination (ih (ordinal + 1))
    | requireAbsent name keyTy key =>
      simpa [readChunks, effectReadChunk, scalarReadDestinations, generatedAbsenceOrdinals,
        absenceName] using
        (List.Perm.cons (absenceName ordinal) (ih (ordinal + 1))).trans
          List.perm_middle.symm
    | require condition =>
      simpa [readChunks, effectReadChunk, scalarReadDestinations, generatedAbsenceOrdinals]
        using ih ordinal
    | writeCell name ty value =>
      simpa [readChunks, effectReadChunk, scalarReadDestinations, generatedAbsenceOrdinals]
        using ih ordinal
    | writeMap name keyTy valueTy key value =>
      simpa [readChunks, effectReadChunk, scalarReadDestinations, generatedAbsenceOrdinals]
        using ih ordinal

/-- Source read names stay distinct from each other and from generated absence
aliases. Every generated alias starts at or after the supplied live ordinal. -/
theorem readChunkNames_fresh_unique (effects : List Effect) (ordinal : Nat)
    (scope : ScalarStateEffects effects)
    (destinationsDistinct : (scalarReadDestinations effects).Nodup)
    (destinationsUnreserved : ∀ name ∈ scalarReadDestinations effects,
      name.startsWith "_noctium_" = false) :
    ((readChunks effects ordinal).flatten.map Prod.fst).Nodup ∧
      ∀ name ∈ (readChunks effects ordinal).flatten.map Prod.fst,
        name ∈ scalarReadDestinations effects ∨
          ∃ position, ordinal ≤ position ∧ name = absenceName position := by
  have ordinals := generatedAbsenceOrdinals_properties effects ordinal scope
  have aliasesDistinct :
      ((generatedAbsenceOrdinals effects ordinal).map absenceName).Nodup :=
    List.Pairwise.map absenceName
      (fun _ _ different same => different (absenceName_injective same)) ordinals.1
  have allDistinct : (scalarReadDestinations effects ++
      (generatedAbsenceOrdinals effects ordinal).map absenceName).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨destinationsDistinct, aliasesDistinct, ?_⟩
    intro sourceName sourceMember aliasName aliasMember same
    obtain ⟨position, _, aliasEq⟩ := List.mem_map.mp aliasMember
    have reserved := absenceName_reserved position
    rw [aliasEq, ← same] at reserved
    rw [destinationsUnreserved sourceName sourceMember] at reserved
    cases reserved
  have chunkNames := readChunks_names effects ordinal scope
  refine ⟨?_, ?_⟩
  · exact chunkNames.nodup_iff.mpr allDistinct
  · intro name member
    have sourceOrAlias := chunkNames.mem_iff.mp member
    rcases List.mem_append.mp sourceOrAlias with source | alias
    · exact Or.inl source
    · obtain ⟨position, positionMember, same⟩ := List.mem_map.mp alias
      exact Or.inr ⟨position, ordinals.2 position positionMember, same.symm⟩

end Noctium.Verification.ScalarReadNames
