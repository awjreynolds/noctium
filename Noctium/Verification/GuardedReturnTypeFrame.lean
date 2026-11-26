import Noctium.Verification.GenericStateCheckedReadDecode
import Noctium.Verification.GenericStateEffectValidation
import Noctium.Verification.GenericStateCheckedReadTrace
import Noctium.Verification.GuardedReadDescriptorTrace
import Noctium.Verification.ScalarEffectReadFacts
import Noctium.Verification.ScalarGuardedReadAdmission
import Noctium.Verification.ScalarNormalizationSoundness

namespace Noctium.Verification.GuardedReturnTypeFrame

open Backend Backend.Native NativeRelation ScalarNormalization
open GenericStateEffectValidation GenericStateCheckedReadTrace
open ScalarGuardedPlanAdmission (ScalarEffect)

private theorem scalar_read_type_bindings (read : Impact.Read)
    (plain : read.components = [])
    (supported : (GenericStateInputValues.scalarType? read.ty).isSome = true) :
    read.typeBindings = [(read.name, read.ty)] := by
  cases read with
  | mk name ty components schema guard rootCellRead =>
      change components = [] at plain
      subst components
      have bindings := GenericStateCheckedReadDecode.supported_plain_read_bindings
        {name, ty, components := [], schema, guard, rootCellRead} rfl supported
      cases ty with
      | native => simp [Impact.Read.typeBindings, Impact.Read.scalarReads, bindings]
      | bool => simp [Impact.Read.typeBindings, Impact.Read.scalarReads, bindings]
      | uint maximum => simp [Impact.Read.typeBindings, Impact.Read.scalarReads, bindings]
      | bytes length => simp [GenericStateInputValues.scalarType?] at supported
      | opaqueBytes => simp [GenericStateInputValues.scalarType?] at supported
      | opaqueString => simp [GenericStateInputValues.scalarType?] at supported
      | jubjubScalar => simp [GenericStateInputValues.scalarType?] at supported
      | jubjubPoint => simp [GenericStateInputValues.scalarType?] at supported
      | foreign kind => simp [GenericStateInputValues.scalarType?] at supported

private theorem flatMap_type_bindings_eq_metadata (reads : List Impact.Read)
    (admitted : ∀ read ∈ reads,
      read.components = [] ∧
        (GenericStateInputValues.scalarType? read.ty).isSome = true) :
    reads.flatMap Impact.Read.typeBindings = reads.map readMetadata := by
  induction reads with
  | nil => rfl
  | cons read rest ih =>
      have head := scalar_read_type_bindings read (admitted read (by simp)).1
        (admitted read (by simp)).2
      have tailAdmitted : ∀ item ∈ rest,
          item.components = [] ∧
            (GenericStateInputValues.scalarType? item.ty).isSome = true := by
        intro item member
        exact admitted item (List.mem_cons_of_mem _ member)
      rw [List.flatMap_cons, head, ih tailAdmitted]
      simp [readMetadata]

private theorem lookup_of_mem_pairwise {items : List (String × Ty)}
    {name : String} {ty : Ty}
    (distinct : items.Pairwise (fun left right => left.1 ≠ right.1))
    (member : (name, ty) ∈ items) :
    items.lookup name = some ty := by
  induction items with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with headMember | tailMember
      · cases head with
        | mk headName headTy =>
            simp only [Prod.mk.injEq] at headMember
            rcases headMember with ⟨rfl, rfl⟩
            simp
      · cases distinct with
        | cons headFresh tailDistinct =>
            have nameFresh : head.1 ≠ name := by
              intro same
              exact headFresh (name, ty) tailMember (by simpa using same)
            have beqFalse : (name == head.1) = false := by
              simp [Ne.symm nameFresh]
            rw [List.lookup_cons]
            simp [beqFalse, ih tailDistinct tailMember]

private theorem lookup_mem {items : List (String × Ty)}
    {name : String} {ty : Ty}
    (lookup : items.lookup name = some ty) : (name, ty) ∈ items := by
  obtain ⟨before, after, equal, _⟩ := List.lookup_eq_some_iff.mp lookup
  rw [equal]
  simp

private theorem effect_type_binding_mem_post_public_metadata
    (state : List StateDecl) (ep : Entrypoint) (plan : Impact.Plan)
    (accepted : Impact.lower state ep = .ok plan)
    (scope : GuardedScalarReadEffects ep.effectGuards ep.effects.zipIdx) :
    ∀ binding ∈ ep.effects.flatMap effectTypeBindings,
      binding ∈ (plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)).map
        readMetadata := by
  intro binding member
  obtain ⟨effect, effectMember, bindingMember⟩ := List.mem_flatMap.mp member
  cases effect with
  | readCell name destination ty =>
      simp only [effectTypeBindings, List.mem_singleton] at bindingMember
      subst binding
      obtain ⟨read, readMember, nameEq, typeEq⟩ :=
        ScalarEffectReadFacts.readCell_descriptor state ep plan name destination ty
          accepted scope effectMember
      apply List.mem_map.mpr
      refine ⟨read, readMember, ?_⟩
      simp [readMetadata, nameEq, typeEq]
  | readMap name destination keyTy valueTy key =>
      simp only [effectTypeBindings, List.mem_singleton] at bindingMember
      subst binding
      obtain ⟨read, readMember, nameEq, typeEq⟩ :=
        ScalarEffectReadFacts.readMap_descriptor state ep plan name destination keyTy valueTy
          key accepted scope effectMember
      apply List.mem_map.mpr
      refine ⟨read, readMember, ?_⟩
      simp [readMetadata, nameEq, typeEq]
  | _ => simp [effectTypeBindings] at bindingMember

/-- A source return frame uses the actual guarded validation chain and actual
post-public read descriptors. Generated absence reads remain in the plan's
type environment, while the source validator's returned bindings agree by
name and type wherever the source validator introduced them. -/
theorem lower_guarded_return_type_frame
    (state : List StateDecl) (ep : Entrypoint) (plan : Impact.Plan)
    (hash : Hash) (assignment : Assignment) (aliases : AliasEnvironment)
    (complete : EvalEnv) (finalTypes : TypeEnv)
    (accepted : Impact.lower state ep = .ok plan)
    (effects : ∀ effect ∈ ep.effects, ScalarEffect state effect)
    (scope : GuardedScalarReadEffects ep.effectGuards ep.effects.zipIdx)
    (validated : GuardValidatedEffects state ep (initialEffectTypeEnv ep)
      ep.effects.zipIdx finalTypes)
    (planFrame : TypedEnvironment hash assignment aliases complete
      (plan.typeEnvironment ep)) :
    TypedEnvironment hash assignment aliases complete finalTypes := by
  let reads := plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)
  let metadata := reads.map readMetadata
  have readAdmission := ScalarGuardedReadAdmission.lower_read_admission
    state ep plan accepted effects
  have readsPlainScalar : ∀ read ∈ reads,
      read.components = [] ∧
        (GenericStateInputValues.scalarType? read.ty).isSome = true := by
    intro read member
    exact ⟨(readAdmission.1 read member).1,
      (readAdmission.1 read member).2.1⟩
  have metadataDistinct : metadata.Pairwise (fun left right => left.1 ≠ right.1) := by
    change (reads.map readMetadata).Pairwise (fun left right => left.1 ≠ right.1)
    exact List.pairwise_map.mpr readAdmission.2.2
  have typeBindings := flatMap_type_bindings_eq_metadata reads readsPlainScalar
  have planTypeShape : plan.typeEnvironment ep =
      initialEffectTypeEnv ep ++ metadata := by
    change initialEffectTypeEnv ep ++ reads.flatMap Impact.Read.typeBindings = _
    rw [typeBindings]
  have sourceValidated : ValidatedEffects state (initialEffectTypeEnv ep)
      ep.effects finalTypes := by
    simpa only [List.zipIdx_map_fst] using validated.effects
  have sourceTypeShape := sourceValidated.type_environment_shape
  have bindingMember := effect_type_binding_mem_post_public_metadata
    state ep plan accepted scope
  have lookupAgreement : ∀ name ty, finalTypes.lookup name = some ty →
      (plan.typeEnvironment ep).lookup name = some ty := by
    intro name ty lookup
    rw [sourceTypeShape, List.lookup_append] at lookup
    cases initialLookup : (initialEffectTypeEnv ep).lookup name with
    | some initialTy =>
        simp [initialLookup] at lookup
        have sameTy : initialTy = ty := lookup
        subst ty
        simp [planTypeShape, List.lookup_append, initialLookup]
    | none =>
        simp [initialLookup] at lookup
        have sourceMember : (name, ty) ∈ ep.effects.flatMap effectTypeBindings := by
          exact lookup_mem lookup
        have metadataMember : (name, ty) ∈ metadata := by
          simpa only [metadata, reads] using bindingMember (name, ty) sourceMember
        have metadataLookup := lookup_of_mem_pairwise metadataDistinct metadataMember
        simp [planTypeShape, List.lookup_append, initialLookup, metadataLookup]
  constructor
  · exact planFrame.aliases
  · intro name ty typed
    exact planFrame.complete name ty (lookupAgreement name ty typed)

end Noctium.Verification.GuardedReturnTypeFrame
