import Noctium.Verification.GenericStateEffectValidation
import Noctium.Verification.GenericStateAliases

namespace Noctium.Verification.GenericStateTypeAdmission
open Backend

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem acceptedCellStateType (caps : Capabilities) (ty : Ty)
    (accepted : (if ty.isOpaqueString then ty.validate caps
      else if ty.isOpaqueString then
        Except.error "OpaqueString is only supported as a root Bytes32 tree Map value"
      else ty.validate caps) = .ok ()) :
    ty.validate caps = .ok () := by
  cases isOpaqueString : ty.isOpaqueString <;> simp_all

private theorem acceptedMapStateType (caps : Capabilities) (ty : Ty)
    (accepted : (if ty.isOpaqueString then
      Except.error "OpaqueString is only supported as a root Bytes32 tree Map value"
      else ty.validate caps) = .ok ()) :
    ty.validate caps = .ok () := by
  cases isOpaqueString : ty.isOpaqueString <;> simp_all

/-- Accepted native lowering validates every cell type and both map types
through the current source entrypoint prechecks. -/
theorem validated_state_types (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    ∀ decl ∈ state,
      ∀ ty ∈ (match decl.kind with
        | .cell ty => [ty]
        | .map keyTy valueTy => [keyTy, valueTy]
        | _ => []),
      ty.validate GenericStateEffectValidation.stateEffectCaps = .ok () := by
  have source := GenericStateEffectValidation.lower_source_validated state ep plan accepted
  unfold Entrypoint.validate at source
  simp only [bind_ok] at source
  rcases source with ⟨_, prefixAccepted, _⟩
  unfold Entrypoint.validateEffectPrefix at prefixAccepted
  simp only [bind_ok] at prefixAccepted
  rcases prefixAccepted with ⟨_, prechecksAccepted, _⟩
  unfold Entrypoint.validateEffectPrechecks at prechecksAccepted
  simp only [bind_ok] at prechecksAccepted
  rcases prechecksAccepted with ⟨_, stateChecked, _⟩
  refine GenericStateAliases.forIn_extract _
    (fun decl => ∀ ty ∈ (match decl.kind with
      | .cell ty => [ty]
      | .map keyTy valueTy => [keyTy, valueTy]
      | _ => []),
      ty.validate GenericStateEffectValidation.stateEffectCaps = .ok ())
    state ?_ stateChecked
  intro decl step success
  cases decl with
  | mk name kind sealed span alignment =>
    cases kind with
    | cell ty =>
      dsimp only [StateDecl.kind] at success
      simp only [List.forIn_cons, List.forIn_nil] at success
      split at success
      · cases step <;> simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at success
      · rename_i result checked
        change (if ty.isOpaqueString then ty.validate
          GenericStateEffectValidation.stateEffectCaps
          else if ty.isOpaqueString then
            Except.error "OpaqueString is only supported as a root Bytes32 tree Map value"
          else ty.validate GenericStateEffectValidation.stateEffectCaps) = .ok result at checked
        have typeValid : ty.validate GenericStateEffectValidation.stateEffectCaps = .ok () := by
          cases result
          exact acceptedCellStateType GenericStateEffectValidation.stateEffectCaps ty checked
        cases step <;> simp [Bind.bind, Except.bind, Pure.pure, Except.pure,
          typeValid] at success ⊢
    | map keyTy valueTy =>
      dsimp only [StateDecl.kind] at success
      simp only [List.forIn_cons, List.forIn_nil] at success
      split at success
      · cases step <;> simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at success
      · rename_i keyResult keyChecked
        change (if keyTy.isOpaqueString then
          Except.error "OpaqueString is only supported as a root Bytes32 tree Map value"
          else keyTy.validate GenericStateEffectValidation.stateEffectCaps) = .ok keyResult at keyChecked
        have keyValid : keyTy.validate GenericStateEffectValidation.stateEffectCaps = .ok () := by
          cases keyResult
          exact acceptedMapStateType GenericStateEffectValidation.stateEffectCaps keyTy keyChecked
        try simp only [keyValid] at success
        try dsimp at success
        split at success
        · cases step <;> simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at success
        · rename_i valueResult valueChecked
          change (if valueTy.isOpaqueString then
            Except.error "OpaqueString is only supported as a root Bytes32 tree Map value"
            else valueTy.validate GenericStateEffectValidation.stateEffectCaps) = .ok valueResult at valueChecked
          have valueValid : valueTy.validate GenericStateEffectValidation.stateEffectCaps = .ok () := by
            cases valueResult
            exact acceptedMapStateType GenericStateEffectValidation.stateEffectCaps valueTy valueChecked
          cases step <;> simp [Bind.bind, Except.bind, Pure.pure, Except.pure,
            keyValid, valueValid] at success ⊢
    | tree schema =>
      cases step with
      | done _ =>
        cases checked : LedgerValueType.validateCellRoot
            GenericStateEffectValidation.stateEffectCaps schema <;>
          simp [checked, List.forIn_nil, Bind.bind,
            Except.bind, Pure.pure, Except.pure] at success
      | yield _ =>
        simp [List.forIn_nil, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at success ⊢
    | merkleTree depth =>
      cases step <;> simp [List.forIn_nil,
        Bind.bind, Except.bind, Pure.pure, Except.pure] at success ⊢
    | historicMerkleTree depth =>
      cases step <;> simp [List.forIn_nil,
        Bind.bind, Except.bind, Pure.pure, Except.pure] at success ⊢
    | opaqueString =>
      cases step <;> simp [List.forIn_nil,
        Bind.bind, Except.bind, Pure.pure, Except.pure] at success ⊢

end Noctium.Verification.GenericStateTypeAdmission
