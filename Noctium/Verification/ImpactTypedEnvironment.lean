import Noctium.Verification.ImpactReferenceEvaluation
import Noctium.Verification.ScalarNormalizationSoundness

namespace Noctium.Verification.ImpactTypedEnvironment

open Noctium
open ImpactReferenceEvaluation ScalarNormalization

/-- A packed scalar value is accepted only when its dynamic representation
matches the declared type and its source value is canonical. -/
private def packedCanonical? (ty : Ty) (raw : Value) :
    Option { value : ty.Denote // raw = Value.pack ty value ∧ Canonical ty value } :=
  match ty with
  | .native =>
    match raw with
    | .native value =>
      if canonical : value < Field.modulus then
        some ⟨value, ⟨rfl, by
          change value < Field.modulus ∧ True
          exact ⟨canonical, trivial⟩⟩⟩
      else none
    | _ => none
  | .bool =>
    match raw with
    | .bool value =>
      some ⟨value, ⟨rfl, by
        cases value <;> simp [Canonical, sourceNumber?] <;> decide⟩⟩
    | _ => none
  | .uint maximum =>
    match raw with
    | .uint found value =>
      if sameType : found = maximum then
        if inRange : maximum ≤ ScalarPolicy.maxUint ∧ value ≤ maximum ∧
            value < Field.modulus then
          some ⟨value, ⟨by rw [sameType]; rfl, by
            change value < Field.modulus ∧
              maximum ≤ ScalarPolicy.maxUint ∧ value ≤ maximum
            exact ⟨inRange.2.2, inRange.1, inRange.2.1⟩⟩⟩
        else none
      else none
    | _ => none
  | .bytes _ | .opaqueBytes | .opaqueString | .jubjubScalar | .jubjubPoint | .foreign _ => none

private def checkBinding (types : TypeEnv) (values : EvalEnv)
    (binding : String × Ty) : Bool :=
  let (name, ty) := binding
  if decide (types.lookup name = some ty) then
    match values.lookup name with
    | none => Bool.false
    | some raw => (packedCanonical? ty raw).isSome
  else Bool.true

private def checkBindings (types : TypeEnv) (values : EvalEnv) :
    List (String × Ty) → Bool
  | [] => Bool.true
  | binding :: rest => checkBinding types values binding && checkBindings types values rest

/-- Check all visible declarations against the first value bound to each name.
Hidden type declarations do not constrain the environment. -/
def check (types : TypeEnv) (env : EvalEnv) : Bool :=
  checkBindings types env types

private theorem packedCanonical?_sound {ty : Ty} {raw : Value}
    (accepted : (packedCanonical? ty raw).isSome = Bool.true) :
    ∃ value : ty.Denote, raw = Value.pack ty value ∧ Canonical ty value := by
  cases result : packedCanonical? ty raw with
  | none => simp [result] at accepted
  | some packed =>
    simp [result] at accepted
    rcases packed with ⟨value, evidence⟩
    rcases evidence with ⟨packedValue, canonical⟩
    exact ⟨value, packedValue, canonical⟩

private theorem checkBindings_sound (types : TypeEnv) (values : EvalEnv) :
    ∀ bindings, checkBindings types values bindings = Bool.true →
      ∀ name ty, (name, ty) ∈ bindings → types.lookup name = some ty →
        ∃ value : ty.Denote,
          values.lookup name = some (Value.pack ty value) ∧ Canonical ty value := by
  intro bindings
  induction bindings with
  | nil =>
    intro accepted name ty member _
    simp at member
  | cons binding rest ih =>
    cases binding with
    | mk bindingName bindingTy =>
      intro accepted name ty member visible
      simp only [checkBindings, Bool.and_eq_true] at accepted
      rcases accepted with ⟨headAccepted, tailAccepted⟩
      rcases List.mem_cons.mp member with headMember | tailMember
      · cases headMember
        cases envFound : values.lookup bindingName with
        | none =>
          simp [checkBinding, visible, envFound] at headAccepted
        | some raw =>
          have packedAccepted : (packedCanonical? bindingTy raw).isSome = Bool.true := by
            simpa [checkBinding, visible, envFound] using headAccepted
          obtain ⟨value, packedValue, canonical⟩ := packedCanonical?_sound packedAccepted
          refine ⟨value, ?_, canonical⟩
          rw [packedValue]
      · exact ih tailAccepted name ty tailMember visible

private theorem lookup_mem (bindings : TypeEnv) {name : String} {ty : Ty}
    (found : bindings.lookup name = some ty) : (name, ty) ∈ bindings := by
  induction bindings with
  | nil => simp at found
  | cons binding rest ih =>
    cases binding with
    | mk bindingName bindingTy =>
      by_cases same : name = bindingName
      · subst name
        simp at found
        subst ty
        simp
      · have different : (name == bindingName) = Bool.false :=
          beq_eq_false_iff_ne.mpr same
        simp [List.lookup_cons, different] at found
        have inTail := ih found
        simp [inTail, same]

private theorem scalarType_of_canonical {ty : Ty} {value : ty.Denote}
    (canonical : Canonical ty value) : Nonempty (ScalarType ty) := by
  cases ty with
  | native => exact ⟨.native⟩
  | bool => exact ⟨.bool⟩
  | uint maximum => exact ⟨.uint maximum⟩
  | bytes length => simp [Canonical, sourceNumber?] at canonical
  | opaqueBytes => simp [Canonical, sourceNumber?] at canonical
  | opaqueString => simp [Canonical, sourceNumber?] at canonical
  | jubjubScalar => simp [Canonical, sourceNumber?] at canonical
  | jubjubPoint => simp [Canonical, sourceNumber?] at canonical
  | foreign kind => simp [Canonical, sourceNumber?] at canonical

private theorem typed_value_eq_pack {ty : Ty} (support : ScalarType ty)
    (raw : Value) (value : ty.Denote) (typed : raw.as ty = some value) :
    raw = Value.pack ty value := by
  cases support with
  | native => cases raw <;> simp_all [Value.as, Value.pack]
  | bool => cases raw <;> simp_all [Value.as, Value.pack]
  | uint maximum => cases raw <;> simp_all [Value.as, Value.pack]

/-- A typed source environment supplies canonical values for the native
Impact reference semantics. -/
theorem of_normalization {hash : NativeRelation.Hash} {inputs : NativeRelation.Assignment}
    {aliases : Backend.Native.AliasEnvironment} {env : EvalEnv} {types : TypeEnv}
    (environment : TypedEnvironment hash inputs aliases env types) :
    ImpactReferenceEvaluation.TypedScalarEnv types env := by
  intro name ty declared
  obtain ⟨raw, value, found, typed⟩ := environment.complete name ty declared
  have canonical : Canonical ty value :=
    (environment.aliases name ty raw value found typed).1
  obtain ⟨support⟩ := scalarType_of_canonical canonical
  have packed := typed_value_eq_pack support raw value typed
  refine ⟨value, ?_, canonical⟩
  rw [← packed]
  exact found

/-- Every visible declaration has a canonical packed scalar value in the
environment. The type and value lookups both use their first matching entry. -/
theorem check_sound {types : TypeEnv} {env : EvalEnv}
    (accepted : check types env = Bool.true) :
    ImpactReferenceEvaluation.TypedScalarEnv types env := by
  intro name ty declared
  exact checkBindings_sound types env types accepted name ty
    (lookup_mem types declared) declared

end Noctium.Verification.ImpactTypedEnvironment
