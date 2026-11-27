import Noctium.Verification.ScalarNormalization
namespace Noctium.Verification.ScalarNormalization
open Backend.Native NativeRelation

private theorem scalarType_notOpaque {ty : Ty} (supported : ScalarType ty) :
    ty.isOpaqueBytes = false ∧ ty.isOpaqueString = false := by
  cases supported <;> exact ⟨rfl, rfl⟩

/-- Every name admitted by source type checking has an actual value and alias.
No source execution or compiler-preservation conclusion is assumed. -/
structure TypedEnvironment (hash : Hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv) (types : TypeEnv) : Prop where
  aliases : AliasAgreement hash inputs aliases values
  complete : ∀ name ty, types.lookup name = some ty →
    ∃ raw value, values.lookup name = some raw ∧ raw.as ty = some value

theorem TypedEnvironment.cons (hash : Hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv) (types : TypeEnv)
    (environment : TypedEnvironment hash inputs aliases values types)
    (name : String) (ty : Ty) (value : ty.Denote) (term : Term)
    (canonical : Canonical ty value)
    (meaning : interpret hash inputs term = sourceScalar? ty value) :
    TypedEnvironment hash inputs ((name, term) :: aliases) ((name, Value.pack ty value) :: values)
      ((name, ty) :: types) := by
  constructor
  · exact aliasAgreement_cons _ _ _ _ _ _ _ _ environment.aliases canonical meaning
  · intro found foundTy lookup
    by_cases same : found = name
    · subst found
      simp only [List.lookup_cons, beq_self_eq_true, Option.some.injEq] at lookup
      subst foundTy
      exact ⟨Value.pack ty value, value, by simp, number_pack_as ty value canonical⟩
    · have unequal : (found == name) = false := by simp [same]
      simp only [List.lookup_cons, unequal] at lookup
      obtain ⟨raw, result, lookup, typed⟩ := environment.complete found foundTy lookup
      exact ⟨raw, result, by simp [List.lookup_cons, unequal, lookup], typed⟩

private theorem normalized_success (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv)
    (agreement : AliasAgreement hash inputs aliases values)
    (expression : Expr ty) (admission : ScalarExpression expression) (normalized : Normalized)
    (normal : normalize aliases expression = .ok normalized)
    (value : ty.Denote) (success : expression.eval ctx values = .ok value) :
    ∃ result, expression.eval ctx values = .ok result ∧ Represents hash inputs ty normalized result := by
  obtain ⟨actual, found, represented⟩ := normalize_success ctx hash implementation inputs aliases values agreement expression admission value success
  rw [normal] at found
  cases found
  exact ⟨value, success, represented⟩

private theorem except_bind_ok (first : Except ε α) (next : α → Except ε β) (value : β) :
    Except.bind first next = .ok value ↔ ∃ intermediate, first = .ok intermediate ∧ next intermediate = .ok value := by
  cases first <;> simp [Except.bind]

private theorem except_map_ok (first : Except ε α) (next : α → β) (value : β) :
    Except.map next first = .ok value ↔ ∃ intermediate, first = .ok intermediate ∧ next intermediate = value := by
  cases first <;> simp [Except.map, Except.pure]

private theorem except_unit_bind (first next : Except ε Unit) :
    Except.bind first (fun _ => next) = .ok () ↔ first = .ok () ∧ next = .ok () := by
  cases first <;> simp [Except.bind]

private theorem requirements_children (hash : Hash) (inputs : Assignment)
    (left right : Normalized) (term : Term) (extra : List (Term × Nat))
    (requirements : Requirements hash inputs
      {term, bounds := left.bounds ++ right.bounds ++ extra, assertions := left.assertions ++ right.assertions}) :
    Requirements hash inputs left ∧ Requirements hash inputs right := by
  constructor <;> constructor
  · intro requirement member
    exact requirements.1 requirement (List.mem_append_left _ (List.mem_append_left _ member))
  · intro assertion member
    exact requirements.2 assertion (List.mem_append_left _ member)
  · intro requirement member
    exact requirements.1 requirement (List.mem_append_left _ (List.mem_append_right _ member))
  · intro assertion member
    exact requirements.2 assertion (List.mem_append_right _ member)

private theorem requirements_child (hash : Hash) (inputs : Assignment)
    (child : Normalized) (term : Term) (extra : List (Term × Nat))
    (requirements : Requirements hash inputs {term, bounds := child.bounds ++ extra, assertions := child.assertions}) :
    Requirements hash inputs child := by
  exact ⟨fun requirement member => requirements.1 requirement (List.mem_append_left _ member), requirements.2⟩

private theorem uint_valid_bound (maximum : Nat)
    (valid : (Ty.uint maximum).validate Capabilities.scalarFragment = .ok ()) : maximum ≤ ScalarPolicy.maxUint := by
  by_cases bound : maximum ≤ ScalarPolicy.maxUint
  · exact bound
  · simp [Ty.validate, Ty.scalarKind, ScalarPolicy.validate, bound, bind, Except.bind] at valid

private theorem scalar_type_beq_sound {ty : Ty} (scalarType : ScalarType ty)
    (left : Ty) (equal : (left == ty) = true) : left = ty := by
  cases scalarType <;> cases left <;> simp_all [BEq.beq, instBEqTy.beq]

private theorem scalar_ref_validate_lookup {ty : Ty} (supported : ScalarType ty)
    (types : TypeEnv) (name : String)
    (valid : (Expr.ref name : Expr ty).validate Capabilities.scalarFragment types = .ok ()) :
    types.lookup name = some ty := by
  cases supported with
  | native =>
    simp only [Expr.validate, bind, except_bind_ok] at valid
    rcases valid with ⟨_, _, lookup⟩
    cases found : types.lookup name with
    | none => simp [found] at lookup
    | some foundTy =>
      simp only [found] at lookup
      split at lookup
      next equal =>
        have equalTy := scalar_type_beq_sound ScalarType.native foundTy equal
        simpa [equalTy] using found
      next unequal => cases lookup
  | bool =>
    simp only [Expr.validate, bind, except_bind_ok] at valid
    rcases valid with ⟨_, _, lookup⟩
    cases found : types.lookup name with
    | none => simp [found] at lookup
    | some foundTy =>
      simp only [found] at lookup
      split at lookup
      next equal =>
        have equalTy := scalar_type_beq_sound ScalarType.bool foundTy equal
        simpa [equalTy] using found
      next unequal => cases lookup
  | uint maximum =>
    simp only [Expr.validate, bind, except_bind_ok] at valid
    rcases valid with ⟨_, _, lookup⟩
    cases found : types.lookup name with
    | none => simp [found] at lookup
    | some foundTy =>
      simp only [found] at lookup
      split at lookup
      next equal =>
        have equalTy := scalar_type_beq_sound (ScalarType.uint maximum) foundTy equal
        simpa [equalTy] using found
      next unequal => cases lookup

/-- All accepted normalized range and assertion requirements force successful
source evaluation. Native instruction satisfaction is connected separately. -/
theorem normalize_sound (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (types : TypeEnv) (aliases : AliasEnvironment) (values : EvalEnv)
    (environment : TypedEnvironment hash inputs aliases values types)
    (expression : Expr ty) (admission : ScalarExpression expression) (normalized : Normalized)
    (valid : expression.validate Capabilities.scalarFragment types = .ok ())
    (normal : normalize aliases expression = .ok normalized)
    (requirements : Requirements hash inputs normalized) :
    ∃ value, expression.eval ctx values = .ok value ∧ Represents hash inputs ty normalized value := by
  induction admission generalizing types aliases values normalized with
  | native n =>
    simp only [Expr.validate, Capabilities.nativeModulus, Field.modulus] at valid
    have bound : n < Field.modulus := by
      simpa only [Expr.validate, Capabilities.nativeModulus, Field.modulus] using
        (show n < Field.modulus from by
          change (if n < Field.modulus then Except.ok () else Except.error "noncanonical native constant") = Except.ok () at valid
          split at valid
          next h => exact h
          next h => cases valid)
    apply normalized_success ctx hash implementation inputs aliases values environment.aliases _
      (ScalarExpression.native n) _ normal n
    simp [Expr.eval, implementation.modulus, bound] <;> rfl
  | bool b =>
    simp only [Expr.validate] at valid
    exact normalized_success ctx hash implementation inputs aliases values environment.aliases _
      (ScalarExpression.bool b) _ normal b (by simp [Expr.eval])
  | uint maximum n =>
    simp only [Expr.validate] at valid
    change Except.bind ((Ty.uint maximum).validate Capabilities.scalarFragment)
      (fun _ => if n ≤ maximum then Except.ok () else Except.error "unsigned constant exceeds its type") = Except.ok () at valid
    rw [except_unit_bind] at valid
    have valueBound : n ≤ maximum := by
      split at valid
      next h => exact h
      next h => cases valid.2
    have typeBound : maximum ≤ ScalarPolicy.maxUint := uint_valid_bound maximum valid.1
    apply normalized_success ctx hash implementation inputs aliases values environment.aliases _
      (ScalarExpression.uint maximum n) _ normal n
    simp only [Expr.eval]
    change (if (decide (maximum ≤ ScalarPolicy.maxUint) && decide (n ≤ maximum) &&
        decide (n < ctx.modulus)) = true then Except.ok n
      else Except.error "noncanonical unsigned constant") = Except.ok n
    have fieldBound : n < ctx.modulus := by
      rw [implementation.modulus]
      exact Nat.lt_of_le_of_lt (Nat.le_trans valueBound typeBound) ScalarPolicy.maxUint_lt_native
    simp [typeBound, valueBound, fieldBound]
  | @ref ty name scalarType =>
    have lookup : types.lookup name = some ty := by
      exact scalar_ref_validate_lookup scalarType types name valid
    obtain ⟨raw, value, rawLookup, typed⟩ := environment.complete name ty lookup
    obtain ⟨canonical, term, alias, meaning⟩ := environment.aliases name ty raw value rawLookup typed
    apply normalized_success ctx hash implementation inputs aliases values environment.aliases _
      (ScalarExpression.ref name scalarType) _ normal value
    simp only [Expr.eval, rawLookup, typed]
    cases scalarType with
    | native =>
      change (if !(value < ctx.modulus) then _ else _) = _
      have bound : value < ctx.modulus := by simpa [implementation.modulus, number] using canonical.1
      simp [bound] <;> rfl
    | bool => rfl
    | uint maximum =>
      change (if !(maximum ≤ ScalarPolicy.maxUint && value ≤ maximum && value < ctx.modulus) then _ else _) = _
      have bound : value < ctx.modulus := by simpa [implementation.modulus, number] using canonical.1
      simp [canonical.2.1, canonical.2.2, bound] <;> rfl
  | add a b leftSupported rightSupported ia ib =>
    simp only [Expr.validate] at valid
    change Except.bind (a.validate Capabilities.scalarFragment types)
      (fun _ => b.validate Capabilities.scalarFragment types) = .ok () at valid
    rw [except_unit_bind] at valid
    simp only [normalize, bind, Functor.map, Except.map, except_bind_ok, Except.pure] at normal
    rcases normal with ⟨an, na, bn, nb, equal⟩
    cases equal
    simp only [normalizeNativeAdd] at requirements
    obtain ⟨ar, br⟩ := requirements_children hash inputs an bn _ [] (by simpa using requirements)
    obtain ⟨av, ea, ac, aq, am⟩ := ia types aliases values environment an valid.1 na ar
    obtain ⟨bv, eb, bc, bq, bm⟩ := ib types aliases values environment bn valid.2 nb br
    apply normalized_success ctx hash implementation inputs aliases values environment.aliases _
      (ScalarExpression.add a b leftSupported rightSupported) _
      (by simp only [normalize, na, nb]; rfl) ((av + bv) % ctx.modulus)
    exact (by simp [Expr.eval, ea, eb, implementation.modulus, Field.modulus, bind, Except.bind, Except.map, Except.pure] <;> rfl)
  | mul a b leftSupported rightSupported ia ib =>
    simp only [Expr.validate] at valid
    change Except.bind (a.validate Capabilities.scalarFragment types)
      (fun _ => b.validate Capabilities.scalarFragment types) = .ok () at valid
    rw [except_unit_bind] at valid
    simp only [normalize, bind, Functor.map, Except.map, except_bind_ok, Except.pure] at normal
    rcases normal with ⟨an, na, bn, nb, equal⟩
    cases equal
    simp only [arithmetic_eq, requireSourceType_eq] at requirements
    obtain ⟨ar, br⟩ := requirements_children hash inputs an bn _ [] (by simpa using requirements)
    obtain ⟨av, ea, ac, aq, am⟩ := ia types aliases values environment an valid.1 na ar
    obtain ⟨bv, eb, bc, bq, bm⟩ := ib types aliases values environment bn valid.2 nb br
    apply normalized_success ctx hash implementation inputs aliases values environment.aliases _
      (ScalarExpression.mul a b leftSupported rightSupported) _
      (by simp only [normalize, na, nb]; rfl) ((av * bv) % ctx.modulus)
    exact (by simp [Expr.eval, ea, eb, implementation.modulus, Field.modulus, bind, Except.bind, Except.map, Except.pure] <;> rfl)
  | sub a b leftSupported rightSupported ia ib =>
    simp only [Expr.validate] at valid
    change Except.bind (a.validate Capabilities.scalarFragment types)
      (fun _ => b.validate Capabilities.scalarFragment types) = .ok () at valid
    rw [except_unit_bind] at valid
    simp only [normalize, bind, Functor.map, Except.map, except_bind_ok, Except.pure] at normal
    rcases normal with ⟨an, na, bn, nb, equal⟩
    cases equal
    simp only [subtraction_eq, requireSourceType_eq] at requirements
    obtain ⟨ar, br⟩ := requirements_children hash inputs an bn _ [] (by simpa using requirements)
    obtain ⟨av, ea, ac, aq, am⟩ := ia types aliases values environment an valid.1 na ar
    obtain ⟨bv, eb, bc, bq, bm⟩ := ib types aliases values environment bn valid.2 nb br
    apply normalized_success ctx hash implementation inputs aliases values environment.aliases _
      (ScalarExpression.sub a b leftSupported rightSupported) _
      (by simp only [normalize, na, nb]; rfl) ((ctx.modulus + av - bv) % ctx.modulus)
    exact (by simp [Expr.eval, ea, eb, implementation.modulus, Field.modulus, bind, Except.bind, Except.map, Except.pure] <;> rfl)
  | @uadd m n a b leftSupported rightSupported ia ib =>
    simp only [Expr.validate] at valid
    change Except.bind ((Ty.uint (m + n)).validate Capabilities.scalarFragment)
      (fun _ => Except.bind (a.validate Capabilities.scalarFragment types)
        (fun _ => b.validate Capabilities.scalarFragment types)) = .ok () at valid
    rw [except_unit_bind, except_unit_bind] at valid
    have typeBound := uint_valid_bound (m + n) valid.1
    simp only [normalize, bind, except_bind_ok, Except.pure] at normal
    rcases normal with ⟨an, na, bn, nb, equal⟩
    cases equal
    simp only [normalizeUIntAdd, requireSourceType_eq] at requirements
    obtain ⟨ar, br⟩ := requirements_children hash inputs an bn _ _ requirements
    obtain ⟨av, ea, ac, aq, am⟩ := ia types aliases values environment an valid.2.1 na ar
    obtain ⟨bv, eb, bc, bq, bm⟩ := ib types aliases values environment bn valid.2.2 nb br
    have range : av + bv ≤ m + n := Nat.add_le_add ac.2.2 bc.2.2
    have canonical : av + bv < ctx.modulus := by
      rw [implementation.modulus]
      exact Nat.lt_of_le_of_lt (Nat.le_trans range typeBound) ScalarPolicy.maxUint_lt_native
    apply normalized_success (ty := .uint (m + n)) ctx hash implementation inputs aliases values environment.aliases _
      (ScalarExpression.uadd a b leftSupported rightSupported) _
      (by simp only [normalize, na, nb]; rfl) (av + bv)
    simp only [Expr.eval, ea, eb, bind, Except.bind]
    change (if m + n ≤ ScalarPolicy.maxUint && av + bv ≤ m + n && av + bv < ctx.modulus
      then Except.ok (av + bv) else Except.error "scalar conversion exceeds unsigned bound") = Except.ok (av + bv)
    simp [typeBound, range, canonical]
  | @usub m n a b leftSupported rightSupported ia ib =>
    simp only [Expr.validate] at valid
    change Except.bind ((Ty.uint m).validate Capabilities.scalarFragment)
      (fun _ => Except.bind (a.validate Capabilities.scalarFragment types)
        (fun _ => b.validate Capabilities.scalarFragment types)) = .ok () at valid
    rw [except_unit_bind, except_unit_bind] at valid
    have typeBound := uint_valid_bound m valid.1
    simp only [normalize, bind, except_bind_ok, Except.pure] at normal
    rcases normal with ⟨an, na, bn, nb, equal⟩
    cases equal
    simp only [subtraction_eq, requireSourceType_eq] at requirements
    obtain ⟨ar, br⟩ := requirements_children hash inputs an bn _ _ requirements
    obtain ⟨av, ea, ac, aq, am⟩ := ia types aliases values environment an valid.2.1 na ar
    obtain ⟨bv, eb, bc, bq, bm⟩ := ib types aliases values environment bn valid.2.2 nb br
    have resultBound := requirements.1 (.binary "add" an.term (.unary "neg" bn.term), m)
      (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    simp [sourceScalar?, sourceNumber?, number] at am bm
    simp only [Prod.fst, Prod.snd] at resultBound
    rcases resultBound with ⟨found, meaning, bound⟩
    simp [interpret, ScalarTermMeaning.interpret?, am, bm] at meaning
    cases meaning
    change (scalar (av % Field.modulus + (scalar (Field.modulus - bv % Field.modulus)).val)).val ≤ m at bound
    rw [Nat.mod_eq_of_lt (show av < Field.modulus from ac.1),
      Nat.mod_eq_of_lt (show bv < Field.modulus from bc.1), subtraction_mod av bv bc.1] at bound
    change ((Field.modulus + av - bv) % Field.modulus) % Field.modulus ≤ m at bound
    rw [Nat.mod_mod] at bound
    have noUnderflow : ¬ av < bv := by
      intro underflow
      have rejected := unsigned_underflow_modulo_rejected av bv underflow (Nat.le_trans bc.2.2 bc.2.1)
      omega
    have range : av - bv ≤ m := Nat.le_trans (Nat.sub_le _ _) ac.2.2
    have canonical : av - bv < ctx.modulus := by
      rw [implementation.modulus]
      exact Nat.lt_of_le_of_lt (Nat.le_trans range typeBound) ScalarPolicy.maxUint_lt_native
    apply normalized_success ctx hash implementation inputs aliases values environment.aliases _
      (ScalarExpression.usub a b leftSupported rightSupported) _
      (by simp only [normalize, na, nb]; rfl) (av - bv)
    simp only [Expr.eval, ea, eb, bind, Except.bind, noUnderflow, ↓reduceIte]
    change (if m ≤ ScalarPolicy.maxUint && av - bv ≤ m && av - bv < ctx.modulus
      then Except.ok (av - bv) else Except.error "scalar conversion exceeds unsigned bound") = Except.ok (av - bv)
    simp [typeBound, range, canonical]
  | @umul m n a b leftSupported rightSupported ia ib =>
    simp only [Expr.validate] at valid
    change Except.bind ((Ty.uint (m * n)).validate Capabilities.scalarFragment)
      (fun _ => Except.bind (a.validate Capabilities.scalarFragment types)
        (fun _ => b.validate Capabilities.scalarFragment types)) = .ok () at valid
    rw [except_unit_bind, except_unit_bind] at valid
    have typeBound := uint_valid_bound (m * n) valid.1
    simp only [normalize, bind, except_bind_ok, Except.pure] at normal
    rcases normal with ⟨an, na, bn, nb, equal⟩
    cases equal
    simp only [arithmetic_eq, requireSourceType_eq] at requirements
    obtain ⟨ar, br⟩ := requirements_children hash inputs an bn _ _ requirements
    obtain ⟨av, ea, ac, aq, am⟩ := ia types aliases values environment an valid.2.1 na ar
    obtain ⟨bv, eb, bc, bq, bm⟩ := ib types aliases values environment bn valid.2.2 nb br
    have range : av * bv ≤ m * n := Nat.mul_le_mul ac.2.2 bc.2.2
    have canonical : av * bv < ctx.modulus := by
      rw [implementation.modulus]
      exact Nat.lt_of_le_of_lt (Nat.le_trans range typeBound) ScalarPolicy.maxUint_lt_native
    apply normalized_success (ty := .uint (m * n)) ctx hash implementation inputs aliases values environment.aliases _
      (ScalarExpression.umul a b leftSupported rightSupported) _
      (by simp only [normalize, na, nb]; rfl) (av * bv)
    simp only [Expr.eval, ea, eb, bind, Except.bind]
    change (if m * n ≤ ScalarPolicy.maxUint && av * bv ≤ m * n && av * bv < ctx.modulus
      then Except.ok (av * bv) else Except.error "scalar conversion exceeds unsigned bound") = Except.ok (av * bv)
    simp [typeBound, range, canonical]
  | @cast source target expression sourceType targetType valueSupported ih =>
    simp only [Expr.validate] at valid
    have scalarGuards : (target.isBytes || source.isBytes) = false ∧
        (target.isJubjub || source.isJubjub || target.isForeign || source.isForeign) = false := by
      cases sourceType <;> cases targetType <;> simp [Ty.isBytes, Ty.isJubjub, Ty.isForeign]
    rw [scalarGuards.1, scalarGuards.2] at valid
    simp only [(scalarType_notOpaque sourceType).1, (scalarType_notOpaque sourceType).2,
      (scalarType_notOpaque targetType).1, (scalarType_notOpaque targetType).2,
      Bool.or_false, Bool.false_eq_true, if_false] at valid
    change Except.bind (target.validate Capabilities.scalarFragment)
      (fun _ => expression.validate Capabilities.scalarFragment types) = .ok () at valid
    rw [except_unit_bind] at valid
    simp only [normalize, bind, except_bind_ok, pure, Except.pure] at normal
    rcases normal with ⟨vn, nv, equal⟩
    cases equal
    cases targetType with
    | native =>
      simp only [requireSourceType_eq] at requirements
      obtain ⟨result, ev, vc, vr, vm⟩ := ih types aliases values environment vn valid.2 nv requirements
      have sourceBound := scalar_number_canonical sourceType result vc
      apply normalized_success (ty := .native) ctx hash implementation inputs aliases values environment.aliases _
        (ScalarExpression.cast expression sourceType .native valueSupported) _
        (by simp only [normalize, nv]; rfl) (number sourceType result)
      have bound : number sourceType result < ctx.modulus := by
        simpa [implementation.modulus] using sourceBound
      have castEval := eval_cast_scalar ctx values expression sourceType .native result ev
      rw [castEval]
      simp [scalarCast, bound]
    | bool =>
      simp only [requireSourceType_eq] at requirements
      have child := requirements_child hash inputs vn _ _ requirements
      obtain ⟨result, ev, vc, vr, vm⟩ := ih types aliases values environment vn valid.2 nv child
      apply normalized_success (ty := .bool) ctx hash implementation inputs aliases values environment.aliases _
        (ScalarExpression.cast expression sourceType .bool valueSupported) _
        (by simp only [normalize, nv]; rfl) (number sourceType result != 0)
      have castEval := eval_cast_scalar ctx values expression sourceType .bool result ev
      rw [castEval]
      simp [scalarCast]
    | uint maximum =>
      simp only [requireSourceType_eq] at requirements
      have child := requirements_child hash inputs vn _ _ requirements
      obtain ⟨result, ev, vc, vr, vm⟩ := ih types aliases values environment vn valid.2 nv child
      have resultBound := requirements.1 (vn.term, maximum) (List.mem_append_right _ (List.mem_singleton.mpr rfl))
      simp only [Prod.fst, Prod.snd] at resultBound
      have vm' : interpret hash inputs vn.term = some (scalar (number sourceType result)) := by
        rw [sourceScalar_number sourceType result] at vm
        exact vm
      change ∃ value, interpret hash inputs vn.term = some value ∧ value.val ≤ maximum at resultBound
      rcases resultBound with ⟨bounded, boundedMeaning, bound⟩
      rw [vm'] at boundedMeaning
      cases boundedMeaning
      change (scalar (number sourceType result)).val ≤ maximum at bound
      have sourceBound := scalar_number_canonical sourceType result vc
      change number sourceType result % Field.modulus ≤ maximum at bound
      rw [Nat.mod_eq_of_lt sourceBound] at bound
      have typeBound := uint_valid_bound maximum valid.1
      have canonical : number sourceType result < ctx.modulus := by
        simpa [implementation.modulus] using sourceBound
      apply normalized_success (ty := .uint maximum) ctx hash implementation inputs aliases values environment.aliases _
        (ScalarExpression.cast expression sourceType (.uint maximum) valueSupported) _
        (by simp only [normalize, nv]; rfl) (number sourceType result)
      have castEval := eval_cast_scalar ctx values expression sourceType (.uint maximum) result ev
      rw [castEval]
      simp [scalarCast, typeBound, bound, canonical, scalar, Nat.mod_eq_of_lt sourceBound]
  | @letE source ty name expression body sourceScalar valueSupported bodySupported iv ib =>
    simp only [Expr.validate] at valid
    change Except.bind (expression.validate Capabilities.scalarFragment types)
      (fun _ => body.validate Capabilities.scalarFragment ((name, source) :: types)) = .ok () at valid
    rw [except_unit_bind] at valid
    simp only [normalize, bind, except_bind_ok, Except.pure] at normal
    rcases normal with ⟨vn, nv, bn, nb, equal⟩
    cases equal
    obtain ⟨vr, br⟩ := requirements_children hash inputs vn bn _ [] (by simpa using requirements)
    obtain ⟨result, ev, vc, vq, vm⟩ := iv types aliases values environment vn valid.1 nv vr
    obtain ⟨resultBody, eb, bc, bq, bm⟩ := ib ((name, source) :: types) ((name, vn.term) :: aliases)
      ((name, Value.pack source result) :: values)
      (environment.cons hash inputs aliases values types name source result vn.term
        vc vm) bn valid.2 nb br
    apply normalized_success (ty := ty) ctx hash implementation inputs aliases values environment.aliases _
      (ScalarExpression.letE name expression body sourceScalar valueSupported bodySupported) _
      (by simp only [normalize, nv, bind, Except.bind, nb]; rfl) resultBody
    simpa only [Expr.eval, ev, bind, Except.bind] using eb
  | @assertE ty condition body conditionSupported bodySupported ic ib =>
    simp only [Expr.validate] at valid
    change Except.bind (condition.validate Capabilities.scalarFragment types)
      (fun _ => body.validate Capabilities.scalarFragment types) = .ok () at valid
    rw [except_unit_bind] at valid
    simp only [normalize, bind, except_bind_ok, Except.pure] at normal
    rcases normal with ⟨cn, nc, bn, nb, equal⟩
    cases equal
    have cr : Requirements hash inputs cn := by
      constructor
      · intro requirement member
        exact requirements.1 requirement (List.mem_append_left _ member)
      · intro assertion member
        exact requirements.2 assertion (List.mem_append_left _ (List.mem_append_left _ member))
    have br : Requirements hash inputs bn := by
      constructor
      · intro requirement member
        exact requirements.1 requirement (List.mem_append_right _ member)
      · intro assertion member
        exact requirements.2 assertion (List.mem_append_right _ member)
    obtain ⟨cv, ec, cc, cq, cm⟩ := ic types aliases values environment cn valid.1 nc cr
    obtain ⟨bv, eb, bc, bq, bm⟩ := ib types aliases values environment bn valid.2 nb br
    have asserted : interpret hash inputs cn.term = some one := requirements.2 cn.term
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
    have conditionTrue : cv = true := by
      rw [cm] at asserted
      simp [sourceScalar?, sourceNumber?, scalar_one, scalar_zero] at asserted
      cases cv
      · exact False.elim (zero_ne_one asserted)
      · rfl
    subst cv
    apply normalized_success (ty := ty) ctx hash implementation inputs aliases values environment.aliases _
      (ScalarExpression.assertE condition body conditionSupported bodySupported) _
      (by simp only [normalize, nc, nb]; rfl) bv
    simpa only [Expr.eval, ec, bind, Except.bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.pure] using eb
  | copyValue expression supported ih =>
    simp only [Expr.validate, Expr.eval, normalize] at valid normal ⊢
    exact ih types aliases values environment normalized valid normal requirements
  | disclose span expression supported ih =>
    simp only [Expr.validate, Expr.eval, normalize] at valid normal ⊢
    exact ih types aliases values environment normalized valid normal requirements
  | @eq ty a b scalarType leftSupported rightSupported ia ib =>
    simp only [Expr.validate] at valid
    have scalarKinds : ty.isBytes = false ∧ ty.isJubjub = false ∧ ty.isForeign = false := by
      cases scalarType <;> simp [Ty.isBytes, Ty.isJubjub, Ty.isForeign]
    simp only [scalarKinds.1, scalarKinds.2.1, scalarKinds.2.2,
      (scalarType_notOpaque scalarType).1, (scalarType_notOpaque scalarType).2,
      Bool.or_false, Bool.false_eq_true, if_false] at valid
    change Except.bind (a.validate Capabilities.scalarFragment types)
      (fun _ => b.validate Capabilities.scalarFragment types) = .ok () at valid
    rw [except_unit_bind] at valid
    simp only [normalize, bind, except_bind_ok, Except.pure] at normal
    rcases normal with ⟨an, na, bn, nb, equal⟩
    cases equal
    simp only [arithmetic_eq, requireSourceType_eq] at requirements
    obtain ⟨ar, br⟩ := requirements_children hash inputs an bn _ _ requirements
    obtain ⟨av, ea, ac, aq, am⟩ := ia types aliases values environment an valid.1 na ar
    obtain ⟨bv, eb, bc, bq, bm⟩ := ib types aliases values environment bn valid.2 nb br
    have equalityAdmission := ScalarExpression.eq a b scalarType leftSupported rightSupported
    cases scalarType <;>
      apply normalized_success (ty := .bool) ctx hash implementation inputs aliases values environment.aliases _
        equalityAdmission _
        (by simp only [normalize, na, nb]; rfl) (av == bv) <;>
      simp only [Expr.eval, ea, eb, bind, Except.bind] <;> rfl
  | @select ty c a b scalarType conditionSupported yesSupported noSupported ic ia ib =>
    simp only [Expr.validate] at valid
    have scalarKinds : ty.isBytes = false ∧ ty.isJubjub = false ∧ ty.isForeign = false := by
      cases scalarType <;> simp [Ty.isBytes, Ty.isJubjub, Ty.isForeign]
    simp only [scalarKinds.1, scalarKinds.2.1, scalarKinds.2.2,
      (scalarType_notOpaque scalarType).1, (scalarType_notOpaque scalarType).2,
      Bool.or_false, Bool.false_eq_true, if_false] at valid
    change Except.bind (c.validate Capabilities.scalarFragment types)
      (fun _ => Except.bind (a.validate Capabilities.scalarFragment types)
        (fun _ => b.validate Capabilities.scalarFragment types)) = .ok () at valid
    rw [except_unit_bind, except_unit_bind] at valid
    simp only [normalize, bind, except_bind_ok, Except.pure] at normal
    rcases normal with ⟨cn, nc, an, na, bn, nb, equal⟩
    cases equal
    simp only [requireSourceType_eq] at requirements
    have baseRequirements : Requirements hash inputs
        {term := cn.term.select an.term bn.term, bounds := cn.bounds ++ an.bounds ++ bn.bounds,
          assertions := cn.assertions ++ an.assertions ++ bn.assertions} := by
      constructor
      · intro requirement member
        apply requirements.1 requirement
        cases scalarType with
        | native => exact member
        | bool => exact List.mem_append_left _ member
        | uint maximum => exact List.mem_append_left _ member
      · exact requirements.2
    obtain ⟨car, br⟩ := requirements_children hash inputs
      {term := an.term, bounds := cn.bounds ++ an.bounds, assertions := cn.assertions ++ an.assertions}
      bn _ [] (by simpa using baseRequirements)
    obtain ⟨cr, ar⟩ := requirements_children hash inputs cn an _ [] (by simpa using car)
    obtain ⟨cv, ec, cc, cq, cm⟩ := ic types aliases values environment cn valid.1 nc cr
    obtain ⟨av, ea, ac, aq, am⟩ := ia types aliases values environment an valid.2.1 na ar
    obtain ⟨bv, eb, bc, bq, bm⟩ := ib types aliases values environment bn valid.2.2 nb br
    apply normalized_success (ty := ty) ctx hash implementation inputs aliases values environment.aliases _
      (ScalarExpression.select c a b scalarType conditionSupported yesSupported noSupported) _
      (by simp only [normalize, nc, na, nb]; rfl) (if cv then av else bv)
    simp only [Expr.eval, ec, ea, eb, bind, Except.bind]
    rfl
  | poseidon2 domain a b leftSupported rightSupported ia ib =>
    simp only [Expr.validate] at valid
    split at valid
    next invalid => cases valid
    next validDomain =>
      have domainBound : domain < Field.modulus := Nat.lt_of_not_ge validDomain
      change Except.bind (a.validate Capabilities.scalarFragment types)
        (fun _ => b.validate Capabilities.scalarFragment types) = .ok () at valid
      rw [except_unit_bind] at valid
      simp only [normalize, bind, except_bind_ok, Except.pure] at normal
      rcases normal with ⟨an, na, bn, nb, equal⟩
      cases equal
      obtain ⟨ar, br⟩ := requirements_children hash inputs an bn _ [] (by simpa using requirements)
      obtain ⟨av, ea, ac, aq, am⟩ := ia types aliases values environment an valid.1 na ar
      obtain ⟨bv, eb, bc, bq, bm⟩ := ib types aliases values environment bn valid.2 nb br
      have oracle : ctx.poseidon2 domain av bv = .ok (hash [scalar domain, scalar av, scalar bv]).val := by
        simpa only [scalar, Nat.mod_eq_of_lt domainBound,
          Nat.mod_eq_of_lt (show av < Field.modulus from ac.1),
          Nat.mod_eq_of_lt (show bv < Field.modulus from bc.1)] using
          implementation.calls (scalar domain) (scalar av) (scalar bv)
      have resultBound : (hash [scalar domain, scalar av, scalar bv]).val < ctx.modulus := by
        rw [implementation.modulus]
        exact (hash _).isLt
      have domainCanonical : ¬domain ≥ ctx.modulus := by
        rw [implementation.modulus]
        exact Nat.not_le_of_gt domainBound
      apply normalized_success ctx hash implementation inputs aliases values environment.aliases _
        (ScalarExpression.poseidon2 domain a b leftSupported rightSupported) _
        (by simp only [normalize, na, nb]; rfl) (hash [scalar domain, scalar av, scalar bv]).val
      simp [Expr.eval, domainCanonical, ea, eb, oracle, bind, Except.bind, pure,
        Except.pure, Nat.not_le_of_gt resultBound] <;> rfl
/-- Exact scalar normalization semantics. This statement derives successful
source execution from the normalized obligations rather than assuming success. -/
theorem normalize_exact (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (types : TypeEnv) (aliases : AliasEnvironment) (values : EvalEnv)
    (environment : TypedEnvironment hash inputs aliases values types)
    (expression : Expr ty) (admission : ScalarExpression expression) (normalized : Normalized)
    (valid : expression.validate Capabilities.scalarFragment types = .ok ())
    (normal : normalize aliases expression = .ok normalized) :
    Requirements hash inputs normalized ↔ ∃ value, expression.eval ctx values = .ok value := by
  constructor
  · intro requirements
    obtain ⟨value, success, _⟩ := normalize_sound ctx hash implementation inputs types aliases values
      environment expression admission normalized valid normal requirements
    exact ⟨value, success⟩
  · rintro ⟨value, success⟩
    obtain ⟨_, _, represented⟩ := normalized_success ctx hash implementation inputs aliases values
      environment.aliases expression admission normalized normal value success
    exact represented.2.1

end Noctium.Verification.ScalarNormalization
