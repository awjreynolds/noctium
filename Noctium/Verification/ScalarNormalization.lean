import Noctium.Backend.NativeExpected
import Noctium.Verification.NativeRelation
import Noctium.Verification.ScalarTermMeaning

namespace Noctium.Verification.ScalarNormalization

open Backend.Native NativeRelation

/-- Capability set used by the scalar-normalization proof. Keep the scalar
operations admitted by `ScalarExpression`, including equality and selection,
while leaving unrelated source features disabled. -/
def Capabilities.scalarFragment : Capabilities := Capabilities.crypto

/-- Keep scalar meaning partial. Unsupported byte and operation terms have no
field value and cannot enter scalar range or assertion checks. -/
abbrev interpret := ScalarTermMeaning.interpret?

/-- Project only source values with native-field meanings. Unsupported source
types remain absent instead of acquiring a synthetic numeric value. -/
def sourceNumber? : (ty : Ty) → ty.Denote → Except String Nat
  | .native, value | .uint _, value => .ok value
  | .bool, value => .ok (if value then 1 else 0)
  | .bytes _, _ | .opaqueBytes, _ => .error "byte strings do not support scalar conversion"
  | .opaqueString, _ => .error "opaque strings do not support scalar conversion"
  | .jubjubScalar, _ => .error "Jubjub scalars do not support scalar conversion"
  | .jubjubPoint, _ => .error "Jubjub points do not support scalar conversion"
  | .foreign _, _ => .error "foreign values do not support scalar conversion"

/-- A source value has a numeric scalar projection only for Native, Bool and UInt. -/
inductive ScalarType : Ty → Type where
  | native : ScalarType .native
  | bool : ScalarType .bool
  | uint (maximum : Nat) : ScalarType (.uint maximum)

private theorem scalarType_supported {ty : Ty} (scalarType : ScalarType ty) :
    ty.isBytes = false ∧ ty.isJubjub = false ∧ ty.isForeign = false := by
  cases scalarType <;> simp [Ty.isBytes, Ty.isJubjub, Ty.isForeign]

/-- Extract the source number only after the type carries scalar admission. -/
def number {ty : Ty} : ScalarType ty → ty.Denote → Nat
  | .native, value => value
  | .bool, value => if value then 1 else 0
  | .uint _, value => value

def scalarCast (ctx : EvalContext) : (target : Ty) → ScalarType target → Nat →
    Except String target.Denote
  | .native, .native, value =>
      if value < ctx.modulus then .ok value else .error "noncanonical scalar conversion"
  | .bool, .bool, value => .ok (value != 0)
  | .uint maximum, .uint _, value =>
      if maximum ≤ ScalarPolicy.maxUint && value ≤ maximum && value < ctx.modulus then
        .ok value
      else .error "scalar conversion exceeds unsigned bound"

theorem eval_cast_scalar (ctx : EvalContext) (env : EvalEnv)
    {source target : Ty} (expression : Expr source) (sourceType : ScalarType source)
    (targetType : ScalarType target) (value : source.Denote)
    (evaluation : expression.eval ctx env = .ok value) :
    Expr.eval ctx env (.cast target expression) =
      scalarCast ctx target targetType (number sourceType value) := by
  cases sourceType <;> cases targetType <;>
    simp only [Expr.eval, evaluation, bind, Except.bind, pure, Except.pure] <;> rfl

/-- The exact fragment covered by scalar normalization soundness. It includes
Native, Bool and UInt literals and references, their established arithmetic,
casts, lets, assertions, disclosures, copies, equality and selection, plus
Poseidon2 over Native values. Byte, Jubjub, foreign and unsupported gate
expressions receive no admission. -/
inductive ScalarExpression : Expr ty → Prop where
  | native (value : Nat) : ScalarExpression (.native value)
  | bool (value : Bool) : ScalarExpression (.bool value)
  | uint (maximum value : Nat) : ScalarExpression (.uint maximum value)
  | ref {ty : Ty} (name : String) (scalarType : ScalarType ty) :
      ScalarExpression (.ref (ty := ty) name)
  | add (left right : Expr .native) (leftSupported : ScalarExpression left)
      (rightSupported : ScalarExpression right) : ScalarExpression (.add left right)
  | mul (left right : Expr .native) (leftSupported : ScalarExpression left)
      (rightSupported : ScalarExpression right) : ScalarExpression (.mul left right)
  | sub (left right : Expr .native) (leftSupported : ScalarExpression left)
      (rightSupported : ScalarExpression right) : ScalarExpression (.sub left right)
  | uadd {m n : Nat} (left : Expr (.uint m)) (right : Expr (.uint n))
      (leftSupported : ScalarExpression left) (rightSupported : ScalarExpression right) :
      ScalarExpression (.uadd left right)
  | usub {m n : Nat} (left : Expr (.uint m)) (right : Expr (.uint n))
      (leftSupported : ScalarExpression left) (rightSupported : ScalarExpression right) :
      ScalarExpression (.usub left right)
  | umul {m n : Nat} (left : Expr (.uint m)) (right : Expr (.uint n))
      (leftSupported : ScalarExpression left) (rightSupported : ScalarExpression right) :
      ScalarExpression (.umul left right)
  | cast {source target : Ty} (value : Expr source)
      (sourceType : ScalarType source) (targetType : ScalarType target)
      (valueSupported : ScalarExpression value) : ScalarExpression (.cast target value)
  | letE {source target : Ty} (name : String) (value : Expr source) (body : Expr target)
      (sourceScalar : ScalarType source) (valueSupported : ScalarExpression value)
      (bodySupported : ScalarExpression body) : ScalarExpression (.letE name value body)
  | assertE {target : Ty} (condition : Expr .bool) (body : Expr target)
      (conditionSupported : ScalarExpression condition) (bodySupported : ScalarExpression body) :
      ScalarExpression (.assertE condition body)
  | copyValue {ty : Ty} (value : Expr ty) (supported : ScalarExpression value) :
      ScalarExpression (.copyValue value)
  | disclose {ty : Ty} (span : SourceSpan) (value : Expr ty)
      (supported : ScalarExpression value) : ScalarExpression (.disclose span value)
  | eq {ty : Ty} (left right : Expr ty) (scalarType : ScalarType ty)
      (leftSupported : ScalarExpression left) (rightSupported : ScalarExpression right) :
      ScalarExpression (.eq left right)
  | select {ty : Ty} (condition : Expr .bool) (yes no : Expr ty)
      (scalarType : ScalarType ty) (conditionSupported : ScalarExpression condition)
      (yesSupported : ScalarExpression yes) (noSupported : ScalarExpression no) :
      ScalarExpression (.select condition yes no)
  | poseidon2 (domain : Nat) (left right : Expr .native)
      (leftSupported : ScalarExpression left) (rightSupported : ScalarExpression right) :
      ScalarExpression (.poseidon2 domain left right)

/-- A source value is admitted only when its partial numeric projection exists,
fits the native field, and satisfies its declared scalar range. -/
def Canonical (ty : Ty) (value : ty.Denote) : Prop :=
  match sourceNumber? ty value with
  | .error _ => False
  | .ok number =>
    number < Field.modulus ∧ match ty with
      | .native => True
      | .bool => True
      | .uint maximum => maximum ≤ ScalarPolicy.maxUint ∧ value ≤ maximum
      | .bytes _ | .opaqueBytes | .opaqueString | .jubjubScalar | .jubjubPoint | .foreign _ => False

/-- The source-side scalar interpretation is partial for the same admission
boundary as `sourceNumber?`. -/
def sourceScalar? (ty : Ty) (value : ty.Denote) : Option Scalar :=
  match sourceNumber? ty value with
  | .ok number => some (scalar number)
  | .error _ => none

@[simp] theorem scalar_zero : scalar 0 = zero := by apply Fin.ext; rfl
@[simp] theorem scalar_one : scalar 1 = one := by apply Fin.ext; decide

theorem sourceScalar_number {ty : Ty} (scalarType : ScalarType ty)
    (value : ty.Denote) :
    sourceScalar? ty value = some (scalar (number scalarType value)) := by
  cases scalarType <;> cases value <;> simp [sourceScalar?, sourceNumber?, number,
    scalar_zero, scalar_one]

theorem scalar_number_canonical {ty : Ty} (scalarType : ScalarType ty)
    (value : ty.Denote) (canonical : Canonical ty value) :
    number scalarType value < Field.modulus := by
  cases scalarType <;> simp_all [Canonical, sourceNumber?, number]

/-- Bounds and assertions are admitted only when the partial symbolic meaning
returns an explicit scalar value. -/
abbrev Requirements := ScalarTermMeaning.Requirements

/-- All aliases, including a shadowing let alias, refer to the first visible
binding. Every numeric value is canonical before the alias is used. -/
def AliasAgreement (hash : Hash) (inputs : Assignment) (aliases : AliasEnvironment)
    (values : EvalEnv) : Prop :=
  ∀ name ty raw value, values.lookup name = some raw → raw.as ty = some value →
    Canonical ty value ∧ ∃ term, aliases.lookup name = some term ∧
      interpret hash inputs term = sourceScalar? ty value

/-- Observable normal-form meaning. This is intentionally independent of an
honest SSA witness: `inputs` fixes only the declared source values. -/
def Represents (hash : Hash) (inputs : Assignment) (ty : Ty)
    (normalized : Normalized) (value : ty.Denote) : Prop :=
  Canonical ty value ∧ Requirements hash inputs normalized ∧
    interpret hash inputs normalized.term = sourceScalar? ty value

@[simp] theorem number_pack_as (ty : Ty) (value : ty.Denote)
    (canonical : Canonical ty value) :
    (Value.pack ty value).as ty = some value := by
  cases ty <;> simp_all [Canonical, sourceNumber?, Value.pack, Value.as]

@[simp] theorem sourceNumber_bool (value : Bool) :
    sourceNumber? .bool value = .ok (if value then 1 else 0) := rfl

@[simp] theorem interpret_constant (hash : Hash) (inputs : Assignment) (value : Nat) :
    interpret hash inputs (.constant value) = some (scalar value) := by simp [interpret]

@[simp] theorem interpret_input (hash : Hash) (inputs : Assignment) (name : String) :
    interpret hash inputs (.input name) = some (inputs name) := by simp [interpret]

/-- The semantic environment extends in the same order as the actual normalizer.
No global name-uniqueness assumption forbids valid let shadowing. -/
theorem aliasAgreement_cons (hash : Hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv) (name : String) (ty : Ty)
    (value : ty.Denote) (term : Term)
    (agreement : AliasAgreement hash inputs aliases values)
    (canonical : Canonical ty value)
    (meaning : interpret hash inputs term = sourceScalar? ty value) :
    AliasAgreement hash inputs ((name, term) :: aliases) ((name, Value.pack ty value) :: values) := by
  intro found foundTy raw foundValue lookup typed
  by_cases same : found = name
  · subst found
    simp only [List.lookup_cons, beq_self_eq_true] at lookup
    cases lookup
    cases ty <;> cases foundTy <;> simp_all [Value.pack, Value.as, Canonical, sourceNumber?]
    all_goals try (rcases typed with ⟨rfl, rfl⟩)
    all_goals simp_all [sourceScalar?, sourceNumber?]
  · have unequal : (found == name) = false := by simp [same]
    simp only [List.lookup_cons, unequal] at lookup
    obtain ⟨canonical, existing, lookup, meaning⟩ := agreement found foundTy raw foundValue lookup typed
    exact ⟨canonical, existing, by simp [List.lookup_cons, unequal, lookup], meaning⟩

end Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.ScalarNormalization
open Backend.Native NativeRelation

private theorem requirements_empty (hash : Hash) (inputs : Assignment) (term : Term) :
    Requirements hash inputs {term := term} := by
  simp [Requirements, ScalarTermMeaning.Requirements]

private theorem bool_requirements (hash : Hash) (inputs : Assignment) (term : Term)
    (value : Bool) (meaning : interpret hash inputs term = some (bit value)) :
    Requirements hash inputs {term, bounds := [(term, 1)]} := by
  constructor
  · intro requirement member
    have same : requirement = (term, 1) := List.mem_singleton.mp member
    subst requirement
    change ∃ found : Scalar, interpret hash inputs term = some found ∧ found.val ≤ 1
    cases value
    · refine ⟨zero, ?_, ?_⟩
      simpa [bit, scalar_zero] using meaning
      change zero.val ≤ 1
      decide
    · refine ⟨one, ?_, ?_⟩
      simpa [bit, scalar_one] using meaning
      change one.val ≤ 1
      decide
  · intro assertion member
    simp at member

private theorem uint_requirements (hash : Hash) (inputs : Assignment) (term : Term)
    (maximum value : Nat) (bound : (scalar value).val ≤ maximum)
    (meaning : interpret hash inputs term = some (scalar value)) :
    Requirements hash inputs {term, bounds := [(term, maximum)]} := by
  constructor
  · intro requirement member
    have same : requirement = (term, maximum) := List.mem_singleton.mp member
    subst requirement
    change ∃ found : Scalar, interpret hash inputs term = some found ∧ found.val ≤ maximum
    refine ⟨scalar value, meaning, ?_⟩
    exact bound
  · intro assertion member
    simp at member

@[simp] theorem interpret_add (hash : Hash) (inputs : Assignment) (left right : Term) :
    interpret hash inputs (.binary "add" left right) =
      (interpret hash inputs left).bind fun leftValue =>
        (interpret hash inputs right).bind fun rightValue =>
          scalar (leftValue.val + rightValue.val) := by
  simp [interpret, ScalarTermMeaning.interpret?]

@[simp] theorem interpret_mul (hash : Hash) (inputs : Assignment) (left right : Term) :
    interpret hash inputs (.binary "mul" left right) =
      (interpret hash inputs left).bind fun leftValue =>
        (interpret hash inputs right).bind fun rightValue =>
          scalar (leftValue.val * rightValue.val) := by
  simp [interpret, ScalarTermMeaning.interpret?]

@[simp] theorem interpret_neg (hash : Hash) (inputs : Assignment) (value : Term) :
    interpret hash inputs (.unary "neg" value) =
      (interpret hash inputs value).bind fun inner => some (scalar (Field.modulus - inner.val)) := by
  simp [interpret, ScalarTermMeaning.interpret?]

private theorem bit_sourceScalar (b : Bool) : bit b = sourceScalar? .bool b := by
  cases b <;> simp [sourceScalar?, sourceNumber?, bit, scalar_zero, scalar_one]

private theorem native_canonical (number : Nat) (bound : number < Field.modulus) :
    Canonical .native number := by
  change number < Field.modulus ∧ True
  exact ⟨bound, trivial⟩

private theorem scalar_eq_zero (value : Nat) (bound : value < Field.modulus) :
    scalar value = zero ↔ value = 0 := by
  constructor
  · intro equality
    have raw := congrArg Fin.val equality
    simpa [scalar, zero, Nat.mod_eq_of_lt bound] using raw
  · intro equality
    subst value
    exact scalar_zero

@[simp] theorem interpret_testEq (hash : Hash) (inputs : Assignment) (left right : Term) :
    interpret hash inputs (.binary "test_eq" left right) =
      (interpret hash inputs left).bind fun leftValue =>
        (interpret hash inputs right).bind fun rightValue =>
          bit (decide (leftValue = rightValue)) := by
  simp [interpret, ScalarTermMeaning.interpret?]

@[simp] theorem interpret_not (hash : Hash) (inputs : Assignment) (value : Term) :
    interpret hash inputs (.unary "not" value) =
      (interpret hash inputs value).bind fun inner => some (bit (decide (inner = zero))) := by
  simp [interpret, ScalarTermMeaning.interpret?]

private theorem scalar_numbers_equal (left right : Nat)
    (hl : left < Field.modulus) (hr : right < Field.modulus) :
    scalar left = scalar right ↔ left = right := by
  constructor
  · intro equality
    have raw := congrArg Fin.val equality
    simpa only [scalar, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr] using raw
  · exact congrArg scalar

private theorem bool_canonical (value : Bool) : Canonical .bool value := by
  cases value <;> simp [Canonical, sourceNumber?] <;> decide

private theorem canonical_projection {ty : Ty} {value : ty.Denote}
    (canonical : Canonical ty value) : ∃ number, sourceNumber? ty value = .ok number ∧
      number < Field.modulus := by
  cases found : sourceNumber? ty value with
  | error message => simp [Canonical, found] at canonical
  | ok number =>
    unfold Canonical at canonical
    rw [found] at canonical
    exact ⟨number, rfl, canonical.1⟩

@[simp] theorem interpret_select (hash : Hash) (inputs : Assignment) (condition yes no : Term) :
    interpret hash inputs (.select condition yes no) =
      (interpret hash inputs condition).bind fun conditionValue =>
        if conditionValue = one then interpret hash inputs yes else interpret hash inputs no := by
  simp [interpret, ScalarTermMeaning.interpret?]

@[simp] theorem interpret_hash (hash : Hash) (inputs : Assignment) (values : List Term) :
    interpret hash inputs (.hash values) =
      (values.mapM (interpret hash inputs)).bind fun values => some (hash values) := by
  simp [interpret, ScalarTermMeaning.interpret?]

theorem subtraction_mod (a b : Nat) (hb : b < Field.modulus) :
    scalar (a + (scalar (Field.modulus - b)).val) = scalar ((Field.modulus + a - b) % Field.modulus) := by
  apply Fin.ext
  change (a + (Field.modulus - b) % Field.modulus) % Field.modulus =
    ((Field.modulus + a - b) % Field.modulus) % Field.modulus
  rw [Nat.mod_mod, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  congr 1
  omega

private theorem requirements_join (hash : Hash) (inputs : Assignment)
    (left right : Normalized) (term : Term)
    (hl : Requirements hash inputs left) (hr : Requirements hash inputs right) :
    Requirements hash inputs {term := term, bounds := left.bounds ++ right.bounds, assertions := left.assertions ++ right.assertions} := by
  exact ScalarTermMeaning.requirements_join hash inputs left right term hl hr

private def typeBounds (ty : Ty) (term : Term) (bounds : List (Term × Nat)) : List (Term × Nat) :=
  match ty with
  | .native => bounds
  | .bool => bounds ++ [(term, 1)]
  | .uint maximum => bounds ++ [(term, maximum)]
  | .bytes _ | .opaqueBytes | .opaqueString | .jubjubScalar | .jubjubPoint | .foreign _ => bounds

private theorem represent_with_bound (hash : Hash) (inputs : Assignment) (ty : Ty)
    (term : Term) (bounds : List (Term × Nat)) (assertions : List Term)
    (value : ty.Denote) (canonical : Canonical ty value)
    (requirements : Requirements hash inputs {term, bounds, assertions})
    (meaning : interpret hash inputs term = sourceScalar? ty value) :
    Represents hash inputs ty {term, assertions, bounds := typeBounds ty term bounds} value := by
  refine ⟨canonical, ?_, meaning⟩
  constructor
  · intro requirement member
    cases ty with
    | native => exact requirements.1 requirement member
    | bool =>
      rcases List.mem_append.mp member with member | member
      · exact requirements.1 requirement member
      · have same := List.mem_singleton.mp member
        subst requirement
        cases value
        · refine ⟨zero, by simpa [sourceScalar?, sourceNumber?, scalar_zero] using meaning, ?_⟩
          change zero.val ≤ 1
          decide
        · refine ⟨one, by simpa [sourceScalar?, sourceNumber?, scalar_one] using meaning, ?_⟩
          change one.val ≤ 1
          decide
    | uint maximum =>
      rcases List.mem_append.mp member with member | member
      · exact requirements.1 requirement member
      · have same := List.mem_singleton.mp member
        subst requirement
        refine ⟨scalar value, ?_, ?_⟩
        · simpa [sourceScalar?, sourceNumber?] using meaning
        · simpa [scalar, Nat.mod_eq_of_lt canonical.1] using canonical.2.2
    | bytes _ | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ => cases canonical
  · exact requirements.2

/-- Successful source evaluation establishes every range and assertion retained
by normalization, including unused partial computations and both select arms. -/
theorem normalize_success (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv)
    (agreement : AliasAgreement hash inputs aliases values)
    (expression : Expr ty) (admission : ScalarExpression expression) (value : ty.Denote)
    (success : expression.eval ctx values = .ok value) :
    ∃ normalized, normalize aliases expression = .ok normalized ∧
      Represents hash inputs ty normalized value := by
  induction admission generalizing aliases values with
  | native n =>
    simp only [Expr.eval] at success
    split at success
    next h =>
      cases success
      refine ⟨{term := .constant n}, by simp [normalize, pure, Except.pure], ?_⟩
      refine ⟨?_, requirements_empty _ _ _, ?_⟩
      · simpa [Canonical, sourceNumber?, implementation.modulus] using h
      · simp [sourceScalar?, sourceNumber?]
    next h => cases success
  | bool b =>
    simp only [Expr.eval] at success
    cases success
    let term : Term := .constant (if b then 1 else 0)
    refine ⟨{term, bounds := [(term, 1)]}, ?_, ?_⟩
    · simp [normalize, term, requireSourceType_eq, pure, Except.pure]
    have constantMeaning : interpret hash inputs term = some (bit b) := by
      cases b <;> simp [interpret, term, bit, scalar_zero, scalar_one]
    refine ⟨bool_canonical b, bool_requirements _ _ term b constantMeaning, ?_⟩
    exact constantMeaning.trans (bit_sourceScalar b)
  | uint maximum n =>
    simp only [Expr.eval] at success
    split at success
    next h =>
      cases success
      refine ⟨{term := .constant n, bounds := [(.constant n, maximum)]}, ?_, ?_⟩
      · simp [normalize, requireSourceType_eq, pure, Except.pure]
      change (maximum ≤ ScalarPolicy.maxUint && n ≤ maximum && n < ctx.modulus) = true at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨⟨hmaximum, hvalue⟩, hfield⟩
      simp [Represents, Canonical, sourceNumber?, sourceScalar?, Requirements,
        ScalarTermMeaning.Requirements, requireSourceType_eq,
        scalar, Nat.mod_eq_of_lt (show n < Field.modulus by simpa [implementation.modulus] using hfield), hmaximum, hvalue,
        show n < Field.modulus by simpa [implementation.modulus] using hfield]
    next h => cases success
  | @ref ty name scalarType =>
    simp only [Expr.eval] at success
    cases lookup : values.lookup name with
    | none => simp [lookup] at success
    | some raw =>
      simp only [lookup] at success
      cases typed : raw.as ty with
      | none => simp [typed] at success
      | some result =>
        simp only [typed] at success
        split at success
        next h => cases success
        next h =>
          cases success
          obtain ⟨canonical, term, alias, meaning⟩ := agreement name ty raw value lookup typed
          refine ⟨_, by simp only [normalize, alias]; rfl, ?_⟩
          simp only [requireSourceType_eq]
          refine ⟨canonical, ?_, meaning⟩
          cases scalarType with
          | native => simp [Requirements, ScalarTermMeaning.Requirements]
          | bool =>
            have boolMeaning : interpret hash inputs term = some (bit value) := by
              cases value <;> simpa [sourceScalar?, sourceNumber?, bit, scalar_zero, scalar_one] using meaning
            exact bool_requirements _ _ term value boolMeaning
          | uint maximum =>
            have bound : (scalar value).val ≤ maximum := by
              change value % Field.modulus ≤ maximum
              have fieldBound : value < Field.modulus := by
                rcases canonical_projection canonical with ⟨number, projected, fieldBound⟩
                have numberEq : number = value := by simpa [sourceNumber?] using projected.symm
                simpa [numberEq] using fieldBound
              rw [Nat.mod_eq_of_lt fieldBound]
              exact canonical.2.2
            have meaning' : interpret hash inputs term = some (scalar value) := by
              simpa [sourceScalar?, sourceNumber?] using meaning
            exact uint_requirements _ _ term maximum value bound meaning'
  | add a b leftSupported rightSupported ia ib =>
    cases ea : a.eval ctx values with
    | error message => simp [Expr.eval, ea, implementation.modulus, Field.modulus, bind, pure, Except.bind, Except.map, Except.pure] at success
    | ok av =>
      cases eb : b.eval ctx values with
      | error message => simp [Expr.eval, ea, eb, implementation.modulus, Field.modulus, bind, pure, Except.bind, Except.map, Except.pure] at success
      | ok bv =>
        obtain ⟨an, na, ac, ar, am⟩ := ia aliases values agreement av ea
        obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement bv eb
        simp [Expr.eval, ea, eb, implementation.modulus, Field.modulus, bind, pure, Except.bind, Except.map, Except.pure] at success
        cases success
        refine ⟨_, by simp only [normalize, na, nb]; rfl, ?_⟩
        simp only [arithmetic_eq, requireSourceType_eq]
        refine ⟨native_canonical _ (Nat.mod_lt _ (show 0 < Field.modulus by decide)),
          requirements_join _ _ _ _ _ ar br, ?_⟩
        simp [interpret_add, am, bm, sourceScalar?, sourceNumber?]
        change scalar ((av % Field.modulus) + (bv % Field.modulus)) = scalar ((av + bv) % Field.modulus)
        simp [scalar, Nat.mod_eq_of_lt (show av < Field.modulus from ac.1),
          Nat.mod_eq_of_lt (show bv < Field.modulus from bc.1)]
  | mul a b leftSupported rightSupported ia ib =>
    cases ea : a.eval ctx values with
    | error message => simp [Expr.eval, ea, implementation.modulus, Field.modulus, bind, pure, Except.bind, Except.map, Except.pure] at success
    | ok av =>
      cases eb : b.eval ctx values with
      | error message => simp [Expr.eval, ea, eb, implementation.modulus, Field.modulus, bind, pure, Except.bind, Except.map, Except.pure] at success
      | ok bv =>
        obtain ⟨an, na, ac, ar, am⟩ := ia aliases values agreement av ea
        obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement bv eb
        simp [Expr.eval, ea, eb, implementation.modulus, Field.modulus, bind, pure, Except.bind, Except.map, Except.pure] at success
        cases success
        refine ⟨_, by simp only [normalize, na, nb]; rfl, ?_⟩
        simp only [arithmetic_eq, requireSourceType_eq]
        refine ⟨native_canonical _ (Nat.mod_lt _ (show 0 < Field.modulus by decide)),
          requirements_join _ _ _ _ _ ar br, ?_⟩
        simp [interpret_mul, am, bm, sourceScalar?, sourceNumber?]
        change scalar ((av % Field.modulus) * (bv % Field.modulus)) = scalar ((av * bv) % Field.modulus)
        simp [scalar, Nat.mod_eq_of_lt (show av < Field.modulus from ac.1),
          Nat.mod_eq_of_lt (show bv < Field.modulus from bc.1)]
  | sub a b leftSupported rightSupported ia ib =>
    cases ea : a.eval ctx values with
    | error message => simp [Expr.eval, ea, implementation.modulus, Field.modulus, bind, Except.bind, Except.pure] at success
    | ok av =>
      cases eb : b.eval ctx values with
      | error message => simp [Expr.eval, ea, eb, implementation.modulus, Field.modulus, bind, Except.bind, Except.pure] at success
      | ok bv =>
        obtain ⟨an, na, ac, ar, am⟩ := ia aliases values agreement av ea
        obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement bv eb
        simp [Expr.eval, ea, eb, implementation.modulus, Field.modulus, bind, Except.bind, Except.pure] at success
        cases success
        refine ⟨_, by simp only [normalize, na, nb]; rfl, ?_⟩
        simp only [subtraction_eq, requireSourceType_eq]
        refine ⟨native_canonical _ (Nat.mod_lt _ (show 0 < Field.modulus by decide)),
          requirements_join _ _ _ _ _ ar br, ?_⟩
        simp [interpret_add, interpret_neg, am, bm, sourceScalar?, sourceNumber?]
        change scalar ((av % Field.modulus) + (scalar (Field.modulus - bv % Field.modulus)).val) =
          scalar ((Field.modulus + av - bv) % Field.modulus)
        rw [Nat.mod_eq_of_lt (show av < Field.modulus from ac.1),
          Nat.mod_eq_of_lt (show bv < Field.modulus from bc.1)]
        exact subtraction_mod av bv bc.1
  | @uadd m n a b leftSupported rightSupported ia ib =>
    cases ea : a.eval ctx values with
    | error message => simp [Expr.eval, ea, bind, Except.bind] at success
    | ok av =>
      cases eb : b.eval ctx values with
      | error message => simp [Expr.eval, ea, eb, bind, Except.bind] at success
      | ok bv =>
        obtain ⟨an, na, ac, ar, am⟩ := ia aliases values agreement av ea
        obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement bv eb
        simp only [Expr.eval, ea, eb, bind, Except.bind] at success
        change (if m + n ≤ ScalarPolicy.maxUint && av + bv ≤ m + n && av + bv < ctx.modulus
          then Except.ok (av + bv) else Except.error "scalar conversion exceeds unsigned bound") = Except.ok value at success
        split at success
        next valid =>
          cases success
          simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
          have canonical : Canonical (.uint (m + n)) (av + bv) :=
            ⟨by simpa [implementation.modulus, Canonical, sourceNumber?] using valid.2,
              valid.1.1, valid.1.2⟩
          refine ⟨_, by simp only [normalize, na, nb]; rfl, ?_⟩
          simp only [arithmetic_eq, requireSourceType_eq]
          apply represent_with_bound _ _ _ _ _ _ _ canonical (requirements_join _ _ _ _ _ ar br)
          simp [interpret_add, am, bm, sourceScalar?, sourceNumber?]
          change scalar ((av % Field.modulus) + (bv % Field.modulus)) = scalar (av + bv)
          rw [Nat.mod_eq_of_lt (show av < Field.modulus from ac.1),
            Nat.mod_eq_of_lt (show bv < Field.modulus from bc.1)]
        next invalid => cases success
  | @usub m n a b leftSupported rightSupported ia ib =>
    cases ea : a.eval ctx values with
    | error message => simp [Expr.eval, ea, bind, Except.bind] at success
    | ok av =>
      cases eb : b.eval ctx values with
      | error message => simp [Expr.eval, ea, eb, bind, Except.bind] at success
      | ok bv =>
        obtain ⟨an, na, ac, ar, am⟩ := ia aliases values agreement av ea
        obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement bv eb
        simp only [Expr.eval, ea, eb, bind, Except.bind] at success
        by_cases underflow : av < bv
        · simp [underflow] at success
        · simp only [underflow, ↓reduceIte] at success
          change (if m ≤ ScalarPolicy.maxUint && av - bv ≤ m && av - bv < ctx.modulus
            then Except.ok (av - bv) else Except.error "scalar conversion exceeds unsigned bound") = Except.ok value at success
          split at success
          next valid =>
            cases success
            simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
            have canonical : Canonical (.uint m) (av - bv) :=
              ⟨by simpa [implementation.modulus, Canonical, sourceNumber?] using valid.2,
                valid.1.1, valid.1.2⟩
            refine ⟨_, by simp only [normalize, na, nb]; rfl, ?_⟩
            simp only [subtraction_eq, requireSourceType_eq]
            apply represent_with_bound _ _ _ _ _ _ _ canonical (requirements_join _ _ _ _ _ ar br)
            simp [interpret_add, interpret_neg, am, bm, sourceScalar?, sourceNumber?]
            change scalar ((av % Field.modulus) + (scalar (Field.modulus - bv % Field.modulus)).val) = scalar (av - bv)
            rw [Nat.mod_eq_of_lt (show av < Field.modulus from ac.1),
              Nat.mod_eq_of_lt (show bv < Field.modulus from bc.1), subtraction_mod av bv bc.1]
            have equality : Field.modulus + av - bv = Field.modulus + (av - bv) := Nat.add_sub_assoc (Nat.le_of_not_gt underflow) _
            rw [equality, Nat.add_mod]
            simp only [Nat.mod_self, Nat.zero_add, Nat.mod_mod]
            rw [Nat.mod_eq_of_lt (show av - bv < Field.modulus from canonical.1)]
          next invalid => cases success
  | @umul m n a b leftSupported rightSupported ia ib =>
    cases ea : a.eval ctx values with
    | error message => simp [Expr.eval, ea, bind, Except.bind] at success
    | ok av =>
      cases eb : b.eval ctx values with
      | error message => simp [Expr.eval, ea, eb, bind, Except.bind] at success
      | ok bv =>
        obtain ⟨an, na, ac, ar, am⟩ := ia aliases values agreement av ea
        obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement bv eb
        simp only [Expr.eval, ea, eb, bind, Except.bind] at success
        change (if m * n ≤ ScalarPolicy.maxUint && av * bv ≤ m * n && av * bv < ctx.modulus
          then Except.ok (av * bv) else Except.error "scalar conversion exceeds unsigned bound") = Except.ok value at success
        split at success
        next valid =>
          cases success
          simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
          have canonical : Canonical (.uint (m * n)) (av * bv) :=
            ⟨by simpa [implementation.modulus, Canonical, sourceNumber?] using valid.2,
              valid.1.1, valid.1.2⟩
          refine ⟨_, by simp only [normalize, na, nb]; rfl, ?_⟩
          simp only [arithmetic_eq, requireSourceType_eq]
          apply represent_with_bound _ _ _ _ _ _ _ canonical (requirements_join _ _ _ _ _ ar br)
          simp [interpret_mul, am, bm, sourceScalar?, sourceNumber?]
          change scalar ((av % Field.modulus) * (bv % Field.modulus)) = scalar (av * bv)
          rw [Nat.mod_eq_of_lt (show av < Field.modulus from ac.1),
            Nat.mod_eq_of_lt (show bv < Field.modulus from bc.1)]
        next invalid => cases success
  | @cast source target expression sourceScalar targetScalar valueSupported ih =>
    cases ev : expression.eval ctx values with
    | error message =>
      have guardFalse : (target.isBytes || source.isBytes || target.isJubjub ||
          source.isJubjub || target.isForeign || source.isForeign) = false := by
        cases sourceScalar <;> cases targetScalar <;>
          simp [Ty.isBytes, Ty.isJubjub, Ty.isForeign]
      simp only [Expr.eval] at success
      rw [guardFalse] at success
      simp [ev, bind, Except.bind] at success
    | ok result =>
      obtain ⟨vn, nv, vc, vr, vm⟩ := ih aliases values agreement result ev
      have castEval := eval_cast_scalar ctx values expression sourceScalar targetScalar result ev
      rw [castEval] at success
      cases targetScalar with
      | native =>
        simp only [scalarCast] at success
        change (if number sourceScalar result < ctx.modulus then Except.ok (number sourceScalar result)
          else Except.error "noncanonical scalar conversion") = Except.ok value at success
        split at success
        next bound =>
          cases success
          have canonical : Canonical .native (number sourceScalar result) :=
            native_canonical _ (by simpa [implementation.modulus] using bound)
          refine ⟨_, by simp only [normalize, nv]; rfl, canonical, vr, ?_⟩
          rw [sourceScalar_number sourceScalar result] at vm
          simpa [sourceScalar?, sourceNumber?] using vm
        next invalid => cases success
      | bool =>
        simp only [scalarCast] at success
        change Except.ok (number sourceScalar result != 0) = Except.ok value at success
        cases success
        refine ⟨_, by simp only [normalize, nv]; rfl, ?_⟩
        simp only [requireSourceType_eq]
        let term : Term := .unary "not" (.binary "test_eq" vn.term (.constant 0))
        have vm' : interpret hash inputs vn.term = some (scalar (number sourceScalar result)) := by
          rw [sourceScalar_number sourceScalar result] at vm
          exact vm
        have meaning : interpret hash inputs term = some (bit (number sourceScalar result != 0)) := by
          simp [term, interpret_not, interpret_testEq, vm', scalar_zero,
            scalar_eq_zero _ (scalar_number_canonical sourceScalar result vc), bit]
          by_cases isZero : number sourceScalar result = 0
          · simp [isZero, zero_ne_one]
          · simp [isZero, zero_ne_one]
        refine ⟨bool_canonical _, ?_, ?_⟩
        · simpa [term] using requirements_join _ _ vn {term := term, bounds := [(term, 1)]} term vr
            (bool_requirements _ _ term (number sourceScalar result != 0) meaning)
        · exact meaning.trans (bit_sourceScalar (number sourceScalar result != 0))
      | uint maximum =>
        simp only [scalarCast] at success
        change (if maximum ≤ ScalarPolicy.maxUint && number sourceScalar result ≤ maximum && number sourceScalar result < ctx.modulus
          then Except.ok (number sourceScalar result) else Except.error "scalar conversion exceeds unsigned bound") = Except.ok value at success
        split at success
        next valid =>
          cases success
          simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
          have canonical : Canonical (.uint maximum) (number sourceScalar result) :=
            ⟨by simpa [implementation.modulus, Canonical, sourceNumber?] using valid.2,
              valid.1.1, valid.1.2⟩
          refine ⟨_, by simp only [normalize, nv]; rfl, ?_⟩
          simp only [requireSourceType_eq]
          have vm' : interpret hash inputs vn.term = some (scalar (number sourceScalar result)) := by
            rw [sourceScalar_number sourceScalar result] at vm
            exact vm
          have targetMeaning : interpret hash inputs vn.term = sourceScalar? (.uint maximum)
              (number sourceScalar result) := by
            simpa [sourceScalar?, sourceNumber?] using vm'
          exact represent_with_bound _ _ _ _ _ _ _ canonical vr targetMeaning
        next invalid => cases success
  | @letE source ty name expression body sourceScalar valueSupported bodySupported iv ib =>
    cases ev : expression.eval ctx values with
    | error message => simp [Expr.eval, ev, bind, Except.bind] at success
    | ok result =>
      obtain ⟨vn, nv, vc, vr, vm⟩ := iv aliases values agreement result ev
      have bodySuccess : body.eval ctx ((name, Value.pack source result) :: values) = .ok value := by
        simpa only [Expr.eval, ev, bind, Except.bind] using success
      obtain ⟨bn, nb, bc, br, bm⟩ := ib ((name, vn.term) :: aliases) ((name, Value.pack source result) :: values)
        (aliasAgreement_cons _ _ _ _ _ _ _ _ agreement vc vm) value bodySuccess
      refine ⟨{term := bn.term, bounds := vn.bounds ++ bn.bounds, assertions := vn.assertions ++ bn.assertions}, by simp only [normalize, nv, bind, Except.bind, nb]; rfl, bc, ?_, bm⟩
      exact requirements_join _ _ vn bn bn.term vr br
  | assertE condition body conditionSupported bodySupported ic ib =>
    cases ec : condition.eval ctx values with
    | error message => simp [Expr.eval, ec, bind, Except.bind] at success
    | ok result =>
      cases result with
      | false => simp [Expr.eval, ec, bind, Except.bind] at success
      | true =>
        obtain ⟨cn, nc, cc, cr, cm⟩ := ic aliases values agreement true ec
        have bodySuccess : body.eval ctx values = .ok value := by
          simpa only [Expr.eval, ec, bind, Except.bind, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, Except.pure] using success
        obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement value bodySuccess
        refine ⟨{term := bn.term, bounds := cn.bounds ++ bn.bounds, assertions := cn.assertions ++ [cn.term] ++ bn.assertions}, by simp only [normalize, nc, nb]; rfl, bc, ?_, bm⟩
        constructor
        · intro requirement member
          rcases List.mem_append.mp member with member | member
          · exact cr.1 requirement member
          · exact br.1 requirement member
        · intro term member
          rcases List.mem_append.mp member with member | member
          · rcases List.mem_append.mp member with member | member
            · exact cr.2 term member
            · have same := List.mem_singleton.mp member
              subst term
              simpa [sourceScalar?, sourceNumber?, scalar_one, bit] using cm
          · exact br.2 term member
  | copyValue expression supported ih =>
    simp only [Expr.eval] at success
    simp only [normalize] at ⊢
    exact ih aliases values agreement value success
  | disclose span expression supported ih =>
    simp only [Expr.eval] at success
    simp only [normalize] at ⊢
    exact ih aliases values agreement value success
  | @eq ty a b scalarType leftSupported rightSupported ia ib =>
    cases ea : a.eval ctx values with
    | error message => simp [Expr.eval, ea, bind, Except.bind] at success
    | ok av =>
      cases eb : b.eval ctx values with
      | error message => simp [Expr.eval, ea, eb, bind, Except.bind] at success
      | ok bv =>
        obtain ⟨an, na, ac, ar, am⟩ := ia aliases values agreement av ea
        obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement bv eb
        simp only [Expr.eval, ea, eb, bind, Except.bind] at success
        have same : value = (number scalarType av == number scalarType bv) := by
          cases scalarType with
          | native =>
            cases success
            rfl
          | bool =>
            cases av <;> cases bv <;> cases success <;> rfl
          | uint maximum =>
            cases success
            rfl
        subst value
        refine ⟨_, by simp only [normalize, na, nb]; rfl, ?_⟩
        simp only [arithmetic_eq, requireSourceType_eq]
        apply represent_with_bound _ _ _ _ _ _ _ (bool_canonical _) (requirements_join _ _ _ _ _ ar br)
        have am' : interpret hash inputs an.term = some (scalar (number scalarType av)) := by
          rw [sourceScalar_number scalarType av] at am
          exact am
        have bm' : interpret hash inputs bn.term = some (scalar (number scalarType bv)) := by
          rw [sourceScalar_number scalarType bv] at bm
          exact bm
        have numberBoundLeft := scalar_number_canonical scalarType av ac
        have numberBoundRight := scalar_number_canonical scalarType bv bc
        have compare : decide (scalar (number scalarType av) = scalar (number scalarType bv)) =
            (number scalarType av == number scalarType bv) := by
          have raw : scalar (number scalarType av) = scalar (number scalarType bv) ↔
              number scalarType av = number scalarType bv :=
            scalar_numbers_equal _ _ numberBoundLeft numberBoundRight
          by_cases equal : number scalarType av = number scalarType bv
          · have scalarEqual := raw.mpr equal
            simp [equal, scalarEqual]
          · have scalarDifferent : scalar (number scalarType av) ≠ scalar (number scalarType bv) :=
              fun scalarEqual => equal (raw.mp scalarEqual)
            have nativeDifferent : (number scalarType av == number scalarType bv) = false := by
              cases beq : (number scalarType av == number scalarType bv) with
              | false => rfl
              | true => exact (equal (eq_of_beq beq)).elim
            simp [scalarDifferent, nativeDifferent]
        have outputMeaning : interpret hash inputs (.binary "test_eq" an.term bn.term) =
            some (bit (number scalarType av == number scalarType bv)) := by
          simp [interpret_testEq, am', bm', compare]
        exact outputMeaning.trans (bit_sourceScalar (number scalarType av == number scalarType bv))
  | @select ty c a b scalarType conditionSupported yesSupported noSupported ic ia ib =>
    cases ec : c.eval ctx values with
    | error message => simp [Expr.eval, ec, bind, Except.bind] at success
    | ok cv =>
      cases ea : a.eval ctx values with
      | error message => simp [Expr.eval, ec, ea, bind, Except.bind] at success
      | ok av =>
        cases eb : b.eval ctx values with
        | error message => simp [Expr.eval, ec, ea, eb, bind, Except.bind] at success
        | ok bv =>
          obtain ⟨cn, nc, cc, cr, cm⟩ := ic aliases values agreement cv ec
          obtain ⟨an, na, ac, ar, am⟩ := ia aliases values agreement av ea
          obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement bv eb
          have sourceResult : value = if cv then av else bv := by
            simpa [Expr.eval, ec, ea, eb, bind, Except.bind, pure, Except.pure] using success.symm
          subst value
          refine ⟨_, by simp only [normalize, nc, na, nb]; rfl, ?_⟩
          simp only [requireSourceType_eq]
          change Represents hash inputs ty {term := .select cn.term an.term bn.term, bounds := typeBounds ty (.select cn.term an.term bn.term) (cn.bounds ++ an.bounds ++ bn.bounds), assertions := cn.assertions ++ an.assertions ++ bn.assertions} (if cv then av else bv)
          apply represent_with_bound hash inputs ty (.select cn.term an.term bn.term)
            (cn.bounds ++ an.bounds ++ bn.bounds) (cn.assertions ++ an.assertions ++ bn.assertions) (if cv then av else bv)
          · cases cv
            · exact bc
            · exact ac
          · exact requirements_join _ _
              {term := an.term, bounds := cn.bounds ++ an.bounds, assertions := cn.assertions ++ an.assertions}
              bn _ (requirements_join _ _ cn an _ cr ar) br
          · have conditionMeaning : interpret hash inputs cn.term = some (bit cv) := by
              rw [← bit_sourceScalar cv] at cm
              exact cm
            cases cv <;> simp [interpret_select, conditionMeaning, am, bm, bit, zero_ne_one]
  | poseidon2 domain a b leftSupported rightSupported ia ib =>
    simp only [Expr.eval] at success
    split at success
    next invalid => cases success
    next valid =>
      have domainBound : domain < Field.modulus := by
        have : domain < ctx.modulus := Nat.lt_of_not_ge valid
        simpa [implementation.modulus] using this
      cases ea : a.eval ctx values with
      | error message => simp [ea, bind, Except.bind] at success
      | ok av =>
        cases eb : b.eval ctx values with
        | error message => simp [ea, eb, bind, Except.bind] at success
        | ok bv =>
          obtain ⟨an, na, ac, ar, am⟩ := ia aliases values agreement av ea
          obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement bv eb
          have oracle : ctx.poseidon2 domain av bv = .ok (hash [scalar domain, scalar av, scalar bv]).val := by
            simpa only [scalar, Nat.mod_eq_of_lt domainBound,
              Nat.mod_eq_of_lt (show av < Field.modulus from ac.1),
              Nat.mod_eq_of_lt (show bv < Field.modulus from bc.1)] using
              implementation.calls (scalar domain) (scalar av) (scalar bv)
          have resultBound : (hash [scalar domain, scalar av, scalar bv]).val < ctx.modulus := by
            simpa [implementation.modulus] using (hash [scalar domain, scalar av, scalar bv]).isLt
          simp [ea, eb, oracle, bind, Except.bind, pure, Except.pure,
            Nat.not_le_of_gt resultBound] at success
          cases success
          refine ⟨_, by simp only [normalize, na, nb]; rfl, ⟨(hash _).isLt, trivial⟩,
            requirements_join _ _ _ _ _ ar br, ?_⟩
          have am' : interpret hash inputs an.term = some (scalar av) := by
            simpa [sourceScalar?, sourceNumber?] using am
          have bm' : interpret hash inputs bn.term = some (scalar bv) := by
            simpa [sourceScalar?, sourceNumber?] using bm
          let hashValue : Scalar := hash [scalar domain, scalar av, scalar bv]
          have termMeaning : interpret hash inputs
              (.hash [.constant domain, an.term, bn.term]) = some hashValue := by
            simp [interpret_hash, interpret_constant, am', bm']
            dsimp [hashValue]
          have valueMeaning : sourceScalar? .native
              (hash [scalar domain, scalar av, scalar bv]).val =
                some (hash [scalar domain, scalar av, scalar bv]) := by
            rw [sourceScalar_number ScalarType.native]
            congr 1
            apply Fin.ext
            exact Nat.mod_eq_of_lt (hash [scalar domain, scalar av, scalar bv]).isLt
          exact termMeaning.trans valueMeaning.symm

end Noctium.Verification.ScalarNormalization
