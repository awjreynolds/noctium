import Noctium.Verification.GenericStateAdmissionPrefix

namespace Noctium.Verification.GenericStateEffectValidation
open Backend

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem curve_beq_true (left right : Foreign.Curve)
    (same : (left == right) = true) : left = right := by
  cases left <;> cases right <;>
    simp_all [BEq.beq, Foreign.instBEqCurve.beq, Foreign.Curve.ctorIdx]

private theorem curve_beq_self (curve : Foreign.Curve) : (curve == curve) = true := by
  cases curve <;> rfl

private theorem foreignKind_beq_true (left right : Foreign.Kind)
    (same : (left == right) = true) : left = right := by
  cases left with
  | base leftCurve =>
      cases right with
      | base rightCurve =>
          change (leftCurve == rightCurve) = true at same
          exact congrArg Foreign.Kind.base (curve_beq_true leftCurve rightCurve same)
      | _ => simp [BEq.beq, Foreign.instBEqKind.beq] at same
  | scalar leftCurve =>
      cases right with
      | scalar rightCurve =>
          change (leftCurve == rightCurve) = true at same
          exact congrArg Foreign.Kind.scalar (curve_beq_true leftCurve rightCurve same)
      | _ => simp [BEq.beq, Foreign.instBEqKind.beq] at same
  | point leftCurve =>
      cases right with
      | point rightCurve =>
          change (leftCurve == rightCurve) = true at same
          exact congrArg Foreign.Kind.point (curve_beq_true leftCurve rightCurve same)
      | _ => simp [BEq.beq, Foreign.instBEqKind.beq] at same

private theorem foreignKind_beq_self (kind : Foreign.Kind) : (kind == kind) = true := by
  cases kind with
  | base curve => cases curve <;> rfl
  | scalar curve => cases curve <;> rfl
  | point curve => cases curve <;> rfl

private theorem type_beq_true (left right : Ty) (same : (left == right) = true) :
    left = right := by
  cases left <;> cases right <;> try
    simp_all [BEq.beq, instBEqTy.beq]
  case foreign.foreign leftKind rightKind =>
    change (leftKind == rightKind) = true at same
    exact foreignKind_beq_true leftKind rightKind same

private theorem type_beq_self (ty : Ty) : (ty == ty) = true := by
  cases ty with
  | foreign kind => exact foreignKind_beq_self kind
  | _ => simp [BEq.beq, instBEqTy.beq]

private theorem kind_cell_beq_true (kind : StateKind) (ty : Ty)
    (same : (kind == .cell ty) = true) : kind = .cell ty := by
  cases kind with
  | cell found =>
    have equal : (found == ty) = true := by
      simpa only [BEq.beq, instBEqStateKind.beq] using same
    exact congrArg StateKind.cell (type_beq_true found ty equal)
  | _ => simp [BEq.beq, instBEqStateKind.beq] at same

private theorem kind_map_beq_true (kind : StateKind) (keyTy valueTy : Ty)
    (same : (kind == .map keyTy valueTy) = true) :
    kind = .map keyTy valueTy := by
  cases kind with
  | cell found => simp [BEq.beq, instBEqStateKind.beq] at same
  | map foundKey foundValue =>
    have both : (foundKey == keyTy) = true ∧ (foundValue == valueTy) = true := by
      simpa only [BEq.beq, instBEqStateKind.beq, Bool.and_eq_true] using same
    have equalKey : (foundKey == keyTy) = true := by
      exact both.1
    have equalValue : (foundValue == valueTy) = true := by
      exact both.2
    cases type_beq_true foundKey keyTy equalKey
    cases type_beq_true foundValue valueTy equalValue
    rfl
  | _ => simp [BEq.beq, instBEqStateKind.beq] at same

def stateEffectCaps : Capabilities :=
  {poseidon2 := true, persistentHash32 := true, persistentHashVector32 := true,
    persistentHashNative := true, bytes32Conversions := true, sha512 := true,
    keccak256 := true, typedBoolean := true, hashToCurve := true,
    foreignValues := true, foreignArithmetic := true,
    foreignByteConversions := true, jubjub := true,
    stateCells := true, stateMaps := true}

def HasDeclaration (state : List StateDecl) (name : String)
    (kind : StateKind) : Prop :=
  ∃ declaration,
    state.find? (fun item => item.name == name) = some declaration ∧
      declaration.kind = kind

inductive ScalarStateEffect : Effect → Prop where
  | readCell (state destination : String) (ty : Ty) :
      ScalarStateEffect (.readCell state destination ty)
  | readMap (state destination : String) (keyTy valueTy : Ty)
      (key : Expr keyTy) :
      ScalarStateEffect (.readMap state destination keyTy valueTy key)
  | require (condition : Expr .bool) : ScalarStateEffect (.require condition)
  | writeCell (state : String) (ty : Ty) (value : Expr ty) :
      ScalarStateEffect (.writeCell state ty value)
  | writeMap (state : String) (keyTy valueTy : Ty)
      (key : Expr keyTy) (value : Expr valueTy) :
      ScalarStateEffect (.writeMap state keyTy valueTy key value)
  | requireAbsent (state : String) (keyTy : Ty) (key : Expr keyTy) :
      ScalarStateEffect (.requireAbsent state keyTy key)

inductive ScalarStateEffects : List Effect → Prop where
  | nil : ScalarStateEffects []
  | cons {effect : Effect} {rest : List Effect}
      (head : ScalarStateEffect effect) (tail : ScalarStateEffects rest) :
      ScalarStateEffects (effect :: rest)

inductive EffectValidation (state : List StateDecl) :
    TypeEnv → Effect → TypeEnv → Prop where
  | readCell {env : TypeEnv} {stateName destination : String} {ty : Ty}
      (declared : HasDeclaration state stateName (.cell ty))
      (fresh : env.lookup destination = none) :
      EffectValidation state env (.readCell stateName destination ty)
        (env ++ [(destination, ty)])
  | readMap {env : TypeEnv} {stateName destination : String}
      {keyTy valueTy : Ty} {key : Expr keyTy}
      (declared : HasDeclaration state stateName (.map keyTy valueTy))
      (keyValid : key.validate stateEffectCaps env = .ok ())
      (fresh : env.lookup destination = none) :
      EffectValidation state env
        (.readMap stateName destination keyTy valueTy key)
        (env ++ [(destination, valueTy)])
  | require {env : TypeEnv} {condition : Expr .bool}
      (conditionValid : condition.validate stateEffectCaps env = .ok ()) :
      EffectValidation state env (.require condition) env
  | writeCell {env : TypeEnv} {stateName : String} {ty : Ty}
      {value : Expr ty} (declared : HasDeclaration state stateName (.cell ty))
      (valueValid : value.validate stateEffectCaps env = .ok ()) :
      EffectValidation state env (.writeCell stateName ty value) env
  | writeMap {env : TypeEnv} {stateName : String} {keyTy valueTy : Ty}
      {key : Expr keyTy} {value : Expr valueTy}
      (declared : HasDeclaration state stateName (.map keyTy valueTy))
      (keyValid : key.validate stateEffectCaps env = .ok ())
      (valueValid : value.validate stateEffectCaps env = .ok ()) :
      EffectValidation state env (.writeMap stateName keyTy valueTy key value) env
  | requireAbsent {env : TypeEnv} {stateName : String} {keyTy : Ty}
      {key : Expr keyTy} {valueTy : Ty}
      (declared : HasDeclaration state stateName (.map keyTy valueTy))
      (keyValid : key.validate stateEffectCaps env = .ok ()) :
      EffectValidation state env (.requireAbsent stateName keyTy key) env

inductive EffectBindingValidation (state : List StateDecl) :
    TypeEnv → Effect → List (String × Ty) → Prop where
  | readCell {env : TypeEnv} {stateName destination : String} {ty : Ty}
      (declared : HasDeclaration state stateName (.cell ty)) :
      EffectBindingValidation state env (.readCell stateName destination ty)
        [(destination, ty)]
  | readMap {env : TypeEnv} {stateName destination : String}
      {keyTy valueTy : Ty} {key : Expr keyTy}
      (declared : HasDeclaration state stateName (.map keyTy valueTy))
      (keyValid : key.validate stateEffectCaps env = .ok ()) :
      EffectBindingValidation state env
        (.readMap stateName destination keyTy valueTy key) [(destination, valueTy)]
  | require {env : TypeEnv} {condition : Expr .bool}
      (conditionValid : condition.validate stateEffectCaps env = .ok ()) :
      EffectBindingValidation state env (.require condition) []
  | writeCell {env : TypeEnv} {stateName : String} {ty : Ty}
      {value : Expr ty} (declared : HasDeclaration state stateName (.cell ty))
      (valueValid : value.validate stateEffectCaps env = .ok ()) :
      EffectBindingValidation state env (.writeCell stateName ty value) []
  | writeMap {env : TypeEnv} {stateName : String} {keyTy valueTy : Ty}
      {key : Expr keyTy} {value : Expr valueTy}
      (declared : HasDeclaration state stateName (.map keyTy valueTy))
      (keyValid : key.validate stateEffectCaps env = .ok ())
      (valueValid : value.validate stateEffectCaps env = .ok ()) :
      EffectBindingValidation state env (.writeMap stateName keyTy valueTy key value) []
  | requireAbsent {env : TypeEnv} {stateName : String} {keyTy valueTy : Ty}
      {key : Expr keyTy} (declared : HasDeclaration state stateName (.map keyTy valueTy))
      (keyValid : key.validate stateEffectCaps env = .ok ()) :
      EffectBindingValidation state env (.requireAbsent stateName keyTy key) []

inductive ValidatedEffects (state : List StateDecl) :
    TypeEnv → List Effect → TypeEnv → Prop where
  | nil {env : TypeEnv} : ValidatedEffects state env [] env
  | readCell {env final : TypeEnv} {rest : List Effect}
      {stateName destination : String} {ty : Ty}
      (declared : HasDeclaration state stateName (.cell ty))
      (fresh : env.lookup destination = none)
      (tail : ValidatedEffects state (env ++ [(destination, ty)]) rest final) :
      ValidatedEffects state env (.readCell stateName destination ty :: rest) final
  | readMap {env final : TypeEnv} {rest : List Effect}
      {stateName destination : String} {keyTy valueTy : Ty}
      {key : Expr keyTy}
      (declared : HasDeclaration state stateName (.map keyTy valueTy))
      (keyValid : key.validate stateEffectCaps env = .ok ())
      (fresh : env.lookup destination = none)
      (tail : ValidatedEffects state (env ++ [(destination, valueTy)]) rest final) :
      ValidatedEffects state env
        (.readMap stateName destination keyTy valueTy key :: rest) final
  | require {env final : TypeEnv} {rest : List Effect}
      {condition : Expr .bool}
      (conditionValid : condition.validate stateEffectCaps env = .ok ())
      (tail : ValidatedEffects state env rest final) :
      ValidatedEffects state env (.require condition :: rest) final
  | writeCell {env final : TypeEnv} {rest : List Effect}
      {stateName : String} {ty : Ty} {value : Expr ty}
      (declared : HasDeclaration state stateName (.cell ty))
      (valueValid : value.validate stateEffectCaps env = .ok ())
      (tail : ValidatedEffects state env rest final) :
      ValidatedEffects state env (.writeCell stateName ty value :: rest) final
  | writeMap {env final : TypeEnv} {rest : List Effect}
      {stateName : String} {keyTy valueTy : Ty}
      {key : Expr keyTy} {value : Expr valueTy}
      (declared : HasDeclaration state stateName (.map keyTy valueTy))
      (keyValid : key.validate stateEffectCaps env = .ok ())
      (valueValid : value.validate stateEffectCaps env = .ok ())
      (tail : ValidatedEffects state env rest final) :
      ValidatedEffects state env (.writeMap stateName keyTy valueTy key value :: rest) final
  | requireAbsent {env final : TypeEnv} {rest : List Effect}
      {stateName : String} {keyTy valueTy : Ty} {key : Expr keyTy}
      (declared : HasDeclaration state stateName (.map keyTy valueTy))
      (keyValid : key.validate stateEffectCaps env = .ok ())
      (tail : ValidatedEffects state env rest final) :
      ValidatedEffects state env (.requireAbsent stateName keyTy key :: rest) final

inductive GuardValidatedEffects (state : List StateDecl) (entry : Entrypoint) :
    TypeEnv → List (Effect × Nat) → TypeEnv → Prop where
  | nil {types : TypeEnv} : GuardValidatedEffects state entry types [] types
  | cons {types next final : TypeEnv} {item : Effect × Nat}
      {rest : List (Effect × Nat)}
      (effect : EffectValidation state types item.1 next)
      (guard : ∀ condition, entry.effectGuardAt item.2 = some condition →
        condition.validate stateEffectCaps types = .ok ())
      (tail : GuardValidatedEffects state entry next rest final) :
      GuardValidatedEffects state entry types (item :: rest) final

theorem ValidatedEffects.uncons {state : List StateDecl} {types final : TypeEnv}
    {effect : Effect} {rest : List Effect}
    (chain : ValidatedEffects state types (effect :: rest) final) :
    ∃ nextTypes, EffectValidation state types effect nextTypes ∧
      ValidatedEffects state nextTypes rest final := by
  cases chain with
  | readCell declared fresh tail =>
    exact ⟨_, .readCell declared fresh, tail⟩
  | readMap declared keyValid fresh tail =>
    exact ⟨_, .readMap declared keyValid fresh, tail⟩
  | require conditionValid tail => exact ⟨_, .require conditionValid, tail⟩
  | writeCell declared valueValid tail =>
    exact ⟨_, .writeCell declared valueValid, tail⟩
  | writeMap declared keyValid valueValid tail =>
    exact ⟨_, .writeMap declared keyValid valueValid, tail⟩
  | requireAbsent declared keyValid tail =>
    exact ⟨_, .requireAbsent declared keyValid, tail⟩

theorem ValidatedEffects.final_unique {state : List StateDecl} {initial : TypeEnv}
    {effects : List Effect} {leftFinal rightFinal : TypeEnv}
    (left : ValidatedEffects state initial effects leftFinal)
    (right : ValidatedEffects state initial effects rightFinal) :
    leftFinal = rightFinal := by
  induction left with
  | nil => cases right; rfl
  | @readCell env final rest stateName destination ty declared fresh tail ih =>
      cases right with
      | readCell _ _ otherTail => exact ih otherTail
  | @readMap env final rest stateName destination keyTy valueTy key
      declared keyValid fresh tail ih =>
      cases right with
      | readMap _ _ _ otherTail => exact ih otherTail
  | @require env final rest condition conditionValid tail ih =>
      cases right with
      | require _ otherTail => exact ih otherTail
  | @writeCell env final rest stateName ty value declared valueValid tail ih =>
      cases right with
      | writeCell _ _ otherTail => exact ih otherTail
  | @writeMap env final rest stateName keyTy valueTy key value
      declared keyValid valueValid tail ih =>
      cases right with
      | writeMap _ _ _ otherTail => exact ih otherTail
  | @requireAbsent env final rest stateName keyTy valueTy key
      declared keyValid tail ih =>
      cases right with
      | requireAbsent _ _ otherTail => exact ih otherTail

theorem GuardValidatedEffects.effects {state : List StateDecl} {entry : Entrypoint}
    {types final : TypeEnv} {items : List (Effect × Nat)}
    (chain : GuardValidatedEffects state entry types items final) :
    ValidatedEffects state types (items.map Prod.fst) final := by
  induction chain with
  | nil => exact .nil
  | @cons types next final item rest effectValid _ tail ih =>
    cases item with
    | mk stateEffect index =>
      cases effectValid with
      | readCell declared fresh => exact .readCell declared fresh ih
      | readMap declared keyValid fresh => exact .readMap declared keyValid fresh ih
      | require conditionValid => exact .require conditionValid ih
      | writeCell declared valueValid => exact .writeCell declared valueValid ih
      | writeMap declared keyValid valueValid => exact .writeMap declared keyValid valueValid ih
      | requireAbsent declared keyValid => exact .requireAbsent declared keyValid ih

private theorem forIn_append_shape
    (body : α → TypeEnv → Except ε (ForInStep TypeEnv))
    (binding : α → String × Ty) (values : List α)
    (before after : TypeEnv)
    (actions : ∀ value env step, body value env = .ok step →
      step = .yield (env ++ [binding value]))
    (success : forIn values before body = .ok after) :
    after = before ++ values.map binding := by
  induction values generalizing before with
  | nil =>
    change Except.ok before = .ok after at success
    cases success
    simp
  | cons value rest ih =>
    rw [List.forIn_cons] at success
    cases checked : body value before with
    | error message => simp [checked, bind, Except.bind] at success
    | ok step =>
      have equal := actions value before step checked
      subst step
      simp only [checked, bind, Except.bind] at success
      simpa [List.append_assoc] using ih _ success

def initialEffectTypeEnv (ep : Entrypoint) : TypeEnv :=
  ep.circuit.inputs.map (fun input => (input.name, input.ty)) ++
    ep.circuit.outputs.map (fun output => (output.name, output.ty))

/-- The source bindings introduced by scalar state effects, in effect order. -/
def effectTypeBindings : Effect → TypeEnv
  | .readCell _ destination ty => [(destination, ty)]
  | .readMap _ destination _ ty _ => [(destination, ty)]
  | _ => []

/-- The validated frame adds the declared read bindings to its initial types. -/
theorem ValidatedEffects.type_environment_shape {state : List StateDecl}
    {initial final : TypeEnv} {effects : List Effect}
    (validated : ValidatedEffects state initial effects final) :
    final = initial ++ effects.flatMap effectTypeBindings := by
  induction validated with
  | nil => simp
  | @readCell env final rest stateName destination ty declared fresh tail ih =>
      rw [ih]
      simp [effectTypeBindings, List.append_assoc]
  | @readMap env final rest stateName destination keyTy valueTy key
      declared keyValid fresh tail ih =>
      rw [ih]
      simp [effectTypeBindings, List.append_assoc]
  | @require env final rest condition conditionValid tail ih =>
      simpa [effectTypeBindings] using ih
  | @writeCell env final rest stateName ty value declared valueValid tail ih =>
      simpa [effectTypeBindings] using ih
  | @writeMap env final rest stateName keyTy valueTy key value
      declared keyValid valueValid tail ih =>
      simpa [effectTypeBindings] using ih
  | @requireAbsent env final rest stateName keyTy valueTy key
      declared keyValid tail ih =>
      simpa [effectTypeBindings] using ih

/-- Destination names introduced by scalar source state reads. -/
def scalarReadDestinations (effects : List Effect) : List String :=
  effects.filterMap fun effect => match effect with
    | .readCell _ destination _ | .readMap _ destination .. => some destination
    | _ => none

private theorem lookup_none_fresh (env : TypeEnv) (name : String)
    (absent : env.lookup name = none) : name ∉ env.map Prod.fst := by
  intro member
  obtain ⟨pair, present, same⟩ := List.mem_map.mp member
  have different := List.lookup_eq_none_iff.mp absent pair present
  simp [same] at different

private theorem ValidatedEffects.scalarReadDestinations_fresh_unique
    {state : List StateDecl} {initial final : TypeEnv} {effects : List Effect}
    (chain : ValidatedEffects state initial effects final) :
    (scalarReadDestinations effects).Nodup ∧
      ∀ name ∈ scalarReadDestinations effects, name ∉ initial.map Prod.fst := by
  induction chain with
  | nil => simp [scalarReadDestinations]
  | @readCell env final rest stateName destination ty declared fresh tail ih =>
      have headNotInRest : destination ∉ scalarReadDestinations rest := by
        intro member
        exact ih.2 destination member (by simp)
      constructor
      · change (destination :: scalarReadDestinations rest).Nodup
        exact List.nodup_cons.mpr ⟨headNotInRest, ih.1⟩
      · intro name member
        change name ∈ destination :: scalarReadDestinations rest at member
        rcases List.mem_cons.mp member with same | restMember
        · cases same
          exact lookup_none_fresh _ _ fresh
        · intro present
          exact ih.2 name restMember (by simp [present])
  | @readMap env final rest stateName destination keyTy valueTy key
      declared keyValid fresh tail ih =>
      have headNotInRest : destination ∉ scalarReadDestinations rest := by
        intro member
        exact ih.2 destination member (by simp)
      constructor
      · change (destination :: scalarReadDestinations rest).Nodup
        exact List.nodup_cons.mpr ⟨headNotInRest, ih.1⟩
      · intro name member
        change name ∈ destination :: scalarReadDestinations rest at member
        rcases List.mem_cons.mp member with same | restMember
        · cases same
          exact lookup_none_fresh _ _ fresh
        · intro present
          exact ih.2 name restMember (by simp [present])
  | @require env final rest condition conditionValid tail ih =>
      simpa [scalarReadDestinations] using ih
  | @writeCell env final rest stateName ty value declared valueValid tail ih =>
      simpa [scalarReadDestinations] using ih
  | @writeMap env final rest stateName keyTy valueTy key value
      declared keyValid valueValid tail ih =>
      simpa [scalarReadDestinations] using ih
  | @requireAbsent env final rest stateName keyTy valueTy key
      declared keyValid tail ih =>
      simpa [scalarReadDestinations] using ih

private theorem effectBindings_validated (state : List StateDecl)
    (effect : Effect) (env : TypeEnv) (bindings : List (String × Ty))
    (scope : ScalarStateEffect effect)
    (accepted : Entrypoint.validateEffectBindings stateEffectCaps state effect env =
      .ok bindings) :
    bindings = (match effect with
      | .readCell _ destination ty => [(destination, ty)]
      | .readMap _ destination _ valueTy _ => [(destination, valueTy)]
      | _ => []) ∧ EffectBindingValidation state env effect bindings := by
  cases scope with
  | readCell stateName destination ty =>
    change (Entrypoint.requireState state stateName (.cell ty) >>= fun _ =>
      .ok [(destination, ty)]) = .ok bindings at accepted
    rcases bind_ok.mp accepted with ⟨_, declared, result⟩
    have resultEq : bindings = [(destination, ty)] :=
      (Except.ok.inj result).symm
    have declared' : HasDeclaration state stateName (.cell ty) := by
      obtain ⟨declaration, found, kind⟩ :=
        Entrypoint.requireState_succeeded state stateName (.cell ty) declared
      exact ⟨declaration, found, kind_cell_beq_true declaration.kind ty kind⟩
    constructor
    · exact resultEq
    · subst bindings
      exact .readCell declared'
  | readMap stateName destination keyTy valueTy key =>
    change (Entrypoint.requireState state stateName (.map keyTy valueTy) >>= fun _ =>
      key.validate stateEffectCaps env >>= fun _ => .ok [(destination, valueTy)]) =
        .ok bindings at accepted
    rcases bind_ok.mp accepted with ⟨_, declared, rest⟩
    rcases bind_ok.mp rest with ⟨_, keyValid, result⟩
    have resultEq : bindings = [(destination, valueTy)] :=
      (Except.ok.inj result).symm
    have declared' : HasDeclaration state stateName (.map keyTy valueTy) := by
      obtain ⟨declaration, found, kind⟩ :=
        Entrypoint.requireState_succeeded state stateName (.map keyTy valueTy) declared
      exact ⟨declaration, found, kind_map_beq_true declaration.kind keyTy valueTy kind⟩
    constructor
    · exact resultEq
    · subst bindings
      exact .readMap declared' keyValid
  | require condition =>
    change (condition.validate stateEffectCaps env >>= fun _ => .ok []) =
      .ok bindings at accepted
    rcases bind_ok.mp accepted with ⟨_, conditionValid, result⟩
    have resultEq : bindings = [] := (Except.ok.inj result).symm
    constructor
    · exact resultEq
    · subst bindings
      exact .require conditionValid
  | writeCell stateName ty value =>
    change (Entrypoint.requireState state stateName (.cell ty) >>= fun _ =>
      value.validate stateEffectCaps env >>= fun _ => .ok []) =
        .ok bindings at accepted
    rcases bind_ok.mp accepted with ⟨_, declared, rest⟩
    rcases bind_ok.mp rest with ⟨_, valueValid, result⟩
    have resultEq : bindings = [] := (Except.ok.inj result).symm
    have declared' : HasDeclaration state stateName (.cell ty) := by
      obtain ⟨declaration, found, kind⟩ :=
        Entrypoint.requireState_succeeded state stateName (.cell ty) declared
      exact ⟨declaration, found, kind_cell_beq_true declaration.kind ty kind⟩
    constructor
    · exact resultEq
    · subst bindings
      exact .writeCell declared' valueValid
  | writeMap stateName keyTy valueTy key value =>
    change (Entrypoint.requireState state stateName (.map keyTy valueTy) >>= fun _ =>
      key.validate stateEffectCaps env >>= fun _ =>
      value.validate stateEffectCaps env >>= fun _ => .ok []) =
        .ok bindings at accepted
    rcases bind_ok.mp accepted with ⟨_, declared, rest⟩
    rcases bind_ok.mp rest with ⟨_, keyValid, rest⟩
    rcases bind_ok.mp rest with ⟨_, valueValid, result⟩
    have resultEq : bindings = [] := (Except.ok.inj result).symm
    have declared' : HasDeclaration state stateName (.map keyTy valueTy) := by
      obtain ⟨declaration, found, kind⟩ :=
        Entrypoint.requireState_succeeded state stateName (.map keyTy valueTy) declared
      exact ⟨declaration, found, kind_map_beq_true declaration.kind keyTy valueTy kind⟩
    constructor
    · exact resultEq
    · subst bindings
      exact .writeMap declared' keyValid valueValid
  | requireAbsent stateName keyTy key =>
    unfold Entrypoint.validateEffectBindings at accepted
    cases found : state.find? (fun item => item.name == stateName) with
    | none => simp [found, stateEffectCaps, Bind.bind, Except.bind] at accepted
    | some declaration =>
      cases declaration with
      | mk itemName itemKind sealed span alignment =>
        cases itemKind with
        | cell cellTy => simp [found, stateEffectCaps, Bind.bind, Except.bind] at accepted
        | tree schema => simp [found, stateEffectCaps, Bind.bind, Except.bind] at accepted
        | merkleTree depth => simp [found, stateEffectCaps, Bind.bind, Except.bind] at accepted
        | historicMerkleTree depth =>
          simp [found, stateEffectCaps, Bind.bind, Except.bind] at accepted
        | opaqueString => simp [found, stateEffectCaps, Bind.bind, Except.bind] at accepted
        | map foundKey foundValue =>
          by_cases sameKey : foundKey = keyTy
          · have mismatch : (foundKey != keyTy) = false := by
              rw [sameKey]
              simp only [bne]
              rw [type_beq_self keyTy]
              rfl
            have accepted' := accepted
            simp [stateEffectCaps, found, mismatch, Bind.bind, Except.bind] at accepted'
            rcases bind_ok.mp accepted' with ⟨_, keyValid, result⟩
            have resultEq : bindings = [] := (Except.ok.inj result).symm
            have declared : HasDeclaration state stateName (.map keyTy foundValue) := by
              refine ⟨StateDecl.mk itemName (.map foundKey foundValue) sealed span alignment,
                ?_, ?_⟩
              · exact found
              · cases sameKey
                rfl
            constructor
            · exact resultEq
            · subst bindings
              exact .requireAbsent declared keyValid
          · have unequal : (foundKey == keyTy) = false := by
              cases comparison : (foundKey == keyTy) with
              | false => rfl
              | true =>
                have typeEqual := type_beq_true foundKey keyTy comparison
                exact False.elim (sameKey typeEqual)
            have mismatch : (foundKey != keyTy) = true := by simp [bne, unequal]
            simp [found, mismatch, stateEffectCaps, Bind.bind, Except.bind] at accepted

private theorem effectStep_validated (state : List StateDecl) (ep : Entrypoint)
    (effect : Effect) (index : Nat) (env : TypeEnv) (step : ForInStep TypeEnv)
    (scope : ScalarStateEffect effect)
    (success : Entrypoint.validateEffectStep stateEffectCaps state ep effect index env =
      .ok step) :
    ∃ after, step = .yield after ∧ EffectValidation state env effect after := by
  obtain ⟨bindings, accepted, firstFresh, stepShape⟩ :=
    Entrypoint.validateEffectStep_succeeded stateEffectCaps state ep effect index env step success
  cases scope with
  | readCell stateName destination ty =>
    have source := effectBindings_validated state (.readCell stateName destination ty) env
      bindings (.readCell stateName destination ty) accepted
    have bindingShape : bindings = [(destination, ty)] := by simpa using source.1
    have fresh : env.lookup destination = none := by
      apply firstFresh (destination, ty)
      simp [bindingShape]
    subst bindings
    exact ⟨env ++ [(destination, ty)], stepShape, by
      cases source.2 with
      | readCell declared => exact .readCell declared fresh⟩
  | readMap stateName destination keyTy valueTy key =>
    have source := effectBindings_validated state
      (.readMap stateName destination keyTy valueTy key) env bindings
      (.readMap stateName destination keyTy valueTy key) accepted
    have bindingShape : bindings = [(destination, valueTy)] := by simpa using source.1
    have fresh : env.lookup destination = none := by
      apply firstFresh (destination, valueTy)
      simp [bindingShape]
    subst bindings
    exact ⟨env ++ [(destination, valueTy)], stepShape, by
      cases source.2 with
      | readMap declared valid => exact .readMap declared valid fresh⟩
  | require condition =>
    have source := effectBindings_validated state (.require condition) env bindings
      (.require condition) accepted
    have bindingShape : bindings = [] := by simpa using source.1
    subst bindings
    exact ⟨env, by simpa using stepShape, by
      cases source.2 with
      | require conditionValid => exact .require conditionValid⟩
  | writeCell stateName ty value =>
    have source := effectBindings_validated state (.writeCell stateName ty value) env bindings
      (.writeCell stateName ty value) accepted
    have bindingShape : bindings = [] := by simpa using source.1
    subst bindings
    exact ⟨env, by simpa using stepShape, by
      cases source.2 with
      | writeCell declared valueValid => exact .writeCell declared valueValid⟩
  | writeMap stateName keyTy valueTy key value =>
    have source := effectBindings_validated state
      (.writeMap stateName keyTy valueTy key value) env bindings
      (.writeMap stateName keyTy valueTy key value) accepted
    have bindingShape : bindings = [] := by simpa using source.1
    subst bindings
    exact ⟨env, by simpa using stepShape, by
      cases source.2 with
      | writeMap declared keyValid valueValid => exact .writeMap declared keyValid valueValid⟩
  | requireAbsent stateName keyTy key =>
    have source := effectBindings_validated state (.requireAbsent stateName keyTy key) env bindings
      (.requireAbsent stateName keyTy key) accepted
    have bindingShape : bindings = [] := by simpa using source.1
    subst bindings
    exact ⟨env, by simpa using stepShape, by
      cases source.2 with
      | requireAbsent declared keyValid => exact .requireAbsent declared keyValid⟩

private theorem effectGuard_validated (state : List StateDecl) (ep : Entrypoint)
    (effect : Effect) (index : Nat) (env : TypeEnv) (step : ForInStep TypeEnv)
    (success : Entrypoint.validateEffectStep stateEffectCaps state ep effect index env =
      .ok step) :
    ∀ condition, ep.effectGuardAt index = some condition →
      condition.validate stateEffectCaps env = .ok () := by
  unfold Entrypoint.validateEffectStep at success
  rcases bind_ok.mp success with ⟨_, _, afterWriteGate⟩
  rcases bind_ok.mp afterWriteGate with ⟨_, guardAccepted, _⟩
  intro condition guardAt
  unfold Entrypoint.validateEffectGuard at guardAccepted
  rw [guardAt] at guardAccepted
  cases valid : condition.validate stateEffectCaps env with
  | error message => simp [valid, Bind.bind, Except.bind, throw, throwThe] at guardAccepted
  | ok value => cases value; rfl

private theorem forIn_validated_effects_at (state : List StateDecl) (ep : Entrypoint)
    (effects : List Effect) (offset : Nat) (initial final : TypeEnv)
    (scalar : ScalarStateEffects effects)
    (success : forIn (effects.zipIdx offset) initial
      (fun item env => Entrypoint.validateEffectStep stateEffectCaps state ep
        item.1 item.2 env) = .ok final) :
    GuardValidatedEffects state ep initial (effects.zipIdx offset) final := by
  induction effects generalizing offset initial with
  | nil =>
    change Except.ok initial = .ok final at success
    cases success
    exact .nil
  | cons effect rest ih =>
    cases scalar with
    | cons head tail =>
      simp only [List.zipIdx_cons, List.forIn_cons] at success ⊢
      cases checked : Entrypoint.validateEffectStep stateEffectCaps state ep
          effect offset initial with
      | error message =>
        simp only [checked, bind, Except.bind] at success
        cases success
      | ok step =>
        obtain ⟨middle, shape, validated⟩ := effectStep_validated state ep effect
          offset initial step head checked
        have guardValid := effectGuard_validated state ep effect offset initial
          step checked
        simp only [checked, bind, Except.bind] at success
        rw [shape] at success
        have restValid := ih (offset + 1) middle tail success
        exact .cons (item := (effect, offset)) validated guardValid restValid

private theorem effectPrefix_env_shape (state : List StateDecl) (ep : Entrypoint)
    (env : TypeEnv)
    (accepted : Entrypoint.validateEffectPrefix stateEffectCaps state ep = .ok env) :
    env = initialEffectTypeEnv ep := by
  unfold Entrypoint.validateEffectPrefix at accepted
  rcases bind_ok.mp accepted with ⟨_, _, outputsAccepted⟩
  unfold Entrypoint.validateOutputEnvironment at outputsAccepted
  have shape := forIn_append_shape _
    (fun output : Output => (output.name, output.ty)) ep.circuit.outputs
    (ep.circuit.inputs.map (fun input => (input.name, input.ty))) env
    (by
      intro output before step success
      exact Entrypoint.validateOutputStep_succeeded ep output before step success)
    outputsAccepted
  simpa [initialEffectTypeEnv, List.map_append, List.map_map,
    Function.comp_def] using shape

/-- Successful production Impact lowering first completed the source
entrypoint validator used by the guarded effect projections below. -/
theorem lower_source_validated (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    ep.validate stateEffectCaps state = .ok () := by
  unfold Impact.lower at accepted
  cases lowered : Impact.lowerWithEffectBoundaries state ep with
  | error message => simp [lowered, Except.map] at accepted
  | ok output =>
    cases output with
    | mk candidate boundaries =>
      simp only [lowered, Except.map] at accepted
      have candidateEq : candidate = plan := Except.ok.inj accepted
      subst plan
      unfold Impact.lowerWithEffectBoundaries at lowered
      simp only [bind_ok] at lowered
      rcases lowered with ⟨_, sourceValidated, _, _, _⟩
      exact sourceValidated

private def validateReturnValueStep (caps : Capabilities) (env : TypeEnv)
    (output : Output) (_ : PUnit) : Except Diagnostic (ForInStep PUnit) := do
  if (env.lookup output.name).isSome then
    throw {span := output.span, message := s!"entrypoint return '{output.name}' shadows a source binding"}
  match output.ty.validate caps with
  | .error message => throw {span := output.span, message}
  | .ok _ => pure ()
  match output.value.validate caps env with
  | .error message => throw {span := output.span, message}
  | .ok _ => pure (.yield .unit)

private theorem validateReturnValueStep_succeeded (caps : Capabilities)
    (env : TypeEnv) (output : Output) (step : ForInStep PUnit)
    (success : validateReturnValueStep caps env output .unit = .ok step) :
    step = .yield .unit ∧ output.value.validate caps env = .ok () := by
  unfold validateReturnValueStep at success
  cases shadowed : (env.lookup output.name).isSome with
  | true => simp [shadowed, Bind.bind, Except.bind, throw, throwThe] at success
  | false =>
    cases typeCheck : output.ty.validate caps with
    | error message => simp [shadowed, typeCheck, Bind.bind, Except.bind,
        throw, throwThe] at success
    | ok checkedType =>
      cases valueCheck : output.value.validate caps env with
      | error message => simp [shadowed, typeCheck, valueCheck, throw, throwThe] at success
      | ok value =>
        cases value
        simp [shadowed, typeCheck, valueCheck] at success
        change Except.ok (.yield .unit) = .ok step at success
        exact ⟨(Except.ok.inj success).symm, rfl⟩

private theorem forIn_return_values_valid (caps : Capabilities) (env : TypeEnv)
    (outputs : List Output)
    (loopAccepted : forIn outputs PUnit.unit (validateReturnValueStep caps env) = .ok .unit) :
    ∀ output ∈ outputs, output.value.validate caps env = .ok () := by
  induction outputs with
  | nil => simp
  | cons output rest ih =>
    rw [List.forIn_cons] at loopAccepted
    cases checked : validateReturnValueStep caps env output .unit with
    | error message =>
      rw [checked] at loopAccepted
      cases loopAccepted
    | ok step =>
      obtain ⟨shape, valid⟩ := validateReturnValueStep_succeeded caps env output step checked
      subst step
      rw [checked] at loopAccepted
      simp only [bind, Except.bind] at loopAccepted
      intro result member
      rcases List.mem_cons.mp member with same | later
      · cases same
        exact valid
      · exact ih loopAccepted result later

private theorem validateEffectSuffix_returns_valid (caps : Capabilities)
    (ep : Entrypoint) (env : TypeEnv)
    (accepted : Entrypoint.validateEffectSuffix caps ep env = .ok ()) :
    ∀ output ∈ ep.returns, output.value.validate caps env = .ok () := by
  have loopAccepted :
      forIn ep.returns PUnit.unit (validateReturnValueStep caps env) = .ok .unit := by
    unfold Entrypoint.validateEffectSuffix at accepted
    by_cases namesValid : uniqueNames (ep.returns.map (·.name)) = true
    · by_cases countValid : (ep.returns.map Output.nativeReturnFieldCount).sum ≤
          maxEntrypointReturnFields
      · simp [namesValid, countValid] at accepted
        obtain ⟨_, loopAccepted, _⟩ := bind_ok.mp accepted
        exact loopAccepted
      · simp [namesValid, countValid, bind, Except.bind, throw, throwThe] at accepted
    · simp [namesValid, bind, Except.bind, throw, throwThe] at accepted
  exact forIn_return_values_valid caps env ep.returns loopAccepted

private theorem validateEffectPrechecks_circuit_valid (state : List StateDecl)
    (ep : Entrypoint)
    (accepted : Entrypoint.validateEffectPrechecks stateEffectCaps state ep = .ok ()) :
    ep.circuit.validate stateEffectCaps = .ok () := by
  unfold Entrypoint.validateEffectPrechecks at accepted
  simp only [bind_ok] at accepted
  obtain ⟨_, _, accepted⟩ := accepted
  obtain ⟨_, circuitAccepted, _⟩ := accepted
  exact circuitAccepted

private theorem validateEffectPrechecks_guard_metadata_valid (state : List StateDecl)
    (ep : Entrypoint)
    (accepted : Entrypoint.validateEffectPrechecks stateEffectCaps state ep = .ok ()) :
    (ep.effectGuards.isEmpty || ep.effectGuards.length == ep.effects.length) = true := by
  unfold Entrypoint.validateEffectPrechecks at accepted
  simp only [bind_ok] at accepted
  obtain ⟨_, _, accepted⟩ := accepted
  obtain ⟨_, _, accepted⟩ := accepted
  obtain ⟨_, _, accepted⟩ := accepted
  split at accepted
  · rcases bind_ok.mp accepted with ⟨_, _, final⟩
    cases metadata : (ep.effectGuards.isEmpty ||
        ep.effectGuards.length == ep.effects.length) with
    | true => rfl
    | false => simp [metadata, throw, throwThe] at final
  · simp [throw, throwThe, Bind.bind, Except.bind] at accepted ⊢

private theorem validateEffectPrefix_circuit_valid (state : List StateDecl)
    (ep : Entrypoint) (initial : TypeEnv)
    (accepted : Entrypoint.validateEffectPrefix stateEffectCaps state ep = .ok initial) :
    ep.circuit.validate stateEffectCaps = .ok () := by
  unfold Entrypoint.validateEffectPrefix at accepted
  rcases bind_ok.mp accepted with ⟨_, prechecksAccepted, _⟩
  exact validateEffectPrechecks_circuit_valid state ep prechecksAccepted

private theorem validateEffectPrefix_guard_metadata_valid (state : List StateDecl)
    (ep : Entrypoint) (initial : TypeEnv)
    (accepted : Entrypoint.validateEffectPrefix stateEffectCaps state ep = .ok initial) :
    (ep.effectGuards.isEmpty || ep.effectGuards.length == ep.effects.length) = true := by
  unfold Entrypoint.validateEffectPrefix at accepted
  rcases bind_ok.mp accepted with ⟨_, prechecksAccepted, _⟩
  exact validateEffectPrechecks_guard_metadata_valid state ep prechecksAccepted

/-- Accepted production lowering preserves source-circuit validation under
the canonical source capability set. -/
theorem lower_circuit_validated_source (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    ep.circuit.validate Capabilities.source = .ok () := by
  have source := lower_source_validated state ep plan accepted
  obtain ⟨initial, _, prefixAccepted, _⟩ :=
    Entrypoint.validate_effect_loop_of_success stateEffectCaps state ep source
  have circuitAccepted := validateEffectPrefix_circuit_valid state ep initial prefixAccepted
  simpa [stateEffectCaps, Capabilities.source] using circuitAccepted

/-- Accepted production lowering carries its ordered typed effects, validates each
scheduled guard in the incoming type environment, and validates every physical
return expression in the final source-effect environment. -/
theorem lower_validated_guarded_effects_and_returns (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan)
    (accepted : Impact.lower state ep = .ok plan)
    (scalar : ScalarStateEffects ep.effects) :
    ∃ final, GuardValidatedEffects state ep (initialEffectTypeEnv ep)
        (ep.effects.zipIdx) final ∧
      ∀ output ∈ ep.returns,
        output.value.validate stateEffectCaps final = .ok () := by
  have source := lower_source_validated state ep plan accepted
  unfold Entrypoint.validate at source
  rcases bind_ok.mp source with ⟨initial, prefixAccepted, afterPrefix⟩
  rcases bind_ok.mp afterPrefix with ⟨final, effectsAccepted, suffixAccepted⟩
  have initialShape := effectPrefix_env_shape state ep initial prefixAccepted
  subst initial
  refine ⟨final, ?_, ?_⟩
  · exact forIn_validated_effects_at state ep ep.effects 0
      (initialEffectTypeEnv ep) final scalar (by
        simpa only [Entrypoint.validateEffectLoop] using effectsAccepted)
  · exact validateEffectSuffix_returns_valid stateEffectCaps ep final suffixAccepted

/-- Accepted production lowering carries its ordered typed state effects and
validates every physical return expression in the final source-effect environment. -/
theorem lower_validated_effects_and_returns (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan)
    (scalar : ScalarStateEffects ep.effects) :
    ∃ final, ValidatedEffects state (initialEffectTypeEnv ep) ep.effects final ∧
      ∀ output ∈ ep.returns,
        output.value.validate stateEffectCaps final = .ok () := by
  obtain ⟨final, guarded, returnsValid⟩ :=
    lower_validated_guarded_effects_and_returns state ep plan accepted scalar
  refine ⟨final, ?_, returnsValid⟩
  simpa using GuardValidatedEffects.effects guarded

/-- Accepted production lowering carries the exact ordered typed effect
chain on the supported scalar state-effect scope. -/
theorem lower_validated_effects (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan)
    (scalar : ScalarStateEffects ep.effects) :
    ∃ final, ValidatedEffects state (initialEffectTypeEnv ep) ep.effects final := by
  obtain ⟨final, chain, _⟩ := lower_validated_effects_and_returns state ep plan accepted scalar
  exact ⟨final, chain⟩

/-- Successful lowering validates scalar source read destinations against the
initial bindings and keeps distinct destinations across the effect sequence. -/
theorem lower_scalar_read_destinations_fresh_unique (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan)
    (accepted : Impact.lower state ep = .ok plan)
    (scalar : ScalarStateEffects ep.effects) :
    (scalarReadDestinations ep.effects).Nodup ∧
      ∀ name ∈ scalarReadDestinations ep.effects,
        name ∉ (initialEffectTypeEnv ep).map Prod.fst := by
  obtain ⟨final, validated⟩ :=
    lower_validated_effects state ep plan accepted scalar
  exact ValidatedEffects.scalarReadDestinations_fresh_unique validated

/-- Accepted production lowering rejects malformed effect-guard schedules. -/
theorem lower_guard_metadata_valid (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    (ep.effectGuards.isEmpty || ep.effectGuards.length == ep.effects.length) = true := by
  have source := lower_source_validated state ep plan accepted
  obtain ⟨initial, _, prefixAccepted, _⟩ :=
    Entrypoint.validate_effect_loop_of_success stateEffectCaps state ep source
  exact validateEffectPrefix_guard_metadata_valid state ep initial prefixAccepted

end Noctium.Verification.GenericStateEffectValidation
