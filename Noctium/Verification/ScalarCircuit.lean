import Noctium.Verification.ScalarNormalizationSoundness
import Noctium.Backend.Zkir

namespace Noctium.Verification.ScalarNormalization
open Backend.Native NativeRelation

private theorem bind_ok (first : Except ε α) (next : α → Except ε β) (value : β) :
    Except.bind first next = .ok value ↔ ∃ intermediate, first = .ok intermediate ∧ next intermediate = .ok value := by
  cases first <;> simp [Except.bind]

private theorem throw_eq_error (error : ε) : (throw error : Except ε α) = .error error := rfl

private theorem map_ok (action : Except ε α) (function : α → β) (value : β) :
    function <$> action = .ok value ↔
      ∃ result, action = .ok result ∧ function result = value := by
  cases action <;> simp [Functor.map, Except.map]

private theorem mapM_ok_transfer (left : α → Except ε β) (right : α → Except δ β)
    (agreement : ∀ value result, left value = .ok result ↔ right value = .ok result)
    (values : List α) (results : List β) :
    values.mapM left = .ok results ↔ values.mapM right = .ok results := by
  induction values generalizing results with
  | nil => simp [List.mapM_nil, pure, Except.pure]
  | cons value rest ih =>
    simp only [List.mapM_cons, bind, bind_ok]
    simp only [agreement, ih, pure, Except.pure, Except.ok.injEq]

private theorem forIn_all (body : α → PUnit → Except ε (ForInStep PUnit)) (values : List α)
    (actions : ∀ value ∈ values, body value .unit = .ok (.yield .unit)) :
    forIn values PUnit.unit body = .ok .unit := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    rw [List.forIn_cons, actions value (by simp)]
    change forIn rest PUnit.unit body = .ok .unit
    exact ih (fun value member => actions value (List.mem_cons_of_mem _ member))

private theorem forIn_extract (body : α → PUnit → Except ε (ForInStep PUnit))
    (property : α → Prop) (values : List α)
    (actions : ∀ value step, body value .unit = .ok step → step = .yield .unit ∧ property value)
    (success : forIn values PUnit.unit body = .ok .unit) : ∀ value ∈ values, property value := by
  induction values with
  | nil => simp
  | cons value rest ih =>
    rw [List.forIn_cons] at success
    cases checked : body value .unit with
    | error message => simp [checked, bind, Except.bind] at success
    | ok step =>
      obtain ⟨equal, holds⟩ := actions value step checked
      subst step
      simp only [checked, bind, Except.bind] at success
      intro found member
      rcases List.mem_cons.mp member with equal | member
      · simpa [equal] using holds
      · exact ih success found member

def circuitAliases (circuit : Circuit) : AliasEnvironment :=
  circuit.inputs.map (fun input => (input.name, .input ("%input_" ++ input.name)))

private def expectedCircuitAliases (circuit : Circuit) : AliasEnvironment :=
  circuit.inputs.map (fun input => (input.name, Input.sourceTerm input))

private def scalarTypeOfCanonical {ty : Ty} {value : ty.Denote}
    (canonical : Canonical ty value) : ScalarType ty := by
  cases ty with
  | native => exact .native
  | bool => exact .bool
  | uint maximum => exact .uint maximum
  | bytes length => simp [Canonical, sourceNumber?] at canonical
  | opaqueBytes => simp [Canonical, sourceNumber?] at canonical
  | opaqueString => simp [Canonical, sourceNumber?] at canonical
  | jubjubScalar => simp [Canonical, sourceNumber?] at canonical
  | jubjubPoint => simp [Canonical, sourceNumber?] at canonical
  | foreign kind => simp [Canonical, sourceNumber?] at canonical

private theorem scalarSourceTerm (input : Input) (supported : ScalarType input.ty) :
    Input.sourceTerm input = .input ("%input_" ++ input.name) := by
  cases input with
  | mk name ty visibility span => cases supported <;> rfl

/-- Total projection for scalar relation boundaries. Current theorem consumers
restrict this projection to admitted scalar outputs or successful typed reads;
other values, including records, retain the zero fallback. -/
def valueNumber : Value → Nat
  | .native value | .uint _ value => value
  | .bool value => if value then 1 else 0
  | .bytes _ _ | .opaqueBytes _ | .opaqueString _ | .jubjubScalar _ | .jubjubPoint _ _
  | .foreignBase _ _ | .foreignScalar _ _ | .foreignPoint _ _ | .record _ => 0

theorem valueNumber_pack_scalar (ty : Ty) (value : ty.Denote)
    (scalarType : ScalarType ty) :
    valueNumber (Value.pack ty value) = number scalarType value := by
  cases scalarType <;> rfl

/-- Invert the actual independent expected-statement constructor. -/
theorem expectedCircuit_parts (circuit : Circuit) (expected : Expected)
    (accepted : expectedCircuit circuit = .ok expected) :
    circuit.validate Capabilities.crypto = .ok () ∧
    ∃ (conditions : List Normalized) (outputs : List Normalized × List Normalized),
      circuit.constraints.mapM (normalize (expectedCircuitAliases circuit)) = .ok conditions ∧
      expected.assertions = conditions.flatMap (fun normalized => normalized.assertions ++ [normalized.term]) ++ outputs.1.flatMap (·.assertions) ++ outputs.2.flatMap (·.assertions) ∧
      expected.bounds = conditions.flatMap (·.bounds) ++ outputs.1.flatMap (·.bounds) ++ outputs.2.flatMap (·.bounds) ∧
      expected.returns = outputs.1.map (·.term) ∧
      expected.groups = (circuit.inputs.filter (·.visibility == .«public»)).flatMap (fun input =>
        match input.ty with
        | .bytes 0 => []
        | .bytes _ => [input.nativeIdentifiers.map Term.input]
        | .foreign kind => (List.range kind.encodedFieldCount).map (fun index =>
            [foreignEncodedFieldTerm kind (Input.sourceTerm input) index])
        | _ => input.nativeIdentifiers.map (fun identifier => [Term.input identifier])) ++
          (if outputs.1.isEmpty then [] else [outputs.1.map (·.term)]) ∧
      expected.inputs = circuit.inputs.flatMap Input.requirements ∧
      collectCircuitOutputs (expectedCircuitAliases circuit) circuit.outputs = .ok outputs := by
  simp only [expectedCircuit, bind, bind_ok, Except.pure] at accepted
  rcases accepted with ⟨_, validation, _, disclosure, collected, collectSuccess, conditions,
    conditionSuccess, outputs, outputSuccess, equal⟩
  have collection := (convert_ok _ _ _).mp collectSuccess
  simp only [collect_eq, bind, bind_ok, Except.pure] at collection
  rcases collection with ⟨collectedResults, collectedSuccess, collectedEqual⟩
  have conditionsSuccess := (convert_ok _ _ _).mp conditionSuccess
  rw [conditionsSuccess] at collectedSuccess
  cases collectedSuccess
  cases collectedEqual
  cases equal
  have validationCrypto : circuit.validate Capabilities.crypto = .ok () := by
    change circuit.validate Capabilities.crypto = .ok () at validation
    exact validation
  refine ⟨validationCrypto, conditions, outputs, ?_, rfl, rfl, rfl, ?_, rfl, ?_⟩
  · simpa [expectedCircuitAliases, sourceInputAliases_source] using conditionsSuccess
  · simp only [List.isEmpty_map, List.map_map, Function.comp_apply]
    rfl
  · simpa [expectedCircuitAliases, sourceInputAliases_source] using outputSuccess

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
private theorem scalarExpression_validate_compat {ty : Ty} {expression : Expr ty}
    (admission : ScalarExpression expression) (types : TypeEnv)
    (valid : expression.validate Capabilities.crypto types = .ok ()) :
    expression.validate Capabilities.scalarFragment types = .ok () := by
  simpa [Capabilities.scalarFragment] using valid

private theorem normalize_native_cast {ty : Ty} (aliases : AliasEnvironment)
    (expression : Expr ty) :
    normalize aliases (.cast .native expression) = normalize aliases expression := by
  simp only [normalize, requireSourceType_eq, bind, Except.bind, pure, Except.pure]
  cases normalized : normalize aliases expression <;> simp [normalized]

/-- A scalar ABI return field has the same normalized meaning as its source value. -/
theorem scalarOutputField (aliases : AliasEnvironment) {ty : Ty}
    (value : Expr ty) (scalarType : ScalarType ty) :
    ∃ field, value.nativeCallFields = [field] ∧
      normalize aliases field = normalize aliases value := by
  cases scalarType with
  | native => exact ⟨value, rfl, rfl⟩
  | bool => exact ⟨.cast .native value, rfl, normalize_native_cast aliases value⟩
  | uint maximum => exact ⟨.cast .native value, rfl, normalize_native_cast aliases value⟩

private theorem scalarOutput_success (aliases : AliasEnvironment) (output : Output)
    (scalarType : ScalarType output.ty) {fields : List Normalized}
    {empty : Option Normalized}
    (success : normalizeCircuitOutput aliases output = .ok (fields, empty)) :
    ∃ normal, normalize aliases output.value = .ok normal ∧ fields = [normal] ∧
      empty = none ∧ output.value.nativeCallFields.mapM (normalize aliases) = .ok [normal] := by
  obtain ⟨field, nativeFieldsEq, fieldNormalizerEq⟩ :=
    scalarOutputField aliases output.value scalarType
  have nonEmptyBytes : (output.ty == .bytes 0) = false := by
    rcases output with ⟨name, ty, value, span⟩
    cases scalarType <;> rfl
  simp only [normalizeCircuitOutput, nonEmptyBytes, Bool.false_eq_true, if_false,
    Output.nativeReturnFields, nativeFieldsEq, pure, Except.pure, bind, bind_ok,
    convert_ok, Except.ok.injEq] at success
  obtain ⟨_, rfl, _, rfl, _, normalized, pairEq⟩ := success
  simp only [List.mapM_cons, List.mapM_nil, fieldNormalizerEq, bind, bind_ok, pure,
    Except.pure, convert_ok, Except.ok.injEq] at normalized
  obtain ⟨value, valueSuccess, _, rfl, rfl⟩ := normalized
  cases pairEq
  refine ⟨value, valueSuccess, rfl, rfl, ?_⟩
  rw [nativeFieldsEq, List.mapM_cons, fieldNormalizerEq, valueSuccess]
  rfl

private theorem collectCircuitOutputs_scalar_success (aliases : AliasEnvironment)
    (outputs : List Output) {collected : List Normalized × List Normalized}
    (scalarOutputs : ∀ output ∈ outputs, ScalarType output.ty)
    (success : collectCircuitOutputs aliases outputs = .ok collected) :
    ∃ normalized, outputs.mapM (fun output => normalize aliases output.value) = .ok normalized ∧
      collected.1 = normalized ∧ collected.2 = [] ∧
      outputs.mapM (fun output => output.value.nativeCallFields.mapM (normalize aliases)) =
        .ok (normalized.map fun normal => [normal]) := by
  induction outputs generalizing collected with
  | nil =>
    cases collected with
    | mk fields empty =>
      simp [collectCircuitOutputs] at success
      rcases success with ⟨rfl, rfl⟩
      exact ⟨[], rfl, rfl, rfl, rfl⟩
  | cons output rest ih =>
    simp only [collectCircuitOutputs, bind, bind_ok] at success
    rcases success with ⟨one, oneSuccess, remaining, restSuccess, collectedEq⟩
    obtain ⟨normal, normalSuccess, fieldEq, emptyEq, nativeSuccess⟩ :=
      scalarOutput_success aliases output (scalarOutputs output (by simp)) oneSuccess
    obtain ⟨restNormals, restNormalSuccess, restFieldsEq, restEmptyEq, restNativeSuccess⟩ := ih
      (fun item member => scalarOutputs item (List.mem_cons_of_mem _ member)) restSuccess
    cases collectedEq
    refine ⟨normal :: restNormals, ?_, ?_, ?_, ?_⟩
    · simp only [List.mapM_cons, normalSuccess, restNormalSuccess, bind, Except.bind]
      rfl
    · simp [fieldEq, restFieldsEq]
    · simp [emptyEq, restEmptyEq]
    · rw [List.mapM_cons, nativeSuccess, restNativeSuccess]
      rfl

private def scalarNativeInputGroups (input : Input) : List (List Term) :=
  match input.ty with
  | .bytes 0 => []
  | .bytes _ => [input.nativeIdentifiers.map Term.input]
  | .foreign kind => (List.range kind.encodedFieldCount).map fun index =>
      [foreignEncodedFieldTerm kind (Input.sourceTerm input) index]
  | _ => input.nativeIdentifiers.map fun identifier => [Term.input identifier]

private theorem scalarInputGroup (hash : Hash) (inputs : Assignment) (input : Input)
    (supported : ScalarType input.ty) :
    (scalarNativeInputGroups input).map (fun group => group.map (interpret hash inputs)) =
      [[some (inputs ("%input_" ++ input.name))]] := by
  cases input with
  | mk name ty visibility span =>
    cases ty with
    | native => simp [scalarNativeInputGroups, Input.nativeIdentifiers, interpret_input]
    | bool => simp [scalarNativeInputGroups, Input.nativeIdentifiers, interpret_input]
    | uint maximum => simp [scalarNativeInputGroups, Input.nativeIdentifiers, interpret_input]
    | bytes length => cases supported
    | opaqueBytes => cases supported
    | opaqueString => cases supported
    | jubjubScalar => cases supported
    | jubjubPoint => cases supported
    | foreign kind => cases supported

private theorem scalarInputGroups (hash : Hash) (inputs : Assignment) (sourceInputs : List Input)
    (supported : ∀ input ∈ sourceInputs, ScalarType input.ty) :
    (sourceInputs.flatMap scalarNativeInputGroups).map
        (fun group => group.map (interpret hash inputs)) =
      sourceInputs.map (fun input => [some (inputs ("%input_" ++ input.name))]) := by
  induction sourceInputs with
  | nil => rfl
  | cons input rest ih =>
    simp only [List.flatMap_cons, List.map_append, List.map_cons]
    rw [scalarInputGroup hash inputs input (supported input (by simp))]
    rw [ih (fun item member => supported item (List.mem_cons_of_mem _ member))]
    simp

theorem constraints_sound (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (types : TypeEnv) (aliases : AliasEnvironment) (values : EvalEnv)
    (environment : TypedEnvironment hash inputs aliases values types)
    (span : SourceSpan) (conditions : List (Expr .bool)) (normalized : List Normalized)
    (valid : validateConstraints Capabilities.crypto types span conditions = .ok ())
    (normal : conditions.mapM (normalize aliases) = .ok normalized)
    (bounds : ∀ requirement ∈ normalized.flatMap (·.bounds),
      ∃ value, interpret hash inputs requirement.1 = some value ∧ value.val ≤ requirement.2)
    (assertions : ∀ term ∈ normalized.flatMap (fun result => result.assertions ++ [result.term]),
      interpret hash inputs term = some one)
    (admissions : ∀ condition ∈ conditions, ScalarExpression condition) :
    runConstraints ctx values conditions = .ok () := by
  induction conditions generalizing normalized with
  | nil => rfl
  | cons condition rest ih =>
    simp only [List.mapM_cons, bind, bind_ok, Except.pure] at normal
    rcases normal with ⟨cn, nc, tail, tailNormal, equal⟩
    cases equal
    have conditionValidCrypto : condition.validate Capabilities.crypto types = .ok () := by
      cases checked : condition.validate Capabilities.crypto types with
      | error message => simp [validateConstraints, checked] at valid
      | ok result => cases result; rfl
    have conditionValid := scalarExpression_validate_compat
      (admissions condition (by simp)) types conditionValidCrypto
    have restValid : validateConstraints Capabilities.crypto types span rest = .ok () := by
      unfold validateConstraints at valid
      rw [conditionValidCrypto] at valid
      exact valid
    have requirements : Requirements hash inputs cn := by
      constructor
      · intro requirement member
        exact bounds requirement (by simp [List.mem_flatMap, member])
      · intro term member
        exact assertions term (by simp [List.mem_flatMap, member])
    obtain ⟨value, success, canonical, required, meaning⟩ := normalize_sound ctx hash implementation inputs types aliases values
      environment condition (admissions condition (by simp)) cn conditionValid nc requirements
    have asserted : interpret hash inputs cn.term = some one := assertions cn.term (by simp)
    have trueValue : value = true := by
      rw [meaning] at asserted
      cases value with
      | false =>
        have contradiction := Option.some.inj asserted
        exact False.elim (zero_ne_one (by simpa [bit] using contradiction))
      | true => rfl
    subst value
    simp only [runConstraints, success]
    apply ih tail restValid tailNormal
    · intro requirement member
      exact bounds requirement (by simp [List.mem_flatMap] at member ⊢; exact Or.inr member)
    · intro term member
      exact assertions term (by simp [List.mem_flatMap] at member ⊢; exact Or.inr (Or.inr member))
    · intro item member
      exact admissions item (List.mem_cons_of_mem _ member)

def evalOutput (ctx : EvalContext) (values : EvalEnv) (output : Output) : Except String (String × Value) := do
  pure (output.name, Value.pack output.ty (← output.value.eval ctx values))

theorem outputs_sound (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (types : TypeEnv) (aliases : AliasEnvironment) (values : EvalEnv)
    (environment : TypedEnvironment hash inputs aliases values types)
    (outputs : List Output) (normalized : List Normalized)
    (valid : ∀ output ∈ outputs, output.value.validate Capabilities.crypto types = .ok ())
    (normal : outputs.mapM (fun output => normalize aliases output.value) = .ok normalized)
    (bounds : ∀ requirement ∈ normalized.flatMap (·.bounds),
      ∃ value, interpret hash inputs requirement.1 = some value ∧ value.val ≤ requirement.2)
    (assertions : ∀ term ∈ normalized.flatMap (·.assertions), interpret hash inputs term = some one)
    (admissions : ∀ output ∈ outputs,
      ∃ scalarType : ScalarType output.ty, ScalarExpression output.value) :
    ∃ result, outputs.mapM (evalOutput ctx values) = .ok result ∧
      result.map Prod.fst = outputs.map (·.name) ∧
      result.map (fun pair => some (scalar (valueNumber pair.2))) =
        normalized.map (fun output => interpret hash inputs output.term) := by
  induction outputs generalizing normalized with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at normal
    subst normalized
    exact ⟨[], rfl, rfl, rfl⟩
  | cons output rest ih =>
    simp only [List.mapM_cons, bind, bind_ok] at normal
    rcases normal with ⟨on, no, tail, tailNormal, equal⟩
    cases equal
    have requirements : Requirements hash inputs on := by
      constructor
      · intro requirement member
        exact bounds requirement (by simp [List.mem_flatMap, member])
      · intro term member
        exact assertions term (by simp [List.mem_flatMap, member])
    obtain ⟨outputType, outputAdmission⟩ := admissions output (by simp)
    have outputValidCrypto := valid output (by simp)
    have outputValid := scalarExpression_validate_compat outputAdmission types outputValidCrypto
    obtain ⟨value, success, canonical, required, meaning⟩ := normalize_sound ctx hash implementation inputs types aliases values
      environment output.value outputAdmission on outputValid no requirements
    obtain ⟨result, resultSuccess, names, resultMeaning⟩ := ih tail
      (fun found member => valid found (List.mem_cons_of_mem _ member)) tailNormal
      (fun requirement member => bounds requirement (by simp [List.mem_flatMap] at member ⊢; exact Or.inr member))
      (fun term member => assertions term (by simp [List.mem_flatMap] at member ⊢; exact Or.inr member))
      (fun found member => admissions found (List.mem_cons_of_mem _ member))
    refine ⟨(output.name, Value.pack output.ty value) :: result, ?_, ?_, ?_⟩
    · simp only [List.mapM_cons, evalOutput, success, bind, Except.bind, pure, Except.pure, resultSuccess]
    · simp only [List.map_cons, names]
    · simp only [List.map_cons, resultMeaning, meaning]
      rw [valueNumber_pack_scalar _ _ outputType, sourceScalar_number outputType]

theorem circuit_validation_parts_with_capabilities (caps : Capabilities) (circuit : Circuit)
    (valid : circuit.validate caps = .ok ()) :
    validateConstraints caps (circuit.inputs.map (fun input => (input.name, input.ty))) circuit.span circuit.constraints = .ok () ∧
    ∀ output ∈ circuit.outputs, output.value.validate caps
      (circuit.inputs.map (fun input => (input.name, input.ty))) = .ok () := by
  cases inputNames : uniqueNames (circuit.inputs.map (·.name)) with
  | false =>
    simp [Circuit.validate, inputNames, bind, bind_ok, throw_eq_error] at valid
  | true =>
    cases nativeNames : uniqueNames (circuit.inputs.flatMap Input.nativeIdentifiers) with
    | false =>
      simp [Circuit.validate, inputNames, nativeNames, bind, bind_ok, throw_eq_error] at valid
    | true =>
      cases projectionNames : uniqueNames (circuit.inputs.flatMap Input.publicProjectionIdentifiers) with
      | false => simp [Circuit.validate, inputNames, nativeNames, projectionNames,
          bind, bind_ok, throw_eq_error] at valid
      | true =>
        cases projectionCollision : (circuit.inputs.flatMap Input.publicProjectionIdentifiers).any
            (fun name => circuit.inputs.any (fun input => input.name == name)) with
        | true => simp [Circuit.validate, inputNames, nativeNames, projectionNames,
            projectionCollision, bind, bind_ok, throw_eq_error] at valid
        | false =>
          cases outputNames : uniqueNames (circuit.outputs.map (·.name)) with
          | false => simp [Circuit.validate, inputNames, nativeNames, projectionNames,
              projectionCollision, outputNames, bind, bind_ok, throw_eq_error] at valid
          | true =>
            simp only [Circuit.validate, inputNames, nativeNames, projectionNames,
              projectionCollision, outputNames, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              bind, bind_ok] at valid
            rcases valid with ⟨_, _, afterInputs⟩
            change Except.bind (validateConstraints caps
              (circuit.inputs.map (fun input => (input.name, input.ty))) circuit.span circuit.constraints)
              _ = .ok () at afterInputs
            obtain ⟨checked, constraintsValid, afterConstraints⟩ := (bind_ok _ _ _).mp afterInputs
            cases checked
            change ((fun _ : PUnit => ()) <$> (_ : Except Diagnostic PUnit)) =
              Except.ok () at afterConstraints
            obtain ⟨⟨⟩, outputsValid, _⟩ := (map_ok _ _ _).mp afterConstraints
            refine ⟨constraintsValid, ?_⟩
            refine forIn_extract _ (fun output => output.value.validate caps
              (circuit.inputs.map (fun input => (input.name, input.ty))) = .ok ())
              circuit.outputs ?_ outputsValid
            intro output step success
            cases typeCheck : output.ty.validate caps with
            | error message => simp [typeCheck, bind, Except.bind, throw_eq_error] at success
            | ok checkedType =>
              simp only [typeCheck] at success
              split at success
              next shadows => simp [shadows, bind, Except.bind, throw_eq_error] at success
              next unshadowed =>
                cases valueCheck : output.value.validate caps
                    (circuit.inputs.map (fun input => (input.name, input.ty))) with
                | error message => simp [valueCheck, bind, Except.bind, throw_eq_error] at success
                | ok value =>
                  simp only [valueCheck] at success
                  cases success
                  exact ⟨rfl, rfl⟩

theorem circuit_validation_parts (circuit : Circuit)
    (valid : circuit.validate Capabilities.crypto = .ok ()) :
    validateConstraints Capabilities.crypto
      (circuit.inputs.map (fun input => (input.name, input.ty))) circuit.span circuit.constraints = .ok () ∧
    ∀ output ∈ circuit.outputs, output.value.validate Capabilities.crypto
      (circuit.inputs.map (fun input => (input.name, input.ty))) = .ok () :=
  circuit_validation_parts_with_capabilities Capabilities.crypto circuit valid

/-- Input admission is the executable source preflight plus field-level input
agreement. No source constraints or outputs occur in these premises. -/
structure CanonicalInputs (circuit : Circuit) (values : EvalEnv) (inputs : Assignment) : Prop where
  unique : uniqueNames (values.map Prod.fst) = true
  declared : ∀ name raw, (name, raw) ∈ values → ∃ input ∈ circuit.inputs, input.name = name
  complete : ∀ input ∈ circuit.inputs, ∃ value : input.ty.Denote,
    values.lookup input.name = some (Value.pack input.ty value) ∧ Canonical input.ty value
  binding : ∀ input ∈ circuit.inputs, ∀ value : input.ty.Denote,
    values.lookup input.name = some (Value.pack input.ty value) →
      ∀ (canonical : Canonical input.ty value),
        inputs ("%input_" ++ input.name) = scalar (number (scalarTypeOfCanonical canonical) value)

private theorem lookup_member (values : List (String × α)) (name : String) (value : α)
    (lookup : values.lookup name = some value) : (name, value) ∈ values := by
  obtain ⟨before, after, equal, _⟩ := List.lookup_eq_some_iff.mp lookup
  rw [equal]
  simp

theorem aliases_lookup (inputs : List Input) (name : String)
    (member : ∃ input ∈ inputs, input.name = name) :
    (inputs.map (fun input => (input.name, Term.input ("%input_" ++ input.name)))).lookup name =
      some (.input ("%input_" ++ name)) := by
  induction inputs with
  | nil => simpa using member
  | cons input rest ih =>
    by_cases same : name = input.name
    · simp [same]
    · have unequal : (name == input.name) = false := by simp [same]
      simp only [List.map_cons, List.lookup_cons, unequal]
      apply ih
      obtain ⟨target, targetMember, targetName⟩ := member
      rcases List.mem_cons.mp targetMember with equal | targetMember
      · subst target
        exact False.elim (same targetName.symm)
      · exact ⟨target, targetMember, targetName⟩

private theorem packed_as_canonical (ty found : Ty) (value : ty.Denote) (result : found.Denote)
    (canonical : Canonical ty value) (typed : (Value.pack ty value).as found = some result) :
    Canonical found result ∧ sourceScalar? found result = sourceScalar? ty value := by
  cases ty <;> cases found <;>
    simp_all [Value.pack, Value.as, Canonical, sourceNumber?, sourceScalar?]

structure ScalarCircuitAdmission (circuit : Circuit) : Prop where
  constraints : ∀ condition ∈ circuit.constraints, ScalarExpression condition
  outputs : ∀ output ∈ circuit.outputs,
    ∃ scalarType : ScalarType output.ty, ScalarExpression output.value

/-- Scalar expression admission survives literal-true constraint pruning.
The retained constraints and outputs inherit admission from the source. -/
theorem ScalarCircuitAdmission.pruneCircuit (circuit : Circuit)
    (admitted : ScalarCircuitAdmission circuit) :
    ScalarCircuitAdmission (Passes.pruneCircuit circuit) := by
  have pruneTrue_subset : ∀ conditions condition,
      condition ∈ pruneTrue conditions → condition ∈ conditions := by
    intro conditions
    induction conditions with
    | nil =>
      intro condition member
      simp [pruneTrue] at member
    | cons head rest ih =>
      intro condition member
      by_cases literal : head = .bool true
      · subst head
        simp only [pruneTrue] at member
        exact List.mem_cons_of_mem _ (ih condition member)
      · have retained : pruneTrue (head :: rest) = head :: pruneTrue rest := by
          simp [pruneTrue, literal]
        rw [retained] at member
        rcases List.mem_cons.mp member with same | member
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons.mpr (Or.inr (ih condition member))
  constructor
  · intro condition member
    exact admitted.constraints condition (pruneTrue_subset circuit.constraints condition member)
  · intro output member
    exact admitted.outputs output (by simpa [Passes.pruneCircuit] using member)

/-- A scalar-admitted return lowers through exactly one native ABI field, and
that field remains inside the admitted scalar expression fragment. Bool and
UInt fields use the admitted `.cast .native` projection. -/
theorem ScalarCircuitAdmission.nativeReturnFields (circuit : Circuit)
    (admitted : ScalarCircuitAdmission circuit) (output : Output)
    (member : output ∈ circuit.outputs) :
    ∃ field : Expr .native,
      output.nativeReturnFields = .ok [field] ∧ ScalarExpression field := by
  cases output with
  | mk name ty value span =>
    obtain ⟨scalarType, expressionAdmission⟩ :=
      admitted.outputs ⟨name, ty, value, span⟩ member
    cases scalarType with
    | native =>
      refine ⟨value, ?_, expressionAdmission⟩
      rfl
    | bool =>
      refine ⟨.cast .native value, ?_,
        ScalarExpression.cast value .bool .native expressionAdmission⟩
      rfl
    | uint maximum =>
      refine ⟨.cast .native value, ?_,
        ScalarExpression.cast value (.uint maximum) .native expressionAdmission⟩
      rfl

private theorem expectedAliases_eq_circuitAliases (circuit : Circuit)
    (values : EvalEnv) (inputs : Assignment)
    (admitted : CanonicalInputs circuit values inputs) :
    expectedCircuitAliases circuit = circuitAliases circuit := by
  unfold expectedCircuitAliases circuitAliases
  apply List.map_congr_left
  intro input member
  obtain ⟨value, _, canonical⟩ := admitted.complete input member
  simp only [Prod.mk.injEq]
  exact ⟨trivial, scalarSourceTerm input (scalarTypeOfCanonical canonical)⟩

/-- Establish alias and range invariants from input admission, including the
normalizer's concrete `%input_` alias construction. -/
theorem CanonicalInputs.typedEnvironment (circuit : Circuit) (values : EvalEnv) (inputs : Assignment)
    (admitted : CanonicalInputs circuit values inputs) (hash : Hash) :
    TypedEnvironment hash inputs (circuitAliases circuit) values
      (circuit.inputs.map (fun input => (input.name, input.ty))) := by
  constructor
  · intro name ty raw value lookup typed
    obtain ⟨input, member, inputName⟩ := admitted.declared name raw (lookup_member _ _ _ lookup)
    obtain ⟨inputValue, inputLookup, canonical⟩ := admitted.complete input member
    have rawEqual : raw = Value.pack input.ty inputValue := by
      rw [inputName] at inputLookup
      rw [lookup] at inputLookup
      exact Option.some.inj inputLookup
    subst raw
    obtain ⟨canonicalFound, sourceMeaning⟩ := packed_as_canonical _ _ _ _ canonical typed
    refine ⟨canonicalFound, .input ("%input_" ++ name), ?_, ?_⟩
    · exact aliases_lookup _ _ ⟨input, member, inputName⟩
    · simp only [interpret_input]
      rw [← inputName, admitted.binding input member inputValue inputLookup canonical]
      rw [← sourceScalar_number (scalarTypeOfCanonical canonical)]
      exact sourceMeaning.symm
  · intro name ty lookup
    have member := lookup_member _ _ _ lookup
    obtain ⟨input, inputMember, pairEqual⟩ := List.mem_map.mp member
    have inputName : input.name = name := congrArg Prod.fst pairEqual
    have inputTy : input.ty = ty := congrArg Prod.snd pairEqual
    obtain ⟨value, rawLookup, canonical⟩ := admitted.complete input inputMember
    subst ty
    exact ⟨Value.pack input.ty value, value, by simpa [inputName] using rawLookup,
      number_pack_as _ _ canonical⟩

private theorem bind_ok_intro (first : Except ε α) (next : α → Except ε β) (value : α) (result : β)
    (checked : first = .ok value) (rest : next value = .ok result) :
    Except.bind first next = .ok result := by
  rw [checked]
  exact rest

theorem circuit_run_preflight (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    (circuit : Circuit) (values result : EvalEnv) (inputs : Assignment)
    (admitted : CanonicalInputs circuit values inputs)
    (valid : circuit.validate (evaluationCapabilities ctx) = .ok ())
    (constraints : runConstraints ctx values circuit.constraints = .ok ())
    (outputs : circuit.outputs.mapM (evalOutput ctx values) = .ok result) :
    circuit.run ctx values = .ok result := by
  simp only [Circuit.run, valid, admitted.unique, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine bind_ok_intro _ _ PUnit.unit _ ?_ ?_
  · apply forIn_all
    intro pair member
    obtain ⟨input, inputMember, inputName⟩ := admitted.declared pair.1 pair.2 member
    have declared : (circuit.inputs.any (fun input => input.name == pair.1)) = true := by
      apply List.any_eq_true.mpr
      exact ⟨input, inputMember, by simp [inputName]⟩
    simp only [declared, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  · refine bind_ok_intro _ _ PUnit.unit _ ?_ ?_
    · apply forIn_all
      intro input member
      rcases input with ⟨name, ty, visibility, span⟩
      obtain ⟨value, lookup, canonical⟩ := admitted.complete _ member
      simp [lookup, Value.pack, Value.as, canonical_eq]
      cases ty with
      | native =>
        have bound : value < ctx.modulus := by simpa [modulus] using canonical.1
        simp [bound]
        rfl
      | bool => rfl
      | uint maximum =>
        have bound : value < ctx.modulus := by simpa [modulus] using canonical.1
        simp [canonical.2.1, canonical.2.2, bound]
        rfl
      | bytes length => simp [Canonical, sourceNumber?] at canonical
      | opaqueBytes => simp [Canonical, sourceNumber?] at canonical
      | opaqueString => simp [Canonical, sourceNumber?] at canonical
      | jubjubScalar => simp [Canonical, sourceNumber?] at canonical
      | jubjubPoint => simp [Canonical, sourceNumber?] at canonical
      | foreign kind => simp [Canonical, sourceNumber?] at canonical
    · change Except.bind (runConstraints ctx values circuit.constraints)
        (fun _ => circuit.outputs.mapM (evalOutput ctx values)) = .ok result
      rw [constraints]
      exact outputs

/-- Independent statement semantics imply successful execution of the original
source circuit and its exact return and always-active Impact group values. -/
theorem expectedCircuit_sound (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (circuit : Circuit) (values : EvalEnv) (expected : Expected)
    (admitted : CanonicalInputs circuit values inputs)
    (accepted : expectedCircuit circuit = .ok expected)
    (bounds : ∀ requirement ∈ expected.bounds,
      ∃ value, interpret hash inputs requirement.1 = some value ∧ value.val ≤ requirement.2)
    (assertions : ∀ term ∈ expected.assertions, interpret hash inputs term = some one)
    (scalarAdmission : ScalarCircuitAdmission circuit) :
    ∃ result, circuit.run ctx values = .ok result ∧
      result.map Prod.fst = circuit.outputs.map (·.name) ∧
      result.map (fun pair => some (scalar (valueNumber pair.2))) = expected.returns.map (interpret hash inputs) ∧
      expected.groups.map (fun group => group.map (interpret hash inputs)) =
        (circuit.inputs.filter (·.visibility == .«public»)).map
          (fun input => [some (inputs ("%input_" ++ input.name))]) ++
        (if result.isEmpty then [] else [result.map (fun pair => some (scalar (valueNumber pair.2)))]) := by
  have parts := expectedCircuit_parts circuit expected accepted
  have validation := parts.1
  obtain ⟨conditions, outputs, conditionNormals, shapes⟩ := parts.2
  have aliasesEqual := expectedAliases_eq_circuitAliases circuit values inputs admitted
  rw [aliasesEqual] at conditionNormals
  have assertionShape := shapes.1
  have shapes := shapes.2
  have boundShape := shapes.1
  have shapes := shapes.2
  have returnShape := shapes.1
  have shapes := shapes.2
  have groupShape := shapes.1
  have outputCollectionSuccess := shapes.2.2
  rw [aliasesEqual] at outputCollectionSuccess
  classical
  have outputTypes : ∀ output ∈ circuit.outputs, ScalarType output.ty := by
    intro output member
    exact Classical.choose (scalarAdmission.outputs output member)
  obtain ⟨outputNormals, outputNormalSuccess, outputFieldsEq, outputEmptyEq, _nativeFieldsSuccess⟩ :=
    collectCircuitOutputs_scalar_success (circuitAliases circuit) circuit.outputs
      outputTypes outputCollectionSuccess
  have environment := admitted.typedEnvironment circuit values inputs hash
  obtain ⟨conditionValidation, outputValidation⟩ := circuit_validation_parts circuit validation
  have constraintSuccess := constraints_sound ctx hash implementation inputs _ _ values environment
    circuit.span circuit.constraints conditions conditionValidation conditionNormals
    (fun requirement member => bounds requirement (by
      rw [boundShape]
      simp only [List.mem_append]
      exact Or.inl (Or.inl member)))
    (fun term member => assertions term (by
      rw [assertionShape]
      simp only [List.mem_append]
      exact Or.inl (Or.inl member)))
    (fun condition member => scalarAdmission.constraints condition member)
  obtain ⟨result, outputSuccess, names, outputMeaning⟩ := outputs_sound ctx hash implementation inputs _ _ values environment
    circuit.outputs outputNormals outputValidation outputNormalSuccess
    (fun requirement member => bounds requirement (by
      rw [boundShape, outputFieldsEq, outputEmptyEq]
      simp only [List.flatMap_nil, List.append_nil, List.mem_append]
      exact Or.inr member))
    (fun term member => assertions term (by
      rw [assertionShape, outputFieldsEq, outputEmptyEq]
      simp only [List.flatMap_nil, List.append_nil, List.mem_append]
      exact Or.inr member))
    (fun output member => scalarAdmission.outputs output member)
  have runtimeValidation : circuit.validate (evaluationCapabilities ctx) = .ok () := by
    simpa [evaluationCapabilities, Capabilities.crypto, implementation.modulus] using validation
  refine ⟨result, circuit_run_preflight ctx implementation.modulus circuit values result inputs admitted runtimeValidation
    constraintSuccess outputSuccess, names, ?_, ?_⟩
  · rw [returnShape, outputFieldsEq]
    simpa only [List.map_map, Function.comp_def] using outputMeaning
  · have publicInputGroups := scalarInputGroups hash inputs
      (circuit.inputs.filter (·.visibility == .«public»)) (by
        intro input member
        obtain ⟨inputMember, _⟩ := List.mem_filter.mp member
        have existsInput := admitted.complete input inputMember
        have canonical := (Classical.choose_spec existsInput).2
        exact scalarTypeOfCanonical canonical)
    have empty : outputNormals.isEmpty = result.isEmpty := by
      have same := congrArg List.isEmpty outputMeaning
      simpa only [List.isEmpty_map] using same.symm
    have outputGroup :
        (if outputNormals.isEmpty then [] else [outputNormals.map (·.term)]).map
            (fun group => group.map (interpret hash inputs)) =
          (if result.isEmpty then [] else
            [result.map (fun pair => some (scalar (valueNumber pair.2)))]) := by
      rw [← empty]
      split <;> simp [List.map_map, Function.comp_def, ← outputMeaning]
    rw [groupShape, outputFieldsEq]
    simp only [List.map_append]
    change
      (List.map (fun group => group.map (interpret hash inputs))
          ((circuit.inputs.filter (·.visibility == .«public»)).flatMap scalarNativeInputGroups) ++
        List.map (fun group => group.map (interpret hash inputs))
          (if outputNormals.isEmpty then [] else [outputNormals.map (·.term)])) =
      (List.map (fun input => [some (inputs ("%input_" ++ input.name))])
          (circuit.inputs.filter (·.visibility == .«public»)) ++
        if result.isEmpty then [] else [result.map (fun pair => some (scalar (valueNumber pair.2)))])
    rw [publicInputGroups, outputGroup]


theorem circuit_run_steps (ctx : EvalContext) (circuit : Circuit) (values result : EvalEnv)
    (success : circuit.run ctx values = .ok result) :
    runConstraints ctx values circuit.constraints = .ok () ∧
      circuit.outputs.mapM (evalOutput ctx values) = .ok result := by
  cases validation : circuit.validate (evaluationCapabilities ctx) with
  | error diagnostic => simp [Circuit.run, validation, bind, Except.bind] at success
  | ok value =>
    cases unique : uniqueNames (values.map Prod.fst) with
    | false => simp [Circuit.run, validation, unique, bind, Except.bind] at success
    | true =>
      simp only [Circuit.run, validation, unique, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        bind, bind_ok] at success
      rcases success with ⟨_, declared, _, checked, unit, constraints, output⟩
      cases unit
      exact ⟨constraints, output⟩

theorem constraints_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv)
    (agreement : AliasAgreement hash inputs aliases values)
    (conditions : List (Expr .bool)) (normalized : List Normalized)
    (normal : conditions.mapM (normalize aliases) = .ok normalized)
    (admissions : ∀ condition ∈ conditions, ScalarExpression condition)
    (success : runConstraints ctx values conditions = .ok ()) :
    (∀ requirement ∈ normalized.flatMap (·.bounds),
      ∃ value, interpret hash inputs requirement.1 = some value ∧ value.val ≤ requirement.2) ∧
    (∀ term ∈ normalized.flatMap (fun result => result.assertions ++ [result.term]),
      interpret hash inputs term = some one) := by
  induction conditions generalizing normalized with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at normal
    subst normalized
    simp
  | cons condition rest ih =>
    cases conditionResult : condition.eval ctx values with
    | error message => simp [runConstraints, conditionResult] at success
    | ok result =>
      cases result with
      | false => simp [runConstraints, conditionResult] at success
      | true =>
        have restSuccess : runConstraints ctx values rest = .ok () := by
          simpa only [runConstraints, conditionResult] using success
        simp only [List.mapM_cons, bind, bind_ok] at normal
        rcases normal with ⟨cn, nc, tail, nt, equal⟩
        cases equal
        obtain ⟨actual, actualNormal, canonical, requirements, meaning⟩ := normalize_success ctx hash implementation inputs
          aliases values agreement condition (admissions condition (by simp)) true conditionResult
        rw [nc] at actualNormal
        cases actualNormal
        obtain ⟨tailBounds, tailAssertions⟩ := ih tail nt
          (fun item member => admissions item (List.mem_cons_of_mem _ member)) restSuccess
        constructor
        · intro requirement member
          simp only [List.flatMap_cons, List.mem_append] at member
          rcases member with member | member
          · exact requirements.1 requirement member
          · exact tailBounds requirement member
        · intro term member
          simp only [List.flatMap_cons, List.mem_append, List.mem_singleton] at member
          rcases member with (member | equal) | member
          · exact requirements.2 term member
          · subst term
            simpa [sourceScalar?, sourceNumber?] using meaning
          · exact tailAssertions term member

private theorem outputs_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv)
    (agreement : AliasAgreement hash inputs aliases values)
    (outputs : List Output) (normalized : List Normalized) (result : EvalEnv)
    (normal : outputs.mapM (fun output => normalize aliases output.value) = .ok normalized)
    (admissions : ∀ output ∈ outputs, ScalarExpression output.value)
    (success : outputs.mapM (evalOutput ctx values) = .ok result) :
    (∀ requirement ∈ normalized.flatMap (·.bounds),
      ∃ value, interpret hash inputs requirement.1 = some value ∧ value.val ≤ requirement.2) ∧
    (∀ term ∈ normalized.flatMap (·.assertions), interpret hash inputs term = some one) := by
  induction outputs generalizing normalized result with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at normal
    subst normalized
    simp
  | cons output rest ih =>
    simp only [List.mapM_cons, bind, bind_ok] at normal success
    rcases normal with ⟨on, no, tail, nt, equal⟩
    cases equal
    rcases success with ⟨first, firstResult, remaining, tailResult, equal⟩
    simp only [evalOutput, bind, bind_ok] at firstResult
    rcases firstResult with ⟨value, evaluation, equal⟩
    obtain ⟨actual, actualNormal, canonical, requirements, meaning⟩ := normalize_success ctx hash implementation inputs
      aliases values agreement output.value (admissions output (by simp)) value evaluation
    rw [no] at actualNormal
    cases actualNormal
    obtain ⟨tailBounds, tailAssertions⟩ := ih tail remaining nt
      (fun item member => admissions item (List.mem_cons_of_mem _ member)) tailResult
    constructor
    · intro requirement member
      simp only [List.flatMap_cons, List.mem_append] at member
      rcases member with member | member
      · exact requirements.1 requirement member
      · exact tailBounds requirement member
    · intro term member
      simp only [List.flatMap_cons, List.mem_append] at member
      rcases member with member | member
      · exact requirements.2 term member
      · exact tailAssertions term member

/-- Successful source execution satisfies every requirement of the actual
expected-statement constructor. Native witness existence remains a separate
lowerer completeness obligation. -/
theorem expectedCircuit_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (circuit : Circuit) (values result : EvalEnv) (expected : Expected)
    (admitted : CanonicalInputs circuit values inputs)
    (accepted : expectedCircuit circuit = .ok expected)
    (success : circuit.run ctx values = .ok result)
    (scalarAdmission : ScalarCircuitAdmission circuit) :
    (∀ requirement ∈ expected.bounds,
      ∃ value, interpret hash inputs requirement.1 = some value ∧ value.val ≤ requirement.2) ∧
    (∀ term ∈ expected.assertions, interpret hash inputs term = some one) := by
  have parts := expectedCircuit_parts circuit expected accepted
  obtain ⟨conditions, outputs, conditionNormals, shapes⟩ := parts.2
  have aliasesEqual := expectedAliases_eq_circuitAliases circuit values inputs admitted
  rw [aliasesEqual] at conditionNormals
  have assertionShape := shapes.1
  have shapes := shapes.2
  have boundShape := shapes.1
  have shapes := shapes.2.2.2
  have outputCollectionSuccess := shapes.2
  rw [aliasesEqual] at outputCollectionSuccess
  classical
  have outputTypes : ∀ output ∈ circuit.outputs, ScalarType output.ty := by
    intro output member
    exact Classical.choose (scalarAdmission.outputs output member)
  obtain ⟨outputNormals, outputNormalSuccess, outputFieldsEq, outputEmptyEq, _nativeFieldsSuccess⟩ :=
    collectCircuitOutputs_scalar_success (circuitAliases circuit) circuit.outputs
      outputTypes outputCollectionSuccess
  obtain ⟨conditionSuccess, outputSuccess⟩ := circuit_run_steps ctx circuit values result success
  have environment := admitted.typedEnvironment circuit values inputs hash
  obtain ⟨conditionBounds, conditionAssertions⟩ := constraints_complete ctx hash implementation inputs _ values
    environment.aliases circuit.constraints conditions conditionNormals scalarAdmission.constraints conditionSuccess
  obtain ⟨outputBounds, outputAssertions⟩ := outputs_complete ctx hash implementation inputs _ values
    environment.aliases circuit.outputs outputNormals result outputNormalSuccess
    (fun output member => by
      obtain ⟨_, expressionAdmission⟩ := scalarAdmission.outputs output member
      exact expressionAdmission) outputSuccess
  constructor
  · intro requirement member
    rw [boundShape, outputFieldsEq, outputEmptyEq] at member
    simp only [List.flatMap_nil, List.append_nil, List.mem_append] at member
    rcases member with member | member
    · exact conditionBounds requirement member
    · exact outputBounds requirement member
  · intro term member
    rw [assertionShape, outputFieldsEq, outputEmptyEq] at member
    simp only [List.flatMap_nil, List.append_nil, List.mem_append] at member
    rcases member with member | member
    · exact conditionAssertions term member
    · exact outputAssertions term member

end Noctium.Verification.ScalarNormalization
