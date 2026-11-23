import Noctium.Verification.ScalarCircuit
import Noctium.Verification.GenericStateCircuitParts

namespace Noctium.Verification.GenericStateAliases
open ScalarNormalization NativeRelation Backend.Native

private theorem strip_input_prefix (name : String) :
    (("%input_" ++ name).drop 7).toString = name := by
  apply String.toList_injective
  simp [String.toList_copy_drop, String.toList_append]

theorem initialAliases_eq (entry : Entrypoint) (plan : Backend.Impact.Plan) :
    GenericStateCircuitParts.initialAliases entry plan =
      circuitAliases entry.circuit ++
      ((plan.reads.drop ((entry.circuit.inputs.filter
        (·.visibility == .«public»)).length)).map
          (fun read => (read.name, Term.input ("%input_" ++ read.name)))) := by
  simp only [GenericStateCircuitParts.initialAliases,
    GenericStateCircuitParts.inputRequirements, circuitAliases,
    List.map_append, List.map_map, List.map_drop, Function.comp_def,
    strip_input_prefix]

private theorem bind_ok (first : Except ε α) (next : α → Except ε β)
    (result : β) : Except.bind first next = .ok result ↔
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem throw_eq_error (error : ε) : (throw error : Except ε α) = .error error := rfl

private theorem map_ok (action : Except ε α) (function : α → β) (value : β) :
    function <$> action = .ok value ↔
      ∃ result, action = .ok result ∧ function result = value := by
  cases action <;> simp [Functor.map, Except.map]

theorem forIn_extract (body : α → PUnit → Except ε (ForInStep PUnit))
    (property : α → Prop) (values : List α)
    (actions : ∀ value step, body value .unit = .ok step →
      step = .yield .unit ∧ property value)
    (success : forIn values PUnit.unit body = .ok .unit) :
    ∀ value ∈ values, property value := by
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

/-- Successful source circuit validation forbids an output from shadowing any
declared input, including a value supplied in an input environment. -/
theorem validated_outputs_unshadowed (circuit : Circuit)
    (valid : circuit.validate {poseidon2 := true} = .ok ()) :
    ∀ output ∈ circuit.outputs,
      (circuit.inputs.map (fun input => (input.name, input.ty))).lookup
        output.name = none := by
  cases inputNames : uniqueNames (circuit.inputs.map (·.name)) with
  | false => simp [Circuit.validate, inputNames, bind, bind_ok, throw_eq_error] at valid
  | true =>
    cases nativeNames : uniqueNames (circuit.inputs.flatMap Input.nativeIdentifiers) with
    | false => simp [Circuit.validate, inputNames, nativeNames, bind, bind_ok,
        throw_eq_error] at valid
    | true =>
      cases projectionNames : uniqueNames
          (circuit.inputs.flatMap Input.publicProjectionIdentifiers) with
      | false => simp [Circuit.validate, inputNames, nativeNames, projectionNames,
          bind, bind_ok, throw_eq_error] at valid
      | true =>
        cases projectionCollision : (circuit.inputs.flatMap
            Input.publicProjectionIdentifiers).any (fun name =>
              circuit.inputs.any (fun input => input.name == name)) with
        | true => simp [Circuit.validate, inputNames, nativeNames, projectionNames,
            projectionCollision, bind, bind_ok, throw_eq_error] at valid
        | false =>
          cases outputNames : uniqueNames (circuit.outputs.map (·.name)) with
          | false => simp [Circuit.validate, inputNames, nativeNames, projectionNames,
              projectionCollision, outputNames, bind, bind_ok, throw_eq_error] at valid
          | true =>
            simp only [Circuit.validate, inputNames, nativeNames, projectionNames,
              projectionCollision, outputNames,
              Bool.not_true, Bool.false_eq_true, ↓reduceIte] at valid
            simp only [bind, bind_ok] at valid
            rcases valid with ⟨_, _, afterInputs⟩
            change Except.bind (validateConstraints {poseidon2 := true}
              (circuit.inputs.map (fun input => (input.name, input.ty)))
              circuit.span circuit.constraints) _ = .ok () at afterInputs
            obtain ⟨checked, constraintsValid, afterConstraints⟩ :=
              (bind_ok _ _ _).mp afterInputs
            cases checked
            change ((fun _ : PUnit => ()) <$> (_ : Except _ PUnit)) =
              Except.ok () at afterConstraints
            obtain ⟨⟨⟩, outputChecks, _⟩ := (map_ok _ _ _).mp afterConstraints
            refine forIn_extract _ (fun output =>
              (circuit.inputs.map (fun input => (input.name, input.ty))).lookup
                output.name = none) circuit.outputs ?_ outputChecks
            intro output step success
            cases typeChecked : output.ty.validate {poseidon2 := true} with
            | error message => simp [typeChecked, bind, Except.bind] at success
            | ok result =>
              simp only [typeChecked] at success
              split at success
              next shadow => cases success
              next unshadowed =>
                cases expressionChecked : output.value.validate {poseidon2 := true}
                    (circuit.inputs.map (fun input => (input.name, input.ty))) with
                | error message => simp [expressionChecked, bind, Except.bind] at success
                | ok result =>
                  simp only [expressionChecked] at success
                  cases success
                  constructor
                  · rfl
                  · cases found : (circuit.inputs.map
                        (fun input => (input.name, input.ty))).lookup output.name with
                    | none => rfl
                    | some ty => simp [found] at unshadowed

private theorem lookup_member (values : List (String × α))
    (name : String) (value : α)
    (found : values.lookup name = some value) : (name, value) ∈ values := by
  obtain ⟨before, after, equal, _⟩ := List.lookup_eq_some_iff.mp found
  rw [equal]
  simp

theorem canonicalInputs_output_unused (circuit : Circuit)
    (values : EvalEnv) (inputs : Assignment)
    (admitted : CanonicalInputs circuit values inputs)
    (valid : circuit.validate {poseidon2 := true} = .ok ()) :
    ∀ output ∈ circuit.outputs, values.lookup output.name = none := by
  intro output member
  have typeNone := validated_outputs_unshadowed circuit valid output member
  cases found : values.lookup output.name with
  | none => rfl
  | some raw =>
    obtain ⟨input, inputMember, inputName⟩ :=
      admitted.declared output.name raw (lookup_member values output.name raw found)
    have mapped : (input.name, input.ty) ∈
        circuit.inputs.map (fun item => (item.name, item.ty)) :=
      List.mem_map.mpr ⟨input, inputMember, rfl⟩
    have unmatched := (List.lookup_eq_none_iff.mp typeNone)
      (input.name, input.ty) mapped
    simp [inputName] at unmatched

/-- A normalized output alias whose name is absent from the input environment
does not change the meaning of any existing input binding. -/
theorem aliasAgreement_cons_unused (hash : Hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv)
    (name : String) (term : Term)
    (agreement : AliasAgreement hash inputs aliases values)
    (unused : values.lookup name = none) :
    AliasAgreement hash inputs ((name, term) :: aliases) values := by
  intro found ty raw value lookup typed
  have different : found ≠ name := by
    intro equal
    subst found
    rw [unused] at lookup
    cases lookup
  obtain ⟨canonical, oldTerm, aliasLookup, meaning⟩ :=
    agreement found ty raw value lookup typed
  have unequal : (found == name) = false := by simp [different]
  refine ⟨canonical, oldTerm, ?_, meaning⟩
  simp [List.lookup_cons, unequal, aliasLookup]

theorem typedEnvironment_cons_unused (hash : Hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv) (types : TypeEnv)
    (name : String) (term : Term)
    (environment : TypedEnvironment hash inputs aliases values types)
    (unused : values.lookup name = none) :
    TypedEnvironment hash inputs ((name, term) :: aliases) values types := by
  exact ⟨aliasAgreement_cons_unused hash inputs aliases values name term
    environment.aliases unused, environment.complete⟩

theorem packed_as_canonical (ty found : Ty) (value : ty.Denote)
    (result : found.Denote) (canonical : Canonical ty value)
    (typed : (Value.pack ty value).as found = some result) :
    Canonical found result ∧ sourceScalar? found result = sourceScalar? ty value := by
  cases ty <;> cases found <;>
    simp_all [Value.pack, Value.as, Canonical, sourceNumber?, sourceScalar?]

/-- Appending later read-input aliases cannot change the first alias already
found for an admitted source input. -/
theorem typedEnvironment_append_aliases (hash : Hash) (inputs : Assignment)
    (aliases extra : AliasEnvironment) (values : EvalEnv) (types : TypeEnv)
    (environment : TypedEnvironment hash inputs aliases values types) :
    TypedEnvironment hash inputs (aliases ++ extra) values types := by
  constructor
  · intro name ty raw value lookup typed
    obtain ⟨canonical, term, found, meaning⟩ :=
      environment.aliases name ty raw value lookup typed
    refine ⟨canonical, term, ?_, meaning⟩
    simp [List.lookup_append, found]
  · exact environment.complete

theorem initialTypedEnvironment (hash : Hash) (inputs : Assignment)
    (entry : Entrypoint) (plan : Backend.Impact.Plan) (values : EvalEnv)
    (admitted : CanonicalInputs entry.circuit values inputs) :
    TypedEnvironment hash inputs
      (GenericStateCircuitParts.initialAliases entry plan) values
      (entry.circuit.inputs.map (fun input => (input.name, input.ty))) := by
  rw [initialAliases_eq]
  exact typedEnvironment_append_aliases hash inputs _ _ values _
    (admitted.typedEnvironment entry.circuit values inputs hash)

/-- Append one fresh read alias, value, and type in the same order used by
the production input schema. -/
theorem typedEnvironment_snoc (hash : Hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv) (types : TypeEnv)
    (name : String) (ty : Ty) (value : ty.Denote) (term : Term)
    (environment : TypedEnvironment hash inputs aliases values types)
    (freshAlias : aliases.lookup name = none)
    (freshValue : values.lookup name = none)
    (freshType : types.lookup name = none)
    (canonical : Canonical ty value)
    (meaning : interpret hash inputs term = sourceScalar? ty value) :
    TypedEnvironment hash inputs (aliases ++ [(name, term)])
      (values ++ [(name, Value.pack ty value)]) (types ++ [(name, ty)]) := by
  constructor
  · intro found foundTy raw result lookup typed
    by_cases same : found = name
    · subst found
      simp [List.lookup_append, freshValue] at lookup
      cases lookup
      have aliasLookup : (aliases ++ [(name, term)]).lookup name = some term := by
        simp [List.lookup_append, freshAlias]
      obtain ⟨foundCanonical, sourceMeaning⟩ :=
        packed_as_canonical ty foundTy value result canonical typed
      exact ⟨foundCanonical, term, aliasLookup, meaning.trans sourceMeaning.symm⟩
    · have unequal : (found == name) = false := by simp [same]
      simp only [List.lookup_append, List.lookup_cons, unequal,
        List.lookup_nil, Option.or_none] at lookup
      obtain ⟨oldCanonical, oldTerm, oldLookup, oldMeaning⟩ :=
        environment.aliases found foundTy raw result lookup typed
      refine ⟨oldCanonical, oldTerm, ?_, oldMeaning⟩
      simp [List.lookup_append, oldLookup]
  · intro found foundTy lookup
    by_cases same : found = name
    · subst found
      simp [List.lookup_append, freshType] at lookup
      cases lookup
      exact ⟨Value.pack ty value, value,
        by simp [List.lookup_append, freshValue], number_pack_as ty value canonical⟩
    · have unequal : (found == name) = false := by simp [same]
      simp only [List.lookup_append, List.lookup_cons, unequal,
        List.lookup_nil, Option.or_none] at lookup
      obtain ⟨raw, result, oldLookup, typed⟩ :=
        environment.complete found foundTy lookup
      exact ⟨raw, result, by simp [List.lookup_append, oldLookup], typed⟩

end Noctium.Verification.GenericStateAliases
