import Noctium.Verification.GenericStateCircuitParts
import Noctium.Verification.GenericStateAliases
import Noctium.Verification.GenericStateKeys
import Noctium.Verification.ScalarNormalizationSoundness

namespace Noctium.Verification.ScalarOutputFrame

open Backend.Native NativeRelation ScalarNormalization GenericStateCircuitParts

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem appendOutput_normalize (output : Output) (frame next : OutputFrame)
    (accepted : appendOutput output frame = .ok next) :
    ∃ normalized,
      normalize frame.1 output.value = .ok normalized ∧
      next.1 = (output.name, normalized.term) :: frame.1 ∧
      next.2.1 = frame.2.1 ++ normalized.bounds ∧
      next.2.2 = frame.2.2 ++ normalized.assertions := by
  unfold appendOutput at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨normalized, normalizedAccepted, result⟩
  cases result
  have normal : normalize frame.1 output.value = .ok normalized := by
    unfold normalizeOutput at normalizedAccepted
    cases checked : normalize frame.1 output.value with
    | error message =>
      rw [checked] at normalizedAccepted
      change (Except.error {span := output.span, message := message} :
        Except Diagnostic Normalized) = .ok normalized at normalizedAccepted
      cases normalizedAccepted
    | ok found =>
      simp [checked] at normalizedAccepted
      cases normalizedAccepted
      rfl
  exact ⟨normalized, normal, rfl, rfl, rfl⟩

private theorem appendOutput_source_sound (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (types : TypeEnv) (values : EvalEnv) (output : Output) (frame next : OutputFrame)
    (environment : TypedEnvironment hash inputs frame.1 values types)
    (admission : ScalarExpression output.value)
    (valid : output.value.validate Capabilities.scalarFragment types = .ok ())
    (unused : values.lookup output.name = none)
    (accepted : appendOutput output frame = .ok next)
    (bounds : ∀ requirement ∈ next.2.1,
      ∃ value, interpret hash inputs requirement.1 = some value ∧ value.val ≤ requirement.2)
    (assertions : ∀ term ∈ next.2.2,
      interpret hash inputs term = some one) :
    ∃ normalized value,
      normalize frame.1 output.value = .ok normalized ∧
      output.value.eval ctx values = .ok value ∧
      Canonical output.ty value ∧
      interpret hash inputs normalized.term = sourceScalar? output.ty value ∧
      next.1 = (output.name, normalized.term) :: frame.1 ∧
      TypedEnvironment hash inputs next.1 values types := by
  obtain ⟨normalized, normal, aliases, normalBounds, normalAssertions⟩ :=
    appendOutput_normalize output frame next accepted
  have requirements : Requirements hash inputs normalized := by
    constructor
    · intro requirement member
      exact bounds requirement (by rw [normalBounds]; exact List.mem_append_right _ member)
    · intro term member
      exact assertions term (by rw [normalAssertions]; exact List.mem_append_right _ member)
  obtain ⟨value, evaluated, represented⟩ :=
    normalize_sound ctx hash implementation inputs types frame.1 values environment
      output.value admission normalized valid normal requirements
  refine ⟨normalized, value, normal, evaluated, represented.1, represented.2.2,
    aliases, ?_⟩
  · rw [aliases]
    exact GenericStateAliases.typedEnvironment_cons_unused hash inputs frame.1
      values types output.name normalized.term environment unused

private theorem outputFold_monotone (frame final : OutputFrame)
    (outputs : List Output)
    (accepted : outputFold frame outputs = .ok final) :
    (∀ requirement ∈ frame.2.1, requirement ∈ final.2.1) ∧
    (∀ term ∈ frame.2.2, term ∈ final.2.2) := by
  induction outputs generalizing frame with
  | nil =>
    simp [outputFold] at accepted
    cases accepted
    exact ⟨fun _ member => member, fun _ member => member⟩
  | cons output rest ih =>
    rw [outputFold_cons] at accepted
    change (appendOutput output frame >>= fun next => outputFold next rest) =
      .ok final at accepted
    simp only [bind_ok] at accepted
    rcases accepted with ⟨middle, first, later⟩
    have tail := ih middle later
    obtain ⟨normalized, _, _, boundsShape, assertionsShape⟩ :=
      appendOutput_normalize output frame middle first
    constructor
    · intro requirement member
      apply tail.1 requirement
      rw [boundsShape]
      exact List.mem_append_left _ member
    · intro term member
      apply tail.2 term
      rw [assertionsShape]
      exact List.mem_append_left _ member

private theorem outputFold_source_bindings (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (types : TypeEnv) (values : EvalEnv)
    (outputs : List Output) (frame final : OutputFrame)
    (priorValues : EvalEnv) (priorTypes : TypeEnv)
    (environment : TypedEnvironment hash inputs frame.1 values types)
    (expanded : TypedEnvironment hash inputs frame.1 priorValues priorTypes)
    (admissions : ∀ output ∈ outputs, ScalarExpression output.value)
    (valid : ∀ output ∈ outputs,
      output.value.validate Capabilities.scalarFragment types = .ok ())
    (unused : ∀ output ∈ outputs, values.lookup output.name = none)
    (accepted : outputFold frame outputs = .ok final)
    (bounds : ∀ requirement ∈ final.2.1,
      ∃ value, interpret hash inputs requirement.1 = some value ∧ value.val ≤ requirement.2)
    (assertions : ∀ term ∈ final.2.2,
      interpret hash inputs term = some one) :
    ∃ result, outputs.mapM (evalOutput ctx values) = .ok result ∧
      result.map Prod.fst = outputs.map (·.name) ∧
      TypedEnvironment hash inputs final.1 values types ∧
      TypedEnvironment hash inputs final.1 (result.reverse ++ priorValues)
        ((outputs.map (fun output => (output.name, output.ty))).reverse ++ priorTypes) := by
  induction outputs generalizing frame priorValues priorTypes with
  | nil =>
    simp [outputFold] at accepted
    cases accepted
    exact ⟨[], rfl, rfl, environment, expanded⟩
  | cons output rest ih =>
    rw [outputFold_cons] at accepted
    change (appendOutput output frame >>= fun next => outputFold next rest) =
      .ok final at accepted
    simp only [bind_ok] at accepted
    rcases accepted with ⟨middle, first, later⟩
    have monotone := outputFold_monotone middle final rest later
    have normalBounds : ∀ requirement ∈ middle.2.1,
        ∃ value, interpret hash inputs requirement.1 = some value ∧
          value.val ≤ requirement.2 := by
      intro requirement member
      apply bounds requirement
      exact monotone.1 requirement member
    have normalAssertions : ∀ term ∈ middle.2.2,
        interpret hash inputs term = some one := by
      intro term member
      exact assertions term (monotone.2 term member)
    obtain ⟨normalized, value, _, evaluated, canonical, meaning,
      aliases, nextEnvironment⟩ :=
      appendOutput_source_sound ctx hash implementation inputs types values
        output frame middle environment
        (admissions output (by simp)) (valid output (by simp)) (unused output (by simp))
        first normalBounds normalAssertions
    have nextExpanded : TypedEnvironment hash inputs middle.1
        ((output.name, Value.pack output.ty value) :: priorValues)
        ((output.name, output.ty) :: priorTypes) := by
      rw [aliases]
      exact TypedEnvironment.cons hash inputs frame.1 priorValues priorTypes
        expanded output.name output.ty value normalized.term canonical meaning
    have restAdmissions : ∀ item ∈ rest, ScalarExpression item.value := by
      intro item member
      exact admissions item (by simp [member])
    have restValid : ∀ item ∈ rest,
        item.value.validate Capabilities.scalarFragment types = .ok () := by
      intro item member
      exact valid item (by simp [member])
    have restUnused : ∀ item ∈ rest, values.lookup item.name = none := by
      intro item member
      exact unused item (by simp [member])
    obtain ⟨tail, tailEval, tailNames, finalEnvironment, finalExpanded⟩ :=
      ih middle _ _ nextEnvironment nextExpanded restAdmissions restValid restUnused later
    refine ⟨(output.name, Value.pack output.ty value) :: tail, ?_, ?_,
      finalEnvironment, ?_⟩
    · simp [evalOutput, evaluated, tailEval, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simp [tailNames]
    · simpa [List.reverse_cons, List.append_assoc] using finalExpanded

private theorem lookup_none_of_key_not_mem (items : List (String × α))
    (name : String) (absent : name ∉ items.map Prod.fst) :
    items.lookup name = none := by
  apply List.lookup_eq_none_iff.mpr
  intro pair member
  have different : name ≠ pair.1 := by
    intro equal
    apply absent
    simpa [equal] using (List.mem_map.mpr ⟨pair, member, rfl⟩ :
      pair.1 ∈ items.map Prod.fst)
  simp [different]

private theorem lookup_reverse_unique (items : List (String × α))
    (unique : (items.map Prod.fst).Nodup) (name : String) :
    items.reverse.lookup name = items.lookup name := by
  induction items with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨head, value⟩
    have distinct := List.nodup_cons.mp unique
    have noHeadReverse := lookup_none_of_key_not_mem rest.reverse head (by
      simpa [List.map_reverse, List.mem_reverse] using distinct.1)
    simp only [List.reverse_cons, List.lookup_append]
    by_cases same : name = head
    · subst name
      simp [noHeadReverse]
    · have different : (name == head) = false := by simp [same]
      simp only [List.lookup_cons, different]
      simpa using ih distinct.2

private theorem lookup_append_comm_of_disjoint (left right : List (String × α))
    (disjoint : ∀ name, left.lookup name = none ∨ right.lookup name = none)
    (name : String) :
    (left ++ right).lookup name = (right ++ left).lookup name := by
  rcases disjoint name with first | second
  · simp [List.lookup_append, first]
  · simp [List.lookup_append, second]

private theorem typedEnvironment_lookup_ext (hash : Hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (values replacement : EvalEnv)
    (types replacementTypes : TypeEnv)
    (environment : TypedEnvironment hash inputs aliases values types)
    (sameValues : ∀ name, replacement.lookup name = values.lookup name)
    (sameTypes : ∀ name, replacementTypes.lookup name = types.lookup name) :
    TypedEnvironment hash inputs aliases replacement replacementTypes := by
  constructor
  · intro name ty raw value lookup typed
    exact environment.aliases name ty raw value (by rw [← sameValues]; exact lookup) typed
  · intro name ty lookup
    obtain ⟨raw, value, old, packed⟩ :=
      environment.complete name ty (by rw [← sameTypes]; exact lookup)
    exact ⟨raw, value, by rw [sameValues]; exact old, packed⟩

private theorem typedEnvironment_output_order (hash : Hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (results values : EvalEnv)
    (outputTypes types : TypeEnv)
    (uniqueResults : (results.map Prod.fst).Nodup)
    (uniqueTypes : (outputTypes.map Prod.fst).Nodup)
    (typesFresh : ∀ name, outputTypes.lookup name = none ∨ types.lookup name = none)
    (stack : TypedEnvironment hash inputs aliases
      (results.reverse ++ values) (outputTypes.reverse ++ types)) :
    TypedEnvironment hash inputs aliases (results ++ values) (types ++ outputTypes) := by
  apply typedEnvironment_lookup_ext hash inputs aliases
    (results.reverse ++ values) (results ++ values)
    (outputTypes.reverse ++ types) (types ++ outputTypes) stack
  · intro name
    simp only [List.lookup_append]
    rw [lookup_reverse_unique results uniqueResults name]
  · intro name
    have appended := lookup_append_comm_of_disjoint outputTypes types typesFresh name
    simp only [List.lookup_append] at appended
    rw [List.lookup_append, List.lookup_append]
    rw [lookup_reverse_unique outputTypes uniqueTypes name]
    exact appended.symm

/-- The production output fold evaluates each original source expression under
the original values. Its accepted frame also supplies aliases and a typed
source-order environment for later constraints and state effects. -/
theorem normalizeOutputs_source_frame (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (seed : AliasEnvironment) (types : TypeEnv) (values : EvalEnv)
    (outputs : List Output) (frame : OutputFrame)
    (environment : TypedEnvironment hash inputs seed values types)
    (unique : (outputs.map (·.name)).Nodup)
    (admissions : ∀ output ∈ outputs, ScalarExpression output.value)
    (valid : ∀ output ∈ outputs,
      output.value.validate Capabilities.scalarFragment types = .ok ())
    (unusedValues : ∀ output ∈ outputs, values.lookup output.name = none)
    (unusedTypes : ∀ output ∈ outputs, types.lookup output.name = none)
    (accepted : normalizeOutputs seed outputs = .ok frame)
    (bounds : ∀ requirement ∈ frame.2.1,
      ∃ value, interpret hash inputs requirement.1 = some value ∧ value.val ≤ requirement.2)
    (assertions : ∀ term ∈ frame.2.2,
      interpret hash inputs term = some one) :
    ∃ result, outputs.mapM (evalOutput ctx values) = .ok result ∧
      result.map Prod.fst = outputs.map (·.name) ∧
      TypedEnvironment hash inputs frame.1 values types ∧
      TypedEnvironment hash inputs frame.1 (result ++ values)
        (types ++ outputs.map (fun output => (output.name, output.ty))) := by
  let initial : OutputFrame := (seed, [], [])
  have sourceFrame : outputFold (seed, [], []) outputs = .ok frame := by
    simpa [normalizeOutputs] using accepted
  have initialEnvironment :
      TypedEnvironment hash inputs initial.1 values types := by
    simpa [initial] using environment
  obtain ⟨result, evaluated, names, finalEnvironment, stack⟩ :=
    outputFold_source_bindings ctx hash implementation inputs types values
      outputs initial frame values types initialEnvironment initialEnvironment
      admissions valid unusedValues sourceFrame bounds assertions
  have resultUnique : (result.map Prod.fst).Nodup := by
    rw [names]
    exact unique
  let outputTypes : List (String × Ty) := outputs.map (fun output => (output.name, output.ty))
  have typeUnique : (outputTypes.map Prod.fst).Nodup := by
    change ((outputs.map (fun output => (output.name, output.ty))).map Prod.fst).Nodup
    simpa only [List.map_map, Function.comp_def] using unique
  have typeFresh : ∀ name, outputTypes.lookup name = none ∨ types.lookup name = none := by
    intro name
    cases found : outputTypes.lookup name with
    | none => exact Or.inl rfl
    | some ty =>
      obtain ⟨before, after, membership, _⟩ := List.lookup_eq_some_iff.mp found
      have pairMember : (name, ty) ∈ outputTypes := by
        rw [membership]
        simp
      change (name, ty) ∈ outputs.map (fun output => (output.name, output.ty)) at pairMember
      obtain ⟨output, member, equal⟩ := List.mem_map.mp pairMember
      cases equal
      exact Or.inr (unusedTypes output member)
  refine ⟨result, evaluated, names, finalEnvironment, ?_⟩
  exact typedEnvironment_output_order hash inputs frame.1 result values outputTypes types
    resultUnique typeUnique typeFresh stack

end Noctium.Verification.ScalarOutputFrame
