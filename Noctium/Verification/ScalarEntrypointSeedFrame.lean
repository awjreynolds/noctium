import Noctium.Verification.ScalarCircuit
import Noctium.Verification.GenericStateAliases

namespace Noctium.Verification.ScalarEntrypointSeedFrame
open Backend.Native NativeRelation ScalarNormalization GenericStateCircuitParts

def entrypointReadSeedAliases (entry : Entrypoint) (plan : Backend.Impact.Plan) :
    AliasEnvironment :=
  (plan.reads.drop (Backend.Impact.publicInputReadCount entry.circuit.inputs)).flatMap
    fun read => read.bindings.map fun (name, _) =>
      (name, Term.input ("%input_" ++ name))

private def scalarType_of_canonical {ty : Ty} {value : ty.Denote}
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

private theorem scalarInputAliasTerms (input : Input) (supported : ScalarType input.ty) :
    Input.sourceTerm input = .input ("%input_" ++ input.name) ∧
    Input.callArgumentTerm input = .input ("%input_" ++ input.name) := by
  cases input with
  | mk name ty visibility span =>
    cases supported <;> exact ⟨rfl, rfl⟩

/-- Scalar admission makes both ordinary and selected call-argument inputs use
the normalizer's raw `%input_` reference. Read aliases stay after this input
prefix, so they preserve its lookup priority. -/
theorem entrypointSeedAliases_eq (entry : Entrypoint) (plan : Backend.Impact.Plan)
    (values : EvalEnv) (witness : Assignment)
    (admitted : CanonicalInputs entry.circuit values witness) :
    entrypointSeedAliases entry plan =
      circuitAliases entry.circuit ++ entrypointReadSeedAliases entry plan := by
  unfold entrypointSeedAliases entrypointReadSeedAliases circuitAliases
  congr 1
  apply List.map_congr_left
  intro input member
  obtain ⟨value, _, canonical⟩ := admitted.complete input member
  obtain ⟨sourceTerm, callArgumentTerm⟩ :=
    scalarInputAliasTerms input (scalarType_of_canonical canonical)
  simp [sourceTerm, callArgumentTerm]

/-- Canonical source admission establishes the circuit-input typed environment
for the entrypoint seed frame. The read suffix is appended after those aliases,
so its lookup cannot replace an existing circuit-input alias. This theorem
does not assume or check any native read stream. -/
theorem entrypointSeedAliases_typedEnvironment (entry : Entrypoint)
    (plan : Backend.Impact.Plan) (hash : Hash) (values : EvalEnv)
    (witness : Assignment)
    (admitted : CanonicalInputs entry.circuit values witness) :
    TypedEnvironment hash witness (entrypointSeedAliases entry plan) values
      (entry.circuit.inputs.map fun input => (input.name, input.ty)) := by
  rw [entrypointSeedAliases_eq entry plan values witness admitted]
  exact GenericStateAliases.typedEnvironment_append_aliases hash witness
    (circuitAliases entry.circuit) (entrypointReadSeedAliases entry plan) values
    (entry.circuit.inputs.map fun input => (input.name, input.ty))
    (admitted.typedEnvironment entry.circuit values witness hash)

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem except_bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    Except.bind first next = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Except.bind]

/-- Fresh output names preserve the lookup result for an existing alias. -/
private theorem outputFold_preserves_lookup (outputs : List Output)
    (before after : OutputFrame) (name : String)
    (fresh : ∀ output ∈ outputs, name ≠ output.name)
    (accepted : outputFold before outputs = .ok after) :
    after.1.lookup name = before.1.lookup name := by
  induction outputs generalizing before with
  | nil =>
    change Except.ok before = .ok after at accepted
    cases accepted
    rfl
  | cons output rest ih =>
    rw [outputFold_cons] at accepted
    simp only [except_bind_ok] at accepted
    obtain ⟨middle, first, later⟩ := accepted
    have suffix := ih middle (fun item member => fresh item (by simp [member])) later
    rw [suffix]
    unfold appendOutput at first
    simp only [bind_ok] at first
    obtain ⟨result, _, equal⟩ := first
    cases equal
    have different : (name == output.name) = false := by
      simp [fresh output (by simp)]
    simp only [List.lookup_cons, different]

private theorem readSeedAliases_lookup (reads : List Backend.Impact.Read)
    (singleton : ∀ item ∈ reads, item.bindings = [(item.name, item.ty)])
    (read : Backend.Impact.Read) (member : read ∈ reads) :
    (reads.flatMap fun item => item.bindings.map fun (name, _) =>
      (name, Term.input ("%input_" ++ name))).lookup read.name =
        some (.input ("%input_" ++ read.name)) := by
  induction reads with
  | nil => cases member
  | cons head rest ih =>
    have headSingleton := singleton head (by simp)
    have restSingleton : ∀ item ∈ rest, item.bindings = [(item.name, item.ty)] := by
      intro item present
      exact singleton item (List.mem_cons_of_mem _ present)
    have headAliases : head.bindings.map (fun (name, _) =>
        (name, Term.input ("%input_" ++ name))) =
        [(head.name, Term.input ("%input_" ++ head.name))] := by
      rw [headSingleton]
      rfl
    simp only [List.flatMap_cons, headAliases]
    by_cases same : read.name = head.name
    · simp [same]
    · have different : (read.name == head.name) = false := by simp [same]
      have tailMember : read ∈ rest := by
        rcases List.mem_cons.mp member with equal | present
        · exact False.elim (same (congrArg Backend.Impact.Read.name equal))
        · exact present
      simpa [List.lookup_cons, different] using ih restSingleton tailMember

/-- The normalized output frame retains each plain post-public read as its raw
native input alias. Canonical input aliases come first, singleton read aliases
follow them, and fresh output aliases cannot replace either lookup. -/
theorem normalized_read_lookup (entry : Entrypoint) (plan : Backend.Impact.Plan)
    (frame : OutputFrame) (values : EvalEnv) (witness : Assignment)
    (admitted : CanonicalInputs entry.circuit values witness)
    (normalized : normalizeOutputs (entrypointSeedAliases entry plan)
      entry.circuit.outputs = .ok frame)
    (suffixSingleton : ∀ read ∈
      (plan.reads.drop (Backend.Impact.publicInputReadCount entry.circuit.inputs)),
      read.bindings = [(read.name, read.ty)])
    (suffixFresh : ∀ read ∈
      (plan.reads.drop (Backend.Impact.publicInputReadCount entry.circuit.inputs)),
      read.name ∉ entry.circuit.inputs.map (·.name) ++ entry.circuit.outputs.map (·.name)) :
    ∀ read ∈ (plan.reads.drop
      (Backend.Impact.publicInputReadCount entry.circuit.inputs)),
      frame.1.lookup read.name = some (.input ("%input_" ++ read.name)) := by
  let reads := plan.reads.drop (Backend.Impact.publicInputReadCount entry.circuit.inputs)
  intro read member
  have inputAbsent : (circuitAliases entry.circuit).lookup read.name = none := by
    apply List.lookup_eq_none_iff.mpr
    intro pair pairMember
    obtain ⟨input, inputMember, pairEqual⟩ := List.mem_map.mp pairMember
    have pairName : input.name = pair.1 := congrArg Prod.fst pairEqual
    have different : read.name ≠ pair.1 := by
      intro same
      have targetName : read.name = input.name := same.trans pairName.symm
      exact suffixFresh read member (List.mem_append_left _
        (List.mem_map.mpr ⟨input, inputMember, targetName.symm⟩))
    simp [different]
  have seedLookup : (entrypointSeedAliases entry plan).lookup read.name =
      some (.input ("%input_" ++ read.name)) := by
    rw [entrypointSeedAliases_eq entry plan values witness admitted]
    simp only [List.lookup_append, inputAbsent, Option.none_or]
    exact readSeedAliases_lookup reads suffixSingleton read member
  have foldAccepted : outputFold (entrypointSeedAliases entry plan, [], [])
      entry.circuit.outputs = .ok frame := by
    simpa only [normalizeOutputs] using normalized
  have outputFresh : ∀ output ∈ entry.circuit.outputs, read.name ≠ output.name := by
    intro output outputMember equal
    exact suffixFresh read member
      (List.mem_append_right _
        (List.mem_map.mpr ⟨output, outputMember, equal.symm⟩))
  have unchanged := outputFold_preserves_lookup entry.circuit.outputs
    (entrypointSeedAliases entry plan, [], []) frame read.name outputFresh foldAccepted
  rw [unchanged]
  exact seedLookup

end Noctium.Verification.ScalarEntrypointSeedFrame
