import Noctium.Verification.ScalarNormalizationSoundness
import Noctium.Backend.NativeProducer
import Noctium.Backend.Impact
import Noctium.Verification.GenericStateAliases

namespace Noctium.Verification.GenericStateInputValues
open NativeRelation ScalarNormalization Backend.Native

/-- Source types with scalar encodings in the native relation. -/
def scalarType? : (ty : Ty) → Option (ScalarType ty)
  | .native => some .native
  | .bool => some .bool
  | .uint maximum => some (.uint maximum)
  | .bytes _ | .opaqueBytes | .opaqueString | .jubjubScalar | .jubjubPoint | .foreign _ => none

theorem scalarType?_supported {ty : Ty} (support : ScalarType ty) :
    scalarType? ty = some support := by
  cases support <;> rfl

/-- Decode a relation scalar only when its source type has a scalar witness. -/
def sourceValue {ty : Ty} : ScalarType ty → Scalar → ty.Denote
  | .native, number => number.val
  | .bool, number => number.val == 1
  | .uint _, number => number.val

theorem sourceValue_canonical {ty : Ty} (supported : ScalarType ty) (input : Scalar)
    (typed : ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (bounded : input.val ≤ sourceMaximum ty) :
    Canonical ty (sourceValue supported input) ∧
      sourceScalar? ty (sourceValue supported input) = some input := by
  cases supported with
  | native =>
    constructor
    · exact ⟨input.isLt, trivial⟩
    · have scalarEq : scalar input.val = input := by
        apply Fin.ext
        exact scalar_no_wrap _ input.isLt
      simpa [sourceScalar?, sourceNumber?, sourceValue] using congrArg some scalarEq

  | bool =>
    rcases input with ⟨number, fieldBound⟩
    have valueZeroOrOne : number = 0 ∨ number = 1 := by
      simpa [sourceMaximum] using (Nat.le_one_iff_eq_zero_or_eq_one.mp bounded)
    rcases valueZeroOrOne with zero | one
    · subst number
      constructor
      · simp [Canonical, sourceValue, ScalarNormalization.number, Field.modulus]
      · simp [sourceScalar?, sourceNumber?, sourceValue, zero, Field.modulus]
    · subst number
      constructor
      · simp [Canonical, sourceValue, ScalarNormalization.number, Field.modulus]
      · simp [sourceScalar?, sourceNumber?, sourceValue, one, Field.modulus]
  | uint maximum =>
    have maximumBound : maximum ≤ ScalarPolicy.maxUint := by
      by_cases limit : maximum ≤ ScalarPolicy.maxUint
      · exact limit
      · have fail : ScalarPolicy.validate (.uint maximum) =
            .error "unsigned type exceeds target maximum" := by
          simp [ScalarPolicy.validate, limit]
        change (do
          let _ ← ScalarPolicy.validate (.uint maximum)
          if maximum < Field.modulus then pure ()
          else throw "unsigned type exceeds native representation") = .ok () at typed
        rw [fail] at typed
        cases typed
    constructor
    · exact ⟨input.isLt, maximumBound, by simpa [sourceValue, sourceMaximum] using bounded⟩
    · have scalarEq : scalar input.val = input := by
        apply Fin.ext
        exact scalar_no_wrap _ input.isLt
      simpa [sourceScalar?, sourceNumber?, sourceValue] using congrArg some scalarEq

/-- Candidate typed ledger-read values supplied by the satisfying relation
witness. Checked VM reads must authenticate these candidates before source
effects use them. -/
def decodeRead (read : Backend.Impact.Read) (witness : Assignment) :
    Except String (String × Value) :=
  match scalarType? read.ty with
  | none => .error "unsupported non-scalar read type"
  | some supported => .ok
      (read.name, Value.pack read.ty
        (sourceValue supported (witness ("%input_" ++ read.name))))

/-- Decode read values in production order, failing on the first unsupported type. -/
def decodeReads (reads : List Backend.Impact.Read) (witness : Assignment) : Except String EvalEnv :=
  reads.mapM (fun read => decodeRead read witness)

/-- Read decoding observes only the named inputs of these descriptors, in order. -/
theorem decodeReads_agree_on (reads : List Backend.Impact.Read) (before after : Assignment)
    (agree : ∀ descriptor ∈ reads,
      after ("%input_" ++ descriptor.name) = before ("%input_" ++ descriptor.name)) :
    decodeReads reads after = decodeReads reads before := by
  unfold decodeReads
  induction reads with
  | nil => rfl
  | cons read rest ih =>
    have sameRead : decodeRead read after = decodeRead read before := by
      simp only [decodeRead, agree read (List.mem_cons_self ..)]
    have sameRest := ih (fun descriptor present => agree descriptor (List.mem_cons_of_mem _ present))
    simp only [List.mapM_cons, sameRead, sameRest]

/-- Decoded reads are unchanged when an assignment preserves every `%input_`
binding. The equality covers both successful decoding and the first error. -/
theorem decodeReads_input_frame (reads : List Backend.Impact.Read)
    (before after : Assignment)
    (frame : ∀ name, after ("%input_" ++ name) = before ("%input_" ++ name)) :
    decodeReads reads after = decodeReads reads before :=
  decodeReads_agree_on reads before after (fun descriptor _ => frame descriptor.name)

theorem decodeRead_success (read : Backend.Impact.Read) (witness : Assignment)
    (entry : String × Value) (success : decodeRead read witness = .ok entry) :
    ∃ supported : ScalarType read.ty,
      entry = (read.name, Value.pack read.ty
        (sourceValue supported (witness ("%input_" ++ read.name)))) := by
  cases supportEq : scalarType? read.ty with
  | none => simp [decodeRead, supportEq] at success
  | some scalarType =>
    simp [decodeRead, supportEq] at success
    cases success
    exact ⟨scalarType, rfl⟩

theorem decodeReads_cons_success (read : Backend.Impact.Read)
    (rest : List Backend.Impact.Read) (witness : Assignment) (values : EvalEnv)
    (success : decodeReads (read :: rest) witness = .ok values) :
    ∃ first tail, decodeRead read witness = .ok first ∧
      decodeReads rest witness = .ok tail ∧ values = first :: tail := by
  change List.mapM (fun item => decodeRead item witness) (read :: rest) =
    .ok values at success
  simp only [List.mapM_cons] at success
  cases firstSuccess : decodeRead read witness with
  | error message =>
    simp [firstSuccess, Bind.bind, Except.bind, Except.map, Functor.map, bind,
      pure, Except.pure] at success
  | ok first =>
    cases tailSuccess : List.mapM (fun item => decodeRead item witness) rest with
    | error message =>
      simp [firstSuccess, tailSuccess, Bind.bind, Except.bind, Except.map,
        Functor.map, bind, pure, Except.pure] at success
    | ok tail =>
      simp [firstSuccess, tailSuccess, Bind.bind, Except.bind, Except.map,
        Functor.map, bind, pure, Except.pure] at success
      cases success
      exact ⟨first, tail, rfl, tailSuccess, rfl⟩

def readAliases (reads : List Backend.Impact.Read) : Backend.Native.AliasEnvironment :=
  reads.map fun read => (read.name, .input ("%input_" ++ read.name))

def readTypes (reads : List Backend.Impact.Read) : TypeEnv :=
  reads.map fun read => (read.name, read.ty)

theorem initialAliases_readAliases (entry : Entrypoint)
    (plan : Backend.Impact.Plan) :
    GenericStateCircuitParts.initialAliases entry plan =
      circuitAliases entry.circuit ++
      readAliases (plan.reads.drop
        ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)) := by
  simpa only [readAliases] using GenericStateAliases.initialAliases_eq entry plan

/-- Decoding one existing descriptor supplies exactly its typed binding. -/
theorem decodeReads_singleton_success (read : Backend.Impact.Read) (witness : Assignment)
    (values : EvalEnv) (success : decodeReads [read] witness = .ok values) :
    ∃ supported : ScalarType read.ty,
      values = [(read.name, Value.pack read.ty
        (sourceValue supported (witness ("%input_" ++ read.name))))] := by
  obtain ⟨first, tail, headDecoded, tailDecoded, environment⟩ :=
    decodeReads_cons_success read [] witness values success
  have empty : tail = [] := by
    change Except.ok [] = .ok tail at tailDecoded
    exact (Except.ok.inj tailDecoded).symm
  obtain ⟨support, firstValue⟩ := decodeRead_success read witness first headDecoded
  exact ⟨support, by rw [environment, firstValue, empty]⟩

theorem decodeReads_lookup (reads : List Backend.Impact.Read)
    (witness : Assignment) (values : EvalEnv)
    (success : decodeReads reads witness = .ok values)
    (distinct : reads.Pairwise (fun left right => left.name ≠ right.name))
    (read : Backend.Impact.Read) (member : read ∈ reads) :
    ∃ supported : ScalarType read.ty,
      values.lookup read.name =
        some (Value.pack read.ty
          (sourceValue supported (witness ("%input_" ++ read.name)))) := by
  induction reads generalizing values with
  | nil => cases member
  | cons head tail ih =>
    simp only [List.pairwise_cons] at distinct
    obtain ⟨first, tailValues, firstSuccess, tailSuccess, valuesEq⟩ :=
      decodeReads_cons_success head tail witness values success
    rcases List.mem_cons.mp member with same | later
    · subst read
      obtain ⟨supported, firstEq⟩ := decodeRead_success head witness first firstSuccess
      refine ⟨supported, ?_⟩
      rw [valuesEq, firstEq]
      simp
    · have different : read.name ≠ head.name :=
        (distinct.1 read later).symm
      obtain ⟨_, firstEq⟩ := decodeRead_success head witness first firstSuccess
      obtain ⟨supported, tailLookup⟩ := ih tailValues tailSuccess distinct.2 later
      refine ⟨supported, ?_⟩
      rw [valuesEq, firstEq]
      have unequal : (read.name == head.name) = false := by simp [different]
      simp only [List.lookup_cons, unequal]
      exact tailLookup

private theorem decodeReads_supported (reads : List Backend.Impact.Read)
    (witness : Assignment) (values : EvalEnv)
    (success : decodeReads reads witness = .ok values) :
    ∀ read ∈ reads, Nonempty (ScalarType read.ty) := by
  induction reads generalizing values with
  | nil =>
    intro read member
    cases member
  | cons head rest ih =>
    obtain ⟨first, tail, firstSuccess, tailSuccess, _⟩ :=
      decodeReads_cons_success head rest witness values success
    intro read member
    rcases List.mem_cons.mp member with same | later
    · subst read
      obtain ⟨supported, _⟩ := decodeRead_success head witness first firstSuccess
      exact ⟨supported⟩
    · exact ih tail tailSuccess read later

theorem decodeReads_canonical (reads : List Backend.Impact.Read)
    (witness : Assignment) (values : EvalEnv)
    (success : decodeReads reads witness = .ok values)
    (typed : ∀ read ∈ reads,
      read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (bounded : ∀ read ∈ reads,
      (witness ("%input_" ++ read.name)).val ≤ sourceMaximum read.ty) :
    ∀ read ∈ reads,
      ∃ supported : ScalarType read.ty,
        Canonical read.ty (sourceValue supported
          (witness ("%input_" ++ read.name))) ∧
        sourceScalar? read.ty (sourceValue supported
          (witness ("%input_" ++ read.name))) =
          some (witness ("%input_" ++ read.name)) := by
  intro read member
  obtain ⟨supported⟩ := decodeReads_supported reads witness values success read member
  obtain ⟨canonical, meaning⟩ := sourceValue_canonical supported
    (witness ("%input_" ++ read.name)) (typed read member) (bounded read member)
  exact ⟨supported, canonical, meaning⟩

/-- Relation input bounds plus source type validation build a typed alias
environment for all candidate ledger reads. Native transcript checks still
need to authenticate each candidate against the current state slot. -/
theorem decodedReads_typedEnvironment (reads : List Backend.Impact.Read)
    (hash : Hash) (witness : Assignment) (values : EvalEnv)
    (success : decodeReads reads witness = .ok values)
    (typed : ∀ read ∈ reads,
      read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (bounded : ∀ read ∈ reads,
      (witness ("%input_" ++ read.name)).val ≤ sourceMaximum read.ty) :
    TypedEnvironment hash witness (readAliases reads)
      values (readTypes reads) := by
  induction reads generalizing values with
  | nil =>
    simp [decodeReads] at success
    cases success
    constructor
    · intro name ty raw value lookup _
      simp at lookup
    · intro name ty lookup
      simp [readTypes] at lookup
  | cons read rest ih =>
    obtain ⟨first, tailValues, firstSuccess, tailSuccess, valuesEq⟩ :=
      decodeReads_cons_success read rest witness values success
    have restTyped : ∀ item ∈ rest,
        item.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok () := by
      intro item member
      exact typed item (by simp [member])
    have restBounded : ∀ item ∈ rest,
        (witness ("%input_" ++ item.name)).val ≤ sourceMaximum item.ty := by
      intro item member
      exact bounded item (by simp [member])
    have previous := ih tailValues tailSuccess restTyped restBounded
    obtain ⟨supported, firstEq⟩ := decodeRead_success read witness first firstSuccess
    cases firstEq
    obtain ⟨canonical, meaning⟩ := sourceValue_canonical supported
      (witness ("%input_" ++ read.name)) (typed read (by simp)) (bounded read (by simp))
    rw [valuesEq]
    change TypedEnvironment hash witness
      ((read.name, .input ("%input_" ++ read.name)) :: readAliases rest)
      ((read.name, Value.pack read.ty
        (sourceValue supported (witness ("%input_" ++ read.name)))) :: tailValues)
      ((read.name, read.ty) :: readTypes rest)
    apply TypedEnvironment.cons hash witness (readAliases rest)
      tailValues (readTypes rest) previous
      read.name read.ty (sourceValue supported (witness ("%input_" ++ read.name)))
      (.input ("%input_" ++ read.name)) canonical
    simpa only [interpret_input] using meaning.symm

end Noctium.Verification.GenericStateInputValues
