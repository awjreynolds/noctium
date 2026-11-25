import Noctium.Backend.Zkir
import Noctium.Verification.ScalarWitnessCircuitInputs

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarLowering ScalarNormalization
open ScalarInstructionEncoding ScalarWitness

/-- A plain ledger read has no flattened components and no activity guard.
Its source type is separately constrained to Native, Bool, or UInt by the
`ScalarType` evidence used by the completion theorem. -/
def PlainScalarLedgerRead (read : Impact.Read) : Prop :=
  read.components = [] ∧ read.guard = none

theorem PlainScalarLedgerRead.bindings (read : Impact.Read)
    (plain : PlainScalarLedgerRead read) (scalarType : ScalarType read.ty) :
    read.bindings = [(read.name, read.ty)] := by
  rcases read with ⟨name, ty, components, schema, guard, rootCellRead⟩
  have flat : components = [] := plain.1
  subst components
  cases scalarType <;> rfl

private def ledgerReadEmit (name : String) : StateM Zkir.LowerState Unit :=
  Zkir.emit "public_input"
    [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)),
      ("output", toJson ("%input_" ++ name))]

private def ledgerReadBody (name : String) (ty : Ty) : StateM Zkir.LowerState Unit := do
  ledgerReadEmit name
  Zkir.constrainType ty ("%input_" ++ name)

private theorem lowerLedgerRead_plain_eq (read : Impact.Read)
    (plain : PlainScalarLedgerRead read) (scalarType : ScalarType read.ty) :
    Zkir.lowerLedgerRead read = ledgerReadBody read.name read.ty := by
  rcases read with ⟨name, ty, components, schema, guard, rootCellRead⟩
  rcases plain with ⟨componentsEmpty, unguarded⟩
  change components = [] at componentsEmpty
  change guard = none at unguarded
  subst components
  subst guard
  cases scalarType <;> rfl

private theorem no_plain_read_defaults (read : Impact.Read)
    (plain : PlainScalarLedgerRead read) (scalarType : ScalarType read.ty) :
    read.inactiveDefaultConstraints = [] := by
  rcases read with ⟨name, ty, components, schema, guard, rootCellRead⟩
  rcases plain with ⟨componentsEmpty, unguarded⟩
  change components = [] at componentsEmpty
  change guard = none at unguarded
  subst components
  subst guard
  cases scalarType <;> rfl

private theorem lowerLedgerRead_plain_frame (read : Impact.Read)
    (plain : PlainScalarLedgerRead read) (scalarType : ScalarType read.ty) :
    Zkir.PreservesOutputCapacityFrame (Zkir.lowerLedgerRead read) := by
  apply Zkir.lowerLedgerRead_preservesOutputCapacityFrame read
  · intro scalarRead member guard selected
    have scalarReadEq : scalarRead = read := by
      have member' : scalarRead ∈ [read] := by
        simpa [Impact.Read.scalarReads, plain.1] using member
      exact List.mem_singleton.mp member'
    subst scalarRead
    rw [plain.2] at selected
    cases selected
  · intro condition member
    rw [no_plain_read_defaults read plain scalarType] at member
    simp at member

/-- The exact plain-read lowering emits the source-seeded public input and
then applies its type constraint. Source canonicality supplies the bound
checked for Bool and UInt inputs. -/
theorem completes_lowerLedgerRead_plain (hash : Hash) (inputs : NativeRelation.Assignment)
    (read : Impact.Read) (value : read.ty.Denote) (scalarType : ScalarType read.ty)
    (plain : PlainScalarLedgerRead read) (canonical : Canonical read.ty value)
    (binding : inputs ("%input_" ++ read.name) = scalar (number scalarType value))
    (identifier : validIdentifier ("%input_" ++ read.name) = true) :
    Completes hash inputs (Zkir.lowerLedgerRead read) (fun _ => True) := by
  let input : Input := ⟨read.name, read.ty, .public, {}⟩
  have publicVisibility : (Visibility.public == Visibility.public) = true := by decide
  have emitted : Completes hash inputs (ledgerReadEmit read.name) (fun _ => True) := by
    simpa [ledgerReadEmit, input, publicVisibility] using
      (completes_emit_input hash inputs input identifier :
        Completes hash inputs
          (Zkir.emit (if input.visibility == .«public» then "public_input" else "private_input")
            [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)),
              ("output", toJson ("%input_" ++ input.name))]) (fun _ => True))
  have constrained : Completes hash inputs
      (Zkir.constrainType read.ty ("%input_" ++ read.name)) (fun _ => True) :=
    completes_scalar_constraint hash inputs read.name value scalarType canonical binding
      identifier (aliasRequirement := fun _ => True)
  have operation : Completes hash inputs (ledgerReadBody read.name read.ty) (fun _ => True) := by
    simpa [ledgerReadBody] using
      (completes_bind hash inputs (ledgerReadEmit read.name)
        (fun _ => Zkir.constrainType read.ty ("%input_" ++ read.name))
        (Zkir.emit_preservesOutputCapacityFrame _ _)
        (fun _ => Zkir.constrainType_preservesOutputCapacityFrame _ _)
        emitted (fun _ => constrained) :
        Completes hash inputs
          (ledgerReadEmit read.name >>= fun _ =>
            Zkir.constrainType read.ty ("%input_" ++ read.name)) (fun _ => True))
  rw [lowerLedgerRead_plain_eq read plain scalarType]
  exact operation

/-- Complete post-public plain Native, Bool, and UInt ledger reads from the
seeded assignment. Each read must have canonical source evidence and a valid
`%input_` identifier. The loop preserves any aliases installed before ledger
reads begin. -/
theorem completes_lowerLedgerReads_plain (hash : Hash) (inputs : NativeRelation.Assignment)
    (entry : Entrypoint) (plan : Impact.Plan)
    (plain : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      PlainScalarLedgerRead read)
    (facts : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      ∃ (value : read.ty.Denote) (scalarType : ScalarType read.ty),
        Canonical read.ty value ∧
        inputs ("%input_" ++ read.name) = scalar (number scalarType value))
    (identifiers : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      validIdentifier ("%input_" ++ read.name) = true) :
    Completes hash inputs (Zkir.lowerLedgerReads entry plan) (fun _ => True) := by
  let reads := plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)
  let body : Impact.Read → StateM Zkir.LowerState Unit := Zkir.lowerLedgerRead
  have frames : ∀ read ∈ reads, Zkir.PreservesOutputCapacityFrame (body read) := by
    intro read member
    obtain ⟨value, scalarType, canonical, binding⟩ := facts read member
    simpa only [body] using lowerLedgerRead_plain_frame read (plain read member) scalarType
  have construction : ∀ read ∈ reads,
      Completes hash inputs (body read) (fun _ => True) := by
    intro read member
    obtain ⟨value, scalarType, canonical, binding⟩ := facts read member
    simpa only [body] using completes_lowerLedgerRead_plain hash inputs read value scalarType
      (plain read member) canonical binding (identifiers read member)
  have loop : Completes hash inputs
      (forIn reads () (fun read _ => do body read; pure (.yield ()))) (fun _ => True) :=
    completes_forIn hash inputs reads () body frames
      (aliasRequirement := fun _ => True) construction
  have loweringEq : Zkir.lowerLedgerReads entry plan =
      forIn reads () (fun read _ => do body read; pure (.yield ())) := by
    simp [Zkir.lowerLedgerReads, reads, body]
  rw [loweringEq]
  exact loop

/-- Extend the source environment with plain ledger reads. Earlier bindings
keep precedence. Both lowerers resolve new read names to the input frame. -/
theorem LowerAliasAgreement.appendReadValues (hash : Hash)
    (inputs witness : NativeRelation.Assignment)
    (normalAliases : Native.AliasEnvironment) (lowerAliases : List (String × String))
    (values readValues : EvalEnv)
    (agreement : LowerAliasAgreement hash inputs witness normalAliases lowerAliases values)
    (reads : ∀ pair ∈ readValues,
      normalAliases.lookup pair.1 = some (.input ("%input_" ++ pair.1)) ∧
      lowerAliases.lookup pair.1 = none ∧ validIdentifier ("%input_" ++ pair.1) = true)
    (frame : InputFrame inputs witness) :
    LowerAliasAgreement hash inputs witness normalAliases lowerAliases (values ++ readValues) := by
  intro name ty raw value lookup typed
  rw [List.lookup_append] at lookup
  cases found : values.lookup name with
  | some first =>
    simp only [found, Option.some_or] at lookup
    exact agreement name ty raw value (found.trans lookup) typed
  | none =>
    simp only [found, Option.none_or] at lookup
    obtain ⟨before, after, eq, _⟩ := List.lookup_eq_some_iff.mp lookup
    have member : (name, raw) ∈ readValues := by rw [eq]; simp
    obtain ⟨normalized, absent, valid⟩ := reads (name, raw) member
    refine ⟨.input ("%input_" ++ name), normalized, ?_⟩
    simpa [absent] using OperandMeaning.reference hash inputs witness _ valid
      (.input ("%input_" ++ name)) (by simpa only [interpret_input, Option.some.injEq] using (frame name).symm)

end Noctium.Verification.ScalarWitnessConstruction
