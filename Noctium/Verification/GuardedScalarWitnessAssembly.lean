import Noctium.Verification.GuardedScalarRows
import Noctium.Verification.GuardedPublicInputMeaning
import Noctium.Verification.ScalarWitness

namespace Noctium.Verification.GuardedScalarWitnessAssembly

open Lean NativeRelation NativeRelationJson GuardedScalarRows ScalarWitness

private def inputOutput : Row → Option String
  | .strict (.input _ output) => some output
  | .publicInput output _ => some output
  | _ => none

def inputOutputs (rows : List Row) : List String :=
  rows.filterMap inputOutput

private def instructionReferences : Instruction → List String
  | .input _ _ => []
  | .boolean value | .bits value _ | .neg value _ | .not value _ | .assert value =>
      operandIdentifiers value
  | .lessThan left right _ _ | .add left right _ | .mul left right _
  | .equal left right | .testEq left right _ =>
      operandIdentifiers left ++ operandIdentifiers right
  | .select condition yes no _ =>
      operandIdentifiers condition ++ operandIdentifiers yes ++ operandIdentifiers no
  | .hash values _ | .output values => values.flatMap operandIdentifiers
  | .impact guard values => operandIdentifiers guard ++ values.flatMap operandIdentifiers

private def isCopy (raw : Json) : Bool :=
  match stringField raw "op" with
  | .ok "copy" => true
  | _ => false

private def rowReferences (raw : Json) : Row → List String
  | .strict (.equal source (.reference destination)) =>
      if isCopy raw then operandIdentifiers source
      else operandIdentifiers source ++ [destination]
  | .strict instruction => instructionReferences instruction
  | .publicInput _ guard => guard.toList.flatMap operandIdentifiers
  | .impact guard inputs => operandIdentifiers guard ++ inputs.flatMap operandIdentifiers

/-- A decoded Copy is represented as equality by the native relation decoder.
Only its exact raw opcode makes the destination a witness definition. -/
private def definitionValue (hash : Hash) (raw : Json) (witness : Assignment) :
    Row → Option (String × Scalar)
  | .strict (.equal source (.reference destination)) =>
      if isCopy raw then
        some (destination, source.read witness)
      else none
  | .strict (.lessThan left right _ destination) =>
      some (destination, bit (decide ((left.read witness).val < (right.read witness).val)))
  | .strict (.add left right destination) =>
      some (destination, scalar ((left.read witness).val + (right.read witness).val))
  | .strict (.mul left right destination) =>
      some (destination, scalar ((left.read witness).val * (right.read witness).val))
  | .strict (.neg value destination) =>
      some (destination, scalar (Field.modulus - (value.read witness).val))
  | .strict (.testEq left right destination) =>
      some (destination, bit (decide (left.read witness = right.read witness)))
  | .strict (.not value destination) =>
      some (destination, if value.read witness = zero then one else zero)
  | .strict (.select condition yes no destination) =>
      some (destination, if condition.read witness = one then yes.read witness else no.read witness)
  | .strict (.hash values destination) =>
      some (destination, hash (values.map (·.read witness)))
  | _ => none

/-- Only the actual row operands determine its defined value. A copy input
uses its source, and a constrain-equality row defines no value. -/
private theorem definitionValue_agrees {hash : Hash} {raw : Json} {row : Row}
    {left right : Assignment}
    (agree : ∀ name ∈ rowReferences raw row, left name = right name) :
    definitionValue hash raw left row = definitionValue hash raw right row := by
  cases row with
  | publicInput => rfl
  | impact => rfl
  | strict instruction =>
    cases instruction <;> try rfl
    case equal source target =>
      cases target with
      | immediate => rfl
      | reference destination =>
        by_cases copy : isCopy raw
        · have references : rowReferences raw (.strict (.equal source (.reference destination))) =
              operandIdentifiers source := by simp [rowReferences, copy]
          rw [references] at agree
          simp [definitionValue, copy, Operand.read_agrees source agree]
        · simp [definitionValue, copy]
    case hash inputs output =>
      have values := operands_read_agree inputs (left := left) (right := right) (by
        intro name present
        apply agree
        simpa [rowReferences, instructionReferences] using present)
      simp [definitionValue, values]
    all_goals
      simp [definitionValue, rowReferences, instructionReferences] at agree ⊢
      simp (disch := (intro name used; apply agree; simp_all [List.mem_flatMap]))
        only [Operand.read_agrees (left := left) (right := right)]

/-- A defining row agrees with a satisfying producer witness. The comparison
equation needs the producer's established operand widths. -/
private theorem definitionValue_holds {hash : Hash} {raw : Json} {row : Row}
    {witness : Assignment} {destination : String} {value : Scalar}
    (defined : definitionValue hash raw witness row = some (destination, value))
    (holds : ∀ instruction, row = .strict instruction →
      Instruction.Holds hash witness instruction)
    (lessThanBounds : ∀ left right width output,
      row = .strict (.lessThan left right width output) →
        (left.read witness).val < 2 ^ width ∧ (right.read witness).val < 2 ^ width) :
    witness destination = value := by
  cases row with
  | publicInput => simp [definitionValue] at defined
  | impact => simp [definitionValue] at defined
  | strict instruction =>
    have satisfied := holds instruction rfl
    cases instruction <;> try solve
      | simp [definitionValue] at defined
        rcases defined with ⟨rfl, rfl⟩
        first | exact satisfied | exact satisfied.2
      | cases defined
    case lessThan left right width output =>
      obtain ⟨leftBound, rightBound⟩ := lessThanBounds left right width output rfl
      simp [definitionValue] at defined
      rcases defined with ⟨rfl, rfl⟩
      exact satisfied leftBound rightBound
    case equal left right =>
      cases right with
      | immediate => cases defined
      | reference name =>
        by_cases copy : isCopy raw
        · simp [definitionValue, copy] at defined
          rcases defined with ⟨rfl, rfl⟩
          exact satisfied.symm
        · simp [definitionValue, copy] at defined

private def rowDestination (raw : Json) (row : Row) : Option String :=
  (definitionValue (fun _ => zero) raw (fun _ => zero) row).map Prod.fst

private theorem definition_destination (hash : Hash) (witness : Assignment)
    (raw : Json) (row : Row) :
    (definitionValue hash raw witness row).map Prod.fst = rowDestination raw row := by
  cases row with
  | publicInput => rfl
  | impact => rfl
  | strict instruction =>
    cases instruction <;> try rfl
    case equal source target =>
      cases target with
      | immediate => rfl
      | reference => simp only [rowDestination, definitionValue]; split <;> rfl

/-- Input lanes already belong to the initial scope. Ordinary destinations
enter scope in emitted SSA order, after their row's operands. -/
inductive Scope : List String → List Json → List Row → List String → Prop where
  | nil (registered) : Scope registered [] [] registered
  | cons {registered raw row rawTail rowTail finalNames}
      (references : ∀ name ∈ rowReferences raw row, name ∈ registered)
      (fresh : ∀ destination ∈ (rowDestination raw row).toList,
        destination ∉ registered ∧ destination.startsWith "%input_" = false)
      (tail : Scope ((rowDestination raw row).toList ++ registered) rawTail rowTail finalNames) :
      Scope registered (raw :: rawTail) (row :: rowTail) finalNames

theorem Scope.initial_subset {registered rawRows rows finalNames}
    (scope : Scope registered rawRows rows finalNames) :
    ∀ name ∈ registered, name ∈ finalNames := by
  induction scope with
  | nil => exact fun _ present => present
  | cons _ _ _ ih =>
    intro name present
    exact ih name (List.mem_append_right _ present)

private theorem instruction_identifiers_scoped (raw : Json) (instruction : Instruction) :
    ∀ name ∈ instructionIdentifiers instruction,
      name ∈ rowReferences raw (.strict instruction) ∨
      name ∈ (rowDestination raw (.strict instruction)).toList ∨
      name ∈ (inputOutput (.strict instruction)).toList := by
  intro name present
  cases instruction <;>
    try solve
      | simpa [rowReferences, instructionReferences, rowDestination, definitionValue,
          instructionIdentifiers, inputOutput, or_assoc] using present
  case equal source target =>
    cases target <;> by_cases copy : isCopy raw <;>
      simpa [rowReferences, instructionReferences, rowDestination, definitionValue,
        instructionIdentifiers, inputOutput, operandIdentifiers, copy, or_assoc] using present

private theorem Scope.row_identifiers {registered rawRows rows finalNames}
    (scope : Scope registered rawRows rows finalNames)
    (inputsRegistered : ∀ name ∈ inputOutputs rows, name ∈ registered) :
    ∀ row ∈ rows, ∃ raw, ∀ name,
      (name ∈ rowReferences raw row ∨ name ∈ (rowDestination raw row).toList ∨
        name ∈ (inputOutput row).toList) → name ∈ finalNames := by
  induction scope with
  | nil => simp
  | @cons registered raw row rawTail rowTail finalNames refs _ tail ih =>
    intro found present
    rcases List.mem_cons.mp present with same | later
    · subst found
      refine ⟨raw, fun name used => ?_⟩
      rcases used with ref | dest | input
      · exact tail.initial_subset name (List.mem_append_right _ (refs name ref))
      · exact tail.initial_subset name (List.mem_append_left _ dest)
      · have inputMem : name ∈ inputOutputs (row :: rowTail) := by
          cases checked : inputOutput row with
          | none => simp [checked] at input
          | some lane =>
            have same : name = lane := by simpa [checked] using input
            subst name
            simp [inputOutputs, checked]
        exact tail.initial_subset name (List.mem_append_right _ (inputsRegistered name inputMem))
    · apply ih _ found later
      intro input presentInput
      apply List.mem_append_right
      apply inputsRegistered
      exact List.mem_filterMap.mpr (by
        obtain ⟨inputRow, present, value⟩ := List.mem_filterMap.mp presentInput
        exact ⟨inputRow, List.mem_cons_of_mem _ present, value⟩)

private theorem Scope.strict_identifiers {registered rawRows rows finalNames}
    (scope : Scope registered rawRows rows finalNames)
    (inputsRegistered : ∀ name ∈ inputOutputs rows, name ∈ registered)
    (instruction : Instruction) (present : .strict instruction ∈ rows) :
    ∀ name ∈ instructionIdentifiers instruction, name ∈ finalNames := by
  obtain ⟨raw, included⟩ := scope.row_identifiers inputsRegistered (.strict instruction) present
  intro name used
  exact included name (instruction_identifiers_scoped raw instruction name used)

/-- Scope covers the assignments read by guarded activity and public input
observation. The pre-registered input outputs remain in the final scope. -/
theorem Scope.transcript_identifiers {arguments rawRows rows finalNames}
    (scope : Scope (arguments ++ inputOutputs rows) rawRows rows finalNames) :
    ∀ row ∈ rows, ∀ name ∈ row.transcriptIdentifiers, name ∈ finalNames := by
  intro row present name used
  obtain ⟨raw, included⟩ := scope.row_identifiers
    (fun name lane => List.mem_append_right _ lane) row present
  apply included
  cases row <;> simp_all [Row.transcriptIdentifiers, rowReferences, inputOutput]
  exact used.elim (fun same => .inr (.inr same)) .inl

private theorem inputOutputs_cons (row : Row) (rows : List Row) :
    inputOutputs (row :: rows) = (inputOutput row).toList ++ inputOutputs rows := by
  cases found : inputOutput row <;> simp [inputOutputs, found]

private theorem destination_not_input (raw : Json) (row : Row) {name : String}
    (destination : name ∈ (rowDestination raw row).toList) :
    name ∉ (inputOutput row).toList := by
  cases row with
  | publicInput => simp [rowDestination, definitionValue] at destination
  | impact => simp [inputOutput]
  | strict instruction =>
    cases instruction <;> simp_all [rowDestination, definitionValue, inputOutput]

/-- The producer registers each input or temporary at its own emitted row.
The generated-temporary namespace is checked separately from the producer's
sequential name validation. -/
inductive ProducerScope : List String → List Json → List Row → Prop where
  | nil (known) : ProducerScope known [] []
  | cons {known raw row rawTail rowTail}
      (references : ∀ name ∈ rowReferences raw row, name ∈ known)
      (fresh : ∀ name ∈ (inputOutput row).toList ++ (rowDestination raw row).toList,
        name ∉ known)
      (temporary : ∀ destination ∈ (rowDestination raw row).toList,
        destination.startsWith "%input_" = false)
      (tail : ProducerScope (known ++ (inputOutput row).toList ++ (rowDestination raw row).toList)
        rawTail rowTail) :
      ProducerScope known (raw :: rawTail) (row :: rowTail)

private theorem ProducerScope.future_inputs_fresh {known rawRows rows}
    (scope : ProducerScope known rawRows rows) :
    ∀ name ∈ inputOutputs rows, name ∉ known := by
  induction scope with
  | nil => simp [inputOutputs]
  | @cons known raw row rawTail rowTail _ fresh _ _ ih =>
    intro name present
    rw [inputOutputs_cons] at present
    rcases List.mem_append.mp present with head | later
    · exact fresh name (List.mem_append_left _ head)
    · intro used
      exact ih name later (List.mem_append_left _ (List.mem_append_left _ used))

private theorem ProducerScope.future_inputs_nodup {known rawRows rows}
    (scope : ProducerScope known rawRows rows) : (inputOutputs rows).Nodup := by
  induction scope with
  | nil => simp [inputOutputs]
  | @cons known raw row rawTail rowTail _ _ _ tail ih =>
    rw [inputOutputs_cons]
    cases found : inputOutput row with
    | none => exact ih
    | some lane =>
      apply List.nodup_cons.mpr
      refine ⟨?_, ih⟩
      intro present
      have current : lane ∈ (known ++ (inputOutput row).toList ++ (rowDestination raw row).toList) := by
        simp [found]
      exact tail.future_inputs_fresh lane present current

/-- Producer input validation rules out collisions in the eager seed, even
though the assembler pre-registers input rows before processing them. -/
theorem ProducerScope.input_lanes_nodup {arguments rawRows rows}
    (scope : ProducerScope arguments rawRows rows) (distinct : arguments.Nodup) :
    (arguments ++ inputOutputs rows).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨distinct, scope.future_inputs_nodup, ?_⟩
  intro name used other later same
  subst other
  exact scope.future_inputs_fresh name later used

private theorem ProducerScope.assemble_scope_from {known rawRows rows}
    (producer : ProducerScope known rawRows rows) (registered : List String)
    (names : ∀ name, name ∈ registered ↔ name ∈ known ++ inputOutputs rows) :
    ∃ finalNames, Scope registered rawRows rows finalNames := by
  induction producer generalizing registered with
  | nil => exact ⟨registered, .nil registered⟩
  | @cons known raw row rawTail rowTail references fresh temporary tail ih =>
    have tailNames : ∀ name,
        name ∈ (rowDestination raw row).toList ++ registered ↔
        name ∈ (known ++ (inputOutput row).toList ++ (rowDestination raw row).toList) ++
          inputOutputs rowTail := by
      intro name
      simp [names, inputOutputs_cons, or_assoc, or_left_comm, or_comm]
    obtain ⟨finalNames, rest⟩ := ih _ tailNames
    refine ⟨finalNames, .cons (fun name used => (names name).mpr
      (List.mem_append_left _ (references name used))) ?_ rest⟩
    intro destination defined
    refine ⟨?_, temporary destination defined⟩
    intro already
    have registeredBefore := (names destination).mp already
    rcases List.mem_append.mp registeredBefore with before | input
    · exact fresh destination (List.mem_append_right _ defined) before
    · rw [inputOutputs_cons] at input
      rcases List.mem_append.mp input with atRow | later
      · exact destination_not_input raw row defined atRow
      · exact tail.future_inputs_fresh destination later (List.mem_append_right _ defined)

/-- Ledger input lanes are available to the assembler at the start, although
the producer validated them only at their rows. Sequential freshness ensures
none of these future lanes collides with a temporary. -/
theorem ProducerScope.assemble_scope {arguments rawRows rows}
    (producer : ProducerScope arguments rawRows rows) :
    ∃ finalNames, Scope (arguments ++ inputOutputs rows) rawRows rows finalNames :=
  producer.assemble_scope_from _ (fun _ => Iff.rfl)

private theorem argument_identifiers {state : Backend.Native.State} {raw : Json}
    {field : String} {value : Operand} {fact : Backend.Native.Fact}
    (accepted : Backend.Native.argument state raw field = .ok fact)
    (decoded : decodeOperandField raw field = .ok value) :
    ∀ name ∈ operandIdentifiers value, name ∈ state.definitions.map Prod.fst := by
  intro name used
  cases value with
  | immediate _ => simp [operandIdentifiers] at used
  | reference ref =>
    have same : name = ref := by simpa [operandIdentifiers] using used
    subst name
    unfold Backend.Native.argument Backend.Native.stringField at accepted
    unfold decodeOperandField at decoded
    simp only [ScalarValidationMeaning.bind_ok] at accepted decoded
    obtain ⟨text, ⟨json, parsed, textParsed⟩, operand⟩ := accepted
    obtain ⟨actual, actualParsed, decode⟩ := decoded
    have sameJson := Except.ok.inj (actualParsed.symm.trans parsed)
    subst actual
    have found := ScalarValidationMeaning.operand_decoded_reference_lookup textParsed operand decode
    exact List.mem_map_of_mem (ScalarValidationMeaning.lookup_member found)

private theorem absent_from_definition_names {state : Backend.Native.State} {name : String}
    (missing : state.definitions.lookup name = none) :
    name ∉ state.definitions.map Prod.fst := by
  intro present
  obtain ⟨pair, member, named⟩ := List.mem_map.mp present
  have absent := (List.lookup_eq_none_iff.mp missing) pair member
  simp [named] at absent

private theorem defineResult_names {state next : Backend.Native.State} {raw : Json}
    {destination : String} {fact : Backend.Native.Fact}
    (outputField : Backend.Native.stringField raw "output" = .ok destination)
    (defined : Backend.Native.defineResult state raw fact = .ok next) :
    next.definitions.map Prod.fst = state.definitions.map Prod.fst ++ [destination] ∧
      destination ∉ state.definitions.map Prod.fst := by
  have accepted : Backend.Native.define state destination fact = .ok next := by
    simpa [Backend.Native.defineResult, outputField, Bind.bind, Except.bind] using defined
  obtain ⟨appended, missing⟩ := ScalarValidationMeaning.define_appended_and_missing accepted
  exact ⟨by simp [appended], absent_from_definition_names missing⟩

/-- A validated copy introduces its actual raw output name and reads only its
validated source operand. Its decoded equality records the assigned value. -/
theorem ProducerScope.cons_validated_copy {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json} {source : Operand} {destination : String}
    {rawRows : List Json} {rows : List Row}
    (nativeDefinitions : ScalarValidationArithmeticLoop.NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "copy")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : decodeRow raw = .ok (.strict (.equal source (.reference destination))))
    (temporary : destination.startsWith "%input_" = false)
    (tail : ProducerScope (next.definitions.map Prod.fst) rawRows rows) :
    ProducerScope (state.definitions.map Prod.fst)
      (raw :: rawRows) (.strict (.equal source (.reference destination)) :: rows) := by
  have instruction := (decodeRow_strict decoded).1.decoded
  obtain ⟨parsedSource, destinationField⟩ := decodeInstruction_copyOperandFields
    (by simpa [ScalarValidationMeaning.nativeJson_stringField_eq] using opcode) instruction
  obtain ⟨fact, sourceAccepted, _, outputDefined⟩ :=
    ScalarValidationArithmeticLoop.accepted_copy_components nativeDefinitions opcode accepted
  have nameFrame := defineResult_names destinationField outputDefined
  have copy : isCopy raw = true := by
    simp [isCopy, ScalarValidationMeaning.nativeJson_stringField_eq, opcode]
  apply ProducerScope.cons
  · simpa only [rowReferences, copy, ite_true] using argument_identifiers sourceAccepted parsedSource
  · simpa [inputOutput, rowDestination, definitionValue, copy] using nameFrame.2
  · simpa [rowDestination, definitionValue, copy] using temporary
  · simpa [inputOutput, rowDestination, definitionValue, copy, nameFrame.1] using tail

private theorem ProducerScope.cons_binary_definition
    {state next : Backend.Native.State} {raw : Json} {row : Row} {left right : Operand}
    {destination : String} {leftFact rightFact fact : Backend.Native.Fact}
    {rawRows : List Json} {rows : List Row}
    (references : rowReferences raw row = operandIdentifiers left ++ operandIdentifiers right)
    (definedName : rowDestination raw row = some destination)
    (input : inputOutput row = none)
    (leftField : decodeOperandField raw "a" = .ok left)
    (rightField : decodeOperandField raw "b" = .ok right)
    (destinationField : Backend.Native.stringField raw "output" = .ok destination)
    (leftAccepted : Backend.Native.argument state raw "a" = .ok leftFact)
    (rightAccepted : Backend.Native.argument state raw "b" = .ok rightFact)
    (defined : Backend.Native.defineResult state raw fact = .ok next)
    (temporary : destination.startsWith "%input_" = false)
    (tail : ProducerScope (next.definitions.map Prod.fst) rawRows rows) :
    ProducerScope (state.definitions.map Prod.fst) (raw :: rawRows) (row :: rows) := by
  obtain ⟨names, absent⟩ := defineResult_names destinationField defined
  apply ProducerScope.cons
  · intro name used
    rw [references] at used
    exact (List.mem_append.mp used).elim (argument_identifiers leftAccepted leftField name)
      (argument_identifiers rightAccepted rightField name)
  · simpa [input, definedName] using absent
  · simpa [definedName] using temporary
  · simpa [input, definedName, names] using tail

theorem ProducerScope.cons_validated_add {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json} {left right : Operand} {destination : String}
    {rawRows : List Json} {rows : List Row}
    (nativeDefinitions : ScalarValidationArithmeticLoop.NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "add")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : decodeRow raw = .ok (.strict (.add left right destination)))
    (temporary : destination.startsWith "%input_" = false)
    (tail : ProducerScope (next.definitions.map Prod.fst) rawRows rows) :
    ProducerScope (state.definitions.map Prod.fst) (raw :: rawRows)
      (.strict (.add left right destination) :: rows) := by
  obtain ⟨leftField, rightField, destinationField⟩ :=
    ScalarValidationMeaning.decoded_add_arguments opcode (decodeRow_strict decoded).1.decoded
  obtain ⟨_, _, _, leftAccepted, rightAccepted, _, _, _, defined⟩ :=
    ScalarValidationArithmeticLoop.accepted_add_components nativeDefinitions opcode accepted
  exact ProducerScope.cons_binary_definition rfl rfl rfl leftField rightField destinationField
    leftAccepted rightAccepted defined temporary tail

theorem ProducerScope.cons_validated_mul {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json} {left right : Operand} {destination : String}
    {rawRows : List Json} {rows : List Row}
    (nativeDefinitions : ScalarValidationArithmeticLoop.NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "mul")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : decodeRow raw = .ok (.strict (.mul left right destination)))
    (temporary : destination.startsWith "%input_" = false)
    (tail : ProducerScope (next.definitions.map Prod.fst) rawRows rows) :
    ProducerScope (state.definitions.map Prod.fst) (raw :: rawRows)
      (.strict (.mul left right destination) :: rows) := by
  obtain ⟨leftField, rightField, destinationField⟩ :=
    ScalarValidationMeaning.decoded_mul_arguments opcode (decodeRow_strict decoded).1.decoded
  obtain ⟨_, _, _, leftAccepted, rightAccepted, _, _, _, defined⟩ :=
    ScalarValidationArithmeticLoop.accepted_mul_components nativeDefinitions opcode accepted
  exact ProducerScope.cons_binary_definition rfl rfl rfl leftField rightField destinationField
    leftAccepted rightAccepted defined temporary tail

private theorem refine_names {state next : Backend.Native.State} {operand : String}
    {maximum : Nat} (accepted : Backend.Native.refine state operand maximum = .ok next) :
    next.definitions.map Prod.fst = state.definitions.map Prod.fst := by
  unfold Backend.Native.refine at accepted
  simp only [ScalarValidationMeaning.bind_ok] at accepted
  obtain ⟨_, _, _, _, remainder⟩ := accepted
  split at remainder
  · cases remainder
    simp [List.map_map, Function.comp_def]
  · obtain ⟨_, _, same⟩ := ScalarValidationMeaning.bind_ok.mp remainder
    cases same
    rfl

/-- A validated constrain-equality reads both operands and only tightens
existing facts. The same decoded equality form therefore introduces no SSA
destination on this raw opcode. -/
theorem ProducerScope.cons_validated_constrain_eq {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json} {left right : Operand}
    {rawRows : List Json} {rows : List Row}
    (nativeDefinitions : ScalarValidationArithmeticLoop.NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "constrain_eq")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : decodeRow raw = .ok (.strict (.equal left right)))
    (tail : ProducerScope (next.definitions.map Prod.fst) rawRows rows) :
    ProducerScope (state.definitions.map Prod.fst) (raw :: rawRows)
      (.strict (.equal left right) :: rows) := by
  have instruction := (decodeRow_strict decoded).1.decoded
  obtain ⟨decodedLeft, decodedRight⟩ :=
    ScalarValidationMeaning.decodedConstrainEqOperands opcode instruction
  unfold Backend.Native.validateInstruction at accepted
  simp only [ScalarValidationMeaning.bind_ok] at accepted
  obtain ⟨found, actual, _, _, _, _, result⟩ := accepted
  have sameOp : found = "constrain_eq" := Except.ok.inj (actual.symm.trans opcode)
  subst found
  simp only [ScalarValidationMeaning.bind_ok] at result
  obtain ⟨leftText, leftTextParsed, rightText, rightTextParsed,
    leftFact, leftParsed, rightFact, rightParsed, _, _, remainder⟩ := result
  have acceptedLeft : Backend.Native.argument state raw "a" = .ok leftFact := by
    unfold Backend.Native.argument
    rw [leftTextParsed]
    exact leftParsed
  have acceptedRight : Backend.Native.argument state raw "b" = .ok rightFact := by
    unfold Backend.Native.argument
    rw [rightTextParsed]
    exact rightParsed
  have leftNative := ScalarValidationArithmeticLoop.argument_native_of_state
    nativeDefinitions acceptedLeft
  simp only [leftNative, Backend.Native.ensure, Bind.bind, Except.bind] at remainder
  obtain ⟨_, leftRefined, rest⟩ := ScalarValidationMeaning.bind_ok.mp remainder
  obtain ⟨_, rightRefined, final⟩ := ScalarValidationMeaning.bind_ok.mp rest
  have finalState := Except.ok.inj final
  subst next
  have names := (refine_names rightRefined).trans (refine_names leftRefined)
  have copy : isCopy raw = false := by
    simp [isCopy, ScalarValidationMeaning.nativeJson_stringField_eq, opcode]
  have noneDestination : rowDestination raw (.strict (.equal left right)) = none := by
    cases right <;> simp [rowDestination, definitionValue, copy]
  apply ProducerScope.cons
  · intro name used
    have either : name ∈ operandIdentifiers left ++ operandIdentifiers right := by
      cases right <;> simpa [rowReferences, instructionReferences, copy, operandIdentifiers] using used
    exact (List.mem_append.mp either).elim
      (argument_identifiers acceptedLeft decodedLeft name)
      (argument_identifiers acceptedRight decodedRight name)
  · simp [inputOutput, noneDestination]
  · simp [noneDestination]
  · simpa [inputOutput, noneDestination, names] using tail

theorem ProducerScope.cons_validated_impact {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json} {guard : Operand} {values : List Operand}
    {rawRows : List Json} {rows : List Row}
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : decodeRow raw = .ok (.impact guard values))
    (tail : ProducerScope (next.definitions.map Prod.fst) rawRows rows) :
    ProducerScope (state.definitions.map Prod.fst)
      (raw :: rawRows) (.impact guard values :: rows) := by
  obtain ⟨opcode, decodedGuard, decodedPayload⟩ := decodeRow_impact_fields decoded
  obtain ⟨references, sameDefinitions⟩ :=
    ScalarValidationOutputMeaning.accepted_impact_operand_definitions accepted
      opcode decodedGuard decodedPayload
  apply ProducerScope.cons
  · exact references
  · simp [inputOutput, rowDestination, definitionValue]
  · simp [rowDestination, definitionValue]
  · simpa [inputOutput, rowDestination, definitionValue, sameDefinitions] using tail

theorem ProducerScope.cons_validated_output {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json} {values : List Operand}
    {rawRows : List Json} {rows : List Row}
    (opcode : Backend.Native.stringField raw "op" = .ok "output")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : decodeRow raw = .ok (.strict (.output values)))
    (tail : ProducerScope (next.definitions.map Prod.fst) rawRows rows) :
    ProducerScope (state.definitions.map Prod.fst)
      (raw :: rawRows) (.strict (.output values) :: rows) := by
  obtain ⟨same, references⟩ :=
    ScalarValidationOutputMeaning.accepted_output_operand_definitions accepted opcode
      (decodeRow_strict decoded).1.decoded
  subst next
  apply ProducerScope.cons
  · exact references
  · simp [inputOutput, rowDestination, definitionValue]
  · simp [rowDestination, definitionValue]
  · simpa [inputOutput, rowDestination, definitionValue] using tail

theorem ProducerScope.cons_validated_publicInput {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json} {output : String} {guard : Option Operand}
    {rawRows : List Json} {rows : List Row}
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : decodeRow raw = .ok (.publicInput output guard))
    (tail : ProducerScope (next.definitions.map Prod.fst) rawRows rows) :
    ProducerScope (state.definitions.map Prod.fst)
      (raw :: rawRows) (.publicInput output guard :: rows) := by
  obtain ⟨references, absent, appended⟩ :=
    GuardedPublicInputMeaning.accepted_publicInput_ssa_footprint inputSchema decoded accepted
  apply ProducerScope.cons
  · intro name used
    obtain ⟨fact, lookup⟩ := references name used
    exact List.mem_map_of_mem (ScalarValidationMeaning.lookup_member lookup)
  · simpa [inputOutput, rowDestination, definitionValue] using absent_from_definition_names absent
  · simp [rowDestination, definitionValue]
  · simpa [inputOutput, rowDestination, definitionValue, appended] using tail

theorem ProducerScope.cons_validated_privateInput {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json} {output : String}
    {rawRows : List Json} {rows : List Row}
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (opcode : Backend.Native.stringField raw "op" = .ok "private_input")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : decodeRow raw = .ok (.strict (.input .private output)))
    (tail : ProducerScope (next.definitions.map Prod.fst) rawRows rows) :
    ProducerScope (state.definitions.map Prod.fst)
      (raw :: rawRows) (.strict (.input .private output) :: rows) := by
  obtain ⟨requirement, selected⟩ :=
    ScalarValidationNativeLoop.accepted_input_requirement_selected (visibility := .private)
      opcode accepted
  have scalarInput := inputSchema requirement (List.mem_of_getElem? selected)
  have guard := ScalarValidationNativeLoop.accepted_private_input_unguarded selected opcode accepted
  have outputField := NativeInputOrdinal.strict_decoded_input_output_identifier
    (visibility := .private) opcode (decodeRow_strict decoded).1.decoded
  have defined : next.definitions.map Prod.fst = state.definitions.map Prod.fst ++ [output] ∧
      output ∉ state.definitions.map Prod.fst := by
    unfold Backend.Native.validateInstruction at accepted
    simp only [ScalarValidationMeaning.bind_ok] at accepted
    obtain ⟨found, foundOpcode, _, _, _, _, body⟩ := accepted
    have same := Except.ok.inj (foundOpcode.symm.trans opcode)
    subst found
    simp only [selected] at body
    split at body
    · simp_all [Ty.isForeign]
    · simp only [guard, ScalarValidationMeaning.bind_ok] at body
      obtain ⟨_, _, _, _, kind, kindParsed, _, _, _, _, name, nameField, _, _,
        definedState, added, result⟩ := body
      cases kindParsed
      have sameName := Except.ok.inj (nameField.symm.trans outputField)
      subst name
      obtain ⟨appended, missing⟩ := ScalarValidationMeaning.define_appended_and_missing added
      cases result
      exact ⟨by simp [appended], absent_from_definition_names missing⟩
  apply ProducerScope.cons
  · simp [rowReferences, instructionReferences]
  · simpa [inputOutput, rowDestination, definitionValue] using defined.2
  · simp [rowDestination, definitionValue]
  · simpa [inputOutput, rowDestination, definitionValue, defined.1] using tail

private theorem decoded_testEq_arguments {raw : Json} {left right : Operand} {output : String}
    (opcode : Backend.Native.stringField raw "op" = .ok "test_eq")
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.testEq left right output)) :
    NativeRelationJson.decodeOperandField raw "a" = .ok left ∧
      NativeRelationJson.decodeOperandField raw "b" = .ok right ∧
      Backend.Native.stringField raw "output" = .ok output := by
  unfold NativeRelationJson.decodeInstruction at decoded
  simp only [ScalarValidationMeaning.bind_ok,
    ScalarValidationMeaning.nativeJson_stringField_eq] at decoded
  rcases decoded with ⟨opcodeName, opcodeParsed, body⟩
  have opcodeEq : opcodeName = "test_eq" :=
    Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp only [ScalarValidationMeaning.bind_ok] at body
  rcases body with ⟨_, _, leftName, leftParsed, rightName, rightParsed,
    outputName, outputParsed, _, _, result⟩
  simp only [Pure.pure, Except.pure] at result
  have resultEq := Except.ok.inj result
  injection resultEq with leftEq rightEq outputEq
  subst left right output
  exact ⟨leftParsed, rightParsed, outputParsed⟩

theorem ProducerScope.cons_validated_neg {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json} {value : Operand} {destination : String}
    {rawRows : List Json} {rows : List Row}
    (nativeDefinitions : ScalarValidationArithmeticLoop.NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "neg")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : decodeRow raw = .ok (.strict (.neg value destination)))
    (temporary : destination.startsWith "%input_" = false)
    (tail : ProducerScope (next.definitions.map Prod.fst) rawRows rows) :
    ProducerScope (state.definitions.map Prod.fst) (raw :: rawRows)
      (.strict (.neg value destination) :: rows) := by
  obtain ⟨valueField, destinationField⟩ :=
    ScalarValidationMeaning.decoded_neg_argument opcode (decodeRow_strict decoded).1.decoded
  obtain ⟨_, fact, valueAccepted, _, _, defined⟩ :=
    ScalarValidationArithmeticLoop.accepted_neg_components nativeDefinitions opcode accepted
  obtain ⟨names, absent⟩ := defineResult_names destinationField defined
  apply ProducerScope.cons
  · intro name used
    have present : name ∈ operandIdentifiers value := by
      simpa [rowReferences, instructionReferences] using used
    exact argument_identifiers valueAccepted valueField name present
  · simpa [inputOutput, rowDestination, definitionValue] using absent
  · simpa [rowDestination, definitionValue] using temporary
  · simpa [inputOutput, rowDestination, definitionValue, names] using tail

theorem ProducerScope.cons_validated_not {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json} {value : Operand} {destination : String}
    {rawRows : List Json} {rows : List Row}
    (nativeDefinitions : ScalarValidationArithmeticLoop.NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "not")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : decodeRow raw = .ok (.strict (.not value destination)))
    (temporary : destination.startsWith "%input_" = false)
    (tail : ProducerScope (next.definitions.map Prod.fst) rawRows rows) :
    ProducerScope (state.definitions.map Prod.fst) (raw :: rawRows)
      (.strict (.not value destination) :: rows) := by
  obtain ⟨valueField, destinationField⟩ :=
    ScalarValidationMeaning.decoded_not_argument opcode (decodeRow_strict decoded).1.decoded
  obtain ⟨_, fact, valueAccepted, _, _, _, defined⟩ :=
    ScalarValidationArithmeticLoop.accepted_not_components nativeDefinitions opcode accepted
  obtain ⟨names, absent⟩ := defineResult_names destinationField defined
  apply ProducerScope.cons
  · intro name used
    have present : name ∈ operandIdentifiers value := by
      simpa [rowReferences, instructionReferences] using used
    exact argument_identifiers valueAccepted valueField name present
  · simpa [inputOutput, rowDestination, definitionValue] using absent
  · simpa [rowDestination, definitionValue] using temporary
  · simpa [inputOutput, rowDestination, definitionValue, names] using tail

theorem ProducerScope.cons_validated_testEq {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json} {left right : Operand}
    {destination : String} {rawRows : List Json} {rows : List Row}
    (nativeDefinitions : ScalarValidationArithmeticLoop.NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "test_eq")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : decodeRow raw = .ok (.strict (.testEq left right destination)))
    (temporary : destination.startsWith "%input_" = false)
    (tail : ProducerScope (next.definitions.map Prod.fst) rawRows rows) :
    ProducerScope (state.definitions.map Prod.fst) (raw :: rawRows)
      (.strict (.testEq left right destination) :: rows) := by
  obtain ⟨leftField, rightField, destinationField⟩ :=
    decoded_testEq_arguments opcode (decodeRow_strict decoded).1.decoded
  obtain ⟨_, _, _, leftAccepted, rightAccepted, _, _, _, defined⟩ :=
    ScalarValidationArithmeticLoop.accepted_testEq_components nativeDefinitions opcode accepted
  exact ProducerScope.cons_binary_definition rfl rfl rfl leftField rightField destinationField
    leftAccepted rightAccepted defined temporary tail

theorem ProducerScope.cons_validated_select {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json} {condition yes no : Operand}
    {destination : String} {rawRows : List Json} {rows : List Row}
    (nativeDefinitions : ScalarValidationArithmeticLoop.NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "cond_select")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : decodeRow raw = .ok (.strict (.select condition yes no destination)))
    (temporary : destination.startsWith "%input_" = false)
    (tail : ProducerScope (next.definitions.map Prod.fst) rawRows rows) :
    ProducerScope (state.definitions.map Prod.fst) (raw :: rawRows)
      (.strict (.select condition yes no destination) :: rows) := by
  obtain ⟨conditionField, yesField, noField, destinationField⟩ :=
    ScalarValidationMeaning.decoded_select_arguments opcode (decodeRow_strict decoded).1.decoded
  obtain ⟨_, _, _, _, conditionAccepted, yesAccepted, noAccepted,
    _, _, _, _, _, defined⟩ :=
    ScalarValidationArithmeticLoop.accepted_native_select_components
      nativeDefinitions opcode accepted
  obtain ⟨names, absent⟩ := defineResult_names destinationField defined
  apply ProducerScope.cons
  · intro name used
    have present : name ∈ operandIdentifiers condition ++
        operandIdentifiers yes ++ operandIdentifiers no := by
      simpa [rowReferences, instructionReferences] using used
    rcases List.mem_append.mp present with conditionOrYes | noPresent
    · rcases List.mem_append.mp conditionOrYes with conditionPresent | yesPresent
      · exact argument_identifiers conditionAccepted conditionField name conditionPresent
      · exact argument_identifiers yesAccepted yesField name yesPresent
    · exact argument_identifiers noAccepted noField name noPresent
  · simpa [inputOutput, rowDestination, definitionValue] using absent
  · simpa [rowDestination, definitionValue] using temporary
  · simpa [inputOutput, rowDestination, definitionValue, names] using tail

private theorem guarded_row_nativeDefinitions {expected : Backend.Native.Expected}
    {raw : Json} {row : Row} {state next : Backend.Native.State}
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (typed : ScalarValidationArithmeticLoop.NativeDefinitions state)
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : decodeRow raw = .ok row) :
    ScalarValidationArithmeticLoop.NativeDefinitions next := by
  cases row with
  | strict instruction =>
    exact ScalarValidationNativeDefinitions.nativeDefinitions_step inputSchema typed
      (decodeRow_strict decoded).1 accepted
  | impact guard values =>
    rw [ScalarValidationNativeDefinitions.accepted_impact_state
      (decodeRow_impact_fields decoded).1 accepted]
    exact typed
  | publicInput output guard =>
    have appended :=
      (GuardedPublicInputMeaning.accepted_publicInput_ssa_footprint inputSchema decoded accepted).2.2
    intro name fact present
    rw [appended] at present
    rcases List.mem_append.mp present with prior | added
    · exact typed name fact prior
    · have same := List.mem_singleton.mp added
      cases same
      rfl

/-- Defining non-input rows use a separate temporary namespace. Producer
freshness alone does not distinguish temporary names from unused seed names. -/
def TemporaryNamespace (items : List Json) (rows : List Row) : Prop :=
  ∀ pair ∈ items.zip rows, ∀ destination ∈ (rowDestination pair.1 pair.2).toList,
    destination.startsWith "%input_" = false

private theorem decodedBooleanField {raw : Json} {value : Operand}
    (opcode : Backend.Native.stringField raw "op" = .ok "constrain_to_boolean")
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.boolean value)) :
    decodeOperandField raw "val" = .ok value := by
  simp [NativeRelationJson.decodeInstruction,
    ScalarValidationMeaning.nativeJson_stringField_eq, opcode,
    ScalarValidationMeaning.bind_ok, ScalarValidationOutputMeaning.map_ok] at decoded
  rcases decoded with ⟨_, valueParsed⟩
  exact valueParsed

private theorem decodedBitsFields {raw : Json} {value : Operand} {bits : Nat}
    (opcode : Backend.Native.stringField raw "op" = .ok "constrain_bits")
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.bits value bits)) :
    decodeOperandField raw "val" = .ok value ∧
      NativeRelationJson.naturalField raw "bits" = .ok bits := by
  simp [NativeRelationJson.decodeInstruction,
    ScalarValidationMeaning.nativeJson_stringField_eq, opcode,
    ScalarValidationMeaning.bind_ok, ScalarValidationOutputMeaning.map_ok] at decoded
  rcases decoded with ⟨_, foundBits, bitsParsed, _, foundValue, valueParsed, result⟩
  rcases result with ⟨valueEq, bitsEq⟩
  cases valueEq
  cases bitsEq
  exact ⟨valueParsed, bitsParsed⟩

private theorem decodedAssertCondition {raw : Json} {condition : Operand}
    (opcode : Backend.Native.stringField raw "op" = .ok "assert")
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.assert condition)) :
    decodeOperandField raw "cond" = .ok condition := by
  unfold NativeRelationJson.decodeInstruction at decoded
  simp only [ScalarValidationMeaning.bind_ok,
    ScalarValidationMeaning.nativeJson_stringField_eq] at decoded
  rcases decoded with ⟨opcodeName, opcodeParsed, body⟩
  have opcodeEq : opcodeName = "assert" := Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp only [ScalarValidationMeaning.bind_ok] at body
  rcases body with ⟨_, _, foundCondition, result⟩
  rcases result with ⟨conditionParsed, result⟩
  simp only [Pure.pure, Except.pure] at result
  have resultEq : Instruction.assert foundCondition = Instruction.assert condition :=
    Except.ok.inj result
  injection resultEq with conditionEq
  subst condition
  exact conditionParsed

private theorem decodeRow_boolean_fields {raw : Json} {value : Operand}
    (decoded : decodeRow raw = .ok (.strict (.boolean value))) :
    Backend.Native.stringField raw "op" = .ok "constrain_to_boolean" ∧
      decodeOperandField raw "val" = .ok value := by
  obtain ⟨supported, instructionDecoded⟩ := (decodeRow_strict decoded).1
  cases supported with
  | boolean _ opcode => exact ⟨opcode, decodedBooleanField opcode instructionDecoded⟩

private theorem decodeRow_bits_fields {raw : Json} {value : Operand} {bits : Nat}
    (decoded : decodeRow raw = .ok (.strict (.bits value bits))) :
    Backend.Native.stringField raw "op" = .ok "constrain_bits" ∧
      decodeOperandField raw "val" = .ok value ∧
      NativeRelationJson.naturalField raw "bits" = .ok bits := by
  obtain ⟨supported, instructionDecoded⟩ := (decodeRow_strict decoded).1
  cases supported with
  | bits _ _ opcode =>
    obtain ⟨valueParsed, bitsParsed⟩ := decodedBitsFields opcode instructionDecoded
    exact ⟨opcode, valueParsed, bitsParsed⟩

private theorem decodeRow_assert_fields {raw : Json} {condition : Operand}
    (decoded : decodeRow raw = .ok (.strict (.assert condition))) :
    Backend.Native.stringField raw "op" = .ok "assert" ∧
      decodeOperandField raw "cond" = .ok condition := by
  obtain ⟨supported, instructionDecoded⟩ := (decodeRow_strict decoded).1
  cases supported with
  | assertion _ opcode => exact ⟨opcode, decodedAssertCondition opcode instructionDecoded⟩

private theorem refine_argument {state next : Backend.Native.State} {raw : Json}
    {text : String} {maximum : Nat}
    (textParsed : Backend.Native.stringField raw "val" = .ok text)
    (accepted : Backend.Native.refine state text maximum = .ok next) :
    ∃ fact, Backend.Native.argument state raw "val" = .ok fact := by
  unfold Backend.Native.refine at accepted
  simp only [ScalarValidationMeaning.bind_ok] at accepted
  obtain ⟨fact, operandAccepted, _⟩ := accepted
  refine ⟨fact, ?_⟩
  unfold Backend.Native.argument
  rw [textParsed]
  exact operandAccepted

theorem ProducerScope.cons_validated_boolean {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json} {value : Operand}
    {rawRows : List Json} {rows : List Row}
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : decodeRow raw = .ok (.strict (.boolean value)))
    (tail : ProducerScope (next.definitions.map Prod.fst) rawRows rows) :
    ProducerScope (state.definitions.map Prod.fst) (raw :: rawRows)
      (.strict (.boolean value) :: rows) := by
  obtain ⟨opcode, decodedValue⟩ := decodeRow_boolean_fields decoded
  unfold Backend.Native.validateInstruction at accepted
  simp only [ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨found, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq := Except.ok.inj (op.symm.trans opcode)
  subst found
  simp only [ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨text, textParsed, refined⟩
  obtain ⟨_, valueAccepted⟩ := refine_argument textParsed refined
  have names := refine_names refined
  apply ProducerScope.cons
  · simpa [rowReferences, instructionReferences] using
      argument_identifiers valueAccepted decodedValue
  · simp [inputOutput, rowDestination, definitionValue]
  · simp [rowDestination, definitionValue]
  · simpa [inputOutput, rowDestination, definitionValue, names] using tail

theorem ProducerScope.cons_validated_bits {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json} {value : Operand} {bits : Nat}
    {rawRows : List Json} {rows : List Row}
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : decodeRow raw = .ok (.strict (.bits value bits)))
    (tail : ProducerScope (next.definitions.map Prod.fst) rawRows rows) :
    ProducerScope (state.definitions.map Prod.fst) (raw :: rawRows)
      (.strict (.bits value bits) :: rows) := by
  obtain ⟨opcode, decodedValue, decodedBits⟩ := decodeRow_bits_fields decoded
  unfold Backend.Native.validateInstruction at accepted
  simp only [ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨found, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq := Except.ok.inj (op.symm.trans opcode)
  subst found
  simp only [ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨text, textParsed, accepted⟩
  rcases accepted with ⟨producerBits, producerBitsParsed, refined⟩
  have widthAgreement := ScalarParserAgreement.natField_naturalField_agree raw "bits"
    producerBits bits (by
      unfold Backend.Native.width at producerBitsParsed
      simp only [ScalarValidationMeaning.bind_ok] at producerBitsParsed
      rcases producerBitsParsed with ⟨foundBits, fieldParsed, _, equal⟩
      have same : foundBits = producerBits := Except.ok.inj equal.2
      rw [← same]
      exact fieldParsed) decodedBits
  have producerBitsEq : producerBits = bits := widthAgreement
  rw [producerBitsEq] at refined
  have valueTextParsed : Backend.Native.stringField raw "val" = .ok text := textParsed
  obtain ⟨_, valueAccepted⟩ := refine_argument valueTextParsed refined
  have names := refine_names refined
  apply ProducerScope.cons
  · simpa [rowReferences, instructionReferences] using
      argument_identifiers valueAccepted decodedValue
  · simp [inputOutput, rowDestination, definitionValue]
  · simp [rowDestination, definitionValue]
  · simpa [inputOutput, rowDestination, definitionValue, names] using tail

theorem ProducerScope.cons_validated_assert {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json} {condition : Operand}
    {rawRows : List Json} {rows : List Row}
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : decodeRow raw = .ok (.strict (.assert condition)))
    (tail : ProducerScope (next.definitions.map Prod.fst) rawRows rows) :
    ProducerScope (state.definitions.map Prod.fst) (raw :: rawRows)
      (.strict (.assert condition) :: rows) := by
  obtain ⟨opcode, decodedCondition⟩ := decodeRow_assert_fields decoded
  unfold Backend.Native.validateInstruction at accepted
  simp only [ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨opcodeName, opcodeParsed, descriptor, descriptorParsed,
    registry, fieldsParsed, accepted⟩
  have opcodeEq : opcodeName = "assert" := Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp at accepted
  simp only [ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨fact, factParsed, _, booleanChecked, accepted⟩
  have factArgument := Backend.Native.nativeArgument_parts factParsed
  have names : next.definitions.map Prod.fst = state.definitions.map Prod.fst := by
    let assertionCounted := if expected.assertions[state.assertionCount]? == some fact.term then
      {state with assertionCount := state.assertionCount + 1} else state
    let assertionState : Backend.Native.State :=
      {assertionCounted with
        establishedAssertions := (fact.term :: assertionCounted.establishedAssertions).eraseDups}
    have assertionNames : assertionState.definitions.map Prod.fst = state.definitions.map Prod.fst := by
      by_cases matched : expected.assertions[state.assertionCount]? == some fact.term
      · simp [assertionState, assertionCounted, matched]
      · simp [assertionState, assertionCounted, matched]
    split at accepted
    · simp only [ScalarValidationMeaning.bind_ok] at accepted
      rcases accepted with ⟨_, _, refined⟩
      exact (refine_names refined).trans assertionNames
    · cases accepted
      exact assertionNames
  apply ProducerScope.cons
  · simpa [rowReferences, instructionReferences] using
      argument_identifiers factArgument.1 decodedCondition
  · simp [inputOutput, rowDestination, definitionValue]
  · simp [rowDestination, definitionValue]
  · simpa [inputOutput, rowDestination, definitionValue, names] using tail
private theorem ProducerScope.decoded_lessThan_fields {raw : Json} {left right : Operand}
    {bits : Nat} {output : String}
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.lessThan left right bits output)) :
    NativeRelationJson.decodeOperandField raw "a" = .ok left ∧
      NativeRelationJson.decodeOperandField raw "b" = .ok right ∧
      NativeRelationJson.naturalField raw "bits" = .ok bits ∧
      Backend.Native.stringField raw "output" = .ok output := by
  unfold NativeRelationJson.decodeInstruction at decoded
  simp only [ScalarValidationMeaning.bind_ok,
    ScalarValidationOutputMeaning.nativeJson_stringField_eq] at decoded
  rcases decoded with ⟨opcodeName, opcodeParsed, body⟩
  have opcodeEq : opcodeName = "less_than" :=
    Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp only [ScalarValidationMeaning.bind_ok] at body
  rcases body with ⟨_, _, body⟩
  rcases body with ⟨foundBits, bitsParsed, body⟩
  rcases body with ⟨_, _, body⟩
  rcases body with ⟨foundLeft, leftParsed, body⟩
  rcases body with ⟨foundRight, rightParsed, body⟩
  rcases body with ⟨foundOutput, outputParsed, body⟩
  rcases body with ⟨_, _, result⟩
  simp only [Pure.pure, Except.pure] at result
  have resultEq : Instruction.lessThan foundLeft foundRight foundBits foundOutput =
      Instruction.lessThan left right bits output := Except.ok.inj result
  injection resultEq with leftEq rightEq bitsEq outputEq
  subst left right bits output
  exact ⟨leftParsed, rightParsed, bitsParsed, outputParsed⟩

theorem ProducerScope.cons_validated_lessThan {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json}
    {left right : Operand} {bits : Nat} {destination : String}
    {rawRows : List Json} {rows : List GuardedScalarRows.Row}
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : GuardedScalarRows.decodeRow raw =
      .ok (.strict (.lessThan left right bits destination)))
    (temporary : destination.startsWith "%input_" = false)
    (tail : ProducerScope (next.definitions.map Prod.fst) rawRows rows) :
    ProducerScope (state.definitions.map Prod.fst) (raw :: rawRows)
      (.strict (.lessThan left right bits destination) :: rows) := by
  have instruction := (GuardedScalarRows.decodeRow_strict decoded).1.decoded
  obtain ⟨leftField, rightField, _, destinationField⟩ :=
    decoded_lessThan_fields opcode instruction
  obtain ⟨_, _, _, _, _, _, leftAccepted, rightAccepted, _, _, _, _, defined⟩ :=
    RangeDedupComparisonMeaning.acceptedLessThanDefinition opcode accepted
  exact ProducerScope.cons_binary_definition rfl rfl rfl leftField rightField
    destinationField leftAccepted rightAccepted defined temporary tail

theorem ProducerScope.cons_validated_hash {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json}
    {values : List Operand} {destination : String}
    {rawRows : List Json} {rows : List GuardedScalarRows.Row}
    (opcode : Backend.Native.stringField raw "op" = .ok "transient_hash")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : GuardedScalarRows.decodeRow raw =
      .ok (.strict (.hash values destination)))
    (temporary : destination.startsWith "%input_" = false)
    (tail : ProducerScope (next.definitions.map Prod.fst) rawRows rows) :
    ProducerScope (state.definitions.map Prod.fst) (raw :: rawRows)
      (.strict (.hash values destination) :: rows) := by
  have instruction := (GuardedScalarRows.decodeRow_strict decoded).1.decoded
  have fields := NativeRelationJson.decodeInstruction_hashFields opcode instruction
  obtain ⟨_, _, _, acceptedArguments, _, defined⟩ :=
    ScalarValidationHashMeaning.accepted_hash_definition opcode accepted
  have references := ScalarValidationOutputMeaning.arguments_decoded_identifiers_defined
    acceptedArguments fields.1
  obtain ⟨names, absent⟩ := defineResult_names fields.2 defined
  apply ProducerScope.cons
  · simpa [rowReferences, instructionReferences] using references
  · simpa [inputOutput, rowDestination, definitionValue] using absent
  · simpa [rowDestination, definitionValue] using temporary
  · simpa [inputOutput, rowDestination, definitionValue, names] using tail

private theorem ProducerScope.cons_validated
    {expected : Backend.Native.Expected} {state next : Backend.Native.State}
    {raw : Json} {row : Row} {rawTail : List Json} {rowTail : List Row}
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (typed : ScalarValidationArithmeticLoop.NativeDefinitions state)
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next)
    (decoded : decodeRow raw = .ok row)
    (temporary : ∀ destination ∈ (rowDestination raw row).toList,
      destination.startsWith "%input_" = false)
    (tail : ProducerScope (next.definitions.map Prod.fst) rawTail rowTail) :
    ProducerScope (state.definitions.map Prod.fst) (raw :: rawTail) (row :: rowTail) := by
  cases row with
  | publicInput output guard =>
    exact ProducerScope.cons_validated_publicInput inputSchema accepted decoded tail
  | impact guard values =>
    exact ProducerScope.cons_validated_impact accepted decoded tail
  | strict instruction =>
    have temporaryName (destination : String)
        (defined : rowDestination raw (.strict instruction) = some destination) :
        destination.startsWith "%input_" = false :=
      temporary destination (by simp [defined])
    obtain ⟨step, notImpact⟩ := decodeRow_strict decoded
    cases step.supported with
    | publicInput _ opcode =>
      exact False.elim (decodeRow_strict_not_publicInput decoded opcode)
    | privateInput _ opcode =>
      exact ProducerScope.cons_validated_privateInput inputSchema opcode accepted decoded tail
    | add _ _ destination opcode =>
      exact ProducerScope.cons_validated_add typed opcode accepted decoded
        (temporaryName destination rfl) tail
    | mul _ _ destination opcode =>
      exact ProducerScope.cons_validated_mul typed opcode accepted decoded
        (temporaryName destination rfl) tail
    | neg _ destination opcode =>
      exact ProducerScope.cons_validated_neg typed opcode accepted decoded
        (temporaryName destination rfl) tail
    | lessThan _ _ _ destination opcode =>
      exact ProducerScope.cons_validated_lessThan opcode accepted decoded
        (temporaryName destination rfl) tail
    | testEq _ _ destination opcode =>
      exact ProducerScope.cons_validated_testEq typed opcode accepted decoded
        (temporaryName destination rfl) tail
    | hash _ destination opcode =>
      exact ProducerScope.cons_validated_hash opcode accepted decoded
        (temporaryName destination rfl) tail
    | not _ destination opcode =>
      exact ProducerScope.cons_validated_not typed opcode accepted decoded
        (temporaryName destination rfl) tail
    | select _ _ _ destination opcode =>
      exact ProducerScope.cons_validated_select typed opcode accepted decoded
        (temporaryName destination rfl) tail
    | bits _ _ _ => exact ProducerScope.cons_validated_bits accepted decoded tail
    | boolean _ _ => exact ProducerScope.cons_validated_boolean accepted decoded tail
    | assertion _ _ => exact ProducerScope.cons_validated_assert accepted decoded tail
    | copy _ destination opcode =>
      exact ProducerScope.cons_validated_copy typed opcode accepted decoded
        (temporaryName destination (by
          simp [rowDestination, definitionValue, isCopy,
            ScalarValidationMeaning.nativeJson_stringField_eq, opcode])) tail
    | impact _ _ opcode => exact False.elim (notImpact opcode)
    | output _ opcode => exact ProducerScope.cons_validated_output opcode accepted decoded tail
    | constrainEq _ _ opcode =>
      exact ProducerScope.cons_validated_constrain_eq typed opcode accepted decoded tail

/-- Replay the accepted producer trace in decoded artifact order. Each row
uses the definition state reached by its actual predecessor. -/
theorem ProducerScope.of_validation_loop
    {expected : Backend.Native.Expected} {items : List (Json × Nat)} {rows : List Row}
    {initial final : Backend.Native.State}
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (initialTyped : ScalarValidationArithmeticLoop.NativeDefinitions initial)
    (decoded : (items.map Prod.fst).mapM decodeRow = .ok rows)
    (accepted : Backend.Native.validateInstructionLoop expected items initial = .ok final)
    (temporary : TemporaryNamespace (items.map Prod.fst) rows) :
    ProducerScope (initial.definitions.map Prod.fst) (items.map Prod.fst) rows := by
  induction items generalizing initial final rows with
  | nil =>
    change (Except.ok [] : Except String (List Row)) = .ok rows at decoded
    cases decoded
    exact .nil _
  | cons item items ih =>
    rcases item with ⟨raw, ordinal⟩
    simp only [List.map_cons, List.mapM_cons, ScalarValidationMeaning.bind_ok] at decoded
    obtain ⟨row, head, rest, restDecoded, sameRows⟩ := decoded
    cases sameRows
    rw [Backend.Native.validateInstructionLoop, List.forIn_cons] at accepted
    cases checked : Backend.Native.validateInstruction expected initial raw with
    | error message => simp [checked, Bind.bind, Except.bind] at accepted
    | ok next =>
      simp only [checked, bind_pure_comp] at accepted
      have nextTyped := guarded_row_nativeDefinitions inputSchema initialTyped checked head
      have tailNamespace : TemporaryNamespace (items.map Prod.fst) rest := by
        intro pair present name defined
        exact temporary pair (List.mem_cons_of_mem (raw, row) present) name defined
      exact ProducerScope.cons_validated inputSchema initialTyped checked head
        (temporary (raw, row) (List.mem_cons_self ..))
        (ih nextTyped restDecoded accepted tailNamespace)

private theorem inputOutputs_cursor_noninput
    {expected : Backend.Native.Expected} {raw : Json}
    {initial next : Backend.Native.State} {instruction : Instruction}
    (initialTyped : ScalarValidationArithmeticLoop.NativeDefinitions initial)
    (supported : ScalarValidationNativeDefinitions.SupportedScalarOpcode raw instruction)
    (notInput : ∀ visibility output, instruction ≠ .input visibility output)
    (_inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (accepted : Backend.Native.validateInstruction expected initial raw = .ok next)
    {final : Backend.Native.State} {tailRows : List Row}
    (tailSequence : (expected.inputs.take final.inputCount).map (·.identifier) =
      (expected.inputs.take next.inputCount).map (·.identifier) ++ inputOutputs tailRows) :
    (expected.inputs.take final.inputCount).map (·.identifier) =
      (expected.inputs.take initial.inputCount).map (·.identifier) ++
        inputOutputs (.strict instruction :: tailRows) := by
  have inputCount :=
    ScalarValidationNativeDefinitions.accepted_supportedScalarOpcode_noninput_inputCount_preserved
      initialTyped supported notInput accepted
  have outputNone : inputOutput (.strict instruction) = none := by
    cases instruction with
    | input visibility output => exact False.elim (notInput visibility output rfl)
    | _ => rfl
  rw [tailSequence, inputCount, inputOutputs_cons, outputNone]
  simp

private theorem inputOutputs_cursor
    {expected : Backend.Native.Expected} {items : List (Json × Nat)}
    {rows : List Row} {initial final : Backend.Native.State}
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (initialTyped : ScalarValidationArithmeticLoop.NativeDefinitions initial)
    (decoded : (items.map Prod.fst).mapM decodeRow = .ok rows)
    (accepted : Backend.Native.validateInstructionLoop expected items initial = .ok final) :
    (expected.inputs.take final.inputCount).map (·.identifier) =
      (expected.inputs.take initial.inputCount).map (·.identifier) ++ inputOutputs rows := by
  induction items generalizing initial final rows with
  | nil =>
    change (Except.ok [] : Except String (List Row)) = .ok rows at decoded
    cases decoded
    have stateEq : initial = final := by injection accepted
    subst final
    simp [inputOutputs]
  | cons item items ih =>
    rcases item with ⟨raw, ordinal⟩
    simp only [List.map_cons, List.mapM_cons, ScalarValidationMeaning.bind_ok] at decoded
    obtain ⟨row, head, rest, restDecoded, rowsEq⟩ := decoded
    cases rowsEq
    rw [Backend.Native.validateInstructionLoop, List.forIn_cons] at accepted
    cases checked : Backend.Native.validateInstruction expected initial raw with
    | error message => simp [checked, Bind.bind, Except.bind] at accepted
    | ok next =>
      simp only [checked, bind_pure_comp] at accepted
      cases row with
      | publicInput output guard =>
        have nextTyped := guarded_row_nativeDefinitions inputSchema initialTyped checked head
        have tailSequence := ih nextTyped restDecoded accepted
        have fields := decodeRow_publicInput_fields head
        have inputOpcode : Backend.Native.stringField raw "op" =
            .ok (ScalarValidationNativeLoop.inputOpcode .public) := by
          simpa [ScalarValidationNativeLoop.inputOpcode] using fields.1
        obtain ⟨requirement, selected, increment⟩ :=
          NativeInputOrdinal.accepted_input_row_step inputSchema inputOpcode checked
        have descriptor := NativeInputOrdinal.accepted_input_output_descriptor
          selected (inputSchema requirement (List.mem_of_getElem? selected)) inputOpcode checked
        have outputEq : output = requirement.identifier :=
          Except.ok.inj (fields.2.1.symm.trans descriptor.1)
        have takeStep : expected.inputs.take next.inputCount =
            expected.inputs.take initial.inputCount ++ [requirement] := by
          rw [increment, List.take_add_one, selected]
          simp
        rw [tailSequence, takeStep]
        simp [inputOutputs_cons, inputOutput, outputEq, List.map_append]
      | impact guard inputs =>
        have nextTyped := guarded_row_nativeDefinitions inputSchema initialTyped checked head
        have tailSequence := ih nextTyped restDecoded accepted
        have fields := decodeRow_impact_fields head
        have inputCount :=
          ScalarValidationNativeDefinitions.accepted_impact_inputCount fields.1 checked
        rw [tailSequence, inputCount]
        simp [inputOutputs_cons, inputOutput]
      | strict instruction =>
        have nextTyped := guarded_row_nativeDefinitions inputSchema initialTyped checked head
        have tailSequence := ih nextTyped restDecoded accepted
        obtain ⟨step, _notImpact⟩ := decodeRow_strict head
        have notPublicInput := decodeRow_strict_not_publicInput head
        cases instruction with
        | input visibility output =>
          cases visibility with
          | «public» =>
            cases step.supported with
            | publicInput _ opcode =>
              exact False.elim (notPublicInput (by
                simpa [ScalarValidationNativeLoop.inputOpcode] using opcode))
          | «private» =>
            cases step.supported with
            | privateInput _ opcode =>
              have inputOpcode : Backend.Native.stringField raw "op" =
                  .ok (ScalarValidationNativeLoop.inputOpcode .private) := by
                simpa [ScalarValidationNativeLoop.inputOpcode] using opcode
              obtain ⟨requirement, selected, increment⟩ :=
                NativeInputOrdinal.accepted_input_row_step inputSchema inputOpcode checked
              have descriptor := NativeInputOrdinal.accepted_input_row_descriptor_agrees
                selected (inputSchema requirement (List.mem_of_getElem? selected))
                inputOpcode checked step.decoded
              have outputEq : output = requirement.identifier := by
                have equality := congrArg Prod.snd descriptor.2
                simpa using equality
              have takeStep : expected.inputs.take next.inputCount =
                  expected.inputs.take initial.inputCount ++ [requirement] := by
                rw [increment, List.take_add_one, selected]
                simp
              rw [tailSequence, takeStep]
              simp [inputOutputs_cons, inputOutput, outputEq, List.map_append]
        | _ =>
          exact inputOutputs_cursor_noninput initialTyped step.supported
            (by intro visibility output same; cases same) inputSchema checked tailSequence

/-- The decoded input lane sequence is exactly the descriptor prefix consumed
by the accepted producer trace. In particular, a completed zero-based input
cursor yields every expected input identifier in order. -/
theorem inputOutputs_eq_expectedInputs
    {expected : Backend.Native.Expected} {items : List (Json × Nat)}
    {rows : List Row} {initial final : Backend.Native.State}
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (initialTyped : ScalarValidationArithmeticLoop.NativeDefinitions initial)
    (decoded : (items.map Prod.fst).mapM decodeRow = .ok rows)
    (accepted : Backend.Native.validateInstructionLoop expected items initial = .ok final)
    (initialInputCount : initial.inputCount = 0)
    (finalInputCount : final.inputCount = expected.inputs.length) :
    inputOutputs rows = expected.inputs.map (·.identifier) := by
  have sequence := inputOutputs_cursor inputSchema initialTyped decoded accepted
  rw [initialInputCount, finalInputCount, List.take_length, List.take_zero] at sequence
  simpa using sequence.symm

private def FramedAssignment (seed : Assignment) :=
  { witness : Assignment // ∀ name, witness ("%input_" ++ name) = seed ("%input_" ++ name) }

private theorem inputName_startsWith (name : String) :
    ("%input_" ++ name).startsWith "%input_" = true := by
  apply String.startsWith_string_iff.mpr
  rw [String.toList_append]
  have marker : "%input_".toList = ['%', 'i', 'n', 'p', 'u', 't', '_'] := by decide
  rw [marker]
  exact ⟨name.toList, rfl⟩

private theorem different_from_inputName (output name : String)
    (notInput : output.startsWith "%input_" = false) :
    output ≠ "%input_" ++ name := by
  intro same
  have starts := congrArg (fun value : String => value.startsWith "%input_") same
  simp [notInput, inputName_startsWith] at starts

/-- `registered` begins with all caller-supplied arguments and all row input
outputs. Their values already exist in `seed`, so the order check applies to
SSA temporaries introduced by defining rows. -/
private def assembleRows (hash : Hash) (seed : Assignment)
    (rawRows : List Json) (rows : List Row) (registered : List String)
    (state : FramedAssignment seed) : Except String (FramedAssignment seed) := do
  match rawRows, rows with
  | [], [] => pure state
  | raw :: rawTail, row :: rowTail => do
      ensure ((rowReferences raw row).all registered.contains)
        "native scalar row references a name before definition"
      match definitionValue hash raw state.1 row with
      | none => assembleRows hash seed rawTail rowTail registered state
      | some (destination, value) =>
          if registered.contains destination then
            throw "repeated native scalar definition"
          if notInput : destination.startsWith "%input_" = false then
            let nextState : FramedAssignment seed := ⟨
              ScalarWitness.assign state.1 destination value,
              by
                intro name
                have destinationDifferent : destination ≠ "%input_" ++ name :=
                  different_from_inputName destination name notInput
                calc
                  ScalarWitness.assign state.1 destination value ("%input_" ++ name) =
                      state.1 ("%input_" ++ name) :=
                    ScalarWitness.assign_other state.1 destination ("%input_" ++ name)
                      value destinationDifferent.symm
                  _ = seed ("%input_" ++ name) := state.2 name⟩
            assembleRows hash seed rawTail rowTail (destination :: registered) nextState
          else throw "native scalar definition overwrites a preseeded input"
  | _, _ => throw "decoded native scalar row count mismatch"

/-- Build witness values for guarded scalar rows. Header arguments and all row
input outputs read from the seed assignment. Defining scalar opcodes extend the
assignment in row order; constraint and observation rows leave it unchanged. -/
def assemble (hash : NativeRelation.Hash) (seed : NativeRelation.Assignment)
    (arguments : List String) (rawRows : List Lean.Json) :
    Except String { output : NativeRelation.Assignment //
      ∀ name, output ("%input_" ++ name) = seed ("%input_" ++ name) } := do
  ensure (arguments.all validIdentifier) "invalid scalar call input identifier"
  let rows ← rawRows.mapM GuardedScalarRows.decodeRow
  let seededRows := inputOutputs rows
  let registered := arguments ++ seededRows
  ensure (registered.eraseDups.length == registered.length)
    "native scalar input names collide or repeat"
  let initial : FramedAssignment seed := ⟨seed, by intro name; rfl⟩
  assembleRows hash seed rawRows rows registered initial

private theorem assembleRows_of_scope (hash : Hash) (seed : Assignment)
    {registered : List String} {rawRows : List Json} {rows : List Row} {finalNames : List String}
    (scope : Scope registered rawRows rows finalNames) (initial : FramedAssignment seed) :
    ∃ witness : FramedAssignment seed,
      assembleRows hash seed rawRows rows registered initial = .ok witness ∧
      ∀ target : Assignment,
        (∀ name ∈ registered, initial.val name = target name) →
        (∀ instruction, .strict instruction ∈ rows → Instruction.Holds hash target instruction) →
        (∀ left right width destination,
          .strict (.lessThan left right width destination) ∈ rows →
          (left.read target).val < 2 ^ width ∧ (right.read target).val < 2 ^ width) →
        ∀ name ∈ finalNames, witness.val name = target name := by
  induction scope generalizing initial with
  | nil => exact ⟨initial, rfl, fun _ agrees _ _ => agrees⟩
  | @cons registered raw row rawTail rowTail finalNames refs fresh tail ih =>
    have referenced : ((rowReferences raw row).all registered.contains) = true := by
      apply List.all_eq_true.mpr
      intro name used
      simp [refs name used]
    cases defined : definitionValue hash raw initial.val row with
    | none =>
      have destinationEq : rowDestination raw row = none := by
        rw [← definition_destination hash initial.val, defined]
        rfl
      simp only [destinationEq, Option.toList_none, List.nil_append] at ih
      obtain ⟨witness, runs, agrees⟩ := ih initial
      refine ⟨witness, ?_, fun target seedAgreement holds widths => agrees target seedAgreement
        (fun instruction present => holds instruction (List.mem_cons_of_mem _ present))
        (fun left right width destination present =>
          widths left right width destination (List.mem_cons_of_mem _ present))⟩
      simpa [assembleRows, referenced, defined, ensure, Bind.bind, Except.bind] using runs
    | some pair =>
      rcases pair with ⟨destination, value⟩
      have destinationEq : rowDestination raw row = some destination := by
        rw [← definition_destination hash initial.val, defined]
        rfl
      have admitted := fresh destination (by simp [destinationEq])
      let next : FramedAssignment seed := ⟨assign initial.val destination value, by
        intro name
        rw [assign_other _ _ _ _ (different_from_inputName destination name admitted.2).symm]
        exact initial.property name⟩
      simp only [destinationEq, Option.toList_some, List.singleton_append] at ih
      obtain ⟨witness, runs, agrees⟩ := ih next
      refine ⟨witness, ?_, ?_⟩
      · simpa [assembleRows, referenced, defined, admitted.1, admitted.2, next,
          ensure, Bind.bind, Except.bind] using runs
      · intro target seedAgreement holds widths
        have targetDefined : definitionValue hash raw target row = some (destination, value) := by
          rw [← definitionValue_agrees (hash := hash) (raw := raw) (row := row)
            (left := initial.val) (right := target) (fun name used => seedAgreement name (refs name used))]
          exact defined
        have outputEq := definitionValue_holds targetDefined
          (fun instruction same => holds instruction (by simp [same]))
          (fun left right width output same => widths left right width output (by simp [same]))
        apply agrees target _ (fun instruction present => holds instruction (List.mem_cons_of_mem _ present))
          (fun left right width dest present => widths left right width dest (List.mem_cons_of_mem _ present))
        intro name present
        rcases List.mem_cons.mp present with same | present
        · subst name
          exact (assign_same initial.val destination value).trans outputEq.symm
        · have different : name ≠ destination := by
            intro same
            exact admitted.1 (same ▸ present)
          exact (assign_other initial.val destination name value different).trans (seedAgreement name present)

/-- Once the decoded names and ordering are valid, the assembler produces an
assignment for any seed. An independently satisfying extension determines
the resulting values on all names in the validated scope. -/
theorem assemble_with_scope (hash : Hash) (seed : Assignment)
    (arguments : List String) (rawRows : List Json) (rows : List Row) (finalNames : List String)
    (decoded : rawRows.mapM GuardedScalarRows.decodeRow = .ok rows)
    (validArguments : arguments.all validIdentifier = true)
    (distinctInputs : (arguments ++ inputOutputs rows).eraseDups.length =
      (arguments ++ inputOutputs rows).length)
    (scope : Scope (arguments ++ inputOutputs rows) rawRows rows finalNames) :
    ∃ witness : FramedAssignment seed,
      assemble hash seed arguments rawRows = .ok witness ∧
      ∀ target : Assignment,
        (∀ name ∈ arguments ++ inputOutputs rows, seed name = target name) →
        (∀ instruction, .strict instruction ∈ rows → Instruction.Holds hash target instruction) →
        (∀ left right width destination, .strict (.lessThan left right width destination) ∈ rows →
          (left.read target).val < 2 ^ width ∧ (right.read target).val < 2 ^ width) →
        ∀ name ∈ finalNames, witness.val name = target name := by
  obtain ⟨witness, runs, agreement⟩ := assembleRows_of_scope hash seed scope ⟨seed, fun _ => rfl⟩
  have noCollision : ((arguments ++ inputOutputs rows).eraseDups.length ==
      (arguments ++ inputOutputs rows).length) = true := by simp [distinctInputs]
  refine ⟨witness, ?_, agreement⟩
  simpa only [assemble, validArguments, decoded, noCollision, ensure, ite_true,
    Bind.bind, Except.bind, FramedAssignment] using runs

/-- Replay the exact guarded scalar rows from the runtime seed. Given an
ordered scope and an independent satisfying assignment with the checked
comparison widths, assembly reconstructs its values on all defined names
and preserves every ordinary constraint. -/
theorem assemble_of_scope (hash : Hash) (seed target : Assignment)
    (arguments : List String) (rawRows : List Json) (rows : List Row) (finalNames : List String)
    (decoded : rawRows.mapM GuardedScalarRows.decodeRow = .ok rows)
    (validArguments : arguments.all validIdentifier = true)
    (distinctInputs : (arguments ++ inputOutputs rows).eraseDups.length =
      (arguments ++ inputOutputs rows).length)
    (scope : Scope (arguments ++ inputOutputs rows) rawRows rows finalNames)
    (inputsAgree : ∀ name ∈ arguments ++ inputOutputs rows, seed name = target name)
    (holds : ∀ instruction, .strict instruction ∈ rows → Instruction.Holds hash target instruction)
    (widths : ∀ left right width destination, .strict (.lessThan left right width destination) ∈ rows →
      (left.read target).val < 2 ^ width ∧ (right.read target).val < 2 ^ width) :
    ∃ (witness : FramedAssignment seed),
      assemble hash seed arguments rawRows = .ok witness ∧
      (∀ name ∈ finalNames, witness.val name = target name) ∧
      ∀ instruction, .strict instruction ∈ rows → Instruction.Holds hash witness.val instruction := by
  obtain ⟨witness, runs, agrees⟩ :=
    assemble_with_scope hash seed arguments rawRows rows finalNames decoded validArguments
      distinctInputs scope
  have agreement := agrees target inputsAgree holds widths
  refine ⟨witness, runs, agreement, ?_⟩
  intro instruction present
  apply (Instruction.Holds.agrees hash instruction (fun name used => agreement name
    (scope.strict_identifiers (fun name lane => List.mem_append_right _ lane)
      instruction present name used))).mpr
  exact holds instruction present

end Noctium.Verification.GuardedScalarWitnessAssembly
