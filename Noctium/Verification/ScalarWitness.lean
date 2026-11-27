import Noctium.Verification.NativeRelation

namespace Noctium.Verification.ScalarWitness

open NativeRelation

def assign (witness : Assignment) (name : String) (value : Scalar) : Assignment :=
  fun found => if found = name then value else witness found

@[simp] theorem assign_same (witness : Assignment) (name : String) (value : Scalar) :
    assign witness name value name = value := by simp [assign]

@[simp] theorem assign_other (witness : Assignment) (name found : String) (value : Scalar)
    (different : found ≠ name) : assign witness name value found = witness found := by
  simp [assign, different]

def OperandIndependent (name : String) : Operand → Prop
  | .immediate _ => True
  | .reference found => found ≠ name

@[simp] theorem Operand.read_assign (witness : Assignment) (name : String) (value : Scalar)
    (operand : Operand) (independent : OperandIndependent name operand) :
    operand.read (assign witness name value) = operand.read witness := by
  cases operand with
  | immediate _ => rfl
  | reference found =>
    have condition : ¬(found = name) := fun equal => independent equal
    simp [Operand.read, assign, condition]

def operandIdentifiers : Operand → List String
  | .immediate _ => []
  | .reference name => [name]

@[simp] theorem Operand.read_assign_of_not_identifier (witness : Assignment) (name : String)
    (value : Scalar) (operand : Operand)
    (absent : name ∉ operandIdentifiers operand) :
    operand.read (assign witness name value) = operand.read witness := by
  cases operand with
  | immediate _ => rfl
  | reference reference =>
    simp only [operandIdentifiers, List.mem_singleton] at absent
    exact Operand.read_assign witness name value _ (fun equal => absent equal.symm)

def instructionIdentifiers : Instruction → List String
  | .input _ name => [name]
  | .boolean value | .bits value _ => operandIdentifiers value
  | .lessThan left right _ output | .add left right output | .mul left right output
  | .testEq left right output => operandIdentifiers left ++ operandIdentifiers right ++ [output]
  | .neg value output | .not value output => operandIdentifiers value ++ [output]
  | .equal left right => operandIdentifiers left ++ operandIdentifiers right
  | .select condition yes no output =>
    operandIdentifiers condition ++ operandIdentifiers yes ++ operandIdentifiers no ++ [output]
  | .hash values output => values.flatMap operandIdentifiers ++ [output]
  | .assert condition => operandIdentifiers condition
  | .impact guard values => operandIdentifiers guard ++ values.flatMap operandIdentifiers
  | .output values => values.flatMap operandIdentifiers

def InstructionIndependent (name : String) (instruction : Instruction) : Prop :=
  name ∉ instructionIdentifiers instruction

theorem Operand.read_agrees (operand : Operand) {left right : Assignment}
    (agrees : ∀ name ∈ operandIdentifiers operand, left name = right name) :
    operand.read left = operand.read right := by
  cases operand with
  | immediate _ => rfl
  | reference name => exact agrees name (by simp [operandIdentifiers])

theorem operands_read_agree (operands : List Operand) {left right : Assignment}
    (agrees : ∀ name ∈ operands.flatMap operandIdentifiers, left name = right name) :
    operands.map (·.read left) = operands.map (·.read right) := by
  apply List.map_congr_left
  intro operand present
  apply Operand.read_agrees
  intro name used
  exact agrees name (List.mem_flatMap.mpr ⟨operand, present, used⟩)

/-- Scope an ordinary relation constraint to the operands and destination
spelled in the decoded instruction. -/
theorem Instruction.Holds.agrees (hash : Hash) (instruction : Instruction)
    {left right : Assignment}
    (agreement : ∀ name ∈ instructionIdentifiers instruction, left name = right name) :
    Instruction.Holds hash left instruction ↔ Instruction.Holds hash right instruction := by
  cases instruction <;> simp_all [Instruction.Holds, instructionIdentifiers]
  all_goals
    simp (disch := (intro name used; apply agreement; simp_all [List.mem_flatMap]))
      only [Operand.read_agrees (left := left) (right := right),
        operands_read_agree (left := left) (right := right), iff_self]

theorem Instruction.Holds.assign_frame (hash : Hash) (witness : Assignment)
    (name : String) (value : Scalar) (instruction : Instruction)
    (independent : InstructionIndependent name instruction) :
    Instruction.Holds hash (assign witness name value) instruction ↔
      Instruction.Holds hash witness instruction := by
  apply Instruction.Holds.agrees
  intro found present
  apply assign_other
  rintro rfl
  exact independent present

end Noctium.Verification.ScalarWitness
