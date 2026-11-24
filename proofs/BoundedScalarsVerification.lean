import examples.BoundedScalars

namespace Noctium.BoundedScalarsVerification

def applyEntry : Entrypoint :=
  BoundedScalars.entrypoints.headD {name := "missing", circuit := {name := "missing"}}

theorem apply_disclosure : Disclosure.entrypoint applyEntry = .ok () := by
  with_unfolding_all rfl

structure Inputs where
  expected : Nat
  left : Nat
  right : Nat
  deriving DecidableEq

def inputEnvironment (input : Inputs) : EvalEnv :=
  [("expected", .uint 510 input.expected), ("left", .uint 255 input.left),
   ("right", .uint 255 input.right)]

def sumExpression : Expr (.uint 510) :=
  Expr.uadd (Expr.ref "left" : Expr (.uint 255)) (Expr.ref "right" : Expr (.uint 255))

def relationConstraints : List (Expr .bool) :=
  [sumExpression.eq sumExpression,
   sumExpression.eq (Expr.ref "expected")]

def context : EvalContext := { modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused" }

theorem relation_validates : Circuit.validate (evaluationCapabilities context) boundedRelation = .ok () := by
  with_unfolding_all rfl

theorem sum_expression_eval (input : Inputs) (hleft : input.left ≤ 255)
    (hright : input.right ≤ 255) :
    (Expr.uadd (Expr.ref "left" : Expr (.uint 255)) (Expr.ref "right" : Expr (.uint 255))).eval
        context (inputEnvironment input) = .ok (input.left + input.right) := by
  have leftLookup : (inputEnvironment input).lookup "left" = some (.uint 255 input.left) := by rfl
  have rightLookup : (inputEnvironment input).lookup "right" = some (.uint 255 input.right) := by rfl
  have leftField : input.left < Field.modulus := Nat.lt_of_le_of_lt hleft (by decide)
  have rightField : input.right < Field.modulus := Nat.lt_of_le_of_lt hright (by decide)
  have leftEval : (Expr.ref "left" : Expr (.uint 255)).eval context (inputEnvironment input) = .ok input.left := by
    rw [Expr.eval, leftLookup]
    simp [Value.as, canonical_eq, context, ScalarPolicy.maxUint, ScalarPolicy.maxBits, hleft, leftField]
    rfl
  have rightEval : (Expr.ref "right" : Expr (.uint 255)).eval context (inputEnvironment input) = .ok input.right := by
    rw [Expr.eval, rightLookup]
    simp [Value.as, canonical_eq, context, ScalarPolicy.maxUint, ScalarPolicy.maxBits, hright, rightField]
    rfl
  simp only [Expr.eval, leftEval, rightEval, Except.bind, Bind.bind]
  change (if 510 ≤ ScalarPolicy.maxUint && input.left + input.right ≤ 510 &&
      input.left + input.right < Field.modulus then (Except.ok (input.left + input.right) : Except String Nat)
    else Except.error "scalar conversion exceeds unsigned bound") = .ok (input.left + input.right)
  have hsum : input.left + input.right ≤ 510 := by
    calc
      input.left + input.right ≤ 255 + 255 := Nat.add_le_add hleft hright
      _ = 510 := by decide
  have maximumBound : 510 ≤ ScalarPolicy.maxUint := by decide
  have sumField : input.left + input.right < Field.modulus :=
    Nat.lt_of_le_of_lt hsum (by decide)
  simp [maximumBound, sumField]
  exact hsum

theorem expected_expression_eval (input : Inputs) (hbound : input.expected ≤ 510) :
    (Expr.ref "expected" : Expr (.uint 510)).eval context (inputEnvironment input) =
      .ok input.expected := by
  have lookup : (inputEnvironment input).lookup "expected" = some (.uint 510 input.expected) := by rfl
  have field : input.expected < Field.modulus := Nat.lt_of_le_of_lt hbound (by decide)
  rw [Expr.eval, lookup]
  simp [Value.as, canonical_eq, context, ScalarPolicy.maxUint, ScalarPolicy.maxBits, hbound, field]
  rfl

theorem accepted_constraints_recover_sum (input : Inputs) (hexpected : input.expected ≤ 510)
    (hleft : input.left ≤ 255) (hright : input.right ≤ 255)
    (accepted : runConstraints context (inputEnvironment input) boundedRelation.constraints = .ok ()) :
    input.expected = input.left + input.right := by
  have sumEval := sum_expression_eval input hleft hright
  have expectedEval := expected_expression_eval input hexpected
  change runConstraints context (inputEnvironment input) relationConstraints = .ok () at accepted
  have firstEval : (sumExpression.eq sumExpression).eval
      context (inputEnvironment input) = (Except.ok (_root_.Bool.true) : Except String _root_.Bool) := by
    simp only [sumExpression, Expr.eval, sumEval, Except.bind, Bind.bind]
    change (Except.ok (input.left + input.right == input.left + input.right) : Except String _root_.Bool) =
      (Except.ok (_root_.Bool.true) : Except String _root_.Bool)
    simp
  have secondEval : (sumExpression.eq (Expr.ref "expected")).eval context (inputEnvironment input) =
      (Except.ok (input.left + input.right == input.expected) : Except String _root_.Bool) := by
    simp only [sumExpression, Expr.eval, sumEval, expectedEval, Except.bind, Bind.bind]
    rfl
  simp only [relationConstraints, runConstraints, firstEval, secondEval] at accepted
  have result : input.left + input.right == input.expected := by
    cases h : (input.left + input.right == input.expected) <;> simp [h] at accepted ⊢
  exact (Nat.eq_of_beq_eq_true result).symm

theorem bounded_relation_accepts (input : Inputs) (outputs : EvalEnv)
    (hexpected : input.expected ≤ 510) (hleft : input.left ≤ 255) (hright : input.right ≤ 255)
    (run : Circuit.run context boundedRelation (inputEnvironment input) = .ok outputs) :
    input.expected = input.left + input.right ∧ outputs = [("result", .uint 510 input.expected)] := by
  have expectedField : input.expected < Field.modulus := Nat.lt_of_le_of_lt hexpected (by decide)
  have leftField : input.left < Field.modulus := Nat.lt_of_le_of_lt hleft (by decide)
  have rightField : input.right < Field.modulus := Nat.lt_of_le_of_lt hright (by decide)
  have namesUnique : uniqueNames ["expected", "left", "right"] = _root_.Bool.true := by decide
  unfold Circuit.run at run
  rw [relation_validates] at run
  have expectedEval := expected_expression_eval input hexpected
  have expectedEvalSource :
      Expr.eval { modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused" }
        [("expected", .uint 510 input.expected), ("left", .uint 255 input.left),
         ("right", .uint 255 input.right)] (Expr.ref "expected" : Expr (.uint 510)) =
          (Except.ok input.expected : Except String Nat) := by
    simpa [context, inputEnvironment] using expectedEval
  simp [context, boundedRelation, namesUnique, List.lookup, Value.as, canonical_eq,
    ScalarPolicy.maxUint, ScalarPolicy.maxBits, inputEnvironment, hexpected, hleft, hright,
    expectedField, leftField, rightField] at run
  have sourceConstraintsAccepted :
      runConstraints
        { modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused" }
        [("expected", .uint 510 input.expected), ("left", .uint 255 input.left),
         ("right", .uint 255 input.right)]
        [((Expr.ref "left" : Expr (.uint 255)).uadd (Expr.ref "right" : Expr (.uint 255))).eq
            ((Expr.ref "left" : Expr (.uint 255)).uadd (Expr.ref "right" : Expr (.uint 255))),
         ((Expr.ref "left" : Expr (.uint 255)).uadd (Expr.ref "right" : Expr (.uint 255))).eq
            (Expr.ref "expected" : Expr (.uint 510))] = .ok () := by
    cases h : runConstraints
        { modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused" }
        [("expected", .uint 510 input.expected), ("left", .uint 255 input.left),
         ("right", .uint 255 input.right)]
        [((Expr.ref "left" : Expr (.uint 255)).uadd (Expr.ref "right" : Expr (.uint 255))).eq
            ((Expr.ref "left" : Expr (.uint 255)).uadd (Expr.ref "right" : Expr (.uint 255))),
         ((Expr.ref "left" : Expr (.uint 255)).uadd (Expr.ref "right" : Expr (.uint 255))).eq
            (Expr.ref "expected" : Expr (.uint 510))] with
    | error message => rw [h] at run; contradiction
    | ok value => cases value; rfl
  have constraintsAccepted : runConstraints context (inputEnvironment input) relationConstraints = .ok () := by
    simpa [context, inputEnvironment, relationConstraints, sumExpression] using sourceConstraintsAccepted
  have exactSum := accepted_constraints_recover_sum input hexpected hleft hright constraintsAccepted
  have exactOutput : outputs = [("result", .uint 510 input.expected)] := by
    simp [sourceConstraintsAccepted, Value.pack, Except.bind, Bind.bind] at run
    simp only [expectedEvalSource] at run
    exact (Except.ok.inj run).symm
  exact ⟨exactSum, exactOutput⟩

theorem bounded_relation_private_outputs (left right : Inputs) (leftOutputs rightOutputs : EvalEnv)
    (samePublic : left.expected = right.expected)
    (leftExpectedBound : left.expected ≤ 510) (rightExpectedBound : right.expected ≤ 510)
    (leftBound : left.left ≤ 255) (leftRightBound : left.right ≤ 255)
    (rightBound : right.left ≤ 255) (rightRightBound : right.right ≤ 255)
    (leftRun : Circuit.run context boundedRelation (inputEnvironment left) = .ok leftOutputs)
    (rightRun : Circuit.run context boundedRelation (inputEnvironment right) = .ok rightOutputs) :
    leftOutputs = rightOutputs := by
  have leftResult := bounded_relation_accepts left leftOutputs leftExpectedBound leftBound
    leftRightBound leftRun
  have rightResult := bounded_relation_accepts right rightOutputs rightExpectedBound rightBound
    rightRightBound rightRun
  rw [leftResult.2, rightResult.2, samePublic]

theorem sample_circuit_run :
    Circuit.run context boundedRelation (inputEnvironment ⟨5, 2, 3⟩) =
      .ok [("result", .uint 510 5)] := by
  with_unfolding_all rfl

end Noctium.BoundedScalarsVerification
