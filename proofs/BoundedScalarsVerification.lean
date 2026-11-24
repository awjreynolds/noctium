import examples.BoundedScalars
import Noctium.Verification
import Noctium.Verification.ScalarNormalization
import Noctium.Verification.SourceEffects

namespace Noctium.BoundedScalarsVerification

open Verification

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

def state (total : Nat) : LedgerState := { cells := [("total", .uint 510 total)] }

def applyEffects : List Effect :=
  [.readCell "total" "old" (.uint 510),
   .require ((Expr.cast .native (Expr.ref "old" : Expr (.uint 510))).eq (Expr.native 0)),
   .writeCell "total" (.uint 510) (Expr.ref "result")]

theorem apply_effects_shape : applyEntry.effects = applyEffects := by
  with_unfolding_all rfl

theorem apply_guards_shape : applyEntry.effectGuards = [none, none, none] := by
  with_unfolding_all rfl

private theorem require_step_success_condition (condition : Expr .bool) (env : EvalEnv)
    (ledger : LedgerState) (after : EvalEnv × LedgerState)
    (success : Noctium.Verification.SourceEffects.step context (.require condition) (env, ledger) = .ok after) :
    condition.eval context env = .ok _root_.Bool.true ∧ after = (env, ledger) := by
  cases evaluated : condition.eval context env with
  | error message =>
    simp [Noctium.Verification.SourceEffects.step, runEffectWithEnv, evaluated,
      Except.bind, Bind.bind] at success
  | ok value =>
    cases value with
    | «false» =>
      simp [Noctium.Verification.SourceEffects.step, runEffectWithEnv, evaluated,
        Except.bind, Bind.bind] at success
    | «true» =>
      simp [Noctium.Verification.SourceEffects.step, runEffectWithEnv, evaluated,
        Except.bind, Bind.bind] at success
      exact ⟨rfl, (Except.ok.inj success).symm⟩

theorem apply_effects_success (input : Inputs) (total : Nat)
    (finalEnv : EvalEnv) (after : LedgerState)
    (totalBound : total ≤ 510) (expectedBound : input.expected ≤ 510)
    (success : runEffectsWithGuardsAndEnv context applyEntry.effects applyEntry.effectGuards
      ([ ("result", .uint 510 input.expected) ] ++ inputEnvironment input) (state total) =
      .ok (finalEnv, after)) :
    total = 0 ∧
      finalEnv = ("old", .uint 510 total) :: ([ ("result", .uint 510 input.expected) ] ++ inputEnvironment input) ∧
      after = state input.expected := by
  rw [apply_effects_shape, apply_guards_shape] at success
  change runEffectsWithEnv context applyEffects
    ([ ("result", .uint 510 input.expected) ] ++ inputEnvironment input) (state total) =
      .ok (finalEnv, after) at success
  rw [SourceEffects.runEffectsWithEnv_eq_fold, applyEffects] at success
  let initialEnv := [("result", .uint 510 input.expected)] ++ inputEnvironment input
  let readEnv := ("old", .uint 510 total) :: initialEnv
  have totalField : total < Field.modulus := Nat.lt_of_le_of_lt totalBound (by decide)
  have readStep : SourceEffects.step context (.readCell "total" "old" (.uint 510))
      (initialEnv, state total) = .ok (readEnv, state total) := by
    simp [readEnv, initialEnv, SourceEffects.step, runEffectWithEnv, state,
      canonical_eq, context, ScalarPolicy.maxUint, ScalarPolicy.maxBits,
      totalBound, Field.modulus, Value.as, Value.pack]
    split
    · omega
    · simp [pure, Except.pure]
  rw [SourceEffects.fold_cons, readStep, Except.bind] at success
  rw [SourceEffects.fold_cons] at success
  have resultLookup : readEnv.lookup "result" = some (.uint 510 input.expected) := by
    simp [readEnv, initialEnv, inputEnvironment, List.lookup]
  have resultEval : (Expr.ref "result" : Expr (.uint 510)).eval context readEnv =
      .ok input.expected := by
    rw [Expr.eval, resultLookup]
    have expectedField : input.expected < Field.modulus :=
      Nat.lt_of_le_of_lt expectedBound (by decide)
    simp [Value.as, canonical_eq, context, ScalarPolicy.maxUint,
      ScalarPolicy.maxBits, expectedBound, expectedField, pure, Except.pure]
  have castEval : (Expr.cast .native (Expr.ref "old" : Expr (.uint 510))).eval
      context readEnv = .ok total := by
    have oldLookup : readEnv.lookup "old" = some (.uint 510 total) := by
      rfl
    have oldEval : (Expr.ref "old" : Expr (.uint 510)).eval context readEnv = .ok total := by
      rw [Expr.eval, oldLookup]
      simp [Value.as, canonical_eq, context, ScalarPolicy.maxUint,
        ScalarPolicy.maxBits, totalBound, totalField, pure, Except.pure]
    have castResult := ScalarNormalization.eval_cast_scalar context readEnv
      (Expr.ref "old" : Expr (.uint 510)) (.uint 510) .native total oldEval
    simp [ScalarNormalization.scalarCast, ScalarNormalization.number, context,
      totalField] at castResult
    exact castResult
  have conditionEval :
      ((Expr.cast .native (Expr.ref "old" : Expr (.uint 510))).eq (Expr.native 0)).eval
        context readEnv = .ok (total == 0) := by
    simp only [Expr.eval, castEval]
    rfl
  cases requireStep : SourceEffects.step context
      (.require ((Expr.cast .native (Expr.ref "old" : Expr (.uint 510))).eq (Expr.native 0)))
      (readEnv, state total) with
  | error message => simp [requireStep, Except.bind] at success
  | ok middle =>
  rw [requireStep, Except.bind] at success
  rw [SourceEffects.fold_cons] at success
  have conditionAccepted := require_step_success_condition
    ((Expr.cast .native (Expr.ref "old" : Expr (.uint 510))).eq (Expr.native 0))
    readEnv (state total) middle requireStep
  rcases conditionAccepted with ⟨conditionAccepted, frameAfter⟩
  rw [conditionEval] at conditionAccepted
  have totalZero : total = 0 := of_decide_eq_true (Except.ok.inj conditionAccepted)
  have middleEq : middle = (readEnv, state total) := frameAfter
  subst middle
  subst total
  have writeStep : SourceEffects.step context
      (.writeCell "total" (.uint 510) (Expr.ref "result"))
      (readEnv, state 0) = .ok (readEnv, state input.expected) := by
    rw [SourceEffects.step, runEffectWithEnv]
    rw [resultEval]
    rfl
  have finalEq : (Except.ok (readEnv, state input.expected) : Except String (EvalEnv × LedgerState)) =
      .ok (finalEnv, after) := by
    simpa only [writeStep, Except.bind, SourceEffects.fold_nil] using success
  have afterEq : state input.expected = after :=
    congrArg Prod.snd (Except.ok.inj finalEq)
  have environmentEq : readEnv = finalEnv := congrArg Prod.fst (Except.ok.inj finalEq)
  exact ⟨rfl, environmentEq.symm, afterEq.symm⟩

private theorem successful_apply_run (input : Inputs) (total : Nat) (outputs : EvalEnv)
    (after : LedgerState) (totalBound : total ≤ 510)
    (expectedBound : input.expected ≤ 510)
    (circuitSuccess : Circuit.run context boundedRelation (inputEnvironment input) =
      .ok [("result", .uint 510 input.expected)])
    (success : applyEntry.run context (inputEnvironment input) (state total) =
      .ok (outputs, after)) :
    total = 0 ∧ outputs = [("result", .uint 510 input.expected)] ∧ after = state input.expected := by
  have entryCircuit : applyEntry.circuit.run context (inputEnvironment input) =
      .ok [("result", .uint 510 input.expected)] := by
    simpa [applyEntry, BoundedScalars] using circuitSuccess
  unfold Entrypoint.run at success
  rw [apply_disclosure, entryCircuit] at success
  simp [applyEntry, BoundedScalars, state] at success
  simp only [Except.bind, Bind.bind] at success
  let effectRunner := runEffectsWithGuardsAndEnv context
    [Effect.readCell "total" "old" (.uint 510),
     Effect.require ((Expr.cast .native (Expr.ref "old" : Expr (.uint 510))).eq (Expr.native 0)),
     Effect.writeCell "total" (.uint 510) (Expr.ref "result")]
    [none, none, none] ([ ("result", .uint 510 input.expected) ] ++ inputEnvironment input)
    (state total)
  change (fun a => ([("result", .uint 510 input.expected)], a.2)) <$> effectRunner =
    .ok (outputs, after) at success
  cases effects : effectRunner with
  | error message =>
    rw [effects] at success
    cases success
  | ok frame =>
    rcases frame with ⟨effectEnv, effectState⟩
    have pairEq : ([("result", .uint 510 input.expected)], effectState) = (outputs, after) := by
      rw [effects] at success
      injection success
    have transition := apply_effects_success input total effectEnv effectState
      totalBound expectedBound (by simpa [effectRunner, applyEntry, BoundedScalars] using effects)
    have afterEq : effectState = after := congrArg Prod.snd pairEq
    exact ⟨transition.1, (congrArg Prod.fst pairEq).symm, afterEq.symm.trans transition.2.2⟩

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

theorem bounded_relation_runs (input : Inputs) (sumCorrect : input.expected = input.left + input.right)
    (hleft : input.left ≤ 255) (hright : input.right ≤ 255) :
    Circuit.run context boundedRelation (inputEnvironment input) =
      .ok [("result", .uint 510 input.expected)] := by
  have expectedBound : input.expected ≤ 510 := by
    rw [sumCorrect]
    calc
      input.left + input.right ≤ 255 + 255 := Nat.add_le_add hleft hright
      _ = 510 := by decide
  have expectedField : input.expected < Field.modulus := Nat.lt_of_le_of_lt expectedBound (by decide)
  have leftField : input.left < Field.modulus := Nat.lt_of_le_of_lt hleft (by decide)
  have rightField : input.right < Field.modulus := Nat.lt_of_le_of_lt hright (by decide)
  have expectedEval := expected_expression_eval input expectedBound
  have sumEval := sum_expression_eval input hleft hright
  have firstEval : (sumExpression.eq sumExpression).eval context (inputEnvironment input) =
      .ok _root_.Bool.true := by
    simp only [sumExpression, Expr.eval, sumEval, Except.bind, Bind.bind]
    change (Except.ok (input.left + input.right == input.left + input.right) : Except String _root_.Bool) =
      Except.ok _root_.Bool.true
    simp
  have secondEval : (sumExpression.eq (Expr.ref "expected")).eval context (inputEnvironment input) =
      .ok (input.left + input.right == input.expected) := by
    simp only [sumExpression, Expr.eval, sumEval, expectedEval, Except.bind, Bind.bind]
    rfl
  have constraintsAccepted : runConstraints context (inputEnvironment input)
      relationConstraints = .ok () := by
    simp [relationConstraints, runConstraints, firstEval, secondEval, sumCorrect]
  have sourceConstraintsAccepted :
      runConstraints
        { modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused" }
        [("expected", .uint 510 input.expected), ("left", .uint 255 input.left),
         ("right", .uint 255 input.right)]
        [((Expr.ref "left" : Expr (.uint 255)).uadd (Expr.ref "right" : Expr (.uint 255))).eq
            ((Expr.ref "left" : Expr (.uint 255)).uadd (Expr.ref "right" : Expr (.uint 255))),
         ((Expr.ref "left" : Expr (.uint 255)).uadd (Expr.ref "right" : Expr (.uint 255))).eq
            (Expr.ref "expected" : Expr (.uint 510))] = .ok () := by
    simpa [context, inputEnvironment, relationConstraints, sumExpression] using constraintsAccepted
  have expectedEvalSource :
      Expr.eval { modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused" }
        [("expected", .uint 510 input.expected), ("left", .uint 255 input.left),
         ("right", .uint 255 input.right)] (Expr.ref "expected" : Expr (.uint 510)) =
          .ok input.expected := by
    simpa [context, inputEnvironment] using expectedEval
  have namesUnique : uniqueNames ["expected", "left", "right"] = _root_.Bool.true := by decide
  unfold Circuit.run
  rw [relation_validates]
  simp [context, boundedRelation, namesUnique,
    List.lookup, Value.as, canonical_eq, ScalarPolicy.maxUint, ScalarPolicy.maxBits,
    inputEnvironment, sourceConstraintsAccepted, expectedEvalSource, Value.pack,
    expectedBound, hleft, hright, expectedField, leftField, rightField]
  rfl

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

theorem successful_apply_run_from_acceptance (input : Inputs) (total : Nat)
    (outputs : EvalEnv) (after : LedgerState) (totalBound : total ≤ 510)
    (expectedBound : input.expected ≤ 510) (leftBound : input.left ≤ 255)
    (rightBound : input.right ≤ 255)
    (success : applyEntry.run context (inputEnvironment input) (state total) =
      .ok (outputs, after)) :
    input.expected = input.left + input.right ∧ total = 0 ∧
      outputs = [("result", .uint 510 input.expected)] ∧ after = state input.expected := by
  have originalSuccess := success
  unfold Entrypoint.run at success
  rw [apply_disclosure] at success
  cases circuitRun : applyEntry.circuit.run context (inputEnvironment input) with
  | error message => simp [circuitRun, Except.bind, Bind.bind] at success
  | ok circuitOutputs =>
    have actualCircuit : Circuit.run context boundedRelation (inputEnvironment input) =
        .ok circuitOutputs := by
      simpa [applyEntry, BoundedScalars] using circuitRun
    have accepted := bounded_relation_accepts input circuitOutputs expectedBound
      leftBound rightBound actualCircuit
    have exactCircuit : Circuit.run context boundedRelation (inputEnvironment input) =
        .ok [("result", .uint 510 input.expected)] := by
      rw [accepted.2] at actualCircuit
      exact actualCircuit
    exact ⟨accepted.1, successful_apply_run input total outputs after totalBound
      expectedBound exactCircuit originalSuccess⟩

theorem successful_apply_private_observation (left right : Inputs) (total : Nat)
    (leftOutputs rightOutputs : EvalEnv) (leftAfter rightAfter : LedgerState)
    (samePublic : left.expected = right.expected) (totalBound : total ≤ 510)
    (leftExpectedBound : left.expected ≤ 510) (rightExpectedBound : right.expected ≤ 510)
    (leftBound : left.left ≤ 255) (leftRightBound : left.right ≤ 255)
    (rightBound : right.left ≤ 255) (rightRightBound : right.right ≤ 255)
    (leftRun : applyEntry.run context (inputEnvironment left) (state total) =
      .ok (leftOutputs, leftAfter))
    (rightRun : applyEntry.run context (inputEnvironment right) (state total) =
      .ok (rightOutputs, rightAfter)) :
    (leftOutputs, leftAfter) = (rightOutputs, rightAfter) := by
  have leftResult := successful_apply_run_from_acceptance left total leftOutputs leftAfter
    totalBound leftExpectedBound leftBound leftRightBound leftRun
  have rightResult := successful_apply_run_from_acceptance right total rightOutputs rightAfter
    totalBound rightExpectedBound rightBound rightRightBound rightRun
  rw [leftResult.2.2.1, leftResult.2.2.2, rightResult.2.2.1, rightResult.2.2.2, samePublic]

theorem apply_effects_run (input : Inputs) (expectedBound : input.expected ≤ 510) :
    runEffectsWithGuardsAndEnv context applyEntry.effects applyEntry.effectGuards
      ([ ("result", .uint 510 input.expected) ] ++ inputEnvironment input) (state 0) =
    .ok (("old", .uint 510 0) :: ([ ("result", .uint 510 input.expected) ] ++ inputEnvironment input),
      state input.expected) := by
  rw [apply_effects_shape, apply_guards_shape]
  change runEffectsWithEnv context applyEffects
      ([ ("result", .uint 510 input.expected) ] ++ inputEnvironment input) (state 0) = _
  rw [SourceEffects.runEffectsWithEnv_eq_fold, applyEffects]
  let initialEnv := [("result", .uint 510 input.expected)] ++ inputEnvironment input
  let readEnv := ("old", .uint 510 0) :: initialEnv
  have readStep : SourceEffects.step context (.readCell "total" "old" (.uint 510))
      (initialEnv, state 0) = .ok (readEnv, state 0) := by
    simp [readEnv, initialEnv, SourceEffects.step, runEffectWithEnv, state,
      canonical_eq, context, ScalarPolicy.maxUint, ScalarPolicy.maxBits,
      Field.modulus, Value.as, Value.pack, pure, Except.pure]
  have resultLookup : readEnv.lookup "result" = some (.uint 510 input.expected) := by
    simp [readEnv, initialEnv, inputEnvironment, List.lookup]
  have resultEval : (Expr.ref "result" : Expr (.uint 510)).eval context readEnv =
      .ok input.expected := by
    rw [Expr.eval, resultLookup]
    have expectedField : input.expected < Field.modulus :=
      Nat.lt_of_le_of_lt expectedBound (by decide)
    simp [Value.as, canonical_eq, context, ScalarPolicy.maxUint,
      ScalarPolicy.maxBits, expectedBound, expectedField, pure, Except.pure]
  have castEval : (Expr.cast .native (Expr.ref "old" : Expr (.uint 510))).eval
      context readEnv = .ok 0 := by
    with_unfolding_all rfl
  have conditionEval :
      ((Expr.cast .native (Expr.ref "old" : Expr (.uint 510))).eq (Expr.native 0)).eval
        context readEnv = .ok _root_.Bool.true := by
    simp only [Expr.eval, castEval]
    rfl
  have requireStep : SourceEffects.step context
      (.require ((Expr.cast .native (Expr.ref "old" : Expr (.uint 510))).eq (Expr.native 0)))
      (readEnv, state 0) = .ok (readEnv, state 0) := by
    simp [SourceEffects.step, runEffectWithEnv, conditionEval, Except.bind, Bind.bind,
      pure, Except.pure]
  have writeStep : SourceEffects.step context
      (.writeCell "total" (.uint 510) (Expr.ref "result"))
      (readEnv, state 0) = .ok (readEnv, state input.expected) := by
    simp [SourceEffects.step, runEffectWithEnv, resultEval, state, updateAssoc,
      Value.pack, Value.as, pure, Except.pure, Except.bind, Bind.bind]
  change SourceEffects.fold context
    [.readCell "total" "old" (.uint 510),
     .require ((Expr.cast .native (Expr.ref "old" : Expr (.uint 510))).eq (Expr.native 0)),
     .writeCell "total" (.uint 510) (Expr.ref "result")]
    (initialEnv, state 0) = _
  rw [SourceEffects.fold_cons, readStep, Except.bind,
    SourceEffects.fold_cons, requireStep, Except.bind,
    SourceEffects.fold_cons, writeStep, Except.bind, SourceEffects.fold_nil]

theorem apply_runs_when_enabled (input : Inputs)
    (sumCorrect : input.expected = input.left + input.right)
    (hleft : input.left ≤ 255) (hright : input.right ≤ 255) :
    applyEntry.run context (inputEnvironment input) (state 0) =
      .ok ([ ("result", .uint 510 input.expected) ], state input.expected) := by
  have expectedBound : input.expected ≤ 510 := by
    rw [sumCorrect]
    calc
      input.left + input.right ≤ 255 + 255 := Nat.add_le_add hleft hright
      _ = 510 := by decide
  have circuitSuccess := bounded_relation_runs input sumCorrect hleft hright
  have effectsSuccess := apply_effects_run input expectedBound
  have entryCircuit : applyEntry.circuit.run context (inputEnvironment input) =
      .ok [("result", .uint 510 input.expected)] := by
    simpa [applyEntry, BoundedScalars] using circuitSuccess
  have effectsSuccess' : runEffectsWithGuardsAndEnv context applyEntry.effects applyEntry.effectGuards
      ([ ("result", .uint 510 input.expected) ] ++ inputEnvironment input)
      { cells := [("total", .uint 510 0)] } =
      .ok (("old", .uint 510 0) :: ([ ("result", .uint 510 input.expected) ] ++ inputEnvironment input),
        state input.expected) := by
    simpa [state] using effectsSuccess
  unfold Entrypoint.run
  rw [apply_disclosure]
  rw [entryCircuit]
  simp only [Except.bind, Bind.bind]
  simp only [state]
  rw [effectsSuccess']
  simp [applyEntry, BoundedScalars, state, pure, Except.pure]

theorem apply_success_iff (input : Inputs) (total : Nat) (outputs : EvalEnv)
    (after : LedgerState) (totalBound : total ≤ 510) (expectedBound : input.expected ≤ 510)
    (leftBound : input.left ≤ 255) (rightBound : input.right ≤ 255) :
    applyEntry.run context (inputEnvironment input) (state total) = .ok (outputs, after) ↔
      input.expected = input.left + input.right ∧ total = 0 ∧
        outputs = [("result", .uint 510 input.expected)] ∧ after = state input.expected := by
  constructor
  · exact successful_apply_run_from_acceptance input total outputs after totalBound
      expectedBound leftBound rightBound
  · rintro ⟨sumCorrect, totalZero, outputEq, stateEq⟩
    rw [totalZero, outputEq, stateEq]
    exact apply_runs_when_enabled input sumCorrect leftBound rightBound

theorem sample_circuit_run :
    Circuit.run context boundedRelation (inputEnvironment ⟨5, 2, 3⟩) =
      .ok [("result", .uint 510 5)] := by
  with_unfolding_all rfl

theorem sample_apply_run :
    applyEntry.run context (inputEnvironment ⟨5, 2, 3⟩) (state 0) =
      .ok ([("result", .uint 510 5)], state 5) := by
  with_unfolding_all rfl

def initial (before : LedgerState) : Prop := before = state 0

def invariant (before : LedgerState) : Prop :=
  ∃ total, total ≤ 510 ∧ before = state total

def precondition (ctx : EvalContext) (inputs : EvalEnv) (_before : LedgerState) : Prop :=
  ctx = context ∧ ∃ input, inputs = inputEnvironment input ∧
    input.expected ≤ 510 ∧ input.left ≤ 255 ∧ input.right ≤ 255

def enabled (_ctx : EvalContext) (inputs : EvalEnv) (before : LedgerState) : Prop :=
  before = state 0 ∧ ∃ input, inputs = inputEnvironment input ∧
    input.expected = input.left + input.right ∧ input.left ≤ 255 ∧ input.right ≤ 255

def postcondition (_ctx : EvalContext) (inputs : EvalEnv) (before : LedgerState)
    (outputs : EvalEnv) (after : LedgerState) : Prop :=
  ∃ input, inputs = inputEnvironment input ∧ input.expected = input.left + input.right ∧
    before = state 0 ∧ outputs = [("result", .uint 510 input.expected)] ∧
    after = state input.expected

def specification : Specification := { initial, invariant, precondition, enabled, postcondition }

def subject : Subject := { contract := BoundedScalars, entrypoint := ⟨0, by decide⟩, specification }

private theorem subject_entry : subject.entry = applyEntry := by rfl

def policy : AuditPolicy := {
  subject
  privacy := { releases := .none, scope := .successfulOnly }
  functionalGuarantee := "For canonical bounded inputs and a canonical total cell, accepted apply runs start from zero, return the exact sum, and set total to that value. Every enabled run succeeds."
  privacyGuarantee := "Successful source outcomes have equal returned values and ledger state for equal public expected input, context, and starting state."
}

theorem sample_nonvacuity : ∃ ctx inputs before,
    initial before ∧ precondition ctx inputs before ∧ enabled ctx inputs before := by
  let sample : Inputs := ⟨5, 2, 3⟩
  refine ⟨context, inputEnvironment sample, state 0, rfl, ?_, ?_⟩
  · exact ⟨rfl, sample, rfl, by decide, by decide, by decide⟩
  · exact ⟨rfl, sample, rfl, by decide, by decide, by decide⟩

theorem functional : FunctionalObligation policy := by
  change Correctness subject
  constructor
  · intro before started
    exact ⟨0, by decide, started⟩
  · intro ctx inputs before outputs after canonical pre success
    change invariant before at canonical
    change precondition ctx inputs before at pre
    rcases canonical with ⟨total, totalBound, stateEq⟩
    rcases pre with ⟨contextEq, input, inputsEq, expectedBound, leftBound, rightBound⟩
    subst ctx inputs before
    obtain ⟨sumCorrect, totalZero, resultEq, afterEq⟩ :=
      successful_apply_run_from_acceptance input total outputs after totalBound
        expectedBound leftBound rightBound success
    exact ⟨⟨input, rfl, sumCorrect, congrArg state totalZero, resultEq, afterEq⟩,
      input.expected, expectedBound, afterEq⟩
  · intro ctx inputs before _canonical pre active
    change precondition ctx inputs before at pre
    change enabled ctx inputs before at active
    rcases active with ⟨beforeEq, input, inputsEq, sumCorrect, leftBound, rightBound⟩
    have contextEq := pre.1
    subst ctx inputs before
    exact ⟨[("result", .uint 510 input.expected)], state input.expected,
      apply_runs_when_enabled input sumCorrect leftBound rightBound⟩
  · exact sample_nonvacuity

private theorem actual_public_inputs (input : Inputs) :
    subject.publicInputs (inputEnvironment input) =
      [("expected", some (.uint 510 input.expected))] := by rfl

theorem privacy : PrivacyObligation policy := by
  intro left right leftAdmissible rightAdmissible equivalent _releaseAgreement covered
  rcases left with ⟨leftContext, leftInputs, leftState⟩
  rcases right with ⟨rightContext, rightInputs, rightState⟩
  change invariant leftState ∧ precondition leftContext leftInputs leftState at leftAdmissible
  change invariant rightState ∧ precondition rightContext rightInputs rightState at rightAdmissible
  change leftContext = rightContext ∧ leftState = rightState ∧
    subject.publicInputs leftInputs = subject.publicInputs rightInputs at equivalent
  rcases equivalent with ⟨_sameContext, sameState, publicInputsEqual⟩
  rcases leftAdmissible.1 with ⟨total, totalBound, leftStateEq⟩
  have rightStateEq := sameState.symm.trans leftStateEq
  rcases leftAdmissible.2 with
    ⟨leftContextEq, leftInput, leftInputsEq, leftExpectedBound, leftBound, leftRightBound⟩
  rcases rightAdmissible.2 with
    ⟨rightContextEq, rightInput, rightInputsEq, rightExpectedBound, rightBound, rightRightBound⟩
  have publicHeadEqual :
      some ("expected", some (Value.uint 510 leftInput.expected)) =
        some ("expected", some (Value.uint 510 rightInput.expected)) := by
    simpa [leftInputsEq, rightInputsEq, actual_public_inputs] using
      congrArg List.head? publicInputsEqual
  have expectedEqual : leftInput.expected = rightInput.expected := by
    have valuesEqual := congrArg Prod.snd (Option.some.inj publicHeadEqual)
    exact (Value.uint.inj (Option.some.inj valuesEqual)).2
  subst leftContext rightContext leftInputs rightInputs leftState rightState
  simp only [policy, ObservationScope.covers, Subject.execute, subject_entry] at covered
  rcases covered with ⟨⟨leftOutputs, leftAfter, leftRun⟩, ⟨rightOutputs, rightAfter, rightRun⟩⟩
  have observation := successful_apply_private_observation leftInput rightInput total
    leftOutputs rightOutputs leftAfter rightAfter expectedEqual totalBound
    leftExpectedBound rightExpectedBound leftBound leftRightBound rightBound rightRightBound
    leftRun rightRun
  change subject.entry.run context (inputEnvironment leftInput) (state total) =
    subject.entry.run context (inputEnvironment rightInput) (state total)
  rw [subject_entry, leftRun, rightRun]
  exact congrArg Except.ok observation

#noctium_register_functional functional for policy
#noctium_register_privacy privacy for policy

#print axioms functional
#print axioms privacy

end Noctium.BoundedScalarsVerification
