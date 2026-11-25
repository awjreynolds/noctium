import Noctium.Verification.ImpactExpressionEvaluation

namespace Noctium.Verification.ImpactExpressionComparison

open Lean ImpactExpressionNode ImpactExpressionEvaluation

/-- Compare ordered bindings without comparing their JSON representation. -/
private def bindingsMatch (compare : Json → Json → Bool) :
    List (String × Json) → List (String × Json) → Bool
  | [], [] => true
  | (leftName, leftValue) :: leftTail, (rightName, rightValue) :: rightTail =>
      (leftName == rightName) && compare leftValue rightValue &&
        bindingsMatch compare leftTail rightTail
  | _, _ => false

/-- Compare two decoded nodes using the supplied recursive child comparison. -/
private def nodeMatches (compare : Json → Json → Bool) : Node → Node → Bool
  | .native left, .native right => left == right
  | .bool left, .bool right => left == right
  | .uint leftMaximum leftValue, .uint rightMaximum rightValue =>
      (leftMaximum == rightMaximum) && (leftValue == rightValue)
  | .reference left, .reference right => left == right
  | .binary leftOp leftA leftB, .binary rightOp rightA rightB =>
      decide (leftOp = rightOp) && compare leftA rightA && compare leftB rightB
  | .unsigned leftOp leftMaximum leftA leftB,
    .unsigned rightOp rightMaximum rightA rightB =>
      decide (leftOp = rightOp) && (leftMaximum == rightMaximum) &&
        compare leftA rightA && compare leftB rightB
  | .cast leftTarget leftValue, .cast rightTarget rightValue =>
      (leftTarget == rightTarget) && compare leftValue rightValue
  | .bind leftBindings leftBody, .bind rightBindings rightBody =>
      bindingsMatch compare leftBindings rightBindings && compare leftBody rightBody
  | .assertThen leftCondition leftBody, .assertThen rightCondition rightBody =>
      compare leftCondition rightCondition && compare leftBody rightBody
  | .select leftCondition leftYes leftNo, .select rightCondition rightYes rightNo =>
      compare leftCondition rightCondition && compare leftYes rightYes &&
        compare leftNo rightNo
  | .poseidon2 leftDomain leftA leftB, .poseidon2 rightDomain rightA rightB =>
      (leftDomain == rightDomain) && compare leftA rightA && compare leftB rightB
  | _, _ => false

/-- Return true when both expressions decode and have the same ordered,
recursively compared structure within the supplied depth bound. -/
def «matches» : Nat → Json → Json → Bool
  | 0, _, _ => false
  | budget + 1, left, right =>
      match decode left, decode right with
      | .ok leftNode, .ok rightNode => nodeMatches («matches» budget) leftNode rightNode
      | _, _ => false

private theorem bindingsMatch_evaluateBindings
    (budget : Nat) (run : Runner)
    (run_agrees : ∀ left right, «matches» budget left right = true →
      ∀ env, run env left = run env right)
    (env : EvalEnv) {left right : List (String × Json)}
    (matched : bindingsMatch («matches» budget) left right = true) :
    evaluateBindings run env left = evaluateBindings run env right := by
  induction left generalizing right env with
  | nil =>
      cases right <;> simp [bindingsMatch] at matched ⊢
  | cons leftHead leftTail ih =>
      cases leftHead with
      | mk leftName leftValue =>
          cases right with
          | nil => simp [bindingsMatch] at matched
          | cons rightHead rightTail =>
              cases rightHead with
              | mk rightName rightValue =>
                  change ((leftName == rightName) &&
                    («matches» budget leftValue rightValue) &&
                    bindingsMatch («matches» budget) leftTail rightTail) = true at matched
                  rcases Bool.and_eq_true_iff.mp matched with ⟨nameValueMatched, tailMatched⟩
                  rcases Bool.and_eq_true_iff.mp nameValueMatched with
                    ⟨nameMatched, valueMatched⟩
                  have namesEqual : leftName = rightName := by
                    exact beq_iff_eq.mp nameMatched
                  subst rightName
                  have valuesEqual := run_agrees leftValue rightValue valueMatched env
                  have evaluatedRight : run env rightValue = run env leftValue :=
                    valuesEqual.symm
                  cases evaluated : run env leftValue with
                  | none =>
                      simp [evaluateBindings, evaluated, evaluatedRight]
                  | some value =>
                      have evaluatedRightValue : run env rightValue = some value := by
                        rw [evaluatedRight, evaluated]
                      simp [evaluateBindings, evaluated, evaluatedRightValue]
                      exact ih ((leftName, value) :: env) tailMatched

private theorem nodeMatches_evaluateNode
    (budget fuel : Nat) (ctx : EvalContext)
    (children_agree : ∀ {left right}, «matches» budget left right = true →
      ∀ env, evaluate fuel ctx env left = evaluate fuel ctx env right)
    (env : EvalEnv) {left right : Node}
    (matched : nodeMatches («matches» budget) left right = true) :
    evaluateNode ctx (evaluate fuel ctx) env left =
      evaluateNode ctx (evaluate fuel ctx) env right := by
  cases left with
  | native leftValue =>
      cases right with
      | native rightValue =>
          simp only [nodeMatches] at matched
          simp [evaluateNode, beq_iff_eq.mp matched]
      | _ => simp [nodeMatches] at matched
  | bool leftValue =>
      cases right with
      | bool rightValue =>
          simp only [nodeMatches] at matched
          simp [evaluateNode, beq_iff_eq.mp matched]
      | _ => simp [nodeMatches] at matched
  | uint leftMaximum leftValue =>
      cases right with
      | uint rightMaximum rightValue =>
          change (leftMaximum == rightMaximum && leftValue == rightValue) = true at matched
          rcases Bool.and_eq_true_iff.mp matched with ⟨maximumMatched, valueMatched⟩
          simp [evaluateNode, beq_iff_eq.mp maximumMatched, beq_iff_eq.mp valueMatched]
      | _ => simp [nodeMatches] at matched
  | reference leftName =>
      cases right with
      | reference rightName =>
          simp only [nodeMatches] at matched
          simp [evaluateNode, beq_iff_eq.mp matched]
      | _ => simp [nodeMatches] at matched
  | binary leftOp leftA leftB =>
      cases right with
      | binary rightOp rightA rightB =>
          change (decide (leftOp = rightOp) && «matches» budget leftA rightA &&
            «matches» budget leftB rightB) = true at matched
          rcases Bool.and_eq_true_iff.mp matched with ⟨opAndLeft, rightMatched⟩
          rcases Bool.and_eq_true_iff.mp opAndLeft with ⟨opMatched, leftMatched⟩
          have opEqual : leftOp = rightOp := of_decide_eq_true opMatched
          subst rightOp
          have leftEqual := children_agree leftMatched env
          have rightEqual := children_agree rightMatched env
          cases leftOp <;> simp [evaluateNode, leftEqual, rightEqual]
      | _ => simp [nodeMatches] at matched
  | unsigned leftOp leftMaximum leftA leftB =>
      cases right with
      | unsigned rightOp rightMaximum rightA rightB =>
          change (decide (leftOp = rightOp) && leftMaximum == rightMaximum &&
            «matches» budget leftA rightA && «matches» budget leftB rightB) = true at matched
          rcases Bool.and_eq_true_iff.mp matched with ⟨prefixMatched, rightMatched⟩
          rcases Bool.and_eq_true_iff.mp prefixMatched with ⟨prefixMatched, leftMatched⟩
          rcases Bool.and_eq_true_iff.mp prefixMatched with ⟨opMatched, maximumMatched⟩
          have opEqual : leftOp = rightOp := of_decide_eq_true opMatched
          have maximumEqual : leftMaximum = rightMaximum := beq_iff_eq.mp maximumMatched
          subst rightOp
          subst rightMaximum
          have leftEqual := children_agree leftMatched env
          have rightEqual := children_agree rightMatched env
          simp [evaluateNode, leftEqual, rightEqual]
      | _ => simp [nodeMatches] at matched
  | cast leftTarget leftValue =>
      cases right with
      | cast rightTarget rightValue =>
          change (leftTarget == rightTarget && «matches» budget leftValue rightValue) = true at matched
          rcases Bool.and_eq_true_iff.mp matched with ⟨targetMatched, valueMatched⟩
          have targetEqual : leftTarget = rightTarget := beq_iff_eq.mp targetMatched
          subst rightTarget
          have valueEqual := children_agree valueMatched env
          simp [evaluateNode, valueEqual]
      | _ => simp [nodeMatches] at matched
  | bind leftBindings leftBody =>
      cases right with
      | bind rightBindings rightBody =>
          change (bindingsMatch («matches» budget) leftBindings rightBindings &&
            «matches» budget leftBody rightBody) = true at matched
          rcases Bool.and_eq_true_iff.mp matched with ⟨bindingsMatched, bodyMatched⟩
          have bindingsEqual := bindingsMatch_evaluateBindings budget
            (evaluate fuel ctx)
            (fun left right childMatched childEnv => children_agree childMatched childEnv)
            env bindingsMatched
          have bodyEqual := children_agree bodyMatched
          simp [evaluateNode, bindingsEqual, bodyEqual]
      | _ => simp [nodeMatches] at matched
  | assertThen leftCondition leftBody =>
      cases right with
      | assertThen rightCondition rightBody =>
          change («matches» budget leftCondition rightCondition &&
            «matches» budget leftBody rightBody) = true at matched
          rcases Bool.and_eq_true_iff.mp matched with ⟨conditionMatched, bodyMatched⟩
          have conditionEqual := children_agree conditionMatched env
          have bodyEqual := children_agree bodyMatched env
          simp [evaluateNode, conditionEqual, bodyEqual]
      | _ => simp [nodeMatches] at matched
  | select leftCondition leftYes leftNo =>
      cases right with
      | select rightCondition rightYes rightNo =>
          change («matches» budget leftCondition rightCondition &&
            «matches» budget leftYes rightYes && «matches» budget leftNo rightNo) = true at matched
          rcases Bool.and_eq_true_iff.mp matched with ⟨conditionAndYes, noMatched⟩
          rcases Bool.and_eq_true_iff.mp conditionAndYes with ⟨conditionMatched, yesMatched⟩
          have conditionEqual := children_agree conditionMatched env
          have yesEqual := children_agree yesMatched env
          have noEqual := children_agree noMatched env
          simp [evaluateNode, conditionEqual, yesEqual, noEqual]
      | _ => simp [nodeMatches] at matched
  | poseidon2 leftDomain leftA leftB =>
      cases right with
      | poseidon2 rightDomain rightA rightB =>
          change (leftDomain == rightDomain && «matches» budget leftA rightA &&
            «matches» budget leftB rightB) = true at matched
          rcases Bool.and_eq_true_iff.mp matched with ⟨domainAndLeft, rightMatched⟩
          rcases Bool.and_eq_true_iff.mp domainAndLeft with ⟨domainMatched, leftMatched⟩
          have domainEqual : leftDomain = rightDomain := beq_iff_eq.mp domainMatched
          subst rightDomain
          have leftEqual := children_agree leftMatched env
          have rightEqual := children_agree rightMatched env
          simp [evaluateNode, leftEqual, rightEqual]
      | _ => simp [nodeMatches] at matched

/-- A successful comparison preserves the evaluator result, including
rejections, at every fuel amount and in every context and environment. -/
theorem evaluate_eq_of_matches {budget : Nat} {left right : Json}
    (matched : «matches» budget left right = true) (fuel : Nat)
    (ctx : EvalContext) (env : EvalEnv) :
    ImpactExpressionEvaluation.evaluate fuel ctx env left =
      ImpactExpressionEvaluation.evaluate fuel ctx env right := by
  induction fuel generalizing budget left right ctx env with
  | zero => simp [ImpactExpressionEvaluation.evaluate]
  | succ fuel ih =>
      cases budget with
      | zero => simp [«matches»] at matched
      | succ budget =>
          cases leftDecoded : decode left with
          | error message => simp [«matches», leftDecoded] at matched
          | ok leftNode =>
              cases rightDecoded : decode right with
              | error message => simp [«matches», leftDecoded, rightDecoded] at matched
              | ok rightNode =>
                  have nodesMatched : nodeMatches («matches» budget) leftNode rightNode = true := by
                    simpa [«matches», leftDecoded, rightDecoded] using matched
                  rw [evaluate_decoded fuel ctx env leftDecoded,
                    evaluate_decoded fuel ctx env rightDecoded]
                  exact nodeMatches_evaluateNode budget fuel ctx
                    (fun {childLeft} {childRight} childMatched childEnv =>
                      ih (budget := budget) childMatched ctx childEnv)
                    env nodesMatched

end Noctium.Verification.ImpactExpressionComparison
