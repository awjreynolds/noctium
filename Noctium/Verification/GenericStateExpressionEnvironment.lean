import Noctium.Semantics

namespace Noctium.Verification.GenericStateExpressionEnvironment

open Noctium

private abbrev Agreement (ty : Ty) (expression : Expr ty) : Prop :=
  ∀ (ctx : EvalContext) (left right : EvalEnv),
    (∀ name, left.lookup name = right.lookup name) →
    expression.eval ctx left = expression.eval ctx right

private theorem forIn_equal {α β : Type} (values : List α) (initial : β)
    (leftStep rightStep : α → β → Except String (ForInStep β))
    (agree : ∀ value ∈ values, ∀ state, leftStep value state = rightStep value state) :
    forIn values initial leftStep = forIn values initial rightStep := by
  simpa only [forIn'_eq_forIn] using
    (List.forIn'_congr (as := values) (bs := values) rfl (b := initial) (b' := initial) rfl
      (f := fun value _ state => leftStep value state)
      (g := fun value _ state => rightStep value state) agree)

set_option maxHeartbeats 500000 in
private theorem eval_agreements (ty : Ty) (expression : Expr ty) : Agreement ty expression := by
  apply Expr.rec (motive_1 := Agreement)
    (motive_2 := fun values => ∀ expression ∈ values, Agreement _ expression)
    (motive_3 := fun values => ∀ expression ∈ values, Agreement _ expression)
    (motive_4 := fun values => ∀ expression ∈ values, Agreement expression.1 expression.2)
    (motive_5 := fun expression => Agreement expression.1 expression.2)
  all_goals first | rfl | skip
  all_goals try (simp only [Agreement] at *; intros; first | rfl | (simp only [Expr.eval] <;> grind))

  case toBytes32 =>
    intro ty value ih ctx left right agreed
    cases ty <;> simp [Expr.eval, ih ctx left right agreed]
  case fromBytes32 =>
    intro ty value ih ctx left right agreed
    cases ty <;> simp [Expr.eval, ih ctx left right agreed]
  case fromBytes =>
    intro ty length value ih ctx left right agreed
    cases ty <;> simp [Expr.eval, ih ctx left right agreed]
  case inv =>
    intro ty value ih ctx left right agreed
    cases ty <;> simp [Expr.eval, ih ctx left right agreed]
  case foreignBinary =>
    intro operation a b iha ihb ctx left right agreed
    simp [Expr.eval, iha ctx left right agreed, ihb ctx left right agreed]

  case persistentHashVector32 | persistentHashNativeVector | hashToCurve | transientHash =>
    intro values ih ctx left right agreed
    simp only [Expr.eval]
    split
    · rfl
    · congr 1
      apply forIn_equal
      intro value member state
      rw [ih value member ctx left right agreed]
  case hashToCurveFab =>
    intro environment type values ih ctx left right agreed
    exact Expr.eval_hashToCurveFab_env_congr ctx left right environment type values
      (fun item member => ih item member ctx left right agreed)
  case transientHashFab =>
    intro environment type values ih ctx left right agreed
    exact Expr.eval_transientHashFab_env_congr ctx left right environment type values
      (fun item member => ih item member ctx left right agreed)
  case persistentHashFab =>
    intro environment type values ih ctx left right agreed
    exact Expr.eval_persistentHashFab_env_congr ctx left right environment type values
      (fun item member => ih item member ctx left right agreed)
  case sha512Fab =>
    intro environment type values ih ctx left right agreed
    exact Expr.eval_sha512Fab_env_congr ctx left right environment type values
      (fun item member => ih item member ctx left right agreed)
  case keccak256Fab =>
    intro environment type values ih ctx left right agreed
    exact Expr.eval_keccak256Fab_env_congr ctx left right environment type values
      (fun item member => ih item member ctx left right agreed)
  case persistentCommitFab =>
    intro environment type opening values ihOpening ih ctx left right agreed
    exact Expr.eval_persistentCommitFab_env_congr ctx left right environment type opening values
      (ihOpening ctx left right agreed) (fun item member => ih item member ctx left right agreed)
  case transientCommitFab =>
    intro environment type opening values ihOpening ih ctx left right agreed
    exact Expr.eval_transientCommitFab_env_congr ctx left right environment type opening values
      (ihOpening ctx left right agreed) (fun item member => ih item member ctx left right agreed)
  all_goals
    first
    | intro item member
      simp at member
    | intro head tail ihHead ihTail item member
      rcases List.mem_cons.mp member with rfl | present
      · exact ihHead
      · exact ihTail item present
    | intro ty value ih
      exact ih

/-- Evaluation depends only on first-match value lookup, including under
local let bindings, eager branches, and aggregate expression evaluation. -/
theorem eval_lookup_ext (ctx : EvalContext) (expression : Expr ty)
    (left right : EvalEnv)
    (agreement : ∀ name, left.lookup name = right.lookup name) :
    expression.eval ctx left = expression.eval ctx right := by
  exact eval_agreements ty expression ctx left right agreement

end Noctium.Verification.GenericStateExpressionEnvironment
