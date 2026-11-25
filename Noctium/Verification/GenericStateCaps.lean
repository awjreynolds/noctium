import Noctium.IR

namespace Noctium.Verification.GenericStateCaps

private theorem type_validate_state_caps (caps : Capabilities) (ty : Ty) :
    ty.validate {caps with stateCells := true, stateMaps := true} =
      ty.validate {caps with stateCells := false, stateMaps := false} := by rfl

private noncomputable def validationTaskSize :
    (ty : Ty) ×' (_ : TypeEnv) ×' Expr ty ⊕' (_ : TypeEnv) ×' List (Sigma Expr) → Nat
  | .inl ⟨_, ⟨_, expression⟩⟩ => sizeOf expression
  | .inr ⟨_, values⟩ => sizeOf values

private theorem validation_task_state_caps (caps : Capabilities)
    (task : (ty : Ty) ×' (_ : TypeEnv) ×' Expr ty ⊕' (_ : TypeEnv) ×' List (Sigma Expr)) :
    Expr.validate._mutual {caps with stateCells := true, stateMaps := true} task =
      Expr.validate._mutual {caps with stateCells := false, stateMaps := false} task := by
  apply WellFounded.induction (measure validationTaskSize).wf task
  intro task smaller
  have smaller' (child : (ty : Ty) ×' (_ : TypeEnv) ×' Expr ty ⊕' (_ : TypeEnv) ×' List (Sigma Expr))
      (bound : validationTaskSize child < validationTaskSize task) :=
    smaller child (by change validationTaskSize child < validationTaskSize task; exact bound)
  cases task with
  | inl input =>
    cases input with
    | mk ty input =>
      cases input with
      | mk env expression =>
        cases expression <;>
          rw [Expr.validate._mutual.eq_1, Expr.validate._mutual.eq_1]
        all_goals first
          | rfl
          | simp (discharger := {
              try simp [validationTaskSize, WellFoundedRelation.rel, measure]
              try simp_wf
              all_goals first
                | have _h := Noctium.sizeOfSigmaExprMemberLt (by assumption); omega
                | have _h := Noctium.sizeOfSigmaExprHeadLt _ _; omega
                | have _h := Noctium.sizeOfMemberListLt (by assumption); omega
                | omega
                | skip })
              [type_validate_state_caps, validationTaskSize, smaller', Except.bind]
  | inr input =>
    cases input with
    | mk env values =>
      cases values with
      | nil => rfl
      | cons head tail =>
        cases head with
        | mk ty expression =>
          rw [Expr.validate._mutual.eq_1, Expr.validate._mutual.eq_1]
          first
          | rfl
          | simp (discharger := {
              try simp [validationTaskSize, WellFoundedRelation.rel, measure]
              try simp_wf
              all_goals first
                | have _h := Noctium.sizeOfSigmaExprMemberLt (by assumption); omega
                | have _h := Noctium.sizeOfSigmaExprHeadLt _ _; omega
                | have _h := Noctium.sizeOfMemberListLt (by assumption); omega
                | omega
                | skip })
              [type_validate_state_caps, validationTaskSize, smaller', Except.bind]

private theorem expr_validate_state_caps (caps : Capabilities) (expression : Expr ty) (env : TypeEnv) :
    expression.validate {caps with stateCells := true, stateMaps := true} env =
      expression.validate {caps with stateCells := false, stateMaps := false} env := by
  calc
    _ = Expr.validate._mutual {caps with stateCells := true, stateMaps := true}
        (PSum.inl ⟨ty, ⟨env, expression⟩⟩) := by with_unfolding_all rfl
    _ = Expr.validate._mutual {caps with stateCells := false, stateMaps := false} (PSum.inl ⟨ty, ⟨env, expression⟩⟩) :=
      validation_task_state_caps caps (PSum.inl ⟨ty, ⟨env, expression⟩⟩)
    _ = _ := by with_unfolding_all rfl

private theorem constraints_validate_state_caps (caps : Capabilities) (env : TypeEnv)
    (span : SourceSpan) (conditions : List (Expr .bool)) :
    validateConstraints {caps with stateCells := true, stateMaps := true}
      env span conditions =
    validateConstraints {caps with stateCells := false, stateMaps := false} env span conditions := by
  induction conditions with
  | nil => rfl
  | cons condition rest ih =>
    simp [validateConstraints, expr_validate_state_caps, ih]

/-- Ledger capability flags do not affect a circuit's own type checks.
The production entrypoint validator enables those flags for state effects. -/
theorem circuit_validate_state_flags (caps : Capabilities) (circuit : Circuit) :
    circuit.validate {caps with stateCells := true, stateMaps := true} =
      circuit.validate {caps with stateCells := false, stateMaps := false} := by
  unfold Circuit.validate
  simp [type_validate_state_caps, expr_validate_state_caps,
    constraints_validate_state_caps]

theorem circuit_validate_state_caps (circuit : Circuit) :
    circuit.validate {poseidon2 := true, stateCells := true, stateMaps := true} =
      circuit.validate {poseidon2 := true} :=
  circuit_validate_state_flags {poseidon2 := true} circuit

theorem circuit_validate_source_crypto (circuit : Circuit) :
    circuit.validate Capabilities.source = circuit.validate Capabilities.crypto :=
  circuit_validate_state_flags Capabilities.crypto circuit

end Noctium.Verification.GenericStateCaps
