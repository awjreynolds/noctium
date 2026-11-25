import Noctium.Verification.GenericStatePrefixEnvironment
import Noctium.Verification.ScalarCircuit

namespace Noctium.Verification.ScalarLedgerSourceReturns

open Backend.Native NativeRelation ScalarNormalization

private theorem bind_ok {α β : Type} {first : Except String α}
    {next : α → Except String β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem evalReturns_fold (ctx : EvalContext) (entry : Entrypoint)
    (outputs : List Output) (values result : EvalEnv)
    (success : Entrypoint.evalReturns ctx {entry with returns := outputs} values = .ok result) :
    outputs.mapM (evalOutput ctx values) = .ok result := by
  induction outputs generalizing result with
  | nil =>
    change (Except.ok [] : Except String EvalEnv) = .ok result at success
    cases success
    rfl
  | cons output rest ih =>
    simp only [Entrypoint.evalReturns, List.mapM_cons, bind_ok] at success
    obtain ⟨head, headSuccess, tail, tailSuccess, resultAccepted⟩ := success
    have headEval : evalOutput ctx values output = .ok head := by
      rcases headSuccess with ⟨value, evaluated, packed⟩
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at packed
      split at packed
      · simp at packed
      · have pairShape : head = (output.name, Value.pack output.ty value) :=
          (Except.ok.inj packed).symm
        simp [evalOutput, evaluated, pairShape, Bind.bind, Except.bind,
          Pure.pure, Except.pure]
    have tailEval : rest.mapM (evalOutput ctx values) = .ok tail :=
      ih tail (by
        change Entrypoint.evalReturns ctx {entry with returns := rest} values = .ok tail
        exact tailSuccess)
    have resultShape : result = head :: tail := by
      simpa [Pure.pure, Except.pure] using (Except.ok.inj resultAccepted).symm
    subst result
    simp only [List.mapM_cons, headEval, tailEval]
    rfl

/-- Successful source returns keep their evaluated values and order when
transported to a typed candidate environment that agrees on every declared
return name. -/
theorem evalReturns_transport (ctx : EvalContext) (entry : Entrypoint)
    (sourceEnv complete : EvalEnv) (types : TypeEnv) (result : EvalEnv)
    (agrees : GenericStatePrefixEnvironment.AgreesOnTypes types sourceEnv complete)
    (valid : ∀ output ∈ entry.returns,
      output.value.validate Capabilities.crypto types = .ok ())
    (success : Entrypoint.evalReturns ctx entry sourceEnv = .ok result) :
    entry.returns.mapM (evalOutput ctx complete) = .ok result := by
  have sameFold : entry.returns.mapM (evalOutput ctx complete) =
      entry.returns.mapM (evalOutput ctx sourceEnv) := by
    have outputsAgree (outputs : List Output)
        (valid : ∀ output ∈ outputs,
          output.value.validate Capabilities.crypto types = .ok ()) :
        outputs.mapM (evalOutput ctx complete) = outputs.mapM (evalOutput ctx sourceEnv) := by
      induction outputs with
    | nil => rfl
    | cons output rest ih =>
      have head := GenericStatePrefixEnvironment.eval_scoped types sourceEnv complete agrees
        ctx Capabilities.crypto output.value (valid output (by simp))
      have tailValid : ∀ returned ∈ rest,
          returned.value.validate Capabilities.crypto types = .ok () := by
        intro returned member
        exact valid returned (List.mem_cons_of_mem _ member)
      simp only [List.mapM_cons]
      rw [show evalOutput ctx complete output = evalOutput ctx sourceEnv output by
        simp [evalOutput, head]]
      rw [ih tailValid]
    exact outputsAgree entry.returns valid
  rw [sameFold]
  exact evalReturns_fold ctx entry entry.returns sourceEnv result success

end Noctium.Verification.ScalarLedgerSourceReturns
