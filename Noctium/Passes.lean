import Noctium.Semantics

namespace Noctium.Passes

/-- Remove only literal true constraints. No evaluation, hash oracle, field
identity, or target capability assumption is needed. -/
def pruneCircuit (c : Circuit) : Circuit :=
  {c with constraints := pruneTrue c.constraints}

theorem prune_validation (caps : Capabilities) (env : TypeEnv) (span : SourceSpan)
    (conditions : List (Expr .bool)) :
    validateConstraints caps env span (pruneTrue conditions) =
      validateConstraints caps env span conditions := by
  induction conditions with
  | nil => rfl
  | cons condition rest ih =>
    cases condition with
    | bool b => cases b <;> simp [pruneTrue, validateConstraints, Expr.validate, ih]
    | boolAnd left right => simp only [pruneTrue, validateConstraints, ih]
    | boolOr left right => simp only [pruneTrue, validateConstraints, ih]
    | boolXor left right => simp only [pruneTrue, validateConstraints, ih]
    | copyValue value => simp only [pruneTrue, validateConstraints, ih]
    | ref name => simp only [pruneTrue, validateConstraints, ih]
    | eq a b => simp only [pruneTrue, validateConstraints, ih]
    | select condition a b => simp only [pruneTrue, validateConstraints, ih]
    | cast target value => simp only [pruneTrue, validateConstraints, ih]
    | letE name value body => simp only [pruneTrue, validateConstraints, ih]
    | assertE condition body => simp only [pruneTrue, validateConstraints, ih]
    | disclose span value => simp only [pruneTrue, validateConstraints, ih]
    | inv value => simp only [pruneTrue, validateConstraints, ih]
    | fromBytes32 value => simp only [pruneTrue, validateConstraints, ih]
    | fromBytes value => simp only [pruneTrue, validateConstraints, ih]

theorem prune_evaluation (ctx : EvalContext) (env : EvalEnv)
    (conditions : List (Expr .bool)) :
    runConstraints ctx env (pruneTrue conditions) = runConstraints ctx env conditions := by
  induction conditions with
  | nil => rfl
  | cons condition rest ih =>
    cases condition with
    | bool b => cases b <;> simp [pruneTrue, runConstraints, Expr.eval, ih]
    | boolAnd left right => simp only [pruneTrue, runConstraints, ih]
    | boolOr left right => simp only [pruneTrue, runConstraints, ih]
    | boolXor left right => simp only [pruneTrue, runConstraints, ih]
    | copyValue value => simp only [pruneTrue, runConstraints, ih]
    | ref name => simp only [pruneTrue, runConstraints, ih]
    | eq a b => simp only [pruneTrue, runConstraints, ih]
    | select condition a b => simp only [pruneTrue, runConstraints, ih]
    | cast target value => simp only [pruneTrue, runConstraints, ih]
    | letE name value body => simp only [pruneTrue, runConstraints, ih]
    | assertE condition body => simp only [pruneTrue, runConstraints, ih]
    | disclose span value => simp only [pruneTrue, runConstraints, ih]
    | inv value => simp only [pruneTrue, runConstraints, ih]
    | fromBytes32 value => simp only [pruneTrue, runConstraints, ih]
    | fromBytes value => simp only [pruneTrue, runConstraints, ih]

theorem pruneCircuit_validate (caps : Capabilities) (c : Circuit) :
    (pruneCircuit c).validate caps = c.validate caps := by
  simp only [Circuit.validate, pruneCircuit, prune_validation]
  rfl

theorem prune_disclosure_constraints (env : Disclosure.Environment) (span : SourceSpan)
    (conditions : List (Expr .bool)) :
    Disclosure.checkConstraints env span (pruneTrue conditions) =
      Disclosure.checkConstraints env span conditions := by
  induction conditions with
  | nil => rfl
  | cons condition rest ih =>
    cases condition with
    | bool b => cases b <;> simp [pruneTrue, Disclosure.checkConstraints_literal, ih]
    | boolAnd left right => simp only [pruneTrue, Disclosure.checkConstraints, ih]
    | boolOr left right => simp only [pruneTrue, Disclosure.checkConstraints, ih]
    | boolXor left right => simp only [pruneTrue, Disclosure.checkConstraints, ih]
    | copyValue value => simp only [pruneTrue, Disclosure.checkConstraints, ih]
    | ref name => simp only [pruneTrue, Disclosure.checkConstraints, ih]
    | eq a b => simp only [pruneTrue, Disclosure.checkConstraints, ih]
    | select condition a b => simp only [pruneTrue, Disclosure.checkConstraints, ih]
    | cast target value => simp only [pruneTrue, Disclosure.checkConstraints, ih]
    | letE name value body => simp only [pruneTrue, Disclosure.checkConstraints, ih]
    | assertE condition body => simp only [pruneTrue, Disclosure.checkConstraints, ih]
    | disclose span value => simp only [pruneTrue, Disclosure.checkConstraints, ih]
    | inv value => simp only [pruneTrue, Disclosure.checkConstraints, ih]
    | fromBytes32 value => simp only [pruneTrue, Disclosure.checkConstraints, ih]
    | fromBytes value => simp only [pruneTrue, Disclosure.checkConstraints, ih]

theorem pruneCircuit_disclosure (c : Circuit) (control : Disclosure.Origins) :
    Disclosure.circuit (pruneCircuit c) control = Disclosure.circuit c control := by
  simp only [Disclosure.circuit, pruneCircuit, prune_disclosure_constraints]
  rfl

/-- Complete executable semantics equality includes input validation, exact errors,
constraint failure order, hash-oracle errors, and named outputs. -/
theorem pruneCircuit_run (ctx : EvalContext) (env : EvalEnv) (c : Circuit) :
    (pruneCircuit c).run ctx env = c.run ctx env := by
  unfold Circuit.run
  rw [pruneCircuit_validate]
  simp only [pruneCircuit, prune_evaluation]
  rfl

/-- Preserve state effects verbatim while optimizing the associated relation. -/
def pruneEntrypoint (entry : Entrypoint) : Entrypoint :=
  {entry with circuit := pruneCircuit entry.circuit}

theorem pruneEntrypoint_disclosure (entry : Entrypoint) (control : Disclosure.Origins) :
    Disclosure.entrypoint (pruneEntrypoint entry) control = Disclosure.entrypoint entry control := by
  unfold Disclosure.entrypoint
  dsimp only [pruneEntrypoint]
  rw [pruneCircuit_disclosure]
  rfl

set_option maxHeartbeats 1000000 in
theorem pruneEntrypoint_validate (caps : Capabilities) (state : List StateDecl) (entry : Entrypoint) :
    (pruneEntrypoint entry).validate caps state = entry.validate caps state := by
  unfold Entrypoint.validate
  dsimp only [pruneEntrypoint]
  simp only [pruneCircuit_validate]
  rfl

theorem pruneEntrypoint_run (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (entry : Entrypoint) :
    (pruneEntrypoint entry).run ctx env state = entry.run ctx env state := by
  unfold Entrypoint.run
  rw [pruneEntrypoint_disclosure]
  dsimp only [pruneEntrypoint]
  rw [pruneCircuit_run]

end Noctium.Passes
