import Noctium.Verification.GenericStateInputValues
import Noctium.Verification.GenericStateExpressionScope

namespace Noctium.Verification.GenericStatePrefixEnvironment
open Backend.Native NativeRelation ScalarNormalization

/-- The source evaluator's current bindings agree with the complete relation
candidate environment on every name admitted at this effect prefix. -/
def AgreesOnTypes (types : TypeEnv) (current complete : EvalEnv) : Prop :=
  ∀ name ty, types.lookup name = some ty →
    current.lookup name = complete.lookup name

theorem AgreesOnTypes.named (types : TypeEnv) (current complete : EvalEnv)
    (agrees : AgreesOnTypes types current complete) :
    ∀ name ∈ types.map Prod.fst,
      current.lookup name = complete.lookup name := by
  intro name member
  obtain ⟨pair, present, same⟩ := List.mem_map.mp member
  cases found : types.lookup name with
  | some ty => exact agrees name ty found
  | none =>
    have different := List.lookup_eq_none_iff.mp found pair present
    simp [same] at different

theorem eval_scoped (types : TypeEnv) (current complete : EvalEnv)
    (agrees : AgreesOnTypes types current complete)
    (ctx : EvalContext) (caps : Capabilities) (expression : Expr ty)
    (valid : expression.validate caps types = .ok ()) :
    expression.eval ctx current = expression.eval ctx complete := by
  exact GenericStateExpressionScope.eval_agree_of_valid expression caps types
    ctx current complete valid (agrees.named types current complete)

theorem initial_agreement (types : TypeEnv) (current future : EvalEnv)
    (present : ∀ name ty, types.lookup name = some ty →
      ∃ value, current.lookup name = some value) :
    AgreesOnTypes types current (current ++ future) := by
  intro name ty typed
  obtain ⟨value, found⟩ := present name ty typed
  simp [List.lookup_append, found]

theorem initial_from_typed (hash : Hash) (witness : Assignment)
    (aliases : AliasEnvironment) (types : TypeEnv)
    (current future : EvalEnv)
    (environment : TypedEnvironment hash witness aliases current types) :
    AgreesOnTypes types current (current ++ future) := by
  apply initial_agreement types current future
  intro name ty typed
  obtain ⟨raw, _, found, _⟩ := environment.complete name ty typed
  exact ⟨raw, found⟩

/-- A fresh source read binds the authenticated candidate at the front of
the source environment while the validator appends its type at the end. -/
theorem extend_read (types : TypeEnv) (current complete : EvalEnv)
    (name : String) (ty : Ty) (value : Value)
    (agrees : AgreesOnTypes types current complete)
    (fresh : types.lookup name = none)
    (candidate : complete.lookup name = some value) :
    AgreesOnTypes (types ++ [(name, ty)])
      ((name, value) :: current) complete := by
  intro found foundTy typed
  by_cases same : found = name
  · subst found
    simp [List.lookup_append, fresh] at typed
    simp [List.lookup_cons, candidate]
  · have unequal : (found == name) = false := by simp [same]
    simp only [List.lookup_append, List.lookup_cons, unequal,
      List.lookup_nil, Option.or_none] at typed
    simp only [List.lookup_cons, unequal]
    exact agrees found foundTy typed

/-- A freshly named read keeps the exact decoded binding when appended after
the source input and output bindings. -/
theorem candidate_read_lookup (base decoded : EvalEnv)
    (reads : List Backend.Impact.Read) (witness : Assignment)
    (success : GenericStateInputValues.decodeReads reads witness = .ok decoded)
    (distinct : reads.Pairwise (fun left right => left.name ≠ right.name))
    (read : Backend.Impact.Read) (member : read ∈ reads)
    (fresh : base.lookup read.name = none) :
    ∃ supported : ScalarType read.ty,
      (base ++ decoded).lookup read.name = some (Value.pack read.ty
        (GenericStateInputValues.sourceValue supported
          (witness ("%input_" ++ read.name)))) := by
  rw [List.lookup_append, fresh]
  exact GenericStateInputValues.decodeReads_lookup reads witness decoded success distinct read member

/-- Non-read effects keep the same source environment and scope. -/
theorem preserve (types : TypeEnv) (current complete : EvalEnv)
    (agrees : AgreesOnTypes types current complete) :
    AgreesOnTypes types current complete := agrees

end Noctium.Verification.GenericStatePrefixEnvironment
