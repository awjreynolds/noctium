import examples.openzeppelin.ConfidentialToken
import Noctium.Semantics
import Lean

open Lean Elab Tactic

/-- `scalarCast` and `scalarNumber` are private in the evaluator module. Add
their actual environment declarations to the simplifier so the checked proof
can reduce the exact source cast without changing production visibility. -/
elab "unfold_semantics_scalar_helpers" : tactic => do
  let env ← getEnv
  let mut simpTheorems ← Meta.getSimpTheorems
  for (name, _) in env.constants.toList do
    if name.toString.endsWith "Noctium.scalarCast" ||
        name.toString.endsWith "Noctium.scalarNumber" then
      simpTheorems := simpTheorems.addDeclToUnfoldCore name
  let congrTheorems ← Meta.getSimpCongrTheorems
  let context ← Meta.Simp.mkContext
    (simpTheorems := #[simpTheorems]) (congrTheorems := congrTheorems)
  let goal ← getMainGoal
  let (goal?, _) ← Meta.simpTarget goal context
  replaceMainGoal goal?.toList

namespace OpenZeppelinPort.ConfidentialTokenMintSupply

open Noctium

/-- The actual `mint` entry in ConfidentialToken, selected by its source index. -/
def mintEntry : Entrypoint :=
  OpenZeppelinPort.ConfidentialToken.entrypoints[1]'(by decide)

def uint128Max : Nat := 2 ^ 128 - 1

def supplyWriteSpan : SourceSpan := {
  file := "examples/openzeppelin/ConfidentialToken.lean"
  line := 610
  column := 26
}

def mintSupplyRead : Effect :=
  .readCell "totalSupply" "oldSupply" (.uint uint128Max)

def mintSupplyWriteValue : Expr (.uint uint128Max) :=
  .disclose supplyWriteSpan
    (.cast (.uint uint128Max)
      (.uadd
        (.ref "oldSupply" : Expr (.uint uint128Max))
        (.ref "value" : Expr (.uint uint128Max))))

def mintSupplyWrite : Effect :=
  .writeCell "totalSupply" (.uint uint128Max) mintSupplyWriteValue

def mintSupplySuffix : List Effect := [mintSupplyRead, mintSupplyWrite]

/-- The checked entrypoint ends with exactly the supply read and widened,
checked UInt128 write. -/
theorem mint_supply_suffix_is_actual_source :
    mintEntry.effects.drop (mintEntry.effects.length - 2) = mintSupplySuffix := by
  unfold mintEntry mintSupplySuffix mintSupplyRead mintSupplyWrite mintSupplyWriteValue
  with_unfolding_all rfl

/-- `mint` has no committed call arguments or grouped call-input views. This
records the empty call interface that blocks composing the local supply suffix
into a joint claimMint proof. It does not claim the ledger entry has no circuit
inputs or native effects. -/
theorem mint_empty_committed_call_interface :
    mintEntry.callInputs = [] ∧ mintEntry.callInputViews = [] ∧
      mintEntry.callArguments = [] := by
  constructor
  · unfold mintEntry
    with_unfolding_all rfl
  constructor
  · unfold mintEntry
    with_unfolding_all rfl
  · unfold mintEntry
    with_unfolding_all rfl

/-- A successful local suffix replaces only the totalSupply cell. The state
argument represents the ledger after the entrypoint's guarded prefix. -/
def supplyUpdatedState (state : LedgerState) (newSupply : Nat) : LedgerState :=
  { state with cells := updateAssoc "totalSupply" (.uint uint128Max newSupply) state.cells }

def supplyInputEnv (value : Nat) : EvalEnv :=
  [("value", .uint uint128Max value)]

theorem uint128_model_bounds :
    uint128Max ≤ ScalarPolicy.maxUint ∧
    2 * uint128Max ≤ ScalarPolicy.maxUint ∧
    uint128Max < Field.modulus := by
  decide

private theorem sum_le_wide_max (supply value : Nat)
    (supplyBound : supply ≤ uint128Max) (valueBound : value ≤ uint128Max) :
    supply + value ≤ 2 * uint128Max := by omega

private theorem sum_lt_native (supply value : Nat)
    (supplyBound : supply ≤ uint128Max) (valueBound : value ≤ uint128Max) :
    supply + value < Field.modulus := by
  have wide := sum_le_wide_max supply value supplyBound valueBound
  have wideNative := Nat.lt_of_le_of_lt uint128_model_bounds.2.1 ScalarPolicy.maxUint_lt_native
  exact Nat.lt_of_le_of_lt wide wideNative

private theorem supplyAddExpressionEval (ctx : EvalContext) (env : EvalEnv)
    (supply value : Nat)
    (modulus : ctx.modulus = Field.modulus)
    (oldSupplyInput : env.lookup "oldSupply" = some (.uint uint128Max supply))
    (valueInput : env.lookup "value" = some (.uint uint128Max value))
    (supplyBound : supply ≤ uint128Max)
    (valueBound : value ≤ uint128Max) :
    mintSupplyWriteValue.eval ctx env =
      if supply + value ≤ uint128Max then .ok (supply + value)
      else .error "scalar conversion exceeds unsigned bound" := by
  have wide := sum_le_wide_max supply value supplyBound valueBound
  have sumField := sum_lt_native supply value supplyBound valueBound
  have supplyField : supply < ctx.modulus := by
    rw [modulus]
    exact Nat.lt_of_le_of_lt supplyBound uint128_model_bounds.2.2
  have valueField : value < ctx.modulus := by
    rw [modulus]
    exact Nat.lt_of_le_of_lt valueBound uint128_model_bounds.2.2
  have uint128Policy := uint128_model_bounds.1
  have widePolicy := uint128_model_bounds.2.1
  have wideCastBound : uint128Max + uint128Max ≤ ScalarPolicy.maxUint := by
    simpa [Nat.two_mul] using widePolicy
  have sumWideBound : supply + value ≤ uint128Max + uint128Max := by
    calc
      supply + value ≤ 2 * uint128Max := wide
      _ = uint128Max + uint128Max := by omega
  have supplyNoOver : ¬ uint128Max < supply := Nat.not_lt_of_ge supplyBound
  have valueNoOver : ¬ uint128Max < value := Nat.not_lt_of_ge valueBound
  have supplyNotMod : ¬ Field.modulus ≤ supply := Nat.not_le_of_gt (by
    rw [← modulus]
    exact supplyField)
  have valueNotMod : ¬ Field.modulus ≤ value := Nat.not_le_of_gt (by
    rw [← modulus]
    exact valueField)
  by_cases fits : supply + value ≤ uint128Max
  · unfold mintSupplyWriteValue
    simp [Expr.eval, Ty.isBytes, Ty.isJubjub, Ty.isForeign, oldSupplyInput,
      valueInput, Value.as, canonical_eq, modulus, uint128Policy,
      supplyNotMod, valueNotMod, supplyNoOver, valueNoOver, fits] <;>
      unfold_semantics_scalar_helpers
    simp_all
    change Except.ok (supply + value) = Except.ok (supply + value)
    rfl
  · unfold mintSupplyWriteValue
    simp [Expr.eval, Ty.isBytes, Ty.isJubjub, Ty.isForeign, oldSupplyInput,
      valueInput, Value.as, canonical_eq, modulus, uint128Policy,
      supplyNotMod, valueNotMod, supplyNoOver, valueNoOver, fits] <;>
      unfold_semantics_scalar_helpers
    have notFits : ¬ supply + value ≤ uint128Max := by omega
    simp_all
    intro h
    exfalso
    omega

private theorem mintSupplyRead_eval (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (supply : Nat)
    (modulus : ctx.modulus = Field.modulus)
    (supplyCell : state.cells.lookup "totalSupply" = some (.uint uint128Max supply))
    (supplyBound : supply ≤ uint128Max) :
    runEffectWithEnv ctx mintSupplyRead env state =
      .ok ( ("oldSupply", .uint uint128Max supply) :: env, state) := by
  have supplyField : supply < Field.modulus := by
    exact Nat.lt_of_le_of_lt supplyBound uint128_model_bounds.2.2
  simp [runEffectWithEnv, mintSupplyRead, supplyCell, Value.as,
    canonical_eq, modulus, supplyBound, uint128_model_bounds.1,
    supplyField]
  change Except.ok (("oldSupply", .uint uint128Max supply) :: env, state) =
    Except.ok (("oldSupply", .uint uint128Max supply) :: env, state)
  rfl

private theorem mintSupplyWrite_eval (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (supply value : Nat)
    (supplyCell : state.cells.lookup "totalSupply" = some (.uint uint128Max supply))
    (expressionEval : Expr.eval ctx env mintSupplyWriteValue = .ok value) :
    runEffectWithEnv ctx mintSupplyWrite env state =
      .ok (env, supplyUpdatedState state value) := by
  simp [runEffectWithEnv, mintSupplyWrite, supplyUpdatedState,
    supplyCell, Value.as, expressionEval]
  change Except.ok (env, supplyUpdatedState state value) =
    Except.ok (env, supplyUpdatedState state value)
  rfl

/-- The actual final supply suffix adds canonical UInt128 operands without
wrapping. If the sum fits UInt128, it returns the exact mathematical sum and
frames every other entering ledger field. -/
theorem mint_supply_suffix_representable
    (ctx : EvalContext) (env : EvalEnv) (state : LedgerState)
    (supply value : Nat)
    (modulus : ctx.modulus = Field.modulus)
    (supplyCell : state.cells.lookup "totalSupply" = some (.uint uint128Max supply))
    (valueInput : env.lookup "value" = some (.uint uint128Max value))
    (supplyBound : supply ≤ uint128Max)
    (valueBound : value ≤ uint128Max)
    (representable : supply + value ≤ uint128Max) :
    runEffectsWithEnv ctx mintSupplySuffix env state =
      .ok (("oldSupply", .uint uint128Max supply) :: env,
        supplyUpdatedState state (supply + value)) := by
  have expressionEval := supplyAddExpressionEval ctx
    (("oldSupply", .uint uint128Max supply) :: env) supply value modulus
    (by simp [List.lookup]) (by simp [List.lookup, valueInput]) supplyBound valueBound
  have readResult := mintSupplyRead_eval ctx env state supply modulus supplyCell supplyBound
  have writeResult := mintSupplyWrite_eval ctx
    (("oldSupply", .uint uint128Max supply) :: env) state supply (supply + value)
    supplyCell (by simpa [representable] using expressionEval)
  simp only [runEffectsWithEnv, mintSupplySuffix, List.foldlM]
  rw [readResult]
  simp [Bind.bind, Except.bind, writeResult]
  change Except.ok (("oldSupply", .uint uint128Max supply) :: env,
    supplyUpdatedState state (supply + value)) =
    Except.ok (("oldSupply", .uint uint128Max supply) :: env,
      supplyUpdatedState state (supply + value))
  rfl

/-- Overflow is rejected by the final UInt128 cast. The evaluator returns no
successor state when the widened sum exceeds the UInt128 maximum. -/
theorem mint_supply_suffix_overflow
    (ctx : EvalContext) (env : EvalEnv) (state : LedgerState)
    (supply value : Nat)
    (modulus : ctx.modulus = Field.modulus)
    (supplyCell : state.cells.lookup "totalSupply" = some (.uint uint128Max supply))
    (valueInput : env.lookup "value" = some (.uint uint128Max value))
    (supplyBound : supply ≤ uint128Max)
    (valueBound : value ≤ uint128Max)
    (overflow : uint128Max < supply + value) :
    runEffectsWithEnv ctx mintSupplySuffix env state =
      .error "scalar conversion exceeds unsigned bound" := by
  have expressionEval := supplyAddExpressionEval ctx
    (("oldSupply", .uint uint128Max supply) :: env) supply value modulus
    (by simp [List.lookup]) (by simp [List.lookup, valueInput]) supplyBound valueBound
  have readResult := mintSupplyRead_eval ctx env state supply modulus supplyCell supplyBound
  have writeError :
      runEffectWithEnv ctx mintSupplyWrite
        (("oldSupply", .uint uint128Max supply) :: env) state =
        .error "scalar conversion exceeds unsigned bound" := by
    have notFits : ¬ supply + value ≤ uint128Max := by omega
    simp [runEffectWithEnv, mintSupplyWrite, supplyCell, Value.as,
      expressionEval, notFits] <;> rfl
  simp only [runEffectsWithEnv, mintSupplySuffix, List.foldlM]
  rw [readResult]
  simp [Bind.bind, Except.bind, writeError]

def supplyContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .ok 0
}

def supplyState (supply : Nat) : LedgerState := {
  cells := [("totalSupply", .uint uint128Max supply)]
}

/-- The last representable addition reaches UInt128 max exactly. -/
theorem mint_supply_boundary_sum_succeeds :
    runEffectsWithEnv supplyContext mintSupplySuffix (supplyInputEnv 1)
      (supplyState (uint128Max - 1)) =
      .ok ([("oldSupply", .uint uint128Max (uint128Max - 1)),
        ("value", .uint uint128Max 1)], supplyState uint128Max) := by
  have run := mint_supply_suffix_representable supplyContext (supplyInputEnv 1)
    (supplyState (uint128Max - 1)) (uint128Max - 1) 1 rfl (by simp [supplyState])
    (by simp [supplyInputEnv]) (by simp [uint128Max]) (by simp [uint128Max])
    (by simp [uint128Max])
  simpa [supplyContext, supplyInputEnv, supplyState, supplyUpdatedState,
    updateAssoc, uint128Max] using run

/-- Adding zero at the maximum remains representable. -/
theorem mint_supply_max_plus_zero_succeeds :
    runEffectsWithEnv supplyContext mintSupplySuffix (supplyInputEnv 0)
      (supplyState uint128Max) =
      .ok ([("oldSupply", .uint uint128Max uint128Max),
        ("value", .uint uint128Max 0)], supplyState uint128Max) := by
  have run := mint_supply_suffix_representable supplyContext (supplyInputEnv 0)
    (supplyState uint128Max) uint128Max 0 rfl (by simp [supplyState])
    (by simp [supplyInputEnv]) (by simp [uint128Max]) (by simp [uint128Max])
    (by simp [uint128Max])
  simpa [supplyContext, supplyInputEnv, supplyState, supplyUpdatedState,
    updateAssoc, uint128Max] using run

/-- One above the maximum is rejected at the first overflow boundary. -/
theorem mint_supply_first_overflow_rejects :
    runEffectsWithEnv supplyContext mintSupplySuffix (supplyInputEnv 1)
      (supplyState uint128Max) =
      .error "scalar conversion exceeds unsigned bound" := by
  exact mint_supply_suffix_overflow supplyContext (supplyInputEnv 1)
    (supplyState uint128Max) uint128Max 1 rfl (by simp [supplyState])
    (by simp [supplyInputEnv]) (by simp [uint128Max]) (by simp [uint128Max])
    (by simp [uint128Max])

end OpenZeppelinPort.ConfidentialTokenMintSupply
