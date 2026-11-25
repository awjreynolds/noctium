import Noctium.Verification.GenericStateMapReadAuthentication
import Noctium.Verification.GuardedScalarInput
import Noctium.Verification.GuardedScalarTotalization

namespace Noctium.Verification.GuardedMapReadAuthentication
open Backend NativeRelation NativeState ScalarNormalization

private theorem guarded_chunk (ctx : EvalContext) (env : EvalEnv)
    (state : List StateDecl) (name destination : String) (keyTy valueTy : Ty) (key : Expr keyTy)
    (admitted : ScalarExpression key) (guard : Expr .bool) (before after : Impact.Plan)
    (active : guard.eval ctx env = .ok true) (modulus : ctx.modulus = Field.modulus)
    (compiled : Impact.appendEffectWithActivity state (.readMap name destination keyTy valueTy key)
      (some guard) before = .ok after) :
    ∃ emittedKey : Expr keyTy, emittedKey.eval ctx env = key.eval ctx env ∧ ∃ raw,
      Impact.appendEffect state (.readMap name destination keyTy valueTy emittedKey)
        before = .ok raw ∧ after.operations = raw.operations := by
  obtain ⟨scalarType⟩ := GenericStateEvaluationCanonical.scalarExpression_type admitted
  have nonForeign : ∀ kind, keyTy ≠ .foreign kind := by cases scalarType <;> simp
  obtain ⟨binder, fresh, raw, appended, sameOps⟩ := Impact.appendEffectWithActivity_readMap_key
    state name destination keyTy valueTy key guard before after nonForeign compiled
  exact ⟨_, GuardedScalarTotalization.eval_active_value ctx env key admitted guard
      binder fresh active modulus,
    raw, appended, sameOps⟩

/-- An active guarded Map read authenticates the actual native read against
its current source Map, including when the emitted key was totalized. -/
theorem active_readMap_candidate_source_step (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name destination : String) (keyTy valueTy : Ty) (key : Expr keyTy)
    (keyAdmission : ScalarExpression key)
    (keyAgreement : key.eval ctx sourceEnv = key.eval ctx candidateEnv)
    (guard : Expr .bool) (active : guard.eval ctx sourceEnv = .ok true)
    (guardAgreement : guard.eval ctx sourceEnv = guard.eval ctx candidateEnv)
    (candidate : valueTy.Denote) (before plan : Impact.Plan)
    (segment : List NativeState.Op) (reads : List NativeState.Cell) (after : NativeState.Machine)
    (compiled : Impact.appendEffectWithActivity state (.readMap name destination keyTy valueTy key)
      (some guard) before = .ok plan)
    (declaration : StateDecl) (declared : state.find? (·.name == name) = some declaration)
    (kind : declaration.kind = .map keyTy valueTy)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (lookup : candidateEnv.lookup destination = some (Value.pack valueTy candidate))
    (canonical : Canonical valueTy candidate) (modulus : ctx.modulus = Field.modulus)
    (evaluated : (plan.operations.drop before.operations.length).mapM
      (GenericStateOps.evalOp ctx candidateEnv) = .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after) :
    runEffectsWithGuardsAndEnv ctx [.readMap name destination keyTy valueTy key] [some guard]
      sourceEnv current = .ok ((destination, Value.pack valueTy candidate) :: sourceEnv, current) ∧
    after = ⟨[.vector slots], reads ++ [field (scalar (GenericStateEncoding.number valueTy candidate))]⟩ := by
  obtain ⟨emittedKey, keyEval, raw, appended, sameOps⟩ := guarded_chunk ctx candidateEnv state
    name destination keyTy valueTy key keyAdmission guard before plan (guardAgreement.symm.trans active)
    modulus compiled
  rw [sameOps] at evaluated
  obtain ⟨valueSupport⟩ := GenericStateWriteEvaluation.scalarType_of_canonical canonical
  rw [GuardedScalarInput.run_active_map_read ctx sourceEnv current name destination
    key valueSupport guard active]
  exact GenericStateMapReadAuthentication.readMap_chunk_source_step ctx sourceEnv candidateEnv
    state current slots name destination keyTy valueTy key emittedKey keyAdmission
    (keyAgreement.trans keyEval.symm) candidate before raw segment reads after appended
    declaration declared kind encoded lookup canonical modulus evaluated checked

/-- A successful active source Map read determines the exact emitted native
chunk and the unchanged encoded root with its appended scalar read. -/
theorem source_active_readMap_emitted (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name destination : String) (keyTy valueTy : Ty) (key : Expr keyTy)
    (keyAdmission : ScalarExpression key) (valueSupport : ScalarType valueTy)
    (keyAgreement : key.eval ctx candidateEnv = key.eval ctx sourceEnv)
    (guard : Expr .bool) (active : guard.eval ctx sourceEnv = .ok true)
    (guardAgreement : guard.eval ctx sourceEnv = guard.eval ctx candidateEnv)
    (sourceAfter : SourceEffects.Frame) (before plan : Impact.Plan) (reads : List NativeState.Cell)
    (sourceStep : runEffectsWithGuardsAndEnv ctx [.readMap name destination keyTy valueTy key]
      [some guard] sourceEnv current = .ok sourceAfter)
    (candidateLookup : candidateEnv.lookup destination = sourceAfter.1.lookup destination)
    (compiled : Impact.appendEffectWithActivity state (.readMap name destination keyTy valueTy key)
      (some guard) before = .ok plan)
    (declaration : StateDecl) (declared : state.find? (·.name == name) = some declaration)
    (kind : declaration.kind = .map keyTy valueTy)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ (slot : Nat) (resolved : keyTy.Denote) (value : valueTy.Denote),
      state.findIdx? (·.name == name) = some slot ∧
      (plan.operations.drop before.operations.length).mapM (GenericStateOps.evalOp ctx candidateEnv) =
        .ok (GenericStateVM.readMapOps slot (scalar (GenericStateEncoding.number keyTy resolved))
          (scalar (GenericStateEncoding.number valueTy value))) ∧
      NativeState.run (GenericStateVM.readMapOps slot (scalar (GenericStateEncoding.number keyTy resolved))
        (scalar (GenericStateEncoding.number valueTy value))) ⟨[.vector slots], reads⟩ =
          some ⟨[.vector slots], reads ++ [field (scalar (GenericStateEncoding.number valueTy value))]⟩ ∧
      sourceAfter = ((destination, Value.pack valueTy value) :: sourceEnv, current) := by
  obtain ⟨emittedKey, keyEval, raw, appended, sameOps⟩ := guarded_chunk ctx candidateEnv state
    name destination keyTy valueTy key keyAdmission guard before plan (guardAgreement.symm.trans active)
    modulus compiled
  rw [sameOps]
  rw [GuardedScalarInput.run_active_map_read ctx sourceEnv current name destination
    key valueSupport guard active] at sourceStep
  exact GenericStateMapReadAuthentication.source_readMap_chunk ctx sourceEnv candidateEnv
    state current slots name destination keyTy valueTy key emittedKey keyAdmission
    (keyEval.trans keyAgreement) sourceAfter before raw reads sourceStep candidateLookup
    appended declaration declared kind encoded modulus

end Noctium.Verification.GuardedMapReadAuthentication
