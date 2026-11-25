import Noctium.Verification.GenericStateMapReadEvaluation
import Noctium.Verification.GenericStateSchemaSpans
import Noctium.Verification.GenericStateEvaluationCanonical
import Noctium.Verification.GenericStateWriteInversion
import Noctium.Verification.GenericStateInputValues
import Noctium.Verification.GuardedEffectPrefix

namespace Noctium.Verification.GenericStateMapReadAuthentication

open Backend NativeRelation NativeState ScalarNormalization GenericStateInputValues

/-- A checked raw Map-read chunk authenticates the typed candidate against
the current source map when the emitted key has the source key semantics. -/
theorem readMap_chunk_source_step (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name destination : String) (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (emittedKey : Expr keyTy) (keyAdmission : ScalarExpression keyExpr)
    (keyAgreement : keyExpr.eval ctx sourceEnv = emittedKey.eval ctx candidateEnv)
    (candidate : valueTy.Denote) (before plan : Impact.Plan)
    (segment : List NativeState.Op) (reads : List NativeState.Cell)
    (after : NativeState.Machine)
    (compiled : Impact.appendEffect state (.readMap name destination keyTy valueTy emittedKey)
      before = .ok plan)
    (declaration : StateDecl)
    (declared : state.find? (·.name == name) = some declaration)
    (kind : declaration.kind = .map keyTy valueTy)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (lookup : candidateEnv.lookup destination = some (Value.pack valueTy candidate))
    (canonical : Canonical valueTy candidate)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : (plan.operations.drop before.operations.length).mapM
      (GenericStateOps.evalOp ctx candidateEnv) = .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after) :
    SourceEffects.step ctx (.readMap name destination keyTy valueTy keyExpr) (sourceEnv, current) =
      .ok ((destination, Value.pack valueTy candidate) :: sourceEnv, current) ∧
    after = ⟨[.vector slots], reads ++
      [field (scalar (GenericStateEncoding.number valueTy candidate))]⟩ := by
  obtain ⟨keySupport⟩ := GenericStateEvaluationCanonical.scalarExpression_type keyAdmission
  let valueSupport := GenericStateReadCellEvaluation.scalarCellTypeOfCanonical canonical
  obtain ⟨_, _, operations, _⟩ := GenericStateMapReadEvaluation.readMap_scalar_chunk
    state name destination keyTy valueTy emittedKey before plan keySupport valueSupport compiled
  have keySucceeds : ∃ key, emittedKey.eval ctx candidateEnv = .ok key := by
    cases projection : (GenericStateWriteEvaluation.scalarProjection keySupport emittedKey).eval
        ctx candidateEnv with
    | error message =>
      rw [operations, List.drop_left] at evaluated
      simp [List.mapM_cons, GenericStateOps.evalOp, GenericStateOps.evalAligned,
        projection, bind, Except.bind, pure, Except.pure] at evaluated
    | ok number =>
      obtain ⟨key, keyEval, _⟩ := GenericStateWriteInversion.scalarProjection_invert
        ctx candidateEnv keySupport emittedKey number modulus projection
      exact ⟨key, keyEval⟩
  obtain ⟨key, keyEval⟩ := keySucceeds
  have sourceKey := keyAgreement.trans keyEval
  have keyCanonical := GenericStateEvaluationCanonical.expression_eval_canonical
    ctx sourceEnv keyExpr keyAdmission key modulus sourceKey
  obtain ⟨slot, located, exactEval⟩ := GenericStateMapReadEvaluation.readMap_candidate_eval
    state name destination keyTy valueTy emittedKey before plan ctx candidateEnv key candidate
    compiled lookup modulus keyEval keyCanonical canonical
  rw [exactEval] at evaluated
  cases evaluated
  have named : declaration.name = name :=
    beq_iff_eq.mp (List.find?_some (p := fun item : StateDecl => item.name == name) declared)
  have declarationAt : state[slot]? = some declaration := by
    rwa [List.find?_eq_bind_findIdx?_getElem?, located] at declared
  obtain ⟨value, sourceStep, sourceCanonical, valueMatches, tape⟩ :=
    GenericStateSchemaSpans.readMap_source_step ctx sourceEnv state current slots slot declaration
      name destination keyTy valueTy keyExpr key (scalar (GenericStateEncoding.number valueTy candidate))
      reads after declarationAt named kind encoded modulus sourceKey keyCanonical checked
  have sameEncoding :
      GenericStateEncoding.encodeValue valueTy (Value.pack valueTy candidate) =
        GenericStateEncoding.encodeValue valueTy (Value.pack valueTy value) := by
    rw [GenericStateEncoding.encodeValue_pack valueTy candidate canonical,
      GenericStateEncoding.encodeValue_pack valueTy value sourceCanonical, valueMatches]
  have equal := GenericStateEncoding.encodeValue_pack_injective valueTy
    candidate value canonical sourceCanonical sameEncoding
  subst value
  exact ⟨sourceStep, tape⟩

/-- A checked unguarded Map-read suffix authenticates the typed candidate
against the current source map. Success of the native key projection supplies
the source key under agreement on the expression's prefix bindings. -/
theorem readMap_candidate_source_step (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name destination : String) (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (keyAdmission : ScalarExpression keyExpr)
    (keyAgreement : keyExpr.eval ctx sourceEnv = keyExpr.eval ctx candidateEnv)
    (candidate : valueTy.Denote) (before plan : Impact.Plan)
    (segment : List NativeState.Op) (reads : List NativeState.Cell)
    (after : NativeState.Machine)
    (compiled : Impact.appendEffectWithActivity state (.readMap name destination keyTy valueTy keyExpr)
      none before = .ok plan)
    (declaration : StateDecl)
    (declared : state.find? (·.name == name) = some declaration)
    (kind : declaration.kind = .map keyTy valueTy)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (lookup : candidateEnv.lookup destination = some (Value.pack valueTy candidate))
    (canonical : Canonical valueTy candidate)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : (plan.operations.drop before.operations.length).mapM
      (GenericStateOps.evalOp ctx candidateEnv) = .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after) :
    SourceEffects.step ctx (.readMap name destination keyTy valueTy keyExpr) (sourceEnv, current) =
      .ok ((destination, Value.pack valueTy candidate) :: sourceEnv, current) ∧
    after = ⟨[.vector slots], reads ++
      [field (scalar (GenericStateEncoding.number valueTy candidate))]⟩ := by
  obtain ⟨rawPlan, appended, sameOps, _⟩ := GuardedEffectPrefix.appendEffectWithActivity_none_result
    state (.readMap name destination keyTy valueTy keyExpr) before plan compiled
  rw [sameOps] at evaluated
  exact readMap_chunk_source_step ctx sourceEnv candidateEnv state current slots
    name destination keyTy valueTy keyExpr keyExpr keyAdmission keyAgreement candidate before
    rawPlan segment reads after appended declaration declared kind encoded lookup canonical
    modulus evaluated checked

/-- A production Map read authenticates the singleton decoded witness lane
against the actual current map and appends that exact scalar to the tape. -/
theorem readMap_decoded_source_step (ctx : EvalContext)
    (sourceEnv baseEnv decodedReads : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name destination : String) (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (keyAdmission : ScalarExpression keyExpr)
    (keyAgreement : keyExpr.eval ctx sourceEnv = keyExpr.eval ctx (baseEnv ++ decodedReads))
    (before plan : Impact.Plan) (segment : List NativeState.Op) (reads : List NativeState.Cell)
    (after : NativeState.Machine) (witness : Assignment)
    (compiled : Impact.appendEffectWithActivity state (.readMap name destination keyTy valueTy keyExpr)
      none before = .ok plan)
    (declaration : StateDecl)
    (declared : state.find? (·.name == name) = some declaration)
    (kind : declaration.kind = .map keyTy valueTy)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (decoded : decodeReads (plan.reads.drop before.reads.length) witness = .ok decodedReads)
    (fresh : baseEnv.lookup destination = none)
    (typed : valueTy.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (bounded : (witness ("%input_" ++ destination)).val ≤ Native.sourceMaximum valueTy)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : (plan.operations.drop before.operations.length).mapM
      (GenericStateOps.evalOp ctx (baseEnv ++ decodedReads)) = .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after) :
    ∃ candidate : valueTy.Denote,
      SourceEffects.step ctx (.readMap name destination keyTy valueTy keyExpr) (sourceEnv, current) =
        .ok ((destination, Value.pack valueTy candidate) :: sourceEnv, current) ∧
      sourceScalar? valueTy candidate = some (witness ("%input_" ++ destination)) ∧
      after = ⟨[.vector slots], reads ++ [field (witness ("%input_" ++ destination))]⟩ := by
  obtain ⟨rawPlan, appended, _, sameReads⟩ := GuardedEffectPrefix.appendEffectWithActivity_none_result
    state (.readMap name destination keyTy valueTy keyExpr) before plan compiled
  have exactReads := GuardedEffectPrefix.appendEffect_readMap_read_suffix
    state name destination keyTy valueTy keyExpr before rawPlan appended
  rw [sameReads, exactReads, List.drop_left] at decoded
  obtain ⟨support, environment⟩ := decodeReads_singleton_success
    {name := destination, ty := valueTy} witness decodedReads decoded
  let input := witness ("%input_" ++ destination)
  let candidate := sourceValue support input
  have lookup : (baseEnv ++ decodedReads).lookup destination = some (Value.pack valueTy candidate) := by
    rw [environment]
    simp [List.lookup_append, fresh, input, candidate]
  obtain ⟨canonical, exactScalar⟩ := sourceValue_canonical support input typed bounded
  obtain ⟨sourceStep, tape⟩ := readMap_candidate_source_step ctx sourceEnv
    (baseEnv ++ decodedReads) state current slots name destination keyTy valueTy keyExpr keyAdmission
    keyAgreement candidate before plan segment reads after compiled declaration declared kind encoded
    lookup canonical modulus evaluated checked
  have numberMatches := Option.some.inj
    ((GenericStateEncoding.sourceScalar_eq_field support candidate).symm.trans exactScalar)
  exact ⟨candidate, sourceStep, exactScalar, by rw [tape, numberMatches]⟩

/-- A successful source Map read determines the evaluated raw chunk and its
native successor when the emitted key agrees with the source. -/
theorem source_readMap_chunk (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name destination : String) (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (emittedKey : Expr keyTy) (keyAdmission : ScalarExpression keyExpr)
    (keyAgreement : emittedKey.eval ctx candidateEnv = keyExpr.eval ctx sourceEnv)
    (sourceAfter : SourceEffects.Frame) (before plan : Impact.Plan) (reads : List NativeState.Cell)
    (sourceStep : SourceEffects.step ctx (.readMap name destination keyTy valueTy keyExpr)
      (sourceEnv, current) = .ok sourceAfter)
    (candidateLookup : candidateEnv.lookup destination = sourceAfter.1.lookup destination)
    (compiled : Impact.appendEffect state (.readMap name destination keyTy valueTy emittedKey)
      before = .ok plan)
    (declaration : StateDecl)
    (declared : state.find? (·.name == name) = some declaration)
    (kind : declaration.kind = .map keyTy valueTy)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ (slot : Nat) (key : keyTy.Denote) (value : valueTy.Denote),
      state.findIdx? (·.name == name) = some slot ∧
      (plan.operations.drop before.operations.length).mapM (GenericStateOps.evalOp ctx candidateEnv) =
        .ok (GenericStateVM.readMapOps slot (scalar (GenericStateEncoding.number keyTy key))
          (scalar (GenericStateEncoding.number valueTy value))) ∧
      NativeState.run (GenericStateVM.readMapOps slot (scalar (GenericStateEncoding.number keyTy key))
        (scalar (GenericStateEncoding.number valueTy value))) ⟨[.vector slots], reads⟩ =
          some ⟨[.vector slots], reads ++ [field (scalar (GenericStateEncoding.number valueTy value))]⟩ ∧
      sourceAfter = ((destination, Value.pack valueTy value) :: sourceEnv, current) := by
  obtain ⟨slot, located, declarationAt⟩ :=
    GenericStateSchemaSpans.find_declaration_slot state name declaration declared
  have named : declaration.name = name :=
    beq_iff_eq.mp (List.find?_some (p := fun item : StateDecl => item.name == name) declared)
  obtain ⟨key, value, keyEval, keyCanonical, valueCanonical, frame, nativeRun⟩ :=
    GenericStateSchemaSpans.readMap_source_native ctx sourceEnv state current slots slot declaration
      name destination keyTy valueTy keyExpr sourceAfter reads declarationAt named kind encoded
      keyAdmission modulus sourceStep
  have lookup : candidateEnv.lookup destination = some (Value.pack valueTy value) := by
    simp [candidateLookup, frame]
  obtain ⟨selected, selection, evaluated⟩ := GenericStateMapReadEvaluation.readMap_candidate_eval
    state name destination keyTy valueTy emittedKey before plan ctx candidateEnv key value
    compiled lookup modulus (keyAgreement.trans keyEval) keyCanonical valueCanonical
  have sameSlot : selected = slot := Option.some.inj (selection.symm.trans located)
  subst selected
  exact ⟨slot, key, value, located, evaluated, nativeRun, frame⟩

/-- A successful source Map read determines the exact evaluated unguarded
suffix and its native successor. The candidate environment carries the
source-derived read binding and agrees on key evaluation. -/
theorem source_readMap_emitted (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name destination : String) (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (keyAdmission : ScalarExpression keyExpr)
    (keyAgreement : keyExpr.eval ctx candidateEnv = keyExpr.eval ctx sourceEnv)
    (sourceAfter : SourceEffects.Frame) (before plan : Impact.Plan) (reads : List NativeState.Cell)
    (sourceStep : SourceEffects.step ctx (.readMap name destination keyTy valueTy keyExpr)
      (sourceEnv, current) = .ok sourceAfter)
    (candidateLookup : candidateEnv.lookup destination = sourceAfter.1.lookup destination)
    (compiled : Impact.appendEffectWithActivity state (.readMap name destination keyTy valueTy keyExpr)
      none before = .ok plan)
    (declaration : StateDecl)
    (declared : state.find? (·.name == name) = some declaration)
    (kind : declaration.kind = .map keyTy valueTy)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ (slot : Nat) (key : keyTy.Denote) (value : valueTy.Denote),
      state.findIdx? (·.name == name) = some slot ∧
      (plan.operations.drop before.operations.length).mapM (GenericStateOps.evalOp ctx candidateEnv) =
        .ok (GenericStateVM.readMapOps slot (scalar (GenericStateEncoding.number keyTy key))
          (scalar (GenericStateEncoding.number valueTy value))) ∧
      NativeState.run (GenericStateVM.readMapOps slot (scalar (GenericStateEncoding.number keyTy key))
        (scalar (GenericStateEncoding.number valueTy value))) ⟨[.vector slots], reads⟩ =
          some ⟨[.vector slots], reads ++ [field (scalar (GenericStateEncoding.number valueTy value))]⟩ ∧
      sourceAfter = ((destination, Value.pack valueTy value) :: sourceEnv, current) := by
  obtain ⟨rawPlan, appended, sameOps, _⟩ := GuardedEffectPrefix.appendEffectWithActivity_none_result
    state (.readMap name destination keyTy valueTy keyExpr) before plan compiled
  rw [sameOps]
  exact source_readMap_chunk ctx sourceEnv candidateEnv state current slots name destination
    keyTy valueTy keyExpr keyExpr keyAdmission keyAgreement sourceAfter before rawPlan reads
    sourceStep candidateLookup appended declaration declared kind encoded modulus

end Noctium.Verification.GenericStateMapReadAuthentication
