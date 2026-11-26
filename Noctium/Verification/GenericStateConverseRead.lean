import Noctium.Verification.GenericStateReadCellEvaluation
import Noctium.Verification.GenericStateReadAuthentication
import Noctium.Verification.GenericStateMapReadAuthentication
import Noctium.Verification.GuardedMapReadAuthentication
import Noctium.Verification.GenericStateSchemaSpans
import Noctium.Verification.GuardedScalarInput
import Noctium.Verification.GuardedSourceEffects
import Noctium.Verification.GuardedEffectPrefix
import Noctium.Verification.GuardedPlanExecution

namespace Noctium.Verification.GenericStateConverseRead
open Backend GenericStateCellAdmission GenericStateEncoding NativeRelation
  NativeState ScalarNormalization

private theorem source_readCell_step_value (ctx : EvalContext)
    (env : EvalEnv) (state : LedgerState) (name destination : String) (ty : Ty)
    (success : SourceEffects.step ctx (.readCell name destination ty)
      (env, state) = .ok after) :
    ∃ (raw : Value) (value : ty.Denote),
      state.cells.lookup name = some raw ∧
      raw.as ty = some value := by
  cases found : state.cells.lookup name with
  | none =>
    simp [SourceEffects.step, runEffectWithEnv, found, bind, Except.bind,
      throw, pure, Except.pure] at success
  | some raw =>
    cases typed : raw.as ty with
    | none =>
      simp [SourceEffects.step, runEffectWithEnv, found, typed, bind, Except.bind,
        throw, pure, Except.pure] at success
    | some value =>
      exact ⟨raw, value, rfl, typed⟩

private theorem sourceCanonical (ctx : EvalContext) {ty : Ty}
    {value : ty.Denote} (scalar : ScalarCellType ty)
    (modulus : ctx.modulus = Field.modulus) (canonical : Canonical ty value) :
    SourceEffects.canonicalValue ctx ty value = true := by
  cases scalar with
  | native =>
    simpa [SourceEffects.canonicalValue, Canonical, sourceNumber?, modulus] using canonical.1
  | bool => rfl
  | uint maximum valid =>
    rcases canonical with ⟨bound, maximumBound, valueBound⟩
    have fieldBound : value < Field.modulus := by simpa [GenericStateEncoding.number] using bound
    simp [SourceEffects.canonicalValue, modulus, fieldBound, maximumBound, valueBound]

private theorem encodeDeclaration_cell_result (state : LedgerState)
    (declaration : StateDecl) (ty : Ty) (slot : NativeState.Slot)
    (kind : declaration.kind = .cell ty)
    (encoded : GenericStateEncoding.encodeDeclaration state declaration = some slot) :
    ∃ cell, slot = .cell cell := by
  cases declaration with
  | mk name actualKind sealed span cellAlignment? =>
    simp only at kind
    subst actualKind
    cases slot with
    | cell cell => exact ⟨cell, rfl⟩
    | map entries =>
      cases cellAlignment? with
      | some alignment =>
        simp [GenericStateEncoding.encodeDeclaration] at encoded
      | none =>
        cases found : state.cells.lookup name with
        | none =>
          simp [GenericStateEncoding.encodeDeclaration, found] at encoded
        | some raw =>
          cases value : GenericStateEncoding.encodeValue ty raw with
          | none =>
            simp [GenericStateEncoding.encodeDeclaration, found, value] at encoded
          | some cellValue =>
            simp [GenericStateEncoding.encodeDeclaration, found, value] at encoded

private theorem encodeDeclaration_cell_eq_default (state : LedgerState)
    (name : String) (ty : Ty) (declaration : StateDecl)
    (named : declaration.name = name) (kind : declaration.kind = .cell ty)
    (unaligned : declaration.cellAlignment? = none) :
    GenericStateEncoding.encodeDeclaration state declaration =
      GenericStateEncoding.encodeDeclaration state {name, kind := .cell ty} := by
  cases declaration with
  | mk actualName actualKind sealed span cellAlignment? =>
    simp only at named kind unaligned
    subst actualName
    subst actualKind
    subst cellAlignment?
    rfl

/-- A successful source read and native cell encoding select the same typed
value. The scalar proof uses the encoded declaration, which excludes wider
aligned cells and source types without field storage. -/
theorem source_readCell_native (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List Slot)
    (name destination : String) (ty : Ty)
    (sourceAfter : SourceEffects.Frame) (base : Impact.Plan)
    (reads : List Cell)
    (sourceStep : SourceEffects.step ctx (.readCell name destination ty)
      (sourceEnv, current) = .ok sourceAfter)
    (candidateLookup : candidateEnv.lookup destination =
      sourceAfter.1.lookup destination)
    (sourceDeclaration : StateDecl)
    (declared : state.find? (·.name == name) = some sourceDeclaration)
    (named : sourceDeclaration.name = name)
    (kind : sourceDeclaration.kind = .cell ty)
    (compiled : Impact.appendEffect state (.readCell name destination ty) {} =
      .ok base)
    (encoded : encodeState state current = some slots)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ slot value,
      state.findIdx? (·.name == name) = some slot ∧
      base.operations.mapM (GenericStateOps.evalOp ctx candidateEnv) =
        .ok (GenericStateVM.readCellOps slot
          (field (scalar (GenericStateEncoding.number ty value)))) ∧
      run (GenericStateVM.readCellOps slot
        (field (scalar (GenericStateEncoding.number ty value))))
        ⟨[.vector slots], reads⟩ =
        some ⟨[.vector slots], reads ++
          [field (scalar (GenericStateEncoding.number ty value))]⟩ ∧
      sourceAfter = ((destination, Value.pack ty value) :: sourceEnv, current) := by
  obtain ⟨raw, value, sourceLookup, sourceTyped⟩ :=
    source_readCell_step_value ctx sourceEnv current name destination ty sourceStep
  obtain ⟨sourceSlot, sourceLocated, declarationAt⟩ :=
    GenericStateSchemaSpans.find_declaration_slot state name sourceDeclaration declared
  have sourceSlotBound : sourceSlot < state.length :=
    (List.getElem?_eq_some_iff.mp declarationAt).1
  have slotBound : sourceSlot < slots.length := by
    rw [GenericStateEncoding.encodeState_length state current slots encoded]
    exact sourceSlotBound
  have alignment := GenericStateSchemaSpans.encoded_cell_alignment_none state current slots
    sourceSlot sourceDeclaration ty declarationAt kind encoded
  have slotEncoding := GenericStateEncoding.encodeState_slot state current slots
    sourceSlot encoded
  rw [declarationAt] at slotEncoding
  simp only [Option.bind_some] at slotEncoding
  cases slotAt : slots[sourceSlot]? with
  | none =>
    have outside := List.getElem?_eq_none_iff.mp slotAt
    omega
  | some slotValue =>
    have actualEncoding : encodeDeclaration current sourceDeclaration = some slotValue := by
      rw [slotAt] at slotEncoding
      exact slotEncoding.symm
    obtain ⟨cell, slotValueCell⟩ :=
      encodeDeclaration_cell_result current sourceDeclaration ty slotValue kind actualEncoding
    have defaultEncoding : encodeDeclaration current {name, kind := .cell ty} =
        some (.cell cell) := by
      rw [← encodeDeclaration_cell_eq_default current name ty sourceDeclaration
        named kind alignment]
      rw [slotValueCell] at actualEncoding
      exact actualEncoding
    obtain ⟨encodedValue, encodedLookup, valueCanonical, cellEncoding⟩ :=
      GenericStateEncoding.encoded_cell_typed current name ty cell defaultEncoding
    have rawEqual : raw = Value.pack ty encodedValue :=
      Option.some.inj (sourceLookup.symm.trans encodedLookup)
    have valueEqual : value = encodedValue := by
      rw [rawEqual] at sourceTyped
      rw [ScalarNormalization.number_pack_as ty encodedValue valueCanonical] at sourceTyped
      exact (Option.some.inj sourceTyped).symm
    subst encodedValue
    let scalarType := GenericStateReadCellEvaluation.scalarCellTypeOfCanonical valueCanonical
    rw [rawEqual] at sourceLookup sourceTyped
    have sourceCanonicalValue := sourceCanonical ctx scalarType modulus valueCanonical
    have sourceShape : sourceAfter =
        ((destination, Value.pack ty value) :: sourceEnv, current) := by
      have stepShape : SourceEffects.step ctx (.readCell name destination ty)
          (sourceEnv, current) =
          .ok ((destination, Value.pack ty value) :: sourceEnv, current) := by
        cases scalarType with
        | native =>
          have fieldBound : value < ctx.modulus := by
            simpa [SourceEffects.canonicalValue] using sourceCanonicalValue
          simp [SourceEffects.step, runEffectWithEnv, sourceLookup, sourceTyped,
            canonical_eq, fieldBound, pure, Except.pure]
        | bool =>
          simp [SourceEffects.step, runEffectWithEnv, sourceLookup, sourceTyped,
            canonical_eq, pure, Except.pure]
        | uint maximum valid =>
          have bounds : (maximum ≤ ScalarPolicy.maxUint ∧ value ≤ maximum) ∧
              value < ctx.modulus := by
            simpa [SourceEffects.canonicalValue] using sourceCanonicalValue
          simp [SourceEffects.step, runEffectWithEnv, sourceLookup, sourceTyped,
            canonical_eq, bounds, pure, Except.pure]
      rw [stepShape] at sourceStep
      exact (Except.ok.inj sourceStep).symm
    let scalarDeclaration : ScalarCellDeclaration state name ty :=
      ⟨sourceDeclaration, declared, kind, alignment⟩
    have candidate : candidateEnv.lookup destination = some (Value.pack ty value) := by
      rw [candidateLookup, sourceShape]
      simp
    obtain ⟨slot, located, evaluated⟩ :=
      GenericStateReadCellEvaluation.readCell_candidate_eval state name destination
        ty base ctx candidateEnv value scalarType scalarDeclaration compiled candidate
        modulus valueCanonical
    rw [sourceLocated] at located
    have sameSlot : slot = sourceSlot := Option.some.inj located.symm
    subst slot
    have declarationEncoding : encodeDeclaration current sourceDeclaration =
        some (.cell (field (scalar (GenericStateEncoding.number ty value)))) := by
      rw [encodeDeclaration_cell_eq_default current name ty sourceDeclaration
        named kind alignment]
      simpa only [cellEncoding] using defaultEncoding
    rw [declarationEncoding] at slotEncoding
    refine ⟨sourceSlot, value, sourceLocated, evaluated, ?_, sourceShape⟩
    exact GenericStateVM.readCell_exact slots sourceSlot
      (field (scalar (GenericStateEncoding.number ty value))) reads slotEncoding

private def scalarTypeOfCell : {ty : Ty} → ScalarCellType ty → ScalarType ty
  | _, .native => .native
  | _, .bool => .bool
  | _, .uint maximum _ => .uint maximum

private theorem source_readCell_frame_canonical (ctx : EvalContext)
    (env : EvalEnv) (declarations : List StateDecl) (current : LedgerState)
    (slots : List Slot) (name destination : String) (ty : Ty)
    (sourceAfter : SourceEffects.Frame) (declaration : StateDecl)
    (declared : declarations.find? (·.name == name) = some declaration)
    (named : declaration.name = name) (kind : declaration.kind = .cell ty)
    (encoded : encodeState declarations current = some slots)
    (modulus : ctx.modulus = Field.modulus)
    (sourceStep : SourceEffects.step ctx (.readCell name destination ty)
      (env, current) = .ok sourceAfter) :
    ∃ value, sourceAfter.1.lookup destination = some (Value.pack ty value) ∧
      Canonical ty value ∧ sourceAfter.2 = current := by
  obtain ⟨raw, value, sourceLookup, sourceTyped⟩ :=
    source_readCell_step_value ctx env current name destination ty sourceStep
  obtain ⟨sourceSlot, _, declarationAt⟩ :=
    GenericStateSchemaSpans.find_declaration_slot declarations name declaration declared
  have sourceSlotBound : sourceSlot < declarations.length :=
    (List.getElem?_eq_some_iff.mp declarationAt).1
  have slotBound : sourceSlot < slots.length := by
    rw [encodeState_length declarations current slots encoded]
    exact sourceSlotBound
  have alignment := GenericStateSchemaSpans.encoded_cell_alignment_none declarations current
    slots sourceSlot declaration ty declarationAt kind encoded
  have slotEncoding := encodeState_slot declarations current slots sourceSlot encoded
  rw [declarationAt] at slotEncoding
  simp only [Option.bind_some] at slotEncoding
  cases slotAt : slots[sourceSlot]? with
  | none =>
    have outside := List.getElem?_eq_none_iff.mp slotAt
    omega
  | some slotValue =>
    have actualEncoding : encodeDeclaration current declaration = some slotValue := by
      rw [slotAt] at slotEncoding
      exact slotEncoding.symm
    obtain ⟨cell, slotValueCell⟩ :=
      encodeDeclaration_cell_result current declaration ty slotValue kind actualEncoding
    have defaultEncoding : encodeDeclaration current {name, kind := .cell ty} =
        some (.cell cell) := by
      rw [← encodeDeclaration_cell_eq_default current name ty declaration named kind alignment]
      rw [slotValueCell] at actualEncoding
      exact actualEncoding
    obtain ⟨encodedValue, encodedLookup, valueCanonical, _⟩ :=
      encoded_cell_typed current name ty cell defaultEncoding
    have rawEqual : raw = Value.pack ty encodedValue :=
      Option.some.inj (sourceLookup.symm.trans encodedLookup)
    have valueEqual : value = encodedValue := by
      rw [rawEqual] at sourceTyped
      rw [ScalarNormalization.number_pack_as ty encodedValue valueCanonical] at sourceTyped
      exact (Option.some.inj sourceTyped).symm
    subst encodedValue
    let scalarType := GenericStateReadCellEvaluation.scalarCellTypeOfCanonical valueCanonical
    rw [rawEqual] at sourceLookup sourceTyped
    have checkedCanonical := sourceCanonical ctx scalarType modulus valueCanonical
    have sourceShape : sourceAfter =
        ((destination, Value.pack ty value) :: env, current) := by
      have stepShape : SourceEffects.step ctx (.readCell name destination ty)
          (env, current) = .ok ((destination, Value.pack ty value) :: env, current) := by
        cases scalarType with
        | native =>
          have fieldBound : value < ctx.modulus := by
            simpa [SourceEffects.canonicalValue] using checkedCanonical
          simp [SourceEffects.step, runEffectWithEnv, sourceLookup, sourceTyped,
            canonical_eq, fieldBound, pure, Except.pure]
        | bool =>
          simp [SourceEffects.step, runEffectWithEnv, sourceLookup, sourceTyped,
            canonical_eq, pure, Except.pure]
        | uint maximum valid =>
          have bounds : (maximum ≤ ScalarPolicy.maxUint ∧ value ≤ maximum) ∧
              value < ctx.modulus := by
            simpa [SourceEffects.canonicalValue] using checkedCanonical
          simp [SourceEffects.step, runEffectWithEnv, sourceLookup, sourceTyped,
            canonical_eq, bounds, pure, Except.pure]
      rw [stepShape] at sourceStep
      exact (Except.ok.inj sourceStep).symm
    exact ⟨value, by rw [sourceShape]; simp, valueCanonical, by rw [sourceShape]⟩

private theorem scalarCellDefault_canonical {ty : Ty}
    (supported : ScalarCellType ty) :
    Canonical ty (GenericStateInputValues.sourceValue (scalarTypeOfCell supported)
      NativeRelation.zero) := by
  cases supported with
  | native => simp [GenericStateInputValues.sourceValue, Canonical,
      ScalarNormalization.sourceNumber?, scalarTypeOfCell, NativeRelation.zero] <;> decide
  | bool => simp [GenericStateInputValues.sourceValue, Canonical,
      ScalarNormalization.sourceNumber?, scalarTypeOfCell, NativeRelation.zero] <;> decide
  | uint maximum valid =>
      simp [GenericStateInputValues.sourceValue, Canonical,
        ScalarNormalization.sourceNumber?, scalarTypeOfCell, NativeRelation.zero, valid] <;> decide

private theorem guarded_readCell_suffix (state : List StateDecl)
    (name destination : String) (ty : Ty) (guard : Option (Expr .bool))
    (before plan base : Impact.Plan)
    (compiled : Impact.appendEffectWithActivity state (.readCell name destination ty)
      guard before = .ok plan)
    (baseCompiled : Impact.appendEffect state (.readCell name destination ty) {} = .ok base) :
    plan.operations = before.operations ++ base.operations := by
  cases guard with
  | none =>
    obtain ⟨actualBase, actualCompiled, suffix⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_unguarded_readCell_chunk
        state name destination ty before plan compiled
    have sameBase : actualBase = base :=
      Except.ok.inj (actualCompiled.symm.trans baseCompiled)
    simpa [sameBase] using suffix
  | some condition =>
    exact (GuardedEffectPrefix.appendEffectWithActivity_readCell_empty_chunk
      state name destination ty condition before plan base compiled baseCompiled).1

private theorem evalChunk_none_of_operations (ctx : EvalContext) (env : EvalEnv)
    (chunk : List Impact.Op) (operations : List NativeState.Op)
    (evaluated : chunk.mapM (GenericStateOps.evalOp ctx env) = .ok operations) :
    GuardedPlanExecution.evalChunk ctx env none chunk = .ok (none, operations) := by
  unfold GuardedPlanExecution.evalChunk
  rw [evaluated]
  rfl

private theorem evalChunk_some_active_of_operations (ctx : EvalContext) (env : EvalEnv)
    (condition : Expr .bool) (chunk : List Impact.Op) (operations : List NativeState.Op)
    (active : condition.eval ctx env = .ok true)
    (evaluated : chunk.mapM (GenericStateOps.evalOp ctx env) = .ok operations) :
    GuardedPlanExecution.evalChunk ctx env (some condition) chunk =
      .ok (some true, operations) := by
  unfold GuardedPlanExecution.evalChunk
  have guardEvaluation : (some condition).mapM (fun condition => condition.eval ctx env) =
      .ok (some true) := by
    change (some <$> condition.eval ctx env) = .ok (some true)
    rw [active]
    rfl
  rw [guardEvaluation]
  rw [evaluated]
  rfl

private theorem evalChunk_some_inactive (ctx : EvalContext) (env : EvalEnv)
    (condition : Expr .bool) (chunk : List Impact.Op)
    (inactive : condition.eval ctx env = .ok false) :
    GuardedPlanExecution.evalChunk ctx env (some condition) chunk =
      .ok (some false, []) := by
  unfold GuardedPlanExecution.evalChunk
  have guardEvaluation : (some condition).mapM (fun condition => condition.eval ctx env) =
      .ok (some false) := by
    change (some <$> condition.eval ctx env) = .ok (some false)
    rw [inactive]
    rfl
  rw [guardEvaluation]
  rfl

/-- A successful guarded Cell read fixes the exact compiled suffix, its
native read-tape effect, and the typed source binding. Inactive reads produce
typed zero without evaluating a Cell operation. -/
theorem guarded_scalarCell_read_emitted (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (declarations : List StateDecl)
    (current : LedgerState) (slots : List Slot) (reads : List Cell)
    (name destination : String) (ty : Ty) (supported : ScalarCellType ty)
    (guard : Option (Expr .bool)) (sourceAfter : GuardedSourceEffects.Frame)
    (before plan base : Impact.Plan) (declaration : StateDecl)
    (declared : declarations.find? (·.name == name) = some declaration)
    (named : declaration.name = name) (kind : declaration.kind = .cell ty)
    (compiled : Impact.appendEffectWithActivity declarations
      (.readCell name destination ty) guard before = .ok plan)
    (baseCompiled : Impact.appendEffect declarations
      (.readCell name destination ty) {} = .ok base)
    (encoded : encodeState declarations current = some slots)
    (modulus : ctx.modulus = Field.modulus)
    (sourceStep : GuardedSourceEffects.step ctx guard
      (.readCell name destination ty) (sourceEnv, current) = .ok sourceAfter)
    (candidateLookup : candidateEnv.lookup destination = sourceAfter.1.lookup destination)
    (guardAgreement : ∀ condition, guard = some condition →
      condition.eval ctx sourceEnv = condition.eval ctx candidateEnv) :
    ∃ (value : ty.Denote) (activity : Option Bool) (segment : List NativeState.Op),
      GuardedPlanExecution.evalChunk ctx candidateEnv guard
        (plan.operations.drop before.operations.length) = .ok (activity, segment) ∧
      NativeState.run segment ⟨[.vector slots], reads⟩ =
        some ⟨[.vector slots], reads ++
          (if activity.getD true then
            [field (scalar (GenericStateEncoding.number ty value))] else [])⟩ ∧
      sourceAfter = ((destination, Value.pack ty value) :: sourceEnv, current) ∧
      (activity = some false → value = GenericStateInputValues.sourceValue
        (scalarTypeOfCell supported) NativeRelation.zero) := by
  cases guard with
  | none =>
    have unguardedStep : SourceEffects.step ctx (.readCell name destination ty)
        (sourceEnv, current) = .ok sourceAfter := by
      rw [GuardedSourceEffects.step_unguarded] at sourceStep
      exact sourceStep
    obtain ⟨slot, value, located, evaluated, checked, sourceShape⟩ :=
      source_readCell_native ctx sourceEnv candidateEnv declarations current slots
        name destination ty sourceAfter base reads unguardedStep candidateLookup declaration
        declared named kind baseCompiled encoded modulus
    have suffix := guarded_readCell_suffix declarations name destination ty none before plan
      base compiled baseCompiled
    have exactSuffix : plan.operations.drop before.operations.length = base.operations := by
      rw [suffix]
      simp
    have evalResult := evalChunk_none_of_operations ctx candidateEnv base.operations
      (GenericStateVM.readCellOps slot
        (field (scalar (GenericStateEncoding.number ty value)))) evaluated
    have evalSuffix : GuardedPlanExecution.evalChunk ctx candidateEnv none
        (plan.operations.drop before.operations.length) =
        .ok (none, GenericStateVM.readCellOps slot
          (field (scalar (GenericStateEncoding.number ty value)))) := by
      rw [exactSuffix]
      exact evalResult
    refine ⟨value, none, _, evalSuffix, ?_, sourceShape, ?_⟩
    · simpa using checked
    · intro inactive
      cases inactive
  | some condition =>
    cases sourceGuard : condition.eval ctx sourceEnv with
    | error message =>
      have rejected := GuardedSourceEffects.step_guard_error ctx condition
        (.readCell name destination ty) (sourceEnv, current) message
        (.readCell condition name destination ty) sourceGuard
      rw [rejected] at sourceStep
      cases sourceStep
    | ok active =>
      have candidateGuard := (guardAgreement condition rfl).symm
      cases active with
      | false =>
        change runEffectsWithGuardsAndEnv ctx [.readCell name destination ty]
          [some condition] sourceEnv current = .ok sourceAfter at sourceStep
        rw [GuardedScalarInput.run_inactive_scalarCell_read ctx sourceEnv current name
          destination (scalarTypeOfCell supported) condition sourceGuard] at sourceStep
        have sourceShape := Except.ok.inj sourceStep
        have evalResult := evalChunk_some_inactive ctx candidateEnv condition
          (plan.operations.drop before.operations.length) (candidateGuard.trans sourceGuard)
        refine ⟨GenericStateInputValues.sourceValue (scalarTypeOfCell supported)
            NativeRelation.zero, some false, [], evalResult, ?_, ?_, ?_⟩
        · simp [NativeState.run]
        · exact sourceShape.symm
        · intro _
          rfl
      | true =>
        have activeSource : condition.eval ctx sourceEnv = .ok true := sourceGuard
        have activeCandidate : condition.eval ctx candidateEnv = .ok true :=
          candidateGuard.trans activeSource
        have unguardedStep : SourceEffects.step ctx (.readCell name destination ty)
            (sourceEnv, current) = .ok sourceAfter := by
          change runEffectsWithGuardsAndEnv ctx [.readCell name destination ty]
            [some condition] sourceEnv current = .ok sourceAfter at sourceStep
          rw [GuardedScalarInput.run_active_scalarCell_read ctx sourceEnv current name
            destination (scalarTypeOfCell supported) condition activeSource] at sourceStep
          exact sourceStep
        obtain ⟨slot, value, located, evaluated, checked, sourceShape⟩ :=
          source_readCell_native ctx sourceEnv candidateEnv declarations current slots
            name destination ty sourceAfter base reads unguardedStep candidateLookup declaration
            declared named kind baseCompiled encoded modulus
        have suffix := guarded_readCell_suffix declarations name destination ty
          (some condition) before plan base compiled baseCompiled
        have exactSuffix : plan.operations.drop before.operations.length = base.operations := by
          rw [suffix]
          simp
        have evalResult := evalChunk_some_active_of_operations ctx candidateEnv condition
          (plan.operations.drop before.operations.length)
          (GenericStateVM.readCellOps slot
            (field (scalar (GenericStateEncoding.number ty value)))) activeCandidate
          (by rw [exactSuffix]; exact evaluated)
        refine ⟨value, some true, _, evalResult, ?_, sourceShape, ?_⟩
        · simpa using checked
        · intro inactive
          cases inactive

/-- A successful guarded scalar cell read binds a canonical value and leaves
the current encoded ledger unchanged. Inactive reads bind their typed zero. -/
theorem guarded_scalarCell_read_canonical (ctx : EvalContext)
    (env : EvalEnv) (declarations : List StateDecl) (current : LedgerState)
    (slots : List Slot) (name destination : String) (ty : Ty)
    (guard : Option (Expr .bool)) (after : GuardedSourceEffects.Frame)
    (supported : ScalarCellType ty) (declaration : StateDecl)
    (declared : declarations.find? (·.name == name) = some declaration)
    (named : declaration.name = name) (kind : declaration.kind = .cell ty)
    (encoded : encodeState declarations current = some slots)
    (modulus : ctx.modulus = Field.modulus)
    (success : GuardedSourceEffects.step ctx guard (.readCell name destination ty)
      (env, current) = .ok after) :
    ∃ value, after.1.lookup destination = some (Value.pack ty value) ∧
      Canonical ty value ∧ after.2 = current := by
  cases guard with
  | none =>
    rw [GuardedSourceEffects.step_unguarded] at success
    exact source_readCell_frame_canonical ctx env declarations current slots name destination ty
      after declaration declared named kind encoded modulus success
  | some condition =>
    cases evaluated : condition.eval ctx env with
    | error message =>
      have rejected := GuardedSourceEffects.step_guard_error ctx condition
        (.readCell name destination ty) (env, current) message
        (.readCell condition name destination ty) evaluated
      rw [rejected] at success
      cases success
    | ok active =>
      cases active with
      | false =>
        change runEffectsWithGuardsAndEnv ctx [.readCell name destination ty] [some condition]
          env current = .ok after at success
        rw [GuardedScalarInput.run_inactive_scalarCell_read ctx env current name destination
          (scalarTypeOfCell supported) condition evaluated] at success
        have frame := Except.ok.inj success
        rw [← frame]
        exact ⟨GenericStateInputValues.sourceValue (scalarTypeOfCell supported)
          NativeRelation.zero, by simp, scalarCellDefault_canonical supported, rfl⟩
      | true =>
        change runEffectsWithGuardsAndEnv ctx [.readCell name destination ty] [some condition]
          env current = .ok after at success
        rw [GuardedScalarInput.run_active_scalarCell_read ctx env current name destination
          (scalarTypeOfCell supported) condition evaluated] at success
        exact source_readCell_frame_canonical ctx env declarations current slots name destination
          ty after declaration declared named kind encoded modulus success

private theorem guardedMapSource (ctx : EvalContext) (env : EvalEnv)
    (declarations : List StateDecl) (current : LedgerState) (slots : List Slot)
    (name destination : String) (keyTy valueTy : Ty) (key : Expr keyTy)
    (keyAdmission : ScalarExpression key) (after : GuardedSourceEffects.Frame)
    (declaration : StateDecl)
    (declared : declarations.find? (·.name == name) = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .map keyTy valueTy)
    (encoded : encodeState declarations current = some slots)
    (modulus : ctx.modulus = Field.modulus)
    (sourceStep : SourceEffects.step ctx (.readMap name destination keyTy valueTy key)
      (env, current) = .ok after) :
    ∃ value, after.1.lookup destination = some (Value.pack valueTy value) ∧
      Canonical valueTy value ∧ after.2 = current := by
  obtain ⟨slot, _, declarationAt⟩ :=
    GenericStateSchemaSpans.find_declaration_slot declarations name declaration declared
  obtain ⟨_, value, _, _, valueCanonical, sourceFrame, _⟩ :=
    GenericStateSchemaSpans.readMap_source_native ctx env declarations current slots slot
      declaration name destination keyTy valueTy key after [] declarationAt named kind encoded
      keyAdmission modulus sourceStep
  exact ⟨value, by rw [sourceFrame]; simp, valueCanonical, by rw [sourceFrame]⟩

/-- A successful guarded scalar Map read binds a canonical value from the
current encoded map and leaves the ledger unchanged. Inactive reads bind zero. -/
theorem guarded_scalarMap_read_canonical (ctx : EvalContext)
    (env : EvalEnv) (declarations : List StateDecl) (current : LedgerState)
    (slots : List Slot) (name destination : String) (keyTy valueTy : Ty)
    (key : Expr keyTy) (keyAdmission : ScalarExpression key)
    (guard : Option (Expr .bool)) (after : GuardedSourceEffects.Frame)
    (supported : ScalarCellType valueTy) (declaration : StateDecl)
    (declared : declarations.find? (·.name == name) = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .map keyTy valueTy)
    (encoded : encodeState declarations current = some slots)
    (modulus : ctx.modulus = Field.modulus)
    (success : GuardedSourceEffects.step ctx guard
      (.readMap name destination keyTy valueTy key) (env, current) = .ok after) :
    ∃ value, after.1.lookup destination = some (Value.pack valueTy value) ∧
      Canonical valueTy value ∧ after.2 = current := by
  cases guard with
  | none =>
    rw [GuardedSourceEffects.step_unguarded] at success
    exact guardedMapSource ctx env declarations current slots name destination keyTy valueTy key
      keyAdmission after declaration declared named kind encoded modulus success
  | some condition =>
    cases evaluated : condition.eval ctx env with
    | error message =>
      have rejected := GuardedSourceEffects.step_guard_error ctx condition
        (.readMap name destination keyTy valueTy key) (env, current) message
        (.readMap condition name destination keyTy valueTy key) evaluated
      rw [rejected] at success
      cases success
    | ok active =>
      cases active with
      | false =>
        change runEffectsWithGuardsAndEnv ctx
          [.readMap name destination keyTy valueTy key] [some condition] env current = .ok after at success
        rw [GuardedScalarInput.run_inactive_scalarMap_read ctx env current name destination key
          (scalarTypeOfCell supported) condition evaluated] at success
        have frame := Except.ok.inj success
        rw [← frame]
        exact ⟨GenericStateInputValues.sourceValue (scalarTypeOfCell supported)
          NativeRelation.zero, by simp, scalarCellDefault_canonical supported, rfl⟩
      | true =>
        change runEffectsWithGuardsAndEnv ctx
          [.readMap name destination keyTy valueTy key] [some condition] env current = .ok after at success
        rw [GuardedScalarInput.run_active_map_read ctx env current name destination key
          (scalarTypeOfCell supported) condition evaluated] at success
        exact guardedMapSource ctx env declarations current slots name destination keyTy valueTy key
          keyAdmission after declaration declared named kind encoded modulus success

/-- A successful guarded scalar Map read fixes the exact compiled suffix,
its native read-tape effect, and the typed source binding. An inactive read
binds typed zero without evaluating its key. -/
theorem guarded_scalarMap_read_emitted (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (declarations : List StateDecl)
    (current : LedgerState) (slots : List Slot) (reads : List Cell)
    (name destination : String) (keyTy valueTy : Ty) (key : Expr keyTy)
    (keyAdmission : ScalarExpression key) (supported : ScalarCellType valueTy)
    (guard : Option (Expr .bool)) (sourceAfter : GuardedSourceEffects.Frame)
    (before plan : Impact.Plan) (declaration : StateDecl)
    (declared : declarations.find? (·.name == name) = some declaration)
    (kind : declaration.kind = .map keyTy valueTy)
    (compiled : Impact.appendEffectWithActivity declarations
      (.readMap name destination keyTy valueTy key) guard before = .ok plan)
    (encoded : encodeState declarations current = some slots)
    (modulus : ctx.modulus = Field.modulus)
    (sourceStep : GuardedSourceEffects.step ctx guard
      (.readMap name destination keyTy valueTy key) (sourceEnv, current) = .ok sourceAfter)
    (candidateLookup : candidateEnv.lookup destination = sourceAfter.1.lookup destination)
    (keyAgreement : guard = none → key.eval ctx candidateEnv = key.eval ctx sourceEnv)
    (activeKeyAgreement : ∀ condition, guard = some condition →
      condition.eval ctx sourceEnv = .ok true →
      key.eval ctx candidateEnv = key.eval ctx sourceEnv)
    (guardAgreement : ∀ condition, guard = some condition →
      condition.eval ctx sourceEnv = condition.eval ctx candidateEnv) :
    ∃ (value : valueTy.Denote) (activity : Option Bool) (segment : List NativeState.Op),
      GuardedPlanExecution.evalChunk ctx candidateEnv guard
        (plan.operations.drop before.operations.length) = .ok (activity, segment) ∧
      NativeState.run segment ⟨[.vector slots], reads⟩ =
        some ⟨[.vector slots], reads ++
          (if activity.getD true then
            [field (scalar (GenericStateEncoding.number valueTy value))] else [])⟩ ∧
      sourceAfter = ((destination, Value.pack valueTy value) :: sourceEnv, current) ∧
      (activity = some false → value = GenericStateInputValues.sourceValue
        (scalarTypeOfCell supported) NativeRelation.zero) := by
  cases guard with
  | none =>
    have unguardedStep : SourceEffects.step ctx (.readMap name destination keyTy valueTy key)
        (sourceEnv, current) = .ok sourceAfter := by
      rw [GuardedSourceEffects.step_unguarded] at sourceStep
      exact sourceStep
    obtain ⟨slot, resolved, value, located, evaluated, checked, sourceShape⟩ :=
      GenericStateMapReadAuthentication.source_readMap_emitted ctx sourceEnv candidateEnv
        declarations current slots name destination keyTy valueTy key keyAdmission
        (keyAgreement rfl)
        sourceAfter before plan reads unguardedStep candidateLookup compiled declaration declared
        kind encoded modulus
    refine ⟨value, none, _, evalChunk_none_of_operations ctx candidateEnv
      (plan.operations.drop before.operations.length) _ evaluated, ?_, sourceShape, ?_⟩
    · simpa using checked
    · intro inactive
      cases inactive
  | some condition =>
    cases sourceGuard : condition.eval ctx sourceEnv with
    | error message =>
      have rejected := GuardedSourceEffects.step_guard_error ctx condition
        (.readMap name destination keyTy valueTy key) (sourceEnv, current) message
        (.readMap condition name destination keyTy valueTy key) sourceGuard
      rw [rejected] at sourceStep
      cases sourceStep
    | ok active =>
      have candidateGuard := (guardAgreement condition rfl).symm
      cases active with
      | false =>
        change runEffectsWithGuardsAndEnv ctx
          [.readMap name destination keyTy valueTy key] [some condition]
          sourceEnv current = .ok sourceAfter at sourceStep
        rw [GuardedScalarInput.run_inactive_scalarMap_read ctx sourceEnv current name
          destination key (scalarTypeOfCell supported) condition sourceGuard] at sourceStep
        have sourceShape := Except.ok.inj sourceStep
        have evalResult := evalChunk_some_inactive ctx candidateEnv condition
          (plan.operations.drop before.operations.length) (candidateGuard.trans sourceGuard)
        refine ⟨GenericStateInputValues.sourceValue (scalarTypeOfCell supported)
            NativeRelation.zero, some false, [], evalResult, ?_, ?_, ?_⟩
        · simp [NativeState.run]
        · exact sourceShape.symm
        · intro _
          rfl
      | true =>
        have activeSource : condition.eval ctx sourceEnv = .ok true := sourceGuard
        have activeCandidate : condition.eval ctx candidateEnv = .ok true :=
          candidateGuard.trans activeSource
        have keyEvalAgreement := activeKeyAgreement condition rfl activeSource
        obtain ⟨slot, resolved, value, located, evaluated, checked, sourceShape⟩ :=
          GuardedMapReadAuthentication.source_active_readMap_emitted ctx sourceEnv candidateEnv
            declarations current slots name destination keyTy valueTy key keyAdmission
            (scalarTypeOfCell supported) keyEvalAgreement condition activeSource
            (guardAgreement condition rfl) sourceAfter before plan reads sourceStep candidateLookup
            compiled declaration declared kind encoded modulus
        have evalResult := evalChunk_some_active_of_operations ctx candidateEnv condition
          (plan.operations.drop before.operations.length)
          (GenericStateVM.readMapOps slot
            (scalar (GenericStateEncoding.number keyTy resolved))
            (scalar (GenericStateEncoding.number valueTy value))) activeCandidate evaluated
        refine ⟨value, some true, _, evalResult, ?_, sourceShape, ?_⟩
        · simpa using checked
        · intro inactive
          cases inactive

end Noctium.Verification.GenericStateConverseRead
