import Noctium.Verification.GenericStateReadCellEvaluation
import Noctium.Verification.GenericStateSchemaSpans

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

private def scalarCellTypeOfCanonical {ty : Ty} {value : ty.Denote}
    (canonical : Canonical ty value) : ScalarCellType ty := by
  cases ty with
  | native => exact .native
  | bool => exact .bool
  | uint maximum => exact .uint maximum canonical.2.1
  | bytes _ | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ =>
    simp [Canonical, ScalarNormalization.sourceNumber?] at canonical

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
    let scalarType := scalarCellTypeOfCanonical valueCanonical
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

end Noctium.Verification.GenericStateConverseRead
