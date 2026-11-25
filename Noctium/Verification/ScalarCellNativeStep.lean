import Noctium.Verification.GenericStateCellAdmission
import Noctium.Verification.GenericStateConverseRead
import Noctium.Verification.GenericStateConverseWrite
import Noctium.Verification.GenericStateEffectValidation
import Noctium.Verification.GenericStateEncoding
import Noctium.Verification.GenericStatePrefixEnvironment
import Noctium.Verification.ScalarCellSourceReads

namespace Noctium.Verification.ScalarCellNativeStep

open Backend GenericStateCellAdmission GenericStateEffectValidation
  GenericStatePrefixEnvironment NativeRelation NativeState ScalarNormalization
  ScalarCellSourceReads

private def scalarTypeOfCell {ty : Ty} : ScalarCellType ty → ScalarType ty
  | .native => .native
  | .bool => .bool
  | .uint maximum _ => .uint maximum

private theorem scalarNumber_eq_encoding {ty : Ty}
    (scalar : ScalarCellType ty) (value : ty.Denote) :
    ScalarNormalization.number (scalarTypeOfCell scalar) value =
      GenericStateEncoding.number ty value := by
  cases scalar <;> rfl

/-- One accepted, unguarded scalar cell append compiles and runs against the
candidate environment. The native read tape records the source value emitted
by this effect. -/
theorem scalar_cell_native_step (ctx : EvalContext) (state : List StateDecl)
    (types nextTypes : TypeEnv) (effect : Effect)
    (sourceEnv complete : EvalEnv) (current : LedgerState)
    (sourceAfter : SourceEffects.Frame) (slots : List NativeState.Slot)
    (reads : List NativeState.Cell) (plan : Impact.Plan) (ordinal : Nat)
    (cell : ScalarCellEffect state effect)
    (operand : ScalarCellSourceReads.ScalarCellOperand effect)
    (validated : EffectValidation state types effect nextTypes)
    (sourceStep : SourceEffects.step ctx effect (sourceEnv, current) =
      .ok sourceAfter)
    (agrees : AgreesOnTypes types sourceEnv complete)
    (readCandidate : ∀ name destination ty,
      effect = .readCell name destination ty →
      complete.lookup destination = sourceAfter.1.lookup destination)
    (accepted : Impact.appendEffect state effect ({} : Impact.Plan) = .ok plan)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ segment nextSlots nextReads,
      plan.operations.mapM (GenericStateOps.evalOp ctx complete) = .ok segment ∧
      NativeState.run segment ⟨[.vector slots], reads⟩ =
        some ⟨[.vector nextSlots], nextReads⟩ ∧
      GenericStateEncoding.encodeState state sourceAfter.2 = some nextSlots ∧
      nextReads = reads ++
        (effectEntries effect ordinal sourceAfter).map
          (fun record => NativeState.field record.2) ∧
      AgreesOnTypes nextTypes sourceAfter.1 complete := by
  cases cell with
  | readCell name destination ty scalar declaration =>
    cases validated with
    | readCell validatedDeclaration fresh =>
      rcases declaration with
        ⟨sourceDeclaration, sourceDeclared, sourceKind, sourceAlignment⟩
      have sourceName : sourceDeclaration.name = name := by
        exact beq_iff_eq.mp (List.find?_some
          (p := fun item : StateDecl => item.name == name) sourceDeclared)
      obtain ⟨slot, value, located, evaluated, nativeRun, frame⟩ :=
        GenericStateConverseRead.source_readCell_native ctx sourceEnv complete
          state current slots name destination ty sourceAfter plan reads sourceStep
          (readCandidate name destination ty rfl)
          sourceDeclaration sourceDeclared sourceName sourceKind accepted encoded modulus
      have planEval : plan.operations.mapM
          (GenericStateOps.evalOp ctx complete) =
          .ok (GenericStateVM.readCellOps slot
            (NativeState.field (NativeRelation.scalar
              (GenericStateEncoding.number ty value)))) := evaluated
      have entriesShape : effectEntries (.readCell name destination ty)
          ordinal sourceAfter =
            [({name := destination, ty},
              NativeRelation.scalar (GenericStateEncoding.number ty value))] := by
        rw [frame]
        simp only [effectEntries, List.lookup_cons, beq_self_eq_true]
        rw [ScalarNormalization.valueNumber_pack_scalar ty value
          (scalarTypeOfCell scalar)]
        rw [scalarNumber_eq_encoding scalar value]
      have tapeShape :
          (effectEntries (.readCell name destination ty) ordinal sourceAfter).map
            (fun record => NativeState.field record.2) =
          [NativeState.field
            (NativeRelation.scalar (GenericStateEncoding.number ty value))] := by
        rw [entriesShape]
        rfl
      have candidate : complete.lookup destination =
          some (Value.pack ty value) := by
        rw [readCandidate name destination ty rfl, frame]
        simp
      have nextAgreement : AgreesOnTypes (types ++ [(destination, ty)])
          ((destination, Value.pack ty value) :: sourceEnv) complete :=
        extend_read types sourceEnv complete destination ty
          (Value.pack ty value) agrees fresh candidate
      refine ⟨GenericStateVM.readCellOps slot
          (NativeState.field (NativeRelation.scalar
            (GenericStateEncoding.number ty value))), slots,
        reads ++ (effectEntries (.readCell name destination ty)
          ordinal sourceAfter).map (fun record => NativeState.field record.2),
        planEval, ?_, ?_, rfl, ?_⟩
      · simpa only [tapeShape] using nativeRun
      · rw [frame]
        exact encoded
      · rw [frame]
        exact nextAgreement
  | writeCell name ty expression scalar declaration =>
    cases validated with
    | writeCell validatedDeclaration expressionValid =>
      have expressionAdmission : ScalarExpression expression := by
        simpa [ScalarCellSourceReads.ScalarCellOperand] using operand
      have candidateAgreement : expression.eval ctx complete =
          expression.eval ctx sourceEnv :=
        (eval_scoped types sourceEnv complete agrees ctx
          GenericStateEffectValidation.stateEffectCaps expression expressionValid).symm
      rcases declaration with
        ⟨sourceDeclaration, sourceDeclared, sourceKind, sourceAlignment⟩
      have sourceName : sourceDeclaration.name = name := by
        exact beq_iff_eq.mp (List.find?_some
          (p := fun item : StateDecl => item.name == name) sourceDeclared)
      obtain ⟨slot, value, nextSlots, located, evaluated, encodedNext,
          nativeRun, frame⟩ :=
        GenericStateConverseWrite.source_writeCell_chunk ctx sourceEnv complete
          state current slots name ty expression expression expressionAdmission
          sourceAfter ({} : Impact.Plan) plan reads sourceStep candidateAgreement
          sourceDeclaration sourceDeclared sourceName sourceKind accepted encoded
          distinct stateBound modulus
      have planEval : plan.operations.mapM
          (GenericStateOps.evalOp ctx complete) =
          .ok (GenericStateVM.writeCellOps slot
            (NativeState.field (NativeRelation.scalar
              (GenericStateEncoding.number ty value)))) := by
        simpa using evaluated
      refine ⟨GenericStateVM.writeCellOps slot
          (NativeState.field (NativeRelation.scalar
            (GenericStateEncoding.number ty value))), nextSlots, reads,
        planEval, ?_, encodedNext, ?_, ?_⟩
      · simpa using nativeRun
      · simp [ScalarCellSourceReads.effectEntries]
      · rw [frame]
        exact agrees

end Noctium.Verification.ScalarCellNativeStep
