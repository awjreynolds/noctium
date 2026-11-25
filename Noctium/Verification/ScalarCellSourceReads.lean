import Noctium.Verification.GenericStateCellAdmission
import Noctium.Verification.GenericStateSourceTrace
import Noctium.Verification.GenericStateWriteSourceTrace
import Noctium.Verification.GenericStateCheckedReadTrace
import Noctium.Verification.GenericStateEncoding
import Noctium.Verification.ScalarCircuit

namespace Noctium.Verification.ScalarCellSourceReads

open Backend NativeRelation ScalarNormalization

abbrev Frame := SourceEffects.Frame

/-- A source sequence admitted as reads and writes of declared scalar cells. -/
def ScalarCellEffects (state : List StateDecl) (effects : List Effect) : Prop :=
  ∀ effect ∈ effects, GenericStateCellAdmission.ScalarCellEffect state effect

/-- Only scalar source operands are needed to expose the typed value of a
successful cell write. -/
def ScalarCellOperand : Effect → Prop
  | .readCell .. => True
  | .writeCell _ _ value => ScalarExpression value
  | _ => False

/-- One successful source cell read contributes the compiler's read name and
the value bound in the frame after that source step. -/
def effectEntries (effect : Effect) (_ordinal : Nat)
    (after : Frame) : List (Impact.Read × Scalar) :=
  match effect with
  | .readCell _ destination ty =>
    [({name := destination, ty},
      match after.1.lookup destination with
      | some raw => scalar (ScalarNormalization.valueNumber raw)
      | none => zero)]
  | _ => []

def effectReadChunk (effect : Effect) (_ordinal : Nat) : List Impact.Read :=
  match effect with
  | .readCell _ destination ty => [{name := destination, ty}]
  | _ => []

def readChunks : List Effect → Nat → List (List Impact.Read)
  | [], _ => []
  | effect :: rest, ordinal =>
    let chunk := effectReadChunk effect ordinal
    chunk :: readChunks rest (ordinal + chunk.length)

/-- A recorded relation input retains a canonical value at its source type. -/
def CanonicalReadRecord (record : Impact.Read × Scalar) : Prop :=
  ∃ value : record.1.ty.Denote,
    Canonical record.1.ty value ∧
      record.2 = scalar (GenericStateEncoding.number record.1.ty value)

private def scalarTypeOfCell {ty : Ty} :
    GenericStateCellAdmission.ScalarCellType ty → ScalarType ty
  | .native => .native
  | .bool => .bool
  | .uint maximum _ => .uint maximum

private theorem scalarNumber_eq_encoding {ty : Ty}
    (scalar : GenericStateCellAdmission.ScalarCellType ty)
    (value : ty.Denote) :
    ScalarNormalization.number (scalarTypeOfCell scalar) value =
      GenericStateEncoding.number ty value := by
  cases scalar <;> rfl

/-- Scalar cell admission lets the source-step read lemma recover its typed,
canonical cell value. -/
theorem readCell_step_value (ctx : EvalContext) (env : EvalEnv)
    (ledger : LedgerState) (declarations : List StateDecl)
    (name destination : String) (ty : Ty)
    (source : GenericStateCellAdmission.ScalarCellEffect declarations
      (.readCell name destination ty))
    (after : Frame) (modulus : ctx.modulus = Field.modulus)
    (success : SourceEffects.step ctx (.readCell name destination ty)
      (env, ledger) = .ok after) :
    ∃ value : ty.Denote,
      ledger.cells.lookup name = some (Value.pack ty value) ∧
      Canonical ty value ∧
      after = ((destination, Value.pack ty value) :: env, ledger) := by
  cases source with
  | readCell _ _ _ scalar _ =>
    exact GenericStateSourceTrace.readCell_step_value
      (scalarTypeOfCell scalar) ctx env ledger name destination after modulus success

/-- Scalar operand admission lets the source-step write lemma expose the
exact typed update used by later reads. -/
theorem writeCell_step_value (ctx : EvalContext) (env : EvalEnv)
    (ledger : LedgerState) (declarations : List StateDecl)
    (name : String) (ty : Ty) (expression : Expr ty)
    (source : GenericStateCellAdmission.ScalarCellEffect declarations
      (.writeCell name ty expression))
    (expressionAdmission : ScalarExpression expression)
    (after : Frame) (modulus : ctx.modulus = Field.modulus)
    (success : SourceEffects.step ctx (.writeCell name ty expression)
      (env, ledger) = .ok after) :
    ∃ oldValue value : ty.Denote,
      ledger.cells.lookup name = some (Value.pack ty oldValue) ∧
      expression.eval ctx env = .ok value ∧ Canonical ty value ∧
      after = (env, {ledger with cells :=
        SourceEffects.updateEntry name (Value.pack ty value) ledger.cells}) := by
  cases source with
  | writeCell _ _ _ _ _ =>
    exact GenericStateWriteSourceTrace.writeCell_step_value ctx env ledger name ty
      expression after expressionAdmission modulus success

theorem effectEntries_names (effect : Effect) (ordinal : Nat)
    (after : Frame) :
    (effectEntries effect ordinal after).map Prod.fst = effectReadChunk effect ordinal := by
  cases effect <;> rfl

theorem effectEntries_length (effect : Effect) (ordinal : Nat)
    (after : Frame) :
    (effectEntries effect ordinal after).length =
      (effectReadChunk effect ordinal).length := by
  rw [← effectEntries_names, List.length_map]

/-- On a successful source cell read, the recorded field equals the canonical
encoding of the typed value bound by the production source step. -/
theorem effectEntries_readCell (ctx : EvalContext) (before after : Frame)
    (declarations : List StateDecl) (ordinal : Nat)
    (name destination : String) (ty : Ty)
    (source : GenericStateCellAdmission.ScalarCellEffect declarations
      (.readCell name destination ty))
    (modulus : ctx.modulus = Field.modulus)
    (success : SourceEffects.step ctx (.readCell name destination ty) before =
      .ok after) :
    ∃ value : ty.Denote,
      Canonical ty value ∧
      effectEntries (.readCell name destination ty) ordinal after =
        [({name := destination, ty}, scalar (GenericStateEncoding.number ty value))] := by
  rcases before with ⟨env, current⟩
  cases source with
  | readCell _ _ _ cellType declaration =>
    obtain ⟨value, _, canonical, final⟩ :=
      readCell_step_value ctx env current declarations name destination ty
        (.readCell name destination ty cellType declaration) after modulus success
    subst after
    refine ⟨value, canonical, ?_⟩
    simp [effectEntries]
    rw [ScalarNormalization.valueNumber_pack_scalar ty value
      (scalarTypeOfCell cellType)]
    rw [scalarNumber_eq_encoding cellType value]
    simp [GenericStateEncoding.number]

/-- Record source read values after each successful source step. The recursive
call receives the exact next frame, so reads after writes observe the update. -/
def sourceReadInputs (ctx : EvalContext) :
    List Effect → Nat → Frame → Except String (List (Impact.Read × Scalar) × Frame)
  | [], _, frame => .ok ([], frame)
  | effect :: rest, ordinal, frame => do
      let next ← SourceEffects.step ctx effect frame
      let head := effectEntries effect ordinal next
      let (tail, final) ← sourceReadInputs ctx rest (ordinal + head.length) next
      pure (head ++ tail, final)

theorem sourceReadInputs_cons (ctx : EvalContext) (effect : Effect)
    (rest : List Effect) (ordinal : Nat) (before after : Frame)
    (entries : List (Impact.Read × Scalar))
    (success : sourceReadInputs ctx (effect :: rest) ordinal before =
      .ok (entries, after)) :
    ∃ middle tail,
      SourceEffects.step ctx effect before = .ok middle ∧
      sourceReadInputs ctx rest
        (ordinal + (effectEntries effect ordinal middle).length) middle =
        .ok (tail, after) ∧
      entries = effectEntries effect ordinal middle ++ tail := by
  cases first : SourceEffects.step ctx effect before with
  | error message => simp [sourceReadInputs, first, bind, Except.bind] at success
  | ok middle =>
    cases later : sourceReadInputs ctx rest
        (ordinal + (effectEntries effect ordinal middle).length) middle with
    | error message =>
      simp [sourceReadInputs, first, later, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨tail, final⟩
      simp only [sourceReadInputs, first, later, bind, Except.bind,
        pure, Except.pure] at success
      cases success
      exact ⟨middle, tail, rfl, later, rfl⟩

theorem sourceReadInputs_of_fold (ctx : EvalContext) (effects : List Effect)
    (ordinal : Nat) (before after : Frame)
    (success : SourceEffects.fold ctx effects before = .ok after) :
    ∃ entries, sourceReadInputs ctx effects ordinal before = .ok (entries, after) := by
  induction effects generalizing ordinal before with
  | nil =>
    simp only [SourceEffects.fold_nil] at success
    cases success
    exact ⟨[], rfl⟩
  | cons effect rest ih =>
    obtain ⟨middle, first, later⟩ :=
      GenericStateSourceTrace.source_cons ctx effect rest before after success
    obtain ⟨tail, tailResult⟩ := ih (ordinal +
      (effectEntries effect ordinal middle).length) middle later
    refine ⟨effectEntries effect ordinal middle ++ tail, ?_⟩
    simp [sourceReadInputs, first, tailResult, bind, Except.bind,
      pure, Except.pure]

theorem sourceReadInputs_frame (ctx : EvalContext) (effects : List Effect)
    (ordinal : Nat) (before after : Frame)
    (entries : List (Impact.Read × Scalar))
    (success : sourceReadInputs ctx effects ordinal before = .ok (entries, after)) :
    SourceEffects.fold ctx effects before = .ok after := by
  induction effects generalizing ordinal before after entries with
  | nil =>
    simp only [sourceReadInputs] at success
    cases success
    rfl
  | cons effect rest ih =>
    obtain ⟨middle, tail, first, later, _⟩ :=
      sourceReadInputs_cons ctx effect rest ordinal before after entries success
    rw [SourceEffects.fold_cons, first]
    exact ih _ _ _ _ later

theorem sourceReadInputs_names (ctx : EvalContext) (effects : List Effect)
    (ordinal : Nat) (before after : Frame)
    (entries : List (Impact.Read × Scalar))
    (success : sourceReadInputs ctx effects ordinal before = .ok (entries, after)) :
    entries.map Prod.fst = (readChunks effects ordinal).flatten := by
  induction effects generalizing ordinal before after entries with
  | nil =>
    simp only [sourceReadInputs] at success
    cases success
    rfl
  | cons effect rest ih =>
    obtain ⟨middle, tail, first, later, entriesShape⟩ :=
      sourceReadInputs_cons ctx effect rest ordinal before after entries success
    simp only [entriesShape, List.map_append, readChunks, List.flatten_cons]
    rw [effectEntries_names]
    rw [← effectEntries_length effect ordinal middle]
    exact congrArg (effectReadChunk effect ordinal ++ ·)
      (ih _ _ _ _ later)

/-- Every successful source cell effect contributes only canonical typed
records. Writes contribute no reads. -/
private theorem sourceReadInputs_canonical_records (ctx : EvalContext)
    (state : List StateDecl) (effects : List Effect) (ordinal : Nat)
    (before after : Frame) (entries : List (Impact.Read × Scalar))
    (cellScope : ScalarCellEffects state effects)
    (operandScope : ∀ effect ∈ effects, ScalarCellOperand effect)
    (modulus : ctx.modulus = Field.modulus)
    (success : sourceReadInputs ctx effects ordinal before = .ok (entries, after)) :
    ∀ record ∈ entries, CanonicalReadRecord record := by
  induction effects generalizing ordinal before after entries with
  | nil =>
    simp only [sourceReadInputs] at success
    cases success
    intro record member
    simp at member
  | cons effect rest ih =>
    obtain ⟨middle, tail, first, later, entriesShape⟩ :=
      sourceReadInputs_cons ctx effect rest ordinal before after entries success
    have tailCells : ScalarCellEffects state rest := by
      intro next member
      exact cellScope next (List.mem_cons_of_mem effect member)
    have tailOperands : ∀ next ∈ rest, ScalarCellOperand next := by
      intro next member
      exact operandScope next (List.mem_cons_of_mem effect member)
    have tailCanonical := ih (ordinal + (effectEntries effect ordinal middle).length)
      middle after tail tailCells tailOperands later
    intro record member
    rw [entriesShape] at member
    rcases List.mem_append.mp member with headMember | tailMember
    · have headCell := cellScope effect (by simp)
      have headOperand := operandScope effect (by simp)
      cases headCell with
      | readCell name destination ty scalar declaration =>
        obtain ⟨value, canonical, headShape⟩ :=
          effectEntries_readCell ctx before middle state ordinal name destination ty
            (.readCell name destination ty scalar declaration) modulus first
        rw [headShape] at headMember
        simp only [List.mem_singleton] at headMember
        subst record
        exact ⟨value, canonical, rfl⟩
      | writeCell name ty expression scalar declaration =>
        have expressionAdmission : ScalarExpression expression := by
          simpa [ScalarCellOperand] using headOperand
        obtain ⟨_, _, _, _, _, _⟩ :=
          writeCell_step_value ctx before.1 before.2 state name ty expression
            (.writeCell name ty expression scalar declaration)
            expressionAdmission middle modulus first
        simp [effectEntries] at headMember
    · exact tailCanonical record tailMember

/-- The unguarded production runner and the source read recorder return the
same final frame. Records follow source order and carry canonical typed values. -/
theorem runEffectsWithGuardsAndEnv_source_cell_reads (ctx : EvalContext)
    (state : List StateDecl) (effects : List Effect) (ordinal : Nat)
    (initial final : Frame)
    (cellScope : ScalarCellEffects state effects)
    (operandScope : ∀ effect ∈ effects, ScalarCellOperand effect)
    (modulus : ctx.modulus = Field.modulus)
    (success : runEffectsWithGuardsAndEnv ctx effects [] initial.1 initial.2 =
      .ok final) :
    ∃ entries,
      sourceReadInputs ctx effects ordinal initial = .ok (entries, final) ∧
      entries.map Prod.fst = (readChunks effects ordinal).flatten ∧
      (∀ record ∈ entries, CanonicalReadRecord record) := by
  have runner : runEffectsWithEnv ctx effects initial.1 initial.2 = .ok final := by
    simpa [runEffectsWithGuardsAndEnv] using success
  have foldSuccess : SourceEffects.fold ctx effects initial = .ok final := by
    simpa [SourceEffects.runEffectsWithEnv_eq_fold] using runner
  obtain ⟨entries, instrumented⟩ :=
    sourceReadInputs_of_fold ctx effects ordinal initial final foldSuccess
  refine ⟨entries, instrumented, ?_, ?_⟩
  · exact sourceReadInputs_names ctx effects ordinal initial final entries instrumented
  · exact sourceReadInputs_canonical_records ctx state effects ordinal initial final
      entries cellScope operandScope modulus instrumented

private theorem scalarCellEffects_readScope {state : List StateDecl}
    {effects : List Effect} (scope : ScalarCellEffects state effects) :
    GenericStateCheckedReadTrace.ScalarReadEffects effects := by
  intro effect member
  cases scope effect member <;> constructor

private theorem readChunks_metadata (state : List StateDecl)
    (effects : List Effect) (ordinal : Nat)
    (scope : ScalarCellEffects state effects) :
    (readChunks effects ordinal).flatten.map
        GenericStateCheckedReadTrace.readMetadata =
      (GenericStateCheckedReadTrace.readChunks effects ordinal).flatten := by
  induction effects generalizing ordinal with
  | nil => rfl
  | cons effect rest ih =>
    have headShape :
        (effectReadChunk effect ordinal).map
            GenericStateCheckedReadTrace.readMetadata =
          GenericStateCheckedReadTrace.effectReadChunk effect ordinal := by
      cases scope effect (by simp) with
      | readCell _ _ _ _ _ => rfl
      | writeCell _ _ _ _ _ => simp [effectReadChunk,
          GenericStateCheckedReadTrace.effectReadChunk]
    have headLength :
        (effectReadChunk effect ordinal).length =
          (GenericStateCheckedReadTrace.effectReadChunk effect ordinal).length := by
      rw [← List.length_map, headShape]
    have tailScope : ScalarCellEffects state rest := by
      intro next member
      exact scope next (List.mem_cons_of_mem effect member)
    simp only [readChunks, GenericStateCheckedReadTrace.readChunks,
      List.flatten_cons, List.map_append, headShape]
    have tailMetadata :=
      ih (ordinal + (effectReadChunk effect ordinal).length) tailScope
    simpa only [headLength] using congrArg
      (GenericStateCheckedReadTrace.effectReadChunk effect ordinal ++ ·)
      tailMetadata

/-- For accepted unguarded scalar-cell effects, actual source read records
have the same ordered metadata as production lowering after public inputs. -/
theorem lowerWithEffectBoundaries_source_cell_read_metadata
    (ctx : EvalContext) (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (boundaries : List Nat) (initial final : Frame)
    (cellScope : ScalarCellEffects state entry.effects)
    (operandScope : ∀ effect ∈ entry.effects, ScalarCellOperand effect)
    (modulus : ctx.modulus = Field.modulus)
    (accepted : Impact.lowerWithEffectBoundaries state entry =
      .ok (plan, boundaries))
    (unguarded : entry.effectGuards = [])
    (success : runEffectsWithGuardsAndEnv ctx entry.effects entry.effectGuards
      initial.1 initial.2 = .ok final) :
    ∃ inputPlan entries,
      Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan ∧
      sourceReadInputs ctx entry.effects inputPlan.reads.length initial =
        .ok (entries, final) ∧
      (GenericStateCheckedReadTrace.planReadMetadata plan).drop
          inputPlan.reads.length =
        (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata ∧
      (∀ record ∈ entries, CanonicalReadRecord record) := by
  have metadata :=
    GenericStateCheckedReadTrace.lowerWithEffectBoundaries_read_metadata
      state entry plan boundaries accepted unguarded
      (scalarCellEffects_readScope cellScope)
  obtain ⟨inputPlan, inputAccepted, metadataShape⟩ := metadata
  have sourceSuccess : runEffectsWithGuardsAndEnv ctx entry.effects []
      initial.1 initial.2 = .ok final := by
    simpa [unguarded] using success
  obtain ⟨entries, instrumented, _, canonical⟩ :=
    runEffectsWithGuardsAndEnv_source_cell_reads ctx state entry.effects
      inputPlan.reads.length initial final cellScope operandScope modulus sourceSuccess
  have sourceNames := sourceReadInputs_names ctx entry.effects
    inputPlan.reads.length initial final entries instrumented
  have metadataSuffix :
      (GenericStateCheckedReadTrace.planReadMetadata plan).drop
          inputPlan.reads.length =
        (GenericStateCheckedReadTrace.readChunks entry.effects
          inputPlan.reads.length).flatten := by
    rw [metadataShape]
    simp [GenericStateCheckedReadTrace.planReadMetadata]
  refine ⟨inputPlan, entries, inputAccepted, instrumented, ?_, canonical⟩
  calc
    (GenericStateCheckedReadTrace.planReadMetadata plan).drop
        inputPlan.reads.length =
      (GenericStateCheckedReadTrace.readChunks entry.effects
        inputPlan.reads.length).flatten := metadataSuffix
    _ = (readChunks entry.effects inputPlan.reads.length).flatten.map
          GenericStateCheckedReadTrace.readMetadata :=
      (readChunks_metadata state entry.effects inputPlan.reads.length cellScope).symm
    _ = (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata := by
      rw [← sourceNames]

end Noctium.Verification.ScalarCellSourceReads
