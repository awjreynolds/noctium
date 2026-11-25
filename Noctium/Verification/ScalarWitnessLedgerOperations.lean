import Noctium.Verification.ScalarExpressionLowering
import Noctium.Verification.ScalarWitnessAssembly
import Noctium.Verification.ScalarStateExtensions
import Noctium.Verification.ScalarNormalizationSoundness

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarLowering
open ScalarNormalization ScalarWitness ScalarAllocationOutputFrame

private def AliasCompletes (hash : Hash) (inputs : Assignment)
    (normalAliases : Backend.Native.AliasEnvironment) (values : EvalEnv)
    (operation : StateM Zkir.LowerState α) : Prop :=
  ∀ witness state, LowerStateMeaning hash witness state →
    LowerAliasAgreement hash inputs witness normalAliases state.aliases values →
    (operation.run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength →
    ∃ extension : PrefixExtension hash witness state (operation.run state).2,
      LowerAliasAgreement hash inputs extension.witness normalAliases
        (operation.run state).2.aliases values

private theorem stateRunBind {α β} (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β) (state : Zkir.LowerState) :
    (do let value ← first; next value).run state =
      (next (first.run state).1).run (first.run state).2 := rfl

private def PrefixExtension.trans {hash : Hash} {beforeWitness middleWitness : Assignment}
    {before middle after : Zkir.LowerState}
    (first : PrefixExtension hash beforeWitness before middle)
    (second : PrefixExtension hash middleWitness middle after)
    (firstFrame : Zkir.OutputCapacityFrame before middle)
    (sameWitness : middleWitness = first.witness) :
    PrefixExtension hash beforeWitness before after := by
  subst middleWitness
  refine ⟨second.witness, second.meaning, second.aliases.trans first.aliases, ?_⟩
  intro name scope
  exact (second.frame name (InScope.mono firstFrame.next scope)).trans
    (first.frame name scope)

private theorem AliasCompletes.pure (hash : Hash) (inputs : Assignment)
    (normalAliases : Backend.Native.AliasEnvironment) (values : EvalEnv) (value : α) :
    AliasCompletes hash inputs normalAliases values (pure value) := by
  intro witness state meaning aliases budget
  exact ⟨{witness, meaning, aliases := rfl, frame := by intro name _; rfl}, aliases⟩

private theorem AliasCompletes.bind (hash : Hash) (inputs : Assignment)
    (normalAliases : Backend.Native.AliasEnvironment) (values : EvalEnv)
    (first : StateM Zkir.LowerState α) (next : α → StateM Zkir.LowerState β)
    (firstFrame : Zkir.PreservesOutputCapacityFrame first)
    (nextFrame : ∀ value, Zkir.PreservesOutputCapacityFrame (next value))
    (firstComplete : AliasCompletes hash inputs normalAliases values first)
    (nextComplete : ∀ value, AliasCompletes hash inputs normalAliases values (next value)) :
    AliasCompletes hash inputs normalAliases values (first >>= next) := by
  intro witness state meaning aliases budget
  have fullBudget : ((next (first.run state).1).run (first.run state).2).2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    change ((first >>= next).run state).2.next ≤ _
    exact budget
  have firstBudget : (first.run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength :=
    Nat.le_trans (nextFrame (first.run state).1 (first.run state).2).next fullBudget
  obtain ⟨left, leftAliases⟩ := firstComplete witness state meaning aliases firstBudget
  obtain ⟨right, rightAliases⟩ := nextComplete (first.run state).1 left.witness
    (first.run state).2 left.meaning leftAliases fullBudget
  let composed : PrefixExtension hash witness state
      ((first >>= next).run state).2 :=
    PrefixExtension.trans left right (firstFrame state) rfl
  refine ⟨composed, ?_⟩
  change LowerAliasAgreement hash inputs right.witness normalAliases
    ((next (first.run state).1).run (first.run state).2).2.aliases values
  exact rightAliases

private theorem AliasCompletes.loop (hash : Hash) (inputs : Assignment)
    (normalAliases : Backend.Native.AliasEnvironment) (values : EvalEnv)
    (items : List α) (initial : β) (body : α → StateM Zkir.LowerState Unit)
    (frames : ∀ item ∈ items, Zkir.PreservesOutputCapacityFrame (body item))
    (complete : ∀ item ∈ items, AliasCompletes hash inputs normalAliases values (body item)) :
    AliasCompletes hash inputs normalAliases values
      (ForIn.forIn items initial
        (fun item _ => do body item; Pure.pure (ForInStep.yield initial))) := by
  induction items with
  | nil => exact AliasCompletes.pure hash inputs normalAliases values initial
  | cons item rest ih =>
    rw [List.forIn_cons]
    simp only [bind_assoc, pure_bind]
    change AliasCompletes hash inputs normalAliases values
      (body item >>= fun _ => ForIn.forIn rest initial
        (fun item _ => do body item; Pure.pure (ForInStep.yield initial)))
    apply AliasCompletes.bind hash inputs normalAliases values
      (first := body item)
      (next := fun _ => ForIn.forIn rest initial
        (fun item _ => do body item; Pure.pure (ForInStep.yield initial)))
      (frames item (by simp))
    · intro ignored
      exact Zkir.forIn_preservesOutputCapacityFrame_of_mem rest initial _ (by
        intro restItem member accumulator
        exact Zkir.bind_preservesOutputCapacityFrame _ _
          (frames restItem (List.mem_cons_of_mem _ member))
          (fun _ => Zkir.pure_preservesOutputCapacityFrame _))
    · exact complete item (by simp)
    · intro ignored
      apply ih
      · intro restItem member
        exact frames restItem (List.mem_cons_of_mem _ member)
      · intro restItem member
        exact complete restItem (List.mem_cons_of_mem _ member)

private structure LoweredFieldList (hash : Hash) (inputs beforeWitness : Assignment)
    (normalAliases : Backend.Native.AliasEnvironment) (values : EvalEnv)
    (fields : List Impact.Scalar) (before : Zkir.LowerState) where
  texts : List String
  after : Zkir.LowerState
  extension : PrefixExtension hash beforeWitness before after
  aliases : LowerAliasAgreement hash inputs extension.witness normalAliases after.aliases values
  scopes : ∀ text ∈ texts, TextScope after.next text
  run : (fields.mapM Zkir.lowerExpr).run before = (texts, after)

private theorem outputCapacity_first_stage_budget {α β : Type} (state : Zkir.LowerState)
    (first : StateM Zkir.LowerState α) (next : α → StateM Zkir.LowerState β)
    (nextFrame : ∀ value, Zkir.PreservesOutputCapacityFrame (next value))
    (budget : ((first >>= next).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    (first.run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
  have suffixBudget : ((next (first.run state).1).run (first.run state).2).2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    change ((first >>= next).run state).2.next ≤ _
    exact budget
  exact Nat.le_trans (nextFrame (first.run state).1 (first.run state).2).next suffixBudget

private theorem lowerFields_frame (fields : List Impact.Scalar)
    (admitted : ∀ field ∈ fields, ScalarExpression field) :
    Zkir.PreservesOutputCapacityFrame (fields.mapM Zkir.lowerExpr) := by
  induction fields with
  | nil => simp only [List.mapM_nil]; exact Zkir.pure_preservesOutputCapacityFrame _
  | cons field tail ih =>
    have tailAdmission : ∀ item ∈ tail, ScalarExpression item := by
      intro item member
      exact admitted item (List.mem_cons_of_mem _ member)
    have restFrame := ih tailAdmission
    have firstFrame := lowerExpr_admitted_preservesOutputCapacityFrame field
      (admitted field (by simp))
    have continuationFrame (text : String) :
        Zkir.PreservesOutputCapacityFrame (do
          let rest ← tail.mapM Zkir.lowerExpr
          pure (text :: rest)) := by
      apply Zkir.bind_preservesOutputCapacityFrame _ _ restFrame
      intro rest
      exact Zkir.pure_preservesOutputCapacityFrame _
    simpa only [List.mapM_cons] using
      Zkir.bind_preservesOutputCapacityFrame (Zkir.lowerExpr field)
        (fun text => do
          let rest ← tail.mapM Zkir.lowerExpr
          pure (text :: rest)) firstFrame continuationFrame

private theorem lowerFields_result (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (normalAliases : Backend.Native.AliasEnvironment) (values : EvalEnv)
    (types : TypeEnv) (sourceAliases : AliasAgreement hash inputs normalAliases values)
    (fields : List Impact.Scalar)
    (admitted : ∀ field ∈ fields, ScalarExpression field)
    (validated : ∀ field ∈ fields,
      field.validate Capabilities.crypto types = .ok ())
    (evaluated : ∀ field ∈ fields, ∃ value, field.eval ctx values = .ok value)
    (witness : Assignment) (state : Zkir.LowerState)
    (meaning : LowerStateMeaning hash witness state)
    (aliases : LowerAliasAgreement hash inputs witness normalAliases state.aliases values)
    (budget : (fields.mapM Zkir.lowerExpr).run state |>.2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (LoweredFieldList hash inputs witness normalAliases values fields state) := by
  induction fields generalizing witness state with
  | nil =>
    exact ⟨{
      texts := []
      after := state
      extension := ⟨witness, meaning, rfl, by intro name _; rfl⟩
      aliases := aliases
      scopes := by simp
      run := by rfl
    }⟩
  | cons field tail ih =>
    let fieldAdmission := admitted field (by simp)
    let fieldValidation := validated field (by simp)
    obtain ⟨fieldValue, fieldEvaluation⟩ := evaluated field (by simp)
    have tailAdmission : ∀ item ∈ tail, ScalarExpression item := by
      intro item member
      exact admitted item (List.mem_cons_of_mem _ member)
    have tailValidated : ∀ item ∈ tail, item.validate Capabilities.crypto types = .ok () := by
      intro item member
      exact validated item (List.mem_cons_of_mem _ member)
    have tailEvaluated : ∀ item ∈ tail, ∃ value, item.eval ctx values = .ok value := by
      intro item member
      exact evaluated item (List.mem_cons_of_mem _ member)
    have firstFrame : Zkir.PreservesOutputCapacityFrame (Zkir.lowerExpr field) :=
      lowerExpr_admitted_preservesOutputCapacityFrame field fieldAdmission
    have restFrame := lowerFields_frame tail tailAdmission
    have continuationFrame (text : String) :
        Zkir.PreservesOutputCapacityFrame (do
          let rest ← tail.mapM Zkir.lowerExpr
          pure (text :: rest)) := by
      apply Zkir.bind_preservesOutputCapacityFrame _ _ restFrame
      intro rest
      exact Zkir.pure_preservesOutputCapacityFrame _
    have mapCons : (field :: tail).mapM Zkir.lowerExpr = (do
        let text ← Zkir.lowerExpr field
        let rest ← tail.mapM Zkir.lowerExpr
        pure (text :: rest)) := by
      simp only [List.mapM_cons]
    have budget' : ((do
        let text ← Zkir.lowerExpr field
        let rest ← tail.mapM Zkir.lowerExpr
        pure (text :: rest)).run state).2.next ≤
          Native.maxInstructions * Native.maxVectorLength := by
      rw [← mapCons]
      exact budget
    have firstBudget := outputCapacity_first_stage_budget state (Zkir.lowerExpr field)
      (fun text => do
        let rest ← tail.mapM Zkir.lowerExpr
        pure (text :: rest)) continuationFrame budget'
    obtain ⟨first⟩ := ScalarExpressionLowering.lowerExpr_complete field fieldAdmission
      ctx hash implementation inputs witness state normalAliases values types fieldValue
      fieldValidation fieldEvaluation sourceAliases aliases meaning firstBudget
    have restBudget : (tail.mapM Zkir.lowerExpr).run first.finalState |>.2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
      have bound := budget'
      rw [stateRunBind, first.run] at bound
      simp only [StateT.run_bind, StateT.run_pure] at bound
      exact bound
    have lowerAliasAfterFirst : LowerAliasAgreement hash inputs first.finalWitness
        normalAliases first.finalState.aliases values := by
      have preserved := LowerAliasAgreement.of_frame hash inputs witness first.finalWitness
        state.next normalAliases state.aliases values aliases meaning.aliases first.frame
      simpa only [first.aliasesPreserved] using preserved
    obtain ⟨rest⟩ := ih tailAdmission tailValidated tailEvaluated
      first.finalWitness first.finalState first.stateMeaning lowerAliasAfterFirst restBudget
    have firstFrameAt : Zkir.OutputCapacityFrame state first.finalState := by
      simpa only [first.run] using firstFrame state
    let extension : PrefixExtension hash witness state rest.after :=
      PrefixExtension.trans
        ⟨first.finalWitness, first.stateMeaning, first.aliasesPreserved, first.frame⟩
        rest.extension firstFrameAt rfl
    refine ⟨{
      texts := first.text :: rest.texts
      after := rest.after
      extension := extension
      aliases := by simpa [extension, PrefixExtension.trans] using rest.aliases
      scopes := ?_
      run := ?_
    }⟩
    · intro text member
      rcases List.mem_cons.mp member with firstText | restText
      · cases firstText
        simpa only [rest.run] using
          TextScope.mono (restFrame first.finalState).next first.textScope
      · exact rest.scopes text restText
    · rw [mapCons, stateRunBind, first.run]
      change (do
        let tailTexts ← tail.mapM Zkir.lowerExpr
        pure (first.text :: tailTexts)).run first.finalState = _
      rw [stateRunBind, rest.run]
      rfl

private theorem bindPublicGuarded_true (texts : List String) :
    Zkir.bindPublicGuarded (.bool true) texts = Zkir.bindPublic texts := by
  simp [Zkir.bindPublicGuarded, Zkir.bindPublic, Zkir.lowerExpr]

private def lowerLedgerFieldGroup (fields : List Impact.Scalar) :
    StateM Zkir.LowerState Unit := do
  let texts ← fields.mapM Zkir.lowerExpr
  Zkir.bindPublicGuarded (.bool true) texts

private theorem lowerLedgerFieldGroup_frame (fields : List Impact.Scalar)
    (admitted : ∀ field ∈ fields, ScalarExpression field) :
    Zkir.PreservesOutputCapacityFrame (lowerLedgerFieldGroup fields) := by
  apply Zkir.bind_preservesOutputCapacityFrame _ _ (lowerFields_frame fields admitted)
  intro texts
  simpa only [bindPublicGuarded_true, Zkir.bindPublic] using
    Zkir.emit_preservesOutputCapacityFrame "impact"
      [("guard", toJson ("0x01" : String)), ("inputs", toJson texts)]

private theorem lowerLedgerFieldGroup_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (normalAliases : Backend.Native.AliasEnvironment) (values : EvalEnv)
    (types : TypeEnv) (sourceAliases : AliasAgreement hash inputs normalAliases values)
    (fields : List Impact.Scalar)
    (admitted : ∀ field ∈ fields, ScalarExpression field)
    (validated : ∀ field ∈ fields,
      field.validate Capabilities.crypto types = .ok ())
    (evaluated : ∀ field ∈ fields, ∃ value, field.eval ctx values = .ok value) :
    AliasCompletes hash inputs normalAliases values (lowerLedgerFieldGroup fields) := by
  intro witness state meaning aliases budget
  have fieldsFrame := lowerFields_frame fields admitted
  have impactFrame (texts : List String) :
      Zkir.PreservesOutputCapacityFrame (Zkir.bindPublicGuarded (.bool true) texts) := by
    simpa only [bindPublicGuarded_true, Zkir.bindPublic] using
      Zkir.emit_preservesOutputCapacityFrame "impact"
        [("guard", toJson ("0x01" : String)), ("inputs", toJson texts)]
  have fieldsBudget : (fields.mapM Zkir.lowerExpr).run state |>.2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    apply outputCapacity_first_stage_budget state (fields.mapM Zkir.lowerExpr)
      (fun texts => Zkir.bindPublicGuarded (.bool true) texts) impactFrame
    simpa only [lowerLedgerFieldGroup, stateRunBind] using budget
  obtain ⟨lowered⟩ := lowerFields_result ctx hash implementation inputs normalAliases values
    types sourceAliases fields admitted validated evaluated witness state meaning aliases fieldsBudget
  let emittedState := (Zkir.bindPublic lowered.texts).run lowered.after |>.2
  have emittedMeaning := emit_impact hash lowered.extension.witness lowered.after
    lowered.extension.meaning lowered.texts lowered.scopes
  have run : (lowerLedgerFieldGroup fields).run state =
      (Zkir.bindPublic lowered.texts).run lowered.after := by
    simp only [lowerLedgerFieldGroup, stateRunBind, lowered.run, bindPublicGuarded_true]
  let extension : PrefixExtension hash witness state
      ((lowerLedgerFieldGroup fields).run state).2 := by
    refine ⟨lowered.extension.witness, ?_, ?_, ?_⟩
    · simpa only [run] using emittedMeaning
    · have emitsKeepAliases : emittedState.aliases = lowered.after.aliases := by
        rfl
      rw [run, emitsKeepAliases]
      exact lowered.extension.aliases
    · intro name inScope
      exact lowered.extension.frame name inScope
  have finalAliases : LowerAliasAgreement hash inputs extension.witness normalAliases
      ((lowerLedgerFieldGroup fields).run state).2.aliases values := by
    have extensionWitness : extension.witness = lowered.extension.witness := by rfl
    rw [extensionWitness]
    rw [run]
    change LowerAliasAgreement hash inputs lowered.extension.witness normalAliases
      lowered.after.aliases values
    exact lowered.aliases
  exact ⟨extension, finalAliases⟩

private def lowerLedgerOperationGroups (operation : Impact.Op) :
    StateM Zkir.LowerState Unit := do
  for fields in operation.fieldGroups do
    Zkir.bindPublicGuarded (.bool true) (← fields.mapM Zkir.lowerExpr)

private theorem lowerLedgerOperationGroups_frame (operation : Impact.Op)
    (admitted : ∀ fields ∈ operation.fieldGroups, ∀ field ∈ fields, ScalarExpression field) :
    Zkir.PreservesOutputCapacityFrame (lowerLedgerOperationGroups operation) := by
  unfold lowerLedgerOperationGroups
  apply Zkir.forIn_preservesOutputCapacityFrame_of_mem
  intro fields member _
  apply Zkir.bind_preservesOutputCapacityFrame _ _
    (lowerFields_frame fields (admitted fields member))
  intro texts
  apply Zkir.bind_preservesOutputCapacityFrame _ _
  · simpa [Zkir.bindPublicGuarded, Zkir.lowerExpr] using
      Zkir.emit_preservesOutputCapacityFrame "impact"
        [("guard", toJson ("0x01" : String)), ("inputs", toJson texts)]
  · intro _
    exact Zkir.pure_preservesOutputCapacityFrame _

private theorem lowerLedgerOperationGroups_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (normalAliases : Backend.Native.AliasEnvironment) (values : EvalEnv)
    (types : TypeEnv) (sourceAliases : AliasAgreement hash inputs normalAliases values)
    (operation : Impact.Op)
    (admitted : ∀ fields ∈ operation.fieldGroups, ∀ field ∈ fields, ScalarExpression field)
    (validated : ∀ fields ∈ operation.fieldGroups, ∀ field ∈ fields,
      field.validate Capabilities.crypto types = .ok ())
    (evaluated : ∀ fields ∈ operation.fieldGroups, ∀ field ∈ fields,
      ∃ value, field.eval ctx values = .ok value) :
    AliasCompletes hash inputs normalAliases values (lowerLedgerOperationGroups operation) := by
  apply AliasCompletes.loop hash inputs normalAliases values operation.fieldGroups ()
    (fun fields => lowerLedgerFieldGroup fields)
  · intro fields member
    exact lowerLedgerFieldGroup_frame fields (admitted fields member)
  · intro fields member
    exact lowerLedgerFieldGroup_complete ctx hash implementation inputs normalAliases values
      types sourceAliases fields (admitted fields member) (validated fields member)
      (evaluated fields member)

private def selectedLedgerGuard (plan : Impact.Plan) (item : Impact.Op × Nat) :
    Expr .bool := ((plan.activityGuards[item.2]?).getD none).getD (.bool true)

private theorem selectedLedgerGuard_eq_true (plan : Impact.Plan)
    (allNone : plan.activityGuards.all Option.isNone = true) (item : Impact.Op × Nat) :
    selectedLedgerGuard plan item = .bool true := by
  unfold selectedLedgerGuard
  cases selected : plan.activityGuards[item.2]? with
  | none => rfl
  | some activity =>
    have present : activity ∈ plan.activityGuards := List.mem_of_getElem? selected
    have noneActivity : Option.isNone activity = true := (List.all_eq_true.mp allNone) _ present
    cases activity with
    | none => simp
    | some guard => simp at noneActivity

private theorem lowerLedgerOperationFrame (plan : Impact.Plan)
    (admitted : ∀ operation ∈ plan.operations,
      ∀ fields ∈ operation.fieldGroups,
      ∀ field ∈ fields, ScalarExpression field)
    (item : Impact.Op × Nat) (member : item ∈ plan.operations.zipIdx) :
    Zkir.PreservesOutputCapacityFrame (lowerLedgerOperationGroups item.1) :=
  lowerLedgerOperationGroups_frame item.1 (fun fields group field present =>
    admitted item.1 (List.fst_mem_of_mem_zipIdx member) fields group field present)

private theorem lowerLedgerOperations_aliasComplete_unGuarded (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (normalAliases : Backend.Native.AliasEnvironment) (values : EvalEnv)
    (types : TypeEnv) (sourceAliases : AliasAgreement hash inputs normalAliases values)
    (plan : Impact.Plan)
    (allNone : plan.activityGuards.all Option.isNone = true)
    (admitted : ∀ operation ∈ plan.operations, ∀ fields ∈ operation.fieldGroups,
      ∀ field ∈ fields, ScalarExpression field)
    (validated : ∀ operation ∈ plan.operations, ∀ fields ∈ operation.fieldGroups,
      ∀ field ∈ fields, field.validate Capabilities.crypto types = .ok ())
    (evaluated : ∀ operation ∈ plan.operations, ∀ fields ∈ operation.fieldGroups,
      ∀ field ∈ fields, ∃ value, field.eval ctx values = .ok value) :
    AliasCompletes hash inputs normalAliases values (Zkir.lowerLedgerOperations plan) := by
  have operationFrame (item : Impact.Op × Nat) (member : item ∈ plan.operations.zipIdx) :
      Zkir.PreservesOutputCapacityFrame (lowerLedgerOperationGroups item.1) :=
    lowerLedgerOperationFrame plan admitted item member
  have operationComplete (item : Impact.Op × Nat) (member : item ∈ plan.operations.zipIdx) :
      AliasCompletes hash inputs normalAliases values (lowerLedgerOperationGroups item.1) := by
    have opMember : item.1 ∈ plan.operations := List.fst_mem_of_mem_zipIdx member
    apply lowerLedgerOperationGroups_complete ctx hash implementation inputs normalAliases values
      types sourceAliases item.1
    · intro fields group field present
      exact admitted item.1 opMember fields group field present
    · intro fields group field present
      exact validated item.1 opMember fields group field present
    · intro fields group field present
      exact evaluated item.1 opMember fields group field present
  have loopComplete := AliasCompletes.loop hash inputs normalAliases values
    plan.operations.zipIdx () (fun item => lowerLedgerOperationGroups item.1)
    operationFrame operationComplete
  have exactStage : Zkir.lowerLedgerOperations plan =
      ForIn.forIn plan.operations.zipIdx ()
        (fun item _ => do
          let guard := selectedLedgerGuard plan item
          for fields in item.1.fieldGroups do
            Zkir.bindPublicGuarded guard (← fields.mapM Zkir.lowerExpr)
          pure (ForInStep.yield ())) := by
    rfl
  rw [exactStage]
  have bodyEq : (fun (item : Impact.Op × Nat) (_ : Unit) => do
        let guard := selectedLedgerGuard plan item
        for fields in item.1.fieldGroups do
          Zkir.bindPublicGuarded guard (← fields.mapM Zkir.lowerExpr)
        pure (ForInStep.yield ())) =
      (fun (item : Impact.Op × Nat) (_ : Unit) => do
        lowerLedgerOperationGroups item.1
        pure (ForInStep.yield ())) := by
    funext item accumulator
    simp only [selectedLedgerGuard_eq_true plan allNone item]
    rfl
  rw [bodyEq]
  exact loopComplete

/-- Witness completeness for the production ledger operation stage when no
activity guards are requested. Field order and grouping follow `Op.fieldGroups`;
source acceptance, evaluation, alias meaning, and output capacity stay explicit. -/
theorem lowerLedgerOperations_complete_unGuarded (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (normalAliases : Backend.Native.AliasEnvironment) (values : EvalEnv)
    (entry : Entrypoint) (plan : Impact.Plan)
    (typed : TypedEnvironment hash inputs normalAliases values (plan.typeEnvironment entry))
    (witness : Assignment) (state : Zkir.LowerState)
    (meaning : LowerStateMeaning hash witness state)
    (lowerAliases : LowerAliasAgreement hash inputs witness normalAliases state.aliases values)
    (allNone : plan.activityGuards.all Option.isNone = true)
    (admitted : ∀ operation ∈ plan.operations, ∀ fields ∈ operation.fieldGroups,
      ∀ field ∈ fields, ScalarExpression field)
    (validated : ∀ operation ∈ plan.operations, ∀ fields ∈ operation.fieldGroups,
      ∀ field ∈ fields,
        field.validate Capabilities.crypto (plan.typeEnvironment entry) = .ok ())
    (evaluated : ∀ operation ∈ plan.operations, ∀ fields ∈ operation.fieldGroups,
      ∀ field ∈ fields, ∃ value, field.eval ctx values = .ok value)
    (budget : (Zkir.lowerLedgerOperations plan).run state |>.2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    ∃ extension : PrefixExtension hash witness state
        ((Zkir.lowerLedgerOperations plan).run state).2,
      LowerAliasAgreement hash inputs extension.witness normalAliases
        ((Zkir.lowerLedgerOperations plan).run state).2.aliases values := by
  exact (lowerLedgerOperations_aliasComplete_unGuarded ctx hash implementation inputs normalAliases
    values (plan.typeEnvironment entry) typed.aliases plan allNone admitted validated evaluated)
    witness state meaning lowerAliases budget

end Noctium.Verification.ScalarWitnessConstruction
