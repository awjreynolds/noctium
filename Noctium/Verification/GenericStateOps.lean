import Noctium.Backend.Impact
import Noctium.Verification.NativeState

namespace Noctium.Verification.GenericStateOps
open Backend NativeRelation NativeState

private theorem scalar_one_eq : scalar 1 = one := by
  apply Fin.ext
  decide

def ScalarAligned : Impact.Aligned → Prop
  | .field _ | .bit _ | .bitExpr _ => True
  | _ => False

/-- The independent scalar VM models only the operations represented by
`NativeState.Op`. Keep the supported fragment explicit so newer ledger and
cryptographic operations fail closed instead of acquiring placeholder
semantics. -/
def ScalarOperation : Impact.Op → Prop
  | .dup | .index _ _ | .member | .insert _ => True
  | .mapIndex _ (.field _) => True
  | .push value _ | .popeq value => ScalarAligned value
  | _ => False

def evalAligned (ctx : EvalContext) (env : EvalEnv) : Impact.Aligned → Except String Cell
  | .field expression => do
    pure (field (scalar (← expression.eval ctx env)))
  | .bit value => pure (boolean value)
  | .bitExpr expression => boolean <$> expression.eval ctx env
  | _ => .error "unsupported Impact alignment in scalar state interpreter"

/-- Dynamic membership results keep the byte-aligned Bool cell used by the
ledger VM instead of being reinterpreted as a field cell. -/
theorem evalAligned_bitExpr (ctx : EvalContext) (env : EvalEnv)
    (expression : Expr .bool) :
    evalAligned ctx env (.bitExpr expression) = boolean <$> expression.eval ctx env := rfl

example (ctx : EvalContext) (env : EvalEnv) :
    evalAligned ctx env (.bitExpr (.bool true)) = .ok (boolean true) := by
  simp [evalAligned, Expr.eval, Except.map, Functor.map]

example (ctx : EvalContext) (env : EvalEnv) :
    evalAligned ctx env (.bitExpr (.bool false)) = .ok (boolean false) := by
  simp [evalAligned, Expr.eval, Except.map, Functor.map]

/-- Interpret a symbolic Impact operation with the same source environment
used by the ordered effect evaluator. Evaluation errors reject the native
schedule instead of inventing a field value. -/
def evalOp (ctx : EvalContext) (env : EvalEnv) : Impact.Op → Except String Op
  | .dup => pure .dup
  | .index slot path => pure (.index slot path)
  | .mapIndex slot (.field key) => do
    pure (.mapIndex slot (← evalAligned ctx env (.field key)))
  | .push value storage => do pure (.push (← evalAligned ctx env value) storage)
  | .popeq value => do pure (.popeq (← evalAligned ctx env value))
  | .member => pure .member
  | .insert levels => pure (.insert levels)
  | _ => .error "unsupported Impact operation in scalar state interpreter"

def evalPlan (ctx : EvalContext) (env : EvalEnv) (plan : Impact.Plan) :
    Except String (List Op) := plan.operations.mapM (evalOp ctx env)

/-- Scalar map keys arrive through Impact's field alignment, including Bool
keys normalized to a native 0 or 1 expression. -/
theorem evalOp_mapIndex_field (ctx : EvalContext) (env : EvalEnv)
    (slot value : Nat) (key : Impact.Scalar)
    (evaluated : key.eval ctx env = .ok value) :
    evalOp ctx env (.mapIndex slot (.field key)) =
      .ok (.mapIndex slot (field (scalar value))) := by
  simp [evalOp, evalAligned, evaluated, Except.map, Functor.map]

theorem evalOp_supported (ctx : EvalContext) (env : EvalEnv)
    (operation : Impact.Op) (native : Op)
    (accepted : evalOp ctx env operation = .ok native) :
    ScalarOperation operation := by
  cases operation with
  | dup | index _ _ | member | insert _ => simp [ScalarOperation]
  | mapIndex _ key =>
    cases key with
    | field _ => simp [ScalarOperation]
    | foreignKey _ _ | bit _ | bitExpr _ | bytes32 _ | bytes _ _ | compress _
      | compressString _ | nativeFields _ | counter _ | u128 _ =>
        simp [evalOp] at accepted
  | push aligned _ =>
    cases aligned with
    | field _ | bit _ | bitExpr _ => simp [ScalarOperation, ScalarAligned]
    | _ =>
      simp [evalOp, evalAligned] at accepted
      cases accepted
  | popeq aligned =>
    cases aligned with
    | field _ | bit _ | bitExpr _ => simp [ScalarOperation, ScalarAligned]
    | _ =>
      simp [evalOp, evalAligned] at accepted
      cases accepted
  | _ => simp_all [evalOp]

theorem evalOperations_supported (ctx : EvalContext) (env : EvalEnv)
    (operations : List Impact.Op) (native : List Op)
    (accepted : operations.mapM (evalOp ctx env) = .ok native) :
    ∀ operation ∈ operations, ScalarOperation operation := by
  induction operations generalizing native with
  | nil => simp
  | cons operation rest ih =>
    simp only [List.mapM_cons] at accepted
    cases head : evalOp ctx env operation with
    | error message =>
      simp [head] at accepted
      contradiction
    | ok value =>
      cases tail : rest.mapM (evalOp ctx env) with
      | error message =>
        simp [head, tail] at accepted
        contradiction
      | ok values =>
        simp [head, tail] at accepted
        intro item member
        rcases List.mem_cons.mp member with same | present
        · cases same
          exact evalOp_supported ctx env operation value head
        · exact ih values tail item present

example (ctx : EvalContext) (env : EvalEnv) :
    evalOp ctx env .dup = .ok .dup := rfl

example (ctx : EvalContext) (env : EvalEnv) :
    evalOp ctx env .newMap =
      .error "unsupported Impact operation in scalar state interpreter" := rfl

def evalFields (ctx : EvalContext) (env : EvalEnv)
    (fields : List Impact.Scalar) : Except String (List Scalar) :=
  fields.mapM fun expression => scalar <$> expression.eval ctx env

private theorem evalFields_suffix (ctx : EvalContext) (env : EvalEnv)
    (before after : List Impact.Scalar) (values : List Scalar)
    (accepted : evalFields ctx env (before ++ after) = .ok values) :
    ∃ suffixValues, evalFields ctx env after = .ok suffixValues := by
  simp only [evalFields, List.mapM_append] at accepted
  cases head : before.mapM (fun expression => scalar <$> expression.eval ctx env) with
  | error message => simp [head, bind, Except.bind] at accepted
  | ok headValues =>
    cases suffix : after.mapM (fun expression => scalar <$> expression.eval ctx env) with
    | error message => simp [head, suffix, bind, Except.bind] at accepted
    | ok suffixValues => exact ⟨suffixValues, suffix⟩

private theorem evalFields_single (ctx : EvalContext) (env : EvalEnv)
    (expression : Impact.Scalar) (values : List Scalar)
    (accepted : evalFields ctx env [expression] = .ok values) :
    ∃ value, expression.eval ctx env = .ok value := by
  simp only [evalFields, List.mapM_cons, List.mapM_nil] at accepted
  cases evaluated : expression.eval ctx env with
  | error message => simp [evaluated, bind, Except.bind, Except.map, Functor.map] at accepted
  | ok value => exact ⟨value, rfl⟩

theorem evalAligned_of_fields (ctx : EvalContext) (env : EvalEnv)
    (aligned : Impact.Aligned) (values : List Scalar)
    (supported : ScalarAligned aligned)
    (accepted : evalFields ctx env aligned.fields = .ok values) :
    ∃ cell, evalAligned ctx env aligned = .ok cell := by
  cases aligned with
  | bit value => exact ⟨boolean value, rfl⟩
  | bitExpr expression =>
    have suffix : ∃ tail,
        evalFields ctx env [(.select expression (.native 1) (.native 0))] = .ok tail := by
      apply evalFields_suffix ctx env [.native 1, .native 1]
        [(.select expression (.native 1) (.native 0))] values
      simpa [Impact.Aligned.fields] using accepted
    obtain ⟨tail, tailEval⟩ := suffix
    obtain ⟨_, projectedEval⟩ := evalFields_single ctx env
      (.select expression (.native 1) (.native 0)) tail tailEval
    cases evaluated : expression.eval ctx env with
    | error message =>
      simp [Expr.eval, evaluated, bind, Except.bind] at projectedEval
    | ok value => exact ⟨boolean value,
        by simp [evalAligned, evaluated, Except.map, Functor.map]⟩
  | field expression =>
    simp only [ScalarAligned] at supported
    have suffix : ∃ tail, evalFields ctx env [expression] = .ok tail := by
      apply evalFields_suffix ctx env [.native 1, .native (Field.modulus - 2)]
      simpa [Impact.Aligned.fields] using accepted
    obtain ⟨tail, tailEval⟩ := suffix
    obtain ⟨value, evaluated⟩ := evalFields_single ctx env expression tail tailEval
    exact ⟨field (scalar value), by simp [evalAligned, evaluated, Except.map, Functor.map]⟩
  | foreignKey _ _ => simp [ScalarAligned] at supported
  | bytes32 _ => simp [ScalarAligned] at supported
  | bytes _ _ => simp [ScalarAligned] at supported
  | compress _ => simp [ScalarAligned] at supported
  | compressString _ => simp [ScalarAligned] at supported
  | nativeFields _ => simp [ScalarAligned] at supported
  | counter _ => simp [ScalarAligned] at supported
  | u128 _ => simp [ScalarAligned] at supported

theorem evalOp_of_fields (ctx : EvalContext) (env : EvalEnv)
    (operation : Impact.Op) (values : List Scalar)
    (supported : ScalarOperation operation)
    (accepted : evalFields ctx env operation.fields = .ok values) :
    ∃ native, evalOp ctx env operation = .ok native := by
  cases operation with
  | dup => exact ⟨.dup, rfl⟩
  | index slot path => exact ⟨.index slot path, rfl⟩
  | mapIndex slot key =>
    cases key with
    | field expression =>
      have alignedSupported : ScalarAligned (.field expression) := by trivial
      obtain ⟨tail, alignedFields⟩ := evalFields_suffix ctx env
        ([.native 0x51] ++ (Impact.Aligned.field (.native slot)).fields)
        (Impact.Aligned.field expression).fields values
        (by simpa [Impact.Op.fields, List.append_assoc] using accepted)
      obtain ⟨cell, alignedEval⟩ := evalAligned_of_fields ctx env
        (.field expression) tail alignedSupported alignedFields
      exact ⟨.mapIndex slot cell,
        by simp [evalOp, alignedEval, Except.map, Functor.map]⟩
    | foreignKey _ _ | bit _ | bitExpr _ | bytes32 _ | bytes _ _ | compress _
      | compressString _ | nativeFields _ | counter _ | u128 _ =>
        simp [ScalarOperation] at supported
  | member => exact ⟨.member, rfl⟩
  | insert levels => exact ⟨.insert levels, rfl⟩
  | push aligned storage =>
    have alignedSupported : ScalarAligned aligned := by
      simpa [ScalarOperation] using supported
    obtain ⟨tail, alignedFields⟩ := evalFields_suffix ctx env
      [.native (if storage then 0x11 else 0x10), .native 1]
      aligned.fields values (by simpa [Impact.Op.fields] using accepted)
    obtain ⟨cell, alignedEval⟩ := evalAligned_of_fields ctx env aligned tail
      alignedSupported alignedFields
    exact ⟨.push cell storage, by simp [evalOp, alignedEval, Except.map, Functor.map]⟩
  | popeq aligned =>
    have alignedSupported : ScalarAligned aligned := by
      simpa [ScalarOperation] using supported
    obtain ⟨tail, alignedFields⟩ := evalFields_suffix ctx env
      [.native 0x0c] aligned.fields values
      (by simpa [Impact.Op.fields] using accepted)
    obtain ⟨cell, alignedEval⟩ := evalAligned_of_fields ctx env aligned tail
      alignedSupported alignedFields
    exact ⟨.popeq cell, by simp [evalOp, alignedEval, Except.map, Functor.map]⟩
  | _ => simp [ScalarOperation] at supported

theorem evalOperations_of_fields (ctx : EvalContext) (env : EvalEnv)
    (operations : List Impact.Op) (groups : List (List Scalar))
    (supported : ∀ operation ∈ operations, ScalarOperation operation)
    (accepted : operations.mapM (fun operation =>
      evalFields ctx env operation.fields) = .ok groups) :
    ∃ native, operations.mapM (evalOp ctx env) = .ok native := by
  induction operations generalizing groups with
  | nil => exact ⟨[], rfl⟩
  | cons operation rest ih =>
    have headSupported : ScalarOperation operation := supported operation (by simp)
    have tailSupported : ∀ item ∈ rest, ScalarOperation item := by
      intro item present
      exact supported item (by simp [present])
    simp only [List.mapM_cons] at accepted
    cases first : evalFields ctx env operation.fields with
    | error message => simp [first, bind, Except.bind] at accepted
    | ok values =>
      cases later : rest.mapM (fun item => evalFields ctx env item.fields) with
      | error message => simp [first, later, bind, Except.bind] at accepted
      | ok remaining =>
        obtain ⟨head, headEval⟩ := evalOp_of_fields ctx env operation values
          headSupported first
        obtain ⟨tail, tailEval⟩ := ih remaining tailSupported later
        refine ⟨head :: tail, ?_⟩
        simp only [List.mapM_cons, headEval, tailEval]
        rfl

theorem evalOperations_chunks (ctx : EvalContext) (env : EvalEnv)
    (chunks : List (List Impact.Op)) (native : List Op)
    (accepted : chunks.flatten.mapM (evalOp ctx env) = .ok native) :
    ∃ groups, chunks.mapM (fun chunk => chunk.mapM (evalOp ctx env)) = .ok groups ∧
      native = groups.flatten := by
  induction chunks generalizing native with
  | nil =>
    simp at accepted
    cases accepted
    exact ⟨[], rfl, rfl⟩
  | cons chunk rest ih =>
    simp only [List.flatten_cons, List.mapM_append] at accepted
    cases head : chunk.mapM (evalOp ctx env) with
    | error message => simp [head, bind, Except.bind] at accepted
    | ok first =>
      cases tail : rest.flatten.mapM (evalOp ctx env) with
      | error message => simp [head, tail, bind, Except.bind] at accepted
      | ok remaining =>
        simp [head, tail, bind, Except.bind] at accepted
        cases accepted
        obtain ⟨groups, groupEval, groupFlat⟩ := ih remaining tail
        refine ⟨first :: groups, ?_, ?_⟩
        · simp only [List.mapM_cons, head, groupEval]
          rfl
        · simp [groupFlat]

def FieldAdmitted : Impact.Op → Prop
  | .index slot _ => slot < Field.modulus
  | .mapIndex slot _ => slot < Field.modulus
  | .insert levels => 0x90 + levels < Field.modulus
  | _ => True

private theorem literal_eval (ctx : EvalContext) (env : EvalEnv)
    (n : Nat) (modulus : ctx.modulus = Field.modulus)
    (bound : n < Field.modulus) :
    (Expr.native n : Expr .native).eval ctx env = .ok n := by
  simp [Expr.eval, modulus, bound, Except.pure] <;> rfl

private theorem evalFields_literal_cons (ctx : EvalContext) (env : EvalEnv)
    (n : Nat) (rest : List Impact.Scalar)
    (modulus : ctx.modulus = Field.modulus)
    (bound : n < Field.modulus) :
    evalFields ctx env ((.native n) :: rest) =
      (fun values => scalar n :: values) <$> evalFields ctx env rest := by
  simp [evalFields, List.mapM_cons, literal_eval ctx env n modulus bound,
    Except.bind, Except.map, Functor.map, Except.pure] <;> rfl

theorem evalAligned_fields (ctx : EvalContext) (env : EvalEnv)
    (value : Impact.Aligned) (cell : Cell)
    (modulus : ctx.modulus = Field.modulus)
    (accepted : evalAligned ctx env value = .ok cell) :
    evalFields ctx env value.fields = .ok cell.fields := by
  cases value with
  | field expression =>
    cases evaluated : expression.eval ctx env with
    | error message =>
      simp only [evalAligned, evaluated] at accepted
      change (Except.error message : Except String Cell) = .ok cell at accepted
      cases accepted
    | ok number =>
      simp [evalAligned, evaluated] at accepted
      cases accepted
      have oneEval : (Expr.native 1 : Expr .native).eval ctx env = .ok 1 := by
        simp [Expr.eval, modulus, Field.modulus, Except.pure] <;> rfl
      have alignmentEval :
          (Expr.native (Field.modulus - 2) : Expr .native).eval ctx env =
            .ok (Field.modulus - 2) := by
        simp [Expr.eval, modulus, Field.modulus, Except.pure] <;> rfl
      simp [evalFields, Impact.Aligned.fields, Cell.fields,
        field, oneEval, alignmentEval, evaluated, scalar, one,
        Except.bind, Except.map, Functor.map, Except.pure] <;> rfl
  | bit value =>
    simp [evalAligned] at accepted
    cases accepted
    have oneEval : (Expr.native 1 : Expr .native).eval ctx env = .ok 1 := by
      simp [Expr.eval, modulus, Field.modulus, Except.pure] <;> rfl
    have zeroEval : (Expr.native 0 : Expr .native).eval ctx env = .ok 0 := by
      simp [Expr.eval, modulus, Field.modulus, Except.pure] <;> rfl
    cases value <;>
      simp [evalFields, Impact.Aligned.fields, Cell.fields, boolean,
        bit, one, zero, oneEval, zeroEval,
        Except.bind, Except.map, Functor.map, Except.pure] <;> rfl
  | bitExpr expression =>
    cases evaluated : expression.eval ctx env with
    | error message =>
      simp [evalAligned, evaluated] at accepted
      cases accepted
    | ok value =>
      simp [evalAligned, evaluated] at accepted
      cases accepted
      have oneEval : (Expr.native 1 : Expr .native).eval ctx env = .ok 1 := by
        simp [Expr.eval, modulus, Field.modulus, Except.pure] <;> rfl
      have zeroEval : (Expr.native 0 : Expr .native).eval ctx env = .ok 0 := by
        simp [Expr.eval, modulus, Field.modulus, Except.pure] <;> rfl
      cases value <;>
        simp [evalFields, Impact.Aligned.fields, Cell.fields, boolean,
          bit, one, zero, evaluated, Expr.eval, oneEval, zeroEval,
          scalar_one_eq, Except.bind, Except.map, Functor.map,
          Except.pure] <;> rfl
  | foreignKey _ _ | bytes32 _ | bytes _ _ | compress _ | compressString _
    | nativeFields _ | counter _ | u128 _ => simp [evalAligned] at accepted

theorem evalOp_fields (ctx : EvalContext) (env : EvalEnv)
    (operation : Impact.Op) (native : Op)
    (modulus : ctx.modulus = Field.modulus)
    (admitted : FieldAdmitted operation)
    (accepted : evalOp ctx env operation = .ok native) :
    evalFields ctx env operation.fields = .ok native.fields := by
  cases operation with
  | dup =>
    cases accepted
    change evalFields ctx env [.native 0x30] = .ok [scalar 0x30]
    rw [evalFields_literal_cons ctx env 0x30 [] modulus (by decide)]
    rfl
  | member =>
    cases accepted
    change evalFields ctx env [.native 0x18] = .ok [scalar 0x18]
    rw [evalFields_literal_cons ctx env 0x18 [] modulus (by decide)]
    rfl
  | insert levels =>
    cases accepted
    change evalFields ctx env [.native (0x90 + levels)] =
      .ok [scalar (0x90 + levels)]
    rw [evalFields_literal_cons ctx env (0x90 + levels) [] modulus admitted]
    rfl
  | index slot path =>
    cases accepted
    have opcodeBound : (if path then 0x70 else 0x50) < Field.modulus := by
      cases path <;> decide
    have alignedAccepted : evalAligned ctx env
        (.field (.native slot)) = .ok (field (scalar slot)) := by
      simp [evalAligned, literal_eval ctx env slot modulus admitted,
        Except.bind, Except.pure] <;> rfl
    have alignedFields := evalAligned_fields ctx env
      (.field (.native slot)) (field (scalar slot)) modulus alignedAccepted
    change evalFields ctx env
      (.native (if path then 0x70 else 0x50) ::
        (Impact.Aligned.field (.native slot)).fields) =
      .ok (scalar (if path then 0x70 else 0x50) :: (field (scalar slot)).fields)
    rw [evalFields_literal_cons ctx env _ _ modulus opcodeBound, alignedFields]
    rfl
  | mapIndex slot key =>
    cases key with
    | field expression =>
      cases aligned : evalAligned ctx env (.field expression) with
      | error message =>
        simp only [evalOp, aligned] at accepted
        change (Except.error message : Except String Op) = .ok native at accepted
        cases accepted
      | ok cell =>
        simp [evalOp, aligned] at accepted
        cases accepted
        have opcodeBound : 0x51 < Field.modulus := by decide
        have alignedSlot : evalAligned ctx env
            (.field (.native slot)) = .ok (field (scalar slot)) := by
          simp [evalAligned, literal_eval ctx env slot modulus admitted,
            Except.bind, Except.pure] <;> rfl
        have slotFields := evalAligned_fields ctx env
          (.field (.native slot)) (field (scalar slot)) modulus alignedSlot
        have keyFields := evalAligned_fields ctx env
          (.field expression) cell modulus aligned
        change evalFields ctx env
          (.native 0x51 :: ((Impact.Aligned.field (.native slot)).fields ++
            (Impact.Aligned.field expression).fields)) =
          .ok (scalar 0x51 :: ((field (scalar slot)).fields ++ cell.fields))
        rw [evalFields_literal_cons ctx env 0x51 _ modulus opcodeBound]
        have tailFields : evalFields ctx env
            ((Impact.Aligned.field (.native slot)).fields ++
              (Impact.Aligned.field expression).fields) =
            .ok ((field (scalar slot)).fields ++ cell.fields) := by
          have slotFields' :
              (Impact.Aligned.field (.native slot)).fields.mapM
                (fun item => scalar <$> item.eval ctx env) =
              .ok (field (scalar slot)).fields := by
            simpa [evalFields] using slotFields
          have keyFields' :
              (Impact.Aligned.field expression).fields.mapM
                (fun item => scalar <$> item.eval ctx env) = .ok cell.fields := by
            simpa [evalFields] using keyFields
          change ((Impact.Aligned.field (.native slot)).fields ++
            (Impact.Aligned.field expression).fields).mapM
            (fun item => scalar <$> item.eval ctx env) = _
          rw [List.mapM_append, slotFields', keyFields']
          rfl
        rw [tailFields]
        rfl
    | foreignKey _ _ | bit _ | bitExpr _ | bytes32 _ | bytes _ _ | compress _
      | compressString _ | nativeFields _ | counter _ | u128 _ =>
        simp [evalOp] at accepted
  | push value storage =>
    cases aligned : evalAligned ctx env value with
    | error message =>
      simp only [evalOp, aligned] at accepted
      change (Except.error message : Except String Op) = .ok native at accepted
      cases accepted
    | ok cell =>
      simp [evalOp, aligned] at accepted
      cases accepted
      have opcodeBound : (if storage then 0x11 else 0x10) < Field.modulus := by
        cases storage <;> decide
      have alignedFields := evalAligned_fields ctx env value cell modulus aligned
      change evalFields ctx env
        (.native (if storage then 0x11 else 0x10) :: .native 1 :: value.fields) =
        .ok (scalar (if storage then 0x11 else 0x10) :: one :: cell.fields)
      rw [evalFields_literal_cons ctx env _ _ modulus opcodeBound,
        evalFields_literal_cons ctx env 1 _ modulus (by decide), alignedFields]
      rfl
  | popeq value =>
    cases aligned : evalAligned ctx env value with
    | error message =>
      simp only [evalOp, aligned] at accepted
      change (Except.error message : Except String Op) = .ok native at accepted
      cases accepted
    | ok cell =>
      simp [evalOp, aligned] at accepted
      cases accepted
      have alignedFields := evalAligned_fields ctx env value cell modulus aligned
      change evalFields ctx env (.native 0x0c :: value.fields) =
        .ok (scalar 0x0c :: cell.fields)
      rw [evalFields_literal_cons ctx env 0x0c _ modulus (by decide), alignedFields]
      rfl
  | _ => simp [evalOp] at accepted

/-- The interpreted Impact operation fields equal the native VM field groups
for every accepted operation, with no rearrangement or flattened boundaries. -/
theorem evalOperations_fields (ctx : EvalContext) (env : EvalEnv)
    (operations : List Impact.Op) (native : List Op)
    (modulus : ctx.modulus = Field.modulus)
    (admitted : ∀ operation ∈ operations, FieldAdmitted operation)
    (accepted : operations.mapM (evalOp ctx env) = .ok native) :
    operations.mapM (fun operation => evalFields ctx env operation.fields) =
      .ok (native.map Op.fields) := by
  induction operations generalizing native with
  | nil =>
    simp only [List.mapM_nil] at accepted
    cases accepted
    rfl
  | cons operation rest ih =>
    have headAdmitted := admitted operation (by simp)
    have tailAdmitted : ∀ item ∈ rest, FieldAdmitted item := by
      intro item member
      exact admitted item (by simp [member])
    cases head : evalOp ctx env operation with
    | error message =>
      simp only [List.mapM_cons, head] at accepted
      change (Except.error message : Except String (List Op)) = .ok native at accepted
      cases accepted
    | ok next =>
      cases tail : rest.mapM (evalOp ctx env) with
      | error message =>
        simp only [List.mapM_cons, head, tail] at accepted
        change (Except.error message : Except String (List Op)) = .ok native at accepted
        cases accepted
      | ok remaining =>
        simp [List.mapM_cons, head, tail] at accepted
        cases accepted
        have one := evalOp_fields ctx env operation next modulus headAdmitted head
        have others := ih remaining tailAdmitted tail
        simp [List.mapM_cons, one, others, Except.pure] <;> rfl

/-- The native schedule preserves exact operation boundaries and order. -/
theorem evalPlan_operations (ctx : EvalContext) (env : EvalEnv)
    (operations : List Impact.Op) :
    evalPlan ctx env {operations := operations} =
      operations.mapM (evalOp ctx env) := rfl

end Noctium.Verification.GenericStateOps
