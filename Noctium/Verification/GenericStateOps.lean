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

private theorem evalFields_single_exact (ctx : EvalContext) (env : EvalEnv)
    (expression : Impact.Scalar) :
    evalFields ctx env [expression] = (fun value => [scalar value]) <$> expression.eval ctx env := by
  cases evaluated : expression.eval ctx env with
  | error message =>
    simp [evalFields, List.mapM_cons, List.mapM_nil, evaluated, bind,
      Except.bind, Except.map, Functor.map] <;> rfl
  | ok value =>
    simp [evalFields, List.mapM_cons, List.mapM_nil, evaluated, bind,
      Except.bind, Except.map, Functor.map] <;> rfl

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

/-- Field encoding preserves both successful aligned values and expression
errors. This exact form is used when operation evaluation is compared with
its scalar field encoding. -/
theorem evalAligned_fields_exact (ctx : EvalContext) (env : EvalEnv)
    (value : Impact.Aligned) (supported : ScalarAligned value)
    (modulus : ctx.modulus = Field.modulus) :
    evalFields ctx env value.fields = (evalAligned ctx env value).map Cell.fields := by
  cases value with
  | field expression =>
    have oneBound : 1 < Field.modulus := by decide
    have alignmentBound : Field.modulus - 2 < Field.modulus := by decide
    change evalFields ctx env
      [.native 1, .native (Field.modulus - 2), expression] =
        (evalAligned ctx env (.field expression)).map Cell.fields
    rw [evalFields_literal_cons ctx env 1 _ modulus oneBound]
    rw [evalFields_literal_cons ctx env (Field.modulus - 2) _ modulus alignmentBound]
    rw [evalFields_single_exact]
    cases evaluated : expression.eval ctx env with
    | error message =>
      simp [evalAligned, evaluated, Cell.fields, field, scalar_one_eq,
        bind, Except.bind, Except.map, Functor.map] <;> rfl
    | ok number =>
      simp [evalAligned, evaluated, Cell.fields, field, scalar_one_eq,
        bind, Except.bind, Except.map, Functor.map] <;> rfl
  | bit value =>
    have oneBound : 1 < Field.modulus := by decide
    change evalFields ctx env
      [.native 1, .native 1, .native (if value then 1 else 0)] =
        (evalAligned ctx env (.bit value)).map Cell.fields
    rw [evalFields_literal_cons ctx env 1 _ modulus oneBound]
    rw [evalFields_literal_cons ctx env 1 _ modulus oneBound]
    cases value with
    | false =>
      have valueBound : (if false then 1 else 0) < Field.modulus := by decide
      rw [evalFields_literal_cons ctx env (if false then 1 else 0) _ modulus valueBound]
      simp [evalFields, evalAligned, Cell.fields, boolean, bit, scalar_one_eq,
        one, zero, bind, Except.bind, Except.map, Except.pure, Functor.map] <;> rfl
    | true =>
      have valueBound : (if true then 1 else 0) < Field.modulus := by decide
      rw [evalFields_literal_cons ctx env (if true then 1 else 0) _ modulus valueBound]
      simp [evalFields, evalAligned, Cell.fields, boolean, bit, scalar_one_eq,
        one, zero, bind, Except.bind, Except.map, Except.pure, Functor.map] <;> rfl
  | bitExpr expression =>
    have oneBound : 1 < Field.modulus := by decide
    have oneEval : (Expr.native 1 : Expr .native).eval ctx env = .ok 1 := by
      simp [Expr.eval, modulus, Field.modulus] <;> rfl
    have zeroEval : (Expr.native 0 : Expr .native).eval ctx env = .ok 0 := by
      simp [Expr.eval, modulus, Field.modulus] <;> rfl
    change evalFields ctx env
      [.native 1, .native 1, .select expression (.native 1) (.native 0)] =
        (evalAligned ctx env (.bitExpr expression)).map Cell.fields
    rw [evalFields_literal_cons ctx env 1 _ modulus oneBound]
    rw [evalFields_literal_cons ctx env 1 _ modulus oneBound]
    rw [evalFields_single_exact]
    cases evaluated : expression.eval ctx env with
    | error message =>
      simp [evalAligned, Expr.eval, evaluated, Cell.fields, boolean, bit,
        scalar_one_eq, one, zero, Except.bind, Except.map, Except.pure,
        oneEval, zeroEval, modulus, Field.modulus, Functor.map] <;> rfl
    | ok bitValue =>
      cases bitValue <;>
        simp [evalAligned, Expr.eval, evaluated, Cell.fields, boolean, bit,
          scalar_one_eq, one, zero, Except.bind, Except.map, Except.pure,
          oneEval, zeroEval, modulus, Field.modulus, Functor.map] <;> rfl
  | foreignKey _ _ | bytes32 _ | bytes _ _ | compress _ | compressString _
    | nativeFields _ | counter _ | u128 _ => simp [ScalarAligned] at supported

theorem evalAligned_fields (ctx : EvalContext) (env : EvalEnv)
    (value : Impact.Aligned) (cell : Cell)
    (modulus : ctx.modulus = Field.modulus)
    (accepted : evalAligned ctx env value = .ok cell) :
    evalFields ctx env value.fields = .ok cell.fields := by
  cases value with
  | field expression =>
    have exact := evalAligned_fields_exact ctx env (.field expression) (by trivial) modulus
    rw [accepted] at exact
    simpa [Except.map] using exact
  | bit value =>
    have exact := evalAligned_fields_exact ctx env (.bit value) (by trivial) modulus
    rw [accepted] at exact
    simpa [Except.map] using exact
  | bitExpr expression =>
    have exact := evalAligned_fields_exact ctx env (.bitExpr expression) (by trivial) modulus
    rw [accepted] at exact
    simpa [Except.map] using exact
  | foreignKey _ _ | bytes32 _ | bytes _ _ | compress _ | compressString _
    | nativeFields _ | counter _ | u128 _ => simp [evalAligned] at accepted

private theorem evalFields_append_exact (ctx : EvalContext) (env : EvalEnv)
    (before after : List Impact.Scalar) :
    evalFields ctx env (before ++ after) =
      (evalFields ctx env before).bind fun beforeValues =>
        (evalFields ctx env after).map fun suffix => beforeValues ++ suffix := by
  simp [evalFields, List.mapM_append, bind, Except.bind, Except.map,
    Functor.map] <;> rfl

/-- The operation field encoder has the same success values and exact failure
messages as the scalar operation interpreter on its supported, field-admitted
fragment. -/
theorem evalOp_fields_exact (ctx : EvalContext) (env : EvalEnv)
    (operation : Impact.Op) (supported : ScalarOperation operation)
    (modulus : ctx.modulus = Field.modulus)
    (admitted : FieldAdmitted operation) :
    evalFields ctx env operation.fields =
      (evalOp ctx env operation).map NativeState.Op.fields := by
  cases operation with
  | dup =>
    change evalFields ctx env [.native 0x30] =
      (evalOp ctx env .dup).map NativeState.Op.fields
    rw [evalFields_literal_cons ctx env 0x30 [] modulus (by decide)]
    rfl
  | member =>
    change evalFields ctx env [.native 0x18] =
      (evalOp ctx env .member).map NativeState.Op.fields
    rw [evalFields_literal_cons ctx env 0x18 [] modulus (by decide)]
    rfl
  | insert levels =>
    change evalFields ctx env [.native (0x90 + levels)] =
      (evalOp ctx env (.insert levels)).map NativeState.Op.fields
    rw [evalFields_literal_cons ctx env (0x90 + levels) [] modulus admitted]
    rfl
  | index slot path =>
    have slotBound : slot < Field.modulus := admitted
    have opcodeBound : (if path then 0x70 else 0x50) < Field.modulus := by
      cases path <;> decide
    have slotEval : evalAligned ctx env (.field (.native slot)) =
        .ok (field (scalar slot)) := by
      simp [evalAligned, literal_eval ctx env slot modulus slotBound,
        bind, Except.bind, Except.pure] <;> rfl
    have slotFields := evalAligned_fields_exact ctx env
      (.field (.native slot)) (by trivial) modulus
    change evalFields ctx env
      (.native (if path then 0x70 else 0x50) ::
        (Impact.Aligned.field (.native slot)).fields) =
      (evalOp ctx env (.index slot path)).map NativeState.Op.fields
    rw [evalFields_literal_cons ctx env _ _ modulus opcodeBound, slotFields]
    simp [evalOp, slotEval, NativeState.Op.fields, scalar_one_eq,
      Except.map, Functor.map] <;> rfl
  | mapIndex slot key =>
    cases key with
    | field expression =>
      have slotBound : slot < Field.modulus := admitted
      have opcodeBound : 0x51 < Field.modulus := by decide
      have slotPrefix : evalFields ctx env
          ([.native 0x51] ++ (Impact.Aligned.field (.native slot)).fields) =
          .ok (scalar 0x51 :: (field (scalar slot)).fields) := by
        change evalFields ctx env
          [.native 0x51, .native 1, .native (Field.modulus - 2), .native slot] = _
        rw [evalFields_literal_cons ctx env 0x51 _ modulus opcodeBound]
        rw [evalFields_literal_cons ctx env 1 _ modulus (by decide)]
        rw [evalFields_literal_cons ctx env (Field.modulus - 2) _ modulus (by decide)]
        rw [evalFields_literal_cons ctx env slot _ modulus slotBound]
        rfl
      have keyFields := evalAligned_fields_exact ctx env
        (.field expression) (by trivial) modulus
      change evalFields ctx env
          (([.native 0x51] ++ (Impact.Aligned.field (.native slot)).fields) ++
            (Impact.Aligned.field expression).fields) =
        (evalOp ctx env (.mapIndex slot (.field expression))).map
          NativeState.Op.fields
      rw [evalFields_append_exact, slotPrefix, keyFields]
      cases aligned : evalAligned ctx env (.field expression) with
      | error message =>
        simp [evalOp, aligned, NativeState.Op.fields, scalar_one_eq,
          Except.map, Functor.map] <;> rfl
      | ok cell =>
        simp [evalOp, aligned, NativeState.Op.fields, scalar_one_eq,
          Except.map, Functor.map] <;> rfl
    | foreignKey _ _ | bit _ | bitExpr _ | bytes32 _ | bytes _ _ | compress _
      | compressString _ | nativeFields _ | counter _ | u128 _ =>
        simp [ScalarOperation] at supported
  | push value storage =>
    have alignedSupported : ScalarAligned value := by
      simpa [ScalarOperation] using supported
    have opcodeBound : (if storage then 0x11 else 0x10) < Field.modulus := by
      cases storage <;> decide
    have alignedFields := evalAligned_fields_exact ctx env value
      alignedSupported modulus
    change evalFields ctx env
      (.native (if storage then 0x11 else 0x10) :: .native 1 :: value.fields) =
        (evalOp ctx env (.push value storage)).map NativeState.Op.fields
    rw [evalFields_literal_cons ctx env _ _ modulus opcodeBound]
    rw [evalFields_literal_cons ctx env 1 _ modulus (by decide)]
    cases aligned : evalAligned ctx env value with
    | error message =>
      rw [alignedFields]
      simp [evalOp, aligned, NativeState.Op.fields, scalar_one_eq,
        Except.map, Functor.map]
    | ok cell =>
      rw [alignedFields]
      simp [evalOp, aligned, NativeState.Op.fields, scalar_one_eq,
        Except.map, Functor.map]
  | popeq value =>
    have alignedSupported : ScalarAligned value := by
      simpa [ScalarOperation] using supported
    have alignedFields := evalAligned_fields_exact ctx env value
      alignedSupported modulus
    change evalFields ctx env (.native 0x0c :: value.fields) =
      (evalOp ctx env (.popeq value)).map NativeState.Op.fields
    rw [evalFields_literal_cons ctx env 0x0c _ modulus (by decide)]
    cases aligned : evalAligned ctx env value with
    | error message =>
      rw [alignedFields]
      simp [evalOp, aligned, NativeState.Op.fields, Except.map, Functor.map]
    | ok cell =>
      rw [alignedFields]
      simp [evalOp, aligned, NativeState.Op.fields, Except.map, Functor.map]
  | _ => simp [ScalarOperation] at supported

/-- Successful operation interpretation is a direct corollary of the exact
correspondence. -/
theorem evalOp_fields (ctx : EvalContext) (env : EvalEnv)
    (operation : Impact.Op) (native : Op)
    (modulus : ctx.modulus = Field.modulus)
    (admitted : FieldAdmitted operation)
    (accepted : evalOp ctx env operation = .ok native) :
    evalFields ctx env operation.fields = .ok native.fields := by
  have supported := evalOp_supported ctx env operation native accepted
  have exact := evalOp_fields_exact ctx env operation supported modulus admitted
  rw [accepted] at exact
  simpa [Except.map] using exact

/-- The exact field-operation correspondence composes over ordered operation
lists, preserving group boundaries and the first evaluation error. -/
theorem evalOperations_fields_exact (ctx : EvalContext) (env : EvalEnv)
    (operations : List Impact.Op)
    (supported : ∀ operation ∈ operations, ScalarOperation operation)
    (modulus : ctx.modulus = Field.modulus)
    (admitted : ∀ operation ∈ operations, FieldAdmitted operation) :
    operations.mapM (fun operation => evalFields ctx env operation.fields) =
      (operations.mapM (evalOp ctx env)).map (List.map NativeState.Op.fields) := by
  induction operations with
  | nil => rfl
  | cons operation rest ih =>
    have headSupported := supported operation (by simp)
    have tailSupported : ∀ item ∈ rest, ScalarOperation item := by
      intro item member
      exact supported item (by simp [member])
    have headAdmitted := admitted operation (by simp)
    have tailAdmitted : ∀ item ∈ rest, FieldAdmitted item := by
      intro item member
      exact admitted item (by simp [member])
    have head := evalOp_fields_exact ctx env operation headSupported modulus headAdmitted
    have tail := ih tailSupported tailAdmitted
    cases headEval : evalOp ctx env operation <;>
      cases tailEval : rest.mapM (evalOp ctx env) <;>
        simp [List.mapM_cons, head, tail, headEval, tailEval, bind,
          Except.bind, Except.map, Functor.map] <;> rfl

/-- The interpreted Impact operation fields equal the native VM field groups
for every accepted operation, with no rearrangement or flattened boundaries. -/
theorem evalOperations_fields (ctx : EvalContext) (env : EvalEnv)
    (operations : List Impact.Op) (native : List Op)
    (modulus : ctx.modulus = Field.modulus)
    (admitted : ∀ operation ∈ operations, FieldAdmitted operation)
    (accepted : operations.mapM (evalOp ctx env) = .ok native) :
    operations.mapM (fun operation => evalFields ctx env operation.fields) =
      .ok (native.map Op.fields) := by
  have supported := evalOperations_supported ctx env operations native accepted
  have exact := evalOperations_fields_exact ctx env operations supported modulus admitted
  rw [accepted] at exact
  simpa [Except.map] using exact

/-- The native schedule preserves exact operation boundaries and order. -/
theorem evalPlan_operations (ctx : EvalContext) (env : EvalEnv)
    (operations : List Impact.Op) :
    evalPlan ctx env {operations := operations} =
      operations.mapM (evalOp ctx env) := rfl

/-- Successful interpretation of an actual Impact plan establishes the exact
scalar operation support needed to interpret its native schedule. -/
theorem evalPlan_supported (ctx : EvalContext) (env : EvalEnv)
    (plan : Impact.Plan) (ops : List Op)
    (evaluated : evalPlan ctx env plan = .ok ops) :
    ∀ operation ∈ plan.operations, ScalarOperation operation := by
  apply evalOperations_supported ctx env plan.operations ops
  simpa only [evalPlan] using evaluated

private theorem publicInputScalarOperation_supported (input : Input)
    (operation : Impact.Op)
    (member : operation ∈ Impact.publicInputScalarOperations input) :
    ScalarOperation operation := by
  cases input with
  | mk name ty visibility span =>
    cases visibility <;> cases ty <;>
      simp [Impact.publicInputScalarOperations] at member <;>
      rcases member with push | popeq <;> subst operation <;>
        simp [ScalarOperation, ScalarAligned]

private theorem publicInputScalarOperations_supported (inputs : List Input)
    (operation : Impact.Op)
    (member : operation ∈ inputs.flatMap Impact.publicInputScalarOperations) :
    ScalarOperation operation := by
  induction inputs with
  | nil => simp at member
  | cons input rest ih =>
    simp only [List.flatMap_cons, List.mem_append] at member
    rcases member with first | remaining
    · exact publicInputScalarOperation_supported input operation first
    · exact ih remaining

/-- A successful scalar-qualified source prefix preserves the scalar VM
operation boundary and leaves the prior plan's support obligations intact. -/
theorem publicInputPlan_scalar_supported (inputs : List Input)
    (initial plan : Impact.Plan)
    (accepted : Impact.publicInputPlan inputs initial = .ok plan)
    (compatible : ∀ input ∈ inputs, Impact.publicInputScalarCompatible input)
    (initialSupported : ∀ operation ∈ initial.operations, ScalarOperation operation) :
    ∀ operation ∈ plan.operations, ScalarOperation operation := by
  have ordered := Impact.publicInputPlan_scalar_operations inputs initial plan
    accepted compatible
  intro operation member
  rw [ordered] at member
  simp only [List.mem_append] at member
  rcases member with prior | publicMember
  · exact initialSupported operation prior
  · exact publicInputScalarOperations_supported inputs operation publicMember

end Noctium.Verification.GenericStateOps
