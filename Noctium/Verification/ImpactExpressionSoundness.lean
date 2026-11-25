import Noctium.NativeExpression
import Noctium.Verification.ImpactExpressionMatch
import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.ImpactExpressionSoundness

open Lean ImpactExpressionMatch ScalarNormalization
open scoped Noctium

private def singleBinding (name : String) (value body : Json) : Json :=
  Json.mkObj [("tag", toJson ("let" : String)), ("name", toJson name),
    ("value", value), ("body", body)]

private def bindingSequence (bindings : List (String × Json)) (body : Json) : Json :=
  Json.mkObj [("tag", toJson ("lets" : String)),
    ("bindings", ImpactExpressionNode.bindingsJson bindings),
    ("body", body)]

private theorem prepend_single (name innerName : String) (value innerValue body : Json) :
    NativeExpression.letJson name value (singleBinding innerName innerValue body) =
      bindingSequence [(name, value), (innerName, innerValue)] body := by
  unfold singleBinding bindingSequence ImpactExpressionNode.bindingsJson
  rw [NativeExpression.letJson_single, List.map_toArray]
  rfl

private theorem prepend_sequence (name : String) (value body : Json)
    (bindings : List (String × Json)) :
    NativeExpression.letJson name value (bindingSequence bindings body) =
      bindingSequence ((name, value) :: bindings) body := by
  unfold bindingSequence ImpactExpressionNode.bindingsJson
  rw [NativeExpression.letJson_multiple]
  simp only [List.map_toArray, List.map_cons]
  rw [List.toArray_cons (ImpactExpressionNode.bindingJson (name, value))
    (bindings.map ImpactExpressionNode.bindingJson)]
  rfl

/-- Carry the serializer's leading binding shape so prepending one binding
preserves the order of the sequence, including repeated names. -/
private inductive Encoded : Expr ty → Json → Prop where
  | plain {expression : Expr ty} {raw : Json} {tag : String}
      (matchedExpr : Matches expression raw)
      (tagRead : (raw.getObjVal? "tag" >>= Json.getStr?) = .ok tag)
      (notLet : tag ≠ "let") (notLets : tag ≠ "lets") :
      Encoded expression raw
  | single {expression : Expr ty} {name : String} {value body : Json}
      (bindings : Bindings expression [(name, value)] body) :
      Encoded expression (singleBinding name value body)
  | sequence {expression : Expr ty} {bindings : List (String × Json)} {body : Json}
      (nonempty : bindings ≠ []) (matchedExpr : Bindings expression bindings body) :
      Encoded expression (bindingSequence bindings body)

private theorem Encoded.matched {expression : Expr ty} {raw : Json}
    (encoded : Encoded expression raw) : Matches expression raw := by
  cases encoded with
  | plain matchedExpr _ _ _ => exact matchedExpr
  | single bindings => exact .letE (ImpactExpressionNode.decode_let _ _ _) (by simp) bindings
  | sequence nonempty bindings => exact .letE (ImpactExpressionNode.decode_lets _ _) nonempty bindings

private theorem Encoded.prepend {value : Expr source} {body : Expr target}
    {valueJson bodyJson : Json} (name : String)
    (decodedValue : Matches value valueJson) (encodedBody : Encoded body bodyJson) :
    Encoded (.letE name value body) (NativeExpression.letJson name valueJson bodyJson) := by
  cases encodedBody with
  | plain matchedExpr tagRead notLet notLets =>
    rw [NativeExpression.letJson_plain name valueJson _ _ tagRead notLet notLets]
    exact .single (.cons decodedValue (.terminal matchedExpr))
  | single inner =>
    rw [prepend_single]
    exact .sequence (by simp) (.cons decodedValue inner)
  | sequence _ inner =>
    rw [prepend_sequence]
    exact .sequence (by simp) (.cons decodedValue inner)

private theorem Encoded.copy {expression : Expr ty} {raw : Json}
    (encoded : Encoded expression raw) : Encoded (.copyValue expression) raw := by
  cases encoded with
  | plain matchedExpr tagRead notLet notLets => exact .plain (.copyValue matchedExpr) tagRead notLet notLets
  | single bindings => exact .single (.copyValue bindings)
  | sequence nonempty bindings => exact .sequence nonempty (.copyValue bindings)

private theorem Encoded.disclosed {expression : Expr ty} {raw : Json}
    (span : SourceSpan) (encoded : Encoded expression raw) :
    Encoded (.disclose span expression) raw := by
  cases encoded with
  | plain matchedExpr tagRead notLet notLets => exact .plain (.disclose matchedExpr) tagRead notLet notLets
  | single bindings => exact .single (.disclose bindings)
  | sequence nonempty bindings => exact .sequence nonempty (.disclose bindings)

private theorem encoded_toJson {expression : Expr ty} (supported : ScalarExpression expression) :
    Encoded expression (NativeExpression.toJson expression) := by
  induction supported with
  | native value =>
    rw [NativeExpression.toJson_native]
    apply Encoded.plain (tag := "constant") (.native rfl) rfl <;> decide
  | bool value =>
    rw [NativeExpression.toJson_bool]
    apply Encoded.plain (tag := "bool") (.bool rfl) rfl <;> decide
  | uint maximum value =>
    rw [NativeExpression.toJson_uint]
    apply Encoded.plain (tag := "uint") (.uint rfl) rfl <;> decide
  | ref name scalarType =>
    rw [NativeExpression.toJson_ref]
    apply Encoded.plain (tag := "reference") (.ref rfl scalarType) rfl <;> decide
  | add left right _ _ ihLeft ihRight =>
    rw [NativeExpression.toJson_add]
    apply Encoded.plain (tag := "add") (.add rfl ihLeft.matched ihRight.matched) rfl <;> decide
  | mul left right _ _ ihLeft ihRight =>
    rw [NativeExpression.toJson_mul]
    apply Encoded.plain (tag := "mul") (.mul rfl ihLeft.matched ihRight.matched) rfl <;> decide
  | sub left right _ _ ihLeft ihRight =>
    rw [NativeExpression.toJson_sub]
    apply Encoded.plain (tag := "sub") (.sub rfl ihLeft.matched ihRight.matched) rfl <;> decide
  | uadd left right _ _ ihLeft ihRight =>
    rw [NativeExpression.toJson_uadd]
    apply Encoded.plain (tag := "uadd") (.uadd rfl ihLeft.matched ihRight.matched) rfl <;> decide
  | usub left right _ _ ihLeft ihRight =>
    rw [NativeExpression.toJson_usub]
    apply Encoded.plain (tag := "usub") (.usub rfl ihLeft.matched ihRight.matched) rfl <;> decide
  | umul left right _ _ ihLeft ihRight =>
    rw [NativeExpression.toJson_umul]
    apply Encoded.plain (tag := "umul") (.umul rfl ihLeft.matched ihRight.matched) rfl <;> decide
  | cast value _ targetType _ ihValue =>
    rw [NativeExpression.toJson_cast]
    apply Encoded.plain (tag := "cast") (.cast rfl targetType ihValue.matched) rfl <;>
      decide
  | letE name value body _ _ _ ihValue ihBody =>
    rw [NativeExpression.toJson_letE]
    exact Encoded.prepend name ihValue.matched ihBody
  | assertE condition body _ _ ihCondition ihBody =>
    rw [NativeExpression.toJson_assertE]
    apply Encoded.plain (tag := "assertThen") (.assertE rfl ihCondition.matched ihBody.matched) rfl <;>
      decide
  | copyValue value _ ihValue =>
    rw [NativeExpression.toJson_copyValue]
    exact ihValue.copy
  | disclose span value _ ihValue =>
    rw [NativeExpression.toJson_disclose]
    exact ihValue.disclosed span
  | eq left right scalarType _ _ ihLeft ihRight =>
    rw [NativeExpression.toJson_eq]
    apply Encoded.plain (tag := "eq")
      (.eq rfl scalarType ihLeft.matched ihRight.matched) rfl <;> decide
  | select condition yes no scalarType _ _ _ ihCondition ihYes ihNo =>
    rw [NativeExpression.toJson_select]
    apply Encoded.plain (tag := "select")
      (.select rfl scalarType ihCondition.matched ihYes.matched ihNo.matched) rfl <;> decide
  | poseidon2 domain left right _ _ ihLeft ihRight =>
    rw [NativeExpression.toJson_poseidon2]
    apply Encoded.plain (tag := "poseidon2") (.poseidon2 rfl ihLeft.matched ihRight.matched) rfl <;>
      decide

/-- Every node of the production scalar expression JSON corresponds to the
typed source expression, including the ordered bindings in a flattened let. -/
theorem matches_toJson {expression : Expr ty} (supported : ScalarExpression expression) :
    Matches expression (NativeExpression.toJson expression) :=
  (encoded_toJson supported).matched

theorem toJson_nonNull {expression : Expr ty} (supported : ScalarExpression expression) :
    (NativeExpression.toJson expression).isNull = Bool.false := by
  generalize equal : NativeExpression.toJson expression = raw
  have encoded := equal ▸ encoded_toJson supported
  cases encoded with
  | plain _ tagRead _ _ => cases raw <;> first | rfl | contradiction
  | single _ => rfl
  | sequence _ _ => rfl

end Noctium.Verification.ImpactExpressionSoundness
