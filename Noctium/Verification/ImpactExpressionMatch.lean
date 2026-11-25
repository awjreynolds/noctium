import Noctium.NativeExpression
import Noctium.Verification.ImpactExpressionNode
import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.ImpactExpressionMatch

open Lean
open Noctium.Verification.ImpactExpressionNode
open Noctium.Verification.ScalarNormalization

mutual
/-- Relate an admitted scalar source expression to JSON which the independent
Impact expression decoder accepts. The decoded node keeps child JSON intact,
so each recursive premise is checked against the exact serialized child. -/
inductive Matches : {ty : Ty} → Expr ty → Json → Prop where
  | native {value : Nat} {raw : Json}
      (decoded : ImpactExpressionNode.decode raw = .ok (.native (toString value))) :
      Matches (.native value) raw
  | bool {value : Bool} {raw : Json}
      (decoded : ImpactExpressionNode.decode raw = .ok (.bool value)) :
      Matches (.bool value) raw
  | uint {maximum value : Nat} {raw : Json}
      (decoded : ImpactExpressionNode.decode raw =
        .ok (.uint (toString maximum) (toString value))) :
      Matches (.uint maximum value) raw
  | ref {ty : Ty} {name : String} {raw : Json}
      (decoded : ImpactExpressionNode.decode raw = .ok (.reference name))
      (scalarType : ScalarType ty) :
      Matches (.ref (ty := ty) name) raw
  | add {left right : Expr .native} {raw leftJson rightJson : Json}
      (decoded : ImpactExpressionNode.decode raw =
        .ok (.binary .add leftJson rightJson))
      (leftMatches : Matches left leftJson) (rightMatches : Matches right rightJson) :
      Matches (.add left right) raw
  | mul {left right : Expr .native} {raw leftJson rightJson : Json}
      (decoded : ImpactExpressionNode.decode raw =
        .ok (.binary .mul leftJson rightJson))
      (leftMatches : Matches left leftJson) (rightMatches : Matches right rightJson) :
      Matches (.mul left right) raw
  | sub {left right : Expr .native} {raw leftJson rightJson : Json}
      (decoded : ImpactExpressionNode.decode raw =
        .ok (.binary .sub leftJson rightJson))
      (leftMatches : Matches left leftJson) (rightMatches : Matches right rightJson) :
      Matches (.sub left right) raw
  | uadd {m n : Nat} {left : Expr (.uint m)} {right : Expr (.uint n)}
      {raw leftJson rightJson : Json}
      (decoded : ImpactExpressionNode.decode raw =
        .ok (.unsigned .add (toString (m + n)) leftJson rightJson))
      (leftMatches : Matches left leftJson) (rightMatches : Matches right rightJson) :
      Matches (.uadd left right) raw
  | usub {m n : Nat} {left : Expr (.uint m)} {right : Expr (.uint n)}
      {raw leftJson rightJson : Json}
      (decoded : ImpactExpressionNode.decode raw =
        .ok (.unsigned .sub (toString m) leftJson rightJson))
      (leftMatches : Matches left leftJson) (rightMatches : Matches right rightJson) :
      Matches (.usub left right) raw
  | umul {m n : Nat} {left : Expr (.uint m)} {right : Expr (.uint n)}
      {raw leftJson rightJson : Json}
      (decoded : ImpactExpressionNode.decode raw =
        .ok (.unsigned .mul (toString (m * n)) leftJson rightJson))
      (leftMatches : Matches left leftJson) (rightMatches : Matches right rightJson) :
      Matches (.umul left right) raw
  | cast {source target : Ty} {value : Expr source} {raw valueJson : Json}
      (decoded : ImpactExpressionNode.decode raw =
        .ok (.cast (NativeExpression.typeName target) valueJson))
      (targetType : ScalarType target) (valueMatches : Matches value valueJson) :
      Matches (.cast target value) raw
  | letE {ty : Ty} {expression : Expr ty} {raw : Json}
      {bindings : List (String × Json)} {bodyJson : Json}
      (decoded : ImpactExpressionNode.decode raw = .ok (.bind bindings bodyJson))
      (nonempty : bindings ≠ []) (bindingsMatch : Bindings expression bindings bodyJson) :
      Matches expression raw
  | assertE {ty : Ty} {condition : Expr .bool} {body : Expr ty}
      {raw conditionJson bodyJson : Json}
      (decoded : ImpactExpressionNode.decode raw =
        .ok (.assertThen conditionJson bodyJson))
      (conditionMatches : Matches condition conditionJson)
      (bodyMatches : Matches body bodyJson) :
      Matches (.assertE condition body) raw
  | copyValue {ty : Ty} {value : Expr ty} {raw : Json}
      (valueMatches : Matches value raw) :
      Matches (.copyValue value) raw
  | disclose {ty : Ty} {span : SourceSpan} {value : Expr ty} {raw : Json}
      (valueMatches : Matches value raw) :
      Matches (.disclose span value) raw
  | eq {ty : Ty} {left right : Expr ty} {raw leftJson rightJson : Json}
      (decoded : ImpactExpressionNode.decode raw =
        .ok (.binary .eq leftJson rightJson))
      (scalarType : ScalarType ty)
      (leftMatches : Matches left leftJson) (rightMatches : Matches right rightJson) :
      Matches (.eq left right) raw
  | select {ty : Ty} {condition : Expr .bool} {yes no : Expr ty}
      {raw conditionJson yesJson noJson : Json}
      (decoded : ImpactExpressionNode.decode raw =
        .ok (.select conditionJson yesJson noJson))
      (scalarType : ScalarType ty)
      (conditionMatches : Matches condition conditionJson)
      (yesMatches : Matches yes yesJson) (noMatches : Matches no noJson) :
      Matches (.select condition yes no) raw
  | poseidon2 {domain : Nat} {left right : Expr .native} {raw leftJson rightJson : Json}
      (decoded : ImpactExpressionNode.decode raw =
        .ok (.poseidon2 (toString domain) leftJson rightJson))
      (leftMatches : Matches left leftJson) (rightMatches : Matches right rightJson) :
      Matches (.poseidon2 domain left right) raw

inductive Bindings : {ty : Ty} → Expr ty → List (String × Json) → Json → Prop where
  | terminal {ty : Ty} {expression : Expr ty} {bodyJson : Json}
      (matched : Matches expression bodyJson) :
      Bindings expression [] bodyJson
  | cons {source target : Ty} {name : String} {value : Expr source}
      {body : Expr target} {valueJson : Json}
      {tail : List (String × Json)} {bodyJson : Json}
      (valueMatches : Matches value valueJson)
      (bodyBindings : Bindings body tail bodyJson) :
      Bindings (.letE name value body) ((name, valueJson) :: tail) bodyJson
  | copyValue {ty : Ty} {value : Expr ty} {bindings : List (String × Json)}
      {bodyJson : Json} (inner : Bindings value bindings bodyJson) :
      Bindings (.copyValue value) bindings bodyJson
  | disclose {ty : Ty} {span : SourceSpan} {value : Expr ty}
      {bindings : List (String × Json)} {bodyJson : Json}
      (inner : Bindings value bindings bodyJson) :
      Bindings (.disclose span value) bindings bodyJson
end

end Noctium.Verification.ImpactExpressionMatch
