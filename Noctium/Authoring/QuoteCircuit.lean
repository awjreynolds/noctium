import Noctium.IR
import Lean

namespace Noctium.Authoring.QuoteCircuit

section

deriving instance Lean.ToExpr for Noctium.Foreign.Curve
attribute [-instance] instToExprCurve
attribute [local instance] instToExprCurve

deriving instance Lean.ToExpr for Noctium.Foreign.Kind
attribute [-instance] instToExprKind
attribute [local instance] instToExprKind

deriving instance Lean.ToExpr for Noctium.Foreign.FieldKind
attribute [-instance] instToExprFieldKind
attribute [local instance] instToExprFieldKind

deriving instance Lean.ToExpr for Noctium.Foreign.Point
attribute [-instance] instToExprPoint
attribute [local instance] instToExprPoint

deriving instance Lean.ToExpr for Noctium.Foreign.UnaryOp
attribute [-instance] instToExprUnaryOp
attribute [local instance] instToExprUnaryOp

deriving instance Lean.ToExpr for Noctium.Foreign.BinaryOp
attribute [-instance] instToExprBinaryOp
attribute [local instance] instToExprBinaryOp

deriving instance Lean.ToExpr for Noctium.SourceSpan
attribute [-instance] instToExprSourceSpan
attribute [local instance] instToExprSourceSpan

deriving instance Lean.ToExpr for Noctium.Ty
attribute [-instance] instToExprTy
attribute [local instance] instToExprTy

deriving instance Lean.ToExpr for Noctium.Types.CompositeType
attribute [-instance] instToExprCompositeType
attribute [local instance] instToExprCompositeType

deriving instance Lean.ToExpr for Noctium.Types.Field
attribute [-instance] instToExprField
attribute [local instance] instToExprField

deriving instance Lean.ToExpr for Noctium.Types.StructDecl
attribute [-instance] instToExprStructDecl
attribute [local instance] instToExprStructDecl

deriving instance Lean.ToExpr for Noctium.Types.VariantDecl
attribute [-instance] instToExprVariantDecl
attribute [local instance] instToExprVariantDecl

deriving instance Lean.ToExpr for Noctium.Types.EnumDecl
attribute [-instance] instToExprEnumDecl
attribute [local instance] instToExprEnumDecl

deriving instance Lean.ToExpr for Noctium.Types.CompositeEnv
attribute [-instance] instToExprCompositeEnv
attribute [local instance] instToExprCompositeEnv

deriving instance Lean.ToExpr for Noctium.Visibility
attribute [-instance] instToExprVisibility
attribute [local instance] instToExprVisibility

deriving instance Lean.ToExpr for Noctium.PrivateOriginKind
attribute [-instance] instToExprPrivateOriginKind
attribute [local instance] instToExprPrivateOriginKind

private def exprFamilyType : Lean.Expr :=
  .lam `ty (Lean.toTypeExpr Noctium.Ty)
    (.app (.const ``Noctium.Expr []) (.bvar 0)) .default

local instance [∀ ty, Lean.ToExpr (Noctium.Expr ty)] :
    Lean.ToExpr (Sigma Noctium.Expr) where
  toTypeExpr := Lean.mkApp2 (.const ``Sigma [0, 0])
    (Lean.toTypeExpr Noctium.Ty) exprFamilyType
  toExpr := fun pair => match pair with
    | ⟨ty, value⟩ => Lean.mkApp4 (.const ``Sigma.mk [0, 0])
        (Lean.toTypeExpr Noctium.Ty) exprFamilyType
        (Lean.toExpr ty) (Lean.toExpr value)

deriving instance Lean.ToExpr for Noctium.Expr
attribute [-instance] instToExprExpr
attribute [local instance] instToExprExpr

deriving instance Lean.ToExpr for Noctium.Input
attribute [-instance] instToExprInput
attribute [local instance] instToExprInput

deriving instance Lean.ToExpr for Noctium.Output
attribute [-instance] instToExprOutput
attribute [local instance] instToExprOutput

deriving instance Lean.ToExpr for Noctium.Circuit
attribute [-instance] instToExprCircuit
attribute [local instance] instToExprCircuit

/-- Convert a checked circuit value into its kernel expression. -/
def circuitValueExpr (circuit : Noctium.Circuit) : Lean.Expr := Lean.toExpr circuit

def circuitTypeExpr : Lean.Expr := Lean.toTypeExpr Noctium.Circuit

end

end Noctium.Authoring.QuoteCircuit
