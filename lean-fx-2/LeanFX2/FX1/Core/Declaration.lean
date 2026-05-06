prelude
import LeanFX2.FX1.Core.Expr

/-! # FX1/Core/Declaration

Root status: Root-FX1 syntax scaffold.

Declarations for the minimal FX1 lambda-Pi environment.  This file only
describes declaration shape; environment well-formedness, typing, and checker
soundness are later M1-M4 obligations.
-/

namespace LeanFX2.FX1

/-- Top-level declarations in the minimal FX1 root calculus.

`axiomDecl` is present so staged object systems can be represented during
development, but it is not a release-root primitive.  The release root must
reject axiom declarations before any `Root-FX1` trust claim is made. -/
inductive Declaration : Type
  | axiomDecl (declName : Name) (typeExpr : Expr) : Declaration
  | defDecl (declName : Name) (typeExpr valueExpr : Expr) : Declaration
  | theoremDecl (declName : Name) (typeExpr proofExpr : Expr) : Declaration

namespace Declaration

/-- The declared constant name. -/
def name : Declaration -> Name
  | Declaration.axiomDecl declName _ => declName
  | Declaration.defDecl declName _ _ => declName
  | Declaration.theoremDecl declName _ _ => declName

/-- The declared type expression. -/
def typeExpr : Declaration -> Expr
  | Declaration.axiomDecl _ declaredTypeExpr => declaredTypeExpr
  | Declaration.defDecl _ declaredTypeExpr _ => declaredTypeExpr
  | Declaration.theoremDecl _ declaredTypeExpr _ => declaredTypeExpr

/-- The transparent value expression, when the declaration has one. -/
def valueExpr? : Declaration -> Option Expr
  | Declaration.axiomDecl _ _ => none
  | Declaration.defDecl _ _ valueExpr => some valueExpr
  | Declaration.theoremDecl _ _ proofExpr => some proofExpr

/-- Whether this declaration carries a transparent implementation/proof term. -/
def hasValue : Declaration -> Bool
  | Declaration.axiomDecl _ _ => false
  | Declaration.defDecl _ _ _ => true
  | Declaration.theoremDecl _ _ _ => true

/-- Whether this declaration is an axiom placeholder. -/
def isAxiomDeclaration : Declaration -> Bool
  | Declaration.axiomDecl _ _ => true
  | Declaration.defDecl _ _ _ => false
  | Declaration.theoremDecl _ _ _ => false

/-- Whether this declaration has the queried FX1 name. -/
def hasName (queryName : Name) (declaration : Declaration) : Bool :=
  Name.beq queryName (Declaration.name declaration)

end Declaration

end LeanFX2.FX1
