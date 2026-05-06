prelude
import LeanFX2.FX1.Core.Level

/-! # FX1/Core/Expr

Root status: Root-FX1 syntax scaffold.

This is the minimal lambda-Pi expression language described in
`kernel-sprint.md` §1.0.1.  It intentionally omits free variables,
metavariables, let expressions, inductives, literals, projections, opaque
declarations, and quotient primitives.  Those features belong to later FX1
or `FX1.LeanKernel` layers after the small core has preservation and checker
soundness.
-/

namespace LeanFX2.FX1

/-- Minimal FX1 expressions: de Bruijn variables, universes, constants,
Pi types, lambda abstractions, and applications. -/
inductive Expr : Type
  | bvar (index : Nat) : Expr
  | sort (sortLevel : Level) : Expr
  | const (constName : Name) : Expr
  | pi (domain body : Expr) : Expr
  | lam (domain body : Expr) : Expr
  | app (functionExpr argumentExpr : Expr) : Expr

namespace Expr

/-- Structural executable equality for FX1 expressions.

The checker uses this as the first exact-syntax comparison before richer
conversion is introduced.  The constructor-pair table is fully enumerated to
avoid wildcard-generated proof artifacts. -/
def beq : Expr -> Expr -> Bool
  | Expr.bvar leftIndex, Expr.bvar rightIndex =>
      Nat.beq leftIndex rightIndex
  | Expr.bvar _, Expr.sort _ => false
  | Expr.bvar _, Expr.const _ => false
  | Expr.bvar _, Expr.pi _ _ => false
  | Expr.bvar _, Expr.lam _ _ => false
  | Expr.bvar _, Expr.app _ _ => false
  | Expr.sort _, Expr.bvar _ => false
  | Expr.sort leftLevel, Expr.sort rightLevel =>
      Level.beq leftLevel rightLevel
  | Expr.sort _, Expr.const _ => false
  | Expr.sort _, Expr.pi _ _ => false
  | Expr.sort _, Expr.lam _ _ => false
  | Expr.sort _, Expr.app _ _ => false
  | Expr.const _, Expr.bvar _ => false
  | Expr.const _, Expr.sort _ => false
  | Expr.const leftName, Expr.const rightName =>
      Name.beq leftName rightName
  | Expr.const _, Expr.pi _ _ => false
  | Expr.const _, Expr.lam _ _ => false
  | Expr.const _, Expr.app _ _ => false
  | Expr.pi _ _, Expr.bvar _ => false
  | Expr.pi _ _, Expr.sort _ => false
  | Expr.pi _ _, Expr.const _ => false
  | Expr.pi leftDomain leftBody, Expr.pi rightDomain rightBody =>
      Bool.and
        (Expr.beq leftDomain rightDomain)
        (Expr.beq leftBody rightBody)
  | Expr.pi _ _, Expr.lam _ _ => false
  | Expr.pi _ _, Expr.app _ _ => false
  | Expr.lam _ _, Expr.bvar _ => false
  | Expr.lam _ _, Expr.sort _ => false
  | Expr.lam _ _, Expr.const _ => false
  | Expr.lam _ _, Expr.pi _ _ => false
  | Expr.lam leftDomain leftBody, Expr.lam rightDomain rightBody =>
      Bool.and
        (Expr.beq leftDomain rightDomain)
        (Expr.beq leftBody rightBody)
  | Expr.lam _ _, Expr.app _ _ => false
  | Expr.app _ _, Expr.bvar _ => false
  | Expr.app _ _, Expr.sort _ => false
  | Expr.app _ _, Expr.const _ => false
  | Expr.app _ _, Expr.pi _ _ => false
  | Expr.app _ _, Expr.lam _ _ => false
  | Expr.app leftFunction leftArgument,
      Expr.app rightFunction rightArgument =>
      Bool.and
        (Expr.beq leftFunction rightFunction)
        (Expr.beq leftArgument rightArgument)

/-- Structural size of an FX1 expression. -/
def nodeCount : Expr -> Nat
  | Expr.bvar _ => 1
  | Expr.sort _ => 1
  | Expr.const _ => 1
  | Expr.pi domain body =>
      Nat.succ (Nat.add (Expr.nodeCount domain) (Expr.nodeCount body))
  | Expr.lam domain body =>
      Nat.succ (Nat.add (Expr.nodeCount domain) (Expr.nodeCount body))
  | Expr.app functionExpr argumentExpr =>
      Nat.succ (Nat.add (Expr.nodeCount functionExpr)
        (Expr.nodeCount argumentExpr))

end Expr

end LeanFX2.FX1
