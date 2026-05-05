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
