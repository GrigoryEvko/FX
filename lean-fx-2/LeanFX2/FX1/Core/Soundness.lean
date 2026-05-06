prelude
import LeanFX2.FX1.Core.Check

/-! # FX1/Core/Soundness

Root status: Root-FX1 proof-carrying checker soundness.

This module exposes the named `FX1.check_sound` theorem required by the
kernel sprint for the current no-constant lambda-Pi checker fragment.  That
theorem is tied to `Expr.check?`, whose result is projected from the
proof-carrying checker.

The extern-clean executable path `Expr.checkCore?` is also proved sound by
`FX1.checkCore_sound`.  Both the proof-carrying and runtime-facing paths
conservatively reject constants until executable environment lookup is proved.
-/

namespace LeanFX2.FX1

/-- Soundness of the current proof-carrying FX1 checker fragment.

Coverage: de Bruijn variables, universes, Pi, lambda, and application.
Constants are conservatively rejected by the checker until executable
environment lookup and conversion are promoted into the same proved fragment.
-/
theorem check_sound
    {environment : Environment}
    {context : Context}
    {expression expectedTypeExpr : Expr}
    (checkingSucceeded :
      Eq
        (Expr.check? environment context expression expectedTypeExpr)
        true) :
    HasType environment context expression expectedTypeExpr :=
  Expr.check?_sound checkingSucceeded

/-- Soundness of the runtime-facing FX1 checker fragment.

Coverage matches `check_sound`: de Bruijn variables, universes, Pi, lambda,
and application.  Constants are conservatively rejected by `Expr.checkCore?`.
-/
theorem checkCore_sound
    {environment : Environment}
    {context : Context}
    {expression expectedTypeExpr : Expr}
    (checkingSucceeded :
      Eq
        (Expr.checkCore? environment context expression expectedTypeExpr)
        true) :
    HasType environment context expression expectedTypeExpr :=
  Expr.checkCore_sound checkingSucceeded

end LeanFX2.FX1
