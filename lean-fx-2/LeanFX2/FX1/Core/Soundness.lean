prelude
import LeanFX2.FX1.Core.Check

/-! # FX1/Core/Soundness

Root status: Root-FX1 proof-carrying checker soundness.

This module exposes the named `FX1.check_sound` theorem required by the
kernel sprint for the current lambda-Pi checker fragment.  That theorem is
tied to `Expr.check?`, whose result is projected from the proof-carrying
checker.

The extern-clean executable path `Expr.checkCore?` is also proved sound by
`FX1.checkCore_sound`.  Both the proof-carrying and runtime-facing paths
accept constants only through proved executable environment lookup; unknown
constants are rejected.
-/

namespace LeanFX2.FX1

/-- Soundness of the current proof-carrying FX1 checker fragment.

Coverage: de Bruijn variables, universes, Pi, lambda, and application.
Constants are accepted only when executable environment lookup returns a
proof-carrying declaration membership witness.  Conversion remains structural
in this root slice.
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
and application.  Constants are accepted by `Expr.checkCore?` only when the
same executable lookup path returns a declared type.
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
