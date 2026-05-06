prelude
import LeanFX2.FX1.Core.Check

/-! # FX1/Core/Soundness

Root status: Root-FX1 proof-carrying checker soundness.

This module exposes the named `FX1.check_sound` theorem required by the
kernel sprint for the current no-constant lambda-Pi checker fragment.  The
theorem is intentionally tied to `Expr.check?`, whose result is projected from
the proof-carrying checker.

The extern-clean executable path `Expr.checkCore?` is already implemented and
audited for extern dependencies, but its direct soundness theorem is still a
separate M4 hardening task.  Do not use this theorem to claim that the
runtime-facing `checkCore?` path has been proved sound.
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

end LeanFX2.FX1
