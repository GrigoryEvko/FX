prelude
import LeanFX2.FX1.LeanKernel.Check
/-! # FX1/LeanKernel/Soundness

Soundness for the first Lean-kernel checker fragment.

## Deliverable

This file exposes the named `LeanKernel.check_sound` theorem for the current
accepted fragment: sorts, bound variables, constants, forall formation, and
lambda introduction.  This is not yet the full Lean kernel checker theorem.
-/

namespace LeanFX2
namespace FX1.LeanKernel

/-- Soundness of the current Lean-kernel checker fragment.

Coverage is deliberately narrow: sorts, bound variables, constants, forall
formation, and lambda introduction.  Unsupported Lean expression forms are
rejected by `check`, so they add no trusted computation rule in this slice.
-/
theorem check_sound {level scope : Nat}
    {environment : Environment level}
    {context : Context level scope}
    {expression typeExpr : Expr level scope}
    (checkingSucceeded :
      Eq
        (check environment context expression)
        (Option.some typeExpr)) :
    HasType environment context expression typeExpr :=
  Expr.check?_sound checkingSucceeded

end FX1.LeanKernel
end LeanFX2
