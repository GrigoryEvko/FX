import LeanFX.Syntax.ToRaw
import LeanFX.Syntax.TermSubst

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Term.toRaw` commute lemmas.

These bridge typed `Term` operations (subst, rename, cast) to their
raw `RawTerm` analogues.  Used by:
  * `Step.par.toRawBridge` — translates typed parallel-step into raw.
  * `Term.toRaw_cd` — translates typed `Term.cd` into raw `RawTerm.cd`.

The key principle: `Term.toRaw` erases all Ty-level annotations, so
any cast `▸` between Ty equations vanishes under `Term.toRaw`.  This
is captured by `Term.toRaw_cast`. -/

/-- Casting a typed term through a Ty equation does not affect its
raw form.  `Term.toRaw` only inspects the term's structure (var,
lam, app, ...), not the Ty index, so the cast is invisible. -/
theorem Term.toRaw_cast {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {T T' : Ty level scope}
    (h : T = T') (t : Term context T) :
    Term.toRaw (h ▸ t) = Term.toRaw t := by
  subst h
  rfl

end LeanFX.Syntax
