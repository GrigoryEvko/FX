import LeanFX.Mode.Defn
import LeanFX.Syntax.Term

/-! # LeanFX — ground-up intrinsic formalisation of FX in Lean 4.

This is the public root of the package.  Every public-facing definition
lives in `LeanFX/...` and is re-exported here in dependency order.

## The architectural commitment

Typing is *construction*, not a separate `Prop` family.  `Term Γ m T` is
a Lean type whose only inhabitants are well-typed FX terms in context
`Γ`, at mode `m`, of type `T`.  The constructor signatures *are* the
typing rules; misstated rules are rejected by Lean's kernel at the
constructor's declaration site, not when someone later writes a program.

## Trust base

  * Lean 4 kernel (~6 KLoC C++; accepted as TCB).
  * `LeanFX.Mode.Defn` — the four-mode enum.  Audited as input data.
  * `LeanFX.Syntax.Term` — the intrinsic Term GADT.  Each constructor
    is a typing rule; adding one is the only way to add a rule.

Everything else — substitution, reduction, conversion, the bidirectional
checker, the elaborator — operates *on* `Term Γ m T` and physically
cannot violate typing.  Bugs in those layers cause false rejections or
non-termination, never false acceptances of ill-typed programs. -/
