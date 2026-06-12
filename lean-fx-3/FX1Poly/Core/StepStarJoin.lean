import FX1Poly.Core.StepStar

/-! # FX1Poly/Core/StepStarJoin
    — joinability vocabulary for the raw reduction relation.

The three shapes every confluence statement is phrased in: `Join`
(two terms reduce to a common reduct), `HasConfluence` (global
Church-Rosser — any two `StepStar`-reducts of a common source join),
and `HasStrip` (the asymmetric one-step-vs-many precursor).  This file
is pure vocabulary — no joins are PROVED here — so both confluence
routes can share it without an import cycle: the table route
(`StepStarConfluenceViaTable`, the kernel's sole proof of the global
properties) and the Newman/accessibility bridge (`StepStarConfluence`,
which consumes the table route's local join).

## Zero-axiom verification

Definitions only.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`. -/

namespace FX1Poly.Core

namespace StepStar

/-- Two raw terms join when they reduce to a common reduct by `StepStar`. -/
def Join {scope : Nat} (leftTerm rightTerm : RawTerm scope) : Prop :=
  ∃ commonTerm : RawTerm scope,
    StepStar leftTerm commonTerm ∧ StepStar rightTerm commonTerm

/-- Global Church-Rosser for the v2 raw `StepStar` relation. -/
def HasConfluence : Prop :=
  ∀ {scope : Nat} {sourceTerm leftReduct rightReduct : RawTerm scope},
    StepStar sourceTerm leftReduct →
    StepStar sourceTerm rightReduct →
    Join leftReduct rightReduct

/-- Strip property: a single step can be joined against an arbitrary
`StepStar` chain from the same source. -/
def HasStrip : Prop :=
  ∀ {scope : Nat} {sourceTerm leftReduct rightReduct : RawTerm scope},
    Step sourceTerm leftReduct →
    StepStar sourceTerm rightReduct →
    Join leftReduct rightReduct

end StepStar

end FX1Poly.Core
