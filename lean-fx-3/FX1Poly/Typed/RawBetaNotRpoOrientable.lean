import FX1Poly.Core.RawIotaRpoBridge
import FX1Poly.Typed.UntypedOmegaNotStronglyNormalizing

/-! # FX1Poly/Typed/RawBetaNotRpoOrientable
    — the β boundary of the rose-tree RPO is a THEOREM, not a hand-typed verdict

`RawIotaRpoBridge` orients the three recursive ι arms (the obstruction that defeats every flat measure) by a
genuine recursive path order on the type-erased syntax `RoseTerm Generator` (via `eraseToRose`), and
`realGenRpoWellFounded` proves that order well-founded.  Its docstring concedes — in prose — that β stays
Tait-imported: "substitution can duplicate the argument arbitrarily, and raw β is non-SN."

This file turns that prose concession into a forced negative result.  No type-blind well-founded order on the
erased terms can orient raw β, because the Ω combinator `(λx. x x) (λx. x x)` β-reduces to ITSELF
(`omegaCombinator_betaSelfStep : Step omegaCombinator omegaCombinator`).  Any order that oriented every
β-step would have to place the reduct strictly below the redex; for Ω's self-step the reduct and redex are the
identical raw term, so its single erasure would sit strictly below itself — a self-loop no well-founded order
admits (`accessibleElementNotSelfRelated`).

Erasure makes the contradiction immediate: source and target of the self-step are the same `RawTerm 0`, hence
the same `RoseTerm Generator`, so no `eraseToRose`-commutation lemma is needed — the order is asked to relate
one fixed rose-tree to itself.

## Consequence for the capstone ledger

The recursive path order is genuinely well-founded on the terminating ι/η fragment (that IS
`realGenRpoWellFounded`), but it can never be a complete strong-normalization certificate for the full raw
β-calculus.  So the rose-tree-word-rewriting leg covers strong normalization only as a PARTIAL fragment — by
this theorem, not by stipulation.  The complement is honest: full β-SN routes through the Tait reducibility
argument with its typing hypothesis (Ω is untypable), exactly as `RawIotaRpoBridge` already imports.

## Zero-axiom verification

`betaNotOrientableByErasure` is the shipped accessibility self-loop refutation (`accessibleElementNotSelfRelated`,
a constant-motive `Acc.rec`) applied to `WellFounded.apply` at `eraseToRose omegaCombinator` and the β-self-step
oriented by the hypothesis.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core.RawIotaRpo

open FX1Poly.Core.RpoInductive
open FX1Poly.Typed

/-- **NO-GO: raw β is not orientable by any well-founded order on erased syntax.**  A `roseOrder` on
`RoseTerm Generator` that is well-founded AND orients every raw β-step (the reduct's erasure sits strictly
below the redex's) cannot exist.  Instantiate the orientation at Ω's β-self-step, whose redex and reduct are
the identical term `omegaCombinator`: it yields `roseOrder (eraseToRose omegaCombinator) (eraseToRose
omegaCombinator)`, a self-loop that `accessibleElementNotSelfRelated` refutes against the accessibility
`WellFounded.apply` supplies.  This is the recursive-path-order bridge's β-boundary as a theorem: the order
orients the terminating ι/η fragment but provably cannot extend to β. -/
theorem betaNotOrientableByErasure
    {roseOrder : RoseTerm Generator → RoseTerm Generator → Prop}
    (wellFounded : WellFounded roseOrder)
    (orientsRawBeta : ∀ {redex reduct : RawTerm 0},
        Step redex reduct → roseOrder (eraseToRose reduct) (eraseToRose redex)) :
    False :=
  accessibleElementNotSelfRelated
    (wellFounded.apply (eraseToRose omegaCombinator))
    (orientsRawBeta omegaCombinator_betaSelfStep)

end FX1Poly.Core.RawIotaRpo
