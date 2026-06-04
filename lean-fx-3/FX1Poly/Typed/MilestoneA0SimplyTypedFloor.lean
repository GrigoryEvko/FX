import FX1Poly.Typed.SimplyTypedConvDecision

/-! # FX1Poly/Typed/MilestoneA0SimplyTypedFloor
    — the UNCONDITIONAL defensible-kernel floor: the simply-typed fragment has SN PROVEN and Conv decidable
      (Milestone A0 over the already-decidable fragment, NOT gated on SN-043)

The Milestone-A spine (decidable typed checking + decidable typed Conv) is shipped over broader fragments
(`TY-DEC`, `TY-CONV-dec`), but the broadest decidable-Conv results are stated WITH a strong-normalization
HYPOTHESIS (`Conv.decidableOfStronglyNormalizing`, `Conv.decidableOfHasTypeDescPiStronglyNormalizes`) — the SN
discharge for the full kernel is the open SN-043, blocked at the universe-domain Π by the cumulativity
obstruction (`DenoteKeyedCumulativityObstruction.lean`).

This file names the honest UNCONDITIONAL FLOOR: the simply-typed fragment (`SimplyTypedTermLF` — neutral / data
leaves + non-dependent arrows, the level-free first-order fragment with a PROVEN fundamental theorem) where
strong normalization is a THEOREM, not a hypothesis, so conversion is decidable with no SN assumption — typing
alone decides.  This is the concrete "defensible kernel" floor the A0 milestone declares over the
already-decidable fragment.

Two declarations:
  * `simplyTypedBareClosedStronglyNormalizing` — the standalone reusable form of the SN half (previously only
    inline inside `Conv.decidableOfSimplyTypedBareClosed`): a closed simply-typed term is strongly normalizing,
    via the fundamental theorem's `stronglyNormalizingClosed` reflected to the bare term through
    `StepStar.stronglyNormalizing_of_subst`.
  * `Conv.decidableOfSimplyTypedBareClosed` (shipped, `SimplyTypedConvDecision.lean`) is the decidable-Conv half.

The QUALIFIER BOUNDARY (honest, NOT silently widened): this floor is the SIMPLY-TYPED fragment only.  The
broader denote/dependent fragments need the full SN-043 (the bound-carrying model #753 or a fragment milestone),
which remains open.  Per-fragment 0/0, not joint.

## Zero-axiom verification

`simplyTypedBareClosedStronglyNormalizing` is the fundamental theorem's SN (`SimplyTypedTermLF.
stronglyNormalizingClosed`) reflected to the bare term through `StepStar.stronglyNormalizing_of_subst` — the
same reflection `Conv.decidableOfSimplyTypedBareClosed` performs inline, now standalone.  No induction, no
`funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **A closed simply-typed term is strongly normalizing** (the standalone SN half of the defensible-kernel
floor).  The simply-typed fundamental theorem gives strong normalization of the term closed by the canonical
empty substitution; `StepStar.stronglyNormalizing_of_subst` reflects that back to the bare term.  Typing alone
proves SN — no hypothesis — which is exactly what makes the simply-typed fragment's conversion decidable
unconditionally (`Conv.decidableOfSimplyTypedBareClosed`).  The reusable form of the reflection previously only
available inline inside that decider. -/
theorem simplyTypedBareClosedStronglyNormalizing {profile : PolyProfile}
    {term type : RawTerm 0}
    (typed : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type) :
    IsStronglyNormalizing term :=
  StepStar.stronglyNormalizing_of_subst emptyClosingSubst term
    (typed.stronglyNormalizingClosed emptyClosingSubst)

end FX1Poly.Typed
