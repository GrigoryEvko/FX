import FX1Poly.Typed.SimplyTypedConvDecision
import FX1Poly.Typed.WfContextDecidableConv

/-! # FX1Poly/Typed/MilestoneA0SimplyTypedFloor
    — the UNCONDITIONAL defensible-kernel floor: the simply-typed fragment has SN PROVEN and Conv decidable
      (Milestone A0 over the already-decidable fragment, NOT gated on SN-043)

The Milestone-A spine (decidable typed checking + decidable typed Conv) is shipped over broader fragments
(`TY-DEC`, `TY-CONV-dec`).  The broadest decidable-Conv DECIDERS are stated WITH a strong-normalization
HYPOTHESIS (`Conv.decidableOfStronglyNormalizing`), but that hypothesis is now DISCHARGED: SN-043 SHIPPED
(`HasTypeDescPi.stronglyNormalizingOfWfContextDesc`, OB-5, over well-formed contexts — the bounded route, NOT the
once-feared universe-domain-Π cumulativity obstruction), so decidable typed Conv is UNCONDITIONAL on the whole
WfContext fragment (`Conv.decidableOfWellTypedInWfContextDesc`, the `wfContextDefensibleKernel` floor below).
HONEST LEDGER (#484): decidability is DONE; SUBJECT REDUCTION is NOT a decidability ingredient (the decider
routes through SN + confluence, never SR — SR / GCC-5 #842 gates canonicity-PROGRESS, not Conv-decidability); the
0-false-positive / 0-false-negative honesty is PER-FRAGMENT, not joint; and the one genuinely-OPEN piece is the
JOINT APEX — full canonicity across the data fragments — gated on the §5 EmptyType candidate model-change
(#810/#768).

This file names the honest UNCONDITIONAL FLOOR: the simply-typed fragment (`SimplyTypedTermLF` — neutral / data
leaves + non-dependent arrows, the level-free first-order fragment with a PROVEN fundamental theorem) where
strong normalization is a THEOREM, not a hypothesis, so conversion is decidable with no SN assumption — typing
alone decides.  This is the concrete "defensible kernel" floor the A0 milestone declares over the
already-decidable fragment.

Two declarations:
  * `simplyTypedBareClosedStronglyNormalizing` — the standalone reusable form of the SN half (also used inline
    inside `Conv.decidableOfSimplyTypedBareClosed`): a closed simply-typed term is strongly normalizing,
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
unconditionally (`Conv.decidableOfSimplyTypedBareClosed`).  The reusable standalone form of the reflection
that decider also uses inline. -/
theorem simplyTypedBareClosedStronglyNormalizing {profile : PolyProfile}
    {term type : RawTerm 0}
    (typed : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type) :
    IsStronglyNormalizing term :=
  StepStar.stronglyNormalizing_of_subst emptyClosingSubst term
    (typed.stronglyNormalizingClosed emptyClosingSubst)

/-- **The Milestone-A0 defensible-kernel floor, as a named bundle.**  Over the simply-typed fragment
(`SimplyTypedTermLF`), the kernel is a DEFENSIBLE DECIDABLE KERNEL UNCONDITIONALLY: strong normalization is a
THEOREM (`stronglyNormalizing`, not a hypothesis) and conversion is therefore decidable with typing alone
(`convDecidable`, no SN hypothesis).  This is the formal declaration of Milestone A0 over the already-decidable
fragment with NO context presupposition at all: the broad decidable-Conv deciders
(`Conv.decidableOfStronglyNormalizing`) TAKE an SN hypothesis, which the simply-typed fundamental theorem
discharges here unconditionally.  (The now-shipped SN-043 discharges the same hypothesis for every WELL-FORMED
context — the `wfContextDefensibleKernel` floor below.)  `Type`-valued because `convDecidable` is decision DATA. -/
structure SimplyTypedDefensibleKernel (profile : PolyProfile) : Type where
  /-- Closed simply-typed terms are strongly normalizing — SN PROVEN, no hypothesis. -/
  stronglyNormalizing : ∀ {term type : RawTerm 0},
    SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type →
      IsStronglyNormalizing term
  /-- Conversion of closed simply-typed terms is decidable — typing alone decides, no SN hypothesis. -/
  convDecidable : ∀ {firstTerm firstType secondTerm secondType : RawTerm 0},
    SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) firstTerm firstType →
      SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) secondTerm secondType →
        Decidable (Conv firstTerm secondTerm)

/-- **The witness for the Milestone-A0 defensible kernel.**  Both fields are the shipped UNCONDITIONAL theorems:
`stronglyNormalizing` is `simplyTypedBareClosedStronglyNormalizing` (the FT's SN reflected to the bare term),
`convDecidable` is `Conv.decidableOfSimplyTypedBareClosed` (the FT's SN feeding the normalizer-based decider).
So Milestone A0 over the simply-typed fragment HOLDS, zero-axiom, with no SN hypothesis AND no context
presupposition — the honest defensible-kernel floor.  (The broader `wfContextDefensibleKernel` below extends this
to EVERY well-formed context via the now-shipped SN-043; only the joint canonicity apex stays open, on §5 / GCC-5.) -/
def simplyTypedDefensibleKernel {profile : PolyProfile} : SimplyTypedDefensibleKernel profile :=
  { stronglyNormalizing := simplyTypedBareClosedStronglyNormalizing
    convDecidable := Conv.decidableOfSimplyTypedBareClosed }

/-- **The WfContext defensible-kernel floor — the SN-043 widening of the simply-typed floor (#484).**  Over
EVERY well-formed context (`WfContextDesc`), the grown kernel `HasTypeDescPi` is a DEFENSIBLE DECIDABLE KERNEL:
strong normalization is a THEOREM (the shipped SN-043, over WF contexts) and conversion is therefore decidable
with the well-formedness presupposition alone — no separate SN hypothesis.  This WIDENS the simply-typed floor
above from the level-free first-order fragment to the WHOLE well-formed-context fragment, the correction the
now-shipped SN-043 makes possible (the file's earlier "open SN-043" framing was stale).  SUBJECT REDUCTION is
NOT an ingredient: the decider routes through SN + confluence, so Conv-decidability does NOT wait on the grown SR
bundle (GCC-5).  `Type`-valued because `convDecidable` is decision DATA. -/
structure WfContextDefensibleKernel (profile : PolyProfile) : Type where
  /-- Well-typed terms in a well-formed context are strongly normalizing — the shipped open SN-043, no
  hypothesis beyond well-formedness. -/
  stronglyNormalizing : ∀ {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope},
    WfContextDesc context → HasTypeDescPi profile context subject classifier →
      IsStronglyNormalizing subject
  /-- Conversion of well-typed terms in a well-formed context is decidable — well-formedness alone decides, no
  SN and no SR hypothesis. -/
  convDecidable : ∀ {scope : Nat} {context : TypingContext profile scope}
      {leftSubject leftClassifier rightSubject rightClassifier : RawTerm scope},
    WfContextDesc context →
      HasTypeDescPi profile context leftSubject leftClassifier →
        HasTypeDescPi profile context rightSubject rightClassifier →
          Decidable (Conv leftSubject rightSubject)

/-- **The witness for the WfContext defensible kernel.**  Both fields are shipped UNCONDITIONAL theorems:
`stronglyNormalizing` is the open-context SN-043 (`HasTypeDescPi.stronglyNormalizingOfWfContextDesc`),
`convDecidable` is `Conv.decidableOfWellTypedInWfContextDesc` (that SN feeding the normalizer-based decider).  So
Milestone-A0 decidability holds over EVERY well-formed context, zero-axiom — the honest current floor, broader
than the simply-typed one, with neither SR nor canonicity among its ingredients (the joint canonicity apex stays
open on §5 / GCC-5). -/
def wfContextDefensibleKernel {profile : PolyProfile} : WfContextDefensibleKernel profile :=
  { stronglyNormalizing := fun contextWellFormed typed =>
      HasTypeDescPi.stronglyNormalizingOfWfContextDesc contextWellFormed typed
    convDecidable := fun contextWellFormed leftTyped rightTyped =>
      Conv.decidableOfWellTypedInWfContextDesc contextWellFormed leftTyped rightTyped }

end FX1Poly.Typed
