import FX1Poly.Typed.MilestoneA0SimplyTypedFloor
import FX1Poly.Core.ReducibilityConversionViaSconing
import FX1Poly.Core.ReducibilityCandidate

/-! # FX1Poly/Typed/SimplyTypedMetatheoryViaSconing
    — the first CONCRETE UNCONDITIONAL instantiation of the metatheory capstone (closed simply-typed fragment)

`ReducibilityConversionViaSconing.lean` ships `reducibilityFullMetatheoryViaSconing`: from ONE reducibility
candidate and its fundamental obligation, the complete decidable metatheory (strong normalization + weak
normalization + decidable conversion) of the strongly-normalizing fragment.  That capstone is PARAMETRIC in the
candidate and the fundamental — until now it had no concrete inhabitant exhibited, so it could in principle have
been a vacuous interface.

This file gives the first concrete UNCONDITIONAL instantiation, witnessing the capstone fires on a real
fragment with NO SN-043 dependency: the closed simply-typed fragment.  The instantiation composes two shipped
zero-axiom facts:

  * the SN reducibility candidate `isStronglyNormalizing_isReducibilityCandidate` (`IsStronglyNormalizing` is the
    degenerate-but-genuine Girard candidate — CR1/CR2/CR3 hold), as the `candidate`;
  * the unconditional simply-typed SN theorem `simplyTypedBareClosedStronglyNormalizing` (closed simply-typed ⟹
    strongly normalizing — the Milestone-A0 floor, proven WITHOUT SN-043), as the `fundamental`.

The composition is genuine and non-circular: the fundamental is "closed simply-typed ⟹ SN" (a real theorem,
isWellTyped ≠ candidate), and the capstone's extractions then carry SN ⟹ {reaches normal form, decidable
conversion}.  So the closed simply-typed fragment has its FULL decidable metatheory derived through the general
sconing capstone, unconditionally — the concrete witness that the capstone is inhabited and useful.

## What lands here (all zero-axiom)

  * `IsClosedSimplyTyped` — closed simply-typed well-typedness as a bare `RawTerm 0 → Prop` predicate (there
    exists a type the term checks against in the empty context).
  * `simplyTypedFullMetatheoryViaSconing` — the capstone instantiated: the closed simply-typed fragment's full
    decidable metatheory (SN + weak normalization + decidable conversion), UNCONDITIONAL.
  * `simplyTypedReachesNormalForm` — the weak-normalization headline: every closed simply-typed term reaches a
    structural normal form (genuinely new — the WN form for the fragment).
  * `simplyTypedConversionDecidableViaSconing` — decidable conversion for the fragment via the sconing route,
    cross-checking the direct `Conv.decidableOfSimplyTypedBareClosed` decider through the general capstone.

## Honest scope boundary

The fragment is the closed simply-typed fragment (`SimplyTypedTermLF` in the empty context); the candidate used
is the degenerate SN candidate (the simply-typed reducibility candidate is not separately threaded — only its SN
consequence is needed, which the Milestone-A0 floor supplies).  The decidable conversion is also shipped directly
(`Conv.decidableOfSimplyTypedBareClosed`); this re-derives it through the general capstone as the first concrete
instantiation, NOT as a new decidability result for a broader fragment.

## Zero-axiom verification

A record literal applying `reducibilityFullMetatheoryViaSconing` to the shipped SN candidate and the simply-typed
SN fundamental, plus two field projections.  No induction, no `funext`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **Closed simply-typed well-typedness as a bare `RawTerm 0` predicate.**  A closed term is well-typed when
there exists a type it checks against in the empty context — the `isWellTyped` notion the metatheory capstone
consumes for the simply-typed fragment. -/
def IsClosedSimplyTyped {profile : PolyProfile} (term : RawTerm 0) : Prop :=
  ∃ type : RawTerm 0, SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type

/-- **The closed simply-typed fragment's full decidable metatheory, via the sconing capstone (unconditional).**
`reducibilityFullMetatheoryViaSconing` instantiated at the SN reducibility candidate and the unconditional
simply-typed SN fundamental (`simplyTypedBareClosedStronglyNormalizing`): strong normalization, weak
normalization, AND decidable conversion for closed simply-typed terms, with NO SN-043 dependency.  The first
concrete inhabitant of the metatheory capstone — the witness that "one fundamental ⟹ the whole decidable
metatheory" is not a vacuous interface but fires on a real proven fragment. -/
def simplyTypedFullMetatheoryViaSconing {profile : PolyProfile} :
    ReducibilityFullMetatheory (IsClosedSimplyTyped (profile := profile)) :=
  reducibilityFullMetatheoryViaSconing isStronglyNormalizing_isReducibilityCandidate
    (fun _term witnessed =>
      witnessed.elim (fun _type typed => simplyTypedBareClosedStronglyNormalizing typed))

/-- **Weak normalization for the closed simply-typed fragment.**  Every closed simply-typed term reaches a
structural normal form — the weak-normalization headline projected from the capstone instance. -/
theorem simplyTypedReachesNormalForm {profile : PolyProfile} (term : RawTerm 0)
    (typed : IsClosedSimplyTyped (profile := profile) term) : reachesStepNormalForm term :=
  simplyTypedFullMetatheoryViaSconing.reachesNormalForm term typed

/-- **Decidable conversion for the closed simply-typed fragment, via the sconing capstone.**  Conversion of two
closed simply-typed terms is decidable — the decidable-conversion field of the capstone instance, cross-checking
the direct `Conv.decidableOfSimplyTypedBareClosed` decider through the general sconing route. -/
def simplyTypedConversionDecidableViaSconing {profile : PolyProfile} (leftTerm rightTerm : RawTerm 0)
    (leftTyped : IsClosedSimplyTyped (profile := profile) leftTerm)
    (rightTyped : IsClosedSimplyTyped (profile := profile) rightTerm) :
    Decidable (Conv leftTerm rightTerm) :=
  simplyTypedFullMetatheoryViaSconing.conversionDecidable leftTerm rightTerm leftTyped rightTyped

end FX1Poly.Typed
