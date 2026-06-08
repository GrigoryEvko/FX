import FX1Poly.Typed.MilestoneA0SimplyTypedFloor
import FX1Poly.Core.ReducibilityConversionViaSconing
import FX1Poly.Core.ReducibilityCandidate

/-! Scratch probe: the FIRST concrete UNCONDITIONAL instantiation of the metatheory capstone — the closed
    simply-typed fragment's full decidable metatheory (SN + reaches-NF + decidable Conv) via the sconing route. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- Closed simply-typed well-typedness as a bare `RawTerm 0` predicate. -/
def IsClosedSimplyTyped {profile : PolyProfile} (term : RawTerm 0) : Prop :=
  ∃ type : RawTerm 0, SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type

/-- The full decidable metatheory of the closed simply-typed fragment, via the sconing capstone, with the SN
reducibility candidate and the unconditional simply-typed SN fundamental. UNCONDITIONAL — no SN-043. -/
def simplyTypedFullMetatheoryViaSconing {profile : PolyProfile} :
    ReducibilityFullMetatheory (IsClosedSimplyTyped (profile := profile)) :=
  reducibilityFullMetatheoryViaSconing isStronglyNormalizing_isReducibilityCandidate
    (fun _term witnessed =>
      witnessed.elim (fun _type typed => simplyTypedBareClosedStronglyNormalizing typed))

/-- Weak normalization for the closed simply-typed fragment: every closed simply-typed term reaches a
structural normal form (the normalization headline via the capstone). -/
theorem simplyTypedReachesNormalForm {profile : PolyProfile} (term : RawTerm 0)
    (typed : IsClosedSimplyTyped (profile := profile) term) : reachesStepNormalForm term :=
  simplyTypedFullMetatheoryViaSconing.reachesNormalForm term typed

/-- Decidable conversion for the closed simply-typed fragment, via the sconing capstone (cross-checking the
direct `Conv.decidableOfSimplyTypedBareClosed`). -/
def simplyTypedConversionDecidableViaSconing {profile : PolyProfile} (leftTerm rightTerm : RawTerm 0)
    (leftTyped : IsClosedSimplyTyped (profile := profile) leftTerm)
    (rightTyped : IsClosedSimplyTyped (profile := profile) rightTerm) :
    Decidable (Conv leftTerm rightTerm) :=
  simplyTypedFullMetatheoryViaSconing.conversionDecidable leftTerm rightTerm leftTyped rightTyped

end FX1Poly.Typed

#print axioms FX1Poly.Typed.simplyTypedFullMetatheoryViaSconing
#print axioms FX1Poly.Typed.simplyTypedReachesNormalForm
#print axioms FX1Poly.Typed.simplyTypedConversionDecidableViaSconing
