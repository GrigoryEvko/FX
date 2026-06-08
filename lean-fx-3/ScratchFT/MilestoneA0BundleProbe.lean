import FX1Poly.Typed.MilestoneA0SimplyTypedFloor

/-! Scratch probe: the Milestone A0 defensible-kernel bundle — a single named structure packaging the
    unconditional simply-typed floor (SN proven + Conv decidable), with a witness from the shipped theorems.
    The formal "declaration" of Milestone A0 over the already-decidable fragment (#666/#557). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

structure SimplyTypedDefensibleKernel (profile : PolyProfile) : Type where
  stronglyNormalizing : ∀ {term type : RawTerm 0},
    SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type →
      IsStronglyNormalizing term
  convDecidable : ∀ {firstTerm firstType secondTerm secondType : RawTerm 0},
    SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) firstTerm firstType →
      SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) secondTerm secondType →
        Decidable (Conv firstTerm secondTerm)

def simplyTypedDefensibleKernel {profile : PolyProfile} : SimplyTypedDefensibleKernel profile :=
  { stronglyNormalizing := simplyTypedBareClosedStronglyNormalizing
    convDecidable := Conv.decidableOfSimplyTypedBareClosed }

#print axioms simplyTypedDefensibleKernel

end FX1Poly.Typed
