import FX1Poly.Core.ConsistencyViaSconing
import FX1Poly.Typed.OpenStronglyNormalizingBetaEta

namespace FX1Poly.Typed.Spike3
open FX1Poly.Core

/-- SN-050 target signature: engine consistency from the empty-candidate bridge. -/
theorem consistencyFromEmptyCandidateBridge {profile : PolyProfile}
    {emptyTypeCode : RawTerm 0}
    (candidateBridge : ∀ closedTerm : RawTerm 0,
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) closedTerm emptyTypeCode →
        CanonicalFormsPredicate emptyIsValue closedTerm)
    (closedTerm : RawTerm 0)
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) closedTerm emptyTypeCode) :
    False :=
  consistencyViaSconing candidateBridge closedTerm typed

end FX1Poly.Typed.Spike3

#print axioms FX1Poly.Typed.Spike3.consistencyFromEmptyCandidateBridge
