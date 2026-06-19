import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Denote.Core.DenoteKeyedCanonicalThreshold

/-! # FX1PolyAudit/AuditDenoteKeyedCanonicalThreshold
    — zero-axiom gate for the canonical-threshold reducibility motive (FTGEN-4.2 / #752 threshold-swap)

The threshold-pinned motive `CandidateReducibleAboveDenote` + its monotone/forget glue + the five canonical
leaf arms + the headline `piTyCode` (the dependent-Π threshold-swap RESOLVED via a FIXED codomain threshold).
Must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.CandidateReducibleAboveDenote
#assert_no_axioms FX1Poly.Typed.CandidateReducibleAboveDenote.raiseThreshold
#assert_no_axioms FX1Poly.Typed.CandidateReducibleAboveDenote.toUniform
#assert_no_axioms FX1Poly.Typed.CandidateReducibleAboveDenote.ofNeutral
#assert_no_axioms FX1Poly.Typed.CandidateReducibleAboveDenote.ofDataEmpty
#assert_no_axioms FX1Poly.Typed.CandidateReducibleAboveDenote.ofDataFlat
#assert_no_axioms FX1Poly.Typed.CandidateReducibleAboveDenote.ofUniverseCode
#assert_no_axioms FX1Poly.Typed.CandidateReducibleAboveDenote.headExpand
#assert_no_axioms FX1Poly.Typed.CandidateReducibleAboveDenote.piTyCode

end FX1PolyAudit
