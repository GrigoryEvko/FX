import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingVcompRightUnconditional

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingVcompRightUnconditional — zero-axiom gate

Per-declaration zero-axiom gate for the empty-mid-boundary leg and the unconditional
vcomp-RIGHT matching congruence headline (the private Nat/range/lookup plumbing is covered
transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.processSpine_extract_eq_ofCanonicalExtractEq_emptyBoundary
#assert_no_axioms FX1Poly.Polygraph.extractAfterProcessing_vcompRight_ofSeed_emptyMid
#assert_no_axioms FX1Poly.Polygraph.matchingOf_vcompRight_congruence
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingVcompRightCongruence

end FX1PolyAudit
