import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingVcompRightCongruence

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingVcompRightCongruence — zero-axiom gate

Per-declaration zero-axiom gate for the vcomp-RIGHT matching congruence (seed-generic core +
the inhabited-mid-boundary walking-adjunction inhabitant; the private Nat/range plumbing is
covered transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.extractAfterProcessing_vcompRight_ofSeed
#assert_no_axioms FX1Poly.Polygraph.matchingOf_vcompRight_congruence_ofMidBoundaryPos
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingVcompRightCongruenceOnPositiveMidBoundary

end FX1PolyAudit
