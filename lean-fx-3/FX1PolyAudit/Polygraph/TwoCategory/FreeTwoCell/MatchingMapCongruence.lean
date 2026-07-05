import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingMapCongruence

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingMapCongruence — zero-axiom gate

Per-declaration zero-axiom gate for the propext-free `Nat`-list map congruence — the
list-congruence the cup-head diagram-partner fold rides on.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natMapCongrOfMemAgree
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasNatMapCongruence

end FX1PolyAudit
