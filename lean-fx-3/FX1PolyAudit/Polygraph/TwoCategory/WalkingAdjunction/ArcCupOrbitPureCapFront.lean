import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupOrbitPureCapFront

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupOrbitPureCapFront — zero-axiom gate

Per-declaration zero-axiom gate for the pure-CAP front-head orbit witness (the dual base of the mixed
cup/cap induction): the full `ArcCupOrbitWitness` discharged with NO re-selection hypothesis on the
pure-cap tail, by consuming the shipped `pureCapSpine_sort` crossed to atomic granularity.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupOrbitWitness_ofFrontHead_pureCap
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupOrbitPureCapFront

end FX1PolyAudit
