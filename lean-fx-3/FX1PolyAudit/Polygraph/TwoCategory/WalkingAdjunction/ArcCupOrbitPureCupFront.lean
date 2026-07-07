import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupOrbitPureCupFront

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupOrbitPureCupFront — zero-axiom gate

Per-declaration zero-axiom gate for the pure-cup front-head orbit witness: the full
`ArcCupOrbitWitness` discharged with NO re-selection hypothesis on the pure-cup fragment, by
consuming the shipped `pureCupSpine_sort` crossed to atomic granularity.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupOrbitWitness_ofFrontHead_pureCup
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupOrbitPureCupFront

end FX1PolyAudit
