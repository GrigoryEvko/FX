import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCaseOrbitReduction

/-! # FX1PolyAudit/…/ArcCupCaseOrbitReduction — zero-axiom gate

Per-declaration zero-axiom gate for the orbit reduction: the located-cup orbit witness discharges
the whole walking-adjunction cup case, isolating `windowPin` + `tailsCancel` as the sole residual.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineArcHeadExtractionChained_cupCase_ofOrbitWitness
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupCaseOrbitReduction

end FX1PolyAudit
