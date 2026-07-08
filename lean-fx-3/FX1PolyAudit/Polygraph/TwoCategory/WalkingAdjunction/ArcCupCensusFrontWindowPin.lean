import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCensusFrontWindowPin

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupCensusFrontWindowPin — zero-axiom gate

Per-declaration zero-axiom gate for the fixed-length HEAD fronting from the census front + `windowPin`:
`cupHeadFronting_ofCensusFrontWindowPin` turns the shipped census front (the fixed-length interchange sort of
a located cup to the front) plus `windowPin` into the fronting of the GENUINE head
(`AtomicTraceEquiv secondList (headAtom :: movedRest)`), and
`cupHeadExtractionConclusion_ofCensusFrontWindowPin` threads it into the swap-NF cup-case discharge —
collapsing the fronting bookkeeping to the two named residuals `windowPin` + tail reselection.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupHeadFronting_ofCensusFrontWindowPin
#assert_no_axioms FX1Poly.Polygraph.cupHeadExtractionConclusion_ofCensusFrontWindowPin
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupCensusFrontWindowPin

end FX1PolyAudit
