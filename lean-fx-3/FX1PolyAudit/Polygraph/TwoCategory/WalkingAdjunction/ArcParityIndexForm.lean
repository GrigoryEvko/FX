import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcParityIndexForm

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcParityIndexForm — zero-axiom gate

Per-declaration zero-axiom gate for the parity invariant's matching-index form: the
run-independent boundary index class, the found-partner class flip, and the cross-run
leg-swap refutation.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcBoundaryIndexClass
#assert_no_axioms FX1Poly.Polygraph.arcPartnerFound_classOpposite
#assert_no_axioms FX1Poly.Polygraph.arcPartnerLegSwap_impossible
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcParityIndexForm

end FX1PolyAudit
