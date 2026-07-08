import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupKFoldBoundaryRead

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupKFoldBoundaryRead — zero-axiom gate

Per-declaration zero-axiom gate for the BOUNDARY-READ side of the head-cup census read-off lifted past an
ARBITRARY window-disjoint cap tail: `natListGetAt_foldRemovals_below` (the removal-side dual of the r6 JOIN-side
`isSameComponent_foldJoins_offProbe`) and the two head-cup boundary reads `kCapBoundaryRead_atLeftLeg` /
`_belowWindow`, generalizing the single-cap `twoAtomBoundaryRead_*` to arbitrary cap-tail length.  The public
assertions transitively cover `foldRemovals` and `cupOpenWiresK`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natListGetAt_foldRemovals_below
#assert_no_axioms FX1Poly.Polygraph.kCapBoundaryRead_atLeftLeg
#assert_no_axioms FX1Poly.Polygraph.kCapBoundaryRead_belowWindow
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupKFoldBoundaryRead

end FX1PolyAudit
