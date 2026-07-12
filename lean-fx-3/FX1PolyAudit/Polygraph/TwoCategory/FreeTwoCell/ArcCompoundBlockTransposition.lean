import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCompoundBlockTransposition

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcCompoundBlockTransposition — zero-axiom gate (MODE-COMMUTE r22)

Per-declaration zero-axiom gate for the COMPOUND fresh-block transposition at symbolic cell
widths: the carrier reconciliation, the compound sigma, its four UF-automorphism obligations
(fixesZero / fixesBelow / fixesAbove / leftInverse / injective), the two renaming-commutation
cruxes (root-commutation + component-preservation), the consumer-shaped below-base fixing bridge,
the two firing probes, the marker, and the r23-open honesty pin.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.blockRotate_eq_arcFreshBlockTransposition
#assert_no_axioms FX1Poly.Polygraph.compoundFreshBlockTransposition
#assert_no_axioms FX1Poly.Polygraph.compoundFreshBlockTransposition_fixesZero
#assert_no_axioms FX1Poly.Polygraph.compoundFreshBlockTransposition_fixesBelow
#assert_no_axioms FX1Poly.Polygraph.compoundFreshBlockTransposition_fixesAbove
#assert_no_axioms FX1Poly.Polygraph.compoundFreshBlockTransposition_leftInverse
#assert_no_axioms FX1Poly.Polygraph.compoundFreshBlockTransposition_injective
#assert_no_axioms FX1Poly.Polygraph.unionFindRootOf_compoundTransposition
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_compoundTransposition
#assert_no_axioms FX1Poly.Polygraph.renameLinks_compoundTransposition_ofBelow
#assert_no_axioms FX1Poly.Polygraph.compoundFreshBlockTransposition_shapes_probe
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_compoundTransposition_probe
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCompoundFreshBlockTransposition
#assert_no_axioms FX1Poly.Polygraph.arcCompoundBlockTransposition_blockSwapCore_stays_open

end FX1PolyAudit
