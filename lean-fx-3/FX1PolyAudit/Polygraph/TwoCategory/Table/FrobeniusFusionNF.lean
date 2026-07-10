import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.FrobeniusFusionNF

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.FrobeniusFusionNF — zero-axiom gate for carrier-A spider fusion
to the connected canonical spider + the general-realization scaffolding (POLY-TAB r1 FROB-RESUME, B3).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.canonicalSpiderOf_mergeStep
#assert_no_axioms FX1Poly.Polygraph.canonicalSpiderOf_fanStep
#assert_no_axioms FX1Poly.Polygraph.canonicalSpiderOf_oneOne
#assert_no_axioms FX1Poly.Polygraph.canonicalSpiderOf_twoOne
#assert_no_axioms FX1Poly.Polygraph.canonicalSpiderOf_twoTwo
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_HCell_isCanonical
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_frobLeft_fusesToCanonical
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_frobRight_fusesToCanonical
#assert_no_axioms FX1Poly.Polygraph.frobeniusCells_fuseToOneSpider
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_idTCell_isStrand
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_unitLeft_fusesToStrand
#assert_no_axioms FX1Poly.Polygraph.fxTab_hasCarrierASpiderFusion
#assert_no_axioms FX1Poly.Polygraph.fxTab_hasGeneralAritySpiderRealization

end FX1PolyAudit
