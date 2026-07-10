import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcExtractorRec

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescArcExtractorRec — zero-axiom gate (BRAUER-MIDDLE r3, B1)

Per-declaration zero-axiom gate for the inversion-CORRECTED arc extractor: the corrected reconstructor + guarded
readback + soundness, the nested/triple-nested `some`-readback + realization witnesses, the r2-flat `none`
regression pins, the no-regression bundle, the bounded totality bundle, and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.permInverse
#assert_no_axioms FX1Poly.Polygraph.reconstructStandardFormExt5Corrected
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExtCorrected
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExtCorrected_sound
#assert_no_axioms FX1Poly.Polygraph.nestedCupsDiagram
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExt_nestedCups_none
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExtCorrected_nestedCups_some
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExtCorrected_nestedCups_realizes
#assert_no_axioms FX1Poly.Polygraph.tripleNestedCupsDiagram
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExtCorrected_tripleNested_some
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExt_tripleNested_none
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExtCorrected_adversarialB_some
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExtCorrected_straddle_some
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExtCorrected_parallelCups_some
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExtCorrected_crossingCap_some
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExtCorrected_boundedTotality
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasExt5CorrectedNestedReadback
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasExt5CorrectedRoundtripProof

end FX1PolyAudit
