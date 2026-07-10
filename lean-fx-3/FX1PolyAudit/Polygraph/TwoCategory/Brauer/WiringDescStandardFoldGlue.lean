import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardFoldGlue

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescStandardFoldGlue — zero-axiom gate (BRAUER-MIDDLE r5,
R3-A-CROSSING-GLUE: the six-phase split assembly + composed cap/cup phase-fold connectivity)

Per-declaration zero-axiom gate for the six-phase glue machinery: the fold-level forest preservation
(`processBrauer_links_isUnionFindForest`), the six-phase `processBrauer_append` split (`standardFormFold_appendSplit`),
the composed cap/interior-cup phase fold (`capThenCupFold_connects`) and its survival past a trailing word
(`capThenCupFold_connects_survivesTail`), the mixed-word non-vacuity, and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.processBrauer_links_isUnionFindForest
#assert_no_axioms FX1Poly.Polygraph.standardFormFold_appendSplit
#assert_no_axioms FX1Poly.Polygraph.capThenCupFold_connects
#assert_no_axioms FX1Poly.Polygraph.capThenCupFold_connects_survivesTail
#assert_no_axioms FX1Poly.Polygraph.capThenCupFold_connects_mixed
#assert_no_axioms FX1Poly.Polygraph.capThenCupFold_mixedWord_diagram
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasSixPhaseGlue
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasSixPhaseGlueRoundtrip

end FX1PolyAudit
