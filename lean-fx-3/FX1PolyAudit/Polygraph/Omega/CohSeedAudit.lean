import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.CohSeed

/-! # FX1PolyAudit.Polygraph.Omega.CohSeedAudit — zero-axiom gate for the CaTT coherence-rule seed
(OMEGA-6 r1, B2).

Per-declaration `#assert_no_axioms` on the coherence-generator fire (`cohGenerator`), its boundary read-offs
and row-generation seed (`cohGenerator_boundarySource` / `_boundaryTarget` / `_fills`), the free globularity
(`cohGenerator_isGlobularCell`), and the two non-vacuity coherence generators (the single-2-cell disk and the
interchange coherence, with their boundary-filling / distinctness / globularity witnesses). -/

namespace FX1PolyAudit

-- CohSeed.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.cohGenerator
#assert_no_axioms FX1Poly.Polygraph.Omega.cohGenerator_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.cohGenerator_boundaryTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.cohGenerator_fills
#assert_no_axioms FX1Poly.Polygraph.Omega.cohGenerator_isGlobularCell
#assert_no_axioms FX1Poly.Polygraph.Omega.oneCellId_isGlobularCell
#assert_no_axioms FX1Poly.Polygraph.Omega.twoGlobeCohRow
#assert_no_axioms FX1Poly.Polygraph.Omega.twoGlobeCohGenerator
#assert_no_axioms FX1Poly.Polygraph.Omega.twoGlobeCohGenerator_fills
#assert_no_axioms FX1Poly.Polygraph.Omega.twoGlobeCohGenerator_isGlobular
#assert_no_axioms FX1Poly.Polygraph.Omega.interchangeCohRow
#assert_no_axioms FX1Poly.Polygraph.Omega.interchangeCohGenerator
#assert_no_axioms FX1Poly.Polygraph.Omega.interchangeCohGenerator_fills
#assert_no_axioms FX1Poly.Polygraph.Omega.interchangeCohGenerator_boundariesDistinct

end FX1PolyAudit
