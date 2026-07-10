import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Steiner.DecideFreeConv

/-! # FX1PolyAudit/Polygraph/Omega/Steiner/DecideFreeConv — zero-axiom gate (OMEGA-2 B5)

Per-declaration `#assert_no_axioms` on the sound semi-decider (`decideFreeConvSound`,
`not_conv_of_linearize_ne`), the demo computad / valuation / dimension-3 cell tower, and the
non-vacuity facts (a dim-3 table, two conv-related equal-table cells via an actual derivation, two
non-conv distinct-table cells).  Every declaration must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.decideFreeConvSound
#assert_no_axioms FX1Poly.Polygraph.Omega.not_conv_of_linearize_ne
#assert_no_axioms FX1Poly.Polygraph.Omega.steinerDemoComputad
#assert_no_axioms FX1Poly.Polygraph.Omega.demoValuation
#assert_no_axioms FX1Poly.Polygraph.Omega.demoZeroCell
#assert_no_axioms FX1Poly.Polygraph.Omega.demoOneCell
#assert_no_axioms FX1Poly.Polygraph.Omega.demoTwoCell
#assert_no_axioms FX1Poly.Polygraph.Omega.cellThreeA
#assert_no_axioms FX1Poly.Polygraph.Omega.cellThreeB
#assert_no_axioms FX1Poly.Polygraph.Omega.demo_linearize_cellThreeA
#assert_no_axioms FX1Poly.Polygraph.Omega.demo_linearize_cellThreeB
#assert_no_axioms FX1Poly.Polygraph.Omega.demo_conv_tables_equal
#assert_no_axioms FX1Poly.Polygraph.Omega.demo_distinct_tables
#assert_no_axioms FX1Poly.Polygraph.Omega.demo_cellsThree_not_conv

end FX1PolyAudit
