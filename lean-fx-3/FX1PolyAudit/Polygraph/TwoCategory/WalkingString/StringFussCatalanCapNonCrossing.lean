import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanCapNonCrossing

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringFussCatalanCapNonCrossing — zero-axiom gate (FC-4, P1)

Per-declaration zero-axiom gate for the CAP non-crossing infrastructure + the LOOP-branch preservation: the de-drop
index map `capRemap` and its strict monotonicity, the new-index-reads-old-wire lemma, the loop-branch links-unchanged
fact, the loop-branch non-crossing preservation, and the three non-vacuity loop-freedom witnesses.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.capRemap_strictMono
#assert_no_axioms FX1Poly.Polygraph.stringStepCap_read_oldIndex
#assert_no_axioms FX1Poly.Polygraph.stringStepCap_links_loopBranch
#assert_no_axioms FX1Poly.Polygraph.stringNonCrossing_stepCap_loopBranch
#assert_no_axioms FX1Poly.Polygraph.stringUnitLower_loops_zero_viaReduction
#assert_no_axioms FX1Poly.Polygraph.stringCrossLevelCell_loops_zero_viaReductionN
#assert_no_axioms FX1Poly.Polygraph.stringSnakeF_loops_zero_viaReduction

end FX1PolyAudit
