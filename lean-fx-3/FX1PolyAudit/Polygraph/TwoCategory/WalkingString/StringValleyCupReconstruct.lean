import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCupReconstruct

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringValleyCupReconstruct — zero-axiom gate
(FC-3 r33, B5: the cup-side DiagramType.ext gated on case 3 + the cup-block splitter)

Per-declaration zero-axiom gate for the string cup-side reconstruction over the walking ADJOINT-TRIPLE signature:
the open-wire-length congruence, the three cup-field agreements, the GATED cup-side `DiagramType.ext`
`stringCupRestrict_reconstructs`, the UNCONDITIONAL cup-block splitter `stringSameWholeMatching_cupBlockMatchingEq`,
and the three field truth-probe firings on the wide (mid-width `2`) valley.  The private range/map/`Nat.blt`
plumbing (`rangeLoopLenSCUR`, …, `neTrueOfEqFalseSCUR`) is covered transitively.  Every declaration must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  The project `#assert_no_axioms` macro is
fuel-based; the independent `#print axioms` lines below are the trusted cross-check. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringProcessSpine_openWiresLength_congr_ofAllCupArity
#assert_no_axioms FX1Poly.Polygraph.stringCupRestrict_loops_eq
#assert_no_axioms FX1Poly.Polygraph.stringCupRestrict_bottomCount_eq
#assert_no_axioms FX1Poly.Polygraph.stringCupRestrict_topCount_eq
#assert_no_axioms FX1Poly.Polygraph.stringCupRestrict_reconstructs
#assert_no_axioms FX1Poly.Polygraph.stringSameWholeMatching_cupBlockMatchingEq
#assert_no_axioms FX1Poly.Polygraph.stringCupRestrict_bottomCount_eq_firesOnWideValley
#assert_no_axioms FX1Poly.Polygraph.stringCupRestrict_topCount_eq_firesOnWideValley
#assert_no_axioms FX1Poly.Polygraph.stringCupRestrict_loops_eq_firesOnWideValley
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCupRestrictReconstructsGatedOnCupTopTop

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringProcessSpine_openWiresLength_congr_ofAllCupArity
#print axioms FX1Poly.Polygraph.stringCupRestrict_loops_eq
#print axioms FX1Poly.Polygraph.stringCupRestrict_bottomCount_eq
#print axioms FX1Poly.Polygraph.stringCupRestrict_topCount_eq
#print axioms FX1Poly.Polygraph.stringCupRestrict_reconstructs
#print axioms FX1Poly.Polygraph.stringSameWholeMatching_cupBlockMatchingEq
#print axioms FX1Poly.Polygraph.stringCupRestrict_bottomCount_eq_firesOnWideValley
#print axioms FX1Poly.Polygraph.stringCupRestrict_topCount_eq_firesOnWideValley
#print axioms FX1Poly.Polygraph.stringCupRestrict_loops_eq_firesOnWideValley
#print axioms FX1Poly.Polygraph.fxString_hasCupRestrictReconstructsGatedOnCupTopTop

end FX1PolyAudit
