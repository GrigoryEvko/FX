import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcBoundaryCensusPerfectMatchingFold

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcBoundaryCensusPerfectMatchingFold — zero-axiom gate
(FC-3 r30, B1: the arc-engine census + perfect-matching fold transport)

Per-declaration zero-axiom gate for the string arc-engine boundary-census and token-frame perfect-matching fold
transport over the walking ADJOINT-TRIPLE signature: the per-atom census / perfect-matching steps, the whole-fold
transports, the canonical-seed capstones, the wide (`bottomCount = 4`, mid-width `2`) and mid-zero
(`bottomCount = 2`) truth-probes, and the `decide` mid-width cross-check.  Every declaration must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  The project `#assert_no_axioms` macro is
fuel-based; the independent `#print axioms` lines below are the trusted cross-check. -/

namespace FX1PolyAudit

-- the per-atom census step + whole-fold transport + canonical-seed capstone
#assert_no_axioms FX1Poly.Polygraph.stringArcBoundaryCensus_stepArcAtom
#assert_no_axioms FX1Poly.Polygraph.stringArcBoundaryCensus_processArcSpine_ofChained
#assert_no_axioms FX1Poly.Polygraph.stringArcBoundaryCensus_ofChainedSpineList

-- the per-atom perfect-matching step + whole-fold transport + canonical-seed capstone
#assert_no_axioms FX1Poly.Polygraph.stringArcPerfectMatchingTokens_stepArcAtom
#assert_no_axioms FX1Poly.Polygraph.stringArcPerfectMatchingTokens_processArcSpine_ofChained
#assert_no_axioms FX1Poly.Polygraph.stringArcPerfectMatchingTokens_ofChainedSpineList

-- the wide (non-degenerate, mid-width 2) truth-probe atoms + chaining + decide cross-check + capstone firings
#assert_no_axioms FX1Poly.Polygraph.stringWideProbeCapAtom
#assert_no_axioms FX1Poly.Polygraph.stringWideProbeCupAtom
#assert_no_axioms FX1Poly.Polygraph.stringWideProbeValley_chained
#assert_no_axioms FX1Poly.Polygraph.stringWideProbe_midWidth_isTwo
#assert_no_axioms FX1Poly.Polygraph.stringArcBoundaryCensus_firesOnWideValley
#assert_no_axioms FX1Poly.Polygraph.stringArcPerfectMatchingTokens_firesOnWideValley

-- the mid-zero smoke probe (chaining + capstone firings)
#assert_no_axioms FX1Poly.Polygraph.stringMidZeroProbeValley_chained
#assert_no_axioms FX1Poly.Polygraph.stringArcBoundaryCensus_firesOnMidZeroValley
#assert_no_axioms FX1Poly.Polygraph.stringArcPerfectMatchingTokens_firesOnMidZeroValley

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcCensusPerfectMatchingFold

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringArcBoundaryCensus_stepArcAtom
#print axioms FX1Poly.Polygraph.stringArcBoundaryCensus_processArcSpine_ofChained
#print axioms FX1Poly.Polygraph.stringArcBoundaryCensus_ofChainedSpineList
#print axioms FX1Poly.Polygraph.stringArcPerfectMatchingTokens_stepArcAtom
#print axioms FX1Poly.Polygraph.stringArcPerfectMatchingTokens_processArcSpine_ofChained
#print axioms FX1Poly.Polygraph.stringArcPerfectMatchingTokens_ofChainedSpineList
#print axioms FX1Poly.Polygraph.stringWideProbeCapAtom
#print axioms FX1Poly.Polygraph.stringWideProbeCupAtom
#print axioms FX1Poly.Polygraph.stringWideProbeValley_chained
#print axioms FX1Poly.Polygraph.stringWideProbe_midWidth_isTwo
#print axioms FX1Poly.Polygraph.stringArcBoundaryCensus_firesOnWideValley
#print axioms FX1Poly.Polygraph.stringArcPerfectMatchingTokens_firesOnWideValley
#print axioms FX1Poly.Polygraph.stringMidZeroProbeValley_chained
#print axioms FX1Poly.Polygraph.stringArcBoundaryCensus_firesOnMidZeroValley
#print axioms FX1Poly.Polygraph.stringArcPerfectMatchingTokens_firesOnMidZeroValley
#print axioms FX1Poly.Polygraph.fxString_hasArcCensusPerfectMatchingFold

end FX1PolyAudit
