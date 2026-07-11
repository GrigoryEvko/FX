import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCapReconstruct

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringValleyCapReconstruct — zero-axiom gate
(FC-3 r32, B4: the cap-side `DiagramType.ext` reconstruction + the cap-block splitter)

Per-declaration zero-axiom gate for the string cap-side restriction over the walking ADJOINT-TRIPLE signature: the
five newly-cloned keyed substrate lemmas (loops split / cup-unlinked preservation / bottom-bottom component frame /
append arity discipline), the two copied-field legs, the four partner legs (survivor-bottom keystone, cap-consumed,
survivor-membership routing, cap-top), the full `DiagramType.ext` `stringCapRestrict_reconstructs`, the cap-block
splitter `stringSameWholeMatching_capBlockMatchingEq`, and the wide (`bottomCount = 4`, mid-width `2`) + mid-zero
(`bottomCount = 2`) truth-probe firings with their arity/chain witnesses.  The private range/map/`Nat.blt`
plumbing (`getAtMemOfLtSVCR`, `rangeLoopLengthSVCR`, …, `neTrueOfEqFalseSVCR`) is covered transitively — any leaked
axiom would surface in the public capstones' `#print axioms` below.  Every declaration must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  The project `#assert_no_axioms` macro is fuel-based;
the independent `#print axioms` lines below are the trusted cross-check. -/

namespace FX1PolyAudit

-- the five new keyed substrate clones
#assert_no_axioms FX1Poly.Polygraph.stringProcessSpine_loops_ofAllCupArity
#assert_no_axioms FX1Poly.Polygraph.stringMatchingOf_loops_split
#assert_no_axioms FX1Poly.Polygraph.stringProcessSpine_preservesArcNodeUnlinked_ofAllCupArity
#assert_no_axioms FX1Poly.Polygraph.stringProcessSpine_isSameComponent_bottom_ofAllCupArity
#assert_no_axioms FX1Poly.Polygraph.stringSpineHasCupCapAtoms_ofAllCapArity
#assert_no_axioms FX1Poly.Polygraph.stringSpineHasCupCapAtoms_append

-- the two copied-field legs
#assert_no_axioms FX1Poly.Polygraph.stringCapRestrict_bottomCount_eq
#assert_no_axioms FX1Poly.Polygraph.stringCapRestrict_loops_eq

-- the four partner legs
#assert_no_axioms FX1Poly.Polygraph.stringCapRestrict_partner_survivorBottom
#assert_no_axioms FX1Poly.Polygraph.stringCapConsumed_partner_agree
#assert_no_axioms FX1Poly.Polygraph.stringBottomSurvivor_of_partnerAbove
#assert_no_axioms FX1Poly.Polygraph.stringCapRestrict_partner_capTop

-- the full ext + the cap-block splitter
#assert_no_axioms FX1Poly.Polygraph.stringCapRestrict_reconstructs
#assert_no_axioms FX1Poly.Polygraph.stringSameWholeMatching_capBlockMatchingEq

-- the wide (non-degenerate, mid-width 2) truth-probe: arity/chain witnesses + ext + reflexive splitter fire
#assert_no_axioms FX1Poly.Polygraph.stringWideProbeCapBlock_pureCap
#assert_no_axioms FX1Poly.Polygraph.stringWideProbeCupBlock_pureCup
#assert_no_axioms FX1Poly.Polygraph.stringWideProbeCupBlock_chained
#assert_no_axioms FX1Poly.Polygraph.stringCapRestrict_reconstructs_firesOnWideValley
#assert_no_axioms FX1Poly.Polygraph.stringSameWholeMatching_capBlockMatchingEq_firesOnWideValley

-- the mid-zero smoke probe: arity/chain witnesses + ext fire
#assert_no_axioms FX1Poly.Polygraph.stringMidZeroProbeCapBlock_pureCap
#assert_no_axioms FX1Poly.Polygraph.stringMidZeroProbeCupBlock_pureCup
#assert_no_axioms FX1Poly.Polygraph.stringMidZeroProbeCupBlock_chained
#assert_no_axioms FX1Poly.Polygraph.stringCapRestrict_reconstructs_firesOnMidZeroValley

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCapRestrictReconstructs

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringProcessSpine_loops_ofAllCupArity
#print axioms FX1Poly.Polygraph.stringMatchingOf_loops_split
#print axioms FX1Poly.Polygraph.stringProcessSpine_preservesArcNodeUnlinked_ofAllCupArity
#print axioms FX1Poly.Polygraph.stringProcessSpine_isSameComponent_bottom_ofAllCupArity
#print axioms FX1Poly.Polygraph.stringSpineHasCupCapAtoms_ofAllCapArity
#print axioms FX1Poly.Polygraph.stringSpineHasCupCapAtoms_append
#print axioms FX1Poly.Polygraph.stringCapRestrict_bottomCount_eq
#print axioms FX1Poly.Polygraph.stringCapRestrict_loops_eq
#print axioms FX1Poly.Polygraph.stringCapRestrict_partner_survivorBottom
#print axioms FX1Poly.Polygraph.stringCapConsumed_partner_agree
#print axioms FX1Poly.Polygraph.stringBottomSurvivor_of_partnerAbove
#print axioms FX1Poly.Polygraph.stringCapRestrict_partner_capTop
#print axioms FX1Poly.Polygraph.stringCapRestrict_reconstructs
#print axioms FX1Poly.Polygraph.stringSameWholeMatching_capBlockMatchingEq
#print axioms FX1Poly.Polygraph.stringWideProbeCapBlock_pureCap
#print axioms FX1Poly.Polygraph.stringWideProbeCupBlock_pureCup
#print axioms FX1Poly.Polygraph.stringWideProbeCupBlock_chained
#print axioms FX1Poly.Polygraph.stringCapRestrict_reconstructs_firesOnWideValley
#print axioms FX1Poly.Polygraph.stringSameWholeMatching_capBlockMatchingEq_firesOnWideValley
#print axioms FX1Poly.Polygraph.stringMidZeroProbeCapBlock_pureCap
#print axioms FX1Poly.Polygraph.stringMidZeroProbeCupBlock_pureCup
#print axioms FX1Poly.Polygraph.stringMidZeroProbeCupBlock_chained
#print axioms FX1Poly.Polygraph.stringCapRestrict_reconstructs_firesOnMidZeroValley
#print axioms FX1Poly.Polygraph.fxString_hasCapRestrictReconstructs

end FX1PolyAudit
