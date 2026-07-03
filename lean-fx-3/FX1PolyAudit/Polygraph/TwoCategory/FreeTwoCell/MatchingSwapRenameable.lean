import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingSwapRenameable

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.MatchingSwapRenameable — zero-axiom gate (matching keystone, LIVE route)

Per-declaration zero-axiom gate for the matching-carrier count-FREE step-simulation route: the cap projection
read-offs, `nextFresh` monotonicity, the union-find forest preservation, the open-wire / root-automorphism / loop
step-preservation, the `MatchingStepSim` invariant + fold + `MatchingRenameRel` read-off, the suffix-peel + the
core obligation + the pointwise parent reduction, and the right-context-irrelevance foundation.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the parent does the unified registration). -/

namespace FX1PolyAudit

-- cap projection read-offs + nextFresh
#assert_no_axioms FX1Poly.Polygraph.stepCap_nextFresh
#assert_no_axioms FX1Poly.Polygraph.stepCap_openWires
#assert_no_axioms FX1Poly.Polygraph.stepCap_links
#assert_no_axioms FX1Poly.Polygraph.stepCap_loops
#assert_no_axioms FX1Poly.Polygraph.stepAtom_nextFresh_le
#assert_no_axioms FX1Poly.Polygraph.processSpine_nextFresh_le
#assert_no_axioms FX1Poly.Polygraph.runMatchingCell_nextFresh_le
#assert_no_axioms FX1Poly.Polygraph.stepAtom_nextFresh_eq

-- the block widths (fresh-count) + the core swap's nfEq field
#assert_no_axioms FX1Poly.Polygraph.stepAtom_nextFresh
#assert_no_axioms FX1Poly.Polygraph.atomsFreshTotal
#assert_no_axioms FX1Poly.Polygraph.processSpine_nextFresh
#assert_no_axioms FX1Poly.Polygraph.cellFreshCount
#assert_no_axioms FX1Poly.Polygraph.atomsFreshTotal_spineDiff
#assert_no_axioms FX1Poly.Polygraph.runMatchingCell_nextFresh
#assert_no_axioms FX1Poly.Polygraph.matchingCoreSwap_nextFresh_eq

-- forest invariant
#assert_no_axioms FX1Poly.Polygraph.isUnionFindForest_stepCup
#assert_no_axioms FX1Poly.Polygraph.isUnionFindForest_stepCap
#assert_no_axioms FX1Poly.Polygraph.isUnionFindForest_stepAtom
#assert_no_axioms FX1Poly.Polygraph.isUnionFindForest_processSpine
#assert_no_axioms FX1Poly.Polygraph.isUnionFindForest_runMatchingCell

-- freshness invariant (the locality anchor + soundness re-gating ingredient)
#assert_no_axioms FX1Poly.Polygraph.WireStateFresh
#assert_no_axioms FX1Poly.Polygraph.wireStateFresh_initial
#assert_no_axioms FX1Poly.Polygraph.stepCup_wireStateFresh
#assert_no_axioms FX1Poly.Polygraph.stepCap_wireStateFresh
#assert_no_axioms FX1Poly.Polygraph.stepAtom_wireStateFresh
#assert_no_axioms FX1Poly.Polygraph.processSpine_wireStateFresh
#assert_no_axioms FX1Poly.Polygraph.runMatchingCell_wireStateFresh

-- step-preservation of the simulation fields
#assert_no_axioms FX1Poly.Polygraph.stepAtom_openWires_map
#assert_no_axioms FX1Poly.Polygraph.stepCup_rootComm
#assert_no_axioms FX1Poly.Polygraph.stepCap_rootComm
#assert_no_axioms FX1Poly.Polygraph.stepAtom_rootComm
#assert_no_axioms FX1Poly.Polygraph.stepAtom_loopsEq

-- the simulation invariant + fold + readoff + suffix-peel + core reduction
#assert_no_axioms FX1Poly.Polygraph.MatchingStepSim
#assert_no_axioms FX1Poly.Polygraph.matchingStepSim_step
#assert_no_axioms FX1Poly.Polygraph.matchingStepSim_processSpine
#assert_no_axioms FX1Poly.Polygraph.matchingStepSim_runMatchingCell
#assert_no_axioms FX1Poly.Polygraph.matchingRenameRel_of_matchingStepSim
#assert_no_axioms FX1Poly.Polygraph.matchingRenameRel_full_of_coreSim
#assert_no_axioms FX1Poly.Polygraph.MatchingGodementCoreSwapSim
#assert_no_axioms FX1Poly.Polygraph.matchingGodementSwapRenameable_pointwise_of_coreSim

-- right-context-irrelevance
#assert_no_axioms FX1Poly.Polygraph.stepAtom_congr
#assert_no_axioms FX1Poly.Polygraph.processSpine_rightAcc_irrel
#assert_no_axioms FX1Poly.Polygraph.runMatchingCell_rightAcc_irrel

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingFoldForestInvariant
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingStepSimInvariant
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingRenameRelSuffixPeel
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingRightContextIrrelevance
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingFoldFreshnessInvariant
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingBlockWidthCount
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingCoreSwapSimProof

end FX1PolyAudit
