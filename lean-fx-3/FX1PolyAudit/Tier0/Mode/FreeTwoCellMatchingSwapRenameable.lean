import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.FreeTwoCellMatchingSwapRenameable

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellMatchingSwapRenameable — zero-axiom gate (matching keystone, LIVE route)

Per-declaration zero-axiom gate for the matching-carrier count-FREE step-simulation route: the cap projection
read-offs, `nextFresh` monotonicity, the union-find forest preservation, the open-wire / root-automorphism / loop
step-preservation, the `MatchingStepSim` invariant + fold + `MatchingRenameRel` read-off, the suffix-peel + the
core obligation + the pointwise parent reduction, and the right-context-irrelevance foundation.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the parent does the unified registration). -/

namespace FX1PolyAudit

-- cap projection read-offs + nextFresh
#assert_no_axioms FX1Poly.Tier0.stepCap_nextFresh
#assert_no_axioms FX1Poly.Tier0.stepCap_openWires
#assert_no_axioms FX1Poly.Tier0.stepCap_links
#assert_no_axioms FX1Poly.Tier0.stepCap_loops
#assert_no_axioms FX1Poly.Tier0.stepAtom_nextFresh_le
#assert_no_axioms FX1Poly.Tier0.processSpine_nextFresh_le
#assert_no_axioms FX1Poly.Tier0.runMatchingCell_nextFresh_le
#assert_no_axioms FX1Poly.Tier0.stepAtom_nextFresh_eq

-- the block widths (fresh-count) + the core swap's nfEq field
#assert_no_axioms FX1Poly.Tier0.stepAtom_nextFresh
#assert_no_axioms FX1Poly.Tier0.atomsFreshTotal
#assert_no_axioms FX1Poly.Tier0.processSpine_nextFresh
#assert_no_axioms FX1Poly.Tier0.cellFreshCount
#assert_no_axioms FX1Poly.Tier0.atomsFreshTotal_spineDiff
#assert_no_axioms FX1Poly.Tier0.runMatchingCell_nextFresh
#assert_no_axioms FX1Poly.Tier0.matchingCoreSwap_nextFresh_eq

-- forest invariant
#assert_no_axioms FX1Poly.Tier0.isUnionFindForest_stepCup
#assert_no_axioms FX1Poly.Tier0.isUnionFindForest_stepCap
#assert_no_axioms FX1Poly.Tier0.isUnionFindForest_stepAtom
#assert_no_axioms FX1Poly.Tier0.isUnionFindForest_processSpine
#assert_no_axioms FX1Poly.Tier0.isUnionFindForest_runMatchingCell

-- freshness invariant (the locality anchor + soundness re-gating ingredient)
#assert_no_axioms FX1Poly.Tier0.WireStateFresh
#assert_no_axioms FX1Poly.Tier0.wireStateFresh_initial
#assert_no_axioms FX1Poly.Tier0.stepCup_wireStateFresh
#assert_no_axioms FX1Poly.Tier0.stepCap_wireStateFresh
#assert_no_axioms FX1Poly.Tier0.stepAtom_wireStateFresh
#assert_no_axioms FX1Poly.Tier0.processSpine_wireStateFresh
#assert_no_axioms FX1Poly.Tier0.runMatchingCell_wireStateFresh

-- step-preservation of the simulation fields
#assert_no_axioms FX1Poly.Tier0.stepAtom_openWires_map
#assert_no_axioms FX1Poly.Tier0.stepCup_rootComm
#assert_no_axioms FX1Poly.Tier0.stepCap_rootComm
#assert_no_axioms FX1Poly.Tier0.stepAtom_rootComm
#assert_no_axioms FX1Poly.Tier0.stepAtom_loopsEq

-- the simulation invariant + fold + readoff + suffix-peel + core reduction
#assert_no_axioms FX1Poly.Tier0.MatchingStepSim
#assert_no_axioms FX1Poly.Tier0.matchingStepSim_step
#assert_no_axioms FX1Poly.Tier0.matchingStepSim_processSpine
#assert_no_axioms FX1Poly.Tier0.matchingStepSim_runMatchingCell
#assert_no_axioms FX1Poly.Tier0.matchingRenameRel_of_matchingStepSim
#assert_no_axioms FX1Poly.Tier0.matchingRenameRel_full_of_coreSim
#assert_no_axioms FX1Poly.Tier0.MatchingGodementCoreSwapSim
#assert_no_axioms FX1Poly.Tier0.matchingGodementSwapRenameable_pointwise_of_coreSim

-- right-context-irrelevance
#assert_no_axioms FX1Poly.Tier0.stepAtom_congr
#assert_no_axioms FX1Poly.Tier0.processSpine_rightAcc_irrel
#assert_no_axioms FX1Poly.Tier0.runMatchingCell_rightAcc_irrel

-- honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMatchingFoldForestInvariant
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMatchingStepSimInvariant
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMatchingRenameRelSuffixPeel
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMatchingRightContextIrrelevance
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMatchingFoldFreshnessInvariant
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMatchingBlockWidthCount
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMatchingCoreSwapSimProof

end FX1PolyAudit
