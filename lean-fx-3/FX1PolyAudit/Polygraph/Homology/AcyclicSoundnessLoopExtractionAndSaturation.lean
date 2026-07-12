import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.AcyclicSoundnessLoopExtractionAndSaturation

/-! # FX1PolyAudit/Polygraph/Homology/AcyclicSoundnessLoopExtractionAndSaturation — zero-axiom gate (the
    checker-soundness core: residuals (ii) checker saturation + (iii) longest-path loop extraction)

Per-declaration zero-axiom gate for TOWER-ANICK r13 (#2144): the hand-rolled `Bool` splitters and
`natListContains`/`List.append` laws, the multi-obstruction guard prefix/suffix lemmas, the reachability
bridges, the SATURATION core (`walkReachesLast`, `reachableWithinMonotone`, `loopImpliesReachesItself`,
`reachesItselfImpliesCheckerFalse`, `shortSimpleLoopImpliesCheckerFalse`), the EXTRACTION
(`splitAtFirst`, `scanForRepeat`, `scanForRepeatSpec`, `extractFirstRepeatLoop`), the headline
`closedEdgeWalkImpliesCheckerFalse`, the end-to-end witness, and the ledger marker.

The `#assert_no_axioms` macro is fuel-based (`DependencyAudit`); as an INDEPENDENT cross-check the
load-bearing decls are ALSO checked with the core `#print axioms` command (which does not truncate) —
each must report "does not depend on any axioms".

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Hand-rolled Bool splitters (never Bool.and_eq_true / Bool.or_eq_true, both leak propext)
#assert_no_axioms FX1Poly.Polygraph.Homology.boolAndElimLeft
#assert_no_axioms FX1Poly.Polygraph.Homology.boolAndElimRight
#assert_no_axioms FX1Poly.Polygraph.Homology.boolAndIntro
#assert_no_axioms FX1Poly.Polygraph.Homology.boolOrLeftFalse
#assert_no_axioms FX1Poly.Polygraph.Homology.boolOrElim
#assert_no_axioms FX1Poly.Polygraph.Homology.boolOrFalseElimLeft
#assert_no_axioms FX1Poly.Polygraph.Homology.boolOrFalseElimRight

-- natListContains over ++
#assert_no_axioms FX1Poly.Polygraph.Homology.natListContainsAppendLeft
#assert_no_axioms FX1Poly.Polygraph.Homology.natListContainsAppendRight
#assert_no_axioms FX1Poly.Polygraph.Homology.natListContainsAppendCases
#assert_no_axioms FX1Poly.Polygraph.Homology.natListContainsAppendFalse

-- the multi-obstruction guard over ++
#assert_no_axioms FX1Poly.Polygraph.Homology.guardTailStep
#assert_no_axioms FX1Poly.Polygraph.Homology.guardFirstPair
#assert_no_axioms FX1Poly.Polygraph.Homology.guardDropPrefix
#assert_no_axioms FX1Poly.Polygraph.Homology.guardTakePrefix

-- obstruction-pair bridges + frontier step
#assert_no_axioms FX1Poly.Polygraph.Homology.obstructionPairImpliesOutNeighbour
#assert_no_axioms FX1Poly.Polygraph.Homology.obstructionPairImpliesSource
#assert_no_axioms FX1Poly.Polygraph.Homology.outNeighbourInFrontierStep

-- SATURATION core
#assert_no_axioms FX1Poly.Polygraph.Homology.lastVertex
#assert_no_axioms FX1Poly.Polygraph.Homology.lastVertexSnoc
#assert_no_axioms FX1Poly.Polygraph.Homology.reachableStepMonotone
#assert_no_axioms FX1Poly.Polygraph.Homology.reachableWithinMonotone
#assert_no_axioms FX1Poly.Polygraph.Homology.walkReachesLast
#assert_no_axioms FX1Poly.Polygraph.Homology.edgeWalkReachesEnd
#assert_no_axioms FX1Poly.Polygraph.Homology.lengthAppendSingleton
#assert_no_axioms FX1Poly.Polygraph.Homology.loopImpliesReachesItself
#assert_no_axioms FX1Poly.Polygraph.Homology.anyContainsReaches
#assert_no_axioms FX1Poly.Polygraph.Homology.reachesItselfImpliesCheckerFalse
#assert_no_axioms FX1Poly.Polygraph.Homology.loopIsShort
#assert_no_axioms FX1Poly.Polygraph.Homology.loopSourceIsEdgeSource
#assert_no_axioms FX1Poly.Polygraph.Homology.shortSimpleLoopImpliesCheckerFalse

-- EXTRACTION (list laws + the first-repeat scan + its correctness)
#assert_no_axioms FX1Poly.Polygraph.Homology.appendNil
#assert_no_axioms FX1Poly.Polygraph.Homology.appendAssoc
#assert_no_axioms FX1Poly.Polygraph.Homology.memAppendRight
#assert_no_axioms FX1Poly.Polygraph.Homology.hasRepeatedVertexSuffix
#assert_no_axioms FX1Poly.Polygraph.Homology.distinctAppendFresh
#assert_no_axioms FX1Poly.Polygraph.Homology.splitAtFirst
#assert_no_axioms FX1Poly.Polygraph.Homology.splitAtFirstSome
#assert_no_axioms FX1Poly.Polygraph.Homology.splitAtFirstNoneImpliesNotContains
#assert_no_axioms FX1Poly.Polygraph.Homology.loopInfixReshape
#assert_no_axioms FX1Poly.Polygraph.Homology.scanForRepeat
#assert_no_axioms FX1Poly.Polygraph.Homology.extractFirstRepeatLoop
#assert_no_axioms FX1Poly.Polygraph.Homology.scanFound
#assert_no_axioms FX1Poly.Polygraph.Homology.scanCont
#assert_no_axioms FX1Poly.Polygraph.Homology.scanForRepeatSpec

-- the headline + witnesses + ledger marker
#assert_no_axioms FX1Poly.Polygraph.Homology.closedEdgeWalkImpliesCheckerFalse
#assert_no_axioms FX1Poly.Polygraph.Homology.extractFirstRepeatLoopSmoke
#assert_no_axioms FX1Poly.Polygraph.Homology.detectionFuelBoundarySmoke
#assert_no_axioms FX1Poly.Polygraph.Homology.reachabilityLayerSmoke
#assert_no_axioms FX1Poly.Polygraph.Homology.threeCycleClosedWalkRefutesAcyclicity
#assert_no_axioms FX1Poly.Polygraph.Homology.acyclicSoundnessLoopExtractionAndSaturationIsComplete

/-! ### Independent `#print axioms` cross-check for the load-bearing decls (not trusting the fuel-based
    macro alone) — each must report "does not depend on any axioms". -/

#print axioms FX1Poly.Polygraph.Homology.closedEdgeWalkImpliesCheckerFalse
#print axioms FX1Poly.Polygraph.Homology.scanForRepeatSpec
#print axioms FX1Poly.Polygraph.Homology.walkReachesLast
#print axioms FX1Poly.Polygraph.Homology.shortSimpleLoopImpliesCheckerFalse
#print axioms FX1Poly.Polygraph.Homology.threeCycleClosedWalkRefutesAcyclicity

end FX1PolyAudit
