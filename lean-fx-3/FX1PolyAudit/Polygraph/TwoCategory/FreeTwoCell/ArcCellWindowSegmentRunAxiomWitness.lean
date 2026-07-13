import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCellWindowSegmentRun

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcCellWindowSegmentRunAxiomWitness — independent #print axioms (MODE-COMMUTE r28)

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the r28
whole-cell segment-run engine.  Each must print "does not depend on any axioms".  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.natListAppendAssoc
#print axioms FX1Poly.Polygraph.natListGetAt_appendBelow
#print axioms FX1Poly.Polygraph.natListGetAt_appendAtLength
#print axioms FX1Poly.Polygraph.natListMem_appendOfLeft
#print axioms FX1Poly.Polygraph.natListMem_appendOfRight
#print axioms FX1Poly.Polygraph.natListMem_appendElim
#print axioms FX1Poly.Polygraph.natListEqNilOfLengthZero
#print axioms FX1Poly.Polygraph.natListEqPairOfLengthTwo
#print axioms FX1Poly.Polygraph.natListSplitAtLength
#print axioms FX1Poly.Polygraph.natAddRightCancelSeg
#print axioms FX1Poly.Polygraph.natAddLeftCancelSeg
#print axioms FX1Poly.Polygraph.boolBothTrueOfAndTrue
#print axioms FX1Poly.Polygraph.boolEitherTrueOfOrTrue
#print axioms FX1Poly.Polygraph.RawTwoCellExpr.isTurnbackOnly
#print axioms FX1Poly.Polygraph.arcProbeDisjointFromSegment
#print axioms FX1Poly.Polygraph.arcCellSegmentRun_ofWellFormed
#print axioms FX1Poly.Polygraph.leftOnlyPath
#print axioms FX1Poly.Polygraph.rightOnlyPath
#print axioms FX1Poly.Polygraph.whiskerShiftedUnitCell
#print axioms FX1Poly.Polygraph.whiskerSandwichedCounitCell
#print axioms FX1Poly.Polygraph.threeAtomTurnbackCell
#print axioms FX1Poly.Polygraph.threeAtomTurnbackCell_isTurnbackOnly
#print axioms FX1Poly.Polygraph.arcSegmentFireSeedState
#print axioms FX1Poly.Polygraph.arcSegmentFireSeedState_isWellFormed
#print axioms FX1Poly.Polygraph.arcSegmentRun_firedOnThreeAtomCell
#print axioms FX1Poly.Polygraph.arcSegmentRun_threeAtomCell_openWires
#print axioms FX1Poly.Polygraph.arcSegmentRun_threeAtomCell_probeRootStable
#print axioms FX1Poly.Polygraph.arcSegmentRun_threeAtomCell_probeDisjoint
#print axioms FX1Poly.Polygraph.fxMode_hasArcCellSegmentRunInvariant
#print axioms FX1Poly.Polygraph.arcCellWindowSegmentRun_disjointWhiskerSupport_stays_false
#print axioms FX1Poly.Polygraph.arcCellWindowSegmentRun_swapRenameableProof2_stays_false
#print axioms FX1Poly.Polygraph.arcCellWindowSegmentRun_partitionCommute_stays_false
#print axioms FX1Poly.Polygraph.arcCellWindowSegmentRun_samePartitionFresh_stays_false

end FX1PolyAudit
