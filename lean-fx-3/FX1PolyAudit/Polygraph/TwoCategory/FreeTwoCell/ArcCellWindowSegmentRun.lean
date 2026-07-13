import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCellWindowSegmentRun

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcCellWindowSegmentRun — zero-axiom gate (MODE-COMMUTE r28)

Per-declaration zero-axiom gate for the r28 whole-cell segment-run engine: the monomorphic
`List Nat` append kit, the Bool split helpers, the turnback-only cell class, the
component-disjointness guard, the master segment-run/invariant theorem, the three-atom fixture
fires, the shipped marker, and the four untouched-false honesty pins.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natListAppendAssoc
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_appendBelow
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_appendAtLength
#assert_no_axioms FX1Poly.Polygraph.natListMem_appendOfLeft
#assert_no_axioms FX1Poly.Polygraph.natListMem_appendOfRight
#assert_no_axioms FX1Poly.Polygraph.natListMem_appendElim
#assert_no_axioms FX1Poly.Polygraph.natListEqNilOfLengthZero
#assert_no_axioms FX1Poly.Polygraph.natListEqPairOfLengthTwo
#assert_no_axioms FX1Poly.Polygraph.natListSplitAtLength
#assert_no_axioms FX1Poly.Polygraph.natAddRightCancelSeg
#assert_no_axioms FX1Poly.Polygraph.natAddLeftCancelSeg
#assert_no_axioms FX1Poly.Polygraph.boolBothTrueOfAndTrue
#assert_no_axioms FX1Poly.Polygraph.boolEitherTrueOfOrTrue
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.isTurnbackOnly
#assert_no_axioms FX1Poly.Polygraph.arcProbeDisjointFromSegment
#assert_no_axioms FX1Poly.Polygraph.arcCellSegmentRun_ofWellFormed
#assert_no_axioms FX1Poly.Polygraph.leftOnlyPath
#assert_no_axioms FX1Poly.Polygraph.rightOnlyPath
#assert_no_axioms FX1Poly.Polygraph.whiskerShiftedUnitCell
#assert_no_axioms FX1Poly.Polygraph.whiskerSandwichedCounitCell
#assert_no_axioms FX1Poly.Polygraph.threeAtomTurnbackCell
#assert_no_axioms FX1Poly.Polygraph.threeAtomTurnbackCell_isTurnbackOnly
#assert_no_axioms FX1Poly.Polygraph.arcSegmentFireSeedState
#assert_no_axioms FX1Poly.Polygraph.arcSegmentFireSeedState_isWellFormed
#assert_no_axioms FX1Poly.Polygraph.arcSegmentRun_firedOnThreeAtomCell
#assert_no_axioms FX1Poly.Polygraph.arcSegmentRun_threeAtomCell_openWires
#assert_no_axioms FX1Poly.Polygraph.arcSegmentRun_threeAtomCell_probeRootStable
#assert_no_axioms FX1Poly.Polygraph.arcSegmentRun_threeAtomCell_probeDisjoint
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCellSegmentRunInvariant
#assert_no_axioms FX1Poly.Polygraph.arcCellWindowSegmentRun_disjointWhiskerSupport_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCellWindowSegmentRun_swapRenameableProof2_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCellWindowSegmentRun_partitionCommute_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCellWindowSegmentRun_samePartitionFresh_stays_false

end FX1PolyAudit
