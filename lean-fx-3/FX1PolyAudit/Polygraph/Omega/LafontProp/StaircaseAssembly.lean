import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.LafontProp.StaircaseAssembly

/-! # FX1PolyAudit.Polygraph.Omega.LafontProp.StaircaseAssembly — zero-axiom gate
(LAFONT-REPAIR stage 2 phase 5: THE ASSEMBLY — canonical completeness lands)

Per-declaration zero-axiom gate for the assembly file: the deep-cell matrix patch kit, the
mu/delta/crossing bottom cores aligned to absorption shape, the below-pad engine instances
and the six-way single-cell dispatcher, the split-product bridge and the multi-cell layer
absorption, the eta-stack kit with the zero-vector shape, the diagonal gadget dissolution,
THE UNIT-COLUMN FAN CLIMB, the tall-identity ladder and the identity-form dissolution, the
chain induction, THE INHABITANT `lsaCanonicalReductionHolds` of the frozen owner Prop
`lstCanonicalReductionOverStrictLayersStatement`, the decision biconditional over
`SldDiagram`, the fires, the kernel-rfl negative control, and the content marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`WellFounded.fix`.  Built by the FX1PolyAudit lib glob; AuditAll registration is a later
round's bookkeeping (AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaNeOfLt
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaNeOfGt
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaLtAddSucc
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaDeepCellLayerEntryInWireRows
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaDeepCellLayerEntryAtPadOffset
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaDeepCellHeadSumVanishes
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaProductThroughDeepCellReadsPrefix
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaDeepMuProductFreshLowColumn
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaDeepMuProductFreshHighColumn
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaDeepDeltaProductFreshColumn
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaDeepCrossingProductFreshLowColumn
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaDeepCrossingProductFreshHighColumn
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaCanonicalDoubleSuccUnfolds
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaMuCellAbsorbsAtBottom
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaDeltaCellAbsorbsAtBottom
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaCrossingCellAbsorbsAtBottom
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaMuCellAbsorbs
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaDeltaCellAbsorbs
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaCrossingCellAbsorbs
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaSingleCellAbsorbs
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaPaddedHeadSourceArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaPaddedHeadTargetArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaSplitMergedSourceArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaSplitMergedTargetArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaSplitLayerEntriesBridge
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaAbsorbedProductsAgree
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaPaddedLayerAbsorbs
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaEtaCells
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaEtaCellsSnoc
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaEtaCellsSourceArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaEtaCellsTargetArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaZeroVectorLayersShape
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaCanonicalZeroSourceShape
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaScaleOneDissolves
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaGadgetOneCollapses
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaFreshZeroIntoGadgetOneMakesCopy
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaWiredEtaStack
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaWiredEtaStackAbsorbsBottomEta
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaUnitColumnFanClimb
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaTallIdentityCanonicalConverts
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaCanonicalOfIdentityDissolves
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaComposableChainReducesToCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaCanonicalReductionHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaConvertibilityDecidedByDenotation
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaCanonicalReductionFireOnDoubling
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaDoublingFireDenotesEqually
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaCanonicalReductionFireOnCrossing
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaCrossingFireDenotesEqually
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaCanonicalReductionFireOnIdentity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaDistinctDenotationsPin
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsaDistinctPairStaysNonConvertible
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.fxLafontStaircase_canonicalCompletenessProven

end FX1PolyAudit
