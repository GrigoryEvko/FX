import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.IotaTableStructuralSR

/-! # FX1PolyAudit/AuditIotaTableCertification — IOTA-T3 audit shard (certification substrate)

Per-declaration zero-axiom gate for the IOTA-T3 bricks: the dim-0
boundary collapse, the slot-indexed certified spine projections (shift
0/1/2, stated against the interpreter's own lookups), the
sort-universal generator-cell inversion, and the two-variable
substitution stability.  Every declaration below must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

/-! ## Dim-0 collapse -/

#assert_no_axioms FX1Poly.Core.PolyCell.atDim0

/-! ## Per-shift head extraction -/

#assert_no_axioms FX1Poly.Core.ScopedChild.certifiedOfAtShiftZero
#assert_no_axioms FX1Poly.Core.ScopedChild.certifiedOfAtShiftOne
#assert_no_axioms FX1Poly.Core.ScopedChild.certifiedOfAtShiftTwo

/-! ## Slot-indexed certified projections -/

#assert_no_axioms FX1Poly.Core.CertifiedTermSpine.certifiedAtShiftZero
#assert_no_axioms FX1Poly.Core.CertifiedTermSpine.certifiedAtShiftOne
#assert_no_axioms FX1Poly.Core.CertifiedTermSpine.certifiedAtShiftTwo

/-! ## Cell inversion -/

#assert_no_axioms FX1Poly.Core.PolyCell.invertGenAtDim0

/-! ## Two-variable substitution certifies -/

#assert_no_axioms FX1Poly.Core.PolyCell.pairSubstDim0Cells
#assert_no_axioms FX1Poly.Core.HasCertifiedCellDim0.preservedBySubstPair

/-! ## Sort-precise cell builders -/

#assert_no_axioms FX1Poly.Core.PolyCell.varCell
#assert_no_axioms FX1Poly.Core.PolyCell.subst0_dim0
#assert_no_axioms FX1Poly.Core.PolyCell.substPair_dim0
#assert_no_axioms FX1Poly.Core.PolyCell.weakenBy_dim0
#assert_no_axioms FX1Poly.Core.PolyCell.weakenBodyUnderOneBinderBy_dim0
#assert_no_axioms FX1Poly.Core.PolyCell.weakenBodyUnderTwoBindersBy_dim0
#assert_no_axioms FX1Poly.Core.CertifiedTermSpine.certifiedWeakenSpineBy

/-! ## Slot replacement certifies -/

#assert_no_axioms FX1Poly.Core.PolyCell.ofDim0
#assert_no_axioms FX1Poly.Core.replacementIntoShiftCertified
#assert_no_axioms FX1Poly.Core.CertifiedTermSpine.certifiedReplaceChildAt

/-! ## The sort discipline (the IOTA-T3 row certificate) -/

#assert_no_axioms FX1Poly.Core.ReductTemplate.CertifiesAtSort
#assert_no_axioms FX1Poly.Core.ReductTemplateSpine.CertifyAgainstSpecs
#assert_no_axioms FX1Poly.Core.SpineReplacements.CertifyReplacementSorts
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.HasSortCertifiedTarget

/-! ## Type-valued Option splitters + per-index firing -/

#assert_no_axioms FX1Poly.Core.optionBindSomeSplit
#assert_no_axioms FX1Poly.Core.optionMapSomeSplit
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeSpecFires_ofIndex

/-! ## The HEADLINE: the master template induction + generic structural SR -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTemplate?_certified
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretBuiltChildren?_certified
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretReplacements?_certified
#assert_no_axioms FX1Poly.Core.HasCertifiedCellDim0.preservedByTableRedex

/-! ## The 18 row certificates + the table dispatcher -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.HasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.hasSortCertifiedTarget_ofPreserving
#assert_no_axioms FX1Poly.Core.betaIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.boolTrueIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.boolFalseIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.fstPairIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.sndPairIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.natElimZeroIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.natRecZeroIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.natElimSuccIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.natRecSuccIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.listElimNilIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.listElimConsIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.optionMatchNoneIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.optionMatchSomeIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.eitherMatchInlIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.eitherMatchInrIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.idJReflIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.idStrictRecReflIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.pathBetaIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.PolyCell.preservedByTableRedex_dim0
#assert_no_axioms FX1Poly.Core.iotaRuleTable_hasSortPreservingTargets

end FX1PolyAudit
