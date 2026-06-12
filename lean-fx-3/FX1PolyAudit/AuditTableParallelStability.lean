import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.TableParallelStability

/-! # FX1PolyAudit/AuditTableParallelStability — IOTA-T6 audit shard (the stability induction)

Per-declaration zero-axiom gate for the orthogonality bricks (lookup
relatedness, rigid-head congruence inversion, firing preservation,
identical payload reads, slot-replacement relatedness) and THE generic
parallel-stability induction with its depth-0 and firing-level
corollaries.  Every declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Membership + rigidity bricks -/

#assert_no_axioms FX1Poly.Core.listEntryAt?_mem
#assert_no_axioms FX1Poly.Core.tableElimRoots_memOfRow
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineesFire_memberFires
#assert_no_axioms FX1Poly.Core.WfIotaTable.scrutineeHeadsAreRigid

/-! ## Pointwise lookup relatedness -/

#assert_no_axioms FX1Poly.Core.ParStepOverTableChildren.lookupAtShiftZeroRelated
#assert_no_axioms FX1Poly.Core.ParStepOverTableChildren.lookupAtShiftOneRelated
#assert_no_axioms FX1Poly.Core.ParStepOverTableChildren.lookupAtShiftTwoRelated

/-! ## Congruence inversion + scrutinee extraction -/

#assert_no_axioms FX1Poly.Core.ParStepOverTable.invertAtRigidHead
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeTermAt?_parRelated
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeCellExtraction_parRelated

/-! ## Firing preservation + payload reads + slot replacement -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeSpecFires_parPreserved
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineesFire_parPreserved
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.resolvePayloadSource?_parPreserved
#assert_no_axioms FX1Poly.Core.RawTermChildren.replaceChildAt?_parRelated

/-! ## THE stability induction + corollaries -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTemplate?_parStable
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretBuiltChildren?_parStable
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretReplacements?_parStable
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTarget?_parStable
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.firesOn?_parStable

end FX1PolyAudit
