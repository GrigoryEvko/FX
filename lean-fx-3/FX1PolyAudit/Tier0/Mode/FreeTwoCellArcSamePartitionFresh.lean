import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.FreeTwoCellArcSamePartitionFresh

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellArcSamePartitionFresh — zero-axiom gate (mode-3 floor, leg B)

Per-declaration zero-axiom gate for the freshness-conditioned Godement arc residual reduced to a renaming
existence: the boolean-equality congruence under an injective renaming (`beq_congr_inj`), the
renaming-commutation of the union-find root (`renameLinks` / `unionFindParent_rename` / `unionFindRoot_rename`
/ `renameLinks_length` / `unionFindRootOf_rename`), the renaming relation and the renaming-invariance of the
partition view (`ArcRenameRel` / `sameArcPartition_of_renameRel`), the residual restated at the renaming level
and the reduction (`ArcGodementSwapRenameable` / `arcGodementSamePartitionFresh_of_swapRenameable`), and the
honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the orchestrator does the unified registration). -/

namespace FX1PolyAudit

-- boolean-equality congruence under an injective renaming
#assert_no_axioms FX1Poly.Tier0.beq_congr_inj

-- renaming-commutation of the union-find root
#assert_no_axioms FX1Poly.Tier0.renameLinks
#assert_no_axioms FX1Poly.Tier0.unionFindParent_rename
#assert_no_axioms FX1Poly.Tier0.unionFindRoot_rename
#assert_no_axioms FX1Poly.Tier0.renameLinks_length
#assert_no_axioms FX1Poly.Tier0.unionFindRootOf_rename

-- the renaming relation + the renaming-invariance of the partition view
#assert_no_axioms FX1Poly.Tier0.ArcRenameRel
#assert_no_axioms FX1Poly.Tier0.sameArcPartition_of_renameRel

-- the residual at the renaming level + the reduction
#assert_no_axioms FX1Poly.Tier0.ArcGodementSwapRenameable
#assert_no_axioms FX1Poly.Tier0.arcGodementSamePartitionFresh_of_swapRenameable

-- the concrete fresh confirmation (freshness fixes the parent's refutation)
#assert_no_axioms FX1Poly.Tier0.freshSwapPartitionComponentsAgree

-- the honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcRenameInvariance
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcGodementReducedToSwapRenameable
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcGodementSwapRenameableProof
#assert_no_axioms FX1Poly.Tier0.fxMode_hasFreshSwapPartitionConfirmed
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcGodementSamePartitionFreshProof2

end FX1PolyAudit
