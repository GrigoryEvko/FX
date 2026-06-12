import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.EtaTableOrthogonality

/-! # FX1PolyAudit/AuditEtaTableOrthogonality — ETA-T4 shard

Per-declaration zero-axiom gate for the WfEtaTable certificate: the
four decidable checkers, the ★ canonical certificate spanning BOTH
canonical tables, the pairwise extractions (intro-root uniqueness +
cross-table rigidity), the root dispatcher with its pins, and the ★
root-contraction determinism.  Every declaration below must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

/-! ## The checkers -/

#assert_no_axioms FX1Poly.Core.allIntroRootsDistinct
#assert_no_axioms FX1Poly.Core.allRawRowsHaveObservation
#assert_no_axioms FX1Poly.Core.allObservationSlotsWithinArity
#assert_no_axioms FX1Poly.Core.etaIntroRootsAvoidIotaElimRoots

/-! ## ★ The canonical cross-table certificate -/

#assert_no_axioms FX1Poly.Core.etaRuleTable_isWf

/-! ## Pairwise extraction -/

#assert_no_axioms FX1Poly.Core.allIntroRootsDistinct_memUnique
#assert_no_axioms FX1Poly.Core.WfEtaTable.introRootsAreNotIotaElims

/-! ## The dispatcher and ★ root determinism -/

#assert_no_axioms FX1Poly.Core.EtaRuleDesc.contractAtRoot?
#assert_no_axioms FX1Poly.Core.EtaRuleDesc.contractAtRoot?_pinsIntro
#assert_no_axioms FX1Poly.Core.EtaRuleDesc.contractAtRoot?_atOwnIntro
#assert_no_axioms FX1Poly.Core.WfEtaTable.rootContractionDeterministic

end FX1PolyAudit
