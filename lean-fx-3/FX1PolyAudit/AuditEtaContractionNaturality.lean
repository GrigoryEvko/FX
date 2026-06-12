import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.EtaContractionNaturality

/-! # FX1PolyAudit/AuditEtaContractionNaturality — ETA-T2 firing
naturality shard

Per-declaration zero-axiom gate for the contraction naturality bricks:
the shift-checked lookup naturality, the fresh-pattern persistence, the
observation extraction naturality, the agreement-gate naturality, and
the ★ full firing naturality.  Every declaration below must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

/-! ## Lookup naturality and fresh persistence -/

#assert_no_axioms FX1Poly.Core.RawTermChildren.childAtShift?_subst
#assert_no_axioms FX1Poly.Core.observerFreshVarsHold_subst

/-! ## Observation and firing naturality -/

#assert_no_axioms FX1Poly.Core.EtaObservationSpec.extractCoreFrom?_subst
#assert_no_axioms FX1Poly.Core.etaObservationsAgree_subst
#assert_no_axioms FX1Poly.Core.EtaRuleDesc.contractsOn?_subst

end FX1PolyAudit
