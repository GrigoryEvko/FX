import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.StrongNormalizationEtaTable

/-! # FX1PolyAudit/AuditStrongNormalizationEtaTable — ETA-T3 shard

Per-declaration zero-axiom gate for the generic eta size-decrease
theorem and table eta SN: strengthening preserves size, lookup finds a
strict subterm, the contraction inversion, the ★ size-decrease theorem,
the full-relation mutual decrease, and the generic + canonical
well-foundedness.  Every declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Size preservation and subterm bounds -/

#assert_no_axioms FX1Poly.Core.RawTerm.size_strengthen
#assert_no_axioms FX1Poly.Core.RawTerm.size_strengthenBy?
#assert_no_axioms FX1Poly.Core.RawTermChildren.size_childAtShift?

/-! ## The contraction inversion and ★ size decrease -/

#assert_no_axioms FX1Poly.Core.EtaRuleDesc.contractsOn?_someInversion
#assert_no_axioms FX1Poly.Core.EtaRuleDesc.contractsOn?_sizeDecreases

/-! ## The full relation decreases -/

#assert_no_axioms FX1Poly.Core.StepEtaOverTable.sizeDecreases
#assert_no_axioms FX1Poly.Core.StepEtaOverTableChildren.sizeDecreases

/-! ## ★ Generic table eta SN -/

#assert_no_axioms FX1Poly.Core.StepEtaOverTable.successorOver
#assert_no_axioms FX1Poly.Core.stepEtaOverTable_wellFounded
#assert_no_axioms FX1Poly.Core.StepEtaOverTable.isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.stepEtaTable_wellFounded

end FX1PolyAudit
