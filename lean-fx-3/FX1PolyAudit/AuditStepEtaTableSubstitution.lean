import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.StepEtaTableSubstitution

/-! # FX1PolyAudit/AuditStepEtaTableSubstitution — ETA-T2 closure shard

Per-declaration zero-axiom gate for the eta relation closure: the
mutual substitution closure, the renaming corollary, the five per-row
scope-safety certificates, the table-level certificate, and the
canonical-table instantiations.  Every declaration below must be free
of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The mutual closure -/

#assert_no_axioms FX1Poly.Core.StepEtaOverTable.subst
#assert_no_axioms FX1Poly.Core.StepEtaOverTableChildren.subst
#assert_no_axioms FX1Poly.Core.StepEtaOverTable.rename

/-! ## The scope-safety certificates -/

#assert_no_axioms FX1Poly.Core.etaLamRow_isScopeSafe
#assert_no_axioms FX1Poly.Core.etaPairRow_isScopeSafe
#assert_no_axioms FX1Poly.Core.etaPathLamRow_isScopeSafe
#assert_no_axioms FX1Poly.Core.etaModIntroRow_isScopeSafe
#assert_no_axioms FX1Poly.Core.etaGlueIntroRow_isScopeSafe
#assert_no_axioms FX1Poly.Core.unitEtaRow_isScopeSafe
#assert_no_axioms FX1Poly.Core.etaRuleTable_isScopeSafe

/-! ## ★ The canonical-table closure -/

#assert_no_axioms FX1Poly.Core.StepEtaTable.subst
#assert_no_axioms FX1Poly.Core.StepEtaTable.rename

end FX1PolyAudit
