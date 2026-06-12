import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.IotaRuleTable
import FX1Poly.Core.IotaTableEquivarianceSubstrate
import FX1Poly.Core.IotaTableStructuralSR
import FX1Poly.Core.IotaTableHonesty

/-! # FX1PolyAudit/AuditIotaTableQuotTruncRows — rows-as-data demo shard

Per-declaration zero-axiom gate for the three NEW iota rules landed
purely as table rows — quotient recursor/eliminator computation on
`quotMk` and truncation recursor computation on `truncIntro` — plus
their per-row certificates (target adequacy, scope uniformity,
sort-preserving targets) and the derived honesty-ledger flips.  No new
`Step` constructors, no new kernel arms: the rows ARE the change.
Every declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The three demo rows -/

#assert_no_axioms FX1Poly.Core.quotRecMkIotaRow
#assert_no_axioms FX1Poly.Core.quotElimMkIotaRow
#assert_no_axioms FX1Poly.Core.truncRecIntroIotaRow

/-! ## Target adequacy — the rows fire to the intended reducts -/

#assert_no_axioms FX1Poly.Core.quotRecMkIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.quotElimMkIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.truncRecIntroIotaRow_interpretsTarget

/-! ## Scope uniformity — the equivariance certificates -/

#assert_no_axioms FX1Poly.Core.quotRecMkIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.quotElimMkIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.truncRecIntroIotaRow_isScopeUniform

/-! ## Sort-preserving targets — the structural-SR certificates -/

#assert_no_axioms FX1Poly.Core.quotRecMkIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.quotElimMkIotaRow_hasSortPreservingTarget
#assert_no_axioms FX1Poly.Core.truncRecIntroIotaRow_hasSortPreservingTarget

/-! ## The honesty-ledger flips — the eliminators went live by data -/

#assert_no_axioms FX1Poly.Core.hasReductionRule_quotRec
#assert_no_axioms FX1Poly.Core.hasReductionRule_quotElim
#assert_no_axioms FX1Poly.Core.hasReductionRule_truncRec

end FX1PolyAudit
