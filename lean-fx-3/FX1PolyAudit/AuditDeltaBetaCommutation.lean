import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Delta.DeltaBetaCommutation

/-! # FX1PolyAudit/AuditDeltaBetaCommutation — RW-4 δ/β commutation audit shard

Per-declaration zero-axiom gate for the δ/β root-commutation core: the two
δ-constant cells are canonical β/ι normal forms (`no_step_from_hyperreal` /
`no_step_from_qubit`), the head-level disjointness reason
(`deltaConstantHead_notRedexHead`), the general no-root-redex-source fact
(`deltaConstantCell_noRootStepSource`), the two concrete competing-step
refutations, and the ★ root-commutation theorem
(`deltaRootRedex_noCanonicalStep`).  Every declaration below must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

/-! ## The δ-redex cells are canonical normal forms -/

#assert_no_axioms FX1Poly.Core.Step.no_step_from_hyperreal
#assert_no_axioms FX1Poly.Core.Step.no_step_from_qubit

/-! ## The head-disjointness reason -/

#assert_no_axioms FX1Poly.Core.deltaConstantHead_notRedexHead
#assert_no_axioms FX1Poly.Core.deltaConstantCell_noRootStepSource

/-! ## The commutation core -/

#assert_no_axioms FX1Poly.Core.hyperrealDeltaRedex_canonicalNormal
#assert_no_axioms FX1Poly.Core.qubitDeltaRedex_canonicalNormal
#assert_no_axioms FX1Poly.Core.deltaRootRedex_noCanonicalStep
#assert_no_axioms FX1Poly.Core.hyperrealDeltaFiresAtCanonicalNormal

end FX1PolyAudit
