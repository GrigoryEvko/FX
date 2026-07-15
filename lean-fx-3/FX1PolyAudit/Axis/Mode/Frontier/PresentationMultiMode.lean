import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.Frontier.PresentationMultiMode

/-! # FX1PolyAudit/AuditAxisModeFrontierPresentationMultiMode — zero-axiom gate for the mode-27 frontier

Per-declaration zero-axiom gate for the MULTI-mode MTT presentation
(`FX1Poly/Axis/Mode/Frontier/PresentationMultiMode.lean`): the mode-annotated lock entry + context, the total and
per-mode lock-depth measures, the two monoid-homomorphism (append-distribution) lemmas, the per-mode-refines-total
bound, the mode-erasure faithfulness theorem, the Unit-mode single-mode specialization, and the biequivalence-
strength object-level functoriality content (structural-functor laws, round-trip degree invariants, the
non-identity witness).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The multi-mode context + depth measures
#assert_no_axioms FX1Poly.Axis.MttEntryMulti
#assert_no_axioms FX1Poly.Axis.MttContextMulti.lockCountMulti
#assert_no_axioms FX1Poly.Axis.MttContextMulti.lockCountAt

-- The monoid-homomorphism structural lemmas (depths distribute over append)
#assert_no_axioms FX1Poly.Axis.lockCountMulti_append
#assert_no_axioms FX1Poly.Axis.lockCountAt_append

-- The per-mode count refines the total count
#assert_no_axioms FX1Poly.Axis.lockCountAt_le_lockCountMulti

-- The faithfulness theorem (mode-erasure recovers the single mode)
#assert_no_axioms FX1Poly.Axis.eraseModes
#assert_no_axioms FX1Poly.Axis.lockCountMulti_eq_erased

-- The single-mode specialization at Mode := Unit
#assert_no_axioms FX1Poly.Axis.lockCountMulti_unit_eq_lockCount
#assert_no_axioms FX1Poly.Axis.lockCountAt_unit_eq_lockCountMulti

-- Biequivalence strength: object-level functoriality (structural-functor laws)
#assert_no_axioms FX1Poly.Axis.fitchToMttTerm_lam
#assert_no_axioms FX1Poly.Axis.fitchToMttTerm_app
#assert_no_axioms FX1Poly.Axis.fitchToMttTerm_boxIntro
#assert_no_axioms FX1Poly.Axis.mttToFitchTerm_lam
#assert_no_axioms FX1Poly.Axis.mttToFitchTerm_app
#assert_no_axioms FX1Poly.Axis.mttToFitchTerm_modIntro

-- Biequivalence strength: round-trip degree invariants + the non-identity witness
#assert_no_axioms FX1Poly.Axis.fitchRoundTrip_boxCount
#assert_no_axioms FX1Poly.Axis.mttRoundTrip_modCount
#assert_no_axioms FX1Poly.Axis.fitchRoundTrip_not_identity

end FX1PolyAudit
