import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2
import LeanFX2.FX1.LeanKernel.Name
import LeanFX2.FX1.LeanKernel.Level
import LeanFX2.FX1.LeanKernel.Expr
import LeanFX2.FX1.LeanKernel.Substitution
import LeanFX2.FX1.LeanKernel.Reduction
import LeanFX2.FX1.LeanKernel.Inductive
import LeanFX2.FX1.LeanKernel.HasType
import LeanFX2.FX1.LeanKernel.Check
import LeanFX2.FX1.LeanKernel.Soundness
import LeanFX2.FX1.LeanKernel.Audit
import LeanFX2.FX1
import LeanFX2.FX1Bridge

namespace LeanFX2.Tools

/-! ## AuditConservativity — per-decl `#assert_no_axioms` checks for the
D9.8 / D9.9 / D9.10 type-level conservativity boundary plus the
D9.14 cross-theory coherence diamond.

Mirrors the `AuditTranslation.lean` / `AuditBridge.lean` pattern: each
shipped decl gets its own line so a regression in any one Conservativity
or InternalLanguage decl fails the build with a precise pointer.

The namespace-wide `#audit_namespace LeanFX2` strict gate already
catches axiom leaks anywhere; this module adds the explicit per-decl
catalogue so the audit dashboard can report Conservativity / InternalLanguage
as a discoverable layer. -/

-- D9.8 HOTTOverMLTT: type-level conservativity.
#assert_no_axioms LeanFX2.Conservativity.isMLTTOnlyTy
#assert_no_axioms LeanFX2.Conservativity.hottToMLTTTy
#assert_no_axioms LeanFX2.Conservativity.hottToMLTTTy_preserves_isMLTTOnlyTy

-- D9.9 CubicalOverHOTT: type-level cubical-free fragment.
#assert_no_axioms LeanFX2.Conservativity.isCubicalFreeTy
#assert_no_axioms LeanFX2.Conservativity.cubicalToObservationalTy_preserves_isCubicalFreeTy

-- D9.10 ModalOverObservational: type-level modal-free fragment.
#assert_no_axioms LeanFX2.Conservativity.isModalFreeTy
#assert_no_axioms LeanFX2.Conservativity.modalToObservationalTy
#assert_no_axioms LeanFX2.Conservativity.modalToObservationalTy_preserves_isModalFreeTy

-- D9.14 InternalLanguage/Coherence: cubical/observational diamond.
#assert_no_axioms LeanFX2.InternalLanguage.unitEqualityTranslationCoherence

end LeanFX2.Tools
