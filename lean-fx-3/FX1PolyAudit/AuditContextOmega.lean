import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.ContextOmega.Interface

/-! # AuditContextOmega — zero-axiom gate for the context omega-category axis

Per-declaration `#assert_no_axioms` coverage for the rebuilt context axis
(`Tier0/ContextOmega/`).  The old 23-file ContextOmega was deleted wholesale
(commit 61e39694) and is being rebuilt as the context-0..21 modal-RMC axis;
this gate grows one block per rung.

Currently covers the context-0 design-lock (`Interface.lean`): the
CwR-functor category (composition + the three category laws), the modal RMC
interface, and the terminal-CwR non-vacuity witness. -/

-- The category of CwRs (composition + identity/identity/associativity laws).
#assert_no_axioms FX1Poly.Tier0.CwRMorphism.compose
#assert_no_axioms FX1Poly.Tier0.CwRMorphism.identityCompose
#assert_no_axioms FX1Poly.Tier0.CwRMorphism.composeIdentity
#assert_no_axioms FX1Poly.Tier0.CwRMorphism.composeAssoc

-- The terminal-CwR non-vacuity witness for the modal RMC interface.
#assert_no_axioms FX1Poly.Tier0.ContextOmega.terminalRawCategory
#assert_no_axioms FX1Poly.Tier0.ContextOmega.terminalRepresentableMaps
#assert_no_axioms FX1Poly.Tier0.ContextOmega.terminalCwR
#assert_no_axioms FX1Poly.Tier0.ContextOmega.trivialModeSkeleton
#assert_no_axioms FX1Poly.Tier0.ContextOmega.trivialModalRMC
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextModalRMCWitness
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextModalRMCWitness_lock_identity
