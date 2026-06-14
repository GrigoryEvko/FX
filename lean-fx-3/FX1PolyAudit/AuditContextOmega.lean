import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.ContextOmega.Interface
import FX1Poly.Tier0.ContextOmega.Comprehension

/-! # AuditContextOmega — zero-axiom gate for context-0 (the context ω-category)

The Tier-0 context ω-category design-lock: the FX instance bridges to the
shipped renaming CwR + global sections, and the honest construction ledger
records the context slice in the four-axis vocabulary.  Every pin must be free
of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- The FX context ω-category is the shipped substrate, re-presented.
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega_base_eq_renamingVecRMC
#assert_no_axioms
  FX1Poly.Tier0.ContextOmega.fxContextOmega_globalSections_eq_renamingVecGlobalSections
#assert_no_axioms
  FX1Poly.Tier0.ContextOmega.fxContextOmega_globalSections_terminal_subsingleton

-- The honest construction ledger (what is built).
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega_hasRepresentableBase
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega_hasGlobalSections

-- The honest construction ledger (the recorded gaps → context-1 … context-21).
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega_hasNoComprehensionPromoted
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega_hasNoUemuraBijection
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega_hasNoRightAdjointTranspension
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega_hasNoModalLock
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega_hasNoDimTwoHomotopy
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega_hasNoStandaloneModalRMC

-- context-1: the comprehension universal property over the FX term base.
#assert_no_axioms FX1Poly.Tier0.ContextOmega.comprehensionSplit_comprehensionPair
#assert_no_axioms FX1Poly.Tier0.ContextOmega.comprehensionPair_comprehensionSplit
#assert_no_axioms FX1Poly.Tier0.ContextOmega.comprehensionBijection

end FX1PolyAudit
