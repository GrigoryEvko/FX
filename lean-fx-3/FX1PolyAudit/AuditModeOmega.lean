import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.ModeOmega.Interface

/-! # AuditModeOmega — zero-axiom gate for the mode ω-category (mode-*)

The Tier-0 mode ω-category design-lock: the FX instance bridges to the shipped `fxModeTheory` (the free
finite-path strict 2-category over the FX mode shifts), the non-degeneracy witness exhibits a genuine
non-identity modality, and the honest construction ledger records the mode slice in the four-axis
vocabulary.  Every pin must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- mode-0 (design-lock).  The FX mode ω-category is the shipped fxModeTheory, re-presented; its
-- non-degeneracy (a genuine ghost ⟶ pure modality) and strict-associativity ride along.
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmega
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmega_modeTheory_eq_fxModeTheory
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmega_hasNonIdentityModality
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmega_composeAssoc

-- The honest construction ledger (what is built vs the mode-1..21 GAPs).
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmega_hasModeTheoryInterface
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmega_hasNoStrictTwoCategoryCore
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmega_hasNoStructureClassCertificate
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmega_hasNoThreeCellsDecidable
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmega_hasNoAdjointStrings
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmega_hasNoTranspensionUniversalModality
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmega_hasNoStandaloneModeOmega

end FX1PolyAudit
