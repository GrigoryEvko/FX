import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.ModeOmega.Interface
import FX1Poly.Tier0.ModeOmega.StrictTwoCategoryCore
import FX1Poly.Tier0.ModeOmega.StructureClassCertificate

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

-- mode-1 (strict 2-category core).  fxModeTheory recognized as a strict 2-category: trivial
-- associator/unitor 2-cells (shipped compose_assoc/identity laws), strict-equality 2-cells, and the
-- abstract-interface ↔ concrete-FXModePath round-trip.  Ladder rung promoted GAP→BUILT by addition.
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeStrictTwoCategoryLedger
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeHorizontalCompositionStrictlyAssociative
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeUnitorsAreTrivial
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeTwoCellsAreStrictEqualities
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeAbstractConcreteRoundTrip
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeRoundTripWitness_ghostPureClassified
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeStrictTwoCategoryCoreRecognized
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmegaCoreLevel
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmegaCoreLevel_hasStrictTwoCategoryCore
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmegaCoreLevel_stillHasModeTheoryInterface
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmegaCoreLevel_hasNoStructureClassCertificate

-- mode-2 (structure-class certificate = DIM-CLASS for modes).  Each FX mode atom is tagged with the
-- structure shape of its home dimension's grade algebra, GROUNDED in the shipped DIM-CLASS classification
-- (gradeAlgebraOf + usage/security/effect ledger theorems + lawful algebra bundles).  Ladder rung
-- structureClassCertificate promoted GAP→BUILT by addition.
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeHomeDimension
#assert_no_axioms FX1Poly.Tier0.ModeOmega.dimensionAlgebraToStructureClass
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeStructureClass
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeStructureClassCertificate
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeStructureClassCertificate_structureClassOf_eq
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeUsageFamilyOrderedSemiring
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeSecurityFamilyOrderedSemiring
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeEffectFamilyBoundedJoinSemilattice
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOrderedSemiringClassIsLawful
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeBoundedJoinSemilatticeClassIsLawful
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeEveryModeClassified
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeStructureClassCertificateLedger
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeStructureClassCertificateRecognized
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmegaStructureClassLevel
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmegaStructureClassLevel_hasStructureClassCertificate
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmegaStructureClassLevel_stillHasStrictTwoCategoryCore
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmegaStructureClassLevel_hasNoThreeCellsDecidable

end FX1PolyAudit
