import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.ModeOmega.Interface
import FX1Poly.Tier0.ModeOmega.StrictTwoCategoryCore
import FX1Poly.Tier0.ModeOmega.StructureClassCertificate

/-! # AuditModeOmega — zero-axiom gate for the mode ω-category (mode-*)

The Tier-0 mode ω-category design-lock: the FX instance bridges to the shipped `fxModeTheory` (the free
finite-path strict 2-category over the FX mode shifts), the non-degeneracy witness exhibits a genuine
non-identity modality, the strict 2-category recognition records the associator/unitor/round-trip facts,
and the structure-class certificate tags each mode with its DIM-CLASS grade-algebra shape.  Every pin
must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- mode-0 (design-lock).  The FX mode ω-category is the shipped fxModeTheory, re-presented; its
-- non-degeneracy (a genuine ghost ⟶ pure modality) and strict-associativity ride along.
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmega
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmega_modeTheory_eq_fxModeTheory
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmega_hasNonIdentityModality
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeOmega_composeAssoc

-- mode-1 (strict 2-category core).  fxModeTheory recognized as a strict 2-category: trivial
-- associator/unitor 2-cells (shipped compose_assoc/identity laws) and the abstract-interface ↔
-- concrete-FXModePath round-trip.
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeHorizontalCompositionStrictlyAssociative
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeUnitorsAreTrivial
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeAbstractConcreteRoundTrip
#assert_no_axioms FX1Poly.Tier0.ModeOmega.fxModeRoundTripWitness_ghostPureClassified

-- mode-2 (structure-class certificate = DIM-CLASS for modes).  Each FX mode atom is tagged with the
-- structure shape of its home dimension's grade algebra, GROUNDED in the shipped DIM-CLASS classification
-- (gradeAlgebraOf + usage/security/effect ledger theorems + lawful algebra bundles).
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

end FX1PolyAudit
