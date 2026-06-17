import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.ModalFracture

/-! # FX1PolyAudit/AuditTier0ModeModalFracture — zero-axiom gate for mode-20

Per-declaration zero-axiom gate for `mode-20` (`FX1Poly/Tier0/Mode/ModalFracture.lean`): the reflective
subuniverse `Modality` + the open/Sierpiński and identity witnesses, the modal-algebra + localization universal
property, the dual coreflective subuniverse + the closed/open pair, the pullback + its full universal property,
the modal fracture comparison square, the orthogonal-factorization lifting/filler/iso machinery, and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The reflective subuniverse / modality + witnesses
#assert_no_axioms FX1Poly.Tier0.Modality
#assert_no_axioms FX1Poly.Tier0.identityModality
#assert_no_axioms FX1Poly.Tier0.openModality

-- Modal algebras + the localization universal property
#assert_no_axioms FX1Poly.Tier0.IsModalAlgebra
#assert_no_axioms FX1Poly.Tier0.Modality.localize_isModal
#assert_no_axioms FX1Poly.Tier0.identity_everything_modal
#assert_no_axioms FX1Poly.Tier0.Modality.extend
#assert_no_axioms FX1Poly.Tier0.Modality.extend_unit
#assert_no_axioms FX1Poly.Tier0.Modality.extend_unique_onUnit

-- The dual coreflective subuniverse + the open/closed pair
#assert_no_axioms FX1Poly.Tier0.CoreflectiveSubuniverse
#assert_no_axioms FX1Poly.Tier0.identityCoreflective
#assert_no_axioms FX1Poly.Tier0.closedComodality

-- The pullback + its universal property
#assert_no_axioms FX1Poly.Tier0.Pullback
#assert_no_axioms FX1Poly.Tier0.Pullback.mediate
#assert_no_axioms FX1Poly.Tier0.Pullback.mediate_onLeft
#assert_no_axioms FX1Poly.Tier0.Pullback.mediate_onRight
#assert_no_axioms FX1Poly.Tier0.Pullback.ext

-- The modal fracture square
#assert_no_axioms FX1Poly.Tier0.Modality.fractureComparison
#assert_no_axioms FX1Poly.Tier0.Modality.fractureComparison_onLeft
#assert_no_axioms FX1Poly.Tier0.Modality.fractureComparison_onRight

-- The orthogonal factorization (lifting / filler / iso orthogonality)
#assert_no_axioms FX1Poly.Tier0.LiftingSquare
#assert_no_axioms FX1Poly.Tier0.Filler
#assert_no_axioms FX1Poly.Tier0.IsIso
#assert_no_axioms FX1Poly.Tier0.leftIso_upperTriangle
#assert_no_axioms FX1Poly.Tier0.leftIso_lowerTriangle
#assert_no_axioms FX1Poly.Tier0.rightIso_upperTriangle
#assert_no_axioms FX1Poly.Tier0.rightIso_lowerTriangle
#assert_no_axioms FX1Poly.Tier0.fillerOfLeftIso
#assert_no_axioms FX1Poly.Tier0.fillerOfRightIso

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasUniqueLifting
#assert_no_axioms FX1Poly.Tier0.fxMode_hasModalFractureEquivalence
#assert_no_axioms FX1Poly.Tier0.fxMode_hasClosedModalityHIT
#assert_no_axioms FX1Poly.Tier0.fxMode_hasKernelModalFractureConnection

end FX1PolyAudit
