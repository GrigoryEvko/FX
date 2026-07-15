import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.ModalFracture

/-! # FX1PolyAudit/AuditAxisModeModalFracture — zero-axiom gate for mode-20

Per-declaration zero-axiom gate for `mode-20` (`FX1Poly/Axis/Mode/ModalFracture.lean`): the reflective
subuniverse `Modality` + the open/Sierpiński and identity witnesses, the modal-algebra + localization universal
property, the dual coreflective subuniverse + the closed/open pair, the pullback + its full universal property,
the modal fracture comparison square, the orthogonal-factorization lifting/filler/iso machinery, and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The reflective subuniverse / modality + witnesses
#assert_no_axioms FX1Poly.Axis.Modality
#assert_no_axioms FX1Poly.Axis.identityModality
#assert_no_axioms FX1Poly.Axis.openModality

-- Modal algebras + the localization universal property
#assert_no_axioms FX1Poly.Axis.IsModalAlgebra
#assert_no_axioms FX1Poly.Axis.Modality.localize_isModal
#assert_no_axioms FX1Poly.Axis.identity_everything_modal
#assert_no_axioms FX1Poly.Axis.Modality.extend
#assert_no_axioms FX1Poly.Axis.Modality.extend_unit
#assert_no_axioms FX1Poly.Axis.Modality.extend_unique_onUnit

-- The dual coreflective subuniverse + the open/closed pair
#assert_no_axioms FX1Poly.Axis.CoreflectiveSubuniverse
#assert_no_axioms FX1Poly.Axis.identityCoreflective
#assert_no_axioms FX1Poly.Axis.closedComodality

-- The pullback + its universal property
#assert_no_axioms FX1Poly.Axis.Pullback
#assert_no_axioms FX1Poly.Axis.Pullback.mediate
#assert_no_axioms FX1Poly.Axis.Pullback.mediate_onLeft
#assert_no_axioms FX1Poly.Axis.Pullback.mediate_onRight
#assert_no_axioms FX1Poly.Axis.Pullback.ext

-- The modal fracture square
#assert_no_axioms FX1Poly.Axis.Modality.fractureComparison
#assert_no_axioms FX1Poly.Axis.Modality.fractureComparison_onLeft
#assert_no_axioms FX1Poly.Axis.Modality.fractureComparison_onRight

-- The orthogonal factorization (lifting / filler / iso orthogonality)
#assert_no_axioms FX1Poly.Axis.LiftingSquare
#assert_no_axioms FX1Poly.Axis.Filler
#assert_no_axioms FX1Poly.Axis.IsIso
#assert_no_axioms FX1Poly.Axis.leftIso_upperTriangle
#assert_no_axioms FX1Poly.Axis.leftIso_lowerTriangle
#assert_no_axioms FX1Poly.Axis.rightIso_upperTriangle
#assert_no_axioms FX1Poly.Axis.rightIso_lowerTriangle
#assert_no_axioms FX1Poly.Axis.fillerOfLeftIso
#assert_no_axioms FX1Poly.Axis.fillerOfRightIso

-- Pointwise uniqueness of the filler against a monomorphism (funext-free, discharges hasUniqueLifting)
#assert_no_axioms FX1Poly.Axis.IsMono
#assert_no_axioms FX1Poly.Axis.filler_pointwise_unique_of_mono
#assert_no_axioms FX1Poly.Axis.isoLeft_monoRight_filler_pointwise_unique

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasUniqueLifting
#assert_no_axioms FX1Poly.Axis.fxMode_hasModalFractureEquivalence
#assert_no_axioms FX1Poly.Axis.fxMode_hasClosedModalityHIT
#assert_no_axioms FX1Poly.Axis.fxMode_hasKernelModalFractureConnection

end FX1PolyAudit
