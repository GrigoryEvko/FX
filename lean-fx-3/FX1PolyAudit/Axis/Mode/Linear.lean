import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.Linear

/-! # FX1PolyAudit/AuditAxisModeLinear — zero-axiom gate for mode-22

Per-declaration zero-axiom gate for `mode-22` (`FX1Poly/Axis/Mode/Linear.lean`): the type-isomorphism structure,
the `!` exponential comonad + the store / identity witnesses, the co-Kleisli extension + its two unit laws, the
linear connectives ⊗ / ⊸ / & (tensor symmetry, the closed ⊗⊸ adjunction, the additive diagonal), the Seely iso
for the identity exponential, and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Type isomorphisms
#assert_no_axioms FX1Poly.Axis.LinearIso

-- The `!` exponential comonad + witnesses
#assert_no_axioms FX1Poly.Axis.LinearExponential
#assert_no_axioms FX1Poly.Axis.storeExponential
#assert_no_axioms FX1Poly.Axis.identityExponential

-- The co-Kleisli (linear -> intuitionistic) structure
#assert_no_axioms FX1Poly.Axis.LinearExponential.coKleisliExtend
#assert_no_axioms FX1Poly.Axis.LinearExponential.coKleisliExtend_extract
#assert_no_axioms FX1Poly.Axis.LinearExponential.extract_coKleisliExtend

-- Multiplicative conjunction (tensor) + symmetry
#assert_no_axioms FX1Poly.Axis.Tensor
#assert_no_axioms FX1Poly.Axis.Tensor.swap
#assert_no_axioms FX1Poly.Axis.Tensor.swap_swap

-- Linear implication + the closed tensor-hom adjunction
#assert_no_axioms FX1Poly.Axis.LinearArrow
#assert_no_axioms FX1Poly.Axis.tensorCurry
#assert_no_axioms FX1Poly.Axis.tensorUncurry
#assert_no_axioms FX1Poly.Axis.tensorCurry_uncurry
#assert_no_axioms FX1Poly.Axis.tensorUncurry_curry

-- Additive conjunction (with) + the diagonal / contraction
#assert_no_axioms FX1Poly.Axis.With
#assert_no_axioms FX1Poly.Axis.With.diagonal
#assert_no_axioms FX1Poly.Axis.With.diagonal_leftComponent
#assert_no_axioms FX1Poly.Axis.With.diagonal_rightComponent

-- The Seely isomorphism (identity exponential)
#assert_no_axioms FX1Poly.Axis.seelyIsoIdentity

-- The `?` why-not modality as a monad (discharges hasWhyNotDuality)
#assert_no_axioms FX1Poly.Axis.WhyNotModality
#assert_no_axioms FX1Poly.Axis.readerWhyNot
#assert_no_axioms FX1Poly.Axis.identityWhyNot
#assert_no_axioms FX1Poly.Axis.WhyNotModality.kleisliExtend
#assert_no_axioms FX1Poly.Axis.WhyNotModality.kleisliExtend_unit
#assert_no_axioms FX1Poly.Axis.WhyNotModality.unit_kleisliExtend
#assert_no_axioms FX1Poly.Axis.storeReaderAdjunction

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasSeelyCoherence
#assert_no_axioms FX1Poly.Axis.fxMode_hasWhyNotDuality
#assert_no_axioms FX1Poly.Axis.fxMode_hasBunchedContextManagement
#assert_no_axioms FX1Poly.Axis.fxMode_hasLinearityEnforcement
#assert_no_axioms FX1Poly.Axis.fxMode_hasKernelLinearConnection

end FX1PolyAudit
