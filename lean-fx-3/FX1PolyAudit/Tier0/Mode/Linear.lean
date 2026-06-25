import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.Linear

/-! # FX1PolyAudit/AuditTier0ModeLinear — zero-axiom gate for mode-22

Per-declaration zero-axiom gate for `mode-22` (`FX1Poly/Tier0/Mode/Linear.lean`): the type-isomorphism structure,
the `!` exponential comonad + the store / identity witnesses, the co-Kleisli extension + its two unit laws, the
linear connectives ⊗ / ⊸ / & (tensor symmetry, the closed ⊗⊸ adjunction, the additive diagonal), the Seely iso
for the identity exponential, and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Type isomorphisms
#assert_no_axioms FX1Poly.Tier0.LinearIso

-- The `!` exponential comonad + witnesses
#assert_no_axioms FX1Poly.Tier0.LinearExponential
#assert_no_axioms FX1Poly.Tier0.storeExponential
#assert_no_axioms FX1Poly.Tier0.identityExponential

-- The co-Kleisli (linear -> intuitionistic) structure
#assert_no_axioms FX1Poly.Tier0.LinearExponential.coKleisliExtend
#assert_no_axioms FX1Poly.Tier0.LinearExponential.coKleisliExtend_extract
#assert_no_axioms FX1Poly.Tier0.LinearExponential.extract_coKleisliExtend

-- Multiplicative conjunction (tensor) + symmetry
#assert_no_axioms FX1Poly.Tier0.Tensor
#assert_no_axioms FX1Poly.Tier0.Tensor.swap
#assert_no_axioms FX1Poly.Tier0.Tensor.swap_swap

-- Linear implication + the closed tensor-hom adjunction
#assert_no_axioms FX1Poly.Tier0.LinearArrow
#assert_no_axioms FX1Poly.Tier0.tensorCurry
#assert_no_axioms FX1Poly.Tier0.tensorUncurry
#assert_no_axioms FX1Poly.Tier0.tensorCurry_uncurry
#assert_no_axioms FX1Poly.Tier0.tensorUncurry_curry

-- Additive conjunction (with) + the diagonal / contraction
#assert_no_axioms FX1Poly.Tier0.With
#assert_no_axioms FX1Poly.Tier0.With.diagonal
#assert_no_axioms FX1Poly.Tier0.With.diagonal_leftComponent
#assert_no_axioms FX1Poly.Tier0.With.diagonal_rightComponent

-- The Seely isomorphism (identity exponential)
#assert_no_axioms FX1Poly.Tier0.seelyIsoIdentity

-- The `?` why-not modality as a monad (discharges hasWhyNotDuality)
#assert_no_axioms FX1Poly.Tier0.WhyNotModality
#assert_no_axioms FX1Poly.Tier0.readerWhyNot
#assert_no_axioms FX1Poly.Tier0.identityWhyNot
#assert_no_axioms FX1Poly.Tier0.WhyNotModality.kleisliExtend
#assert_no_axioms FX1Poly.Tier0.WhyNotModality.kleisliExtend_unit
#assert_no_axioms FX1Poly.Tier0.WhyNotModality.unit_kleisliExtend
#assert_no_axioms FX1Poly.Tier0.storeReaderAdjunction

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSeelyCoherence
#assert_no_axioms FX1Poly.Tier0.fxMode_hasWhyNotDuality
#assert_no_axioms FX1Poly.Tier0.fxMode_hasBunchedContextManagement
#assert_no_axioms FX1Poly.Tier0.fxMode_hasLinearityEnforcement
#assert_no_axioms FX1Poly.Tier0.fxMode_hasKernelLinearConnection

end FX1PolyAudit
