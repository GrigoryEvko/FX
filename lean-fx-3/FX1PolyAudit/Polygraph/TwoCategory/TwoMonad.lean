import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.TwoMonad

/-! # FX1PolyAudit/AuditTier0ModeTwoMonadDoctrine — zero-axiom gate for mode-17

Per-declaration zero-axiom gate for `mode-17` (`FX1Poly/Tier0/Mode/TwoMonadDoctrine.lean`): the 2-monad + the
identity / reader witnesses, the algebra / morphism / free-algebra machinery, the EM adjunction hom-iso (both
round trips), the bi-initial model + its morphism, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The 2-monad + witnesses
#assert_no_axioms FX1Poly.Tier0.TwoMonad
#assert_no_axioms FX1Poly.Tier0.identityTwoMonad
#assert_no_axioms FX1Poly.Tier0.readerTwoMonad

-- Algebras + morphisms + the free algebra
#assert_no_axioms FX1Poly.Tier0.TwoMonad.Algebra
#assert_no_axioms FX1Poly.Tier0.TwoMonad.AlgebraMorphism
#assert_no_axioms FX1Poly.Tier0.TwoMonad.freeAlgebra

-- The EM adjunction hom-iso (the free-algebra universal property)
#assert_no_axioms FX1Poly.Tier0.TwoMonad.freeHomForward
#assert_no_axioms FX1Poly.Tier0.TwoMonad.freeHomBackward
#assert_no_axioms FX1Poly.Tier0.TwoMonad.freeHom_backward_forward
#assert_no_axioms FX1Poly.Tier0.TwoMonad.freeHom_forward_backward

-- The bi-initial model
#assert_no_axioms FX1Poly.Tier0.TwoMonad.biInitialAlgebra
#assert_no_axioms FX1Poly.Tier0.TwoMonad.biInitialMorphism
#assert_no_axioms FX1Poly.Tier0.TwoMonad.biInitialAlgebra_carrier

-- Distributive laws (combining doctrines — the pushout)
#assert_no_axioms FX1Poly.Tier0.TwoMonad.DistributiveLaw
#assert_no_axioms FX1Poly.Tier0.readerReaderDistributiveLaw
#assert_no_axioms FX1Poly.Tier0.readerComposite_Apply
#assert_no_axioms FX1Poly.Tier0.readerCompositeCurry
#assert_no_axioms FX1Poly.Tier0.readerCompositeUncurry
#assert_no_axioms FX1Poly.Tier0.readerCompositeCurry_uncurry
#assert_no_axioms FX1Poly.Tier0.readerCompositeUncurry_curry

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasModeTheoryTwoMonad
#assert_no_axioms FX1Poly.Tier0.fxMode_hasStrictBiInitialUniqueness
#assert_no_axioms FX1Poly.Tier0.fxMode_hasPseudoAlgebras
#assert_no_axioms FX1Poly.Tier0.fxMode_hasKernelTwoMonadConnection

end FX1PolyAudit
