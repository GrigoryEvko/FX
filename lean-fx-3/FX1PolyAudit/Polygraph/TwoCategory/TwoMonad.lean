import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.TwoMonad

/-! # FX1PolyAudit/AuditAxisModeTwoMonadDoctrine — zero-axiom gate for mode-17

Per-declaration zero-axiom gate for `mode-17` (`FX1Poly/Axis/Mode/TwoMonadDoctrine.lean`): the 2-monad + the
identity / reader witnesses, the algebra / morphism / free-algebra machinery, the EM adjunction hom-iso (both
round trips), the bi-initial model + its morphism, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The 2-monad + witnesses
#assert_no_axioms FX1Poly.Polygraph.TwoMonad
#assert_no_axioms FX1Poly.Polygraph.identityTwoMonad
#assert_no_axioms FX1Poly.Polygraph.readerTwoMonad

-- Algebras + morphisms + the free algebra
#assert_no_axioms FX1Poly.Polygraph.TwoMonad.Algebra
#assert_no_axioms FX1Poly.Polygraph.TwoMonad.AlgebraMorphism
#assert_no_axioms FX1Poly.Polygraph.TwoMonad.freeAlgebra

-- The EM adjunction hom-iso (the free-algebra universal property)
#assert_no_axioms FX1Poly.Polygraph.TwoMonad.freeHomForward
#assert_no_axioms FX1Poly.Polygraph.TwoMonad.freeHomBackward
#assert_no_axioms FX1Poly.Polygraph.TwoMonad.freeHom_backward_forward
#assert_no_axioms FX1Poly.Polygraph.TwoMonad.freeHom_forward_backward

-- The bi-initial model
#assert_no_axioms FX1Poly.Polygraph.TwoMonad.biInitialAlgebra
#assert_no_axioms FX1Poly.Polygraph.TwoMonad.biInitialMorphism
#assert_no_axioms FX1Poly.Polygraph.TwoMonad.biInitialAlgebra_carrier

-- Distributive laws (combining doctrines — the pushout)
#assert_no_axioms FX1Poly.Polygraph.TwoMonad.DistributiveLaw
#assert_no_axioms FX1Poly.Polygraph.readerReaderDistributiveLaw
#assert_no_axioms FX1Poly.Polygraph.readerComposite_Apply
#assert_no_axioms FX1Poly.Polygraph.readerCompositeCurry
#assert_no_axioms FX1Poly.Polygraph.readerCompositeUncurry
#assert_no_axioms FX1Poly.Polygraph.readerCompositeCurry_uncurry
#assert_no_axioms FX1Poly.Polygraph.readerCompositeUncurry_curry

-- Honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasModeTheoryTwoMonad
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasStrictBiInitialUniqueness
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasPseudoAlgebras
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasKernelTwoMonadConnection

end FX1PolyAudit
