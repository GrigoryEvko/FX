import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.BohmTree

/-! # FX1PolyAudit.Core.Rewriting.BohmTree

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.BohmTree`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The meaningless-terms theory + the KvOdV reduction-closure axiom
#assert_no_axioms FX1Poly.Core.IsSolvable

#assert_no_axioms FX1Poly.Core.IsMeaningless

#assert_no_axioms FX1Poly.Core.solvable_of_reduction

#assert_no_axioms FX1Poly.Core.meaningless_of_reduction

#assert_no_axioms FX1Poly.Core.meaningless_of_step

-- The genericity core: meaningless / solvable separation + the ⊥-identification
#assert_no_axioms FX1Poly.Core.meaningless_not_joinable_solvable

#assert_no_axioms FX1Poly.Core.meaninglessAreIndiscernible

-- ★ The genericity separation lifted to full conversion (the equational theory, via term-7 Church-Rosser)
#assert_no_axioms FX1Poly.Core.meaningless_not_conv_solvable

-- The finite Böhm-approximant domain
#assert_no_axioms FX1Poly.Core.BohmApprox

#assert_no_axioms FX1Poly.Core.IsLessDefined

#assert_no_axioms FX1Poly.Core.bottom_isLeast

#assert_no_axioms FX1Poly.Core.IsLessDefined.refl

-- The concrete witnesses
#assert_no_axioms FX1Poly.Core.exampleMeaningless

#assert_no_axioms FX1Poly.Core.exampleSolvable

#assert_no_axioms FX1Poly.Core.exampleApproximationAboveBottom

end FX1PolyAudit
