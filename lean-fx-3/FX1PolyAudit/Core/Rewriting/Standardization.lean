import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Standardization

/-! # FX1PolyAudit.Core.Rewriting.Standardization

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Standardization`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Finite developments: the development measure terminates
#assert_no_axioms FX1Poly.Core.accessibleBelowMeasure

#assert_no_axioms FX1Poly.Core.developmentsAreFinite

-- ★ The de Vrijer development bound: the step count is bounded by the measure (proof-relevant sequence)
#assert_no_axioms FX1Poly.Core.ReductionSequence

#assert_no_axioms FX1Poly.Core.ReductionSequence.length

#assert_no_axioms FX1Poly.Core.ReductionSequence.toReflTransClosure

#assert_no_axioms FX1Poly.Core.developmentLength_bounded

#assert_no_axioms FX1Poly.Core.developmentLength_le_measure

-- Standardization: head/internal factorization via strong postponement
#assert_no_axioms FX1Poly.Core.pushOneInternalPastHeads

#assert_no_axioms FX1Poly.Core.factorizationOfStrongPostponement

-- The concrete witnesses
#assert_no_axioms FX1Poly.Core.exampleFiniteDevelopment

#assert_no_axioms FX1Poly.Core.exampleFactorization

end FX1PolyAudit
