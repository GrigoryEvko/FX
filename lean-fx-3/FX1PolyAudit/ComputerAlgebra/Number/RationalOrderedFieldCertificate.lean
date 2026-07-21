import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RationalOrderedFieldCertificate

/-! # FX1PolyAudit/ComputerAlgebra/Number/RationalOrderedFieldCertificate —
    zero-axiom gate

Per-declaration zero-axiom gate for the ℚ certificate: the setoid-relative
decidable ordered-Heyting-field witness structure, the nontriviality one-liner,
and the packaged `RationalPair` instance.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.DecidableOrderedHeytingFieldWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.DecidableOrderedHeytingFieldWitness.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.rationalZeroIsApartFromOne
#assert_no_axioms FX1Poly.ComputerAlgebra.rationalOrderedHeytingFieldWitness

end FX1PolyAudit
