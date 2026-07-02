import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntOrderedRingCertificate

/-! # FX1PolyAudit/ComputerAlgebra/Number/IntOrderedRingCertificate — zero-axiom gate
    (NUM-Z-PACK)

Per-declaration zero-axiom gate for the ℤ certificate: the ordered-commutative-ring
witness structure, the nontriviality one-liner, and the packaged `Int` instance.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.OrderedCommutativeRingWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.OrderedCommutativeRingWitness.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.intZeroIsDistinctFromOne
#assert_no_axioms FX1Poly.ComputerAlgebra.intOrderedCommutativeRingWitness

end FX1PolyAudit
