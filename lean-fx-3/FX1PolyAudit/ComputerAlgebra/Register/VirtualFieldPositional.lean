import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Register.VirtualFieldPositional

/-! # FX1PolyAudit/ComputerAlgebra/Register/VirtualFieldPositional — zero-axiom gate

Per-declaration zero-axiom gate for the positional virtual-field-decode layer
(fx_design.md §18.1): the `2^0` quotient/remainder degeneracies
(`natRemainderTwoPowZero`, `natQuotientTwoPowZero`), the hand-rolled structural
positional accessors (`dropSpecs`, `prefixFieldWidth`, `headSpec`, `fieldSpecAt`,
`fieldWidthAt`, `fieldOffsetAt`), the head-drop quotient
(`virtualReassembledSum_dropsHeadByQuotient`), the prefix-drop iterated quotient
(`virtualReassembledSum_dropsPrefixByQuotient`), the arbitrary-list head-slice
bridge (`virtualReassembledSum_recoversHeadFieldSlice`), and the §18.1 capstone
(`virtualReassembledSum_recoversFieldAt`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.natRemainderTwoPowZero
#assert_no_axioms FX1Poly.ComputerAlgebra.natQuotientTwoPowZero
#assert_no_axioms FX1Poly.ComputerAlgebra.dropSpecs
#assert_no_axioms FX1Poly.ComputerAlgebra.prefixFieldWidth
#assert_no_axioms FX1Poly.ComputerAlgebra.headSpec
#assert_no_axioms FX1Poly.ComputerAlgebra.fieldSpecAt
#assert_no_axioms FX1Poly.ComputerAlgebra.fieldWidthAt
#assert_no_axioms FX1Poly.ComputerAlgebra.fieldOffsetAt
#assert_no_axioms FX1Poly.ComputerAlgebra.virtualReassembledSum_dropsHeadByQuotient
#assert_no_axioms FX1Poly.ComputerAlgebra.virtualReassembledSum_dropsPrefixByQuotient
#assert_no_axioms FX1Poly.ComputerAlgebra.virtualReassembledSum_recoversHeadFieldSlice
#assert_no_axioms FX1Poly.ComputerAlgebra.virtualReassembledSum_recoversFieldAt

/-! ## Independent axiom-provenance headline -/

#print axioms FX1Poly.ComputerAlgebra.virtualReassembledSum_dropsHeadByQuotient
#print axioms FX1Poly.ComputerAlgebra.virtualReassembledSum_dropsPrefixByQuotient
#print axioms FX1Poly.ComputerAlgebra.virtualReassembledSum_recoversFieldAt

end FX1PolyAudit
