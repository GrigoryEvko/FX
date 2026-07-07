import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Register.VirtualField

/-! # FX1PolyAudit/ComputerAlgebra/Register/VirtualField — zero-axiom gate

Per-declaration zero-axiom gate for the virtual-field / non-overlap layer
(fx_design.md §18.1 virtual reassembly, §18.2 pattern non-overlap, §18.4): the
width-explicit slice, the `totalFieldWidth` fold and the `bitVecConcat` virtual
reassembly, the decidable `Bool` non-overlap folds (`isDisjointSpec`,
`isDisjointFromAll`, `isNonOverlapping`) with the `Prop` face, and the
range-semantics tie-off (`boolOrCases`, `isDisjointSpec_ne`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.extractFieldSlice
#assert_no_axioms FX1Poly.ComputerAlgebra.totalFieldWidth
#assert_no_axioms FX1Poly.ComputerAlgebra.extractVirtual
#assert_no_axioms FX1Poly.ComputerAlgebra.isDisjointSpec
#assert_no_axioms FX1Poly.ComputerAlgebra.isDisjointFromAll
#assert_no_axioms FX1Poly.ComputerAlgebra.isNonOverlapping
#assert_no_axioms FX1Poly.ComputerAlgebra.IsNonOverlapping
#assert_no_axioms FX1Poly.ComputerAlgebra.boolOrCases
#assert_no_axioms FX1Poly.ComputerAlgebra.isDisjointSpec_ne

end FX1PolyAudit
