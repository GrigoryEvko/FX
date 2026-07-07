import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Register.FieldLayout

/-! # FX1PolyAudit/ComputerAlgebra/Register/FieldLayout — zero-axiom gate

Per-declaration zero-axiom gate for the register bit-field layer (fx_design.md
§18.1 / §18.4): the layout predicates (`fitsIn`, `isDisjointFrom`), the clean Nat
helpers (two-power split, monotone/strict multiplication, quotient uniqueness /
bound / add-multiple / high-collapse, sub-of-add-le), the arithmetic `extractField`
/`insertField`, the "splice does not overflow" bridge `insertFieldToNat`, and the
two round-trips (`extractField_insertField_same`, `extractField_insertField_disjoint`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.FieldSpec.fitsIn
#assert_no_axioms FX1Poly.ComputerAlgebra.FieldSpec.isDisjointFrom
#assert_no_axioms FX1Poly.ComputerAlgebra.twoPowAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.natMulLeMulLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.natMulLeMulRightBy
#assert_no_axioms FX1Poly.ComputerAlgebra.natLtOfMulLtMulLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.natQuotientOfDecomp
#assert_no_axioms FX1Poly.ComputerAlgebra.natQuotientBound
#assert_no_axioms FX1Poly.ComputerAlgebra.natLowPlusScaledLt
#assert_no_axioms FX1Poly.ComputerAlgebra.natInsertDecomp
#assert_no_axioms FX1Poly.ComputerAlgebra.natQuotientAddMul
#assert_no_axioms FX1Poly.ComputerAlgebra.natQuotientHighCollapse
#assert_no_axioms FX1Poly.ComputerAlgebra.natLeSubOfAddLe
#assert_no_axioms FX1Poly.ComputerAlgebra.extractField
#assert_no_axioms FX1Poly.ComputerAlgebra.insertField
#assert_no_axioms FX1Poly.ComputerAlgebra.insertFieldToNat
#assert_no_axioms FX1Poly.ComputerAlgebra.extractField_insertField_same
#assert_no_axioms FX1Poly.ComputerAlgebra.extractField_insertField_disjoint

end FX1PolyAudit
