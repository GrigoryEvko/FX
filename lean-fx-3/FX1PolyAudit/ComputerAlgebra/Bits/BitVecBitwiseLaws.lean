import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Bits.BitVecBitwiseLaws

/-! # FX1PolyAudit/ComputerAlgebra/Bits/BitVecBitwiseLaws — zero-axiom gate

Per-declaration zero-axiom gate for the symmetric-fold bitwise laws: the generic
`bitwiseFoldSymm` operand-order independence, the commutativity of `and` / `or` /
`xor`, the `bitWeight false = 0` reduction, the XOR self-annihilation fold and its
`BitVec` corollary `x ⊕ x = 0`, and the two groundings.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega` — pure `Bool` truth tables + structural `Nat`
folds, no `Nat.le` lemma, no `List.append`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.bitwiseFoldSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecAndComm
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecOrComm
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecXorComm
#assert_no_axioms FX1Poly.ComputerAlgebra.bitWeightOfFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.bitwiseFoldXorSelf
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecXorSelf
#assert_no_axioms FX1Poly.ComputerAlgebra.natShiftRightZero
#assert_no_axioms FX1Poly.ComputerAlgebra.bitAtNatZero
#assert_no_axioms FX1Poly.ComputerAlgebra.bitwiseFoldAndZero
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecAndZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecAndZeroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecBitwiseCommGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecXorSelfGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecAndZeroGrounding

end FX1PolyAudit
