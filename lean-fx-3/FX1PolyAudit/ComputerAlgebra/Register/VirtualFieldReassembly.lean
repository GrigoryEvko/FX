import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Register.VirtualFieldReassembly

/-! # FX1PolyAudit/ComputerAlgebra/Register/VirtualFieldReassembly — zero-axiom gate

Per-declaration zero-axiom gate for the virtual-field numeric-reassembly layer
(fx_design.md §18.1): the `.toNat` law for LSB-first concatenation
(`bitVecConcatToNat`), the reassembled-sum specification (`virtualReassembledSum`),
the reassembly-correctness theorem (`extractVirtualToNat`), and the low-bits
corollary (`virtualReassembledSum_recoversHeadSlice`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecConcatToNat
#assert_no_axioms FX1Poly.ComputerAlgebra.virtualReassembledSum
#assert_no_axioms FX1Poly.ComputerAlgebra.extractVirtualToNat
#assert_no_axioms FX1Poly.ComputerAlgebra.virtualReassembledSum_recoversHeadSlice

/-! ## Independent axiom-provenance headline -/

#print axioms FX1Poly.ComputerAlgebra.bitVecConcatToNat
#print axioms FX1Poly.ComputerAlgebra.extractVirtualToNat
#print axioms FX1Poly.ComputerAlgebra.virtualReassembledSum_recoversHeadSlice

end FX1PolyAudit
