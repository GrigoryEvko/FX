import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.ISA.ArchState

/-! # FX1PolyAudit/ComputerAlgebra/ISA/ArchState — zero-axiom gate

Per-declaration zero-axiom gate for the golden-reference architectural state
(fx_design.md §18.12): the generic total store (`BitStore` + `const`/`read`/`write`
and its two read-after-write laws), the `ArchState` operations (`zeroed`, register /
memory / PC read-write, `advancePc`, `fetch`), and the observational state laws
(read-after-write same/other for registers and memory, the cross-projection
non-interference laws, and the PC/fetch redirect laws).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.BitStore
#assert_no_axioms FX1Poly.ComputerAlgebra.BitStore.const
#assert_no_axioms FX1Poly.ComputerAlgebra.BitStore.read
#assert_no_axioms FX1Poly.ComputerAlgebra.BitStore.write
#assert_no_axioms FX1Poly.ComputerAlgebra.BitStore.read_write_same
#assert_no_axioms FX1Poly.ComputerAlgebra.BitStore.read_write_other
#assert_no_axioms FX1Poly.ComputerAlgebra.ArchState.zeroed
#assert_no_axioms FX1Poly.ComputerAlgebra.ArchState.readReg
#assert_no_axioms FX1Poly.ComputerAlgebra.ArchState.writeReg
#assert_no_axioms FX1Poly.ComputerAlgebra.ArchState.readMem
#assert_no_axioms FX1Poly.ComputerAlgebra.ArchState.writeMem
#assert_no_axioms FX1Poly.ComputerAlgebra.ArchState.setPc
#assert_no_axioms FX1Poly.ComputerAlgebra.ArchState.advancePc
#assert_no_axioms FX1Poly.ComputerAlgebra.ArchState.fetch
#assert_no_axioms FX1Poly.ComputerAlgebra.ArchState.readReg_writeReg_same
#assert_no_axioms FX1Poly.ComputerAlgebra.ArchState.readReg_writeReg_other
#assert_no_axioms FX1Poly.ComputerAlgebra.ArchState.readMem_writeMem_same
#assert_no_axioms FX1Poly.ComputerAlgebra.ArchState.readMem_writeMem_other
#assert_no_axioms FX1Poly.ComputerAlgebra.ArchState.readReg_writeMem
#assert_no_axioms FX1Poly.ComputerAlgebra.ArchState.readMem_writeReg
#assert_no_axioms FX1Poly.ComputerAlgebra.ArchState.readReg_setPc
#assert_no_axioms FX1Poly.ComputerAlgebra.ArchState.fetch_setPc
#assert_no_axioms FX1Poly.ComputerAlgebra.ArchState.pc_setPc

end FX1PolyAudit
