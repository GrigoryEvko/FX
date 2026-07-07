import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Register.AccessMode

/-! # FX1PolyAudit/ComputerAlgebra/Register/AccessMode — zero-axiom gate

Per-declaration zero-axiom gate for the register access-mode algebra (fx_design.md
§18.3): the all-ones constant, the `RegisterAccessMode` record, the eight modes
(RW/RO/WO/W1C/W1S/RC/RS/RSVD), and every proven semantics lemma — the six
definitional modes plus the read semantics of all eight and the W1C/W1S write FORM.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecAllOnes
#assert_no_axioms FX1Poly.ComputerAlgebra.readWriteMode
#assert_no_axioms FX1Poly.ComputerAlgebra.readOnlyMode
#assert_no_axioms FX1Poly.ComputerAlgebra.writeOnlyMode
#assert_no_axioms FX1Poly.ComputerAlgebra.writeOneToClearMode
#assert_no_axioms FX1Poly.ComputerAlgebra.writeOneToSetMode
#assert_no_axioms FX1Poly.ComputerAlgebra.readToClearMode
#assert_no_axioms FX1Poly.ComputerAlgebra.readToSetMode
#assert_no_axioms FX1Poly.ComputerAlgebra.reservedMode
#assert_no_axioms FX1Poly.ComputerAlgebra.readWriteMode_readValue
#assert_no_axioms FX1Poly.ComputerAlgebra.readWriteMode_writeUpdate
#assert_no_axioms FX1Poly.ComputerAlgebra.readOnlyMode_readValue
#assert_no_axioms FX1Poly.ComputerAlgebra.readOnlyMode_writeUpdate
#assert_no_axioms FX1Poly.ComputerAlgebra.readOnlyMode_rejectsWrite
#assert_no_axioms FX1Poly.ComputerAlgebra.writeOnlyMode_readValue
#assert_no_axioms FX1Poly.ComputerAlgebra.writeOnlyMode_writeUpdate
#assert_no_axioms FX1Poly.ComputerAlgebra.readToClearMode_readValue
#assert_no_axioms FX1Poly.ComputerAlgebra.readToClearMode_readResidual
#assert_no_axioms FX1Poly.ComputerAlgebra.readToSetMode_readValue
#assert_no_axioms FX1Poly.ComputerAlgebra.readToSetMode_readResidual
#assert_no_axioms FX1Poly.ComputerAlgebra.reservedMode_readValue
#assert_no_axioms FX1Poly.ComputerAlgebra.reservedMode_writeUpdate
#assert_no_axioms FX1Poly.ComputerAlgebra.reservedMode_mayWrite
#assert_no_axioms FX1Poly.ComputerAlgebra.reservedMode_zeroWriteLegal
#assert_no_axioms FX1Poly.ComputerAlgebra.writeOneToClearMode_readValue
#assert_no_axioms FX1Poly.ComputerAlgebra.writeOneToClearMode_writeUpdate
#assert_no_axioms FX1Poly.ComputerAlgebra.writeOneToSetMode_readValue
#assert_no_axioms FX1Poly.ComputerAlgebra.writeOneToSetMode_writeUpdate

end FX1PolyAudit
