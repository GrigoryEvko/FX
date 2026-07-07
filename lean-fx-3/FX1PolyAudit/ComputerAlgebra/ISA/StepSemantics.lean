import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.ISA.StepSemantics

/-! # FX1PolyAudit/ComputerAlgebra/ISA/StepSemantics — zero-axiom gate

Per-declaration zero-axiom gate for the golden-reference ISA (fx_design.md §18.12):
the concrete state alias (`IsaState`), the `Instruction` set, the field layout
constants, the total `decode` (opcode `if`-chain over `Nat.decEq`, no match-compiler
propext), the exhaustive total `execute`, the composed `step`, the execute-level
correctness corollaries, and the tie-in to the refinement scaffold
(`isaSelfRefinement`, `isaSelfRefinement_onAllRuns`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.IsaState
#assert_no_axioms FX1Poly.ComputerAlgebra.Instruction
#assert_no_axioms FX1Poly.ComputerAlgebra.opcodeField
#assert_no_axioms FX1Poly.ComputerAlgebra.rdField
#assert_no_axioms FX1Poly.ComputerAlgebra.rs1Field
#assert_no_axioms FX1Poly.ComputerAlgebra.rs2Field
#assert_no_axioms FX1Poly.ComputerAlgebra.immField
#assert_no_axioms FX1Poly.ComputerAlgebra.decode
#assert_no_axioms FX1Poly.ComputerAlgebra.execute
#assert_no_axioms FX1Poly.ComputerAlgebra.step
#assert_no_axioms FX1Poly.ComputerAlgebra.execute_addReg_readReg
#assert_no_axioms FX1Poly.ComputerAlgebra.execute_loadImm_readReg
#assert_no_axioms FX1Poly.ComputerAlgebra.execute_loadImm_readReg_other
#assert_no_axioms FX1Poly.ComputerAlgebra.execute_jump_pc
#assert_no_axioms FX1Poly.ComputerAlgebra.execute_invalid_readReg
#assert_no_axioms FX1Poly.ComputerAlgebra.isaSelfRefinement
#assert_no_axioms FX1Poly.ComputerAlgebra.isaSelfRefinement_onAllRuns

end FX1PolyAudit
