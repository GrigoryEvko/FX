import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Float.BlockScaled

/-! # FX1PolyAudit/ComputerAlgebra/Float/BlockScaled — zero-axiom gate

Per-declaration zero-axiom gate for the MXFP4 / NVFP4 block-scaled quantization
model + the precision bridge (scaled half-ulp error).  Every declaration must be
free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- Int scaffolding
#assert_no_axioms FX1Poly.ComputerAlgebra.intAddSubAddRightCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulLeOfNonnegLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulTwoSwap

-- cross-alignment scale factoring
#assert_no_axioms FX1Poly.ComputerAlgebra.scaleGapTowardMulExactRight
#assert_no_axioms FX1Poly.ComputerAlgebra.crossAlignedMantissaMulExactRight
#assert_no_axioms FX1Poly.ComputerAlgebra.crossAlignedBracketScaledByMul

-- block formats + model
#assert_no_axioms FX1Poly.ComputerAlgebra.e8m0Scale
#assert_no_axioms FX1Poly.ComputerAlgebra.mxfp4
#assert_no_axioms FX1Poly.ComputerAlgebra.nvfp4
#assert_no_axioms FX1Poly.ComputerAlgebra.dequantizeElement
#assert_no_axioms FX1Poly.ComputerAlgebra.dequantize
#assert_no_axioms FX1Poly.ComputerAlgebra.dequantizeElementMantissa
#assert_no_axioms FX1Poly.ComputerAlgebra.dequantizeElementExponent
#assert_no_axioms FX1Poly.ComputerAlgebra.listMapLength
#assert_no_axioms FX1Poly.ComputerAlgebra.dequantizeLength

-- the precision bridge
#assert_no_axioms FX1Poly.ComputerAlgebra.dequantizeErrorBoundBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.dequantizeErrorBoundAbove

end FX1PolyAudit
