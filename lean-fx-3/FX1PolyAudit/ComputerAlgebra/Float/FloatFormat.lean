import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Float.FloatFormat

/-! # FX1PolyAudit/ComputerAlgebra/Float/FloatFormat — zero-axiom gate

Per-declaration zero-axiom gate for the radix-generic float ADT, rounding into a
format, and the half-ulp error bound.  Every declaration must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- concrete formats
#assert_no_axioms FX1Poly.ComputerAlgebra.FloatFormat.binary16
#assert_no_axioms FX1Poly.ComputerAlgebra.FloatFormat.binary32
#assert_no_axioms FX1Poly.ComputerAlgebra.FloatFormat.binary64
#assert_no_axioms FX1Poly.ComputerAlgebra.FloatFormat.fp8E4M3
#assert_no_axioms FX1Poly.ComputerAlgebra.FloatFormat.fp8E5M2
#assert_no_axioms FX1Poly.ComputerAlgebra.FloatFormat.fp4E2M1

-- the ADT + readers
#assert_no_axioms FX1Poly.ComputerAlgebra.BinaryFloat.signedMantissa
#assert_no_axioms FX1Poly.ComputerAlgebra.BinaryFloat.ofSignedMantissa
#assert_no_axioms FX1Poly.ComputerAlgebra.BinaryFloat.toRadixScaled
#assert_no_axioms FX1Poly.ComputerAlgebra.BinaryFloat.toRadixScaled_ofSignedMantissa
#assert_no_axioms FX1Poly.ComputerAlgebra.BinaryFloat.isFinite
#assert_no_axioms FX1Poly.ComputerAlgebra.BinaryFloat.isNaN
#assert_no_axioms FX1Poly.ComputerAlgebra.BinaryFloat.isInfinite
#assert_no_axioms FX1Poly.ComputerAlgebra.BinaryFloat.isZero
#assert_no_axioms FX1Poly.ComputerAlgebra.BinaryFloat.IsCanonicalFinite

-- rounding into the format + the half-ulp bound + faithfulness
#assert_no_axioms FX1Poly.ComputerAlgebra.roundNearestToExponent
#assert_no_axioms FX1Poly.ComputerAlgebra.toRadixScaled_roundNearestToExponent
#assert_no_axioms FX1Poly.ComputerAlgebra.roundNearestErrorBoundBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.roundNearestErrorBoundAbove
#assert_no_axioms FX1Poly.ComputerAlgebra.roundNearestIsFaithful

end FX1PolyAudit
