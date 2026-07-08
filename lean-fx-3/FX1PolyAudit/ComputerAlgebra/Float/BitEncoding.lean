import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Float.BitEncoding

/-! # FX1PolyAudit/ComputerAlgebra/Float/BitEncoding — zero-axiom gate (FLOAT-1c)

Per-declaration zero-axiom gate for the sign|exponent|mantissa bit codec, its
field-bound / disjointness side-conditions, the concrete format layouts
(binary16/32/64, FP8 E4M3/E5M2, FP4 E2M1), and the decode-of-encode round-trip.
Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- layout + concrete formats
#assert_no_axioms FX1Poly.ComputerAlgebra.BitLayout.totalWidth
#assert_no_axioms FX1Poly.ComputerAlgebra.BitLayout.mantSpec
#assert_no_axioms FX1Poly.ComputerAlgebra.BitLayout.expSpec
#assert_no_axioms FX1Poly.ComputerAlgebra.BitLayout.signSpec
#assert_no_axioms FX1Poly.ComputerAlgebra.BitLayout.binary16
#assert_no_axioms FX1Poly.ComputerAlgebra.BitLayout.binary32
#assert_no_axioms FX1Poly.ComputerAlgebra.BitLayout.binary64
#assert_no_axioms FX1Poly.ComputerAlgebra.BitLayout.fp8E4M3
#assert_no_axioms FX1Poly.ComputerAlgebra.BitLayout.fp8E5M2
#assert_no_axioms FX1Poly.ComputerAlgebra.BitLayout.fp4E2M1

-- field bounds + disjointness
#assert_no_axioms FX1Poly.ComputerAlgebra.mantSpecFits
#assert_no_axioms FX1Poly.ComputerAlgebra.expSpecFits
#assert_no_axioms FX1Poly.ComputerAlgebra.signSpecFits
#assert_no_axioms FX1Poly.ComputerAlgebra.signDisjointMant
#assert_no_axioms FX1Poly.ComputerAlgebra.signDisjointExp
#assert_no_axioms FX1Poly.ComputerAlgebra.expDisjointMant

-- encode / decode + the round-trip
#assert_no_axioms FX1Poly.ComputerAlgebra.encodeFields
#assert_no_axioms FX1Poly.ComputerAlgebra.decodeSign
#assert_no_axioms FX1Poly.ComputerAlgebra.decodeExponent
#assert_no_axioms FX1Poly.ComputerAlgebra.decodeMantissa
#assert_no_axioms FX1Poly.ComputerAlgebra.decodeEncodeSign
#assert_no_axioms FX1Poly.ComputerAlgebra.decodeEncodeExponent
#assert_no_axioms FX1Poly.ComputerAlgebra.decodeEncodeMantissa

end FX1PolyAudit
