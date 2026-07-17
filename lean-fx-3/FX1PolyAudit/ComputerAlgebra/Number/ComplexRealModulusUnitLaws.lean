import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.ComplexRealModulusUnitLaws

/-! # FX1PolyAudit/ComputerAlgebra/Number/ComplexRealModulusUnitLaws —
    zero-axiom gate (NUM-C-3, unit laws)

Per-declaration zero-axiom gate for the ℂ modulus unit laws: nonnegativity of
the real unit, the modulus congruence over the product setoid, and the three
headline equalities `|conj z| ~ |z|`, `|1| ~ 1`, `|z^{-1}| * |z| ~ 1`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.oneRealIsNonNegativeReal
#assert_no_axioms FX1Poly.ComputerAlgebra.modulusRespectsDenotesSameComplex
#assert_no_axioms FX1Poly.ComputerAlgebra.modulusConjDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.modulusOneDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.modulusInverseTimesSelfDenotesOne
#assert_no_axioms FX1Poly.ComputerAlgebra.fxComplexReal_hasModulusUnitLaws

end FX1PolyAudit
