import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.ComplexRealModulusLaws

/-! # FX1PolyAudit/ComputerAlgebra/Number/ComplexRealModulusLaws —
    zero-axiom gate

Per-declaration zero-axiom gate for complex modulus multiplicativity: the
multiplicative medial, the squared-modulus identity `|z w|² ~ |z|² |w|²`, and
`|z w| ~ |z| |w|`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.mulComplexMedial
#assert_no_axioms FX1Poly.ComputerAlgebra.modulusSquaredMulDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.modulusMulDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.fxComplexReal_hasModulusMultiplicativity

end FX1PolyAudit
