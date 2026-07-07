import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Analysis.RealContinuity

/-! # FX1PolyAudit/ComputerAlgebra/Analysis/RealContinuity — zero-axiom gate
    (ANALYSIS-CONT-1)

Per-declaration zero-axiom gate for real uniform continuity: the one- and
two-variable modulus-of-continuity predicates, the negation/addition
continuous operations, and the category of uniformly continuous maps
(identity, composition, negation as a bundled map).

Every declaration must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.IsUniformlyContinuous
#assert_no_axioms FX1Poly.ComputerAlgebra.IsUniformlyContinuousTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.isUniformlyContinuousNegReal
#assert_no_axioms FX1Poly.ComputerAlgebra.isUniformlyContinuousTwoAddReal
#assert_no_axioms FX1Poly.ComputerAlgebra.UniformlyContinuousMap
#assert_no_axioms FX1Poly.ComputerAlgebra.idUniformlyContinuousMap
#assert_no_axioms FX1Poly.ComputerAlgebra.composeUniformlyContinuousMap
#assert_no_axioms FX1Poly.ComputerAlgebra.negUniformlyContinuousMap

end FX1PolyAudit
