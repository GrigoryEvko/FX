import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.EndomorphismSimilarity

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/EndomorphismSimilarity — zero-axiom gate

Per-declaration zero-axiom gate for the walking-endomorphism linear model: the windowed-equality
substrate, the scaled-pair witness structure, and the substrate truth-probe.

Confirms the `decide`-discharged window checks are free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.agreeOnWindow
#assert_no_axioms FX1Poly.ComputerAlgebra.EndomorphismSimilarityWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismScaledInverseWindowProbe

end FX1PolyAudit
