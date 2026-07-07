import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.ISA.StepRefinement

/-! # FX1PolyAudit/ComputerAlgebra/ISA/StepRefinement — zero-axiom gate

Per-declaration zero-axiom gate for the forward step-refinement scaffold
(fx_design.md §13.19 / §18.12): the structural iterator (`iterateStep`), the
`StepRefinement` relation carrier, the multi-step lifting (`iterate` / `onAllRuns`),
the functional-abstraction builder (`ofAbstraction`), and the non-vacuous identity
instance (`identity`) plus its `Nat` smoke witness.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.iterateStep
#assert_no_axioms FX1Poly.ComputerAlgebra.StepRefinement
#assert_no_axioms FX1Poly.ComputerAlgebra.StepRefinement.iterate
#assert_no_axioms FX1Poly.ComputerAlgebra.StepRefinement.onAllRuns
#assert_no_axioms FX1Poly.ComputerAlgebra.StepRefinement.ofAbstraction
#assert_no_axioms FX1Poly.ComputerAlgebra.StepRefinement.identity
#assert_no_axioms FX1Poly.ComputerAlgebra.natSuccorRefinement

end FX1PolyAudit
