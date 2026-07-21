import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfCompleteness

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfCompleteness —
    zero-axiom gate (IH_Q syntactic completeness)

Per-declaration zero-axiom gate for:

* denotational NF canonicity (`cvzNfCanonicalUpToSpan`);
* the conditional syntactic-completeness capstone
  (`cvzSyntacticCompletenessGivenReachability`,
  `cvzWordProblemBiconditionalGivenReachability`,
  `cvzHasConditionalWordProblem`);
* the wall (`cvzHasSyntacticCompleteness`);
* the concrete NF diagrams and the ground fires (`cvzNormalFormLineOneTwo`,
  `cvzNormalFormLineTwoFour`, `cvzNormalFormLineOneThree`,
  `cvzFireNfLineCorrect`, `cvzFireNfDenotationsSpanEqual`,
  `cvzFireNfDenotationsSpanUnequalControl`, `cvzFireContentNfCanonicity`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`, `funext`, `WellFounded.fix`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.cvzNfCanonicalUpToSpan
#assert_no_axioms FX1Poly.ComputerAlgebra.cvzSyntacticCompletenessGivenReachability
#assert_no_axioms FX1Poly.ComputerAlgebra.cvzWordProblemBiconditionalGivenReachability
#assert_no_axioms FX1Poly.ComputerAlgebra.cvzHasConditionalWordProblem
#assert_no_axioms FX1Poly.ComputerAlgebra.cvzHasSyntacticCompleteness
#assert_no_axioms FX1Poly.ComputerAlgebra.cvzNormalFormLineOneTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.cvzNormalFormLineTwoFour
#assert_no_axioms FX1Poly.ComputerAlgebra.cvzNormalFormLineOneThree
#assert_no_axioms FX1Poly.ComputerAlgebra.cvzFireNfLineCorrect
#assert_no_axioms FX1Poly.ComputerAlgebra.cvzFireNfDenotationsSpanEqual
#assert_no_axioms FX1Poly.ComputerAlgebra.cvzFireNfDenotationsSpanUnequalControl
#assert_no_axioms FX1Poly.ComputerAlgebra.cvzFireContentNfCanonicity

end FX1PolyAudit
