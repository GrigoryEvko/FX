import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfReachability

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfReachability —
    zero-axiom gate (WP-PROP-3: the IH_Q reachability leg)

Per-declaration zero-axiom gate for the reachability leg: the fourteen scalar
`IhzRowMove` schemas and the A8/I3/I4/I7/I8 absorption rows re-exposed as named
`IhzConv` per-layer steps (T1+T2), the common-reduct principle and the
reachability factorization reducing `ihzReachabilityStatement` to a reduction
leg plus a canonicity leg (T3), the conditional word-problem payoff (T4), the
decision markers and the owner-false wall (`ihkHasFullReachabilityInduction`),
and the ground fires plus the discriminating scalar-2-vs-3 false control (T5).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.ihkProductStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkProductMirrorStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkThroughAddStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkThroughCoaddStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkZeroAbsorbStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkCozeroAbsorbStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkThroughCopyStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkThroughCocopyStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkDiscardAbsorbStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkUnitAbsorbStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkSumStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkSumMirrorStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkForwardCancelStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkBackwardCancelStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkBimonoidStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkBimonoidOpStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkWhiteFrobeniusLeftStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkWhiteFrobeniusRightStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkBlackFrobeniusLeftStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkBlackFrobeniusRightStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkWhiteSpecialStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkBlackSpecialStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkConvOfCommonReduct
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkReachabilityDiagonal
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkReachabilityOfChooserReductionAndCanonicity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkWordProblemGivenReachability
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkWordProblemOfChooserReductionAndCanonicity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkHasConditionalWordProblem
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkHasFullReachabilityInduction
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkScalarTwoLineDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkScalarThreeLineDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkScalarTwoIsNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkFireProductConcrete
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkFireBimonoidConcrete
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkFireSumToNormalForm
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkFireForwardCancelToWire
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkFireCommonReductCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkFireControlSpanDistinct
#assert_no_axioms FX1Poly.ComputerAlgebra.ihkFireControlNotConv

end FX1PolyAudit
