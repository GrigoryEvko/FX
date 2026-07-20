import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Decision.CombinationCompleteness

/-! # FX1PolyAudit/ComputerAlgebra/Decision/CombinationCompleteness — zero-axiom gate
    (DISSAT-COMBINE completeness legs: Nelson–Oppen completeness for the gcc + Farkas
    dispatch)

Per-declaration zero-axiom gate for the combination-completeness reduction: the
propagation-augmented A-side (`nccAugmentedArithmetic`) and its rational infeasibility
(`nccAugmentedRationallyInfeasible`, the denominator-encoded shape of
`lfkFarkasCompletenessStatement`'s antecedent), the DISCHARGED Farkas leg
(`nccAugmentedInfeasibleIffFarkasCertificate` through `lreFarkasCompletenessHolds` /
`lreScaledInfeasibilityOfAcceptedCertificate`; the leg `CombinationDispatch` still calls
owner-false), the completeness reduction `nccAcceptedCertificateOfAugmentedInfeasible`,
the joint-model companion `nccJointModelSatisfiesAugmented`, the single honest wall
`nccEqualityInterpolationStatement` (owner `fxNccCombine_hasEqualityInterpolation = false`,
FALSE over ℤ as stated), the conditional completeness / decision iff
(`nccCombinationCompleteGivenInterpolation`, `nccCombinationDecidesGivenInterpolation`),
the finite pair census bound (`nccPairListLength`, `nccInterfaceLength`, `nccTriangular`,
`nccPairListAppendLength`, `nccCollectCountBounded`, `nccPropagateOverSuffixCountBounded`,
`nccPropagatedCountBoundedByTriangle`), the DECIDED markers, and the concrete congruence
fires (a=b lifted through f to f(a)=f(b)=x0=x1, contradicting the arithmetic gap; the SAT
control; the content fires routing through the discharged Farkas leg).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.nccAugmentedArithmetic
#assert_no_axioms FX1Poly.ComputerAlgebra.nccAugmentedRationallyInfeasible
#assert_no_axioms FX1Poly.ComputerAlgebra.nccAugmentedInfeasibleIffFarkasCertificate
#assert_no_axioms FX1Poly.ComputerAlgebra.nccAcceptedCertificateOfAugmentedInfeasible
#assert_no_axioms FX1Poly.ComputerAlgebra.nccJointModelSatisfiesAugmented
#assert_no_axioms FX1Poly.ComputerAlgebra.nccEqualityInterpolationStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.nccCombinationCompleteGivenInterpolation
#assert_no_axioms FX1Poly.ComputerAlgebra.nccCombinationDecidesGivenInterpolation
#assert_no_axioms FX1Poly.ComputerAlgebra.nccPairListLength
#assert_no_axioms FX1Poly.ComputerAlgebra.nccInterfaceLength
#assert_no_axioms FX1Poly.ComputerAlgebra.nccTriangular
#assert_no_axioms FX1Poly.ComputerAlgebra.nccPairListAppendLength
#assert_no_axioms FX1Poly.ComputerAlgebra.nccCollectCountBounded
#assert_no_axioms FX1Poly.ComputerAlgebra.nccPropagateOverSuffixCountBounded
#assert_no_axioms FX1Poly.ComputerAlgebra.nccPropagatedCountBoundedByTriangle
#assert_no_axioms FX1Poly.ComputerAlgebra.fxNccCombine_hasFarkasLegDischarged
#assert_no_axioms FX1Poly.ComputerAlgebra.fxNccCombine_hasConditionalCompleteness
#assert_no_axioms FX1Poly.ComputerAlgebra.fxNccCombine_hasPropagationCensusBound
#assert_no_axioms FX1Poly.ComputerAlgebra.fxNccCombine_hasEqualityInterpolation
#assert_no_axioms FX1Poly.ComputerAlgebra.nccCongruenceTermFofA
#assert_no_axioms FX1Poly.ComputerAlgebra.nccCongruenceTermFofB
#assert_no_axioms FX1Poly.ComputerAlgebra.nccCongruenceEquations
#assert_no_axioms FX1Poly.ComputerAlgebra.nccCongruenceInterface
#assert_no_axioms FX1Poly.ComputerAlgebra.nccCongruenceArithmetic
#assert_no_axioms FX1Poly.ComputerAlgebra.nccCongruenceProblem
#assert_no_axioms FX1Poly.ComputerAlgebra.nccCongruenceSatArithmetic
#assert_no_axioms FX1Poly.ComputerAlgebra.nccCongruenceSatProblem
#assert_no_axioms FX1Poly.ComputerAlgebra.nccCongruencePropagatesLiftedEquality
#assert_no_axioms FX1Poly.ComputerAlgebra.nccCongruenceFinderHitPin
#assert_no_axioms FX1Poly.ComputerAlgebra.nccCongruenceFinderMissPin
#assert_no_axioms FX1Poly.ComputerAlgebra.nccCongruenceAcceptedPin
#assert_no_axioms FX1Poly.ComputerAlgebra.nccCongruenceAugmentedInfeasible
#assert_no_axioms FX1Poly.ComputerAlgebra.nccCongruenceHasAcceptedCertificate
#assert_no_axioms FX1Poly.ComputerAlgebra.nccCongruenceCensusBoundPin

end FX1PolyAudit
