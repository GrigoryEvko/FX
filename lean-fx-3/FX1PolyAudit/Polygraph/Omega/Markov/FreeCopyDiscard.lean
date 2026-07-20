import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Markov.FreeCopyDiscard

/-! # FX1PolyAudit.Polygraph.Omega.Markov.FreeCopyDiscard — zero-axiom gate (WP-MARKOV)

Per-declaration zero-axiom gate for the free copy-discard (CD) / Markov PROP layer over the reused
Carboni-Walters relation kit: the CD re-tagging of carrier / congruence / denotation / decision, the
comonoid + naturality + special-Frobenius soundness rows and the congruence-closure lift, the two-sided
decision, the deterministic (finite-function) sub-PROP with its intrinsic (`CdConv`-invariant)
determinism theorem and the generator function/non-function split, the walled Markov completeness owner
marker, and the ground fires.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`WellFounded.fix`.  All recursion is structural on `Nat` bounds; all fires are kernel `rfl`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.CdDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.CdConv
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.denoteCd
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdwCopyCoassocSound
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdwCopyLeftCounitSound
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdwCopyRightCounitSound
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdwCopyCocommSound
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdwCopyAfterMergeSound
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdwDiscardAfterMergeSound
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdwSpecialFrobeniusSound
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdConvImpliesDenotationsAgree
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.decideCdConv
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.decisionIsImpliedByCdConv
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.notCdConvOfDistinctMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.countTrueBelow
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.isFunctionColumn
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.allFunctionColumnsBelow
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdwIsDeterministicMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdwIsDeterministic
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.countTrueBelowRespectsPointwise
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.allFunctionColumnsRespectsPointwise
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdwDeterminismRespectsCdConv
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdwMergeIsDeterministic
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdwCreateIsDeterministic
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdwSwapIsDeterministic
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdwIdentityIsDeterministic
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdwCopyIsNotDeterministic
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdwDiscardIsNotDeterministic
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdwSpecialFrobeniusIsDeterministic
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.markovCompletenessStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.markovDeterministicReconstructionStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.cdwHasMarkovCompleteness
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.fireCopyDiscardCounitLaw
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.fireCopyCoassocMatricesEqual
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.fireConvertiblePairDecidesEqual
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.fireIdentityVsSwapControlFalse
#assert_no_axioms FX1Poly.Polygraph.Omega.Markov.fireCopyVsIdentityDeterminismSplit

end FX1PolyAudit
