import FX1Poly.Polygraph.Omega.Markov.FreeCopyDiscard

/-! # FX1PolyAudit.Polygraph.Omega.Markov.FreeCopyDiscardAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and file from the fuel-based
`#assert_no_axioms` gates in the per-file twin) over the headline declarations of the WP-MARKOV round:
the CD denotation, the CD-congruence soundness lift, the two-sided decision, the deterministic sub-PROP
with its intrinsic-determinism theorem and the generator function/non-function split, the walled Markov
completeness owner marker, and the five ground fires.  Each must print "does not depend on any
axioms". -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Omega.Markov.denoteCd
#print axioms FX1Poly.Polygraph.Omega.Markov.cdConvImpliesDenotationsAgree
#print axioms FX1Poly.Polygraph.Omega.Markov.decideCdConv
#print axioms FX1Poly.Polygraph.Omega.Markov.decisionIsImpliedByCdConv
#print axioms FX1Poly.Polygraph.Omega.Markov.notCdConvOfDistinctMatrices
#print axioms FX1Poly.Polygraph.Omega.Markov.cdwIsDeterministic
#print axioms FX1Poly.Polygraph.Omega.Markov.cdwDeterminismRespectsCdConv
#print axioms FX1Poly.Polygraph.Omega.Markov.cdwCopyIsNotDeterministic
#print axioms FX1Poly.Polygraph.Omega.Markov.cdwMergeIsDeterministic
#print axioms FX1Poly.Polygraph.Omega.Markov.markovCompletenessStatement
#print axioms FX1Poly.Polygraph.Omega.Markov.cdwHasMarkovCompleteness
#print axioms FX1Poly.Polygraph.Omega.Markov.fireCopyDiscardCounitLaw
#print axioms FX1Poly.Polygraph.Omega.Markov.fireConvertiblePairDecidesEqual
#print axioms FX1Poly.Polygraph.Omega.Markov.fireIdentityVsSwapControlFalse
#print axioms FX1Poly.Polygraph.Omega.Markov.fireCopyVsIdentityDeterminismSplit

end FX1PolyAudit
