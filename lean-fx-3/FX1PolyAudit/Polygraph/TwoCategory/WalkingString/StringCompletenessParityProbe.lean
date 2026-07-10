import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCompletenessParityProbe

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringCompletenessParityProbe — zero-axiom gate (FC-3 r1, B1)

Per-declaration zero-axiom gate for the completeness parity PROBE: the generic XOR-fold toggle parity and its
`composePath`-homomorphism, the signature-generic boundary-determinacy of a telescoping `genParity`, the two 1-cell
modality-count parities, the two triangle-sound weightings and their `genMatch` obligations, the two boundary-
determinacy instantiations, the parallel-pair equalities (the probe cannot separate a parallel pair), the saturated-conv
soundness, the non-vacuity witness, and the refutation marker.  Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.modalityPathToggleParity
#assert_no_axioms FX1Poly.Polygraph.modalityPathToggleParity_composePath
#assert_no_axioms FX1Poly.Polygraph.stringParity_boundaryDetermined
#assert_no_axioms FX1Poly.Polygraph.stringLeftModalityToggle
#assert_no_axioms FX1Poly.Polygraph.stringCoLeftModalityToggle
#assert_no_axioms FX1Poly.Polygraph.stringLeftModalityParity
#assert_no_axioms FX1Poly.Polygraph.stringCoLeftModalityParity
#assert_no_axioms FX1Poly.Polygraph.stringLeftModalityParity_composePath
#assert_no_axioms FX1Poly.Polygraph.stringCoLeftModalityParity_composePath
#assert_no_axioms FX1Poly.Polygraph.stringLowerGeneratorWeight
#assert_no_axioms FX1Poly.Polygraph.stringUpperGeneratorWeight
#assert_no_axioms FX1Poly.Polygraph.stringLowerGeneratorWeight_boundary
#assert_no_axioms FX1Poly.Polygraph.stringUpperGeneratorWeight_boundary
#assert_no_axioms FX1Poly.Polygraph.stringLowerParity
#assert_no_axioms FX1Poly.Polygraph.stringUpperParity
#assert_no_axioms FX1Poly.Polygraph.stringLowerParity_boundaryDetermined
#assert_no_axioms FX1Poly.Polygraph.stringUpperParity_boundaryDetermined
#assert_no_axioms FX1Poly.Polygraph.stringLowerParity_eq_of_parallel
#assert_no_axioms FX1Poly.Polygraph.stringUpperParity_eq_of_parallel
#assert_no_axioms FX1Poly.Polygraph.stringLowerParity_satConv
#assert_no_axioms FX1Poly.Polygraph.stringUpperParity_satConv
#assert_no_axioms FX1Poly.Polygraph.stringCompletenessParity_isNonVacuous
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCompletenessParityRefutation

end FX1PolyAudit
