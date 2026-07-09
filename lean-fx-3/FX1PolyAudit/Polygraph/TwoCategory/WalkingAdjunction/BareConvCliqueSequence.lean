import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.BareConvCliqueSequence

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.BareConvCliqueSequence — zero-axiom gate

Per-declaration zero-axiom gate for the ORDERED Cartier–Foata clique-SEQUENCE for bare `TwoCellConv` — the
strictly-finer upgrade of r5's flat pattern-multiset, machine-REFUTED as a bare-conv invariant by the interchange
critical pair: the carrier `RawTwoCellExpr.cliqueSequence` with its decidable equality `listListListBoolDecEq`; its
strict refinement of the flat multiset still separating the r4 Godement collision (`wcc_left_cliqueSequence`,
`wcc_right_cliqueSequence`, `wordCodeCollision_cliqueSequence_differs`); the minimal single-scalar signature
(`scalarGraph`, `scalarNil`, `scalarSignature`, `scalarDot`); and the machine-REFUTATION over an `interchange` step
(`cliqueInterchangeSource`, `cliqueInterchangeReduct`, `cliqueInterchange_step`, `cliqueInterchange_conv`,
`cliqueInterchangeSource_cliqueSequence`, `cliqueInterchangeReduct_cliqueSequence`,
`cliqueInterchange_cliqueSequence_differs`, `cliqueInterchange_sortedPatternMultiset_eq`,
`cliqueSequence_not_bareConvInvariant`) plus the two honesty markers
(`fxMode_hasCartierFoataCliqueSequenceComplete`, `fxMode_hasBareConvOrderedCliqueSequenceRefutedByInterchange`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.cliqueSequence
#assert_no_axioms FX1Poly.Polygraph.listListListBoolDecEq
#assert_no_axioms FX1Poly.Polygraph.wcc_left_cliqueSequence
#assert_no_axioms FX1Poly.Polygraph.wcc_right_cliqueSequence
#assert_no_axioms FX1Poly.Polygraph.wordCodeCollision_cliqueSequence_differs
#assert_no_axioms FX1Poly.Polygraph.scalarGraph
#assert_no_axioms FX1Poly.Polygraph.scalarNil
#assert_no_axioms FX1Poly.Polygraph.scalarSignature
#assert_no_axioms FX1Poly.Polygraph.scalarDot
#assert_no_axioms FX1Poly.Polygraph.cliqueInterchangeSource
#assert_no_axioms FX1Poly.Polygraph.cliqueInterchangeReduct
#assert_no_axioms FX1Poly.Polygraph.cliqueInterchange_step
#assert_no_axioms FX1Poly.Polygraph.cliqueInterchange_conv
#assert_no_axioms FX1Poly.Polygraph.cliqueInterchangeSource_cliqueSequence
#assert_no_axioms FX1Poly.Polygraph.cliqueInterchangeReduct_cliqueSequence
#assert_no_axioms FX1Poly.Polygraph.cliqueInterchange_cliqueSequence_differs
#assert_no_axioms FX1Poly.Polygraph.cliqueInterchange_sortedPatternMultiset_eq
#assert_no_axioms FX1Poly.Polygraph.cliqueSequence_not_bareConvInvariant
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCartierFoataCliqueSequenceComplete
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasBareConvOrderedCliqueSequenceRefutedByInterchange

end FX1PolyAudit
