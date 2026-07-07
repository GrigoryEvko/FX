import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyMatchingClassification

/-! # FX1PolyAudit/…/ValleyMatchingClassification — zero-axiom gate

Per-declaration zero-axiom gate for the survivor-top CLASSIFICATION lemma (Piece II tail crux of the fib-3
gate): a whole-valley top port is a survivor-top iff its own open-wire value is a survivor value (`< bc`),
the clean bounded composition of the shipped N1/N2 root facts and the N3a/N3b scan-localization duals.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isSurvivorTop_extractDiagram_classify
#assert_no_axioms FX1Poly.Polygraph.isSurvivorTop_matchingValley_classify
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSurvivorTopClassificationLemma

end FX1PolyAudit
