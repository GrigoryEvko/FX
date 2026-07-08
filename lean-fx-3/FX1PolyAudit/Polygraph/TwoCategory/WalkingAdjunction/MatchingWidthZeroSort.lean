import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingWidthZeroSort

/-! # FX1PolyAudit/…/MatchingWidthZeroSort — zero-axiom gate

Per-declaration zero-axiom gate for Track B b#5 + c: the width-0 location induction `matchingLocateAux` and
the sort assembly `widthZeroPureCupDeterminacy_proof` closing `WidthZeroPureCupDeterminacy` GENERAL and
POSITIVITY-FREE (no arc census, no `arcDiagram_eq_matching`, no `0 < bottomCount`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingLocateAux
#assert_no_axioms FX1Poly.Polygraph.widthZeroPureCupDeterminacy_proof
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingWidthZeroSort

end FX1PolyAudit
