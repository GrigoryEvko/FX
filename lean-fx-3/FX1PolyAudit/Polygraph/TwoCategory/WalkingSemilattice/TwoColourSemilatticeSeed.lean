import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingSemilattice.TwoColourSemilatticeSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingSemilattice.TwoColourSemilatticeSeed — zero-axiom gate (the DECIDED walking bounded semilattice on TWO generators)

Per-declaration zero-axiom gate for the coloured walking bounded semilattice: the `TwoColourSemilatticeTree`
carrier, the two presence folds (`presenceAOf`, `presenceBOf`) + colour-independence smokes, the
`TwoColourSemilatticeTreeConv` five-law convertibility, the two soundness theorems, the four `normalOfPresences`
normal forms, the two coloured prepend lemmas (`prependLeafA`, `prependLeafB`), the `semilatticeMerge`
dispatch, normalization, completeness, the decision biconditional, the `slotPresenceDecEq`-driven decider +
instance, the four groundings, and the marker.  The whole coloured decision must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the two-valued presence model is a
purpose-built type whose join algebra is plain case-analysis, avoiding `Bool`/`decide`.  (The reused
`SlotPresence` / `slotJoin` / `slotPresenceDecEq` are gated in the single-generator sibling's audit twin.) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.TwoColourSemilatticeTree
#assert_no_axioms FX1Poly.Polygraph.presenceAOf
#assert_no_axioms FX1Poly.Polygraph.presenceBOf
#assert_no_axioms FX1Poly.Polygraph.presenceAOf_leafA
#assert_no_axioms FX1Poly.Polygraph.presenceBOf_leafA
#assert_no_axioms FX1Poly.Polygraph.presenceBOf_leafB
#assert_no_axioms FX1Poly.Polygraph.TwoColourSemilatticeTreeConv
#assert_no_axioms FX1Poly.Polygraph.twoColourSemilatticeConv_soundA
#assert_no_axioms FX1Poly.Polygraph.twoColourSemilatticeConv_soundB
#assert_no_axioms FX1Poly.Polygraph.normalOfPresences
#assert_no_axioms FX1Poly.Polygraph.prependLeafA
#assert_no_axioms FX1Poly.Polygraph.prependLeafB
#assert_no_axioms FX1Poly.Polygraph.semilatticeMerge
#assert_no_axioms FX1Poly.Polygraph.twoColourSemilatticeReducesToNormal
#assert_no_axioms FX1Poly.Polygraph.twoColourSemilatticeConv_complete
#assert_no_axioms FX1Poly.Polygraph.twoColourSemilatticeConv_iff_presences
#assert_no_axioms FX1Poly.Polygraph.decideTwoColourSemilatticeTreeConv
#assert_no_axioms FX1Poly.Polygraph.instDecidableTwoColourSemilatticeTreeConv
#assert_no_axioms FX1Poly.Polygraph.twoColourSemilatticeSwapConvertible
#assert_no_axioms FX1Poly.Polygraph.twoColourSemilatticeCollapsesRepeatedColour
#assert_no_axioms FX1Poly.Polygraph.twoColourSemilatticeIdemPairHolds
#assert_no_axioms FX1Poly.Polygraph.twoColourSemilatticeRejectsMissingColour
#assert_no_axioms FX1Poly.Polygraph.fxWalkingSemilattice_hasTwoColourDecision

end FX1PolyAudit
