import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSharedMidWord

/-! # FX1PolyAudit/…/WalkingString/StringSharedMidWord — zero-axiom gate
(FC-3 r37, the shared-`midWord` brick)

Per-declaration zero-axiom gate for the string shared-`midWord` brick over the walking ADJOINT-TRIPLE signature:
Brick II `stringTopWordLength_eq_processSpineWidth` (the top-word-length = mid-width bridge), Brick III
`stringSharedMidWord_ofMidZero` (equal cap top words at mid-width `0`), the `decide` truth-probe
`stringSharedMidWord_probe_topWordLengthIsZero`, the end-to-end fire
`stringSharedMidWord_ofMidZero_firesOnMixedValley`, and the honesty marker.  The private helpers (Brick I
`modalityPathEqOfLengthZero`, `bottomRangeLength`, `bottomRangeLoopLength`) are covered transitively by the public
theorems that consume them.  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`.  The project `#assert_no_axioms` macro is fuel-based; the independent
`#print axioms` lines below are the trusted cross-check. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringTopWordLength_eq_processSpineWidth
#assert_no_axioms FX1Poly.Polygraph.stringSharedMidWord_ofMidZero
#assert_no_axioms FX1Poly.Polygraph.stringSharedMidWord_probe_topWordLengthIsZero
#assert_no_axioms FX1Poly.Polygraph.stringSharedMidWord_ofMidZero_firesOnMixedValley
#assert_no_axioms FX1Poly.Polygraph.fxString_hasSharedMidWord

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringTopWordLength_eq_processSpineWidth
#print axioms FX1Poly.Polygraph.stringSharedMidWord_ofMidZero
#print axioms FX1Poly.Polygraph.stringSharedMidWord_probe_topWordLengthIsZero
#print axioms FX1Poly.Polygraph.stringSharedMidWord_ofMidZero_firesOnMixedValley
#print axioms FX1Poly.Polygraph.fxString_hasSharedMidWord

end FX1PolyAudit
