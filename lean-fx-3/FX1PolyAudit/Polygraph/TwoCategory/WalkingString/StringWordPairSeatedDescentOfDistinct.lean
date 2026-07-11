import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWordPairSeatedDescentOfDistinct

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringWordPairSeatedDescentOfDistinct — zero-axiom gate
(FC-3 r25, B2)

Per-declaration zero-axiom gate for the DISTINCTNESS-founded prefix descent master.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- B2 — the removed-value-gone read (positional distinctness)
#assert_no_axioms FX1Poly.Polygraph.stringNotMem_natListRemoveTwoAt_ofDistinctRead

-- B2 — the re-founded descent master (dropping the false prefixSharesWindowMode premise) + honesty marker
#assert_no_axioms FX1Poly.Polygraph.stringWordPairSeated_bubblesThroughPrefix_ofDistinct
#assert_no_axioms FX1Poly.Polygraph.fxString_hasWordPairSeatedDescentOfDistinct

end FX1PolyAudit
