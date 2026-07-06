import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupTailsFreshLength

/-! # FX1PolyAudit/…/ArcCupTailsFreshLength — zero-axiom gate

Per-declaration zero-axiom gate for the cup tails' shared fresh boundary length: from the
composite-extract equality the two tails' fresh runs at `bottomCount + 2` produce equal open-wire
counts (the cup head preserves the top-wire count; `compositeEq` forces `diagram.topCount`, the
open-wire count definitionally, to agree) — the length prerequisite for every per-port list fold.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupTails_freshOpenWiresLength_ofCompositeEq
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupTailsFreshLength

end FX1PolyAudit
