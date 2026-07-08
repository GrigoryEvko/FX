import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenNext

/-! # FX1PolyAudit/…/SpineValleyStraightenNext — zero-axiom gate

Per-declaration zero-axiom gate for Piece I STRAIGHTEN producer (iii-a) — the DELETED `next` via framed chain
surgery: the delete surgery `framedDeletePrefixChain`, the packaged deleted cell `straightenNextCell`, and its
spine `straightenNextCell_spine`.  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.framedDeletePrefixChain
#assert_no_axioms FX1Poly.Polygraph.straightenNextCell
#assert_no_axioms FX1Poly.Polygraph.straightenNextCell_spine
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyStraightenNext

end FX1PolyAudit
