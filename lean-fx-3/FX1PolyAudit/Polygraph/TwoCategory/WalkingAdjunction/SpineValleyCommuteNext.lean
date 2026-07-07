import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCommuteNext

/-! # FX1PolyAudit/…/SpineValleyCommuteNext — zero-axiom gate

Per-declaration zero-axiom gate for COMMUTE brick 1 (the transposed `next` via framed chain surgery): the
cons-source read-off (`framedChain_consSource`), the located pair's boundary-path coherence
(`framedChain_pairPathCoherence`), the framed-chain pair transposition (`framedSwapPrefixChain`), and the
transposed `next` packaging (`commuteNextCell` / `commuteNextCell_spine`).  Every declaration must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.framedChain_consSource
#assert_no_axioms FX1Poly.Polygraph.framedChain_pairPathCoherence
#assert_no_axioms FX1Poly.Polygraph.framedSwapPrefixChain
#assert_no_axioms FX1Poly.Polygraph.commuteNextCell
#assert_no_axioms FX1Poly.Polygraph.commuteNextCell_spine
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyCommuteNext

end FX1PolyAudit
