import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingPartnerInvolution

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringMatchingPartnerInvolution — zero-axiom gate
(FC-3 r31, B3: the involution + no-fixed-point transport)

Per-declaration zero-axiom gate for the string `matchingOf` partner-INVOLUTION + no-fixed-point over the walking
ADJOINT-TRIPLE signature: the boundary matching is a fixed-point-free involution on the arc structure's `.diagram`
(`stringArcDiagram_partner_isInvolution`) and, transported across the diagram = matching bridge, on the plain
`matchingOf` carrier (`stringMatchingOf_partner_isInvolution` / `_neSelf`); plus the wide (`bottomCount = 4`,
mid-width `2`) and mid-zero (`bottomCount = 2`) truth-probe firings and their cup/cap arity witnesses.  The private
read-off (`stringArcDiagramPartnerReadAt`) and the private no-fixed-point bridge
(`stringPartnerIndexOf_neSelf_ofChainedSpine`) are covered transitively — any leaked axiom would surface in the
public capstones' `#print axioms` below.  Every declaration must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`.  The project `#assert_no_axioms` macro is fuel-based; the independent
`#print axioms` lines below are the trusted cross-check. -/

namespace FX1PolyAudit

-- the involution on the arc `.diagram` + transported involution / no-fixed-point on the plain carrier
#assert_no_axioms FX1Poly.Polygraph.stringArcDiagram_partner_isInvolution
#assert_no_axioms FX1Poly.Polygraph.stringMatchingOf_partner_isInvolution
#assert_no_axioms FX1Poly.Polygraph.stringMatchingOf_partner_neSelf

-- the wide (non-degenerate, mid-width 2) truth-probe: arity witness + no-fixed-point + involution round-trip
#assert_no_axioms FX1Poly.Polygraph.stringWideProbeValley_hasCupCap
#assert_no_axioms FX1Poly.Polygraph.stringMatchingOf_partner_neSelf_firesOnWideValley
#assert_no_axioms FX1Poly.Polygraph.stringMatchingOf_partner_isInvolution_firesOnWideValley

-- the mid-zero smoke probe: arity witness + no-fixed-point firing
#assert_no_axioms FX1Poly.Polygraph.stringMidZeroProbeValley_hasCupCap
#assert_no_axioms FX1Poly.Polygraph.stringMatchingOf_partner_neSelf_firesOnMidZeroValley

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxString_hasMatchingPartnerInvolution

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringArcDiagram_partner_isInvolution
#print axioms FX1Poly.Polygraph.stringMatchingOf_partner_isInvolution
#print axioms FX1Poly.Polygraph.stringMatchingOf_partner_neSelf
#print axioms FX1Poly.Polygraph.stringWideProbeValley_hasCupCap
#print axioms FX1Poly.Polygraph.stringMatchingOf_partner_neSelf_firesOnWideValley
#print axioms FX1Poly.Polygraph.stringMatchingOf_partner_isInvolution_firesOnWideValley
#print axioms FX1Poly.Polygraph.stringMidZeroProbeValley_hasCupCap
#print axioms FX1Poly.Polygraph.stringMatchingOf_partner_neSelf_firesOnMidZeroValley
#print axioms FX1Poly.Polygraph.fxString_hasMatchingPartnerInvolution

end FX1PolyAudit
