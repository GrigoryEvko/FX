import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescPartnerReadOff

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescPartnerReadOff — zero-axiom gate (BRAUER-MIDDLE r11 B2)

Per-declaration zero-axiom gate for the r11 extraction read-off: the census bridge
(`boundaryIndexCensus_ofBoundedBoundaryComponents`), the read-off itself
(`partnerIndexOf_reads_matchingPartner`), the involution corollary
(`partnerIndexOf_involution_ofBoundedBoundaryComponents`), the mixed-diagram read-off firings, and the honesty
marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the census bridge
#assert_no_axioms FX1Poly.Polygraph.boundaryIndexCensus_ofBoundedBoundaryComponents

-- the extraction read-off + the involution corollary
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_reads_matchingPartner
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_involution_ofBoundedBoundaryComponents

-- mixed-diagram read-off firings
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_reads_crossing
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_reads_capThenCup

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasPartnerReadOff

end FX1PolyAudit
