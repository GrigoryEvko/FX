import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.IdentityResidual

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.IdentityResidual — zero-axiom
gate (the create-state ride; the walled identity residual)

Per-declaration zero-axiom gate for the identity-residual round: the disjoint
create-state ride over both congruences (`zxjZeroStateRidePastGenBlock` /
`...Conv`), the conditional whiskered identity lift
(`zxjEmptyRidesToWhiskeredIdentity`), the create-state ride fire with its kernel
span pin, the identity-residual soundness pins at `wireCount` 1/2/3, the live
content marker, and the owner-false identity-absorb marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`, `WellFounded.fix`, `funext`.  Built by the
FX1PolyAudit lib glob; AuditAll registration is a later round's bookkeeping
(AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxjZeroStateRidePastGenBlock
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxjZeroStateRidePastGenBlockConv
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxjEmptyRidesToWhiskeredIdentity

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxjZeroStateRideFire
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxjZeroStateRideFireSpanPin

#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxjIdentityResidualSpanPinOne
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxjIdentityResidualSpanPinTwo
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxjIdentityResidualSpanPinThree

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxjHasCreateStateRide
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxjHasIdentityAbsorb

end FX1PolyAudit
