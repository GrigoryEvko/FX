import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.TransvectionRide

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.TransvectionRide — zero-axiom
gate (the CNOT ride and the generator transport)

Per-declaration zero-axiom gate for the transvection-ride brick: THE FT CNOT
WINDOW whole, the three TT bricks (fork-right discard, shared-control slide,
tap-pair collapse), THE TT CNOT WINDOW whole, the CNOT rider with its discard
boundary, the general-position window, THE CNOT RIDE, THE COMB TRANSVECTION
(`zxvCombXorAbsorbHolds : zxfCombXorAbsorbStatement`), THE GENERATOR
TRANSPORT (`zxvGeneratorTransportHolds : zxwGeneratorTransportStatement`),
the three fires with kernel span pins, and the fresh true markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`, `WellFounded.fix`, `funext`.  Built by the
FX1PolyAudit lib glob; AuditAll registration is a later round's bookkeeping
(AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvCnotWindowFTHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvCnotWindowFTIsProven

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvForkRightDiscard
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvSharedControlSlide
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvTapPairCollapse

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvCnotWindowTTHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvCnotWindowTTIsProven

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvCnotRiderLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvCnotIntoDiscards
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvCnotWindowAt
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvCnotRideDouble

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvCombXorAbsorbHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvCombXorAbsorbIsProven

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvGeneratorTransportHolds
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvGeneratorTransportIsProven

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvCombXorAbsorbFire
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvCombXorAbsorbFireSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvNormalFormXorFire
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvNormalFormXorFireSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvGeneratorTransportFire
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxvGeneratorTransportFireSpanPin

end FX1PolyAudit
