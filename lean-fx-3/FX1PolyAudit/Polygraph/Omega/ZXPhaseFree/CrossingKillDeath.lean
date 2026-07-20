import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.CrossingKillDeath

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.CrossingKillDeath — zero-axiom
gate (the middle-band interchange that inhabits the crossing kill-death wall)

Per-declaration zero-axiom gate for the kill-death brick: the kill-cells split,
the two side-kill peels (splitLayer and the disjoint-block engine) with their
arity-parametrized wrappers, the middle-band interchange
`zxkKillLayerMiddleSplit`, the codomain-width-0 core death, the inhabited wall
`zxkCrossIntoKillHolds : zxcCrossIntoKillStatement`, the unconditional crossing
absorption `zxkCrossingAbsorbHolds : zxbCrossingAbsorbStatement`, the fires with
their kernel span pins, the honest true markers, the identity-residual soundness
pin, and the identity-residual owner-false marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`, `WellFounded.fix`, `funext`.  Built by the
FX1PolyAudit lib glob; AuditAll registration is a later round's bookkeeping
(AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxkKillCellsCat

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxkRightKillPeel
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxkLeftKillPeel
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxkRightKillPeelAt
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxkLeftKillPeelAt

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxkKillLayerMiddleSplit
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxkCrossIntoKillCore
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxkCrossIntoKillHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxkCrossingAbsorbHolds

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxkCrossIntoKillFireEdge
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxkCrossIntoKillFireEdgeSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxkCrossIntoKillFireBands
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxkCrossIntoKillFireBandsSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxkKillLayerMiddleSplitFire

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxkHasCrossIntoKillDeath
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxkHasUnconditionalCrossingAbsorb

#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxkIdentityResidualSpanPinTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxkIdentityAbsorbIsProven

end FX1PolyAudit
