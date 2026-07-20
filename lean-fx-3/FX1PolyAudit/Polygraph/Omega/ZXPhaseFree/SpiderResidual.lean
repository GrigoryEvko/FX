import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.SpiderResidual

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.SpiderResidual — zero-axiom gate
(the whiskered-spider boundary pass and the identity-spider corner)

Per-declaration zero-axiom gate for the spider-residual brick: the generic
whiskered-cell past-init pass, the unconditional identity-spider corners (both
colours), the two tail-death residual statements, the shared absorb step, the two
conditional residual reductions, the fires with their kernel span pins, the
tail-death soundness pins, the refutation fire, and the honest markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`, `WellFounded.fix`, `funext`.  Built by the
FX1PolyAudit lib glob; AuditAll registration is a later round's bookkeeping
(AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsWhiskerCellPastInit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsZIdentitySpiderAbsorb
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsXIdentitySpiderAbsorb

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsZSpiderTailDeathStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsXSpiderTailDeathStatement

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsCellAbsorbStepOfTailDeath
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsZSpiderAbsorbOfTailDeath
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsXSpiderAbsorbOfTailDeath

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsWhiskerCellPastInitZFire
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsWhiskerCellPastInitZFireSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsWhiskerCellPastInitXFire

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsZIdentitySpiderAbsorbFire
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsZIdentitySpiderAbsorbFireSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsXIdentitySpiderAbsorbFire
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsXIdentitySpiderAbsorbFireSpanPin

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsZSpiderTailDeathSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsXSpiderTailDeathSpanPin
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsSpiderRideSpanDistinctNotConv

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsHasZSpiderDecomposition
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsHasXSpiderDecomposition
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsZSpiderResidualIsClosed
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxsXSpiderResidualIsClosed

end FX1PolyAudit
