import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.SpiderTailDeath

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.SpiderTailDeath — zero-axiom gate
(the closed-form absorbed rows and the completeness-sharpened tail-death walls)

Per-declaration zero-axiom gate for the closed-form spider-tail-death brick: the
fold constructor and its width preservation, the whiskered-spider cores with their
well-formedness and codomain arities, the closed-form absorbed rows with proven
exit-boundary width, the sharpened closed-form-conversion walls, the reductions to
the r15 tail-deaths and residuals, the completeness-reflection principle with its
content-instance discharge, the six joint span pins, the refutation and the
globality (per-row-fold impossibility) certificate, and the honest markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`, `WellFounded.fix`, `funext`.  Built by the
FX1PolyAudit lib glob; AuditAll registration is a later round's bookkeeping
(AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdCatRow
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdCatRowLength
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdSplitAt
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdSplitAtPrefixLength
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdSplitAtSuffixLength
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdFoldRow
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdFoldRowLength
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdFoldRows
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdFoldRowsWidth

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdSpiderTailCoreZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdSpiderTailCoreX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdKilledCore
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdAbsorbedRowsZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdAbsorbedRowsX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdAssocBridge

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdSpiderTailCoreZWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdSpiderTailCoreZCod
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdSpiderTailCoreXWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdSpiderTailCoreXCod
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdAbsorbedRowsZWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdAbsorbedRowsXWidth

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdZSpiderTailDeathClosedFormConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdXSpiderTailDeathClosedFormConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdZTailDeathOfClosedForm
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdXTailDeathOfClosedForm
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdZSpiderResidualOfClosedForm
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdXSpiderResidualOfClosedForm

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdConvOfSpanReflection
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdZClosedFormConvOfReflectionAtContentInstance

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdZClosedFormContentInstanceSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdZClosedFormSpanPinBands
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdZClosedFormSpanPinMerge
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdXClosedFormContentInstanceSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdXClosedFormSpanPinBands

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdSpiderRideWrongRowsNotConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdZAbsorptionIsGlobalNotPerRow

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdHasClosedFormAbsorbedRows
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdZSpiderTailDeathClosedFormConvIsProven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdXSpiderTailDeathClosedFormConvIsProven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxdConvOfSpanReflectionIsProven

end FX1PolyAudit
