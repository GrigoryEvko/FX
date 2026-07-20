import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.AbsorptionInduction

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.AbsorptionInduction — zero-axiom
gate (the absorption assembly)

Per-declaration zero-axiom gate for the absorption-assembly brick: the
identity-layer strip, the four cell-level residual statements, the
unconditional wire-cell absorption, the cell dispatch, the layer-to-cell
fission, the layer step, the layer recursion, the absorption assembly, the
conditional completeness/decision corollaries, the fires with their kernel
span pins, the refutation fire, and the honest markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`, `WellFounded.fix`, `funext`.  Built by the
FX1PolyAudit lib glob; AuditAll registration is a later round's bookkeeping
(AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbWireLayerStrip

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbZSpiderAbsorbStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbXSpiderAbsorbStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbCrossingAbsorbStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbIdentityAbsorbStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbCellAbsorbStatement

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbWireCellAbsorb
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbCellAbsorbOfKinds

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbPaddedLayerAbsorb
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbLayerAbsorbOfCellAbsorb

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbAbsorptionGo
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbAbsorptionOfResiduals
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbCompletenessOfResiduals
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbDecisionOfResiduals

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbWireAbsorbFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbWireAbsorbFireSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbWireLayerStripFire
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbIdentityAbsorbZeroFire
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbIdentityResidualSpanPin
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbCrossingResidualSpanPin
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbZSpiderResidualSpanPin
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbXSpiderResidualSpanPin
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbCrossingIntoKillPairFire
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbCrossingIntoKillPairFireSpanPin
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbSpanDistinctNormalFormsNotConv

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbHasAbsorptionAssembly
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbAbsorptionIsProven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbCompletenessIsProven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxbHasFullDecision

end FX1PolyAudit
