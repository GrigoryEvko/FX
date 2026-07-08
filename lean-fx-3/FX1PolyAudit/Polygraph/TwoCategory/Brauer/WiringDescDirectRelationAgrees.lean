import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescDirectRelationAgrees

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescDirectRelationAgrees — zero-axiom gate (KEYSTONE13)

Per-declaration zero-axiom gate for the DIRECT `relationAgrees` assembler (off the refuted cross-order route): the
same-component boundary substitution (`isSameComponent_congr`), the direct assembler
(`relationAgrees_of_boundaryReconnect_twoSided`), the `BrauerConv` bridge (`brauerConv_of_boundaryReconnect_twoSided`),
its non-vacuity witness (`brauerConv_whisker_crossingInvolution_direct`), and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isSameComponent_congr
#assert_no_axioms FX1Poly.Polygraph.relationAgrees_of_boundaryReconnect_twoSided
#assert_no_axioms FX1Poly.Polygraph.brauerConv_of_boundaryReconnect_twoSided
#assert_no_axioms FX1Poly.Polygraph.brauerConv_whisker_crossingInvolution_direct

#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBoundarySubstitution
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasDirectRelationAgreesAssembler
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasDirectBrauerConvBridge
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCollapseTrioResidualOffRefutedRoute
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasR1R3ResidualIsTwoWordFunctoriality
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerSoundnessDirectRouteResidual

end FX1PolyAudit
