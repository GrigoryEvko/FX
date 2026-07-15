import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjointStrings

/-! # FX1PolyAudit/AuditAxisModeAdjointStrings — zero-axiom gate for mode-4's adjoint strings

Per-declaration zero-axiom gate for `mode-4` (`FX1Poly/Axis/Mode/AdjointStrings.lean`): the four
`TwoCellConv` CONGRUENCE lemmas (the step-level congruence lifted through the closure, by induction on the
conversion — the propext-risk points), the adjunction DATA `FreeAdjunctionData` with the non-degenerate
adjunction-seed instance and the identity self-adjunction, the two TRIANGLE IDENTITIES of the identity
adjunction PROVED up to `TwoCellConv`, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- TwoCellConv is a congruence (step-level congruence lifted through the closure)
#assert_no_axioms FX1Poly.Polygraph.TwoCellConv.vcompCongrLeft
#assert_no_axioms FX1Poly.Polygraph.TwoCellConv.vcompCongrRight
#assert_no_axioms FX1Poly.Polygraph.TwoCellConv.whiskerLeftCongr
#assert_no_axioms FX1Poly.Polygraph.TwoCellConv.whiskerRightCongr

-- Adjunction data + the non-degenerate seed + the identity self-adjunction
#assert_no_axioms FX1Poly.Polygraph.FreeAdjunctionData
#assert_no_axioms FX1Poly.Polygraph.adjunctionSeedAdjunctionData
#assert_no_axioms FX1Poly.Polygraph.identityFreeAdjunction

-- The identity adjunction's triangle identities, proved up to TwoCellConv
#assert_no_axioms FX1Poly.Polygraph.identityFreeAdjunction_leftTriangle
#assert_no_axioms FX1Poly.Polygraph.identityFreeAdjunction_rightTriangle

-- The adjoint-triple (cohesion) shape + the identity witness
#assert_no_axioms FX1Poly.Polygraph.AdjointTriple
#assert_no_axioms FX1Poly.Polygraph.identityAdjointTriple
#assert_no_axioms FX1Poly.Polygraph.identityAdjointTriple_central_selfAdjoint

-- Honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasAdjunctionTriangleSaturation
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCohesiveModalityRealization

end FX1PolyAudit
