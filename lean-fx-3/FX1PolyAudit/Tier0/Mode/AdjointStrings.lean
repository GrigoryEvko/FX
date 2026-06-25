import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.AdjointStrings

/-! # FX1PolyAudit/AuditTier0ModeAdjointStrings — zero-axiom gate for mode-4's adjoint strings

Per-declaration zero-axiom gate for `mode-4` (`FX1Poly/Tier0/Mode/AdjointStrings.lean`): the four
`TwoCellConv` CONGRUENCE lemmas (the step-level congruence lifted through the closure, by induction on the
conversion — the propext-risk points), the adjunction DATA `FreeAdjunctionData` with the non-degenerate
adjunction-seed instance and the identity self-adjunction, the two TRIANGLE IDENTITIES of the identity
adjunction PROVED up to `TwoCellConv`, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- TwoCellConv is a congruence (step-level congruence lifted through the closure)
#assert_no_axioms FX1Poly.Tier0.TwoCellConv.vcompCongrLeft
#assert_no_axioms FX1Poly.Tier0.TwoCellConv.vcompCongrRight
#assert_no_axioms FX1Poly.Tier0.TwoCellConv.whiskerLeftCongr
#assert_no_axioms FX1Poly.Tier0.TwoCellConv.whiskerRightCongr

-- Adjunction data + the non-degenerate seed + the identity self-adjunction
#assert_no_axioms FX1Poly.Tier0.FreeAdjunctionData
#assert_no_axioms FX1Poly.Tier0.adjunctionSeedAdjunctionData
#assert_no_axioms FX1Poly.Tier0.identityFreeAdjunction

-- The identity adjunction's triangle identities, proved up to TwoCellConv
#assert_no_axioms FX1Poly.Tier0.identityFreeAdjunction_leftTriangle
#assert_no_axioms FX1Poly.Tier0.identityFreeAdjunction_rightTriangle

-- The adjoint-triple (cohesion) shape + the identity witness
#assert_no_axioms FX1Poly.Tier0.AdjointTriple
#assert_no_axioms FX1Poly.Tier0.identityAdjointTriple
#assert_no_axioms FX1Poly.Tier0.identityAdjointTriple_central_selfAdjoint

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasAdjunctionTriangleSaturation
#assert_no_axioms FX1Poly.Tier0.fxMode_hasCohesiveModalityRealization

end FX1PolyAudit
