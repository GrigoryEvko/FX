import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.Frontier.ModeOmegaMultiplier

/-! # FX1PolyAudit/AuditAxisModeFrontierModeOmegaMultiplier — zero-axiom gate for the mode-21 frontier

Per-declaration zero-axiom gate for `FX1Poly/Axis/Mode/Frontier/ModeOmegaMultiplier.lean`: the connection
proving the general `Multiplier` endofunctor (`mode-12`) is strictly larger than the finite-4
`{affine, cartesian, dedekind, deMorgan}` classification (`mode-2`) — half (i) the embedding, half (ii) the
unpointable witness beyond it, plus the frontier honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The per-class operation profile + its availability flags
#assert_no_axioms FX1Poly.Axis.CubeOperationProfile
#assert_no_axioms FX1Poly.Axis.CubeOperationProfile.hasDiagonal
#assert_no_axioms FX1Poly.Axis.CubeOperationProfile.hasConnections
#assert_no_axioms FX1Poly.Axis.CubeOperationProfile.hasReversal
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.operationProfile
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.operationProfile_matches_flags

-- Half (i): the classification embeds into the general endofunctor
#assert_no_axioms FX1Poly.Axis.realizeClass
#assert_no_axioms FX1Poly.Axis.realizeClass_isIntervalMultiplier
#assert_no_axioms FX1Poly.Axis.realizeClass_isPointed
#assert_no_axioms FX1Poly.Axis.realizeClass_operationProfile_matches
#assert_no_axioms FX1Poly.Axis.realizeClass_reversal_onlyDeMorgan

-- Half (ii): a general Multiplier beyond the finite-4 classification
#assert_no_axioms FX1Poly.Axis.Multiplier.IsBeyondFiniteClassification
#assert_no_axioms FX1Poly.Axis.voidMultiplier_ne_realizeClass
#assert_no_axioms FX1Poly.Axis.voidMultiplier_beyond_finiteClassification
#assert_no_axioms FX1Poly.Axis.generalMultiplier_strictlyBeyond_finiteClassification

-- The frontier honesty marker
#assert_no_axioms FX1Poly.Axis.fxModeFrontier_hasGeneralMultiplierBeyondClassification

end FX1PolyAudit
