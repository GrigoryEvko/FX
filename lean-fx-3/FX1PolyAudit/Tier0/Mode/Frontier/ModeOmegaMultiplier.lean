import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.Frontier.ModeOmegaMultiplier

/-! # FX1PolyAudit/AuditTier0ModeFrontierModeOmegaMultiplier — zero-axiom gate for the mode-21 frontier

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Mode/Frontier/ModeOmegaMultiplier.lean`: the connection
proving the general `Multiplier` endofunctor (`mode-12`) is strictly larger than the finite-4
`{affine, cartesian, dedekind, deMorgan}` classification (`mode-2`) — half (i) the embedding, half (ii) the
unpointable witness beyond it, plus the frontier honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The per-class operation profile + its availability flags
#assert_no_axioms FX1Poly.Tier0.CubeOperationProfile
#assert_no_axioms FX1Poly.Tier0.CubeOperationProfile.hasDiagonal
#assert_no_axioms FX1Poly.Tier0.CubeOperationProfile.hasConnections
#assert_no_axioms FX1Poly.Tier0.CubeOperationProfile.hasReversal
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.operationProfile
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.operationProfile_matches_flags

-- Half (i): the classification embeds into the general endofunctor
#assert_no_axioms FX1Poly.Tier0.realizeClass
#assert_no_axioms FX1Poly.Tier0.realizeClass_isIntervalMultiplier
#assert_no_axioms FX1Poly.Tier0.realizeClass_isPointed
#assert_no_axioms FX1Poly.Tier0.realizeClass_operationProfile_matches
#assert_no_axioms FX1Poly.Tier0.realizeClass_reversal_onlyDeMorgan

-- Half (ii): a general Multiplier beyond the finite-4 classification
#assert_no_axioms FX1Poly.Tier0.Multiplier.IsBeyondFiniteClassification
#assert_no_axioms FX1Poly.Tier0.voidMultiplier_ne_realizeClass
#assert_no_axioms FX1Poly.Tier0.voidMultiplier_beyond_finiteClassification
#assert_no_axioms FX1Poly.Tier0.generalMultiplier_strictlyBeyond_finiteClassification

-- The frontier honesty marker
#assert_no_axioms FX1Poly.Tier0.fxModeFrontier_hasGeneralMultiplierBeyondClassification

end FX1PolyAudit
