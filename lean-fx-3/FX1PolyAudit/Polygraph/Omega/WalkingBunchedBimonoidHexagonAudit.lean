import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidHexagon

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidHexagonAudit — zero-axiom gate for the width-3 hexagon
rows (WP-PROP r4, #2033, the 110-percent grind).

Per-declaration `#assert_no_axioms` on the hexagon delivery: the width-3 whiskered braidings + wide symmetries,
the Yang-Baxter / mu-naturality / delta-naturality legs and their matrix agreements (`rfl` at a raised heartbeat
budget — a compute allowance only, the proof terms stay `Eq.refl`), the hexagon row family added additively over
`BunchedBimonoidSoundRow` through the shipped `unionCellRel`, the widened respects-congruence datum + soundness,
and the two hand-exhibited hexagon completeness instances. -/

namespace FX1PolyAudit

-- B1 — the width-3 whiskered braidings + the wide symmetries (defs + matrix pins).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaWhiskerRight
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaWhiskerLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaWhiskerRightMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaWhiskerLeftMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSymmetryFront
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSymmetryBack
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSymmetryFrontMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSymmetryBackMatrix

-- B1 — the Yang-Baxter truth-probe (self-attack #1).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidYangBaxterLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidYangBaxterRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatrixRespectsYangBaxter

-- B1 — the mu / delta whiskerings + the two naturality hexagons.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuWhiskerLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuWhiskerRight
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaWhiskerLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaWhiskerRight
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuNaturalityLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuNaturalityRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatrixRespectsMuNaturality
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaNaturalityLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaNaturalityRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatrixRespectsDeltaNaturality

-- B1 — the markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_yangBaxterTruthProbed
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_hexagonNaturalityMatrixRespected

-- B2 — the hexagon row family + the widened sound congruence.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidHexagonWidenedRow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidHexagonMatrixEvalAbsorbs
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatrixSoundOverHexagon
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSoundRowEmbedsIntoHexagon
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_hexagonRowsShippedMatrixRespected

-- B3 — the two hexagon completeness instances.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidYangBaxterRightLegConvertibleToCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidYangBaxterLeftLegConvertibleToCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidYangBaxterMatrixSharedOverHexagon
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidYangBaxterCompletenessInstance
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuNaturalityRightLegConvertibleToCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuNaturalityLeftLegConvertibleToCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuNaturalityCompletenessInstance
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_hexagonCompletenessInstancesShipped

-- B4 — the ledger: the r3 hexagon walls retired name-only + the honest star scope (still r5, no fake flip).
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_hexagonWallRetiredNameOnly
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_starCongruenceWidensToHexagon
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_hexagonStarStillRFive
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_hexagonLedgerShipped

end FX1PolyAudit
