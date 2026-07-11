import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPermStage

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidPermStageAudit — zero-axiom gate for the perm-layer
general-spiderOf adjudication (WP-PROP r4, #2033, the 110-percent grind).

Per-declaration `#assert_no_axioms` on the perm-stage delivery: the three-stage NF form, the permutation-word NF
witnesses (2-wire swap = `sigma`, 3-wire reversal = the Yang-Baxter word, both round-tripped at a raised
heartbeat budget — a compute allowance only, the proof terms stay `Eq.refl`), the perm-layer irreducibility (the
reversal separated from the identity + the cited swap-unreachable), and the honest walls (general routing
transpose + Node A's residual strict-law components). -/

namespace FX1PolyAudit

-- B1 — the three-stage NF form + the permutation-word witnesses.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAaaWord
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderStaged
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderPermTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderPermReversalThree
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderPermTwoRoundTrip
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderPermReversalThreeRoundTrip

-- B1 — the perm-layer irreducibility.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidReversalNotIdentity
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermLayerIsLoadBearing
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_permLayerNfShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_permLayerIrreducible

-- B2 — the honest reach + the walls (general routing transpose + Node A narrowed).
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_permStageGeneralRoutingTransposeWall
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_nodeAStrictLawExtensionNarrowed
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_spiderOfReachIsBlockDiagonalPlusPerm
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_permStageLedgerShipped

end FX1PolyAudit
