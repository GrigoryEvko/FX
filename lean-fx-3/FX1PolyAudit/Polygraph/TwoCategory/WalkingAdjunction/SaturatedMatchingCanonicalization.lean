import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingCanonicalization

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingCanonicalization — zero-axiom gate (mode-9 keystone)

Per-declaration zero-axiom gate for the identification of the SATURATED canonicalization carrier as the boundary
planar matching `matchingOf`: the locally-indistinguishable-cups no-go (the variance is GLOBAL), the triangle
snake-collapse ON THE NOSE, the `embeddedTipCap` obstruction resolution (where both monotone folds were refuted),
the face-discrimination (completeness-capable), the whisker-exchange soundness, and the `matchingOf`-carried
saturated canonicalization keystone + its decision.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the parent does the unified registration). -/

namespace FX1PolyAudit

-- the parallel pair the smokes live over
#assert_no_axioms FX1Poly.Tier0.adjunctionIdentityLeft
#assert_no_axioms FX1Poly.Tier0.adjunctionIdentityRight
#assert_no_axioms FX1Poly.Tier0.adjunctionCupAtLeft
#assert_no_axioms FX1Poly.Tier0.adjunctionCupAtRight

-- ★ the no-go: the variance is GLOBAL (locally-indistinguishable cups)
#assert_no_axioms FX1Poly.Tier0.arcMatching_cupAtoms_locallyIndistinguishable

-- ★ the headline: matchingOf is the correct saturated carrier (each rfl)
#assert_no_axioms FX1Poly.Tier0.matchingOf_triangleLeft
#assert_no_axioms FX1Poly.Tier0.matchingOf_triangleRight
#assert_no_axioms FX1Poly.Tier0.matchingOf_resolves_embeddedTipCap
#assert_no_axioms FX1Poly.Tier0.matchingOf_strictlyBetterThanFolds_onEmbeddedTipCap
#assert_no_axioms FX1Poly.Tier0.matchingOf_distinguishes_faces

-- soundness piece: whisker exchange (same-spine)
#assert_no_axioms FX1Poly.Tier0.matchingOf_whiskerExchange

-- ★ the SOUNDNESS direction, PROVEN modulo exactly two named residuals
#assert_no_axioms FX1Poly.Tier0.MatchingSaturatedCongruence
#assert_no_axioms FX1Poly.Tier0.saturatedConv_matchingOf_eq
#assert_no_axioms FX1Poly.Tier0.saturatedMatchingCanonicalization_of

-- the saturated canonicalization keystone carried by matchingOf + its decision
#assert_no_axioms FX1Poly.Tier0.SaturatedMatchingCanonicalization
#assert_no_axioms FX1Poly.Tier0.decideSaturatedConvViaMatching
#assert_no_axioms FX1Poly.Tier0.adjunctionSaturatedWordProblemModuloMatching
#assert_no_axioms FX1Poly.Tier0.decideSaturated_leftSnake_matchingsAgree

-- honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSaturatedMatchingCanonicalizationCarrier
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSaturatedMatchingCanonicalization

end FX1PolyAudit
