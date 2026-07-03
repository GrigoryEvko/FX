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
#assert_no_axioms FX1Poly.Polygraph.adjunctionIdentityLeft
#assert_no_axioms FX1Poly.Polygraph.adjunctionIdentityRight
#assert_no_axioms FX1Poly.Polygraph.adjunctionCupAtLeft
#assert_no_axioms FX1Poly.Polygraph.adjunctionCupAtRight

-- ★ the no-go: the variance is GLOBAL (locally-indistinguishable cups)
#assert_no_axioms FX1Poly.Polygraph.arcMatching_cupAtoms_locallyIndistinguishable

-- ★ the headline: matchingOf is the correct saturated carrier (each rfl)
#assert_no_axioms FX1Poly.Polygraph.matchingOf_triangleLeft
#assert_no_axioms FX1Poly.Polygraph.matchingOf_triangleRight
#assert_no_axioms FX1Poly.Polygraph.matchingOf_resolves_embeddedTipCap
#assert_no_axioms FX1Poly.Polygraph.matchingOf_strictlyBetterThanFolds_onEmbeddedTipCap
#assert_no_axioms FX1Poly.Polygraph.matchingOf_distinguishes_faces

-- soundness piece: whisker exchange (same-spine)
#assert_no_axioms FX1Poly.Polygraph.matchingOf_whiskerExchange

-- ★ the SOUNDNESS direction, PROVEN modulo exactly two named residuals
#assert_no_axioms FX1Poly.Polygraph.MatchingSaturatedCongruence
#assert_no_axioms FX1Poly.Polygraph.saturatedConv_matchingOf_eq
#assert_no_axioms FX1Poly.Polygraph.saturatedMatchingCanonicalization_of

-- the saturated canonicalization keystone carried by matchingOf + its decision
#assert_no_axioms FX1Poly.Polygraph.SaturatedMatchingCanonicalization
#assert_no_axioms FX1Poly.Polygraph.decideSaturatedConvViaMatching
#assert_no_axioms FX1Poly.Polygraph.adjunctionSaturatedWordProblemModuloMatching
#assert_no_axioms FX1Poly.Polygraph.decideSaturated_leftSnake_matchingsAgree

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSaturatedMatchingCanonicalizationCarrier
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSaturatedMatchingCanonicalization

end FX1PolyAudit
