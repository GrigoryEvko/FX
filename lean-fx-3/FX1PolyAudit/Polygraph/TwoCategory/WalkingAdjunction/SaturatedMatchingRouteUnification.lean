import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingRouteUnification

/-! # FX1PolyAudit/…/SaturatedMatchingRouteUnification — zero-axiom gate

Per-declaration zero-axiom gate for the unification of the two fib-3 keystone completeness routes: the
reduction `matchingReductsShareSpineTrace_ofMatchingStaircase` (the canonical-cell residual
`CanonicalMatchingStaircaseData` yields the existence residual `MatchingReductsShareSpineTrace`) must be
free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega` — so the derivation
that closing `MatchingStaircaseReconstructs` closes BOTH shipped keystone routes is itself clean. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingReductsShareSpineTrace_ofMatchingStaircase
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingKeystoneRoutesUnified

end FX1PolyAudit
