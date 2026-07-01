import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellConvDecidable

/-! # FX1PolyAudit.Tier0.Mode.AdjunctionTwoCellConvDecidable — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the full `TwoCellConv` decision at the walking-adjunction seed, reduced to the
Godement residual: the Eckmann–Hilton non-degeneracy witness (interchange is NON-degenerate at the seed —
machine-checked distinct interchange-free normal forms of two `TwoCellConv`-related cells), and the full decision
assembled down to a single `residual` hypothesis (the conditional `Decidable (TwoCellConv …)` and its packaging as
`DecidableTwoCellConvFor`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.adjunctionIdentityTwoCellOnBase
#assert_no_axioms FX1Poly.Tier0.adjunctionIdentityTwoCellOnLeftRight
#assert_no_axioms FX1Poly.Tier0.adjunctionParallelUnitsRedex
#assert_no_axioms FX1Poly.Tier0.adjunctionParallelUnitsReduct
#assert_no_axioms FX1Poly.Tier0.adjunctionParallelUnitsInterchangeStep
#assert_no_axioms FX1Poly.Tier0.adjunctionParallelUnitsConv
#assert_no_axioms FX1Poly.Tier0.adjunctionParallelUnitsGeneratorCountEq
#assert_no_axioms FX1Poly.Tier0.adjunctionParallelUnitsNormalFormsDiffer
#assert_no_axioms FX1Poly.Tier0.adjunctionInterchangeIsNonDegenerate
#assert_no_axioms FX1Poly.Tier0.adjunctionDecidableTwoCellConvModuloResidual
#assert_no_axioms FX1Poly.Tier0.adjunctionTwoCellWordProblemModuloResidual
#assert_no_axioms FX1Poly.Tier0.fxMode_hasGodementResidualDecision

end FX1PolyAudit
