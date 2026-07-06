import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupOrbitFreshSeedTails

/-! # FX1PolyAudit/…/ArcCupOrbitFreshSeedTails — zero-axiom gate

Per-declaration zero-axiom gate for the cup orbit witness assembled from the fresh-seed tails
equality: the located data + window pin + arc-tails equality at the `bottomCount + 2` seed give the
full `ArcCupOrbitWitness` directly, bridged by `arcCupHeadCodBoundaryGrows` (`codBoundaryLength =
bottomCount + 2`), with no folded diagram / count / internal legs — the folded campaign's terminal
premise wired straight to the witness.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupOrbitWitness_ofFreshSeedTails
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupOrbitFreshSeedTails

end FX1PolyAudit
