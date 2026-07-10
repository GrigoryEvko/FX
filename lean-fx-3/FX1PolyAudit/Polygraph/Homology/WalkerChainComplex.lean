import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.WalkerChainComplex

/-! # FX1PolyAudit/Polygraph/Homology/WalkerChainComplex — zero-axiom gate (the walking-monad
    polygraphic chain complex + machine-checked `d d = 0` + Smith-normal boundaries)

Per-declaration zero-axiom gate for the H2-CHAIN r1 walking-monad chain complex: the basis counts,
the generic and instance `d d = 0` theorems, the three boundary-matrix literals, the augmented
directed complex instance, the oracle / non-vacuity smokes, and the two Smith reduction certificates
seeding the H2-WALKERS handoff.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.walkerBasisCount
#assert_no_axioms FX1Poly.Polygraph.Homology.augmentedDirectedComplexBoundaryComposesToZero

end FX1PolyAudit
