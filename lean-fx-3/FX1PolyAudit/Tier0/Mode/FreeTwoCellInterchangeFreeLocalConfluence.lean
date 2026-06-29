import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.FreeTwoCellInterchangeFreeLocalConfluence

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellInterchangeFreeLocalConfluence — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the critical-pair JOIN toolkit of the interchange-free 2-cell fragment:
joinability symmetry, the atomic-source step inversions, the pentagon join, the associativity/left-factor
join, and the two whisker-distribution joins. These discharge every genuine critical pair the fragment's local
confluence consumes.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- ★ Symmetry of joinability + the atomic-source step inversions
#assert_no_axioms FX1Poly.Tier0.joinableSymm
#assert_no_axioms FX1Poly.Tier0.stepFromIdentityCellIsImpossible
#assert_no_axioms FX1Poly.Tier0.stepFromGeneratorCellIsImpossible

-- ★ The pentagon critical-pair join
#assert_no_axioms FX1Poly.Tier0.pentagonCriticalPairJoins

-- ★ Associativity versus a step in the inner-left factor (covers the assoc critical-pair family)
#assert_no_axioms FX1Poly.Tier0.associativityLeftFactorStepJoins

-- ★ Whisker-distribution versus a step in the whiskered body
#assert_no_axioms FX1Poly.Tier0.whiskerLeftDistributionStepJoins
#assert_no_axioms FX1Poly.Tier0.whiskerRightDistributionStepJoins

end FX1PolyAudit
