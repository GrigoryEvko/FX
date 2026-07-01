import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.InterchangeFreeLocalConfluence

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.InterchangeFreeLocalConfluence — zero-axiom gate (mode-3 floor)

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

-- ★ Whisker-source step reflection (the composePath-index-sidestepping inversion)
#assert_no_axioms FX1Poly.Tier0.whiskerLeftReflectGoal
#assert_no_axioms FX1Poly.Tier0.stepSatisfiesWhiskerLeftReflectGoal
#assert_no_axioms FX1Poly.Tier0.whiskerLeftStepReflect
#assert_no_axioms FX1Poly.Tier0.whiskerRightReflectGoal
#assert_no_axioms FX1Poly.Tier0.stepSatisfiesWhiskerRightReflectGoal
#assert_no_axioms FX1Poly.Tier0.whiskerRightStepReflect

-- ★ The main tiling + local confluence + unconditional confluence
#assert_no_axioms FX1Poly.Tier0.twoCellLocalJoin
#assert_no_axioms FX1Poly.Tier0.twoCellInterchangeFreeLocallyConfluent
#assert_no_axioms FX1Poly.Tier0.twoCellStepInterchangeFree_isConfluentUnconditional

end FX1PolyAudit
