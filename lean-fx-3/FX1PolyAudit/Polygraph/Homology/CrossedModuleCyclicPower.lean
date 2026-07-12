import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.CrossedModuleCyclicPower

/-! # FX1PolyAudit/Polygraph/Homology/CrossedModuleCyclicPower — zero-axiom gate (the general cyclic
    `⟨s | sⁿ⟩` boundary + `∂ζₙ = []` ∀ `n`, the proper-power certificate ∀ `n ≥ 2`, and the two-generator
    `⟨a, b | [a, b]⟩` opening with the H₂ cross-check star)

Per-declaration zero-axiom gate for WP-2GROUP r7 (#2199).  Every declaration must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## B1 — the exponent-parameterized boundary + the truth probes -/

#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicPowerRelator
#assert_no_axioms FX1Poly.Polygraph.Homology.conjugatedRelatorBoundaryAt
#assert_no_axioms FX1Poly.Polygraph.Homology.partialBoundaryAt
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicPowerConjugatorGen
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicPowerRelatorInverseGen
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicPowerRotationWitness
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicPowerRelatorThreeMatchesRelatorWord
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicPowerRotationWitnessMatchesShipped
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicPowerBoundaryThreeMatchesShipped
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationBoundaryVanishesAtTwoProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationBoundaryVanishesAtFiveProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationBoundaryVanishesAtZeroProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.powerConjugationCollapsesFourProbe

/-! ## B4a — the two-generator commutator carrier probes -/

#assert_no_axioms FX1Poly.Polygraph.Homology.commutatorRelator
#assert_no_axioms FX1Poly.Polygraph.Homology.commutatorBoundaryIsReduced
#assert_no_axioms FX1Poly.Polygraph.Homology.commutatorSelfInverseVanishes
#assert_no_axioms FX1Poly.Polygraph.Homology.distinctGeneratorsDoNotCancel
#assert_no_axioms FX1Poly.Polygraph.Homology.generatorCancelsOwnInverse

/-! ## B2 — the general theorem `∂ζₙ = []` ∀ `n` -/

#assert_no_axioms FX1Poly.Polygraph.Homology.signPowerExponentSumRelator
#assert_no_axioms FX1Poly.Polygraph.Homology.firstConjWordOverGenZero
#assert_no_axioms FX1Poly.Polygraph.Homology.powerConjugationCollapses
#assert_no_axioms FX1Poly.Polygraph.Homology.firstGenBoundaryExponent
#assert_no_axioms FX1Poly.Polygraph.Homology.secondGenBoundaryExponent
#assert_no_axioms FX1Poly.Polygraph.Homology.firstGenBoundaryOverGenZero
#assert_no_axioms FX1Poly.Polygraph.Homology.secondGenBoundaryOverGenZero
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationBoundaryVanishesAt

/-! ## B3 — the proper-power certificate ∀ `n ≥ 2` -/

#assert_no_axioms FX1Poly.Polygraph.Homology.signPowerPosIsWordPower
#assert_no_axioms FX1Poly.Polygraph.Homology.CyclicPowerProperPowerCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicPowerRelatorProperPower

/-! ## B4b — the H₂ cross-check star + the arc ledger -/

#assert_no_axioms FX1Poly.Polygraph.Homology.CyclicPowerObligationStatus
#assert_no_axioms FX1Poly.Polygraph.Homology.AbelianizedHomologyShadow
#assert_no_axioms FX1Poly.Polygraph.Homology.PiTwoStatus
#assert_no_axioms FX1Poly.Polygraph.Homology.H2CrossCheckRow
#assert_no_axioms FX1Poly.Polygraph.Homology.H2CrossCheckStar
#assert_no_axioms FX1Poly.Polygraph.Homology.h2CrossCheckStar
#assert_no_axioms FX1Poly.Polygraph.Homology.CyclicPowerArcLedger
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicPowerArcLedger
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleCyclicPowerArcIsComplete

end FX1PolyAudit
