import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.CrossedModuleCyclicThree

/-! # FX1PolyAudit/Polygraph/Homology/CrossedModuleCyclicThree — zero-axiom gate (the free crossed
    module of `⟨s | s³⟩`: pre-crossed carrier, the boundary into the free group, the Peiffer congruence,
    the rotation identity `ζ ∈ ker ∂`, the proper-power hypothesis, and the abelianized-shadow bridge)

Per-declaration zero-axiom gate for the WP-2GROUP r1 crossed-module footing (#2199): the
`ConjugatedRelator` carrier and `relatorWord` / `invGen`, the free-group boundary
`conjugatedRelatorBoundary` / `partialBoundary` (`partialBoundaryIsReduced`), the `PeifferEquiv`
congruence and `peifferConjugate` with the concrete coherence hand-diff, ★★ the rotation identity
`rotationIdentityWitness` and `rotationIdentityBoundaryVanishes` (`∂ζ = []`), the proper-power
certificate, the `exponentSum` abelianized shadow and its two down-payments, and the honest `pi_2 ≠ 0`
ledger.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.ConjugatedRelator
#assert_no_axioms FX1Poly.Polygraph.Homology.relatorWord
#assert_no_axioms FX1Poly.Polygraph.Homology.invGen
#assert_no_axioms FX1Poly.Polygraph.Homology.conjugatedRelatorBoundary
#assert_no_axioms FX1Poly.Polygraph.Homology.partialBoundary
#assert_no_axioms FX1Poly.Polygraph.Homology.partialBoundaryIsReduced
#assert_no_axioms FX1Poly.Polygraph.Homology.peifferConjugate
#assert_no_axioms FX1Poly.Polygraph.Homology.PeifferEquiv
#assert_no_axioms FX1Poly.Polygraph.Homology.peifferProbeFirst
#assert_no_axioms FX1Poly.Polygraph.Homology.peifferProbeSecond
#assert_no_axioms FX1Poly.Polygraph.Homology.peifferMovePreservesBoundary
#assert_no_axioms FX1Poly.Polygraph.Homology.peifferMoveProbeBoundaryValue
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationIdentityWitness
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationIdentityBoundaryVanishes
#assert_no_axioms FX1Poly.Polygraph.Homology.wordPower
#assert_no_axioms FX1Poly.Polygraph.Homology.ProperPowerCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeRelatorProperPower
#assert_no_axioms FX1Poly.Polygraph.Homology.exponentSum
#assert_no_axioms FX1Poly.Polygraph.Homology.relatorAbelianShadowIsThree
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationIdentityAbelianShadowVanishes
#assert_no_axioms FX1Poly.Polygraph.Homology.NonTrivialityObligationStatus
#assert_no_axioms FX1Poly.Polygraph.Homology.CrossedModuleNonTrivialityLedger
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeNonTrivialityLedger
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleCyclicThreeFootingIsComplete

end FX1PolyAudit
