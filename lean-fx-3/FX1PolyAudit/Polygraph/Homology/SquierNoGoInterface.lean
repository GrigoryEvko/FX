import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.SquierNoGoInterface

/-! # FX1PolyAudit/Polygraph/Homology/SquierNoGoInterface — zero-axiom gate (the honest Squier no-go
    INTERFACE: `HomologyPresentationInvariance` with the invariance gap explicit, the contrapositive
    `squierNoGoSchema`, the op-duality sign-invariance witness, the honest vacuity caveat, the `S_1`
    witness ledger with obligation 3's wall proved, and the #2139 round-one ledger)

Per-declaration zero-axiom gate for H2-SQUIER-NOGO r1 bricks B2 + B3 + B4.  Every declaration must be
free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.MonoidHandle
#assert_no_axioms FX1Poly.Polygraph.Homology.HomologyPresentationInvariance
#assert_no_axioms FX1Poly.Polygraph.Homology.squierNoGoSchema
#assert_no_axioms FX1Poly.Polygraph.Homology.carrierFinitelyGeneratedPredicate
#assert_no_axioms FX1Poly.Polygraph.Homology.everyCarrierInvariantIsFinitelyGenerated
#assert_no_axioms FX1Poly.Polygraph.Homology.squierNoGoAntecedentUnsatisfiableOverThisCarrier
#assert_no_axioms FX1Poly.Polygraph.Homology.comonadDegreeTwoSmithData
#assert_no_axioms FX1Poly.Polygraph.Homology.monadAndComonadBoundariesDiffer
#assert_no_axioms FX1Poly.Polygraph.Homology.monadAndComonadShareDegreeTwoInvariant
#assert_no_axioms FX1Poly.Polygraph.Homology.opDualityInvarianceInterface
#assert_no_axioms FX1Poly.Polygraph.Homology.opDualityInterfaceHasDistinctPresentations
#assert_no_axioms FX1Poly.Polygraph.Homology.squierNoGoConclusionIsNonVacuous
#assert_no_axioms FX1Poly.Polygraph.Homology.MonoidWitnessObligationStatus
#assert_no_axioms FX1Poly.Polygraph.Homology.SquierWitnessLedgerEntry
#assert_no_axioms FX1Poly.Polygraph.Homology.squierMonoidFiveGeneratorShape
#assert_no_axioms FX1Poly.Polygraph.Homology.squierMonoidFiveGeneratorShapeHasFiveGenerators
#assert_no_axioms FX1Poly.Polygraph.Homology.carrierDegreeThreeChainIsAlwaysFinite
#assert_no_axioms FX1Poly.Polygraph.Homology.squierWitnessLedger
#assert_no_axioms FX1Poly.Polygraph.Homology.squierNoGoRoundOneLedgerIsComplete
#assert_no_axioms FX1Poly.Polygraph.Homology.squierNoGoOpenedButNotClosed

end FX1PolyAudit
