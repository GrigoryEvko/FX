import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringEmptyMidSurvivorIdentity

/-! # FX1PolyAudit.…WalkingString.StringEmptyMidSurvivorIdentity — zero-axiom gate (FC-3 r44, P2c partial)

Per-declaration zero-axiom gate for the empty-mid matching survivor-identity base floor + its no-forward-
chord corollary + the concrete-matching certificate + the three fires.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  The fuel-based `#assert_no_axioms` here is
cross-checked by the raw `#print axioms` in the sibling `...AxiomWitness` file. -/

namespace FX1PolyAudit

-- ★ the base-floor invariant (matching-carrier port of the arc initialPartner_topPort_lt)
#assert_no_axioms FX1Poly.Polygraph.emptyMidMatching_topPort_lt

-- the LOCATE-base-case corollary
#assert_no_axioms FX1Poly.Polygraph.emptyMidMatching_noForwardChord

-- the named invariant at the string signature
#assert_no_axioms FX1Poly.Polygraph.stringEmptyMidMatching_isSurvivorIdentity

-- the concrete-matching certificate (anti-vacuity) + the three fires
#assert_no_axioms FX1Poly.Polygraph.stringEmptyMidMatching_partnerComputesAtMidTwo
#assert_no_axioms FX1Poly.Polygraph.stringEmptyMidMatching_survivorIdentity_firesAtMidTwo
#assert_no_axioms FX1Poly.Polygraph.stringEmptyMidMatching_noForwardChord_firesAtMidTwo

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxString_hasEmptyMidSurvivorIdentity

end FX1PolyAudit
