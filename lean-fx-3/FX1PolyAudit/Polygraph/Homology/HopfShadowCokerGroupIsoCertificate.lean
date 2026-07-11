import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.HopfShadowCokerGroupIsoCertificate

/-! # FX1PolyAudit/Polygraph/Homology/HopfShadowCokerGroupIsoCertificate — zero-axiom gate (the LITERAL
    coker group iso `coker M -> ZZ/3` as a setoid normal form, no `Quot`)

Per-declaration zero-axiom gate for TOWER-ANICK r8 (#2144): the coker normal form / representative /
section / class distinctness, the `ZmodThree` and `Nat`-residue scaffold, the KEYSTONE `intResidue3Add`
(mod-3 additivity over `Int`) with its `subNatNat` law, the group-hom addition law, the well-definedness
(respects) lemma, and the r8 ledger markers (the reflects residual and the node-one completion marker).

The `#assert_no_axioms` macro is fuel-based (`DependencyAudit`); as an INDEPENDENT cross-check the
load-bearing theorems are ALSO checked with the core `#print axioms` command (which does not truncate) —
each must report "does not depend on any axioms".

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  The iso is SETOID-based (explicit `nf` + round-trips), never `Quot`. -/

namespace FX1PolyAudit

-- BRICK A: normal form, representative, section, class distinctness
#assert_no_axioms FX1Poly.Polygraph.Homology.natResidue3
#assert_no_axioms FX1Poly.Polygraph.Homology.intResidue3
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerRep
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerNormalFormRepZeroProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerNormalFormGeneratorOneProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerNormalFormGeneratorTwoProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerNormalFormLargeProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerNormalFormNegativeProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerSectionRoundTrip
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerRepsAreDistinctZeroOne
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerRepsAreDistinctOneTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerRepsAreDistinctZeroTwo

-- BRICK B: the ZmodThree / Nat-residue scaffold
#assert_no_axioms FX1Poly.Polygraph.Homology.addZmod3Comm
#assert_no_axioms FX1Poly.Polygraph.Homology.negZmod3AddDistrib
#assert_no_axioms FX1Poly.Polygraph.Homology.natResidue3Succ
#assert_no_axioms FX1Poly.Polygraph.Homology.natResidue3Add
#assert_no_axioms FX1Poly.Polygraph.Homology.addZmod3ShiftBalance

-- BRICK C: the keystone and the three-multiple
#assert_no_axioms FX1Poly.Polygraph.Homology.natResidueSubStepBridge
#assert_no_axioms FX1Poly.Polygraph.Homology.intResidue3SubNatNat
#assert_no_axioms FX1Poly.Polygraph.Homology.natAddTwoBridge
#assert_no_axioms FX1Poly.Polygraph.Homology.intResidue3Add
#assert_no_axioms FX1Poly.Polygraph.Homology.natResidue3ThreeMul
#assert_no_axioms FX1Poly.Polygraph.Homology.intResidue3ThreeMultiple

-- BRICK D: rearrangements, group-hom addition law, well-definedness
#assert_no_axioms FX1Poly.Polygraph.Homology.intAddSwapMiddleLocal
#assert_no_axioms FX1Poly.Polygraph.Homology.intAddSubAddRearrange
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerPairAdd
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerAdditionLaw
#assert_no_axioms FX1Poly.Polygraph.Homology.intAddSubCancelLeft
#assert_no_axioms FX1Poly.Polygraph.Homology.intCrossSubRearrange
#assert_no_axioms FX1Poly.Polygraph.Homology.threeTimesRightExpand
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerRel
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerWitnessAlgebra
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerNormalFormRespects

-- the r8 ledger markers
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowCokerGroupIsoReflectsIsNamedNode
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowCokerGroupIsoNodeOneIsComplete

/-! ### Independent `#print axioms` cross-check for the load-bearing decls (not trusting the fuel-based
    macro alone) — each must report "does not depend on any axioms". -/

#print axioms FX1Poly.Polygraph.Homology.cokerSectionRoundTrip
#print axioms FX1Poly.Polygraph.Homology.natResidue3Add
#print axioms FX1Poly.Polygraph.Homology.intResidue3SubNatNat
#print axioms FX1Poly.Polygraph.Homology.intResidue3Add
#print axioms FX1Poly.Polygraph.Homology.intResidue3ThreeMultiple
#print axioms FX1Poly.Polygraph.Homology.cokerAdditionLaw
#print axioms FX1Poly.Polygraph.Homology.cokerNormalFormRespects

end FX1PolyAudit
