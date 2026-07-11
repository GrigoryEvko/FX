import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.HopfShadowCokerGroupIsoReflectsCertificate

/-! # FX1PolyAudit/Polygraph/Homology/HopfShadowCokerGroupIsoReflectsCertificate — zero-axiom gate (the
    REFLECTS converse, the retraction, and the two-sided setoid iso `coker M ~= ZZ/3`, no `Quot`)

Per-declaration zero-axiom gate for TOWER-ANICK r9 (#2144): the `ZmodThree` negation facts, the residue of
a negation / a difference, the CONSTRUCTIVE div-by-3 extraction (`natResidue3ZeroDivides` /
`intResidue3ZeroDivides`), the two subtractive keystones, the witness-component identities
(`reflectsFirst` / `reflectsSecond`), THE REFLECTS (injectivity) direction `cokerNormalFormReflects`, the
retraction `cokerRetractionRoundTrip`, the concrete truth-probes, and the r9 ledger markers.

The `#assert_no_axioms` macro is fuel-based (`DependencyAudit`); as an INDEPENDENT cross-check the
load-bearing theorems are ALSO checked with the core `#print axioms` command (which does not truncate) —
each must report "does not depend on any axioms".

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  The two-sided iso is SETOID-based (explicit `nf` + both round-trips), never
`Quot`. -/

namespace FX1PolyAudit

-- BRICK 1: the ZmodThree negation facts
#assert_no_axioms FX1Poly.Polygraph.Homology.negZmod3Involutive
#assert_no_axioms FX1Poly.Polygraph.Homology.negZmod3EqZeroImpliesZero

-- BRICK 2: the residue of a negation and of a difference
#assert_no_axioms FX1Poly.Polygraph.Homology.intResidue3Neg
#assert_no_axioms FX1Poly.Polygraph.Homology.intResidue3Sub

-- BRICK 3: the constructive div-by-3 extraction
#assert_no_axioms FX1Poly.Polygraph.Homology.natResidue3ZeroDivides
#assert_no_axioms FX1Poly.Polygraph.Homology.intResidue3ZeroDivides

-- BRICK 4: the two subtractive keystones
#assert_no_axioms FX1Poly.Polygraph.Homology.intSubAddCancel
#assert_no_axioms FX1Poly.Polygraph.Homology.intSubSubCancel
#assert_no_axioms FX1Poly.Polygraph.Homology.intSubSubMerge

-- BRICK 5: the witness-component identities
#assert_no_axioms FX1Poly.Polygraph.Homology.reflectsFirst
#assert_no_axioms FX1Poly.Polygraph.Homology.reflectsSecond

-- BRICK 6: the reflects direction, the retraction, the concrete probes
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerNormalFormReflects
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerRetractionRoundTrip
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerRelConcreteWitnessProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerRelNegativeWitnessProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerReflectsConcreteProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerReflectsNegativeProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.cokerReflectsLargeProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.intResidue3ZeroDividesConcreteProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.intResidue3ZeroDividesNegativeProbe

-- the r9 ledger markers
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowCokerGroupIsoReflectsIsComplete
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowCokerGroupIsoTwoSidedIsComplete

/-! ### Independent `#print axioms` cross-check for the load-bearing decls (not trusting the fuel-based
    macro alone) — each must report "does not depend on any axioms". -/

#print axioms FX1Poly.Polygraph.Homology.intResidue3Neg
#print axioms FX1Poly.Polygraph.Homology.intResidue3Sub
#print axioms FX1Poly.Polygraph.Homology.natResidue3ZeroDivides
#print axioms FX1Poly.Polygraph.Homology.intResidue3ZeroDivides
#print axioms FX1Poly.Polygraph.Homology.reflectsFirst
#print axioms FX1Poly.Polygraph.Homology.reflectsSecond
#print axioms FX1Poly.Polygraph.Homology.cokerNormalFormReflects
#print axioms FX1Poly.Polygraph.Homology.cokerRetractionRoundTrip

end FX1PolyAudit
