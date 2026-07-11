import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.HopfShadowCokerSmithCertificate

/-! # FX1PolyAudit/Polygraph/Homology/HopfShadowCokerSmithCertificate — zero-axiom gate (the coker
    Smith-INVARIANT of the Hopf-shadow `(t-1)`-action matrix, backed by a machine-checked unimodular
    reduction certificate `M -> diag(1, 3)`)

Per-declaration zero-axiom gate for TOWER-ANICK r7 (#2144): the Smith normal form and the hand-written
checked reduction word, the `IsSmithNormalFormWithin` proof, the assembled reduction certificate and its
checked reduction claim, and the coker `SmithHomologyData` read-off `<0, [3]> = H_1(cyclic-3)`, plus the
r7 ledger markers (the literal group iso residual `hopfShadowCokerGroupIsoIsNamedNode` and the completion
marker).

The `#assert_no_axioms` macro is fuel-based (`DependencyAudit`); as an INDEPENDENT cross-check the
load-bearing theorems are ALSO checked with the core `#print axioms` command (which does not truncate) —
each must report "does not depend on any axioms".

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- the Smith normal form + the hand-written checked reduction certificate
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowReductionWord
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowReductionProducesSmithForm
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowSmithNormalFormIsSmith

-- the reduction certificate and its checked reduction claim
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowCertificateReducesToSmithForm

-- the coker homology data and the ZZ/3 invariant read-off
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowCokerData
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowCokerInvariantIsZmodThree
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowCokerMatchesCyclicThreeH1

-- the r7 ledger markers
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowCokerGroupIsoIsNamedNode
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowCokerSmithCertificateIsComplete

/-! ### Independent `#print axioms` cross-check for the load-bearing decls (not trusting the fuel-based
    macro alone) — each must report "does not depend on any axioms". -/

#print axioms FX1Poly.Polygraph.Homology.hopfShadowReductionProducesSmithForm
#print axioms FX1Poly.Polygraph.Homology.hopfShadowSmithNormalFormIsSmith
#print axioms FX1Poly.Polygraph.Homology.hopfShadowCertificateReducesToSmithForm
#print axioms FX1Poly.Polygraph.Homology.hopfShadowCokerInvariantIsZmodThree
#print axioms FX1Poly.Polygraph.Homology.hopfShadowCokerMatchesCyclicThreeH1

end FX1PolyAudit
