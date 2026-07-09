import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanStaircaseDriver

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringFussCatalanStaircaseDriver — zero-axiom gate (FC-7)

Per-declaration zero-axiom gate for the FC-7 staircase driver: the spine-tag redex LOCATOR
(`locateAdjacentCupThenCap` / `locateStringStaircaseRedex`), the `IsStaircaseNormal` predicate + its `Decidable`
instance, the soundness/completeness bridge (`stringStaircaseLocate_none_iff_normal` /
`stringStaircaseLocate_some_exposesRedex`, transitively covering the private reduction/induction helpers), the descent
STEP (`stringStaircaseSwap` / `stringStaircaseStep_dropsDisorder`), the non-vacuity witnesses, and — the P3 wall — the
machine-witnessed pinning finding `stringStaircaseNormalForm_not_matchingDetermined` and the two honesty markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.locateAdjacentCupThenCap
#assert_no_axioms FX1Poly.Polygraph.locateStringStaircaseRedex
#assert_no_axioms FX1Poly.Polygraph.IsStaircaseNormal
#assert_no_axioms FX1Poly.Polygraph.instDecidableIsStaircaseNormal
#assert_no_axioms FX1Poly.Polygraph.locateAdjacentCupThenCap_none_imp_valley
#assert_no_axioms FX1Poly.Polygraph.locateAdjacentCupThenCap_valley_imp_none
#assert_no_axioms FX1Poly.Polygraph.stringStaircaseLocate_none_iff_normal
#assert_no_axioms FX1Poly.Polygraph.stringStaircaseLocate_some_exposesRedex
#assert_no_axioms FX1Poly.Polygraph.stringStaircaseSwap
#assert_no_axioms FX1Poly.Polygraph.stringStaircaseStep_dropsDisorder
#assert_no_axioms FX1Poly.Polygraph.stringIdentityF_isStaircaseNormal
#assert_no_axioms FX1Poly.Polygraph.stringSnakeF_not_isStaircaseNormal
#assert_no_axioms FX1Poly.Polygraph.stringIdentityG_vcomp_isStaircaseNormal
#assert_no_axioms FX1Poly.Polygraph.stringIdentityG_matchingOf_vcomp_eq
#assert_no_axioms FX1Poly.Polygraph.stringIdentityG_ne_vcomp
#assert_no_axioms FX1Poly.Polygraph.stringStaircaseNormalForm_not_matchingDetermined
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStaircaseRedexLocator
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStaircaseDriverFold

end FX1PolyAudit
