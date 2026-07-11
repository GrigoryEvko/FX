import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPureCapSpineSort

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringPureCapSpineSort — zero-axiom gate
(FC-3 r18, THE CAP-DUAL)

Per-declaration zero-axiom gate for the pure-cap sort machinery ported to the adjoint-triple seed: the string cap
arity kit (`stringCupAtomCount_ofAllCapArity`, `stringCapAtomCount_ofAllCapArity`,
`stringAllCapArity_ofCupAtomCountZero`, `stringAllCapArity_ofCons`, `stringHeadCapArity`), the arc
count/transfer/base clones (`stringAllCapArity_ofArcEqualToPureCap`, `stringPureCapSpines_sameLength_ofArcEqual`,
`stringPureCapSpine_sort_nil`), the cap word pin (`stringCapAtom_eq_of_sharedDom_sameWindow`), the fuel-driver
skeleton assembled modulo the named residual (`stringPureCapSpine_sort` — which transitively gates the private
fueled helper `stringPureCapSpineSortFueled` and the private count reflections `stringCapCountReflect` /
`stringCupCountReflect`), the five concrete truth-probes, and the marker.  Each must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringCupAtomCount_ofAllCapArity
#assert_no_axioms FX1Poly.Polygraph.stringCapAtomCount_ofAllCapArity
#assert_no_axioms FX1Poly.Polygraph.stringAllCapArity_ofCupAtomCountZero
#assert_no_axioms FX1Poly.Polygraph.stringAllCapArity_ofCons
#assert_no_axioms FX1Poly.Polygraph.stringHeadCapArity
#assert_no_axioms FX1Poly.Polygraph.stringAllCapArity_ofArcEqualToPureCap
#assert_no_axioms FX1Poly.Polygraph.stringPureCapSpines_sameLength_ofArcEqual
#assert_no_axioms FX1Poly.Polygraph.stringPureCapSpine_sort_nil
#assert_no_axioms FX1Poly.Polygraph.stringCapAtom_eq_of_sharedDom_sameWindow
#assert_no_axioms FX1Poly.Polygraph.stringPureCapSpine_sort
#assert_no_axioms FX1Poly.Polygraph.stringProbeCapAtom_pinFires
#assert_no_axioms FX1Poly.Polygraph.stringProbeThreeCap_allCap
#assert_no_axioms FX1Poly.Polygraph.stringProbeThreeCap_headArity
#assert_no_axioms FX1Poly.Polygraph.stringProbeThreeCap_transferReflexive
#assert_no_axioms FX1Poly.Polygraph.stringProbeThreeCap_sameLengthReflexive
#assert_no_axioms FX1Poly.Polygraph.stringProbeCapSortNilFires
#assert_no_axioms FX1Poly.Polygraph.fxString_hasMidZeroValleyCapSort

end FX1PolyAudit
