import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.ContextClosure

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.ContextClosure — zero-axiom gate for the generic
contextual-closure package + the invariant fold (POLY-TAB r0, T3a).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.contextClosureRel
#assert_no_axioms FX1Poly.Polygraph.Amalgam.contextClosureRel.ofRow
#assert_no_axioms FX1Poly.Polygraph.Amalgam.contextClosureRel.underPrefix
#assert_no_axioms FX1Poly.Polygraph.Amalgam.contextClosureRel.underSuffix
#assert_no_axioms FX1Poly.Polygraph.Amalgam.contextClosureRel.underVcompLeft
#assert_no_axioms FX1Poly.Polygraph.Amalgam.contextClosureRel.underVcompRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.contextClosureRel.isReflexive
#assert_no_axioms FX1Poly.Polygraph.Amalgam.contextClosureRel.isSymmetric
#assert_no_axioms FX1Poly.Polygraph.Amalgam.contextClosureRel.isTransitive
#assert_no_axioms FX1Poly.Polygraph.Amalgam.SaturatedConvOver.monotone
#assert_no_axioms FX1Poly.Polygraph.Amalgam.contextClosureRel.isIdempotent
#assert_no_axioms FX1Poly.Polygraph.Amalgam.SaturatedConvOver.suffixCongruence
#assert_no_axioms FX1Poly.Polygraph.Amalgam.SaturatedConvOver.prefixCongruence
#assert_no_axioms FX1Poly.Polygraph.Amalgam.rowConvInvariant_foldRel
#assert_no_axioms FX1Poly.Polygraph.Amalgam.rowConvInvariant_foldEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxTab_hasContextClosurePackage

end FX1PolyAudit
