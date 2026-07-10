import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.FrobeniusSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.FrobeniusSeed — zero-axiom gate for the symbolic Frobenius spider
congruence + the SUFFIX-congruence corollary (POLY-TAB r0, T3b, the FALSIFIABILITY CHECK).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.FrobeniusMode
#assert_no_axioms FX1Poly.Polygraph.FrobeniusModality
#assert_no_axioms FX1Poly.Polygraph.frobeniusGraph
#assert_no_axioms FX1Poly.Polygraph.frobeniusT
#assert_no_axioms FX1Poly.Polygraph.frobeniusTThenT
#assert_no_axioms FX1Poly.Polygraph.FrobeniusTwoCell
#assert_no_axioms FX1Poly.Polygraph.frobeniusModeSignature
#assert_no_axioms FX1Poly.Polygraph.frobeniusMultCell
#assert_no_axioms FX1Poly.Polygraph.frobeniusComultCell
#assert_no_axioms FX1Poly.Polygraph.frobeniusUnitCell
#assert_no_axioms FX1Poly.Polygraph.frobeniusCounitCell
#assert_no_axioms FX1Poly.Polygraph.frobeniusIdTCell
#assert_no_axioms FX1Poly.Polygraph.frobeniusUnitLeftCell
#assert_no_axioms FX1Poly.Polygraph.frobeniusLeftLhsCell
#assert_no_axioms FX1Poly.Polygraph.frobeniusRightLhsCell
#assert_no_axioms FX1Poly.Polygraph.frobeniusHCell
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpecialCell
#assert_no_axioms FX1Poly.Polygraph.FrobeniusLawRel
#assert_no_axioms FX1Poly.Polygraph.frobeniusUnitLeftHolds
#assert_no_axioms FX1Poly.Polygraph.frobeniusFrobLeftHolds
#assert_no_axioms FX1Poly.Polygraph.frobeniusFrobRightHolds
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpecialHolds
#assert_no_axioms FX1Poly.Polygraph.frobeniusOrientationsCohere
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderConv_suffixCongruence
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderConv_prefixCongruence
#assert_no_axioms FX1Poly.Polygraph.frobeniusSuffixCongruence_nonVacuous
#assert_no_axioms FX1Poly.Polygraph.frobeniusConstInvariant_fold
#assert_no_axioms FX1Poly.Polygraph.fxTab_hasFrobeniusSymbolicCongruence
#assert_no_axioms FX1Poly.Polygraph.fxTab_frobeniusSuffixCongruenceFallsOut

end FX1PolyAudit
