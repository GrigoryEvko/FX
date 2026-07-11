import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWidthZeroMixedSpeciesWitness

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringWidthZeroMixedSpeciesWitness — zero-axiom gate
(FC-3 r13, B1)

Per-declaration zero-axiom gate for the width-0 mixed-species witness: the two cup atoms
(`stringMixedBaseCup`, `stringMixedTipCup`), the spine (`stringMixedWidthZeroSpine`), the chain / arity / mode /
top-word facts, the packaged refutation (`stringWidthZeroMixedSpecies_exists`), and the marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringMixedBaseCup
#assert_no_axioms FX1Poly.Polygraph.stringMixedTipCup
#assert_no_axioms FX1Poly.Polygraph.stringMixedWidthZeroSpine
#assert_no_axioms FX1Poly.Polygraph.stringMixedWidthZeroSpine_chained
#assert_no_axioms FX1Poly.Polygraph.stringMixedWidthZeroSpine_allCup
#assert_no_axioms FX1Poly.Polygraph.stringMixedWidthZeroSpine_baseCup_mode
#assert_no_axioms FX1Poly.Polygraph.stringMixedWidthZeroSpine_tipCup_mode
#assert_no_axioms FX1Poly.Polygraph.stringMixedWidthZeroSpine_topWord
#assert_no_axioms FX1Poly.Polygraph.stringMixedWidthZeroSpine_topWord_length
#assert_no_axioms FX1Poly.Polygraph.stringWidthZeroMixedSpecies_exists
#assert_no_axioms FX1Poly.Polygraph.fxString_hasWidthZeroMixedSpeciesWitness

end FX1PolyAudit
