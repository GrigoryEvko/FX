import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingOperad.OperadTreeSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingOperad.OperadTreeSeed — zero-axiom gate (the walking monoid operad signature + tree-pasting relation)

Per-declaration zero-axiom gate for the walking monoid operad seed: the `OperadTree` carrier, the
`OperadGenerator` generators + their `generatorArity`, the arity-slot `OperadSignature` /
`monoidOperadSignature` and their smokes, the concrete sample trees, and the monoid-law tree-pasting
`OperadTreeConv` convertibility with its associativity / left-unit / right-unit / whiskered witnesses.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.OperadTree
#assert_no_axioms FX1Poly.Polygraph.OperadGenerator
#assert_no_axioms FX1Poly.Polygraph.generatorArity
#assert_no_axioms FX1Poly.Polygraph.generatorArity_mul
#assert_no_axioms FX1Poly.Polygraph.generatorArity_unit
#assert_no_axioms FX1Poly.Polygraph.OperadSignature
#assert_no_axioms FX1Poly.Polygraph.monoidOperadSignature
#assert_no_axioms FX1Poly.Polygraph.monoidOperadSignature_two
#assert_no_axioms FX1Poly.Polygraph.monoidOperadSignature_zero
#assert_no_axioms FX1Poly.Polygraph.monoidOperadSignature_one
#assert_no_axioms FX1Poly.Polygraph.monoidOperadSignature_three
#assert_no_axioms FX1Poly.Polygraph.operadAssocLeftTree
#assert_no_axioms FX1Poly.Polygraph.operadAssocRightTree
#assert_no_axioms FX1Poly.Polygraph.operadUnitLeftTree
#assert_no_axioms FX1Poly.Polygraph.operadUnitRightTree
#assert_no_axioms FX1Poly.Polygraph.OperadTreeConv
#assert_no_axioms FX1Poly.Polygraph.operadAssocHolds
#assert_no_axioms FX1Poly.Polygraph.operadUnitLeftHolds
#assert_no_axioms FX1Poly.Polygraph.operadUnitRightHolds
#assert_no_axioms FX1Poly.Polygraph.operadUnitLeftWhiskeredHolds

end FX1PolyAudit
