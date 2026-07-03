import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Computad.WordProblem

/-! # FX1PolyAudit/AuditTier0ModeComputadWordProblem — zero-axiom gate for mode-8

Per-declaration zero-axiom gate for `mode-8` (`FX1Poly/Tier0/Mode/ComputadWordProblem.lean`): the 2-computad
framing + free 2-category accessors, the dimension-1 free-monoid word-length homomorphism
(`ModalityPath.length_composePath`), the dimension-2 word length (`RawTwoCellExpr.generatorCount`) + its
conversion invariance + the sound distinguisher, the word-problem interface, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The 2-computad framing + free 2-category accessors
#assert_no_axioms FX1Poly.Polygraph.Computad.zeroCells
#assert_no_axioms FX1Poly.Polygraph.Computad.oneCellGenerator
#assert_no_axioms FX1Poly.Polygraph.Computad.twoCellGenerator
#assert_no_axioms FX1Poly.Polygraph.Computad.freeOneCell
#assert_no_axioms FX1Poly.Polygraph.Computad.freeTwoCell

-- Dimension-1: the free-monoid word-length homomorphism
#assert_no_axioms FX1Poly.Polygraph.ModalityPath.length_composePath

-- Dimension-2: the word length + its conversion invariance + the distinguisher
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.generatorCount
#assert_no_axioms FX1Poly.Polygraph.TwoCellStep.generatorCount_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellConv.generatorCount_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellConv.not_of_generatorCount_ne
#assert_no_axioms FX1Poly.Polygraph.adjunctionUnitThenId_generatorCount_eq_unit

-- The word-problem interface
#assert_no_axioms FX1Poly.Polygraph.Computad.twoCellWordProblem

-- Honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasComputadToOmegacEEncoding
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasConvergentTwoCellPresentation

end FX1PolyAudit
