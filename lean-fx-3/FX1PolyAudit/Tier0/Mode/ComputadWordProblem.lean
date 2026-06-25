import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.ComputadWordProblem

/-! # FX1PolyAudit/AuditTier0ModeComputadWordProblem — zero-axiom gate for mode-8

Per-declaration zero-axiom gate for `mode-8` (`FX1Poly/Tier0/Mode/ComputadWordProblem.lean`): the 2-computad
framing + free 2-category accessors, the dimension-1 free-monoid word-length homomorphism
(`ModalityPath.length_composePath`), the dimension-2 word length (`RawTwoCellExpr.generatorCount`) + its
conversion invariance + the sound distinguisher, the word-problem interface, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The 2-computad framing + free 2-category accessors
#assert_no_axioms FX1Poly.Tier0.Computad.zeroCells
#assert_no_axioms FX1Poly.Tier0.Computad.oneCellGenerator
#assert_no_axioms FX1Poly.Tier0.Computad.twoCellGenerator
#assert_no_axioms FX1Poly.Tier0.Computad.freeOneCell
#assert_no_axioms FX1Poly.Tier0.Computad.freeTwoCell

-- Dimension-1: the free-monoid word-length homomorphism
#assert_no_axioms FX1Poly.Tier0.ModalityPath.length_composePath

-- Dimension-2: the word length + its conversion invariance + the distinguisher
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.generatorCount
#assert_no_axioms FX1Poly.Tier0.TwoCellStep.generatorCount_eq
#assert_no_axioms FX1Poly.Tier0.TwoCellConv.generatorCount_eq
#assert_no_axioms FX1Poly.Tier0.TwoCellConv.not_of_generatorCount_ne
#assert_no_axioms FX1Poly.Tier0.adjunctionUnitThenId_generatorCount_eq_unit

-- The word-problem interface
#assert_no_axioms FX1Poly.Tier0.Computad.twoCellWordProblem

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasComputadToOmegacEEncoding
#assert_no_axioms FX1Poly.Tier0.fxMode_hasConvergentTwoCellPresentation

end FX1PolyAudit
