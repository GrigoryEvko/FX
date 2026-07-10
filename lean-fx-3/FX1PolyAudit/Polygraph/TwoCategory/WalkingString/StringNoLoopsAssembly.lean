import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringNoLoopsAssembly

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringNoLoopsAssembly — zero-axiom gate (STRING-JOINT r2, B3)

Per-declaration zero-axiom gate for the no-loops ASSEMBLY (both walls glued): the generator word facts, the cap-window
cap-word projection, the cup-orient `codLabels` wrapper, the per-atom discipline preservation over the boundary word,
the combined `CapsDistinctAlongFold` fold, the UNCONDITIONAL no-loops theorem `stringMatchingOf_loops_zero` and its
non-vacuity witness, and the assembly-complete marker.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringCupGeneratorCodWord_isCupWord
#assert_no_axioms FX1Poly.Polygraph.stringCapGeneratorDomWord_isCapWord
#assert_no_axioms FX1Poly.Polygraph.stringCapWindow_isCapWord
#assert_no_axioms FX1Poly.Polygraph.stringOrientationDiscipline_stepCup_codLabels
#assert_no_axioms FX1Poly.Polygraph.stringOrientationDiscipline_stepAtom_ofWordChain
#assert_no_axioms FX1Poly.Polygraph.stringCapsDistinctAlongFold_ofWordChain
#assert_no_axioms FX1Poly.Polygraph.stringMatchingOf_loops_zero
#assert_no_axioms FX1Poly.Polygraph.stringMatchingOf_loops_zero_stringCrossLevelCell
#assert_no_axioms FX1Poly.Polygraph.fxString_hasNoLoopsAssemblyComplete

end FX1PolyAudit
