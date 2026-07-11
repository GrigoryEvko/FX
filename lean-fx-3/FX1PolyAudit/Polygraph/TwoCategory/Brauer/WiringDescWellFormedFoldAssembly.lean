import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescWellFormedFoldAssembly

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescWellFormedFoldAssembly — zero-axiom gate (BRAUER r20)

Per-declaration zero-axiom gate for the `WellFormedBrauerFold` word-assembly + the per-phase window-fit discharge:
the word-level append-split (`wellFormedBrauerFold_append` / `_appendSplit`), the eval-first through-strand
cross-phase connectivity probe (`throughStrandConnects_probe`), the four per-phase discharge lemmas
(`wellFormedBrauerFold_crossingWord` / `_cupWord` / `_capZeros` / `_circleWord`), the six-phase reduction
(`wellFormedBrauerFold_standardFormWordExt5_ofPhases`), the full corrected-word coverage on both r19 witnesses, the
wild-diagram exercise of the honest corrected target, and the honesty markers + the #2013 endgame WALL ledger.

Independent `#print axioms` (in a scratch during development) reported every decl as "does not depend on any
axioms".  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- B1: the word-level append law + the eval-first through-strand cross-phase connectivity probe
#assert_no_axioms FX1Poly.Polygraph.wellFormedBrauerFold_append
#assert_no_axioms FX1Poly.Polygraph.wellFormedBrauerFold_appendSplit
#assert_no_axioms FX1Poly.Polygraph.throughStrandConnects_probe

-- B2: the four per-phase discharge lemmas + the six-phase reduction + the full corrected-word coverage
#assert_no_axioms FX1Poly.Polygraph.wellFormedBrauerFold_crossingWord
#assert_no_axioms FX1Poly.Polygraph.wellFormedBrauerFold_cupWord
#assert_no_axioms FX1Poly.Polygraph.wellFormedBrauerFold_capZeros
#assert_no_axioms FX1Poly.Polygraph.wellFormedBrauerFold_circleWord
#assert_no_axioms FX1Poly.Polygraph.wellFormedBrauerFold_standardFormWordExt5_ofPhases
#assert_no_axioms FX1Poly.Polygraph.wellFormedBrauerFold_phaseLemmas_fire
#assert_no_axioms FX1Poly.Polygraph.wellFormedBrauerFold_correctedWord_adversarialB
#assert_no_axioms FX1Poly.Polygraph.wellFormedBrauerFold_correctedWord_nestedCups

-- B3: the fresh wild diagrams + their involution witnesses + the honest corrected target exercise
#assert_no_axioms FX1Poly.Polygraph.wildThroughDiagram
#assert_no_axioms FX1Poly.Polygraph.wildCupLoopDiagram
#assert_no_axioms FX1Poly.Polygraph.wildCapThroughDiagram
#assert_no_axioms FX1Poly.Polygraph.wildCrossThroughDiagram
#assert_no_axioms FX1Poly.Polygraph.isBoundaryInvolution_wildThrough
#assert_no_axioms FX1Poly.Polygraph.isBoundaryInvolution_wildCupLoop
#assert_no_axioms FX1Poly.Polygraph.foldRealizesTargetDiagramCorrected_wildThrough
#assert_no_axioms FX1Poly.Polygraph.foldRealizesTargetDiagramCorrected_wildCupLoop
#assert_no_axioms FX1Poly.Polygraph.foldRealizesTargetDiagramCorrected_wildCapThrough
#assert_no_axioms FX1Poly.Polygraph.foldRealizesTargetDiagramCorrected_wildCrossThrough
#assert_no_axioms FX1Poly.Polygraph.foldRealizesTargetDiagramCorrected_wildBundle

-- B4 / B5: the honesty markers + the #2013 endgame WALL ledger
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWellFormedFoldAppendSplit
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWellFormedFoldPhaseDischarge
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCorrectedTargetWildExercise
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWellFormedFoldGeneralAssembly

end FX1PolyAudit
