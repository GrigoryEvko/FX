import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescSeamRungs

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescSeamRungs — zero-axiom gate

Per-declaration zero-axiom gate for the two BRAUER r37 SEAM RUNGS: the propext-clean length count appended
(`countAtoms_append` + the two drop lemmas `countAtoms_lt_append_cons2` / `countAtoms_lt_append_cons_afterHead`), the
SNAKE annihilation seam (`snakeAnnihilateFree8_cleanS1` / `_cleanS2` +
`legSink_snakeAnnihilate_underStandardPrefix` / `legSink_snakeAnnihilateMirror_underStandardPrefix`), the cup-UNTWIST
seam (`cupUntwistFree8_clean` / `legSink_cupUntwist_underStandardPrefix`), the snake-neighbor classifier
(`snakeNeighborKind`) and its truth-probed adjudication (`snakeNeighbor_probes` / `snakeAnnihilate_diagramSound` /
`snakeLoop_notEmptyWord`), the non-vacuity flagships (`legSnakePeel_demo` / `legUntwistPeel_demo`), the honesty
markers, and the machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — note `List.length_append`
and the stdlib `Nat.beq_refl` LEAK `propext` and are deliberately replaced by the structural `countAtoms` and by
closed-literal `Nat.beq` reductions.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.countAtoms_append
#assert_no_axioms FX1Poly.Polygraph.countAtoms_lt_append_cons2
#assert_no_axioms FX1Poly.Polygraph.countAtoms_lt_append_cons_afterHead
#assert_no_axioms FX1Poly.Polygraph.snakeAnnihilateFree8_cleanS1
#assert_no_axioms FX1Poly.Polygraph.snakeAnnihilateFree8_cleanS2
#assert_no_axioms FX1Poly.Polygraph.cupUntwistFree8_clean
#assert_no_axioms FX1Poly.Polygraph.legSink_snakeAnnihilate_underStandardPrefix
#assert_no_axioms FX1Poly.Polygraph.legSink_snakeAnnihilateMirror_underStandardPrefix
#assert_no_axioms FX1Poly.Polygraph.legSink_cupUntwist_underStandardPrefix
#assert_no_axioms FX1Poly.Polygraph.snakeNeighborKind
#assert_no_axioms FX1Poly.Polygraph.snakeNeighbor_probes
#assert_no_axioms FX1Poly.Polygraph.snakeAnnihilate_diagramSound
#assert_no_axioms FX1Poly.Polygraph.snakeLoop_notEmptyWord
#assert_no_axioms FX1Poly.Polygraph.legSnakePeel_demo
#assert_no_axioms FX1Poly.Polygraph.legUntwistPeel_demo
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasSnakeAnnihilationRung
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCupUntwistSeamRung
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasSeamRungOuterAssembly
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_seamRungsTerminalState

-- Independent cross-check (mandatory, per the AuditAll zero-axiom protocol): the headline declarations print no axioms.
#print axioms FX1Poly.Polygraph.legSink_snakeAnnihilate_underStandardPrefix
#print axioms FX1Poly.Polygraph.legSink_cupUntwist_underStandardPrefix
#print axioms FX1Poly.Polygraph.snakeNeighbor_probes
#print axioms FX1Poly.Polygraph.fxBrauer_seamRungsTerminalState

end FX1PolyAudit
