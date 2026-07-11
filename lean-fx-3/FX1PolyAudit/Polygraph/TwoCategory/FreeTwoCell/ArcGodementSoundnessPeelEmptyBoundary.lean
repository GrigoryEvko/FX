import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcGodementSoundnessPeelEmptyBoundary

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcGodementSoundnessPeelEmptyBoundary — zero-axiom gate (mode-3 floor, empty boundary closed)

Per-declaration zero-axiom gate for the empty-boundary (n = 0) Godement arc soundness via the counter-shift
proxy: the global counter-shift (`renameStateShift` / `addRightInjectiveShift` / `shiftInjective`), the arity
read-offs (`stepArcAtom_eq_stepCupArc` / `_eq_stepCapArc`), the cup/cap counter-shift steps
(`stepCupArc_renameStateShift` / `stepCapArc_renameStateShift`), the step dispatch
(`stepArcAtom_renameStateShift`), the boundary-chained fold (`processArcSpine_renameStateShift_ofChain`), the
empty-boundary rename relation (`arcRenameRel_renameStateShift` / `extractArc_renameStateShift_emptyBoundary`),
the bridge (`extractArcAfterProcessing_emptyBoundary_counterShift`), the empty-boundary soundness leg and total
capstone (`arcStructureOf_sound_of_convFull_adjunction_emptyBoundary` / `_allBoundaries`), the all-boundaries
marker, and the #2043 upstream re-derivation (`arcPeelClosesAdjunctionSoundnessButNotGeneralUpstream`).

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per key declaration — the
two are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in `AuditAll` beyond the parent's unified
registration. -/

namespace FX1PolyAudit

-- the global counter-shift + injectivity
#assert_no_axioms FX1Poly.Polygraph.renameStateShift
#assert_no_axioms FX1Poly.Polygraph.addRightInjectiveShift
#assert_no_axioms FX1Poly.Polygraph.shiftInjective

-- the arity read-offs
#assert_no_axioms FX1Poly.Polygraph.stepArcAtom_eq_stepCupArc
#assert_no_axioms FX1Poly.Polygraph.stepArcAtom_eq_stepCapArc

-- the cup/cap counter-shift steps + dispatch
#assert_no_axioms FX1Poly.Polygraph.stepCupArc_renameStateShift
#assert_no_axioms FX1Poly.Polygraph.stepCapArc_renameStateShift
#assert_no_axioms FX1Poly.Polygraph.stepArcAtom_renameStateShift

-- the boundary-chained fold
#assert_no_axioms FX1Poly.Polygraph.processArcSpine_renameStateShift_ofChain

-- the empty-boundary rename relation + extract invariance
#assert_no_axioms FX1Poly.Polygraph.arcRenameRel_renameStateShift
#assert_no_axioms FX1Poly.Polygraph.extractArc_renameStateShift_emptyBoundary

-- the bridge + soundness leg + total capstone
#assert_no_axioms FX1Poly.Polygraph.extractArcAfterProcessing_emptyBoundary_counterShift
#assert_no_axioms FX1Poly.Polygraph.arcStructureOf_sound_of_convFull_adjunction_emptyBoundary
#assert_no_axioms FX1Poly.Polygraph.arcStructureOf_sound_of_convFull_adjunction_allBoundaries

-- the marker + #2043 upstream re-derivation
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcGodementSoundnessPeelAllBoundaries
#assert_no_axioms FX1Poly.Polygraph.arcPeelClosesAdjunctionSoundnessButNotGeneralUpstream

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.processArcSpine_renameStateShift_ofChain
#print axioms FX1Poly.Polygraph.extractArcAfterProcessing_emptyBoundary_counterShift
#print axioms FX1Poly.Polygraph.arcStructureOf_sound_of_convFull_adjunction_emptyBoundary
#print axioms FX1Poly.Polygraph.arcStructureOf_sound_of_convFull_adjunction_allBoundaries
#print axioms FX1Poly.Polygraph.arcPeelClosesAdjunctionSoundnessButNotGeneralUpstream

end FX1PolyAudit
