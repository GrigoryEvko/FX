import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcRootFlipExtractionSurvival

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/ArcRootFlipExtractionSurvival — zero-axiom gate

Per-declaration zero-axiom gate for the non-vacuity terminal: at the counit/cap root flip that r4's
`not_arcGodementCoreSwapSimCount_adjunction` uses to refute the ROOT-level count vehicle, the FULL
partition view agrees (`arcFlip_samePartition0` / `_samePartition2`) and hence the observable
`extractArc` `FullArcStructure` is LITERALLY EQUAL across the two Godement run orders
(`arcFlip_extractsEqual0` / `_extractsEqual2`) — obtained via the factoring theorem
`extractArc_eq_of_sameArcPartition`, never by deciding `extractArc` itself.  The `#assert_no_axioms` on
the extraction-survival theorems transitively covers the private flip cores, the reassociated
bounded-`∀` helpers, and the `SameArcPartition` witnesses.  The pins record that the r4 refutation stays
`true` and no standing obligation is flipped.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcFlip_rootsDiverge
#assert_no_axioms FX1Poly.Polygraph.arcFlip_samePartition0
#assert_no_axioms FX1Poly.Polygraph.arcFlip_extractsEqual0
#assert_no_axioms FX1Poly.Polygraph.arcFlip_samePartition2
#assert_no_axioms FX1Poly.Polygraph.arcFlip_extractsEqual2
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcRootFlipExtractionSurvival
#assert_no_axioms FX1Poly.Polygraph.arcFlip_coreSwapSimCountRefuted_stays_true
#assert_no_axioms FX1Poly.Polygraph.arcFlip_swapRenameableProof2_stays_false

end FX1PolyAudit
