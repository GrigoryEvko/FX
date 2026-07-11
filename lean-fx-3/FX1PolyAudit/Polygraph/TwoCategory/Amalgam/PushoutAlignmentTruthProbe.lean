import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutAlignmentTruthProbe

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutAlignmentTruthProbe — zero-axiom gate for the r16 alignment
truth-probe VERDICT (ALIGNABLE at the firing-block skeleton) + the regression pins (WP-AMALG-2 r16, B1)

Per-declaration zero-axiom gate for the probe candidates (the slot-count invariant on the r8 and s-heavy words, the
general wall-count invariant, the per-letter-vs-firing-block granularity numeric, the wall-inertness pin) and the two
verdict honesty markers plus the no-flip check.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.alignmentSlotInvariantR8DomCod
#assert_no_axioms FX1Poly.Polygraph.Amalgam.alignmentWallHeavySlotCountEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.alignmentSlotInvariantGeneral
#assert_no_axioms FX1Poly.Polygraph.Amalgam.alignmentFiringBlockRunIsOneSlot
#assert_no_axioms FX1Poly.Polygraph.Amalgam.alignmentPerLetterCountEqWordLength
#assert_no_axioms FX1Poly.Polygraph.Amalgam.alignmentWallsInertAtMu
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_alignmentVerdictAlignableAtSkeleton
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_alignmentDescentStaysJamA
#assert_no_axioms FX1Poly.Polygraph.Amalgam.alignmentVerdictFlipsNoMaster

end FX1PolyAudit
