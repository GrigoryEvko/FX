import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupSlideReadback

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCupSlideReadback — zero-axiom gate (WP-BRAUER-4 r4, B4)

Per-declaration zero-axiom gate for the corrected readback statement + decide probes: the boundary-width-aware
readback Prop (`BrauerCrossingOnlyReadbackInRange`, re-aiming the refuted `∀`), its non-vacuity instance, the
census-to-in-range glue lemma, the two `decidableBrauerConv` probes (stabilizer `isTrue` / loop-separation
`isFalse`), and the two honesty markers (corrected statement + no-flip).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the corrected boundary-width-aware readback statement + non-vacuity
#assert_no_axioms FX1Poly.Polygraph.BrauerCrossingOnlyReadbackInRange
#assert_no_axioms FX1Poly.Polygraph.brauerCrossingOnlyReadbackInRange_instance

-- the census-to-in-range glue
#assert_no_axioms FX1Poly.Polygraph.crossingWordInRange_ofMentionsOnlyBelow

-- the decide probes on the shipped decidable connectivity-congruence
#assert_no_axioms FX1Poly.Polygraph.stabilizerPair_conv
#assert_no_axioms FX1Poly.Polygraph.loopSeparation_notConv

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCorrectedCrossingReadbackStatement
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerV2CompletenessFlip

end FX1PolyAudit
