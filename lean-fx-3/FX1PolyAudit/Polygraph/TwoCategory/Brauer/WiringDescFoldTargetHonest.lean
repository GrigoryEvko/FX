import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFoldTargetHonest

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescFoldTargetHonest — zero-axiom gate (BRAUER r19)

Per-declaration zero-axiom gate for the HONEST six-phase fold-alignment target: the machine refutation of the
uncorrected target (`not_foldRealizesTargetDiagram_nestedCups`, with its involution witness
`isBoundaryInvolution_nestedCups`), the honest restatement over the corrected reconstruction
(`foldRealizesTargetDiagramCorrected` + its adversarial-B and same-witness nested-cups inhabitants), the eval-first
monotonicity truth-probe (`foldTargetConnectivity_monotone_probe` / `…_viaLemma`), and the honesty markers.

Independent `#print axioms` (in a scratch during development) reported every decl as "does not depend on any
axioms".  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- B3a: the refutation of the uncorrected six-phase fold target + its boundary-involution witness
#assert_no_axioms FX1Poly.Polygraph.isBoundaryInvolution_nestedCups
#assert_no_axioms FX1Poly.Polygraph.not_foldRealizesTargetDiagram_nestedCups

-- B3b: the honest restatement over the corrected reconstruction + its two inhabitants
#assert_no_axioms FX1Poly.Polygraph.foldRealizesTargetDiagramCorrected
#assert_no_axioms FX1Poly.Polygraph.foldRealizesTargetDiagramCorrected_adversarialB
#assert_no_axioms FX1Poly.Polygraph.foldRealizesTargetDiagramCorrected_nestedCups

-- B1: the eval-first monotonicity truth-probe + its lemma re-derivation
#assert_no_axioms FX1Poly.Polygraph.foldTargetConnectivity_monotone_probe
#assert_no_axioms FX1Poly.Polygraph.foldTargetConnectivity_monotone_viaLemma

-- B2: the corrected extractor's crossing blocks decode to their read-off orders
#assert_no_axioms FX1Poly.Polygraph.correctedBottomPerm_decodesReadOff
#assert_no_axioms FX1Poly.Polygraph.correctedTopPerm_decodesInverseReadOff
#assert_no_axioms FX1Poly.Polygraph.correctedCrossingBlocks_decode_adversarialB

-- B4 / B5: the honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasFoldTargetRefutation
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasFoldTargetCorrected
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasFoldTargetMonotoneProbe
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCorrectedBlockDecoding
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasFoldTargetHonestAssembly

end FX1PolyAudit
