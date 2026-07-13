import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescClosedDiagramRoundtripClose

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescClosedDiagramRoundtripClose — zero-axiom gate (r55)

Per-declaration zero-axiom gate for the BRAUER r55 closed-diagram roundtrip close: the route D-pad kit
(`padThrough` / `unpadThrough` / injectivity / padded well-formedness / the padded roundtrip via the FROZEN r54
bridge), Brick E (the census-bridge converse `isInvolutionPartner_ofIsBoundaryInvolution` and the packaged iff),
the shift laws (`permInverse_zeroConsShift`, `permutationToCrossingWord_zeroConsShift` — the selection-sort
fold-commutes-with-pad induction), the one-sided left-pad extract transport
(`extractDiagram_padThrough_ofLeftPadSim`), THE STRIP identity (`ext5CorrectedRoundtrip_stripPad`), the
`bottomCount = 0` corner, ★ THE COMPLETE ROUNDTRIP (`ext5CorrectedRoundtrip_complete` /
`_completeOfValidCensus`), the theorems fired on concrete closed diagrams through the GENERAL path, the malformed
negative controls, the superseding content marker, and the machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `WellFounded.fix`.  The
`Nat.sub` / append cancellations are local structural copies (the core `Nat.sub_sub` /
`Nat.add_sub_cancel_left` / `List.append_assoc` / `List.append_nil` leak propext); the census decodes are the
full-enum `Bool` builders; the witness firings supply the census premises by `decide`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.padThrough
#assert_no_axioms FX1Poly.Polygraph.unpadThrough
#assert_no_axioms FX1Poly.Polygraph.unpadThrough_padThrough
#assert_no_axioms FX1Poly.Polygraph.padThrough_injective
#assert_no_axioms FX1Poly.Polygraph.isBoundaryInvolution_padPartner
#assert_no_axioms FX1Poly.Polygraph.padThrough_isBoundaryInvolution
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_padThrough
#assert_no_axioms FX1Poly.Polygraph.isInvolutionPartner_ofIsBoundaryInvolution
#assert_no_axioms FX1Poly.Polygraph.isBoundaryInvolution_iff_validCensus
#assert_no_axioms FX1Poly.Polygraph.permInverse_zeroConsShift
#assert_no_axioms FX1Poly.Polygraph.permutationToCrossingWord_zeroConsShift
#assert_no_axioms FX1Poly.Polygraph.extractDiagram_padThrough_ofLeftPadSim
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_stripPad
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_bottomZero
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_complete
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_completeOfValidCensus
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_general_nestedCups
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_general_tripleNested
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_general_closedEmpty
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_general_loopTriple
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_general_cupWithLoops
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_general_widthEight
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_general_outerOverNestedLoops
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_general_monster
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_stripPad_nestedCups
#assert_no_axioms FX1Poly.Polygraph.isInvolutionPartner_monster_viaConverse
#assert_no_axioms FX1Poly.Polygraph.closedMalformedCensusRejects
#assert_no_axioms FX1Poly.Polygraph.closedMalformedRoundtripFails
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasExt5CorrectedRoundtripComplete
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_closedDiagramRoundtripCloseTerminalState

end FX1PolyAudit
