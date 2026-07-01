import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineReadback

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.SpineReadback — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the readback past the `spine` quotient (the YES-direction, sharpened): the
per-atom readback (`atomFrame`), the cell↔normal-form bridge (`convToInterchangeFreeNormalForm` +
`interchangeFreeNormalForm_spine_eq`), the Godement-step-as-`interchange` content
(`framedGodementInterchangeConv` / `godementWithTailConv`), the reduction of `reconstruct` to its normal-form
restriction (`adjunctionReconstructionFromNf`), and the seed decision modulo `(traceDecision, nfReconstruct)`.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.atomFrame
#assert_no_axioms FX1Poly.Tier0.atomFrame_boundary
#assert_no_axioms FX1Poly.Tier0.nfCell
#assert_no_axioms FX1Poly.Tier0.twoCellConv_ofInterchangeFreeReduction
#assert_no_axioms FX1Poly.Tier0.convToInterchangeFreeNormalForm
#assert_no_axioms FX1Poly.Tier0.spine_eq_ofInterchangeFreeReduction
#assert_no_axioms FX1Poly.Tier0.interchangeFreeNormalForm_spine_eq
#assert_no_axioms FX1Poly.Tier0.framedGodementInterchangeConv
#assert_no_axioms FX1Poly.Tier0.godementWithTailConv
#assert_no_axioms FX1Poly.Tier0.adjunctionReconstructionFromNf
#assert_no_axioms FX1Poly.Tier0.adjunctionTwoCellWordProblemModuloTraceAndNfReconstruction
#assert_no_axioms FX1Poly.Tier0.fxMode_hasNormalFormSpineReadback

end FX1PolyAudit
