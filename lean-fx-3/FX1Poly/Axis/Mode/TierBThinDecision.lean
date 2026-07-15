import FX1Poly.Polygraph.TwoCategory.WalkingInvolution.InvolutionDecision

/-! # Axis/Mode/TierBThinDecision — the Tier-B (thin / poset-enriched) 2-cell decision (Gratzer)

The decidable ceiling (`DecidableCeilingLedger`) has a FREE rung decided generically (Tier A) and an
undecidability WALL for arbitrary finite presentations (rung 3, FLAG A).  Between them Gratzer's MTT
normalization result carves out a decidable band: MTT conversion is decidable EXACTLY WHEN the underlying
mode theory decides the equality of its modalities and 2-cells (Gratzer, *Normalization for Multimodal Type
Theory*, arXiv:2106.01414; journal arXiv:2301.11842 — "deciding type checking and conversion in MTT can be
reduced to deciding the equality of modalities in the underlying modal situation").  The examples Gratzer
names — guarded recursion, internalized parametricity — are THIN mode theories: at most one 2-cell between
any parallel pair of 1-cells, so 2-cell equality collapses to a boundary check and is trivially decidable.

## What "thin" means mechanically here (honest scoping)

Gratzer's PUBLISHED hypothesis is "modality equality is decidable".  The refinement "for a THIN mode theory
(<= one 2-cell between parallel 1-cells) the 2-cell decision degenerates to a boundary check" is the FX-team
specialization of that hypothesis, not a verbatim Gratzer claim.  We abstract it as: 2-cell convertibility
is the KERNEL of a DECIDABLE classifier.  `ThinModeTheory` packages exactly that — a classifier `classify`
with decidable equality, SOUND (convertible cells share a classifier, `convClassified`) and COMPLETE
(equal-classifier cells are convertible, `convOfClassifierEq`) — so comparing classifiers DECIDES conv
(`decideThinTwoCellConv`).  For a genuinely thin poset-enriched theory the classifier IS the 1-cell
boundary and thinness is definitional; for the walking involution the classifier is the Z/2 parity
`involutionParityOf` and "thinness" is the reconstruction `conv_toParityNF` (every word is convertible to
the parity normal form of its class).

## The exhibited instance — the walking involution

The walking involution `<s | s.s = id>` (session-type duality, Wadler `dual(dual(S)) = S`) has an EMPTY
2-signature (`involution_no_two_generators`), so 2-cell equality IS 1-cell equality, and the 1-cell word
problem is decided by the Z/2 parity model (`fxInvolution_hasOneCellWordProblemDecided`).  It is the
canonical thin theory: `classify = involutionParityOf`, soundness `involutionParityOf_congr_of_conv`,
completeness `involutionOneCellConv_of_parity_eq`.

## Honest caveat (do not overclaim)

Decidability holds BECAUSE thinness makes the classifier decide conv — it is genuinely necessary (Gratzer)
that the mode theory's modality/2-cell equality be decidable.  A NON-thin finitely presented mode theory
can encode a monoid with an undecidable word problem — that is FLAG A's Markov/Post wall (rung 3), which
this tier stays strictly below.  Cohesion is NOT among the fetched Gratzer examples; do not attribute it.

Lives in `Axis/Mode/` (cross-layer top file — the ledger pins reference it) although its declarations are
in the `FX1Poly.Polygraph` namespace, mirroring `DecidableCeilingLedger`.  Raw Lean 4 + Init; the decision
is `DecidableEq` on the classifier, every instance field is an already-shipped involution theorem, so every
declaration is `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The Tier-B thin interface -/

/-- A **thin mode theory** (Gratzer): 2-cell convertibility is the KERNEL of a DECIDABLE classifier.
`convClassified` is SOUNDNESS (convertible cells share a classifier); `convOfClassifierEq` is
COMPLETENESS/thinness (equal-classifier cells are convertible).  A decidable classifier hence DECIDES conv.
For a poset-enriched thin theory the classifier is the 1-cell boundary; for the walking involution it is the
Z/2 parity. -/
structure ThinModeTheory where
  /-- The 2-cells being compared (over a fixed parallel 1-cell boundary). -/
  Cell : Type
  /-- The decidable classifier's value type (Z/2 for the involution; the boundary for a poset). -/
  ThinClassifier : Type
  /-- The convertibility relation to be decided. -/
  conv : Cell → Cell → Prop
  /-- The classifier assigning each cell its thin invariant. -/
  classify : Cell → ThinClassifier
  /-- The classifier has decidable equality — the source of the decision. -/
  classifierDecEq : DecidableEq ThinClassifier
  /-- SOUNDNESS: convertible cells share a classifier value. -/
  convClassified : ∀ {leftCell rightCell : Cell}, conv leftCell rightCell →
    classify leftCell = classify rightCell
  /-- COMPLETENESS / thinness: cells with equal classifier value are convertible. -/
  convOfClassifierEq : ∀ {leftCell rightCell : Cell}, classify leftCell = classify rightCell →
    conv leftCell rightCell

/-- ★ **The Tier-B decision.**  Compare the two cells' classifier values: equal ⟹ convertible (by
`convOfClassifierEq`), distinct ⟹ not convertible (`convClassified` would force them equal).  This is the
generic form of `decideInvolutionOneCellConv`. -/
def decideThinTwoCellConv (theory : ThinModeTheory) (leftCell rightCell : theory.Cell) :
    Decidable (theory.conv leftCell rightCell) :=
  match theory.classifierDecEq (theory.classify leftCell) (theory.classify rightCell) with
  | isTrue classifiersEqual => isTrue (theory.convOfClassifierEq classifiersEqual)
  | isFalse classifiersDiffer =>
      isFalse (fun conv => classifiersDiffer (theory.convClassified conv))

/-! ## The exhibited instance — the walking involution as a thin mode theory -/

/-- ★ The **walking involution** as a Tier-B thin mode theory: cells are the free 1-cells over the single
endo-generator `s`, conv is `InvolutionOneCellConv` (`s.s = id`), and the thin classifier is the Z/2 parity
`involutionParityOf`.  Soundness/completeness are the shipped involution theorems. -/
def fxInvolutionThinModeTheory : ThinModeTheory where
  Cell := ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point
  ThinClassifier := Bool
  conv := InvolutionOneCellConv
  classify := involutionParityOf
  classifierDecEq := inferInstance
  convClassified := involutionParityOf_congr_of_conv
  convOfClassifierEq := involutionOneCellConv_of_parity_eq

/-! ## Non-vacuity — the classifier genuinely discriminates -/

/-- Non-vacuity (positive): the double dual `s.s` shares the identity's classifier (both even parity), so
they are convertible — the decision accepts a real pair. -/
theorem fxInvolutionThin_classify_double_eq_nil :
    fxInvolutionThinModeTheory.classify (ModalityPath.cons InvolutionModality.s involutionS)
      = fxInvolutionThinModeTheory.classify involutionNil := rfl

/-- Non-vacuity (negative): the single dual `s` does NOT share the identity's classifier (odd vs even
parity), so the decision rejects — the tier is neither always-true nor always-false. -/
theorem fxInvolutionThin_classify_single_ne_nil :
    ¬ (fxInvolutionThinModeTheory.classify involutionS
        = fxInvolutionThinModeTheory.classify involutionNil) := by
  intro classifiersEqual
  exact Bool.noConfusion classifiersEqual

/-! ## The Tier-B flag -/

/-- ★ **Tier B — thin / poset-enriched — DECIDED.**  Any thin mode theory (2-cell conv = kernel of a
decidable classifier) has decidable 2-cell conv via `decideThinTwoCellConv` (Gratzer: MTT conversion is
decidable when the mode theory decides its modalities); the walking involution `<s | s.s = id>` is the
exhibited instance (`fxInvolutionThinModeTheory`, classifier = Z/2 parity), citing
`fxInvolution_hasOneCellWordProblemDecided`.  Sits strictly BELOW the rung-3 undecidability wall (FLAG A):
a non-thin finitely presented mode theory can encode an undecidable word problem, so this does NOT
generalize past thin.  `= true`. -/
def fxMode_hasTierBThinDecision : Bool := true

/-- The Tier-B flag is pinned to the involution's decided-word-problem marker — flip that marker and this
`rfl` breaks, so the tier cannot claim decided without the backing involution decision. -/
theorem fxMode_hasTierBThinDecision_matchesInvolutionMarker :
    fxMode_hasTierBThinDecision = fxInvolution_hasOneCellWordProblemDecided := rfl

end FX1Poly.Polygraph
