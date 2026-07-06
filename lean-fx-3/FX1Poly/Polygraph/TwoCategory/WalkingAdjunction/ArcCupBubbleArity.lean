import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBubbleToFront

/-! # ArcCupBubbleArity — the bubble preserves the target's generator arities (peel campaign H, cup seat-tracking rung 0)

The cup locate's window pin (`movedTarget.leftContext.length = headAtom.leftContext.length`) is
genuinely history-dependent — each `BubblesToFront` step re-threads the moved atom's whisker
CONTEXTS (`stepLeftOf` leaves `leftContext` fixed; `stepRightOf` resets it to
`composePath (composePath passed.leftContext passed.generatorDom) inertPath`), so the window shifts
by the passed atom's `generatorDom − generatorCod` per right-of step.  What every step leaves
UNTOUCHED is the moved atom's GENERATOR: each constructor produces `{ movedTargetOfRest with … }`
updating only a context field, so the `generatorDom` / `generatorCod` pass through defeq-unchanged.

  * ★ `bubblesToFront_movedGeneratorArities` — the moved atom keeps the target's generator source
    and target 1-cell lengths.  This is the arity half of the located-cup identification: it gives
    BOTH `movedDomPin` (`= 0`) and `movedCodPin` (`= 2`) for a cup target directly from the bubble
    witness, independent of the (history-dependent) window pin the orbit search still owes.

The window pin remains the genuine orbit residual — this brick isolates the arity pins that are
NOT part of the search, so the eventual seat-tracking lemma only has to establish the window.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The bubble preserves the target's generator arities.**  A witnessed bubble carries the
target atom to the front as `movedTarget` re-threading only the whisker contexts, so the moved
atom's generator source and target 1-cell lengths coincide with the target's — structural
induction on the witness, each step reading the arities off the untouched generator field. -/
theorem bubblesToFront_movedGeneratorArities
    {overallSource overallTarget : adjunctionGraph.Mode}
    {target movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {prefixAtoms movedPrefixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (witness : BubblesToFront target prefixAtoms movedTarget movedPrefixAtoms) :
    movedTarget.generatorDom.length = target.generatorDom.length
      ∧ movedTarget.generatorCod.length = target.generatorCod.length := by
  induction witness with
  | nil => exact ⟨rfl, rfl⟩
  | @stepRightOf _ _ _ _ _ _ _ _ inductionHypothesis => exact inductionHypothesis
  | @stepLeftOf _ _ _ _ _ _ _ _ inductionHypothesis => exact inductionHypothesis

/-- The dom-arity pin: a cup target (`generatorDom.length = 0`) bubbles to a moved atom that is
still a cup on its source 1-cell. -/
theorem bubblesToFront_movedDomArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    {target movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {prefixAtoms movedPrefixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (witness : BubblesToFront target prefixAtoms movedTarget movedPrefixAtoms)
    (targetDomArity : target.generatorDom.length = 0) :
    movedTarget.generatorDom.length = 0 :=
  (bubblesToFront_movedGeneratorArities witness).1.trans targetDomArity

/-- The cod-arity pin: a cup target (`generatorCod.length = 2`) bubbles to a moved atom that is
still a cup on its target 1-cell. -/
theorem bubblesToFront_movedCodArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    {target movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {prefixAtoms movedPrefixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (witness : BubblesToFront target prefixAtoms movedTarget movedPrefixAtoms)
    (targetCodArity : target.generatorCod.length = 2) :
    movedTarget.generatorCod.length = 2 :=
  (bubblesToFront_movedGeneratorArities witness).2.trans targetCodArity

/-! ## Honesty marker -/

/-- **Honesty marker — the bubble preserves the target's generator arities (peel campaign H, cup
seat-tracking rung 0).**  `bubblesToFront_movedGeneratorArities` / `bubblesToFront_movedDomArity` /
`bubblesToFront_movedCodArity`: a `BubblesToFront` witness carries the target's `generatorDom` /
`generatorCod` lengths to the moved atom unchanged (each step re-threads only a whisker context),
so BOTH cup arity pins (`= 0`, `= 2`) drop straight out of the witness.  What this marker does NOT
claim: the WINDOW pin `movedTarget.leftContext.length = headAtom.leftContext.length` — that is
history-dependent (the window shifts by `passed.generatorDom − passed.generatorCod` per right-of
step), so it remains the genuine orbit-search residual.  `= true`. -/
def fxMode_hasArcCupBubbleArity : Bool := true

end FX1Poly.Polygraph
