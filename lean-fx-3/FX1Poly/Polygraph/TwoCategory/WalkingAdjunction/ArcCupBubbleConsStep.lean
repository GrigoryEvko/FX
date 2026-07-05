import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBubbleToFront
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupPastAtomWindowDichotomy

/-! # ArcCupBubbleConsStep — one descent step of the cup bubble producer

The cup bubble producer descends a realizing cup to the front of a prefix by iterated
`BubblesToFront` steps.  This file ships the INDUCTIVE STEP: given an inner bubble
`BubblesToFront cup restPrefix movedCup movedRest` whose moved cup is still a cup
(`generatorDom.length = 0`), and one more prefix atom `passedAtom` boundary-chained to it, the
bubble extends by one atom.  The direction (left-of / right-of) is chosen by the per-step
window dichotomy (`adjunctionCupPastAtomWindowDichotomy`, brick 2), and the inert gap path is
MINTED from the window-gap equation by the shipped context factorization
(`adjunctionSpineAtom_contextsFactor[Left]_of_disjointWindows`).

Since the moved cup is still a cup at every step (the `BubblesToFront` constructors preserve the
generator, only re-threading contexts), the dichotomy applies uniformly — no atom obstructs the
descent.  The step returns the extended bubble AND the preservation `newMovedCup` is still a cup,
so the eventual front-first descent recursion threads it with no extra invariant.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **One cup descent step.**  An inner bubble `BubblesToFront cup restPrefix movedCup movedRest`
whose moved cup is a cup (`movedIsCup`), extended past one more boundary-chained atom
`passedAtom`, yields a `BubblesToFront` over `passedAtom :: restPrefix` whose moved cup is again a
cup.  The window dichotomy (brick 2) picks `stepLeftOf` (cup at or below `passedAtom`'s window) or
`stepRightOf` (cup at least `passedAtom.generatorCod.length` beyond it); each direction mints its
inert path from the window-gap equation via the shipped context factorization. -/
theorem adjunctionCupBubbleConsStep
    {overallSource overallTarget : adjunctionGraph.Mode}
    (cup passedAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    {restPrefix : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    {movedCup : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {movedRest : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (restWitness : BubblesToFront cup restPrefix movedCup movedRest)
    (movedIsCup : movedCup.generatorDom.length = 0)
    (boundariesChain : movedCup.domBoundaryLength = passedAtom.codBoundaryLength) :
    ∃ (newMovedCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
      (newMovedRest : List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
      BubblesToFront cup (passedAtom :: restPrefix) newMovedCup newMovedRest
        ∧ newMovedCup.generatorDom.length = 0 := by
  cases adjunctionCupPastAtomWindowDichotomy movedCup passedAtom movedIsCup with
  | inl below =>
      obtain ⟨windowGap, gapSplit⟩ := Nat.le.dest below
      obtain ⟨inertPath, _leftFactor, _rightFactor, inertLength⟩ :=
        adjunctionSpineAtom_contextsFactorLeft_of_disjointWindows passedAtom movedCup
          boundariesChain windowGap (by rw [movedIsCup, Nat.add_zero]; exact gapSplit)
      exact ⟨_, _,
        BubblesToFront.stepLeftOf passedAtom restWitness boundariesChain inertPath
          (by
            rw [movedIsCup, Nat.add_zero]
            exact (congrArg (fun gap => movedCup.leftContext.length + gap) inertLength).trans
              gapSplit),
        movedIsCup⟩
  | inr past =>
      obtain ⟨windowGap, gapSplit⟩ := Nat.le.dest past
      obtain ⟨inertPath, _leftFactor, _rightFactor, inertLength⟩ :=
        adjunctionSpineAtom_contextsFactor_of_disjointWindows passedAtom movedCup
          boundariesChain windowGap gapSplit
      exact ⟨_, _,
        BubblesToFront.stepRightOf passedAtom restWitness boundariesChain inertPath
          (by rw [inertLength]; exact gapSplit),
        movedIsCup⟩

/-! ## Honesty marker -/

/-- **Honesty marker — the cup descent's inductive step is SHIPPED.**
`adjunctionCupBubbleConsStep` extends an inner cup bubble past one boundary-chained atom, picking
the direction by the window dichotomy (brick 2) and minting the inert gap path from the shipped
context factorization; the moved cup stays a cup so the step threads with no extra invariant.
What this marker does NOT claim: the front-first descent RECURSION over the whole prefix (which
threads the boundary chain to supply this step's `boundariesChain` at each cons), nor the CANCEL
(the residual orbit matching the peeled remainder to the tail).  `= true`. -/
def fxMode_hasArcCupBubbleConsStep : Bool := true

end FX1Poly.Polygraph
