import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.DisjointWindowSwap
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionPathRigidity

/-! # ArcBubbleToFront — iterated disjoint-window swaps carry the target to the front

The cup/cap peel locates the head's partner atom deep inside the second spine and must carry it
to the front through every earlier atom.  This file ships that carrier: `BubblesToFront`, the
inductive witness that a target atom transposes past each atom of a prefix (each step a
disjoint-window transposition on one side or the other, with the inert gap path carried
explicitly), and its two consumption theorems —

  * `atomicTraceEquiv_of_bubblesToFront`: the witnessed bubble IS an `AtomicTraceEquiv` from
    `prefix ++ target :: suffix` to `movedTarget :: movedPrefix ++ suffix`, assembled from one
    realized swap per step (the mirrored steps enter through symmetry) under the head-cons
    congruence;
  * `spineBoundaryChained_of_bubblesToFront`: the bubbled list stays boundary-chained at the
    same running boundary, threading the two shipped chain-preservation lemmas.

The witness pins each step's inert path explicitly; the realized-swap lemmas produce their own
factorization path, and seed path rigidity (`adjunctionPath_eq_of_length_eq`) identifies the
two, so the witnessed moved atoms are exactly the swaps'.  What this file does NOT provide: the
LOCATION of the partner (constructing the witness from arc-structure equality) and the
head-cancellation transfer — the peel campaign's remaining rungs.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The bubble witness.**  `BubblesToFront target prefixAtoms movedTarget movedPrefixAtoms`
says the target atom transposes leftward past every atom of `prefixAtoms` (read head-first),
arriving at the front as `movedTarget` and leaving the passed atoms re-threaded as
`movedPrefixAtoms`.  Each step records the passed atom, the boundary chaining of the pair, the
inert gap path between the two windows, and which SIDE the target's window lies on:

  * `stepRightOf` — the target's window sits a gap RIGHT of the passed atom's produced window
    (`passed.left + passed.generatorCod + gap = target.left`); the moved target's left context
    re-threads through the passed atom's SOURCE 1-cell;
  * `stepLeftOf` — the target's window sits a gap LEFT of the passed atom's window
    (`target.left + target.generatorDom + gap = passed.left`); the moved target keeps its
    window and its right context re-threads through the passed atom's source 1-cell.

The moved atoms are the exact record updates of the realized swap lemmas, so consuming the
witness is one swap application per step. -/
inductive BubblesToFront {overallSource overallTarget : adjunctionGraph.Mode}
    (target : SpineAtom adjunctionModeSignature overallSource overallTarget) :
    List (SpineAtom adjunctionModeSignature overallSource overallTarget) →
    SpineAtom adjunctionModeSignature overallSource overallTarget →
    List (SpineAtom adjunctionModeSignature overallSource overallTarget) → Prop where
  /-- An empty prefix: the target is already at the front, untouched. -/
  | nil : BubblesToFront target [] target []
  /-- Pass one more atom whose window lies LEFT of the (already bubbled) target's window. -/
  | stepRightOf (passedAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
      {restPrefix : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
      {movedTargetOfRest : SpineAtom adjunctionModeSignature overallSource overallTarget}
      {movedRestPrefix : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
      (restWitness : BubblesToFront target restPrefix movedTargetOfRest movedRestPrefix)
      (boundariesChain :
        movedTargetOfRest.domBoundaryLength = passedAtom.codBoundaryLength)
      (inertPath : ModalityPath adjunctionGraph
        passedAtom.rightMidMode movedTargetOfRest.leftMidMode)
      (windowsDisjoint :
        passedAtom.leftContext.length + passedAtom.generatorCod.length + inertPath.length
          = movedTargetOfRest.leftContext.length) :
      BubblesToFront target (passedAtom :: restPrefix)
        { movedTargetOfRest with
            leftContext :=
              composePath (composePath passedAtom.leftContext passedAtom.generatorDom)
                inertPath }
        ({ passedAtom with
            rightContext :=
              composePath (composePath inertPath movedTargetOfRest.generatorCod)
                movedTargetOfRest.rightContext }
          :: movedRestPrefix)
  /-- Pass one more atom whose window lies RIGHT of the (already bubbled) target's window. -/
  | stepLeftOf (passedAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
      {restPrefix : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
      {movedTargetOfRest : SpineAtom adjunctionModeSignature overallSource overallTarget}
      {movedRestPrefix : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
      (restWitness : BubblesToFront target restPrefix movedTargetOfRest movedRestPrefix)
      (boundariesChain :
        movedTargetOfRest.domBoundaryLength = passedAtom.codBoundaryLength)
      (inertPath : ModalityPath adjunctionGraph
        movedTargetOfRest.rightMidMode passedAtom.leftMidMode)
      (windowsDisjoint :
        movedTargetOfRest.leftContext.length + movedTargetOfRest.generatorDom.length
            + inertPath.length
          = passedAtom.leftContext.length) :
      BubblesToFront target (passedAtom :: restPrefix)
        { movedTargetOfRest with
            rightContext :=
              composePath (composePath inertPath passedAtom.generatorDom)
                passedAtom.rightContext }
        ({ passedAtom with
            leftContext :=
              composePath (composePath movedTargetOfRest.leftContext
                movedTargetOfRest.generatorCod) inertPath }
          :: movedRestPrefix)

/-- ★ **The bubble is a trace equivalence.**  A witnessed bubble carries
`prefix ++ target :: suffix` to `movedTarget :: movedPrefix ++ suffix` inside
`AtomicTraceEquiv`: induction on the witness, each step lifting the inner bubble under the
head-cons congruence and firing ONE realized disjoint-window swap on the now-adjacent pair —
the right-of step directly, the left-of step through symmetry (the mirrored swap runs
moved-pair to original-pair).  Seed path rigidity identifies the swap's factorization path
with the witness's carried inert path. -/
theorem atomicTraceEquiv_of_bubblesToFront
    {overallSource overallTarget : adjunctionGraph.Mode}
    {target movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {prefixAtoms movedPrefixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (witness : BubblesToFront target prefixAtoms movedTarget movedPrefixAtoms)
    (suffixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    AtomicTraceEquiv adjunctionModeSignature (prefixAtoms ++ target :: suffixAtoms)
      (movedTarget :: (movedPrefixAtoms ++ suffixAtoms)) := by
  induction witness with
  | nil => exact AtomicTraceEquiv.refl (target :: suffixAtoms)
  | @stepRightOf passedAtom restPrefix movedTargetOfRest movedRestPrefix restWitness
      boundariesChain inertPath windowsDisjoint restHypothesis =>
      obtain ⟨factorPath, factorHasGapLength, swapFires⟩ :=
        adjunctionSpineAtomSwap_of_disjointWindows passedAtom movedTargetOfRest
          (movedRestPrefix ++ suffixAtoms) boundariesChain inertPath.length windowsDisjoint
      rw [adjunctionPath_eq_of_length_eq factorPath inertPath factorHasGapLength] at swapFires
      exact AtomicTraceEquiv.trans
        (AtomicTraceEquiv.consCongr passedAtom restHypothesis)
        (AtomicTraceEquiv.ofSwap swapFires)
  | @stepLeftOf passedAtom restPrefix movedTargetOfRest movedRestPrefix restWitness
      boundariesChain inertPath windowsDisjoint restHypothesis =>
      obtain ⟨factorPath, factorHasGapLength, swapFires⟩ :=
        adjunctionSpineAtomSwapLeft_of_disjointWindows passedAtom movedTargetOfRest
          (movedRestPrefix ++ suffixAtoms) boundariesChain inertPath.length windowsDisjoint
      rw [adjunctionPath_eq_of_length_eq factorPath inertPath factorHasGapLength] at swapFires
      exact AtomicTraceEquiv.trans
        (AtomicTraceEquiv.consCongr passedAtom restHypothesis)
        (AtomicTraceEquiv.symm (AtomicTraceEquiv.ofSwap swapFires))

/-- ★ **The bubble preserves the boundary chain.**  A witnessed bubble of a boundary-chained
list is boundary-chained at the SAME running boundary: induction on the witness, each step
re-assembling the chain with the passed atom in front of the bubbled tail and handing the
now-adjacent pair to the matching shipped chain-preservation lemma. -/
theorem spineBoundaryChained_of_bubblesToFront
    {overallSource overallTarget : adjunctionGraph.Mode}
    {target movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {prefixAtoms movedPrefixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (witness : BubblesToFront target prefixAtoms movedTarget movedPrefixAtoms)
    (suffixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    ∀ {boundaryLength : Nat},
      SpineBoundaryChained boundaryLength (prefixAtoms ++ target :: suffixAtoms) →
      SpineBoundaryChained boundaryLength (movedTarget :: (movedPrefixAtoms ++ suffixAtoms)) := by
  induction witness with
  | nil => intro boundaryLength listChained; exact listChained
  | @stepRightOf passedAtom restPrefix movedTargetOfRest movedRestPrefix restWitness
      boundariesChain inertPath windowsDisjoint restHypothesis =>
      intro boundaryLength listChained
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail listChained
      exact adjunctionSwappedPair_isBoundaryChained passedAtom movedTargetOfRest
        (SpineBoundaryChained.cons passedAtom headFires (restHypothesis tailChained))
        inertPath.length windowsDisjoint inertPath rfl
  | @stepLeftOf passedAtom restPrefix movedTargetOfRest movedRestPrefix restWitness
      boundariesChain inertPath windowsDisjoint restHypothesis =>
      intro boundaryLength listChained
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail listChained
      exact adjunctionSwappedPairLeft_isBoundaryChained passedAtom movedTargetOfRest
        (SpineBoundaryChained.cons passedAtom headFires (restHypothesis tailChained))
        inertPath.length windowsDisjoint inertPath rfl

/-- **Honesty marker — the bubble carrier is SHIPPED (peel campaign L1+L2).**
`BubblesToFront` witnesses an iterated disjoint-window transposition carrying a target atom to
the front; `atomicTraceEquiv_of_bubblesToFront` realizes it inside `AtomicTraceEquiv` (one
shipped swap per step, mirrored steps through symmetry, factorization paths pinned by seed
path rigidity) and `spineBoundaryChained_of_bubblesToFront` keeps the bubbled list chained at
the same boundary.  With the peel (`extractArc_eq_of_atomicTraceEquiv`) this makes any
witnessed bubble arc-structure-preserving.  What this marker does NOT claim: constructing the
witness from arc-structure equality (the partner LOCATION) and the head-cancellation transfer
— the remaining rungs of `SpineArcHeadExtractionChained`.  `= true`. -/
def fxMode_hasArcBubbleToFront : Bool := true

end FX1Poly.Polygraph
