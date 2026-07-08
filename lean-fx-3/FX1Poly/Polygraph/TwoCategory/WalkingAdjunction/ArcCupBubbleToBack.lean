import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBubbleToFront
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineTraceAppendCongruence

/-! # ArcCupBubbleToBack — iterated disjoint-window swaps carry the target to the BACK (peel-last carrier)

The peel-LAST cup branch of `SpineArcLastExtractionChained` (`ArcCupPeelLastAssembly`) must, given the
arc-shared top short chord (`lastCup_sharedShortChord_ofArcEqual`, the honest windowPin replacement), locate the
OWNER cup of that chord inside `secondList` and carry it RIGHTWARD to the BACK — the vertical dual of the head
route's leftward `BubblesToFront` (`ArcBubbleToFront`).  This file ships that dual carrier.

  * ★ `BubblesToBack target suffixAtoms movedTarget movedSuffixAtoms` — the inductive witness that the target
    atom transposes RIGHTWARD past every atom of `suffixAtoms` (read head-first, so the FIRST-passed atom is the
    suffix head, immediately to the target's right), arriving at the back as `movedTarget` and leaving the passed
    atoms re-threaded as `movedSuffixAtoms`.  Because the target passes a RIGHT neighbour at each step, the moving
    target CHANGES as it advances, so — unlike the head-fixed `BubblesToFront` — `target` is an INDEX: the step's
    inner witness bubbles the once-moved target through the rest.  Every step is a genuine right-of
    disjoint-window transposition (`adjunctionSpineAtomSwap_of_disjointWindows`), so only ONE swap direction is
    needed (the mirror of `BubblesToFront`'s two).
  * ★ `atomicTraceEquiv_of_bubblesToBack` — the witnessed bubble IS an `AtomicTraceEquiv` from `target :: suffix`
    to `movedSuffix ++ [movedTarget]`: induction on the witness, each step firing ONE realized right-of swap on
    the now-adjacent leading pair (`target :: passedAtom`), then re-cons-ing the moved passed atom over the inner
    bubble.  Seed path rigidity (`adjunctionPath_eq_of_length_eq`) identifies the swap's factorization path with
    the witness's carried inert path.
  * ★ `spineBoundaryChained_of_bubblesToBack` — the bubbled list stays boundary-chained at the same running
    boundary, threading `adjunctionSwappedPair_isBoundaryChained` per step.
  * ★ `spineTraceEquiv_of_bubblesToBack` / `spineTraceEquiv_of_bubblesToBack_withPrefix` — the block-level image
    (via `spineTraceEquiv_iff_atomicTraceEquiv`) and its prefix-lifted form (via `spineTraceEquiv_prefixListCongr`),
    the shape the owner-locate feeds into the peel-last obligation.

What this file does NOT provide: the LOCATION of the owner cup — constructing the `BubblesToBack` witness from
the arc-shared short chord (`lastCup_sharedShortChord_ofArcEqual`) — and the identity `movedTarget = lastCup`.
That owner-locate is the genuine (arc-ANCHORED, but unbuilt) residual of the cup branch, the peel-last analog of
the head route's still-open `arcCupReselection_exists`.  `fxMode_hasArcStructureReconstruction` stays `false`.

Raw Lean 4 + Init; the carrier is a structural induction on the witness reusing the shipped realized-swap and
chain-preservation lemmas; only `List.cons_append` reductions (`rfl`), no `List.append_assoc` (which would leak
`propext`).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The back-bubble witness.**  `BubblesToBack target suffixAtoms movedTarget movedSuffixAtoms` says the
target atom transposes RIGHTWARD past every atom of `suffixAtoms` (read head-first), arriving at the back as
`movedTarget` and leaving the passed atoms re-threaded as `movedSuffixAtoms`.  Each step records the passed atom
(the target's immediate RIGHT neighbour), the boundary chaining of the pair, the inert gap path between the two
windows, and the right-of window disjointness.  The single move is a right-of transposition: after passing, the
target's right context re-threads through the passed atom's TARGET 1-cell and the passed atom's left context
re-threads through the target's SOURCE 1-cell — exactly the record updates of
`adjunctionSpineAtomSwap_of_disjointWindows`.  `target` is an INDEX (it moves), so the inner witness carries the
once-moved target through the rest of the suffix. -/
inductive BubblesToBack {overallSource overallTarget : adjunctionGraph.Mode} :
    SpineAtom adjunctionModeSignature overallSource overallTarget →
    List (SpineAtom adjunctionModeSignature overallSource overallTarget) →
    SpineAtom adjunctionModeSignature overallSource overallTarget →
    List (SpineAtom adjunctionModeSignature overallSource overallTarget) → Prop where
  /-- An empty suffix: the target is already at the back, untouched. -/
  | nil (restingTarget : SpineAtom adjunctionModeSignature overallSource overallTarget) :
      BubblesToBack restingTarget [] restingTarget []
  /-- Pass one more atom, the target's immediate RIGHT neighbour whose window lies a gap to the right. -/
  | step (target passedAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
      {restSuffix : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
      {movedTargetFinal : SpineAtom adjunctionModeSignature overallSource overallTarget}
      {movedRestSuffix : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
      (boundariesChain : passedAtom.domBoundaryLength = target.codBoundaryLength)
      (inertPath : ModalityPath adjunctionGraph target.rightMidMode passedAtom.leftMidMode)
      (windowsDisjoint :
        target.leftContext.length + target.generatorCod.length + inertPath.length
          = passedAtom.leftContext.length)
      (restWitness : BubblesToBack
          { target with
              rightContext :=
                composePath (composePath inertPath passedAtom.generatorCod) passedAtom.rightContext }
          restSuffix movedTargetFinal movedRestSuffix) :
      BubblesToBack target (passedAtom :: restSuffix) movedTargetFinal
        ({ passedAtom with
            leftContext :=
              composePath (composePath target.leftContext target.generatorDom) inertPath }
          :: movedRestSuffix)

/-- ★ **The back-bubble is a trace equivalence.**  A witnessed back-bubble carries `target :: suffixAtoms` to
`movedSuffixAtoms ++ [movedTarget]` inside `AtomicTraceEquiv`: induction on the witness.  The `nil` case is
reflexivity; each `step` fires ONE realized right-of disjoint-window swap on the leading pair
`target :: passedAtom` (`adjunctionSpineAtomSwap_of_disjointWindows`, its factorization path pinned to the
carried inert path by seed rigidity), then re-cons-es the moved passed atom over the inner bubble
(`consCongr`), and glues by `trans` — `(movedPassedAtom :: movedRestSuffix) ++ [movedTarget]` reducing to
`movedPassedAtom :: (movedRestSuffix ++ [movedTarget])` definitionally. -/
theorem atomicTraceEquiv_of_bubblesToBack
    {overallSource overallTarget : adjunctionGraph.Mode}
    {target movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {suffixAtoms movedSuffixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (witness : BubblesToBack target suffixAtoms movedTarget movedSuffixAtoms) :
    AtomicTraceEquiv adjunctionModeSignature (target :: suffixAtoms)
      (movedSuffixAtoms ++ [movedTarget]) := by
  induction witness with
  | nil restingTarget => exact AtomicTraceEquiv.refl [restingTarget]
  | @step target passedAtom restSuffix movedTargetFinal movedRestSuffix boundariesChain inertPath
      windowsDisjoint _restWitness restHypothesis =>
      obtain ⟨factorPath, factorHasGapLength, swapFires⟩ :=
        adjunctionSpineAtomSwap_of_disjointWindows target passedAtom restSuffix boundariesChain
          inertPath.length windowsDisjoint
      rw [adjunctionPath_eq_of_length_eq factorPath inertPath factorHasGapLength] at swapFires
      exact AtomicTraceEquiv.trans
        (AtomicTraceEquiv.ofSwap swapFires)
        (AtomicTraceEquiv.consCongr
          { passedAtom with
              leftContext :=
                composePath (composePath target.leftContext target.generatorDom) inertPath }
          restHypothesis)

/-- ★ **The back-bubble preserves the boundary chain.**  A witnessed back-bubble of a boundary-chained
`target :: suffixAtoms` is boundary-chained at the SAME running boundary as `movedSuffixAtoms ++ [movedTarget]`:
induction on the witness, each step handing the leading pair to `adjunctionSwappedPair_isBoundaryChained`, then
splitting off the (now-front) moved passed atom and threading the inner bubble's chain through the inductive
hypothesis at the moved passed atom's target boundary. -/
theorem spineBoundaryChained_of_bubblesToBack
    {overallSource overallTarget : adjunctionGraph.Mode}
    {target movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {suffixAtoms movedSuffixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (witness : BubblesToBack target suffixAtoms movedTarget movedSuffixAtoms) :
    ∀ {boundaryLength : Nat},
      SpineBoundaryChained boundaryLength (target :: suffixAtoms) →
      SpineBoundaryChained boundaryLength (movedSuffixAtoms ++ [movedTarget]) := by
  induction witness with
  | nil _restingTarget => intro _boundaryLength listChained; exact listChained
  | @step target passedAtom restSuffix movedTargetFinal movedRestSuffix boundariesChain inertPath
      windowsDisjoint _restWitness restHypothesis =>
      intro boundaryLength listChained
      have swappedChained :=
        adjunctionSwappedPair_isBoundaryChained target passedAtom listChained inertPath.length
          windowsDisjoint inertPath rfl
      obtain ⟨movedPassedFires, innerChained⟩ := spineBoundaryChained_tail swappedChained
      exact SpineBoundaryChained.cons _ movedPassedFires (restHypothesis innerChained)

/-! ## Block-level images -/

/-- ★ **The back-bubble as a block-level trace equivalence.**  The `AtomicTraceEquiv` core lifted to
`SpineTraceEquiv` via the closure identification `spineTraceEquiv_iff_atomicTraceEquiv`. -/
theorem spineTraceEquiv_of_bubblesToBack
    {overallSource overallTarget : adjunctionGraph.Mode}
    {target movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {suffixAtoms movedSuffixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (witness : BubblesToBack target suffixAtoms movedTarget movedSuffixAtoms) :
    SpineTraceEquiv adjunctionModeSignature (target :: suffixAtoms)
      (movedSuffixAtoms ++ [movedTarget]) :=
  spineTraceEquiv_iff_atomicTraceEquiv.mpr (atomicTraceEquiv_of_bubblesToBack witness)

/-- ★ **The prefix-lifted back-bubble trace equivalence.**  A fixed list prefix (the atoms of `secondList`
strictly left of the owner cup) passes through both sides via `spineTraceEquiv_prefixListCongr`:
`prefix ++ target :: suffix ~ prefix ++ (movedSuffix ++ [movedTarget])`.  This is the shape the (unbuilt) owner
locate feeds into the peel-last obligation — the trailing `movedTarget` at the back, the remainder
`prefix ++ movedSuffix` before it. -/
theorem spineTraceEquiv_of_bubblesToBack_withPrefix
    {overallSource overallTarget : adjunctionGraph.Mode}
    {target movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {suffixAtoms movedSuffixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (witness : BubblesToBack target suffixAtoms movedTarget movedSuffixAtoms) :
    SpineTraceEquiv adjunctionModeSignature (prefixAtoms ++ target :: suffixAtoms)
      (prefixAtoms ++ (movedSuffixAtoms ++ [movedTarget])) :=
  spineTraceEquiv_prefixListCongr prefixAtoms (spineTraceEquiv_of_bubblesToBack witness)

/-! ## Honesty marker -/

/-- **Honesty marker — the peel-last BACK carrier is SHIPPED (cup-branch dual of `ArcBubbleToFront`).**
`BubblesToBack` witnesses an iterated right-of disjoint-window transposition carrying a target atom to the back;
`atomicTraceEquiv_of_bubblesToBack` realizes it inside `AtomicTraceEquiv` (one shipped right-of swap per step,
factorization paths pinned by seed rigidity), `spineBoundaryChained_of_bubblesToBack` keeps the bubbled list
chained, and `spineTraceEquiv_of_bubblesToBack` / `spineTraceEquiv_of_bubblesToBack_withPrefix` lift it to the
block level with an arbitrary left prefix.  This is the vertical dual of the shipped leftward head carrier,
relocating the peel-last cup branch onto exactly the carrier the arc-shared top short chord anchors.

What this marker does NOT claim: the owner-cup LOCATION — building the `BubblesToBack` witness from
`lastCup_sharedShortChord_ofArcEqual` (which atom of `secondList` owns the top short chord, and that its moved
image equals the peeled last cup).  That owner-locate is the genuine (arc-anchored but unbuilt) residual of the
cup branch, the peel-last analog of the head route's still-open `arcCupReselection_exists`; and the CAP/STUCK
branch is separately walled (`ArcStuckSpineNonSingleton`, decided swap-connected but general completeness open,
`ArcStuckSpineDecided`).  No gate flip; `fxMode_hasArcStructureReconstruction` stays `false`.  `= true`. -/
def fxMode_hasArcCupBubbleToBack : Bool := true

end FX1Poly.Polygraph
