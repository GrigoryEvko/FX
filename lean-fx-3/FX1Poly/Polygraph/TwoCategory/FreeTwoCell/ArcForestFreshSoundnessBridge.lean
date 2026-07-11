import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshGatedPartitionCommute
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshDecision

/-! # mode-3 floor — the FOREST-freshness-gated arc-soundness bridge (threading forest+nfPos through the consumer)

`FreeTwoCellArcFreshGatedPartitionCommute` stated the residual at exactly the strength the LIVE count route
provides — `ArcGodementSamePartitionFreshForest`, gated on `ArcStateFresh ∧ bottomCount ≤ nextFresh ∧
isUnionFindForest links ∧ 0 < nextFresh` — and reduced it to residual (2) `ArcGodementCoreSwapSimCount`.
`FreeTwoCellArcFreshDecision` already threads PLAIN freshness through the consumer (`arcTraceInvariantFresh` /
`arcStructureOf_sound_of_arcGodementSamePartitionFresh`) but only from the STRICTLY STRONGER
`ArcGodementSamePartitionFresh` — the residual the truth-probes showed the count route cannot supply (fresh does
NOT imply forest, `arcFreshCyclicState`).

This file closes the gap the parent :545 marker names — "threading `ArcStateFresh` through the read-only consumer
chain" — at FOREST strength, so the soundness path is driven by exactly the count-route residual:

  ★ `godementInvariantForestFresh_of_samePartitionFreshForest` — the freshness+forest-gated `godementInvariant`
    (the `FreeTwoCellArcFreshDecision` step invariance, its `SameArcPartition` supplied by the FOREST residual;
    the cup/cap COUNT fields are the order-independent atom counts, discharged exactly as the plain-fresh version).

  ★ `arcTraceInvariantForestFresh` — the trace closure re-proved threading forest + non-degeneracy through the
    `consCongr` step (`isUnionFindForest_stepArcAtom` preserves the forest, `stepArcAtom_nextFresh_le` keeps
    `nextFresh` positive), alongside the freshness the plain-fresh version already threads.

  ★ `arcStructureOf_sound_of_forestFresh` — the assembled soundness at a NON-EMPTY boundary
    (`0 < sourcePath.length`): the fold seed `mk (range n) [] n 0 [] []` is fresh (`arcStateFresh_initial`), a
    forest (`isUnionFindForest_initialLinks`), and non-degenerate (`nextFresh = n ≥ 1`), so `arcStructureOf` is
    invariant under the COMPLETE `TwoCellConvFull`, gated on `ArcGodementSamePartitionFreshForest` — the count-route
    residual — alone.  The EMPTY boundary (`sourcePath.length = 0`, `nextFresh = 0`) is out of scope here; it is
    handled by the counter-shift proxy (`FreeTwoCellArcGodementSoundnessPeelEmptyBoundary`).

So the soundness side is now reducible to the count-route residual `ArcGodementCoreSwapSimCount` (residual (2)) —
the SOLE open obligation — at every non-empty boundary.  This flips NOTHING: residual (2) is unconstructed, so
`fxMode_hasArcGodementSamePartitionFreshProof` stays `false`.

Raw Lean 4 + Init; the bridge mirrors `FreeTwoCellArcFreshDecision`'s plain-fresh chain with the forest /
non-degeneracy invariants threaded (`isUnionFindForest_stepArcAtom` / `stepArcAtom_nextFresh_le`).  No `omega`, no
`simp`-AC, no `WellFounded.fix`.  Per-declaration `#assert_no_axioms` + independent `#print axioms` in the audit
twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The freshness+forest-gated Godement-step invariant -/

/-- ★ **The freshness+forest-gated `godementInvariant`.**  From the FOREST residual
`ArcGodementSamePartitionFreshForest`, the state-parametric Godement-step arc-extract invariance holds for every
fresh, FOREST, non-degenerate state with `bottomCount ≤ nextFresh`.  Mirrors
`godementInvariantFresh_of_samePartitionFresh`, feeding the two extra hypotheses (`hForest` / `hNfPos`) into the
residual; the cup/cap COUNT fields are the order-independent atom counts (`Nat.add_right_comm`), identical to the
plain-fresh version. -/
theorem godementInvariantForestFresh_of_samePartitionFreshForest {signature : ModeSignature}
    (samePartitionFreshForest : ArcGodementSamePartitionFreshForest signature)
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat) (state : ArcWireState)
    (hFresh : ArcStateFresh state) (hBottomLe : bottomCount ≤ state.nextFresh)
    (hForest : isUnionFindForest state.links) (hNfPos : 0 < state.nextFresh)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (step : SpineGodementStep signature firstList secondList) :
    extractArcAfterProcessing bottomCount state firstList
      = extractArcAfterProcessing bottomCount state secondList := by
  cases step with
  | godement cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest =>
    simp only [extractArcAfterProcessing, processArcSpine_spineDiff]
    exact extractArc_eq_of_sameArcPartition bottomCount _ _
      (samePartitionFreshForest cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest bottomCount
        state hFresh hBottomLe hForest hNfPos)
      (by simp only [processArcSpine_cupEventNodes_length, runArcCell_cupEventNodes_length]
          rw [Nat.add_right_comm (state.cupEventNodes.length + cellAlpha.cupCount)
            cellAlphaUpper.cupCount cellBeta.cupCount])
      (by simp only [processArcSpine_capEventNodes_length, runArcCell_capEventNodes_length]
          rw [Nat.add_right_comm (state.capEventNodes.length + cellAlpha.capCount)
            cellAlphaUpper.capCount cellBeta.capCount])

/-! ## The forest-freshness-threaded trace invariance -/

/-- ★ **`arcTraceInvariant_of_godementInvariant`, re-proved THREADING forest + non-degeneracy.**  Given the
freshness+forest-gated Godement-step invariance, the full `SpineTraceEquiv` arc-extract invariance holds from every
fresh, forest, non-degenerate state with `bottomCount ≤ nextFresh`.  The `consCongr` step advances through one
`stepArcAtom`, which preserves freshness (`arcStateFresh_stepArcAtom`), the forest invariant
(`isUnionFindForest_stepArcAtom`), and never lowers `nextFresh` (`stepArcAtom_nextFresh_le`, keeping it positive) —
so all four preconditions thread automatically. -/
theorem arcTraceInvariantForestFresh {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat)
    (godementInvariantForestFresh : ∀ (state : ArcWireState), ArcStateFresh state →
        bottomCount ≤ state.nextFresh → isUnionFindForest state.links → 0 < state.nextFresh →
        ∀ {firstList secondList : List (SpineAtom signature overallSource overallTarget)},
        SpineGodementStep signature firstList secondList →
        extractArcAfterProcessing bottomCount state firstList
          = extractArcAfterProcessing bottomCount state secondList)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (equiv : SpineTraceEquiv signature firstList secondList) :
    ∀ (state : ArcWireState), ArcStateFresh state → bottomCount ≤ state.nextFresh →
      isUnionFindForest state.links → 0 < state.nextFresh →
      extractArcAfterProcessing bottomCount state firstList
        = extractArcAfterProcessing bottomCount state secondList := by
  induction equiv with
  | ofStep step =>
      intro state hFresh hLe hForest hNfPos
      exact godementInvariantForestFresh state hFresh hLe hForest hNfPos step
  | refl _ => intro _ _ _ _ _; rfl
  | symm _ inductionHypothesis =>
      intro state hFresh hLe hForest hNfPos
      exact (inductionHypothesis state hFresh hLe hForest hNfPos).symm
  | trans _ _ firstHypothesis secondHypothesis =>
      intro state hFresh hLe hForest hNfPos
      exact (firstHypothesis state hFresh hLe hForest hNfPos).trans
        (secondHypothesis state hFresh hLe hForest hNfPos)
  | consCongr atom _ inductionHypothesis =>
      intro state hFresh hLe hForest hNfPos
      exact inductionHypothesis (stepArcAtom state atom) (arcStateFresh_stepArcAtom state atom hFresh)
        (Nat.le_trans hLe (stepArcAtom_nextFresh_le state atom))
        (isUnionFindForest_stepArcAtom state atom hForest)
        (Nat.lt_of_lt_of_le hNfPos (stepArcAtom_nextFresh_le state atom))

/-! ## The assembled soundness at a non-empty boundary -/

/-- ★ **`arcStructureOf` soundness under the COMPLETE `TwoCellConvFull`, gated on the FOREST residual
`ArcGodementSamePartitionFreshForest` — at a NON-EMPTY boundary.**  The real arc structure folds from the seed
`mk (range n) [] n 0 [] []` (`n = sourcePath.length`), which is fresh (`arcStateFresh_initial`), a forest
(`isUnionFindForest_initialLinks`), and — since `n ≥ 1` (`nonEmptyBoundary`) — non-degenerate; so the four
preconditions discharge automatically and the soundness reduces to the count-route residual taken as a hypothesis.
The empty boundary (`sourcePath.length = 0`) is out of scope here (handled by the counter-shift proxy,
`FreeTwoCellArcGodementSoundnessPeelEmptyBoundary`). -/
theorem arcStructureOf_sound_of_forestFresh {signature : ModeSignature}
    (samePartitionFreshForest : ArcGodementSamePartitionFreshForest signature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (nonEmptyBoundary : 0 < sourcePath.length)
    (convFull : TwoCellConvFull signature firstCell secondCell) :
    arcStructureOf firstCell = arcStructureOf secondCell :=
  arcTraceInvariantForestFresh sourcePath.length
    (fun state hFresh hLe hForest hNfPos {_firstList _secondList} step =>
      godementInvariantForestFresh_of_samePartitionFreshForest samePartitionFreshForest sourcePath.length state
        hFresh hLe hForest hNfPos step)
    (twoCellConvFull_spineTraceEquiv convFull)
    (ArcWireState.mk (List.range sourcePath.length) [] sourcePath.length 0 [] [])
    (arcStateFresh_initial sourcePath.length)
    (Nat.le_refl sourcePath.length)
    (isUnionFindForest_initialLinks sourcePath.length)
    nonEmptyBoundary

/-! ## Honesty marker -/

/-- **Honesty marker — the FOREST-freshness-gated soundness bridge is PROVED (zero-axiom, non-empty boundary).**
`godementInvariantForestFresh_of_samePartitionFreshForest` gates the Godement-step invariance on the FOREST
residual; `arcTraceInvariantForestFresh` threads forest + non-degeneracy through the trace closure; and
`arcStructureOf_sound_of_forestFresh` assembles the complete `TwoCellConvFull` soundness at any non-empty boundary,
gated on `ArcGodementSamePartitionFreshForest` — the count-route residual — alone.  So the soundness side is
reducible to residual (2) `ArcGodementCoreSwapSimCount` (`fxMode_hasArcGodementSwapRenameableProof2 = false`) at
every non-empty boundary; the empty boundary is the counter-shift proxy's job.  This bridge constructs NO witness
and flips NOTHING — `fxMode_hasArcGodementSamePartitionFreshProof` stays `false`.  `= true`. -/
def fxMode_hasArcForestFreshSoundnessBridge : Bool := true

end FX1Poly.Polygraph
