import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMidZeroValleyCellReducer
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSaturatedConv

/-! # WalkingString/StringMidZeroValleyDistinctFire — the GENUINE non-diagonal distinct-pair fire of the
mid-width-`0` valley determinacy reducer (FC-3 r39, the r38 diagonal replaced by a real witness)

The r38 truth-probe `stringMidZeroValleyTraceEquiv_firesOnCrossLevelValley` (`StringMidZeroValleyCellReducer`) fed
`stringCrossLevelCell` as BOTH valleys, so its conclusion is `SpineTraceEquiv X X` with `X :=
stringCrossLevelCell.spine` — provable by `SpineTraceEquiv.refl X` outright.  It exercises the whole reducer machinery
but establishes nothing `refl` could not: it is DIAGONAL.  This file ships the genuine NON-diagonal witness — the
reducer fired on TWO SYNTACTICALLY DISTINCT spines with equal boundary `matchingOf`, on which `SpineTraceEquiv.refl`
FAILS with a type mismatch (the spines are not definitionally equal).

The distinct pair is the disjoint DOUBLE-CAP on `G·F·G·F ⇒ id_tip`, in its two firing orders:

  * `stringDistinctDoubleCapLeftFirst := (ε ▷ G·F) ⊟ ε` — fire the LEFT cap first (whisker the second `G·F` on the
    right of the first cap, then cap the survivor);
  * `stringDistinctDoubleCapRightFirst := (G·F ◁ ε) ⊟ ε` — fire the RIGHT cap first (whisker the first `G·F` on the
    left of the second cap, then cap the survivor).

Both have source `G·F·G·F` (length `4`, positive) and target `id_tip` (mid-width `0` — the two caps consume all four
bottom wires, zero cups).  Their boundary `matchingOf` agree (`matchingOfSpineList`-decidable), yet their spines
differ: the leftContext-length projections are `[0, 0]` (left-first) versus `[2, 0]` (right-first).  So the reducer's
conclusion `SpineTraceEquiv adjointTripleModeSignature leftFirst.spine rightFirst.spine` is NOT the diagonal
`SpineTraceEquiv X X` — feeding `SpineTraceEquiv.refl _` to it fails with a type mismatch, disclosed here as the
non-vacuity evidence.  (The r38 cross-level probe could only be diagonal because it fixed a SINGLE cell; a distinct
same-boundary pair with equal matching first appears at the length-`4` double-cap.)

  What this ships (each zero-axiom, machine-checked):

  * ★★ `stringMidZeroValleyTraceEquiv_firesOnDistinctDoubleCap` — the discharged reducer
    `stringMidZeroValleyTraceEquiv_holds` fired on the DISTINCT double-cap pair (all five hypotheses — two
    cap-then-cup-valley checks, the `matchingOf` equality, source positivity `0 < 4`, mid-width `0` — by `decide`);
  * ★ `stringDistinctDoubleCap_leftContextLengthsDiffer` — the distinctness anchor: the two spines' leftContext-length
    projection lists differ (`[0, 0] ≠ [2, 0]`), decidable at the `List Nat` projection.  This certifies the fire
    relates two genuinely distinct spines.

  What this does NOT flip (honestly): the completeness masters `fxString_hasAdjointTripleCompleteness`
  (`StringMatchingCompleteness`) and `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) stay `false`.  This
  file upgrades the r38 mid-zero-reducer non-vacuity evidence from a DIAGONAL probe to a genuine distinct-pair fire; it
  discharges no new obligation.

Raw Lean 4 + Init.  The fire's `matchingOf` reduction at the length-`4` source is heavy, so this file raises
`maxHeartbeats` (`by decide` / `rfl` under the raised budget — `native_decide` is banned).
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace FX1Poly.Polygraph

/-! ## The disjoint double-cap on `G·F·G·F ⇒ id_tip`, in its two firing orders -/

/-- The disjoint double-cap firing the LEFT cap first: whisker the lower counit `ε : G·F ⇒ id_tip` on the RIGHT by
`G·F` (capping the first `G·F`, leaving the second intact), then cap the survivor with a second `ε`.  A whole
`G·F·G·F ⇒ id_tip` valley (two caps, zero cups). -/
def stringDistinctDoubleCapLeftFirst :
    RawTwoCellExpr adjointTripleModeSignature (composePath stringGF stringGF)
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip) :=
  RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight stringGF stringCounitLower) stringCounitLower

/-- The disjoint double-cap firing the RIGHT cap first: whisker `ε : G·F ⇒ id_tip` on the LEFT by `G·F` (capping the
second `G·F`, leaving the first intact), then cap the survivor with a second `ε`.  The same boundary
`G·F·G·F ⇒ id_tip`, a DISTINCT spine (the caps fire in the opposite order). -/
def stringDistinctDoubleCapRightFirst :
    RawTwoCellExpr adjointTripleModeSignature (composePath stringGF stringGF)
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip) :=
  RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft stringGF stringCounitLower) stringCounitLower

/-! ## The genuine non-diagonal fire + the distinctness anchor -/

/-- ★★ **The mid-width-`0` valley reducer FIRES on a genuinely DISTINCT pair.**  Instantiating the discharged
`stringMidZeroValleyTraceEquiv_holds` on the two firing orders of the disjoint double-cap `G·F·G·F ⇒ id_tip` runs the
whole reducer end-to-end and produces a `SpineTraceEquiv` of TWO SYNTACTICALLY DISTINCT spines (leftContext-length
projections `[0, 0]` vs `[2, 0]`, see `stringDistinctDoubleCap_leftContextLengthsDiffer`) with equal boundary
`matchingOf`.  Every hypothesis is machine-checked (`decide`): both spines are cap-then-cup valleys, the two boundary
`matchingOf` agree, the source `G·F·G·F` has positive length `4`, and the two caps consume all four bottom wires so the
mid-width is `0`.  Unlike the r38 diagonal probe (conclusion `SpineTraceEquiv X X`, `refl`-provable), this conclusion
relates DISTINCT spines — `SpineTraceEquiv.refl _` fails on it with a type mismatch — so the fire is genuinely
non-vacuous. -/
theorem stringMidZeroValleyTraceEquiv_firesOnDistinctDoubleCap :
    SpineTraceEquiv adjointTripleModeSignature
      stringDistinctDoubleCapLeftFirst.spine stringDistinctDoubleCapRightFirst.spine :=
  stringMidZeroValleyTraceEquiv_holds stringDistinctDoubleCapLeftFirst stringDistinctDoubleCapRightFirst
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- ★ **The distinctness anchor.**  The two firing orders' spines have DIFFERENT leftContext-length projection lists
(`[0, 0]` for left-first, `[2, 0]` for right-first), so they are genuinely distinct lists.  Were the two spines equal,
their projections would coincide; the projections are decidably unequal at the `List Nat` level.  This certifies
`stringMidZeroValleyTraceEquiv_firesOnDistinctDoubleCap` is NOT the diagonal `SpineTraceEquiv X X`. -/
theorem stringDistinctDoubleCap_leftContextLengthsDiffer :
    stringDistinctDoubleCapLeftFirst.spine.map (fun spineAtom => spineAtom.leftContext.length)
      ≠ stringDistinctDoubleCapRightFirst.spine.map (fun spineAtom => spineAtom.leftContext.length) := by
  decide

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the mid-width-`0` valley reducer has a GENUINE non-diagonal distinct-pair fire (FC-3 r39).**
The r38 truth-probe was DIAGONAL (`stringCrossLevelCell` fed as both valleys → `SpineTraceEquiv X X`, `refl`-provable).
`stringMidZeroValleyTraceEquiv_firesOnDistinctDoubleCap` replaces it: the reducer fired on the two firing orders of the
disjoint double-cap `G·F·G·F ⇒ id_tip` (bottomCount `4`, mid-width `0`, equal `matchingOf`), whose spines are
genuinely distinct (`stringDistinctDoubleCap_leftContextLengthsDiffer`: leftContext-length lists `[0, 0] ≠ [2, 0]`) —
so `SpineTraceEquiv.refl` FAILS on the conclusion (type mismatch, the spines are not definitionally equal) and the fire
is genuinely non-vacuous.

  What this does NOT flip (honestly): this is an honesty upgrade of the r38 non-vacuity evidence, not a new discharge.
  The completeness masters `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) and
  `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) STAY `false`; the standing residual is unchanged.  This
  round flips ONLY this NEW marker.  `= true`. -/
def fxString_hasMidZeroValleyDistinctFire : Bool := true

end FX1Poly.Polygraph
