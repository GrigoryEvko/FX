import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestLayout

/-! # Polygraph/TwoCategory/Amalgam/PushoutFinestGapMerge — the whisker-frame `t`-run GAP MERGE at the width level
(WP-AMALG-2 r10, B2 — node (ii) of the recon, truth-probed FIRST)

`PushoutFinestLayout.lean` (r9) shipped `finestGapWidths`, the finest gap-width shape of a boundary tag sequence.
The r10 recon's node (ii) asks how a WHISKER frame's finest shape composes with its body's: is
`finestGapWidths (frame ++ body)` the naive concatenation `finestGapWidths frame ++ finestGapWidths body`?  The r8
lesson (never assume a false concatenation invariance) says PROBE FIRST.  This file runs that probe and REFUTES the
naive design, then ships the CORRECT merge law and its structural primitive.

## The probe (the recon's table, machine-checked here)

Tags `true = s`-wall, `false = t`-gap.  A whisker by a pure-`t` frame prepends `t`-letters.

| cell            | tags                  | `finestGapWidths` |
| --------------- | --------------------- | ----------------- |
| frame `t`       | `[false]`             | `[1]`             |
| body `t·s`      | `[false, true]`       | `[1, 0]`          |
| whisker `t·t·s` | `[false, false, true]`| `[2, 0]`          |
| body `s·t`      | `[true, false]`       | `[0, 1]`          |
| whisker `t·s·t` | `[false, true, false]`| `[1, 1]`          |

The naive concat `finestGapWidths [false] ++ finestGapWidths [false, true] = [1] ++ [1, 0] = [1, 1, 0]`, but the
TRUE `finestGapWidths ([false] ++ [false, true]) = finestGapWidths [false, false, true] = [2, 0]`.  They DIFFER
(`[1, 1, 0] ≠ [2, 0]`): the frame's trailing gap WIDENS the body's leading gap (`last(frame) + first(body)`), it
does NOT open a new slot.  This is precisely the r8 failure mode (a false concatenation invariance), REFUTED before
the whisker cell-surgery design (node (ii)) is written.

## What ships (each zero-axiom, STRUCTURAL / `rfl` / `decide`, ASCII-only, full-enum — propext-free)

  * **`bumpHead`** — add a bump into the head of a width list (`[] ↦ [bump]`, `first :: rest ↦ (bump+first) :: rest`).
    The accumulator-shift operator, full-enum on the `List` head.
  * **`finestGapWidthsAux_bumpHead`** — the accumulator SHIFT law: `finestGapWidthsAux (bump + currentGap) tags
    = bumpHead bump (finestGapWidthsAux currentGap tags)`.  A nonzero starting accumulator merely bumps the head of
    the shape.  Structural on the tag list; `Nat.add_assoc` at the gap-widening step (clean, no `add_mul`).
  * **`finestGapWidthsAux_nonempty`** — the shape is always a non-empty list (it emits at least the trailing gap):
    the load-bearing fact that the merge lands on a real head, not the empty-list arm.
  * **`foldBodyAtTail`** — replace the TRAILING width of a width list by folding `body` from it as the starting
    accumulator (the "widen the last slot" operator).
  * **`finestGapWidthsAux_append`** — ★ THE MERGE LAW: `finestGapWidthsAux c (frame ++ body)
    = foldBodyAtTail (finestGapWidthsAux c frame) body`.  The frame's trailing gap becomes the body's starting
    accumulator — the `last(frame) + first(body)` merge, structurally.
  * **`finestGapWidths_tRunFrame`** — a pure-`t` frame of length `n` reads `[n]`: the whisker-frame contribution is
    a single trailing gap that folds into the body's leading gap.
  * **`finestGapWidths_naiveConcatRefuted`** — the r8 self-attack, machine-checked: naive concat `≠` true merge.
  * **`finestGapWidths_frameMergesIntoBody`** — the merge confirmed on the concrete probe (`[2, 0]`).

## What STAYS WALLED (no flip)

This ships the WIDTH-level merge law (node ii's arithmetic layer) — NOT the CELL-level `mergeFrameIntoHead/Tail`
surgery (node ii's genuine `VcompGapPair` head/tail fuse riding a `composePath` junction cast), which is deferred
(B4).  The merge is authored here only for PURE-`t` frames (`false`-runs); an `s`-bearing frame SPLITS the whisker
and shifts downstream walls (the wire-changing case).  `fxAmalg_hasFullSaturatedPushoutDispatch`
(`DispatchSaturated.lean`) STAYS `false`; `fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`;
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  #2043 does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The accumulator-shift operator and its law -/

/-- **Bump the head of a width list** — add `bump` into the leading width, or open `[bump]` on the empty list.
Full-enum on the `List` head (propext-free).  This is what a nonzero starting accumulator does to a finest shape. -/
def bumpHead (bump : Nat) : List Nat → List Nat
  | [] => [bump]
  | first :: rest => (bump + first) :: rest

/-- ★ **The accumulator-shift law.**  Starting `finestGapWidthsAux` from `bump + currentGap` instead of
`currentGap` merely bumps the head of the resulting shape by `bump`: the extra `bump` gap-width flows entirely into
the FIRST slot.  Structural on the tag list — the base and wall (`true`) cases are `rfl` (the head is the current
gap), the gap (`false`) case re-associates the accumulator (`Nat.add_assoc`, clean) and recurses. -/
theorem finestGapWidthsAux_bumpHead (bump : Nat) :
    (currentGap : Nat) → (tags : List Bool) →
    finestGapWidthsAux (bump + currentGap) tags = bumpHead bump (finestGapWidthsAux currentGap tags)
  | currentGap, [] => rfl
  | currentGap, true :: rest => rfl
  | currentGap, false :: rest => by
      show finestGapWidthsAux (bump + currentGap + 1) rest
          = bumpHead bump (finestGapWidthsAux (currentGap + 1) rest)
      rw [Nat.add_assoc]
      exact finestGapWidthsAux_bumpHead bump (currentGap + 1) rest

/-- The finest shape is ALWAYS a non-empty list — it emits at least the trailing gap.  Structural on the tag list
(the `false` case recurses; the `[]` and `true` cases expose the head directly).  The load-bearing fact that the
whisker merge lands on a real head slot, not the empty-list arm of `foldBodyAtTail`. -/
theorem finestGapWidthsAux_nonempty :
    (currentGap : Nat) → (tags : List Bool) →
    ∃ (headWidth : Nat) (tailWidths : List Nat),
      finestGapWidthsAux currentGap tags = headWidth :: tailWidths
  | currentGap, [] => ⟨currentGap, [], rfl⟩
  | currentGap, true :: rest => ⟨currentGap, finestGapWidthsAux 0 rest, rfl⟩
  | currentGap, false :: rest => finestGapWidthsAux_nonempty (currentGap + 1) rest

/-! ## The trailing-fold merge operator and the append law -/

/-- **Fold `body` at the trailing width** — replace the LAST width of a width list by folding `body` from it as the
starting accumulator, keeping the earlier widths.  The empty-list arm is defensive (`finestGapWidthsAux` shapes are
never empty).  Structural on the width list. -/
def foldBodyAtTail (body : List Bool) : List Nat → List Nat
  | [] => finestGapWidthsAux 0 body
  | lastWidth :: [] => finestGapWidthsAux lastWidth body
  | first :: second :: rest => first :: foldBodyAtTail body (second :: rest)

/-- ★★ **THE WHISKER-FRAME GAP-MERGE LAW.**  The finest shape of a concatenated tag sequence folds the frame's
TRAILING gap into the body: `finestGapWidthsAux c (frame ++ body) = foldBodyAtTail body (finestGapWidthsAux c frame)`
— the frame's last accumulated gap becomes the body's starting accumulator (`last(frame) + first(body)`).  This is
the CORRECT merge the naive concat (`finestGapWidths frame ++ finestGapWidths body`) gets WRONG.  Structural on the
frame: the `true` (wall) case exposes the fresh head via `finestGapWidthsAux_nonempty` so the fold recurses past it;
the `false` (gap) case widens the carried accumulator. -/
theorem finestGapWidthsAux_append (body : List Bool) :
    (currentGap : Nat) → (frame : List Bool) →
    finestGapWidthsAux currentGap (frame ++ body)
      = foldBodyAtTail body (finestGapWidthsAux currentGap frame)
  | currentGap, [] => rfl
  | currentGap, false :: rest => finestGapWidthsAux_append body (currentGap + 1) rest
  | currentGap, true :: rest => by
      show currentGap :: finestGapWidthsAux 0 (rest ++ body)
          = foldBodyAtTail body (currentGap :: finestGapWidthsAux 0 rest)
      obtain ⟨headWidth, tailWidths, hshape⟩ := finestGapWidthsAux_nonempty 0 rest
      rw [hshape]
      show currentGap :: finestGapWidthsAux 0 (rest ++ body)
          = currentGap :: foldBodyAtTail body (headWidth :: tailWidths)
      rw [← hshape]
      exact congrArg (currentGap :: ·) (finestGapWidthsAux_append body 0 rest)

/-! ## The pure-`t` frame contribution -/

/-- A **pure-`t` whisker frame of length `n`** reads finest widths `[currentGap + n]` — a single accumulated gap, no
new slot.  This is the whisker-frame contribution: a `t`-run does NOT open a wall slot, it only widens the running
gap.  Structural on the run length. -/
theorem finestGapWidths_tRunFrame :
    (runLength : Nat) → (currentGap : Nat) →
    finestGapWidthsAux currentGap (List.replicate runLength false) = [currentGap + runLength]
  | 0, currentGap => rfl
  | runLength + 1, currentGap => by
      show finestGapWidthsAux (currentGap + 1) (List.replicate runLength false) = [currentGap + (runLength + 1)]
      rw [finestGapWidths_tRunFrame runLength (currentGap + 1), Nat.add_assoc, Nat.add_comm 1 runLength]

/-! ## The r8 self-attack, machine-checked (FIRST) -/

-- The naive concat of the frame `t` and body `t·s` shapes: expect `[1, 1, 0]`.
#eval finestGapWidths [false] ++ finestGapWidths [false, true]
-- The TRUE merged shape of the whisker `t·t·s`: expect `[2, 0]`.
#eval finestGapWidths ([false] ++ [false, true])

/-- ★★★ **THE NAIVE-CONCAT REFUTATION (the r8 self-attack, machine-checked).**  The naive concatenation
`finestGapWidths frame ++ finestGapWidths body` DIFFERS from the true `finestGapWidths (frame ++ body)` on the
concrete whisker `t · (t·s)`: naive `[1] ++ [1, 0] = [1, 1, 0]`, true `[2, 0]`.  So the whisker-case design "prepend
the frame's gap slots to the body's" is FALSE — the frame's trailing gap MERGES into (widens) the body's leading
gap, it does not open a fresh slot.  Refuted before the cell-level surgery (node ii) is written.  `decide` on the
literal `List Nat` inequality (closed data — propext-free). -/
theorem finestGapWidths_naiveConcatRefuted :
    (finestGapWidths [false] ++ finestGapWidths [false, true])
      ≠ finestGapWidths ([false] ++ [false, true]) := by decide

/-- ★★ **The merge CONFIRMED on the concrete probe.**  The whisker `t · (t·s)` reads finest widths `[2, 0]` — the
frame's `t` (`[1]`) merged its trailing gap into the body's leading gap (`[1, 0]`), yielding `[1 + 1, 0] = [2, 0]`,
exactly the `foldBodyAtTail`/`last(frame) + first(body)` law.  `rfl` on the shape. -/
theorem finestGapWidths_frameMergesIntoBody :
    finestGapWidths ([false] ++ [false, true]) = [2, 0] := rfl

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the whisker-frame GAP-MERGE law SHIPS at the width level; the naive concat is REFUTED
(WP-AMALG-2 r10, B2).**  `= true`: `finestGapWidthsAux_append` proves `finestGapWidths (frame ++ body)` folds the
frame's trailing gap into the body (`foldBodyAtTail`, the `last(frame) + first(body)` merge), with the
accumulator-shift primitive `finestGapWidthsAux_bumpHead` and the nonemptiness fact `finestGapWidthsAux_nonempty` as
its structural spine, and `finestGapWidths_tRunFrame` recording that a pure-`t` frame contributes a single trailing
gap.  The r8 self-attack `finestGapWidths_naiveConcatRefuted` machine-checks that the NAIVE concatenation
(`finestGapWidths frame ++ finestGapWidths body`) is WRONG (`[1,1,0] ≠ [2,0]`), refuting the whisker-case
"prepend frame slots" design before the cell surgery is attempted.  This is the WIDTH-level (arithmetic) layer of
node (ii); the CELL-level `mergeFrameIntoHead/Tail` `VcompGapPair` surgery (riding a `composePath` junction cast)
is the deferred B4 node.  Authored for PURE-`t` frames only; `s`-bearing frames are the wire-changing residual.  No
marker flips.  `= true`. -/
def fxAmalg_hasFinestGapMerge : Bool := true

end FX1Poly.Polygraph.Amalgam
