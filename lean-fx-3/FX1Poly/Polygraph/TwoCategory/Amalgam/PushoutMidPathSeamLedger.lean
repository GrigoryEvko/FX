import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutVcompSeam

/-! # Polygraph/TwoCategory/Amalgam/PushoutMidPathSeamLedger — the r9 LEDGER: the midPath seam BYPASSES the r8 jam,
the residual sharpens to the reconstruction-inversion, and NOTHING flips (WP-AMALG-2 r9, B5)

r8 truth-probed the recon's wall-BLOCK alignment FIRST and refuted it (the `s`-block list is not a dom-to-cod
invariant), jamming the vcomp case at `vcomp (gapVcompLayout fwU pairsU) (gapVcompLayout fwL pairsL) ~ gapVcompLayout
fw pairs` — an attempt to ZIP two SEPARATE recursive layouts on a shared wall scaffold that does not exist.  r9
BYPASSES that jam by re-keying off the refuted wall scaffold onto the wall-COUNT-invariant FINEST decomposition, and
matching the seam through the shared MIDDLE 1-cell.  This file records the r9 section of the ledger: what shipped,
how the r8 jam is bypassed, the precisely-sharpened residual (the named node), the no-flip verdict, and what the next
arc inherits.  It flips NOTHING.

## What r9 shipped (each machine-checked, zero-axiom, independently `#print axioms`-clean)

  * **`PushoutFinestLayout.lean`** (B1/B2) — the finest gap-width shape (`finestGapWidths`, keyed to the conserved
    wall COUNT), the r8-word TRUTH-PROBE (`unitSplitsWall_finestSlotCount_domCod_eq`: the domain `s·s` `[0, 0, 0]` and
    the codomain `s·t·s` `[0, 1, 0]` have the SAME slot count — the empty-gap admission, machine-checked), and the
    empty-gap re-expression FREE leg (`emptyGapLayout_conv_id`: a `nil`-gap pair with identity payload collapses to
    the identity on the merged wall, over any signature).
  * **`PushoutVcompSeam.lean`** (B3/B4) — the SEAM (`pushoutFactorizeVcompSeam`: two finest-aligned half-cells vcomp
    into `gapVcompLayout`, keyed to the shared `gapMidLayout`, firing the r7 crux) and its
    `PushoutLayoutFactorization` packaging (`pushoutFactorizeVcompLayout`), plus the COMPOSED-r8 witness
    (`vcompSplitBlockFactorization`: `vcomp unitSplitsWallCell unitThenFaceLowerCell : s·s ==> s·t·t·s` FACTORS
    through the single shared block `[vcompSplitBlockPair]`, the empty `gapDom = nil` absorbing the r8 wall-block
    split).

## How the r8 jam is bypassed (the re-keying)

r8's jam formed TWO separate `gapVcompLayout`s (one per vcomp factor) and tried to vcomp them into ONE, needing a
shared wall scaffold to align the two `pairs` lists — refuted.  r9 never forms two `gapVcompLayout`s.  It factors the
TWO HALF-CELLS of a single vertical composite through ONE SHARED `(finalWall, pairs)` — the finest slots of the
MIDDLE 1-cell `midPath` (a function of the word, keyed to the conserved wall count) — as `gapUpperLayout` (top,
`gapDomLayout ⇒ gapMidLayout`) and `gapLowerLayout` (bottom, `gapMidLayout ⇒ gapCodLayout`), then fires the crux
`vcompGapInterchangeSplice` (`vcomp (gapUpperLayout …) (gapLowerLayout …) ≈ gapVcompLayout …`).  The alignment is the
shared `pairs`, NOT a wall scaffold; the empty `gapDom = nil` slot absorbs exactly the r8 block-split.  The r8 jam is
gone — not zipped, dissolved.

## The precisely-sharpened residual (the named node)

The seam discharges the vcomp case GIVEN two finest-aligned half-factorizations.  The TOTAL `pushoutFactorize` (an
ARBITRARY pushout cell factors) needs to PRODUCE those factorizations for every cell, which the seam does NOT do.
The remaining goal, named at WORD granularity:

  For an arbitrary `cell : RawTwoCellExpr … sourcePath targetPath`, build `PushoutLayoutFactorization baseRel cell`
  by structural induction — the `id` case ships (`pushoutFactorizeId`), the `vcomp` case is the seam GIVEN the two
  sub-factorizations, but the `gen` and `whisker` cases jam on:

  (1) **the per-gap RECONSTRUCTION-INVERSION** — recognize an arbitrary pure-`t` gap cell as `mapCellAlong inclRight
      (monadCell)`, the CONVERSE of `interpretWordFrom_map`, so a `gen`'s wall-free boundary reads as a single gap
      slot with the generator inside it;
  (2) **the whisker-frame `t`-run MERGE** — a whiskering's frame `t`-run merges with the body's leading / trailing
      gap (`hcomp (id oneCell_t-run) (body_leading_gap_cell)`), a genuine case analysis with junction
      cast-bookkeeping (the one place `castBoundary` can reappear).

Named node: **the per-gap reconstruction-inversion + the whisker-frame `t`-run merge of the top-level
`pushoutFactorize` induction** (keyed to the finest decomposition of the middle 1-cell, not a shared wall scaffold).
This is a separate multi-round arc; the seam NARROWS the wall to it but does not remove it.

## HELD — no flip (the honest r9 verdict)

`fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS `false` — the seam is not the
arbitrary-cell coverage its demand's residual (iii) requires; `fxAmalg_hasGeneralPushoutDispatch`
(`PushoutBundle.lean`) STAYS `false`; `fxAmalg_topFactorizationInductionStaysWalled`
(`PushoutVcompInterchangeSplice.lean`) / `fxAmalg_factorizationCompletenessStaysWalled`
(`PushoutWireChangeLedger.lean`) / `fxAmalg_arbitraryCellFactorizationStaysWalled`
(`PushoutMultiGapFactorization.lean`) STAY `true`.  **#2043 does NOT close.**  This file adds markers ONLY; it
touches no shipped marker.  No fabricated flip.

## What the next arc inherits (scope note)

The reconstruction-inversion (the converse of `interpretWordFrom_map`) and the whisker-frame `t`-run merge, both
INSIDE the disjoint `involution +_M monad` scope (the composed-r8 witness uses only the pushout's own `s`, `eta`,
`δ₁`).  The seam and the finest decomposition are the missing scaffolding those two cases will stand on.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The shipped r9 ingredients, machine-witnessed -/

-- THE EMPTY-GAP ADMISSION — the r8 counterexample's two boundaries read the SAME finest slot count.
#check @unitSplitsWall_finestSlotCount_domCod_eq
-- THE EMPTY-GAP FREE LEG — a `nil`-gap pair collapses to the identity, free.
#check @emptyGapLayout_conv_id
-- THE SEAM — two finest-aligned half-cells vcomp into `gapVcompLayout` through the shared middle 1-cell.
#check @pushoutFactorizeVcompSeam
-- THE COMPOSED-r8 WITNESS — the r8 counterexample composed FACTORS end-to-end.
#check @vcompSplitBlockFactorization
-- The master demand STAYS false (referenced, not touched).
#check @fxAmalg_hasFullSaturatedPushoutDispatch

/-! ## Honesty markers — the r9 ledger -/

/-- ★★★ **Honesty marker — r9 BYPASSES the r8 jam via the midPath seam and FLIPS NOTHING; #2043 stays OPEN.**
`= true` (the honest r9 verdict).  r8 jammed the vcomp case at `vcomp (gapVcompLayout fwU pairsU) (gapVcompLayout fwL
pairsL) ~ gapVcompLayout fw pairs` (zip two separate layouts on a refuted wall scaffold).  r9 re-keys off the
refuted scaffold onto the wall-COUNT-invariant FINEST decomposition (`PushoutFinestLayout.lean`: the empty-gap
admission, machine-checked on the r8 word — `s·s` and `s·t·s` read the SAME slot count) and matches the seam through
the shared MIDDLE 1-cell (`PushoutVcompSeam.lean`: `pushoutFactorizeVcompSeam` fires the r7 crux on ONE shared
`pairs`, never forming two `gapVcompLayout`s).  The composed-r8 counterexample — the r8 refuting cell vcomp a face
firing inside its split block — FACTORS end-to-end (`vcompSplitBlockFactorization : s·s ==> s·t·t·s`).  This did NOT
ship the top-level `pushoutFactorize`, and FLIPPED NO marker: `fxAmalg_hasFullSaturatedPushoutDispatch`
(`DispatchSaturated.lean`) STAYS `false`, `fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`,
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  #2043 does NOT close — no fabricated flip.  `= true`. -/
def fxAmalg_r9SeamBypassesR8Jam : Bool := true

/-- ★★ **Honesty marker — the residual sharpens to the RECONSTRUCTION-INVERSION + whisker-frame merge, inside the
DISJOINT scope.**  `= true` (the wall honestly held, precisely named).  The seam (`pushoutFactorizeVcompSeam`)
discharges the vcomp case GIVEN two finest-aligned half-factorizations; the composed-r8 witness confirms it
end-to-end.  The TOTAL `pushoutFactorize` (an arbitrary cell factors) does NOT close: its `gen` / `whisker` cases jam
on (1) the per-gap RECONSTRUCTION-INVERSION — recognize an arbitrary pure-`t` gap as `mapCellAlong inclRight
(monadCell)`, the converse of `interpretWordFrom_map`, so a wall-free `gen` boundary reads as a single gap slot; and
(2) the whisker-frame `t`-run MERGE — a whiskering's frame `t`-run merges with the body's leading / trailing gap,
junction cast-bookkeeping (the one place `castBoundary` can reappear).  Named node: **the per-gap
reconstruction-inversion + the whisker-frame `t`-run merge of the top-level `pushoutFactorize` induction** (keyed to
the finest decomposition of the middle 1-cell).  Both obstructions live INSIDE the disjoint `involution +_M monad`
scope (the composed-r8 witness uses only the pushout's own `s`, `eta`, `δ₁`), so the arc is authorable here — but it
is a separate multi-round arc, not co-closeable with the seam.  `fxAmalg_hasFullSaturatedPushoutDispatch` STAYS
`false`.  No fabricated flip.  `= true`. -/
def fxAmalg_r9ReconstructionInversionResidual : Bool := true

end FX1Poly.Polygraph.Amalgam
