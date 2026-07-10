import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutLayoutFactorization

/-! # Polygraph/TwoCategory/Amalgam/PushoutWallBlockRefutationLedger — the r8 LEDGER: the wall-block alignment is
REFUTED, the residual SHARPENS, and NOTHING flips (WP-AMALG-2 r8, B3/B4/B5)

r8 truth-probed the recon's route to the top-level `pushoutFactorize` FIRST, and the load-bearing alignment premise
(`wallBlocks_dom_eq_cod`) turned out FALSE.  This file records the r8 section of the ledger: what shipped, the exact
jam it exposes in the vcomp case, the precisely-sharpened residual, the no-flip verdict, and what WP-AMALG-3
inherits.  It flips NOTHING.

## What r8 shipped (each machine-checked, zero-axiom)

  * **`PushoutWallBlockScaffold.lean`** — the wall-block read-off (`pushoutPathWord` + the shipped
    `pushoutWallBlocks` / `blockDecompose`) and the REFUTATION: `unitSplitsWallCell` (`whiskerLeft s (whiskerRight s
    eta) : s·s ==> s·t·s`) has domain wall-blocks `[[s, s]]` and codomain wall-blocks `[[s], [s]]`
    (`unitSplitsWall_dom_wallBlocks` / `unitSplitsWall_cod_wallBlocks`, `rfl`); their lengths DIFFER
    (`unitSplitsWall_wallBlockCount_domCod_differ`), while the total wall COUNT is conserved
    (`unitSplitsWall_wallCount_preserved`, via r6's `wallLetterCount_dom_eq_cod`).
  * **`PushoutLayoutFactorization.lean`** — the factorization MOTIVE + the `id` case + the POSITIVE counterpoint
    (`unitSplitsWallFactorization`: the same wall-splitting cell nonetheless factors as an `eta`-gap layout, `rfl`
    casts).  The factorization GOAL survives; the wall-block ALIGNMENT strategy does not.

## The exact jam (the vcomp case)

The recon's vcomp case recurses `factorize cellUp -> (fwU, pairsU, ...)` and `factorize cellLo -> (fwL, pairsL,
...)`, then ZIPS `pairsU` with `pairsL` because they were claimed to share a rigid wall scaffold
(`wallBlocks_dom_eq_cod`).  That zip is BLOCKED: the wall-block list is not a dom-to-cod invariant
(`unitSplitsWall_wallBlockCount_domCod_differ`), so even a SINGLE cell's domain and codomain need not share a wall
scaffold, let alone `cellUp`'s codomain scaffold matching `cellLo`'s domain scaffold across the vcomp seam.  Named
goal: `SaturatedConvOver ... (vcomp (gapVcompLayout fwU pairsU) (gapVcompLayout fwL pairsL)) (gapVcompLayout fw
pairs)` for a SINGLE `(fw, pairs)` — unreachable via the wall-block zip, because no dom/cod-invariant wall scaffold
`fw` exists to key `pairs` to.

## The precisely-sharpened residual (the named node)

The reconstruction bridge cannot be keyed to a wall SCAFFOLD (as the r7 ledger's "keyed to B1's wall skeleton"
sketched): no dom-to-cod-invariant wall skeleton finer than the total COUNT exists (the wire-creating `eta` splits
`s`-blocks; the total count is too coarse to key the per-gap zip).  The alignment must instead be a PER-CELL block
reconciliation that admits EMPTY `t`-gaps (so that an `s·s` domain and an `s·t·s` codomain read as the SAME number
of gap slots — the `t`-gap merely widens from `0` to `1`), matching the vcomp seam through the shared MIDDLE 1-cell
`midPath`, NOT through a shared wall skeleton.  This is the machine-confirmed content of the master demand's
residual (iii) (`DispatchSaturated.lean`: "the unit/counit WIRE-CREATING generators break the convex-block
projection").  Named node: **the per-cell empty-gap-admitting block reconciliation for the vcomp seam of
`pushoutFactorize`** (keyed to the middle 1-cell, not a shared wall scaffold).

## HELD — no flip (the honest r8 verdict)

`fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS `false`;
`fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`;
`fxAmalg_factorizationCompletenessStaysWalled` / `fxAmalg_pushoutNormalFormSpliceStaysWalled` /
`fxAmalg_arbitraryCellFactorizationStaysWalled` / `fxAmalg_topFactorizationInductionStaysWalled` STAY `true`.
**#2043 does NOT close.**  This file adds markers ONLY; it touches no shipped marker.  No fabricated flip.

## What WP-AMALG-3 inherits (scope note)

The r7 ledger framed the residual as "WP-AMALG-3 inherits the shared-generator scope".  r8 SHARPENS the scoping: the
wall-splitting obstruction to a wall-block-canonical bridge is INSIDE the DISJOINT `involution +_M monad` scope (the
counterexample cell uses only the disjoint pushout's own `s`-wall and `eta`), so the per-cell empty-gap-admitting
reconciliation is authorable HERE, not deferred to a shared-generator setting.  WP-AMALG-3 inherits: (1) that
reconciliation (the sharpened node above); (2) the still-open per-gap reconstruction-inversion (recognize an
arbitrary pure-`t` gap as `mapCellAlong inclRight (monadCell)` — the converse of `interpretWordFrom_map`), which the
per-gap decider needs; (3) the shared-generator scope proper.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The shipped r8 ingredients, machine-witnessed -/

-- THE REFUTATION — the wall-block list is not a dom-to-cod invariant (lengths differ).
#check @unitSplitsWall_wallBlockCount_domCod_differ
-- Yet the wall COUNT is conserved — the refutation is precise (count yes, blocks no).
#check @unitSplitsWall_wallCount_preserved
-- THE POSITIVE COUNTERPOINT — the wall-splitting cell nonetheless factors (goal survives, strategy refuted).
#check @unitSplitsWallFactorization
-- The master demand STAYS false (referenced, not touched).
#check @fxAmalg_hasFullSaturatedPushoutDispatch

/-! ## Honesty markers — the r8 ledger -/

/-- ★★★ **Honesty marker — r8 REFUTES the wall-block alignment and FLIPS NOTHING; #2043 stays OPEN.**  `= true`
(the honest r8 verdict).  This round shipped the wall-block read-off + the machine-checked REFUTATION of
`wallBlocks_dom_eq_cod` (`PushoutWallBlockScaffold.lean`: `unitSplitsWallCell : s·s ==> s·t·s` has domain
wall-blocks `[[s, s]]` but codomain wall-blocks `[[s], [s]]` — the wire-creating `eta` splits an `s`-block, so the
wall-block list is NOT a dom-to-cod invariant; only the COUNT is), the factorization MOTIVE + `id` case + the
POSITIVE counterpoint (`PushoutLayoutFactorization.lean`: the same cell factors as an `eta`-gap layout, so the
factorization GOAL survives).  It did NOT ship the top-level `pushoutFactorize`, and it FLIPPED NO marker:
`fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS `false`,
`fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`,
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  The advance: the recon's vcomp-case zip is REFUTED at
its wall-block premise, so the residual sharpens from "reconstruction bridge keyed to the wall skeleton" to "per-cell
empty-gap-admitting block reconciliation keyed to the middle 1-cell".  #2043 does NOT close — no fabricated flip.
`= true`. -/
def fxAmalg_r8WallBlockRefutesAlignment : Bool := true

/-- ★★ **Honesty marker — the residual SHARPENS to the empty-gap-admitting seam reconciliation, inside the DISJOINT
scope.**  `= true` (the wall honestly held, precisely sharpened).  The r7 residual (`reconstruction bridge keyed to
B1's wall skeleton`) is under-determined: NO dom-to-cod-invariant wall skeleton finer than the total `s`-count
exists (`unitSplitsWall_wallBlockCount_domCod_differ`), and the total count is too coarse to key the per-gap zip.
The general vcomp case therefore jams at `vcomp (gapVcompLayout fwU pairsU) (gapVcompLayout fwL pairsL) ~
gapVcompLayout fw pairs` for a single `(fw, pairs)` — unreachable via a shared wall scaffold.  The named node is the
PER-CELL block reconciliation that admits EMPTY `t`-gaps and matches the vcomp seam through the shared MIDDLE 1-cell
`midPath` (not a shared wall skeleton) — the machine-confirmed content of the master demand's residual (iii) (the
WIRE-CREATING `eta` splits `s`-blocks).  This obstruction lives INSIDE the disjoint `involution +_M monad` scope
(the counterexample uses only the pushout's own `s` and `eta`), so the reconciliation is authorable HERE; WP-AMALG-3
additionally inherits the per-gap reconstruction-inversion (the converse of `interpretWordFrom_map`) and the
shared-generator scope proper.  `fxAmalg_hasFullSaturatedPushoutDispatch` STAYS `false`.  No fabricated flip.
`= true`. -/
def fxAmalg_r8ResidualSharpenedNoFlip : Bool := true

end FX1Poly.Polygraph.Amalgam
