import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreeCellInvert
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestBoundaries
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutKeystoneUnlockLedger

/-! # Polygraph/TwoCategory/Amalgam/PushoutCellConverseLedger — the r12 LEDGER: the wall-free CELL converse ships
FORWARD (all five constructors) + the gen backward SECTION; the three masters HOLD (WP-AMALG-2 r12, the cell-converse
round)

The r11 ledger (`PushoutKeystoneUnlockLedger.lean`) closed `pathInvert` (B1) and `finestLayout` (B2) and scoped the
CELL-level `wallFreeCellInvert` — the essential-surjectivity converse feeding `pushoutRightImageConvReflect` — as
cast-heavy LABOR (not undecidability) to r12.  r12 delivered the FORWARD cell converse in full and the gen-case
backward SECTION, and shipped the Finding-A first-zip prerequisite.  This file records the r12 section of the ledger:
the shipped nodes, the accounting updated per TRUTH, the still-open nodes each named with an exact goal, and the
HELD-no-flip verdict.  It flips NOTHING.

## What r12 SHIPPED (machine-checked, zero-axiom)

  * **The generator reseat crux `wallFreeGenInvert`** — a pushout 2-generator at a wall-free boundary reconstructs its
    MONAD 2-generator at the `pathInvert` boundary, the CONVERSE of `interpretWordFrom_map`.  Engine:
    `monadInterpOfPushoutInterp` (the pushout interpretation, being the `mapPath`-image of the monad interpretation,
    pins the monad pre-image; the dependent-Sigma extraction made propext-safe by the WORD projection
    `pushoutPathWord ∘ .snd` BEFORE `Option.some.inj`).  Index by `retractRightTwoGen` (offset `0`).  TRUTH-PROBED:
    the pushout unit inverts to monad `eta` (index `0`), the multiplication to monad `mu` (index `1`).

  * **The wall-free SPLIT/JOIN + `pathInvert_composePath`** — the whisker-case ingredients: `pathWallFree` splits and
    joins over `composePath` (structural, no wall-count arithmetic), and `pathInvert` distributes over `composePath`
    (WORD route via `monadPathWord_injective` + a propext-free `mapAppendDistrib`).

  * **The four-case structural recursion `wallFreeCellInvert`** — `gen` via the crux, `id`/`vcomp` cast-free (middle
    from `wallFreeMiddleOfCell`), the two whisker cases through the single `castBoundary (pathInvert_composePath …)`,
    byte-for-byte `mapCellAlong`'s shape.  The gen boundary modes are universally quantified (the whisker case supplies
    an existential middle mode) and collapse to `monadPushMode` by `pushoutModeUnique` (`subst`).  PROBED on a concrete
    cell of EVERY constructor (`id`/`gen`/`vcomp` by size `rfl`; `whiskerLeft`/`whiskerRight` by typechecking through
    `pathInvert_composePath`).

  * **The gen-case BACKWARD SECTION** — `wallFreeGenInvert_onTwoCell_index_roundTrip`: inverting a reconstructed
    generator then re-coprojecting through `inclusionRightTwoReal`'s `onTwoCell` returns to the ORIGINAL 2-generator
    index (`embedRightTwoGen ∘ retractRightTwoGen = id`).  The reseat is a genuine SECTION of the coprojection, not
    merely a same-boundary map.

  * **Finding-A first-zip (`PushoutFinestBoundaries.lean`)** — `gapMidLayout_finestLayout` + `gapCodLayout_finestLayout`:
    `finestLayout G` presents `G` on ALL THREE boundaries (dom = mid = cod), the legal shared `(finalWall, pairs)` the
    r9 vcomp seam consumes on BOTH halves of a `vcomp`.

## The r11 open-node accounting, updated per TRUTH

  * **`wallFreeCellInvert` (forward) — CLOSED** (`PushoutWallFreeCellInvert.lean`).  The full four-case recursion
    ships; the gen crux is the converse of `interpretWordFrom_map`, delivered.

  * **`wallFreeCellInvert` backward round-trip (CELL level) — PARTIAL → follow-on.**  The gen-case SECTION ships (index
    round-trip).  The full `mapCellAlong inclRight ∘ wallFreeCellInvert = castBoundary … cell` is a
    `reseatCellInv_reseatCell`-style FUEL assembly (per-case `mapCellAlong_castBoundary` + `castBoundary`-fusion step
    theorems, over the mode-generic whisker recursion) — LABOR, not undecidability, scoped to a follow-on round.  Named
    node: **the fuel-recursion cell round-trip + the whisker cast-fusion step theorems**.

  * **Finding-A payload zip — the STRUCTURE ships, the PAYLOADS do not.**  `finestLayout G` presents `G` on all three
    boundaries (this round), a legal shared layout for the seam.  The genuine cell-level re-slice (re-expressing two
    payload-bearing factorizations against `finestLayout G`'s slots, consuming `finestGapWidthsAux_append` at the cell
    level) is the remaining Finding-A labor — named node: **the payload-carrying finest common-refinement zip**.

  * **Finding-C (the multi-gap NORMAL-FORM splice) — STILL CROSS-LANE BLOCKED** on `WalkingMonad.wordMul_vcomp`
    (CONSUME-only, the `WalkingMonad/` READ-ONLY lane); untouched.

## HELD — the three masters do NOT flip (the honest r12 verdict)

`wallFreeCellInvert` is the FORWARD essential-surjectivity converse at the cell level — a genuine new rung.  But the
masters' VERBATIM demands need the FULL two-sided decision (whose isTrue leg needs the backward cell round-trip
GENERAL theorem, the follow-on node) AND the residual (iii) purification/projection COMPLETENESS (essential-surjectivity,
not completeness — untouched by the cell converse), AND the Finding-A payload zip, AND the Finding-C cross-lane splice.
So, per their VERBATIM demands:

  * `fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS `false`.
  * `fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`.
  * `fxAmalg_topFactorizationInductionStaysWalled` (`PushoutVcompInterchangeSplice.lean`) STAYS `true`.

**#2043 does NOT close.**  This file adds markers ONLY; it touches no shipped marker.  No fabricated flip.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The shipped r12 nodes, machine-witnessed -/

-- The generator reseat crux + its engine + the two truth probes (eta -> 0, mu -> 1).
#check @wallFreeGenInvert
#check @monadInterpOfPushoutInterp
#check @wallFreeGenInvert_unit_index
#check @wallFreeGenInvert_mult_index
-- The whisker-case ingredients: wall-free split/join + pathInvert distributes over composition.
#check @pathWallFree_composePath_split
#check @pathWallFree_composePath_join
#check @pathInvert_composePath
-- The four-case forward cell converse.
#check @wallFreeCellInvert
-- The gen-case backward SECTION (the reseat index round-trips).
#check @wallFreeGenInvert_onTwoCell_index_roundTrip
-- Finding-A first-zip: finestLayout presents G on all three boundaries.
#check @gapMidLayout_finestLayout
#check @gapCodLayout_finestLayout
-- The three masters STAY put (referenced, not touched).
#check @fxAmalg_hasFullSaturatedPushoutDispatch
#check @fxAmalg_hasGeneralPushoutDispatch
#check @fxAmalg_topFactorizationInductionStaysWalled

/-! ## Honesty markers — the r12 ledger -/

/-- ★★★ **Honesty marker — the wall-free CELL converse ships FORWARD (all five constructors) + the gen backward
SECTION; #2043 stays OPEN.**  `= true` (the honest r12 verdict).  r11 scoped `wallFreeCellInvert` (the
essential-surjectivity converse) as cast-heavy LABOR to r12.  r12 delivered: the generator reseat crux
`wallFreeGenInvert` (the CONVERSE of `interpretWordFrom_map`, TRUTH-PROBED eta->0 / mu->1), the wall-free split/join +
`pathInvert_composePath`, the four-case forward recursion `wallFreeCellInvert` (probed on a concrete cell of every
constructor), and the gen-case BACKWARD SECTION (`wallFreeGenInvert_onTwoCell_index_roundTrip`: the reseat is a genuine
section, `embedRightTwoGen ∘ retractRightTwoGen = id`).  The FULL cell backward round-trip (a
`reseatCellInv_reseatCell`-style fuel assembly) is scoped to a follow-on round.  FLIPPED NO master:
`fxAmalg_hasFullSaturatedPushoutDispatch` STAYS `false`, `fxAmalg_hasGeneralPushoutDispatch` STAYS `false`,
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  #2043 does NOT close — no fabricated flip.  `= true`. -/
def fxAmalg_r12CellConverseShips : Bool := true

/-- ★★ **Honesty marker — the r11 open-node accounting, updated per TRUTH.**  `= true` (the wall honestly held, each
node precisely named).  `wallFreeCellInvert` (forward): CLOSED (four-case recursion, the gen crux = converse of
`interpretWordFrom_map`).  `wallFreeCellInvert` backward CELL round-trip: PARTIAL — the gen-case index SECTION ships,
the full `mapCellAlong inclRight ∘ wallFreeCellInvert = castBoundary` fuel assembly (per-case cast-fusion step theorems)
scoped to a follow-on.  Finding-A: the STRUCTURE ships (`finestLayout G` presents `G` on dom = mid = cod), the
payload-carrying finest common-refinement zip remains.  Finding-C: STILL CROSS-LANE BLOCKED on
`WalkingMonad.wordMul_vcomp` (READ-ONLY).  Every jam is an exact goal with a named node.  `= true`. -/
def fxAmalg_r12NodeAccounting : Bool := true

/-- ★ **Honesty marker — r12 adds markers ONLY; the three masters and the arbitrary-cell decision stay put.**
`= true`.  `wallFreeCellInvert` is the FORWARD essential-surjectivity converse at the cell level — a genuine new rung,
NOT the two-sided arbitrary-cell DECISION the masters' demands require.  That decision stays blocked on the backward
cell round-trip GENERAL theorem (the follow-on node), the residual (iii) purification/projection COMPLETENESS
(essential-surjectivity, not completeness — untouched by the cell converse), the Finding-A payload zip, and the
Finding-C cross-lane splice.  The three walled markers (`fxAmalg_hasFullSaturatedPushoutDispatch`,
`fxAmalg_hasGeneralPushoutDispatch`, `fxAmalg_topFactorizationInductionStaysWalled`) are UNTOUCHED at `false` / `false`
/ `true`; r12 ships two additive source files (the cell converse, the finest all-boundary round-trips) plus this
ledger and their audit twins and its own AuditAll lines, and nothing in the `WalkingMonad/` READ-ONLY lane was edited.
No fabricated flip.  `= true`. -/
def fxAmalg_r12MastersHold : Bool := true

end FX1Poly.Polygraph.Amalgam
