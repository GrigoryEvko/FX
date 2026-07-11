import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreeInversionLedger
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreePathInversion
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestPairs
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreeCellConverse

/-! # Polygraph/TwoCategory/Amalgam/PushoutKeystoneUnlockLedger — the r11 LEDGER: the endo-mode-transport KEYSTONE
unlocks the two nearest r10 nodes; the three masters HOLD (WP-AMALG-2 r11, B5)

The r10 ledger (`PushoutWallFreeInversionLedger.lean`) factorized the residual to precisely-named nodes and found
the two NEAREST — `pathInvert` (B1) and `finestLayout` (B2) — "both blocked ONLY on the single-mode intermediate-mode
transport."  r11 AUTHORED that keystone transport and unlocked exactly those two.  This file records the r11 section
of the ledger: the keystone, the per-node accounting updated per TRUTH, the still-open nodes each named with an exact
goal, and the HELD-no-flip verdict.  It flips NOTHING.

## The keystone (r11 B1, `PushoutEndoModeTransport.lean`)

The endo-`ModalityPath`-at-single-mode TRANSPORT: the singleton fact (`pushoutModeUnique`: every pushout mode `=
monadPushMode`) ⟹ every 1-generator is an ENDO (`pushoutGenEndpoints`) ⟹ `pushoutEndoPathOfWord` re-types ANY
boundary word as an endo path at the single mode (the middle mode VANISHING, so no `Eq.rec`-through-a-type-level-
function), a bijection with `pushoutPathWord` via the reflection `pushoutPathWord_injective` (the direct port of
`monadPathWord_injective`).  This is the exact lemma the r10 ledger said "unlocks the two nearest nodes."

## The r10 open-node accounting, updated per TRUTH

  * **B1-`pathInvert` — CLOSED** (`PushoutWallFreePathInversion.lean`, r11 B2).  The wall-free 1-cell CONVERSE +
    BOTH round-trips (`mapPath_inclRight_pathInvert` forward, `pathInvert_mapPath_inclRight` reverse) — a genuine
    BIJECTION between monad 1-cells and wall-free pushout 1-cells at the single mode.  The essential-surjectivity
    half that was walled on the transport is now shipped; the injectivity half was already shipped (r10).

  * **B2-`finestLayout` — CLOSED** (`PushoutFinestPairs.lean`, r11 B3).  The cell-carrying PAIRS producer + the
    domain round-trip `gapDomLayout nil ∘ finestLayout = id` (via the word homomorphism + the r11 reflection).
    Per-letter granularity (the maximal refinement, one slot per letter, refining the r9 wall-count slot shape);
    identity cell payloads (the SHAPE, not the seam-firing content).

  * **B3-`wallFreeCellInvert` — PARTIAL → r12** (`PushoutWallFreeCellConverse.lean`, r11 B4).  Its clean structural
    PREREQUISITES ship: the `pathWallFree ↔ pushoutPathWallCount = 0` bridge and `wallFreeMiddleOfCell` (wall-freeness
    is dom-to-cod STABLE across any pushout 2-cell — the `vcomp`-case ingredient).  The full four-case recursion
    (esp. the `gen` monad-2-generator reseat = converse of `interpretWordFrom_map`, + the whisker junction casts) and
    the BACKWARD round-trip are cast-heavy LABOR scoped to r12 — the named node.

  * **B4-`mergeFrameIntoHead/Tail` — UNTOUCHED (r12+).**  The pure-`t` whisker cell surgery (node ii): NOT addressed
    this round; the WIDTH-level merge (`finestGapWidthsAux_append`) shipped r10, the CELL surgery remains open.

  * **Finding-A (the vcomp COMMON-REFINEMENT zip) — UNBLOCKED, not done.**  It was "authorable only once
    `finestLayout` exists"; `finestLayout` now exists (r11 B3), so its alignment arc is authorable — but it is a
    separate arc, not done this round.

  * **Finding-C (the multi-gap NORMAL-FORM splice) — STILL CROSS-LANE BLOCKED.**  Rides
    `WalkingMonad.wordMul_vcomp` (CONSUME-only, the `WalkingMonad/` READ-ONLY lane); untouched, still walled outside
    this lane's authority.

## HELD — the three masters do NOT flip (the honest r11 verdict)

`pathInvert` and `finestLayout` are node-i / node-ii INGREDIENTS (a 1-cell converse and a domain-recovering pairs
producer), NOT the ARBITRARY-CELL coverage the masters' demands require.  That coverage stays blocked on
`wallFreeCellInvert`'s full recursion (r12), the Finding-A vcomp zip (its own arc), and the Finding-C cross-lane
splice.  So, per their VERBATIM demands:

  * `fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS `false`.
  * `fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`.
  * `fxAmalg_topFactorizationInductionStaysWalled` (`PushoutVcompInterchangeSplice.lean`) STAYS `true`.

**#2043 does NOT close.**  This file adds markers ONLY; it touches no shipped marker.  No fabricated flip.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The shipped r11 ingredients, machine-witnessed -/

-- THE KEYSTONE — the endo-`ModalityPath`-at-single-mode transport (word ⟷ endo path bijection).
#check @fxAmalg_hasEndoModeTransport
#check @pushoutEndoPathOfWord
#check @pushoutPathWord_injective
-- B1-`pathInvert` CLOSED — the wall-free 1-cell converse, both round-trips.
#check @mapPath_inclRight_pathInvert
#check @pathInvert_mapPath_inclRight
-- B2-`finestLayout` CLOSED — the cell-carrying pairs, domain round-trip.
#check @gapDomLayout_finestLayout
-- B3-`wallFreeCellInvert` PREREQUISITES — the wall-free/wall-count bridge + dom-to-cod stability.
#check @wallFreeMiddleOfCell
-- The three masters STAY put (referenced, not touched).
#check @fxAmalg_hasFullSaturatedPushoutDispatch
#check @fxAmalg_hasGeneralPushoutDispatch
#check @fxAmalg_topFactorizationInductionStaysWalled

/-! ## Honesty markers — the r11 ledger -/

/-- ★★★ **Honesty marker — the endo-mode-transport KEYSTONE unlocks the two nearest r10 nodes; #2043 stays OPEN.**
`= true` (the honest r11 verdict).  The r10 ledger named `pathInvert` (B1) and `finestLayout` (B2) "both blocked ONLY
on the single-mode intermediate-mode transport."  r11 authored that keystone (`PushoutEndoModeTransport.lean`: the
singleton `pushoutModeUnique` ⟹ endo generators `pushoutGenEndpoints` ⟹ the transport `pushoutEndoPathOfWord`, a
bijection with `pushoutPathWord` via the reflection `pushoutPathWord_injective`) and unlocked exactly those two:
`pathInvert` (the wall-free 1-cell converse + BOTH round-trips, a genuine bijection) and `finestLayout` (the
cell-carrying pairs + the domain round-trip `gapDomLayout nil ∘ finestLayout = id`).  This did NOT ship the top-level
`pushoutFactorize` and FLIPPED NO master: `fxAmalg_hasFullSaturatedPushoutDispatch` STAYS `false`,
`fxAmalg_hasGeneralPushoutDispatch` STAYS `false`, `fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.
#2043 does NOT close — no fabricated flip.  `= true`. -/
def fxAmalg_r11KeystoneUnlocksTwoNearestNodes : Bool := true

/-- ★★ **Honesty marker — the r10 open-node accounting, updated per TRUTH.**  `= true` (the wall honestly held,
each node precisely named).  B1-`pathInvert`: CLOSED (converse + both round-trips).  B2-`finestLayout`: CLOSED (pairs
producer + domain round-trip).  B3-`wallFreeCellInvert`: PARTIAL — its clean structural prerequisites ship (the
`pathWallFree ↔ wallCount = 0` bridge + `wallFreeMiddleOfCell`), the full four-case recursion (the `gen`
monad-2-generator reseat = converse of `interpretWordFrom_map`, + whisker junction casts) + its backward round-trip
scoped to r12.  B4-`mergeFrameIntoHead/Tail`: UNTOUCHED (the node-ii pure-`t` cell surgery, r12+).  Finding-A (the
vcomp COMMON-REFINEMENT zip): UNBLOCKED now that `finestLayout` exists, but a separate arc, not done.  Finding-C (the
multi-gap NORMAL-FORM splice): STILL CROSS-LANE BLOCKED on `WalkingMonad.wordMul_vcomp` (READ-ONLY).  Every jam is an
exact goal with a named node.  `= true`. -/
def fxAmalg_r11NodeAccounting : Bool := true

/-- ★ **Honesty marker — r11 adds markers ONLY; the three masters and the arbitrary-cell decision stay put.**
`= true`.  `pathInvert` / `finestLayout` are node-i / node-ii INGREDIENTS (a 1-cell converse; a domain-recovering
pairs producer), NOT the ARBITRARY-CELL coverage the masters' demands require — that coverage stays blocked on
`wallFreeCellInvert`'s full recursion (r12), the Finding-A vcomp zip, and the Finding-C cross-lane splice.  The three
walled markers (`fxAmalg_hasFullSaturatedPushoutDispatch`, `fxAmalg_hasGeneralPushoutDispatch`,
`fxAmalg_topFactorizationInductionStaysWalled`) are UNTOUCHED at `false` / `false` / `true`; r11 ships five additive
source files (transport, path inversion, finest pairs, cell-converse prerequisites, this ledger) plus their audit
twins and its own AuditAll lines, and nothing in the `WalkingMonad/` READ-ONLY lane was edited.  No fabricated flip.
`= true`. -/
def fxAmalg_r11MastersHold : Bool := true

end FX1Poly.Polygraph.Amalgam
