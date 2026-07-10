import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreePathInjectivity
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestGapMerge
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutMidPathSeamLedger

/-! # Polygraph/TwoCategory/Amalgam/PushoutWallFreeInversionLedger — the r10 LEDGER: the wall-free INVERSION base +
the whisker-frame width MERGE ship, the residual factorizes to finer nodes, and NOTHING flips (WP-AMALG-2 r10, B4/B5)

r9 (`PushoutMidPathSeamLedger.lean`) bypassed the r8 wall-block jam and sharpened the residual to the
reconstruction-inversion (node i) + the whisker-frame `t`-run merge (node ii).  r10 is the total-factorize round: it
TRUTH-PROBES those two nodes FIRST and ships their clean, self-contained BASES, then factorizes the still-open
residual into precisely-named finer nodes.  It flips NOTHING.

## What r10 shipped (each machine-checked, zero-axiom, independently `#print axioms`-clean)

  * **`PushoutWallFreeInversion.lean`** (B1, LETTER level) — the converse `retractRightLetter` of the right
    coprojection `embedRightLetter` on the wall-free (component-2) letters, both round-trips
    (`retractRightLetter_embedRightLetter`, `embedRightLetter_retractRightLetter`), letter-level injectivity
    (`embedRightLetter_injective`, via the propext-free subtraction round-trip `addSubCancelLeft`), the `Nat.blt`-false
    bridge (`geOfBltFalse`), and the concrete gap-letter TRUTH-PROBE (`tLetter_retract`: the gap letter `t` retracts
    to the monad's `t`-index by `decide`; `tLetter_wallFree` / `sLetter_notWallFree` pin the invertible boundary at
    the `letterTag` bit).  This is node (i)'s LETTER base — a wall-free pushout letter reconstructs its monad
    pre-image.

  * **`PushoutWallFreePathInjectivity.lean`** (B1, PATH level) — the induced 1-cell functor
    `mapPath (inclusionRight …)` is INJECTIVE on monad 1-cells (`mapPath_inclRight_injective`), via WORD reflection
    (`monadPathWord`, `mapPath_inclRight_word`, `mapEmbedRight_injective`, `monadPathWord_injective`) that dodges the
    childCons injection-drilling landmine on the function-application-indexed mapped `cons`.  This is the
    shared-middle reconciliation node (i)'s vcomp case needs: the two middle pre-images of a `vcomp` coincide because
    the right coprojection's 1-cell functor is FAITHFUL.

  * **`PushoutFinestGapMerge.lean`** (B2, WIDTH level) — the whisker-frame gap-MERGE law
    (`finestGapWidthsAux_append`: `finestGapWidths (frame ++ body)` folds the frame's TRAILING gap into the body,
    `foldBodyAtTail`, the `last(frame) + first(body)` merge), the accumulator-shift primitive
    (`finestGapWidthsAux_bumpHead`) + nonemptiness (`finestGapWidthsAux_nonempty`), the pure-`t` frame contribution
    (`finestGapWidths_tRunFrame`), and the r8 SELF-ATTACK machine-checked: `finestGapWidths_naiveConcatRefuted`
    proves the NAIVE concatenation `finestGapWidths frame ++ finestGapWidths body` is WRONG (`[1,1,0] ≠ [2,0]`),
    refuting the whisker-case "prepend frame slots" design BEFORE the cell surgery is attempted.

## The residual factorizes to these PRECISELY-NAMED open nodes (the total-factorize accounting)

  * **B1-`pathInvert`** — the wall-free 1-cell CONVERSE (a pushout wall-free path reconstructs a MONAD path, with
    `mapPath inclRight ∘ pathInvert = id`).  Injectivity (the faithfulness half) SHIPPED; `pathInvert` (the
    essential-surjectivity half) is walled by the SINGLE-MODE intermediate-mode transport: a per-letter reconstruction
    needs each intermediate mode typed `monadPushMode`, but a `ModalityPath` `cons`'s middle mode is
    provably-but-not-syntactically the single mode.

  * **B2-`finestLayout`** (the cell-carrying pairs, Finding B) — `finestLayout : path → List VcompGapPair` with
    `gapDomLayout finalWall ∘ finestLayout = id`.  The WIDTH shape (`finestGapWidths`) SHIPPED (r9) and its merge
    law (r10); the PAIRS producer is walled by the SAME single-mode transport (a per-letter block's `wall` / `gapDom`
    must be an endo path `monadPushMode → monadPushMode`, but path letters carry provably-but-not-syntactically-single
    intermediate modes).

  * **B3-`wallFreeCellInvert`** (node i, CELL level) — the essential-surjectivity converse feeding
    `pushoutRightImageConvReflect`: a wall-free-boundary pushout cell EXTRACTS a monad pre-image cell.  Its `id` /
    `vcomp` cases stand on `pathInvert` + `mapPath_inclRight_injective` (the shared-middle reconciliation, half now
    shipped); its `gen` case rides one `Option.some.inj` + a `castBoundary`; its whisker cases ride
    `mapPath_composePath`.

  * **B4-`mergeFrameIntoHead/Tail`** (node ii, CELL level) — the pure-`t` whisker cell surgery: fuse an `id (t-run)`
    frame into the body's head / tail `VcompGapPair` (widening `gapDom` and re-`hcomp`-ing the payload across a
    `composePath` junction cast), matched to the WIDTH merge shipped here.  Authorable only for PURE-`t` frames;
    `s`-bearing frames SPLIT the whisker (the wire-changing residual).

  * **Finding-A** — the vcomp-case COMMON-REFINEMENT zip (`vcomp (gapVcompLayout p) (gapVcompLayout q) ≈
    gapVcompLayout (align p q)`): the re-surfaced r8 jam, authorable only once `finestLayout` exists (its own arc).

  * **Finding-C** — the multi-gap NORMAL-FORM splice (canonical-layout uniqueness, the master demand's
    COMPLETENESS residual iii) rides `WalkingMonad/MonadWordVcomp.wordMul_vcomp` — CONSUME-only, owned by the
    WalkingMonad lane (READ-ONLY here); needs a signature-transported reseat onto `monadComputad.toModeSignature`
    that this lane MAY NOT author.  Cross-lane blocked.

## HELD — no flip (the honest r10 verdict)

`fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS `false` — the shipped bases are node (i)'s
letter/path faithfulness and node (ii)'s width arithmetic, NOT the arbitrary-cell coverage its demand's residual
(iii) requires; `fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`;
`fxAmalg_topFactorizationInductionStaysWalled` (`PushoutVcompInterchangeSplice.lean`) STAYS `true`.  **#2043 does NOT
close.**  This file adds markers ONLY; it touches no shipped marker.  No fabricated flip.

## What WP-AMALG-3 inherits (scope note)

The five named nodes above, in dependency order: `pathInvert` + `finestLayout` (both blocked ONLY on the single-mode
intermediate-mode transport — the next clean lemma to author is `ModalityPath`-endo-at-single-mode transport, then
both unlock) → `wallFreeCellInvert` (B3, standing on the shipped injectivity + `pathInvert`) → `mergeFrameIntoHead/Tail`
(B4, standing on the shipped width merge) → Finding-A zip (its own `finestLayout`-alignment arc) → Finding-C
(cross-lane, gated on a WalkingMonad `wordMul_vcomp` reseat outside this lane's authority).  Every node lives INSIDE
the disjoint `involution +_M monad` scope except Finding-C.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The shipped r10 bases, machine-witnessed -/

-- B1 LETTER — the wall-free letter converse and its concrete truth-probe.
#check @retractRightLetter
#check @retractRightLetter_embedRightLetter
#check @embedRightLetter_injective
#check @tLetter_retract
-- B1 PATH — the right coprojection's 1-cell functor is faithful (the vcomp shared-middle reconciliation).
#check @mapPath_inclRight_injective
-- B2 WIDTH — the whisker-frame gap merge and the naive-concat refutation.
#check @finestGapWidthsAux_append
#check @finestGapWidths_naiveConcatRefuted
-- The master demand STAYS false (referenced, not touched).
#check @fxAmalg_hasFullSaturatedPushoutDispatch

/-! ## Honesty markers — the r10 ledger -/

/-- ★★★ **Honesty marker — r10 ships node (i)'s letter/path INVERSION base + node (ii)'s width MERGE, and FLIPS
NOTHING; #2043 stays OPEN.**  `= true` (the honest r10 verdict).  Node (i) LETTER: `retractRightLetter` (the converse
of `embedRightLetter`) with both round-trips, `embedRightLetter_injective`, and the concrete `tLetter_retract`
truth-probe.  Node (i) PATH: `mapPath_inclRight_injective` (the right coprojection's 1-cell functor is faithful — the
vcomp shared-middle reconciliation — via word reflection dodging the childCons drilling landmine).  Node (ii) WIDTH:
`finestGapWidthsAux_append` (the `last(frame) + first(body)` gap merge) with the r8 self-attack
`finestGapWidths_naiveConcatRefuted` (naive concat `[1,1,0] ≠ [2,0]`).  This did NOT ship the top-level
`pushoutFactorize`, and FLIPPED NO marker: `fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS
`false`, `fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`,
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  #2043 does NOT close — no fabricated flip.  `= true`. -/
def fxAmalg_r10ShipsWallFreeInversionAndGapMerge : Bool := true

/-- ★★ **Honesty marker — the residual factorizes to FIVE precisely-named nodes, the two nearest blocked ONLY on
single-mode transport.**  `= true` (the wall honestly held, precisely named).  The total-factorize accounting:
(B1) `pathInvert` — the wall-free 1-cell CONVERSE (injectivity shipped, converse walled on single-mode
intermediate-mode transport); (B2) `finestLayout` — the cell-carrying pairs (width shape + merge shipped, pairs
producer walled on the SAME transport); (B3) `wallFreeCellInvert` — node (i)'s cell-level converse (stands on
`pathInvert` + the shipped injectivity); (B4) `mergeFrameIntoHead/Tail` — node (ii)'s pure-`t` cell surgery (stands on
the shipped width merge); Finding-A — the vcomp COMMON-REFINEMENT zip (re-surfaced r8 jam, its own `finestLayout`
arc); Finding-C — the multi-gap NORMAL-FORM splice, CROSS-LANE blocked (rides `WalkingMonad.wordMul_vcomp`,
CONSUME-only).  The single next clean lemma that unlocks the two nearest nodes is the endo-`ModalityPath`-at-single-mode
transport.  Named node.  `= true`. -/
def fxAmalg_r10NamedOpenNodes : Bool := true

/-- ★ **Honesty marker — r10 adds markers ONLY; every shipped marker and the arbitrary-cell decision stay put.**
`= true`.  The three walled markers (`fxAmalg_hasFullSaturatedPushoutDispatch`, `fxAmalg_hasGeneralPushoutDispatch`,
`fxAmalg_topFactorizationInductionStaysWalled`) are UNTOUCHED at `false` / `false` / `true`; r10 ships four additive
files (three source + this ledger) plus their audit twins and its own AuditAll lines, and nothing in the
`WalkingMonad/` READ-ONLY lane was edited.  No fabricated flip.  `= true`. -/
def fxAmalg_r10NoFlipHeld : Bool := true

end FX1Poly.Polygraph.Amalgam
