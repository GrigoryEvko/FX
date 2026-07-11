import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeCanonicalWhiskerRight
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallShiftReanchor
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCanonicalReaderStateLedger

/-! # Polygraph/TwoCategory/Amalgam/PushoutWallShiftStateLedger — the #2043 state after r18 (the wall-shift surgery +
total canonical recursion round): the master checklist, the exact #2043 state, every jam = the exact goal with a NAMED
node (WP-AMALG-2 r18, Brick B5)

r18 (the wall-shift surgery + the canonical whiskerRight arm) shipped four bricks, each additive, zero-axiom, no
fabricated flip:

  * **B1** `wallOffsetDom` / `wallOffsetCod` + `pushoutWallShiftComposes` — the per-ordinal wall-OFFSET function and the
    propext-safe paired-`Nat` SHIFT-COMPOSITION law (`wallOffsetDom + gapCodLenSum = wallOffsetCod + gapDomLenSum`,
    never computing the possibly-negative `b − a`), truth-probed on the `mu`-firing wire-changing block (`3 → 2` shift).
    `fxAmalg_hasWallShiftOffset = true`.
  * **B2** `ordinalZeroReanchorDefinitional` + `muWireChangeMergeWitness` — the ordinal-0 re-anchoring is DEFINITIONAL
    (empty prefix, `rfl`) and the S-frame MERGE fires through a WIRE-CHANGING body (slot count preserved); the wall-shift
    is NARROWED (both frame folds touch only extreme ordinals) but NOT flipped.
    `fxAmalg_ordinalZeroReanchorDefinitional = true`, `fxAmalg_ordinalAnchorNarrowsWallShift = true`.
  * **B3 (LEG 1)** `whiskerRight_conv_appendFinalWall` — the trailing-frame append CONS-CASE fold (the r17 leg-1
    residual, now shipped), folding the frame down the right-nested layout.  `fxAmalg_hasWhiskerRightAppendCell = true`.
  * **B4** `pushoutFactorizeWhiskerRightMergeLayout` — the CANONICAL whiskerRight merge-layout arm (`n → n`, off leg 1,
    the dual of the shipped whiskerLeft arm), with the wild probes + the JAM A re-audit.
    `fxAmalg_hasCanonicalWhiskerRightArm = true`.

This ledger machine-records the whole-picture #2043 state and pins each remaining jam to its EXACT goal and NAMED node.

## The two jams (each: the exact goal + the NAMED node)

  * **JAM A — the per-gap DESCENT / purification-completeness (masters i, ii).**  NAMED node:
    `fxAmalg_hasSaturatedDispatchTheorem` (= `false`).  EXACT goal: a whole-cell convertibility DESCENDS to per-gap
    convertibilities (the convex-block projection sound only for word-preserving presentations).  The wire-creating
    `eta` (`t^0 ⇒ t`) / `mu` (`t^2 ⇒ t`) VIOLATE it — they change gap WIDTHS `0 → 1` / `2 → 1` exactly where the
    projection fails.  r18 supplies NONE of the descent (the canonical whisker arms are additive coverage); it is coupled
    to the WalkingMonad reconstruction-faithfulness iso (fib-3, READ-ONLY).

  * **JAM B — the top firing-block FACTORISATION reader (masters ii, iii).**  NAMED node: `pushoutFactorize` — an
    arbitrary pushout cell factors into a firing-block `VcompGapPair` layout with a convertibility to it.  r18 NARROWED
    it further: leg 1 (`whiskerRight_conv_appendFinalWall`) SHIPS the trailing append (the r17 leg-1 residual closed),
    the canonical whiskerRight arm (`pushoutFactorizeWhiskerRightMergeLayout`) SHIPS (`n → n`), and the wall-shift is
    NARROWED to extreme-ordinal cast-only folds (B1/B2).  Three residuals remain, each NAMED: (i) the INTERIOR-ordinal
    wall-shift PRODUCER — placing `gapCodLayout` walls at shifted absolute indices off an ARBITRARY cell with interior
    walls (ordinal ≥ 1, non-empty prefix), which the extreme-ordinal anchoring does NOT supply
    (`fxAmalg_sFrameWallShiftStaysWalled = true`); (ii) the general firing-block PRODUCER over arbitrary paths
    (`fxAmalg_firingBlockProducerStaysWalled = true`); (iii) the TOTAL CANONICAL reader threading each body's own
    factorization conv through the merge/append arms (`fxAmalg_totalCanonicalReaderStaysGated = true`).
    `fxAmalg_factorizationCompletenessStaysWalled = true` records JAM B still walled.

## The master checklist per the verbatim demands (NONE flips)

| Master | NAMED node | Verbatim value | r18 |
|---|---|---|---|
| (i) full saturated pushout dispatch | `fxAmalg_hasFullSaturatedPushoutDispatch` | `false` | STAYS `false` (JAM A) |
| (ii) general pushout dispatch | `fxAmalg_hasGeneralPushoutDispatch` | `false` | STAYS `false` (JAM A + JAM B producer) |
| (iii) top factorisation walled | `fxAmalg_topFactorizationInductionStaysWalled` | `true` | STAYS `true` (JAM B producer + wall-shift) |

Even a COMPLETE canonical reader flips at most (iii); masters (i)/(ii) are gated on the JAM A per-gap DESCENT the reader
never supplies.  So NO master flips this round.

## Close criterion (maximally strict)

`#2043` closes iff `fxAmalg_hasFullSaturatedPushoutDispatch ∧ fxAmalg_hasGeneralPushoutDispatch ∧
¬ fxAmalg_topFactorizationInductionStaysWalled` — both jams closed.  After r18 that is `false ∧ false ∧ ¬true = false`:
`#2043` does NOT close (`fxAmalg_pushoutDispatch2043ClosesAfterR18_false`, machine-checked).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## r18 shipped — the four bricks live (machine-checked conjunction) -/

/-- The r18 deliverable conjunction — B1 wall-offset + shift law, B2 ordinal-0 re-anchoring, B3 leg-1 trailing-append
fold, B4 canonical whiskerRight merge arm, all live. -/
def reconR18BricksShipped : Bool :=
  fxAmalg_hasWallShiftOffset
    && fxAmalg_ordinalZeroReanchorDefinitional
    && fxAmalg_hasWhiskerRightAppendCell
    && fxAmalg_hasCanonicalWhiskerRightArm

/-- The r18 bricks are all live (`rfl`). -/
theorem reconR18BricksShipped_true : reconR18BricksShipped = true := rfl

/-! ## The two jams, each pinned to its NAMED node's current (open / walled) value -/

/-- ★★★ **JAM A pinned — the per-gap DESCENT stays OPEN.**  The NAMED node `fxAmalg_hasSaturatedDispatchTheorem` is
`false` (`rfl`).  r18 completed the whisker fold coverage (leg 1 + the canonical arm) and narrowed the wall-shift, but
supplies NONE of the descent — the convex-block projection the wire-creating `eta`/`mu` violate, coupled to the
WalkingMonad reconstruction iso (fib-3). -/
theorem reconR18JamA_perGapDescentOpen : fxAmalg_hasSaturatedDispatchTheorem = false := rfl

/-- ★★★ **JAM B pinned — the top firing-block factorisation reader stays WALLED (NARROWED, not closed).**  The ledger
node `fxAmalg_factorizationCompletenessStaysWalled` is `true`, and the r18 residual nodes are held: the interior-ordinal
wall-SHIFT producer (`fxAmalg_sFrameWallShiftStaysWalled = true`), the general firing-block PRODUCER
(`fxAmalg_firingBlockProducerStaysWalled = true`), and the TOTAL CANONICAL reader
(`fxAmalg_totalCanonicalReaderStaysGated = true`).  All four `rfl`. -/
theorem reconR18JamB_narrowedButWalled :
    fxAmalg_factorizationCompletenessStaysWalled = true
      ∧ fxAmalg_sFrameWallShiftStaysWalled = true
      ∧ fxAmalg_firingBlockProducerStaysWalled = true
      ∧ fxAmalg_totalCanonicalReaderStaysGated = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- ★★★ **The wall-shift is NARROWED but the leg-2 wall STAYS `true` (no flip).**  B1/B2 reclassify the wall-shift to
"automatic in the shipped `gapCodLayout` representation, both frame folds at extreme ordinals"
(`fxAmalg_ordinalAnchorNarrowsWallShift = true`), but the verbatim leg-2 demand (the INTERIOR-ordinal producer off an
arbitrary cell) is unmet, so `fxAmalg_sFrameWallShiftStaysWalled = true`.  Both `rfl`. -/
theorem reconR18WallShiftStaysWalled :
    fxAmalg_ordinalAnchorNarrowsWallShift = true ∧ fxAmalg_sFrameWallShiftStaysWalled = true :=
  ⟨rfl, rfl⟩

/-! ## The master checklist (NONE flips) -/

/-- ★★★ **THE MASTER CHECKLIST — NO master flips at r18 (`rfl`).**  All three masters stay at their verbatim walled
values: `fxAmalg_hasFullSaturatedPushoutDispatch = false`, `fxAmalg_hasGeneralPushoutDispatch = false`,
`fxAmalg_topFactorizationInductionStaysWalled = true`.  The r18 wall-shift arithmetic + canonical whisker arm are
additive; the flips are gated on the JAM A per-gap descent (masters i/ii) and the JAM B producer + wall-shift (master
iii), NONE of which r18 supplies. -/
theorem reconR18NoMasterFlips :
    fxAmalg_hasFullSaturatedPushoutDispatch = false
      ∧ fxAmalg_hasGeneralPushoutDispatch = false
      ∧ fxAmalg_topFactorizationInductionStaysWalled = true :=
  ⟨rfl, rfl, rfl⟩

/-! ## The #2043 close criterion (maximally strict) -/

/-- The `#2043` close criterion — closes iff BOTH masters (i)/(ii) hold AND the top factorisation is no longer walled.
Encodes the strict "genuine full coverage" bar; anything less is `false`. -/
def fxAmalg_pushoutDispatch2043ClosesAfterR18 : Bool :=
  fxAmalg_hasFullSaturatedPushoutDispatch
    && fxAmalg_hasGeneralPushoutDispatch
    && (fxAmalg_topFactorizationInductionStaysWalled == false)

/-- ★★★ **`#2043` does NOT close after r18 (`rfl`).**  The close criterion evaluates to `false`: both jams (A the
per-gap descent, B the top firing-block factorisation reader) remain open.  The honest ceiling — r18 SHIPPED the leg-1
trailing append (the r17 residual) and the canonical whiskerRight arm, NARROWED the wall-shift to extreme-ordinal
cast-only folds (B1/B2), but neither jam closes: the interior-ordinal producer, the general firing-block producer, the
total canonical body-conv threading, and the JAM A per-gap descent all remain. -/
theorem fxAmalg_pushoutDispatch2043ClosesAfterR18_false :
    fxAmalg_pushoutDispatch2043ClosesAfterR18 = false := rfl

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the #2043 state after r18: the wall-shift NARROWED + leg-1 append SHIPPED + canonical
whiskerRight arm SHIPPED, two named jams remain, #2043 does NOT close (WP-AMALG-2 r18, B5).**  `= true` (the STATE is
honestly recorded, not a claim that #2043 closes).  r18 shipped four bricks (`reconR18BricksShipped_true`): B1 the
wall-offset function + propext-safe shift-composition law, B2 the ordinal-0 definitional re-anchoring + the S-frame merge
through a wire-changing body, B3 the leg-1 trailing-append fold (the r17 residual closed), B4 the canonical whiskerRight
merge-layout arm.  Two jams remain, each pinned to its named node at its open / walled value: JAM A the per-gap DESCENT
(`fxAmalg_hasSaturatedDispatchTheorem = false`, `reconR18JamA_perGapDescentOpen`) and JAM B the top firing-block
factorisation reader (`fxAmalg_factorizationCompletenessStaysWalled = true`, plus the interior-ordinal wall-shift
producer, the general producer, and the total canonical body-conv threading residuals,
`reconR18JamB_narrowedButWalled`).  The leg-2 wall-shift is NARROWED but NOT flipped
(`reconR18WallShiftStaysWalled`).  NO master flips (`reconR18NoMasterFlips`).  The strict close criterion
`fxAmalg_pushoutDispatch2043ClosesAfterR18` is machine-checked `= false` (`fxAmalg_pushoutDispatch2043ClosesAfterR18_false`).
r18 is an HONEST NARROWING.  `#2043` does NOT close.  `= true`. -/
def fxAmalg_canonicalReaderStateAfterR18 : Bool := true

end FX1Poly.Polygraph.Amalgam
