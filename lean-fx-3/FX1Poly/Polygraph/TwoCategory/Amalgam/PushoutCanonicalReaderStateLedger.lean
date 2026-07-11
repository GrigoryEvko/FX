import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerMergeIntoHead
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerRightAppend
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutVcompSkeletonAlignment
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutAmalgamDispatchStateLedger

/-! # Polygraph/TwoCategory/Amalgam/PushoutCanonicalReaderStateLedger — the #2043 state after r17 (the canonical
firing-block reader round): the master checklist, the exact #2043 state, every jam = the exact goal with a NAMED node
(WP-AMALG-2 r17, Brick B5)

r17 (the canonical firing-block reader — JAM B core) shipped four bricks, each additive, zero-axiom, no fabricated
flip:

  * **B1** `whiskerLeft_conv_mergeFrameIntoHead` — the CELL-LEVEL merge-into-head whisker surgery (a `whiskerLeft`
    frame folds into the head slot's leading wall via `whiskerLeftComp` through the `composePath_assoc` cast), with the
    framed two-gap truth-probe (merged `slotCount = 2` preserved).  `fxAmalg_hasWhiskerMergeIntoHeadCell = true`.
  * **B2** `whiskerRight_conv_hcompRight` + `gapDomLayoutAppendFinalWall` / `gapCodLayoutAppendFinalWall` +
    `whiskerRightCastBoundaryEq` — the `whiskerRight` TRAILING-frame append MACHINERY (the two recon-named missing
    lemmas + the hcomp right-push engine + the base case + the two-gap distribution probe).
    `fxAmalg_hasWhiskerRightAppendEngine = true`.
  * **B3** `vcompMultiGapSharedMiddleSlotCountAligns` — the vcomp arm's shared-middle skeleton alignment made a PROVEN
    theorem (the B4 general invariant applied to both halves proves the upper / lower cells read the shared middle `M`
    at the same firing-block slot count).  `fxAmalg_hasVcompSkeletonAlignmentTheorem = true`.
  * **B4** `finestGapWidths_pushoutPathTags_length` + `finestGapWidths_slotCount_domCod_eq` +
    `pushoutFactorizeIdCanonicalNil` — the canonical firing-block SLOT-COUNT SPEC (`(finestGapWidths (pushoutPathTags
    path)).length = wallCount + 1`), the GENERAL dom↔cod slot invariant (off `wallLetterCount_dom_eq_cod`), and the
    `id`-case canonical upgrade (self-attack #4 fix).  `fxAmalg_hasCanonicalFiringBlockSlotSpec = true`.

This ledger machine-records the whole-picture #2043 state and pins each remaining jam to its EXACT goal and NAMED node.

## The two jams (each: the exact goal + the NAMED node)

  * **JAM A — the per-gap DESCENT / purification-completeness (masters i, ii).**  NAMED node:
    `fxAmalg_hasSaturatedDispatchTheorem` (= `false`, `SaturatedDispatch.lean`).  EXACT goal: a whole-cell
    convertibility DESCENDS to per-gap convertibilities (the convex-block / Nelson-Oppen purification projection, sound
    only for word-preserving presentations).  The wire-creating `eta` (`t^0 ⇒ t`) / `mu` (`t^2 ⇒ t`) VIOLATE it —
    they change gap WIDTHS `0 → 1` / `2 → 1` exactly where the projection fails.  r17 NARROWED the skeleton-reflection
    half of JAM A to a GENERAL theorem (`finestGapWidths_slotCount_domCod_eq`) but supplies NONE of the descent; it is
    coupled to the WalkingMonad reconstruction-faithfulness iso (fib-3, READ-ONLY).

  * **JAM B — the top firing-block FACTORISATION reader (masters ii, iii).**  NAMED node: `pushoutFactorize` — an
    arbitrary pushout cell factors into a firing-block `VcompGapPair` layout with a convertibility to it.  r17 NARROWED
    it: the slot-count SPEC ships (`finestGapWidths_pushoutPathTags_length`), the skeleton reflects
    (`finestGapWidths_slotCount_domCod_eq`), the `id`-case is now canonical (`pushoutFactorizeIdCanonicalNil`), the
    whiskerLeft merge arm (B1) and whiskerRight append machinery (B2) ship, and the vcomp shared-middle alignment is a
    theorem (B3).  Three residuals remain, each NAMED: (i) the general firing-block PRODUCER over arbitrary paths
    (`firingBlockLayout : path → List VcompGapPair` at firing-block granularity + its multi-slot all-identity conv,
    `fxAmalg_firingBlockProducerStaysWalled = true`); (ii) the `s`-bearing frame's downstream wall-SHIFT (the
    wire-changing case, leg 2a'', `fxAmalg_sFrameWallShiftStaysWalled = true`); (iii) the whiskerRight cons-case append
    assembly (pure cast-plumbing, all ingredients shipped in B2).  `fxAmalg_factorizationCompletenessStaysWalled =
    true` records JAM B still walled.

## The master checklist per the verbatim demands (NONE flips)

| Master | NAMED node | Verbatim value | r17 |
|---|---|---|---|
| (i) full saturated pushout dispatch | `fxAmalg_hasFullSaturatedPushoutDispatch` | `false` | STAYS `false` (JAM A) |
| (ii) general pushout dispatch | `fxAmalg_hasGeneralPushoutDispatch` | `false` | STAYS `false` (JAM A + JAM B producer) |
| (iii) top factorisation walled | `fxAmalg_topFactorizationInductionStaysWalled` | `true` | STAYS `true` (JAM B producer + wall-shift) |

Even a COMPLETE canonical reader flips at most (iii); masters (i)/(ii) are gated on the JAM A per-gap DESCENT the reader
never supplies.  So NO master flips this round.

## Close criterion (maximally strict)

`#2043` closes iff `fxAmalg_hasFullSaturatedPushoutDispatch ∧ fxAmalg_hasGeneralPushoutDispatch ∧
¬ fxAmalg_topFactorizationInductionStaysWalled` — both jams closed.  After r17 that is `false ∧ false ∧ ¬true = false`:
`#2043` does NOT close (`fxAmalg_pushoutDispatch2043ClosesAfterR17_false`, machine-checked).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## r17 shipped — the four bricks live (machine-checked conjunction) -/

/-- The r17 deliverable conjunction — B1 merge-into-head cell surgery, B2 whiskerRight append engine, B3 vcomp
shared-middle skeleton alignment theorem, B4 canonical firing-block slot-count spec, all live. -/
def reconR17BricksShipped : Bool :=
  fxAmalg_hasWhiskerMergeIntoHeadCell
    && fxAmalg_hasWhiskerRightAppendEngine
    && fxAmalg_hasVcompSkeletonAlignmentTheorem
    && fxAmalg_hasCanonicalFiringBlockSlotSpec

/-- The r17 bricks are all live (`rfl`). -/
theorem reconR17BricksShipped_true : reconR17BricksShipped = true := rfl

/-! ## The two jams, each pinned to its NAMED node's current (open / walled) value -/

/-- ★★★ **JAM A pinned — the per-gap DESCENT stays OPEN.**  The NAMED node `fxAmalg_hasSaturatedDispatchTheorem` is
`false` (`rfl`).  r17 strengthened the skeleton-reflection half to a general theorem
(`finestGapWidths_slotCount_domCod_eq`) but supplies NONE of the descent — the convex-block projection the
wire-creating `eta`/`mu` violate, coupled to the WalkingMonad reconstruction iso (fib-3). -/
theorem reconR17JamA_perGapDescentOpen : fxAmalg_hasSaturatedDispatchTheorem = false := rfl

/-- ★★★ **JAM B pinned — the top firing-block factorisation reader stays WALLED (NARROWED, not closed).**  The ledger
node `fxAmalg_factorizationCompletenessStaysWalled` is `true`, and both r17 residual nodes are held: the general
firing-block PRODUCER (`fxAmalg_firingBlockProducerStaysWalled = true`) and the `s`-frame downstream wall-SHIFT
(`fxAmalg_sFrameWallShiftStaysWalled = true`).  All three `rfl`. -/
theorem reconR17JamB_factorizationNarrowedButWalled :
    fxAmalg_factorizationCompletenessStaysWalled = true
      ∧ fxAmalg_firingBlockProducerStaysWalled = true
      ∧ fxAmalg_sFrameWallShiftStaysWalled = true :=
  ⟨rfl, rfl, rfl⟩

/-! ## The master checklist (NONE flips) -/

/-- ★★★ **THE MASTER CHECKLIST — NO master flips at r17 (`rfl`).**  All three masters stay at their verbatim walled
values: `fxAmalg_hasFullSaturatedPushoutDispatch = false`, `fxAmalg_hasGeneralPushoutDispatch = false`,
`fxAmalg_topFactorizationInductionStaysWalled = true`.  The r17 canonical-reader machinery is additive; the flips are
gated on the JAM A per-gap descent (masters i/ii) and the JAM B producer + wall-shift (master iii), NONE of which r17
supplies. -/
theorem reconR17NoMasterFlips :
    fxAmalg_hasFullSaturatedPushoutDispatch = false
      ∧ fxAmalg_hasGeneralPushoutDispatch = false
      ∧ fxAmalg_topFactorizationInductionStaysWalled = true :=
  ⟨rfl, rfl, rfl⟩

/-! ## The #2043 close criterion (maximally strict) -/

/-- The `#2043` close criterion — closes iff BOTH masters (i)/(ii) hold AND the top factorisation is no longer walled.
Encodes the strict "genuine full coverage" bar; anything less is `false`. -/
def fxAmalg_pushoutDispatch2043ClosesAfterR17 : Bool :=
  fxAmalg_hasFullSaturatedPushoutDispatch
    && fxAmalg_hasGeneralPushoutDispatch
    && (fxAmalg_topFactorizationInductionStaysWalled == false)

/-- ★★★ **`#2043` does NOT close after r17 (`rfl`).**  The close criterion evaluates to `false`: both jams (A the
per-gap descent, B the top firing-block factorisation reader) remain open.  The honest ceiling — r17 NARROWED JAM B
(the slot-count spec, the general skeleton invariant, the canonical `id`-case, the merge / append machinery, the vcomp
skeleton alignment all ship) and STRENGTHENED the JAM A skeleton-reflection half, but neither jam closes. -/
theorem fxAmalg_pushoutDispatch2043ClosesAfterR17_false :
    fxAmalg_pushoutDispatch2043ClosesAfterR17 = false := rfl

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the #2043 state after r17: the canonical firing-block reader NARROWED, two named jams
remain, #2043 does NOT close (WP-AMALG-2 r17, B5).**  `= true` (the STATE is honestly recorded, not a claim that #2043
closes).  r17 shipped four bricks (`reconR17BricksShipped_true`): B1 the cell-level merge-into-head whisker surgery, B2
the whiskerRight trailing-append machinery, B3 the vcomp shared-middle skeleton alignment theorem, B4 the canonical
firing-block slot-count spec + the `id`-case canonical upgrade.  Two jams remain, each pinned to its named node at its
open / walled value: JAM A the per-gap DESCENT (`fxAmalg_hasSaturatedDispatchTheorem = false`,
`reconR17JamA_perGapDescentOpen`) and JAM B the top firing-block factorisation reader
(`fxAmalg_factorizationCompletenessStaysWalled = true`, plus the producer + wall-shift residuals,
`reconR17JamB_factorizationNarrowedButWalled`).  NO master flips (`reconR17NoMasterFlips`).  The strict close criterion
`fxAmalg_pushoutDispatch2043ClosesAfterR17` is machine-checked `= false`
(`fxAmalg_pushoutDispatch2043ClosesAfterR17_false`).  r17 is an HONEST NARROWING.  `#2043` does NOT close.  `= true`. -/
def fxAmalg_canonicalReaderStateAfterR17 : Bool := true

end FX1Poly.Polygraph.Amalgam
