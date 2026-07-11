import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeMasterAuditLedger
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestPairs
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestGapMerge

/-! # Polygraph/TwoCategory/Amalgam/PushoutAlignmentTruthProbe — the r16 alignment truth-probe VERDICT formalized:
ALIGNABLE at the firing-block SKELETON, with the regression pins on the probe candidates (WP-AMALG-2 r16, Brick B1)

The r16 recon ran the ALIGNMENT TRUTH PROBE: do two genuinely multi-slot firing-block layouts of the SAME pushout
cell always align (common firing-block refinement)?  VERDICT: **ALIGNABLE at the firing-block skeleton** — the
refutation the probe hunted (a same-cell layout pair with NO firing-granularity alignment) DOES NOT EXIST for this
signature, because the wall SKELETON is rigid (wall count conserved dom-to-cod, `wallLetterCount_dom_eq_cod`) and
INERT (no firing touches a wall), so any two layouts of the same cell share that skeleton.  This file PINS the probe
candidates as permanent zero-axiom regressions — the numeric evidence the verdict rests on.

## Why ALIGNABLE, not REFUTABLE (the round-deciding distinction)

The r13 zip walled (`PushoutFinestPayloadZip.lean:157`) because it tried the PER-LETTER `finestLayout` (identity
payloads) as the common refinement — FALSE at atomic granularity (`mu : t·t ⇒ t` spans two letters, cannot be
re-sliced into per-letter identity slots).  The alignment actually needed is at FIRING-BLOCK granularity, where each
firing sits atomically undivided in one inter-wall gap.  Alignment needs only EXISTENCE of the common firing-block
refinement — the rigid wall skeleton — NOT the zip EQUALITY.  That existence is provable from the two shipped facts
(`wallLetterCount_dom_eq_cod` + `emptyGapLayout_conv_id`); it is a genuinely DIFFERENT object than the walled
per-letter zip.  So the probe verdict is ALIGNABLE (not a refutation ship), and this round is the PLUMBING plus this
honest adjudication.

## The probe candidates, pinned (each zero-axiom, `rfl` / structural)

  * **`alignmentSlotInvariantR8DomCod`** — the r8 refuting cell `s·s ⇒ s·t·s` reads the SAME firing-block slot count
    at both boundaries (both `3` = 2 walls + 1): the wire-creating `eta` widens the middle gap `0 → 1` but does NOT
    change the slot skeleton (Probe 1 on the r8 counterexample word).
  * **`alignmentWallHeavySlotCountEq`** — the s-heavy word `s·s·s·s ⇒ s·t·s·t·s·s` reads `5` firing-block slots at
    both boundaries (Probe 1, the deeper wild): four walls in, three walls plus two `t`-gaps out, both `5` slots.
  * **`alignmentFiringBlockRunIsOneSlot`** — GENERAL: a pure-`t` run of ANY length is ONE firing-block slot (its
    inter-wall gap merely WIDENS with the run length, `finestGapWidths_tRunFrame`).  The firing-block granularity that
    carries an atomic firing undivided.
  * **`alignmentPerLetterCountEqWordLength`** — GENERAL: the PER-LETTER `finestLayout` has one slot per letter
    (`finestLayout_length`).  Contrasted with the previous pin, this IS Probe 5 (decisive): a `t`-run of length `k`
    is `k` per-letter slots but `1` firing-block slot — for `k ≥ 2` they DIFFER, exactly the `mu`-atomicity that walls
    the per-letter zip yet is free at firing-block granularity.
  * **`alignmentWallsInertAtMu`** — the `mu` gap's boundaries `t·t ⇒ t` carry ZERO walls at both ends (Probe 6):
    firings act on `t`-content only, never touching a wall.
  * **`alignmentSlotInvariantGeneral`** — the general dom-to-cod wall-count invariant instantiated at `mu`
    (`wallLetterCount_dom_eq_cod`): the rigid-skeleton backbone the ALIGNABLE verdict rests on.

## The honest limit (do not overclaim)

ALIGNABLE is at the firing-block SKELETON level — the skeleton is rigid and provable.  The DESCENT of a whole-cell
convertibility to per-gap convertibilities (needed to USE alignment in a decider) is the purification question
(JAM A) and stays coupled to it; the per-gap comparison, once descended, is the MONAD word problem (WalkingMonad
lane, READ-ONLY, fib-3-coupled).  So the alignment LEMMA is true and r17-authorable, but it is ONE ingredient — it
does not by itself close #2043.  `fxAmalg_hasSaturatedDispatchTheorem` (JAM A) STAYS `false`;
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`; the masters STAY at their walled values.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## Probe 1 — the firing-block slot count is a dom-to-cod invariant (the rigid skeleton) -/

/-- ★★ **PROBE 1 (r8 counterexample word).**  The r8 refuting cell's domain `s·s` (tags `[s, s]`) and codomain
`s·t·s` (tags `[s, t, s]`) read the SAME firing-block slot count — both `3` (= two walls + one).  The wire-creating
`eta` widens the middle gap `0 → 1` but leaves the slot SKELETON fixed: the two layouts of the same cell share the
rigid wall skeleton.  This is the core evidence the ALIGNABLE verdict rests on, on the exact word that r8 used to
refute the wall-BLOCK strategy. -/
theorem alignmentSlotInvariantR8DomCod :
    (finestGapWidths [true, true]).length = (finestGapWidths [true, false, true]).length := rfl

/-- ★★ **PROBE 1 (the deeper wild — the s-heavy word).**  The word `s·s·s·s ⇒ s·t·s·t·s·s` reads the SAME
firing-block slot count at both boundaries — both `5`.  Four adjacent walls collapse the interior to empty gaps in
the domain (`[0,0,0,0,0]`); the codomain interleaves two `t`-gaps between the walls (`[0,1,1,0,0]`) — the slot COUNT
is unchanged, only two gap WIDTHS grow.  A genuinely multi-slot, multi-wall witness of the rigid skeleton. -/
theorem alignmentWallHeavySlotCountEq :
    (finestGapWidths [true, true, true, true]).length
      = (finestGapWidths [true, false, true, false, true, true]).length := rfl

/-- ★ **The general dom-to-cod wall-count invariant at `mu`.**  `wallLetterCount_dom_eq_cod` instantiated on the
`mu` generator gives `pushoutPathWallCount (t·t) = pushoutPathWallCount t` — the machine-anchored backbone: the wall
count (hence the firing-block slot count `= wallCount + 1`) is a genuine dom-to-cod invariant for ARBITRARY cells. -/
theorem alignmentSlotInvariantGeneral :
    pushoutPathWallCount (composePath monadPushTPath monadPushTPath) = pushoutPathWallCount monadPushTPath :=
  pushoutMultBoundaryWallCountEq

/-! ## Probe 5 — per-letter vs firing-block granularity (the decisive numeric) -/

/-- ★★ **PROBE 5 (firing-block half) — a pure-`t` run is ONE firing-block slot, ANY length.**  A `t`-run of length
`runLength` reads a single firing-block gap whose width is the run length (`finestGapWidths_tRunFrame`): the run does
NOT open new slots, it widens the running gap.  This is the granularity at which an atomic firing (`mu : t·t ⇒ t`
spanning two letters) sits undivided — the object the r13 per-letter zip lacked. -/
theorem alignmentFiringBlockRunIsOneSlot (runLength : Nat) :
    (finestGapWidths (List.replicate runLength false)).length = 1 := by
  show (finestGapWidthsAux 0 (List.replicate runLength false)).length = 1
  rw [finestGapWidths_tRunFrame runLength 0]
  rfl

/-- ★★ **PROBE 5 (per-letter half, decisive) — the finest per-letter layout has one slot per LETTER.**
`finestLayout_length`: `(finestLayout path).length = path.length`.  Contrasted with `alignmentFiringBlockRunIsOneSlot`
this IS the decisive Probe 5: a `t`-run of length `k` is `k` per-letter slots but `1` firing-block slot — for
`k ≥ 2` they DIFFER.  That difference is exactly the `mu`-atomicity: the only cut finer than `mu`'s single
firing-block slot carries identity payloads, not `mu`, so the per-letter zip is FALSE while the firing-block
alignment holds. -/
theorem alignmentPerLetterCountEqWordLength
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) :
    (finestLayout path).length = path.length :=
  finestLayout_length path

/-! ## Probe 6 — the walls are inert (no firing touches a wall) -/

/-- ★★ **PROBE 6 — the `mu` firing touches ZERO walls.**  The `mu` gap's boundaries `t·t ⇒ t` carry ZERO walls at
both ends (`pushoutMultSlotWallFree`): every firing acts on `t`-content strictly BETWEEN consecutive walls, never
crossing or reordering a wall.  Combined with the rigid-skeleton invariant, this is why two layouts of the same cell
cannot MISALIGN — the firing-block gaps are determined by the (inert, conserved) wall skeleton. -/
theorem alignmentWallsInertAtMu :
    pushoutPathWallCount (composePath monadPushTPath monadPushTPath) = 0
      ∧ pushoutPathWallCount monadPushTPath = 0 :=
  pushoutMultSlotWallFree

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the alignment truth-probe VERDICT is ALIGNABLE at the firing-block SKELETON (WP-AMALG-2
r16, B1).**  `= true`.  The probe hunted a same-cell layout pair with NO firing-granularity alignment; it DOES NOT
exist for this signature.  The evidence, pinned zero-axiom: the firing-block slot count is a dom-to-cod invariant
(`alignmentSlotInvariantR8DomCod` on the r8 word, both `3`; `alignmentWallHeavySlotCountEq` on the s-heavy word, both
`5`; `alignmentSlotInvariantGeneral` = `wallLetterCount_dom_eq_cod` at `mu`), the walls are inert
(`alignmentWallsInertAtMu`, `mu` touches zero walls), and the granularity gap that walled the r13 zip is exactly the
per-letter-vs-firing-block difference (`alignmentFiringBlockRunIsOneSlot`: a `t`-run is ONE firing-block slot;
`alignmentPerLetterCountEqWordLength`: the per-letter layout is one slot per letter — DIFFER for a run of length
`≥ 2`).  So alignment holds at the firing-block SKELETON: any two layouts of the same cell share the rigid wall
skeleton, differing only in FREE padding (`emptyGapLayout_conv_id`, shipped) and the atomic firing that fills each
gap.  Round decision: ALIGNABLE, so NOT a refutation ship — the round is the multi-gap PLUMBING plus this
adjudication.  `= true`. -/
def fxAmalg_alignmentVerdictAlignableAtSkeleton : Bool := true

/-- ★★★ **Honesty marker — ALIGNABLE is at the SKELETON; the per-gap DESCENT stays JAM A; the alignment LEMMA is
r17 (WP-AMALG-2 r16, B1).**  `= true` (the honest limit).  The verdict is ALIGNABLE at the firing-block SKELETON
level — the skeleton is rigid and provable (machine-anchored above).  It does NOT close #2043: (1) the DESCENT of a
whole-cell convertibility to per-gap convertibilities (the "conv-of-images ⟹ equal-layouts" half) is the
purification question, `fxAmalg_hasSaturatedDispatchTheorem = false` (JAM A) — the wire-creating `eta`/`mu` are
exactly what the Nelson-Oppen soundness precondition ("word-preserving / left-connected") violates, so the descent is
a signature-specific soundness lemma, not yet a proof; (2) the per-gap comparison, once descended, is the MONAD word
problem (WalkingMonad lane, READ-ONLY, fib-3-coupled reconstruction-faithfulness iso).  So the alignment LEMMA (two
firing-block layouts share the rigid skeleton, assembled from `wallLetterCount_dom_eq_cod` + `emptyGapLayout_conv_id`
at firing-block granularity) is TRUE and r17-authorable, but it is ONE ingredient.  A canonical multi-slot reader
NARROWS JAM A from "no reflection at all" to "the skeleton reflects; the per-gap descent is the residual" — a real
narrowing, not a close.  `fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`;
`fxAmalg_hasSaturatedDispatchTheorem` STAYS `false`.  `= true`. -/
def fxAmalg_alignmentDescentStaysJamA : Bool := true

/-- The two named walls STAY at their open values under the ALIGNABLE verdict (`rfl`) — the verdict narrows, it does
not flip.  JAM A purification is `false`; the top factorisation is `true` (walled). -/
theorem alignmentVerdictFlipsNoMaster :
    fxAmalg_hasSaturatedDispatchTheorem = false
      ∧ fxAmalg_topFactorizationInductionStaysWalled = true :=
  ⟨rfl, rfl⟩

end FX1Poly.Polygraph.Amalgam
