import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutShiftedGapSplice
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordVcompReconstructed

/-! # Polygraph/TwoCategory/Amalgam/PushoutReconstructedWordGapSplice — the multi-gap gap-EZ splice on the RESEAT
(WP-AMALG-2 r14, Brick B2 — Finding-C's splice, per-gap content produced GENERICALLY from the reseat)

`PushoutShiftedGapSplice` (r6) shipped `multiGapShiftedSplice`: a LIST of wire-changing wall/gap fills splices into
ONE boundary convertibility by pure `hcompCongr` closure across the inert `s`-walls, hypothesis-free.  But its
non-vacuity witnesses (`shiftedAssocGapFill` / `shiftedLeftUnitGapFill`) HAND-WITNESS each gap's fill by a fixed
right-image collapse (`pushoutAssocGapConv` / `pushoutLeftUnitGapConv`).  This file supplies the per-gap fill
GENERICALLY from the reseat (B1's `wordMul_vcompReconstructed`) lifted by `pushoutRightImageCompletenessLift` — so
a gap whose within-gap firing is a vertical word stack `word ccL ⊟ word ccR` gets its normal-form collapse from the
reconstructed word multiplicativity, not a bespoke per-cell witness.

## What ships (each zero-axiom, STRUCTURAL, ASCII-only)

  * **`reconWordGapFill`** — the GENERIC per-gap fill: the reconstructed vertical word stack
    `vcomp (reconWordFromCounts ccL) (cast (reconWordFromCounts ccR))` collapses to
    `cast (reconWordFromCounts (composeCounts ccL ccR))`, right-coprojected into the pushout.  Its `fill` is
    `pushoutRightImageCompletenessLift (wordMul_vcompReconstructed ccR ccL hlen)` — reseat content, no bespoke
    witness.  The generic extension of `shiftedAssocGapFill`.
  * **`reconWordThreeGapSplice`** — the THREE-gap probe: three reseat-produced gap fills (`t²⇒t`, endo `t⇒t`,
    `t²⇒t`) spliced end-to-end across three `s`-walls, confirming the `gap :: rest` recursion and the wall-shift
    absorption are not two-gap-specific and that the reseat-produced fills compose.

## The boundary (what does NOT ship)

This is the SPLICE assembled on the reseat: given the per-gap firing as a within-gap word stack, the gap-EZ
collapse + the multi-gap wall re-nesting ship.  What is STILL missing is the TOP firing-block FACTORISATION
`pushoutFactorize` — the reader that produces the `ShiftedGapFill` list (each slot a maximal firing region) off an
ARBITRARY cell's boundary (`blockDecompose↔composePath` + `mergeFrameIntoHead/Tail`).  Without that reader there is
no total `Decidable`, so masters (ii)/(iii) HOLD; `#2043` does NOT close.  See `fxAmalg_pushoutNormalFormSpliceShips`.
The wall marker `PushoutNormalForm.fxAmalg_pushoutNormalFormSpliceStaysWalled` is NOT flipped — this file adds a
positive marker alongside it for exactly the fragment now authored.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The generic per-gap fill from the reseat -/

/-- ★★ **The GENERIC reconstructed-word gap fill.**  A gap whose within-gap firing is a vertical stack of two
canonical words `word ccL ⊟ word ccR` (partition `ccL.length = listSum ccR`) collapses to the single canonical word
`word (composeCounts ccL ccR)`, right-coprojected into the pushout.  The `fill` is
`pushoutRightImageCompletenessLift (wordMul_vcompReconstructed ..)` — the reseat content, produced GENERICALLY (no
bespoke per-cell witness like `shiftedAssocGapFill`'s `pushoutAssocGapConv`).  All boundary fields inferred from the
fill's parallel endpoints. -/
def reconWordGapFill (ccR ccL : List Nat) (hlen : ccL.length = listSum ccR) :
    ShiftedGapFill involutionMonadPushout.toModeSignature crossPairRealPushoutRel monadPushMode :=
  ⟨_, _, _, _, pushoutRightImageCompletenessLift (wordMul_vcompReconstructed ccR ccL hlen)⟩

/-! ## The three-gap probe -/

/-- The three-gap layout: two genuine merges (`t²⇒t`, `composeCounts [1,1] [2] = [2]`) bracketing an endo merge
(`t⇒t`, `composeCounts [1] [1] = [1]`), each fill reseat-produced.  Mirrors the recon's `[assoc, leftUnit, assoc]`
shape but with the per-gap content generic (from `wordMul_vcompReconstructed`), not hand-witnessed. -/
def reconWordThreeGapLayout :
    List (ShiftedGapFill involutionMonadPushout.toModeSignature crossPairRealPushoutRel monadPushMode) :=
  [reconWordGapFill [2] [1, 1] rfl, reconWordGapFill [1] [1] rfl, reconWordGapFill [2] [1, 1] rfl]

/-- ★★ **The three-gap splice fires on reseat-produced fills.**  `multiGapShiftedSplice` on the three-gap layout
`[t²⇒t, t⇒t, t²⇒t]` (walls `s` before each) produces one pushout convertibility from the presented layout to its
normalized form — three reseat-produced gap fills composed END-TO-END across three `s`-walls.  Confirms the
`gap :: rest` recursion and wall-shift absorption are not two-gap-specific, and that the generic
`reconWordGapFill` content threads through the splice. -/
def reconWordThreeGapSplice :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (shiftedGapSourceCell monadPushSPath reconWordThreeGapLayout)
      (shiftedGapTargetCell monadPushSPath reconWordThreeGapLayout) :=
  multiGapShiftedSplice monadPushSPath reconWordThreeGapLayout

/-! ## Honesty marker -/

/-- ★★ **Honesty marker — the gap-EZ splice on the RESEAT SHIPS (WP-AMALG-2 r14, B2).**  `= true`: the per-gap
firing collapse is now produced GENERICALLY from the reseat — `reconWordGapFill` packs
`pushoutRightImageCompletenessLift (wordMul_vcompReconstructed ..)` as the gap's `fill`, so a within-gap vertical
word stack `word ccL ⊟ word ccR` gets its normal-form collapse from the reconstructed word multiplicativity (B1),
not a bespoke per-cell witness.  `multiGapShiftedSplice` then splices an arbitrary LIST of such generic gap fills
across the inert `s`-walls into one boundary convertibility, non-vacuous on the THREE-gap probe
`reconWordThreeGapSplice` (`t²⇒t`, endo `t⇒t`, `t²⇒t`, END-TO-END).  This authors the CONTENT crux named in
`PushoutNormalForm.fxAmalg_pushoutNormalFormSpliceStaysWalled` (the gap-EZ splice's per-gap content, `wordMul_vcomp`
reseated).  It does NOT flip that wall marker: the FULL NF-soundness still needs the TOP firing-block factorisation
reader `pushoutFactorize` (produce the `ShiftedGapFill` list off an ARBITRARY cell), which the reseat does not
provide.  So masters (ii)/(iii) HOLD and `#2043` does NOT close.  `= true`. -/
def fxAmalg_pushoutNormalFormSpliceShips : Bool := true

end FX1Poly.Polygraph.Amalgam
