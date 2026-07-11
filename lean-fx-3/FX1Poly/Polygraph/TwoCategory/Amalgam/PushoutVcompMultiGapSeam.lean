import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerHeadPrependMultiGap
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutAlignmentTruthProbe

/-! # Polygraph/TwoCategory/Amalgam/PushoutVcompMultiGapSeam — the vcomp case at GENUINE multi-gap granularity: the
r9 seam fired through a SHARED two-gap layout; the full closure stays reader-gated (WP-AMALG-2 r16, Brick B3)

r15's `vcomp` base case (`pushoutFactorizeVcompSingleGap`) buried both halves in ONE shared gap's vertical split
(`slotCount = 1`).  The r16 recon's leg 3 (verdict-conditional on §1 = ALIGNABLE) wants the vcomp arm at GENUINE
multi-gap granularity: two half-cells factoring through a SHARED multi-slot firing-block layout, vertically composed
by the shipped r9 seam.  The alignment the arm consumes — that both halves present the SAME wall skeleton so their gap
lists are index-aligned — is EXACTLY the §1 question, and the B1 verdict (`fxAmalg_alignmentVerdictAlignableAtSkeleton`)
certifies it: the shared skeleton is the middle 1-cell's rigid wall skeleton.

## The vcomp arm at multi-gap granularity

`pushoutFactorizeVcompLayout` (shipped, `PushoutVcompSeam.lean`) takes two half-factorizations through ONE SHARED
`(finalWall, pairs)` and produces `PushoutLayoutFactorization baseRel (vcomp cellUpper cellLower)` on that shared
layout — the seam `pushoutFactorizeVcompSeam` threading `hUpper` / `hLower` through `vcompCongrLeft`/`Right` then
firing the r7 crux `vcompGapInterchangeSplice` gap-by-gap.  This file EXERCISES it at a GENUINE TWO-gap shared layout
(the r7 `[mu-assoc, left-unit]` pairs): `vcomp (gapUpperLayout …) (gapLowerLayout …)` factors into the SHARED two-gap
layout, `slotCount = 2 > 1` — the multi-gap vcomp the r15 single-gap base could not present.

## What alignment fact it consumes (EXACTLY the §1 question)

To vertically compose the two halves through ONE shared `pairs`, both must present the SAME wall SKELETON so the gap
lists are index-aligned (gap `i` of the upper shares its middle 1-cell with gap `i` of the lower).  §1 verdict
ALIGNABLE: YES — the shared skeleton is the middle 1-cell's rigid wall skeleton (`wallLetterCount_dom_eq_cod` +
`emptyGapLayout_conv_id`), NOT the walled per-letter zip.  Here the two halves are given ON the shared layout (the
witness supplies them reflexively); the seam then fires, cast-free.

## What STAYS WALLED (no flip) — the FULL closure is reader-gated

This exercises the vcomp arm at multi-gap granularity GIVEN two half-factorizations through a shared layout.  The FULL
closure — PRODUCING that shared multi-gap layout off two ARBITRARY cells `cellUpper` / `cellLower` — is the CANONICAL
firing-block READER (produce a firing-block layout off an arbitrary cell), which is deferred to r17 (recon §6).  The
seam CONSUMES a shared layout; PRODUCING it is the reader.  `fxAmalg_topFactorizationInductionStaysWalled` STAYS
`true`; the masters STAY at their walled values; #2043 does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The vcomp arm at genuine multi-gap granularity -/

/-- ★★★ **THE MULTI-GAP VCOMP SEAM WITNESS.**  The vertical composite of the UPPER and LOWER cell layouts of the r7
TWO-gap shared layout `[interleavedAssocGapPair, interleavedLeftUnitGapPair]` (a `mu`-associativity `t³ ⇒ t` in gap 1
and a left-unit `t ⇒ t` in gap 2, at the REAL pushout signature) factors, via the shipped seam
`pushoutFactorizeVcompLayout`, into the SHARED TWO-gap layout.  The two halves are supplied reflexively (they ARE the
upper / lower layouts of the shared `pairs`); the seam fires the r7 crux gap-by-gap.  A genuine multi-gap `vcomp`
factorization — `slotCount = 2`, not the r15 single shared gap. -/
def pushoutVcompMultiGapSeamWitness :
    PushoutLayoutFactorization crossPairRealPushoutRel
      (RawTwoCellExpr.vcomp
        (gapUpperLayout pushoutTrivialWall [interleavedAssocGapPair, interleavedLeftUnitGapPair])
        (gapLowerLayout pushoutTrivialWall [interleavedAssocGapPair, interleavedLeftUnitGapPair])) :=
  pushoutFactorizeVcompLayout crossPairRealPushoutRel pushoutTrivialWall
    [interleavedAssocGapPair, interleavedLeftUnitGapPair]
    (gapUpperLayout pushoutTrivialWall [interleavedAssocGapPair, interleavedLeftUnitGapPair])
    (gapLowerLayout pushoutTrivialWall [interleavedAssocGapPair, interleavedLeftUnitGapPair])
    (SaturatedConvOver.refl _) (SaturatedConvOver.refl _)

/-- ★★★ **PROBE (multi-gap vcomp slotCount > 1).**  The multi-gap vcomp seam witness factors through a SHARED TWO-gap
layout (`pairs.length = 2`, `rfl`) — the two firing-block gaps of the shared middle 1-cell, NOT the r15 single shared
gap.  The genuine multi-gap `vcomp` the base case could not present. -/
theorem pushoutVcompMultiGapSeamWitness_slotCount : pushoutVcompMultiGapSeamWitness.pairs.length = 2 := rfl

/-- ★★ **The whiskered multi-gap vcomp — the two arms COMPOSE.**  Feeding the multi-gap vcomp factorization into the
r16 head-prepend arm (`pushoutFactorizeWhiskerLeftMultiGap`) frames the two-gap vcomp with an `s` and yields a
THREE-slot layout — the B2 and B3 arms composing, a genuinely deeper framed multi-gap cell. -/
def pushoutVcompThenWhiskerMultiGapWitness :
    PushoutLayoutFactorization crossPairRealPushoutRel
      (RawTwoCellExpr.whiskerLeft monadPushSPath
        (RawTwoCellExpr.vcomp
          (gapUpperLayout pushoutTrivialWall [interleavedAssocGapPair, interleavedLeftUnitGapPair])
          (gapLowerLayout pushoutTrivialWall [interleavedAssocGapPair, interleavedLeftUnitGapPair]))) :=
  pushoutFactorizeWhiskerLeftMultiGap crossPairRealPushoutRel monadPushSPath pushoutVcompMultiGapSeamWitness

/-- ★★ **PROBE (composed arms slotCount).**  The head-prepend of the multi-gap vcomp witness has `pairs.length = 3`
(`rfl`) — the `s`-frame slot plus the two shared vcomp gaps.  The B2 head-prepend and B3 multi-gap vcomp arms compose
into a deeper multi-slot layout. -/
theorem pushoutVcompThenWhiskerMultiGapWitness_slotCount :
    pushoutVcompThenWhiskerMultiGapWitness.pairs.length = 3 := rfl

/-! ## The skeleton-share adjudication (the §1 verdict consumed) -/

/-- ★★ **The multi-gap vcomp arm consumes the ALIGNABLE skeleton-share.**  The two halves of the witness factor
through the SAME shared layout — index-aligned at the middle 1-cell's rigid wall skeleton, exactly the §1 alignment
fact.  The B1 verdict `fxAmalg_alignmentVerdictAlignableAtSkeleton = true` certifies that share; the master
`fxAmalg_topFactorizationInductionStaysWalled = true` records that PRODUCING the shared layout off two arbitrary cells
(the reader) is NOT yet supplied.  Both machine-checked `rfl`. -/
theorem pushoutVcompMultiGapConsumesAlignableSkeleton :
    fxAmalg_alignmentVerdictAlignableAtSkeleton = true
      ∧ fxAmalg_topFactorizationInductionStaysWalled = true :=
  ⟨rfl, rfl⟩

/-! ## Observability -/

-- The multi-gap vcomp seam witness slot count (expect `2`) and the whiskered composite (expect `3`).
#eval pushoutVcompMultiGapSeamWitness.pairs.length
#eval pushoutVcompThenWhiskerMultiGapWitness.pairs.length

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the vcomp arm fires at GENUINE multi-gap granularity (WP-AMALG-2 r16, B3).**  `= true`.
`pushoutVcompMultiGapSeamWitness` factors a vertical composite through a SHARED TWO-gap layout
(`pushoutVcompMultiGapSeamWitness_slotCount`, `= 2`) — the shipped seam `pushoutFactorizeVcompLayout` firing the r7
crux `vcompGapInterchangeSplice` gap-by-gap on the r7 `[mu-assoc, left-unit]` pairs at the REAL pushout signature —
the genuine multi-gap `vcomp` the r15 single-gap base could not present.  It composes with the B2 head-prepend
(`pushoutVcompThenWhiskerMultiGapWitness`, `slotCount = 3`).  The alignment it consumes is exactly the §1 skeleton
share, certified by the B1 verdict (`pushoutVcompMultiGapConsumesAlignableSkeleton`).  `= true`. -/
def fxAmalg_hasVcompMultiGapSeam : Bool := true

/-- ★★ **Honesty marker — the FULL vcomp multi-gap closure is READER-GATED (WP-AMALG-2 r16, B3).**  `= true` (the
wall is honestly held).  The multi-gap vcomp seam fires GIVEN two half-factorizations through a SHARED multi-gap
layout (the witness supplies them reflexively).  The FULL closure — PRODUCING that shared multi-gap firing-block
layout off two ARBITRARY cells `cellUpper` / `cellLower` — is the CANONICAL firing-block READER (produce a firing-block
layout off an arbitrary cell), deferred to r17 (recon §6).  The seam CONSUMES a shared layout; the reader PRODUCES it,
and the per-gap DESCENT it feeds is JAM A (`fxAmalg_hasSaturatedDispatchTheorem = false`).  Named node: the canonical
firing-block reader + the per-gap descent.  `fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`;
`fxAmalg_hasFullSaturatedPushoutDispatch` / `fxAmalg_hasGeneralPushoutDispatch` STAY `false`.  #2043 does NOT close.
No fabricated flip.  `= true`. -/
def fxAmalg_vcompMultiGapFullClosureGatedOnReader : Bool := true

end FX1Poly.Polygraph.Amalgam
