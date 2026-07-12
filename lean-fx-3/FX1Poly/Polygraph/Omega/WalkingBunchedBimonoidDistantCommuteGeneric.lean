import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidDistantCommuteOverSibling

/-! # Polygraph/Omega/WalkingBunchedBimonoidDistantCommuteGeneric — the FULLY GENERIC distant-commute
`sigmaAt w i ; sigmaAt w j ~ sigmaAt w j ; sigmaAt w i` (`j >= i + 2`) as ONE Godement interchange fire under a
left pad, in additive-parameter form, over the SHIPPED star scope (WP-PROP r21, G1+G2)

★ **THE r20 CENSUS CLAIM (item 1) IS REFUTED — the fully generic `(w, i, j)` distant-commute is NOT a
completeness-star fragment.**  The r20 `RunCommuteConvOverSibling` census
(`fxBunchedBimonoid_starChainCensusAfterUThreeStillOpen`, item 1;
`fxBunchedBimonoid_distantCommuteGenericPositionStillWalled`) recorded arbitrary left/middle/right padding as
needing "the general block Godement interchange — a completeness-star fragment".  This file demonstrates that
`StrictAxiomRel.interchange` is ALREADY generic in `alpha` / `beta`, and the r19 whisker-1-cell associator
(`StrictAxiomRel.whiskerAssocLeft`) + the r19/r15 word-fold bricks (`bunchedBimonoidAWordPowSplitConv`,
`bunchedBimonoidAWordPowTwoIsAaWordConv`) close the padding — so the generic distant-commute lands over the
SHIPPED `bunchedBimonoidStarCongruenceScope` (STRONGER than the U2 sibling delivery), spending NO unitor and
adding NO row.  It is in fact SIMPLER than the U2 `(4, 0, 2)` special case (which reshaped to the bare r9 legs
and spent the U1 point unitor): here the outer `A^leftPad <|` is kept and the interchange fires UNDER
`whiskerLeftCongr`, so the edge pads are never stripped.

This is the printed literature fact made kernel-checked.  Savage (Diagrammatic Techniques 2025, (3.9)/(3.10)):
"the distant braid relation (3.9) `s_i s_j = s_j s_i`, `|i - j| > 1`, follows for free from the interchange law".
Polygraphs (arXiv:2312.00429, Prop 4.1.7 (4.6)): in a 2-category `(alpha g) * (f' beta) = (f beta) * (alpha g')`
— our two whisker orders.  The genuine RESIDUAL is exactly what interchange canNOT reach: the involution
`s_i^2 = 1` (shipped, S2 CANCEL letter) and the ADJACENT braid `s_i s_{i+1} s_i = s_{i+1} s_i s_{i+1}` (Savage
(3.7)/(3.8)) — the adjacent atom stays compute-walled (its width-4 triple-vcomp endpoint `rfl` exceeds even the
4M-heartbeat budget, r20 finding), NOT a soundness gap.

## The additive-parameter form (the Nat-subtraction trap SIDESTEPPED)

The position-indexed letter `sigmaAt w k = A^k <| (sigma |> A^(w - k - 2))` carries truncated subtraction.  We
parameterize by the three PADS `(leftPad, gap, rightPad)` so the exponents are pure ADDITIONS matching the
additive letters on the nose — no `w - i - 2` ever appears in the core.  With `w = leftPad + gap + rightPad + 4`,
`i = leftPad`, `j = leftPad + gap + 2`:

  * `firstLetter  = A^leftPad <| (sigma |> A^(gap + (2 + rightPad)))`  (`= sigmaAt w i` at concrete numerals),
  * `secondLetter = A^(leftPad + (2 + gap)) <| (sigma |> A^rightPad)`  (`= sigmaAt w j` at concrete numerals),
  * `gapSigma     = A^gap <| (sigma |> A^rightPad)`  — the padded inner sigma; `alpha = sigma`, `beta = gapSigma`.

At CONCRETE numerals the additive letters are DEFINITIONALLY the `sigmaAt` letters (the subtraction computes), so
the concrete `sigmaAt`-form corollaries follow from the generic theorem by `rfl`-transport — delivering the bill's
literal `sigmaAt w i / sigmaAt w j` shape at width 5 and 6 with no general subtraction lemma.

## The one Godement fire (the ladder)

`interchange sigma gapSigma` gives, under `whiskerLeftCongr (A^leftPad)`, the two whisker orders of the horizontal
composite; both factors are then reshaped by the SAME dim-1 word fold `bunchedBimonoidWordTripleFoldConv`
(`A^p . (aa . A^q) ~ A^(p + (2 + q))`, assembled from the shipped `aWordPowSplitConv` + `aWordPowTwoIsAaWordConv`).
The first factor reshapes under `whiskerRightWhiskerCongr sigma`; the second nests two `whiskerAssocLeft` firings
before the fold.  No new row, no unitor, no hypothesis.

## The honest scope

The generic distant-commute (Coxeter relation (3.9)) is DELIVERED over the shipped star scope; the sibling form is
the free `bunchedBimonoidStarScopeEmbedsIntoPointUnitorSibling` wrapper.  The ADJACENT braid atom (Coxeter
(3.8)) stays compute-walled; the TRAILING-BOUNDARY reshape + the `permWord`-fold lift (the `vcomp`-form → the
`permWord [..] w` fold) is the r22 rung (its dim-1 leg is exactly `bunchedBimonoidWordTripleFoldConv` +
`bunchedBimonoidSigmaAtBoundaryReshapeConv`, both shipped).  The four star owners (StarAssembly / RiffleAssembly /
CollisionCanonForm / CoxeterUniqueness) stay `= false` byte-intact; the shipped `StrictAxiomRel` + star scope are
untouched; the r20 markers stay byte-intact cross-file (their generic-distant clause is now stale, retire-name-only
rule — this file's docstring corrects the "completeness-star fragment" denotation).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

/-! The concrete `sigmaAt`-form endpoint matrix `rfl` pins evaluate at width 5-6, exceeding the default heartbeat
budget; the raise is a compute allowance only, every generic proof term stays congruence-constructor plumbing,
axiom-free (uniform with the r9 `CoxeterUniqueness` / r20 `DistantCommuteOverSibling`).  The width-4 braid atom's
triple-vcomp endpoint `rfl` exceeds even 4M and is NOT pinned here (compute wall, not soundness). -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # G1.A — THE PADDED-SIGMA CARRIER + ITS SOURCE WORD (additive; no subtraction)
    # =========================================================================================
-/

/-- ★ The **gap-padded inner sigma** `gapSigma gap rightPad = A^gap <| (sigma |> A^rightPad)` — the middle
argument `beta` of the Godement interchange fire.  An endomorphism whose source and target words both compute to
`A^gap . (aa . A^rightPad)` (the `sigma`-source tree with the gap prefix and the right pad). -/
def bunchedBimonoidDistantGapSigma (gap rightPad : Nat) : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerLeft (bunchedBimonoidAWordPow gap)
    (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow rightPad))

/-- ★ The **gap-padded sigma source word** `gapSource gap rightPad = A^gap . (aa . A^rightPad)` — definitionally
`boundarySource (gapSigma gap rightPad)` and `boundaryTarget (gapSigma gap rightPad)` (both reduce to this tree,
since `sigma`'s two boundaries are `aa`).  Written explicitly so the interchange-fire endpoints are transparent. -/
def bunchedBimonoidDistantGapSource (gap rightPad : Nat) : CellExpr bunchedBimonoidOmegaComputad 1 :=
  CellExpr.vcomp (bunchedBimonoidAWordPow gap)
    (CellExpr.vcomp bunchedBimonoidAaWord (bunchedBimonoidAWordPow rightPad))

/-! # =========================================================================================
    # G1.B — THE REUSABLE DIM-1 WORD FOLD `A^p . (aa . A^q) ~ A^(p + (2 + q))` (Brick A)
    # =========================================================================================

★ The reshape ladder's engine — the single dim-1 fact both padded factors need.  This is ALSO G3's dim-1 leg
(the trailing-boundary reshape `boundaryTarget (sigmaAt w k) ~ aWordPow w` is this + the shipped truncated-sub
lemma `bunchedBimonoidSigmaAtBoundaryReshapeConv`).  It replaces the U1 stuck-term workarounds: `aWordPow`'s head
is the plain generator (boundary = point on the nose), so the fold is pure `aWordPowSplitConv` plumbing — no
`0 + n` / map-over-opaque stuck term, no `rfl`-hope on a generic cell. -/

/-- ★★ **THE DIM-1 WORD TRIPLE FOLD `A^p . (aa . A^q) ~ A^(p + (2 + q))`.**  The two-strand block `aa` between an
`A^leadPad` prefix and an `A^tailPad` suffix folds into the flat word `A^(leadPad + (2 + tailPad))` over the
shipped star scope: `aa ~ A^2` (`aWordPowTwoIsAaWordConv`, symm) under `vcompCongrLeft (A^tailPad)`, then
`A^2 . A^tailPad ~ A^(2 + tailPad)` (`aWordPowSplitConv 2 tailPad`, symm) under `vcompCongrRight (A^leadPad)`,
then `A^leadPad . A^(2 + tailPad) ~ A^(leadPad + (2 + tailPad))` (`aWordPowSplitConv leadPad (2 + tailPad)`, symm).
The reusable engine of both letter reshapes (and G3's trailing-boundary dim-1 leg). -/
theorem bunchedBimonoidWordTripleFoldConv (leadPad tailPad : Nat) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp (bunchedBimonoidAWordPow leadPad)
        (CellExpr.vcomp bunchedBimonoidAaWord (bunchedBimonoidAWordPow tailPad)))
      (bunchedBimonoidAWordPow (leadPad + (2 + tailPad))) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrRight (bunchedBimonoidAWordPow leadPad)
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrLeft (bunchedBimonoidAWordPow tailPad)
          (SaturatedConvOverWithId.symm bunchedBimonoidAWordPowTwoIsAaWordConv))
        (SaturatedConvOverWithId.symm (bunchedBimonoidAWordPowSplitConv 2 tailPad))))
    (SaturatedConvOverWithId.symm (bunchedBimonoidAWordPowSplitConv leadPad (2 + tailPad)))

/-! # =========================================================================================
    # G1.C — THE TWO PADDED-LETTER RESHAPES (Bricks B and C)
    # =========================================================================================
-/

/-- ★ **The first-letter reshape (Brick B)** — the interchange-LHS first factor
`A^leftPad <| (sigma |> gapSource)` reshapes to `firstLetter = A^leftPad <| (sigma |> A^(gap + (2 + rightPad)))`.
The gap-source word folds by `bunchedBimonoidWordTripleFoldConv gap rightPad` under `whiskerRightWhiskerCongr
sigma` (vary the whiskering 1-cell), all under `whiskerLeftCongr (A^leftPad)`.  The edge pad `A^leftPad` is never
stripped. -/
theorem bunchedBimonoidDistantFirstLetterReshapeConv (leftPad gap rightPad : Nat) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow leftPad)
        (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidDistantGapSource gap rightPad)))
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow leftPad)
        (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen
          (bunchedBimonoidAWordPow (gap + (2 + rightPad))))) :=
  SaturatedConvOverWithId.whiskerLeftCongr (bunchedBimonoidAWordPow leftPad)
    (SaturatedConvOverWithId.whiskerRightWhiskerCongr bunchedBimonoidAddSigmaGen
      (bunchedBimonoidWordTripleFoldConv gap rightPad))

/-- ★ **The second-letter reshape (Brick C)** — the interchange-side factor
`A^leftPad <| (aa <| gapSigma)` reshapes to `secondLetter = A^(leftPad + (2 + gap)) <| (sigma |> A^rightPad)`.
Two `whiskerAssocLeft` firings re-associate the nested whisker `aa <| (A^gap <| Z)` into `(A^leftPad . (aa .
A^gap)) <| Z` (with `Z = sigma |> A^rightPad`), then `bunchedBimonoidWordTripleFoldConv leftPad gap` folds the
1-cell `A^leftPad . (aa . A^gap) ~ A^(leftPad + (2 + gap))` under `whiskerLeftWhiskerCongr Z`. -/
theorem bunchedBimonoidDistantSecondLetterReshapeConv (leftPad gap rightPad : Nat) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow leftPad)
        (CellExpr.whiskerLeft bunchedBimonoidAaWord (bunchedBimonoidDistantGapSigma gap rightPad)))
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow (leftPad + (2 + gap)))
        (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow rightPad))) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.whiskerLeftCongr (bunchedBimonoidAWordPow leftPad)
      (SaturatedConvOverWithId.symm
        (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
          (StrictAxiomRel.whiskerAssocLeft bunchedBimonoidAaWord (bunchedBimonoidAWordPow gap)
            (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow rightPad))))))
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.symm
        (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
          (StrictAxiomRel.whiskerAssocLeft (bunchedBimonoidAWordPow leftPad)
            (CellExpr.vcomp bunchedBimonoidAaWord (bunchedBimonoidAWordPow gap))
            (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow rightPad)))))
      (SaturatedConvOverWithId.whiskerLeftWhiskerCongr
        (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow rightPad))
        (bunchedBimonoidWordTripleFoldConv leftPad gap)))

/-! # =========================================================================================
    # G1.D — THE TWO FUNCTORIAL FOLDS (the interchange sides collapse to the paired letters)
    # =========================================================================================
-/

/-- ★ **The interchange-LHS fold** — `A^leftPad <| ((sigma |> gapSource) . (aa <| gapSigma))` folds to
`vcomp firstLetter secondLetter`, by `whiskerLeftFunctorial` distributing the outer pad over the vcomp then the
two letter reshapes (Bricks B, C) under `vcompCongrLeft` / `vcompCongrRight`. -/
theorem bunchedBimonoidDistantLhsFoldConv (leftPad gap rightPad : Nat) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow leftPad)
        (CellExpr.vcomp
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidDistantGapSource gap rightPad))
          (CellExpr.whiskerLeft bunchedBimonoidAaWord (bunchedBimonoidDistantGapSigma gap rightPad))))
      (CellExpr.vcomp
        (CellExpr.whiskerLeft (bunchedBimonoidAWordPow leftPad)
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen
            (bunchedBimonoidAWordPow (gap + (2 + rightPad)))))
        (CellExpr.whiskerLeft (bunchedBimonoidAWordPow (leftPad + (2 + gap)))
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow rightPad)))) :=
  SaturatedConvOverWithId.trans
    (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
      (StrictAxiomRel.whiskerLeftFunctorial (bunchedBimonoidAWordPow leftPad)
        (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidDistantGapSource gap rightPad))
        (CellExpr.whiskerLeft bunchedBimonoidAaWord (bunchedBimonoidDistantGapSigma gap rightPad))))
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.vcompCongrLeft
        (CellExpr.whiskerLeft (bunchedBimonoidAWordPow leftPad)
          (CellExpr.whiskerLeft bunchedBimonoidAaWord (bunchedBimonoidDistantGapSigma gap rightPad)))
        (bunchedBimonoidDistantFirstLetterReshapeConv leftPad gap rightPad))
      (SaturatedConvOverWithId.vcompCongrRight
        (CellExpr.whiskerLeft (bunchedBimonoidAWordPow leftPad)
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen
            (bunchedBimonoidAWordPow (gap + (2 + rightPad)))))
        (bunchedBimonoidDistantSecondLetterReshapeConv leftPad gap rightPad)))

/-- ★ **The interchange-RHS fold** — `A^leftPad <| ((aa <| gapSigma) . (sigma |> gapSource))` folds to
`vcomp secondLetter firstLetter` (the reversed order), by the same `whiskerLeftFunctorial` distribution and the
two letter reshapes swapped. -/
theorem bunchedBimonoidDistantRhsFoldConv (leftPad gap rightPad : Nat) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow leftPad)
        (CellExpr.vcomp
          (CellExpr.whiskerLeft bunchedBimonoidAaWord (bunchedBimonoidDistantGapSigma gap rightPad))
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidDistantGapSource gap rightPad))))
      (CellExpr.vcomp
        (CellExpr.whiskerLeft (bunchedBimonoidAWordPow (leftPad + (2 + gap)))
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow rightPad)))
        (CellExpr.whiskerLeft (bunchedBimonoidAWordPow leftPad)
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen
            (bunchedBimonoidAWordPow (gap + (2 + rightPad)))))) :=
  SaturatedConvOverWithId.trans
    (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
      (StrictAxiomRel.whiskerLeftFunctorial (bunchedBimonoidAWordPow leftPad)
        (CellExpr.whiskerLeft bunchedBimonoidAaWord (bunchedBimonoidDistantGapSigma gap rightPad))
        (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidDistantGapSource gap rightPad))))
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.vcompCongrLeft
        (CellExpr.whiskerLeft (bunchedBimonoidAWordPow leftPad)
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidDistantGapSource gap rightPad)))
        (bunchedBimonoidDistantSecondLetterReshapeConv leftPad gap rightPad))
      (SaturatedConvOverWithId.vcompCongrRight
        (CellExpr.whiskerLeft (bunchedBimonoidAWordPow (leftPad + (2 + gap)))
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow rightPad)))
        (bunchedBimonoidDistantFirstLetterReshapeConv leftPad gap rightPad)))

/-! # =========================================================================================
    # G2 — THE GENERIC DISTANT-COMMUTE (ONE Godement fire under the left pad), over the star scope
    # =========================================================================================
-/

/-- ★★★ **THE FULLY GENERIC DISTANT-COMMUTE — Coxeter relation (3.9), ONE Godement interchange fire.**
For any pads `(leftPad, gap, rightPad)`, `vcomp firstLetter secondLetter ~ vcomp secondLetter firstLetter` over
the SHIPPED `bunchedBimonoidStarCongruenceScope`, where

  `firstLetter  = A^leftPad <| (sigma |> A^(gap + (2 + rightPad)))`   ( = `sigmaAt w i` at numerals),
  `secondLetter = A^(leftPad + (2 + gap)) <| (sigma |> A^rightPad)`   ( = `sigmaAt w j` at numerals),
  `w = leftPad + gap + rightPad + 4`, `i = leftPad`, `j = leftPad + gap + 2` (`j = i + gap + 2 >= i + 2`).

The proof: `symm` of the LHS fold, then the single `interchange sigma gapSigma` embedded into the star scope and
whiskered under `whiskerLeftCongr (A^leftPad)`, then the RHS fold — the two whisker orders of the horizontal
composite `sigma *_0 gapSigma`.  Over the SHIPPED star scope (no unitor, no new row); STRONGER than the U2 sibling
`(4, 0, 2)` delivery, which it subsumes at `(0, 0, 0)`.  This machine-checks the printed
"distant relation follows for free from interchange" (Savage (3.9); Polygraphs (4.6)) at ARBITRARY width — the
gap the formalized literature left (no named kernel-checked `interchange |- s_i s_j = s_j s_i` at generic width
exists in Mathlib/Coq/Agda; the distant relation there is absorbed into strictification/coherence tactics). -/
theorem bunchedBimonoidDistantCommuteGenericLetterConv (leftPad gap rightPad : Nat) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp
        (CellExpr.whiskerLeft (bunchedBimonoidAWordPow leftPad)
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen
            (bunchedBimonoidAWordPow (gap + (2 + rightPad)))))
        (CellExpr.whiskerLeft (bunchedBimonoidAWordPow (leftPad + (2 + gap)))
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow rightPad))))
      (CellExpr.vcomp
        (CellExpr.whiskerLeft (bunchedBimonoidAWordPow (leftPad + (2 + gap)))
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow rightPad)))
        (CellExpr.whiskerLeft (bunchedBimonoidAWordPow leftPad)
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen
            (bunchedBimonoidAWordPow (gap + (2 + rightPad)))))) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.symm (bunchedBimonoidDistantLhsFoldConv leftPad gap rightPad))
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.whiskerLeftCongr (bunchedBimonoidAWordPow leftPad)
        (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
          (StrictAxiomRel.interchange bunchedBimonoidAddSigmaGen
            (bunchedBimonoidDistantGapSigma gap rightPad))))
      (bunchedBimonoidDistantRhsFoldConv leftPad gap rightPad))

/-- ★★ **THE GENERIC DISTANT-COMMUTE OVER THE SIBLING** — the free `bunchedBimonoidStarScopeEmbedsIntoPointUnitorSibling`
wrapper transports the generic theorem to `bunchedBimonoidStarScopeWithPointUnitor` (the r20 U-round scope), so
the U3 run-commute consumers can uniformly consume it.  Note the generic form is genuinely OVER the shipped star
scope; the sibling embedding is a strict weakening kept only for interoperability with the U1 sibling. -/
theorem bunchedBimonoidDistantCommuteGenericLetterConvOverSibling (leftPad gap rightPad : Nat) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarScopeWithPointUnitor
      (CellExpr.vcomp
        (CellExpr.whiskerLeft (bunchedBimonoidAWordPow leftPad)
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen
            (bunchedBimonoidAWordPow (gap + (2 + rightPad)))))
        (CellExpr.whiskerLeft (bunchedBimonoidAWordPow (leftPad + (2 + gap)))
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow rightPad))))
      (CellExpr.vcomp
        (CellExpr.whiskerLeft (bunchedBimonoidAWordPow (leftPad + (2 + gap)))
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow rightPad)))
        (CellExpr.whiskerLeft (bunchedBimonoidAWordPow leftPad)
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen
            (bunchedBimonoidAWordPow (gap + (2 + rightPad)))))) :=
  bunchedBimonoidStarScopeEmbedsIntoPointUnitorSibling
    (bunchedBimonoidDistantCommuteGenericLetterConv leftPad gap rightPad)

/-! # =========================================================================================
    # G2.B — THE CONCRETE `sigmaAt`-FORM INSTANCES (the bill's literal shape, by rfl-transport)
    # =========================================================================================

★ At CONCRETE numerals the additive letters are DEFINITIONALLY the `sigmaAt` letters (the truncated subtraction
computes: `w - i - 2 = gap + (2 + rightPad)` etc. reduce to the same numeral), so each generic instance IS the
bill's literal `vcomp (sigmaAt w i) (sigmaAt w j) ~ vcomp (sigmaAt w j) (sigmaAt w i)` — fired at width 5 and 6.
The subtraction trap never enters the CORE (only this transport, which is `rfl`-defeq at numerals). -/

/-- ★★ **`(w, i, j) = (5, 0, 2)` over the sibling** — `vcomp (sigmaAt 5 0) (sigmaAt 5 2) ~ vcomp (sigmaAt 5 2)
(sigmaAt 5 0)`, the generic theorem at `(leftPad, gap, rightPad) = (0, 0, 1)` transported (defeq) to the `sigmaAt`
form.  Width 5, i = 0, j = 2 (`j = i + 2`, gap 0). -/
theorem bunchedBimonoidDistantCommuteSigmaAtFiveZeroTwoOverSibling :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarScopeWithPointUnitor
      (CellExpr.vcomp (bunchedBimonoidSigmaAt 5 0) (bunchedBimonoidSigmaAt 5 2))
      (CellExpr.vcomp (bunchedBimonoidSigmaAt 5 2) (bunchedBimonoidSigmaAt 5 0)) :=
  bunchedBimonoidDistantCommuteGenericLetterConvOverSibling 0 0 1

/-- ★★ **`(w, i, j) = (5, 0, 3)` over the sibling** — `vcomp (sigmaAt 5 0) (sigmaAt 5 3) ~ vcomp (sigmaAt 5 3)
(sigmaAt 5 0)`, the generic theorem at `(0, 1, 0)`.  Width 5, i = 0, j = 3 (gap 1, the first strictly-distant
pair). -/
theorem bunchedBimonoidDistantCommuteSigmaAtFiveZeroThreeOverSibling :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarScopeWithPointUnitor
      (CellExpr.vcomp (bunchedBimonoidSigmaAt 5 0) (bunchedBimonoidSigmaAt 5 3))
      (CellExpr.vcomp (bunchedBimonoidSigmaAt 5 3) (bunchedBimonoidSigmaAt 5 0)) :=
  bunchedBimonoidDistantCommuteGenericLetterConvOverSibling 0 1 0

/-- ★★ **`(w, i, j) = (5, 1, 3)` over the sibling** — `vcomp (sigmaAt 5 1) (sigmaAt 5 3) ~ vcomp (sigmaAt 5 3)
(sigmaAt 5 1)`, the generic theorem at `(1, 0, 0)`.  Width 5, i = 1 (non-zero left pad), j = 3. -/
theorem bunchedBimonoidDistantCommuteSigmaAtFiveOneThreeOverSibling :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarScopeWithPointUnitor
      (CellExpr.vcomp (bunchedBimonoidSigmaAt 5 1) (bunchedBimonoidSigmaAt 5 3))
      (CellExpr.vcomp (bunchedBimonoidSigmaAt 5 3) (bunchedBimonoidSigmaAt 5 1)) :=
  bunchedBimonoidDistantCommuteGenericLetterConvOverSibling 1 0 0

/-- ★★ **`(w, i, j) = (6, 1, 4)` over the sibling** — `vcomp (sigmaAt 6 1) (sigmaAt 6 4) ~ vcomp (sigmaAt 6 4)
(sigmaAt 6 1)`, the generic theorem at `(1, 1, 0)`.  Width 6, i = 1, j = 4 (both non-trivial pad and gap). -/
theorem bunchedBimonoidDistantCommuteSigmaAtSixOneFourOverSibling :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarScopeWithPointUnitor
      (CellExpr.vcomp (bunchedBimonoidSigmaAt 6 1) (bunchedBimonoidSigmaAt 6 4))
      (CellExpr.vcomp (bunchedBimonoidSigmaAt 6 4) (bunchedBimonoidSigmaAt 6 1)) :=
  bunchedBimonoidDistantCommuteGenericLetterConvOverSibling 1 1 0

/-! ## G2.B matrix-soundness pins (the endpoints share their permutation; width 5-6, rfl) -/

/-- The `(5, 0, 2)` endpoints share their `5 x 5` permutation (`rfl`): both orders swap strands 0-1 and 2-3. -/
theorem bunchedBimonoidDistantCommuteFiveZeroTwoMatrixShared :
    bunchedBimonoidEvalCell
        (CellExpr.vcomp (bunchedBimonoidSigmaAt 5 0) (bunchedBimonoidSigmaAt 5 2))
      = bunchedBimonoidEvalCell
        (CellExpr.vcomp (bunchedBimonoidSigmaAt 5 2) (bunchedBimonoidSigmaAt 5 0)) := rfl

/-- The `(5, 1, 3)` endpoints share their `5 x 5` permutation (`rfl`). -/
theorem bunchedBimonoidDistantCommuteFiveOneThreeMatrixShared :
    bunchedBimonoidEvalCell
        (CellExpr.vcomp (bunchedBimonoidSigmaAt 5 1) (bunchedBimonoidSigmaAt 5 3))
      = bunchedBimonoidEvalCell
        (CellExpr.vcomp (bunchedBimonoidSigmaAt 5 3) (bunchedBimonoidSigmaAt 5 1)) := rfl

/-- The `(6, 1, 4)` endpoints share their `6 x 6` permutation (`rfl`; the width-6 pin the r20 finding confirmed
fits the 4M-heartbeat budget). -/
theorem bunchedBimonoidDistantCommuteSixOneFourMatrixShared :
    bunchedBimonoidEvalCell
        (CellExpr.vcomp (bunchedBimonoidSigmaAt 6 1) (bunchedBimonoidSigmaAt 6 4))
      = bunchedBimonoidEvalCell
        (CellExpr.vcomp (bunchedBimonoidSigmaAt 6 4) (bunchedBimonoidSigmaAt 6 1)) := rfl

/-! ## G2 truth-probes (the interpreter, no heartbeat limit): distant pairs COMMUTE, adjacent do NOT -/

-- Distant pairs (j >= i + 2) commute — the delivered instances:
#eval decide ((bunchedBimonoidEvalCell (CellExpr.vcomp (bunchedBimonoidSigmaAt 5 0) (bunchedBimonoidSigmaAt 5 2))).entries
  = (bunchedBimonoidEvalCell (CellExpr.vcomp (bunchedBimonoidSigmaAt 5 2) (bunchedBimonoidSigmaAt 5 0))).entries) -- true
#eval decide ((bunchedBimonoidEvalCell (CellExpr.vcomp (bunchedBimonoidSigmaAt 5 0) (bunchedBimonoidSigmaAt 5 3))).entries
  = (bunchedBimonoidEvalCell (CellExpr.vcomp (bunchedBimonoidSigmaAt 5 3) (bunchedBimonoidSigmaAt 5 0))).entries) -- true
#eval decide ((bunchedBimonoidEvalCell (CellExpr.vcomp (bunchedBimonoidSigmaAt 6 1) (bunchedBimonoidSigmaAt 6 4))).entries
  = (bunchedBimonoidEvalCell (CellExpr.vcomp (bunchedBimonoidSigmaAt 6 4) (bunchedBimonoidSigmaAt 6 1))).entries) -- true
#eval decide ((bunchedBimonoidEvalCell (CellExpr.vcomp (bunchedBimonoidSigmaAt 7 1) (bunchedBimonoidSigmaAt 7 4))).entries
  = (bunchedBimonoidEvalCell (CellExpr.vcomp (bunchedBimonoidSigmaAt 7 4) (bunchedBimonoidSigmaAt 7 1))).entries) -- true (width 7, probe-only)

-- Adjacent pairs (j = i + 1) do NOT commute — the negative controls (must print false):
#eval decide ((bunchedBimonoidEvalCell (CellExpr.vcomp (bunchedBimonoidSigmaAt 5 0) (bunchedBimonoidSigmaAt 5 1))).entries
  = (bunchedBimonoidEvalCell (CellExpr.vcomp (bunchedBimonoidSigmaAt 5 1) (bunchedBimonoidSigmaAt 5 0))).entries) -- false
#eval decide ((bunchedBimonoidEvalCell (CellExpr.vcomp (bunchedBimonoidSigmaAt 6 2) (bunchedBimonoidSigmaAt 6 3))).entries
  = (bunchedBimonoidEvalCell (CellExpr.vcomp (bunchedBimonoidSigmaAt 6 3) (bunchedBimonoidSigmaAt 6 2))).entries) -- false

/-! # =========================================================================================
    # G2.C — THE HONESTY MARKERS (new markers per literal delivery only; owners byte-intact)
    # =========================================================================================
-/

/-- ★★★ **ESTABLISHED (G1+G2) — the FULLY GENERIC distant-commute is DELIVERED over the SHIPPED star scope.**
`= true` records `bunchedBimonoidDistantCommuteGenericLetterConv` (any pads `(leftPad, gap, rightPad)`:
`firstLetter . secondLetter ~ secondLetter . firstLetter` over `bunchedBimonoidStarCongruenceScope`), assembled
from the reusable dim-1 fold `bunchedBimonoidWordTripleFoldConv` (Brick A), the two padded-letter reshapes
(Bricks B, C, via `whiskerRightWhiskerCongr` / two `whiskerAssocLeft` firings), the two functorial folds
(Brick D), and the SINGLE `StrictAxiomRel.interchange sigma gapSigma` fire whiskered under `whiskerLeftCongr
(A^leftPad)`.  It REFUTES the r20 census "completeness-star fragment" denotation: the generic distant-commute
needs NO unitor, NO new row, and is STRONGER than the U2 sibling `(4, 0, 2)` (which it subsumes at `(0, 0, 0)`).
Machine-checks the printed literature (Savage (3.9): "the distant braid relation follows for free from the
interchange law"; Polygraphs (4.6)) at ARBITRARY width — a gap the formalized literature left (Mathlib/Coq/Agda
absorb the distant relation into strictification/coherence tactics; no named kernel-checked generic-width
`interchange |- s_i s_j = s_j s_i` exists).  Zero-axiom (per-decl `#assert_no_axioms` + independent
`#print axioms` in the twin); STRUCTURAL only. -/
def fxBunchedBimonoid_distantCommuteGenericAdditiveShipped : Bool := true

/-- ★★★ **ESTABLISHED (G2.B) — the concrete `sigmaAt`-form instances are DELIVERED at width 5 and 6.**  `= true`
records the four `sigmaAt`-form corollaries over the sibling — `(5, 0, 2)`, `(5, 0, 3)`, `(5, 1, 3)`, `(6, 1, 4)`
— each the generic theorem at the matching pads transported by `rfl`-defeq to the bill's literal
`vcomp (sigmaAt w i) (sigmaAt w j) ~ vcomp (sigmaAt w j) (sigmaAt w i)` form (the truncated subtraction computes at
numerals, so no general subtraction lemma is needed for the concrete cases).  Matrix-soundness pinned by `rfl` at
`(5, 0, 2)`, `(5, 1, 3)`, `(6, 1, 4)`; the interpreter truth-probes confirm the discrimination — distant pairs
(`j >= i + 2`) commute, the adjacent negative controls `(5, 0, 1)` / `(6, 2, 3)` do NOT.  Zero-axiom (per-decl
`#assert_no_axioms` + independent `#print axioms` in the twin). -/
def fxBunchedBimonoid_distantCommuteGenericSigmaAtInstancesShipped : Bool := true

/-- ★ **THE ADJACENT BRAID + THE permWord LIFT STAY OPEN — the honest r21 census, no fabricated flip.**
`= false` records what the generic distant-commute does NOT reach: (1) the ADJACENT braid atom
`sigmaAt w i . sigmaAt w (i+1) . sigmaAt w i ~ sigmaAt w (i+1) . sigmaAt w i . sigmaAt w (i+1)` (Coxeter (3.8),
Savage) — the GENUINE residual interchange canNOT reach (its width-4 triple-vcomp endpoint `rfl` exceeds even
4M heartbeats, r20 finding: a COMPUTE wall, not a soundness gap); (2) the TRAILING-BOUNDARY reshape
`boundaryTarget (sigmaAt w k) ~ aWordPow w` + the first `permWord`-fold lift rung
(`permWord (front ++ back) w ~ vcomp (permWord front w) (permWord back w)`), lifting the `vcomp`-form generic
theorem to the `permWord [..] w` fold — the r22 rung whose dim-1 leg is exactly the shipped
`bunchedBimonoidWordTripleFoldConv` + `bunchedBimonoidSigmaAtBoundaryReshapeConv`; (3) the CONV folds
(`swapCommutesRun*Conv` / `combInsertConv` / `combNormalizeFormConv` / `recCombConv`) + the Brauer `combCanonicity`
per-file clone (census item 5).  The four star owners stay `= false` byte-intact; the shipped `StrictAxiomRel` +
star scope are untouched.  No fabricated star flip. -/
def fxBunchedBimonoid_distantCommuteGenericBraidAndPermWordLiftStillOpen : Bool := false

end FX1Poly.Polygraph.Omega
