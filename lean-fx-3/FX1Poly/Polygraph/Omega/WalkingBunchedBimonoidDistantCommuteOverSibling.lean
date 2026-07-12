import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidIdentityPointUnitor
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCoxeterUniqueness

/-! # Polygraph/Omega/WalkingBunchedBimonoidDistantCommuteOverSibling — the r17 decisive wall instance CLOSED
over the U1 sibling: the distant-commute atom `vcomp (sigmaAt 4 0) (sigmaAt 4 2) ~ vcomp (sigmaAt 4 2)
(sigmaAt 4 0)`, built from the r19 landed rows + the U1 width-0 identity-point unitor + the r9 Godement
interchange (WP-PROP r20, U2)

★ **THE EXACT r17 WALL INSTANCE, NOW CLOSED.**  The r17 `RunCommuteConv` (R3) named the residual precisely:
"the fixed distant pair `sigmaAt 4 0` / `sigmaAt 4 2` already differs from the r9
`bunchedBimonoidDistantSwapLeftLeg` (which the Godement `interchange` DOES relate) by exactly the
identity-whisker unitor `whiskerLeft (a^0 = id point) _ ~ _`, so the r9
`bunchedBimonoidDistantSwapCommuteViaInterchange` (fixed-width `s_1 s_3 = s_3 s_1`) canNOT be re-padded to
arbitrary `(w, i, j)` without these coherences."  The r19 substrate round LANDED the associator + whisker
left/right commute; U1 shipped the sole remaining brick — the width-0 identity-point unitor — as an ADDITIVE
sibling presentation.  This file spends exactly that brick to close the decisive instance the wall named.

## The reshape (the two `sigmaAt` letters meet the r9 legs)

The position-indexed letter `bunchedBimonoidSigmaAt w k = whiskerLeft (a^k) (whiskerRight sigma (a^(w-k-2)))`
carries an `a^0 = id point` whisker pad at each edge (`bunchedBimonoidAWordPow 0 = bunchedBimonoidIdOne =
CellExpr.id bunchedBimonoidPoint`, by defeq).  The two edge letters reshape to the r9 distant-swap factors over
the sibling scope `bunchedBimonoidStarScopeWithPointUnitor`:

  * **`sigmaAt 4 0 ~ sigma |> a.a`** — the position-0 letter `whiskerLeft (a^0 = id point) (sigma |> a^2)` sheds
    its identity-point LEFT whisker via the U1 `bunchedBimonoidSigmaAtZeroUnitorConv`, then `a^2` reshapes to the
    two-strand word `a.a` via the r15 `bunchedBimonoidAWordPowTwoIsAaWordConv` under `whiskerRightWhiskerCongr`.
  * **`sigmaAt 4 2 ~ a.a <| sigma`** — the position-2 letter `whiskerLeft (a^2) (whiskerRight sigma (a^0 = id
    point))` sheds its identity-point RIGHT whisker via the U1 `bunchedBimonoidRightIdPointUnitorConv` under
    `whiskerLeftCongr`, then `a^2` reshapes to `a.a` via `bunchedBimonoidAWordPowTwoIsAaWordConv` under
    `whiskerLeftWhiskerCongr`.

Then the r9 `bunchedBimonoidDistantSwapCommuteViaInterchange` (ONE Godement `interchange` fire at
`alpha = beta = sigma`, embedded into the sibling by `bunchedBimonoidStarScopeEmbedsIntoPointUnitorSibling`)
identifies the two orders, and the reshapes run backwards.  Non-vacuous: the two endpoints are syntactically
distinct `CellExpr` trees (the leftmost `vcomp` factor's position differs) that share their `4 x 4` permutation
matrix (`bunchedBimonoidDistantSwapCommuteFourZeroTwoMatrixShared`).

## The honest scope (what this does NOT deliver)

This closes the width-4 edge-anchored atom `(w, i, j) = (4, 0, 2)` — the exact instance the r17 wall named.  The
FULLY generic `(w, i, j)` distant-commute (`i + 2 <= j` at arbitrary width, with a middle gap block `a^(j-i-2)`)
needs the general block Godement interchange with arbitrary left/middle/right padding — a fragment of the
unproven completeness star, NOT this width-4 fixed-block instance.  The shipped `StrictAxiomRel` and the four
star owners stay byte-intact; the r17 `fxBunchedBimonoid_runCommuteConvGatedOnWhiskerAssociatorAndUnitors`
stays `= false` (the SHIPPED star scope still lacks the unitor — the closure is over the additive sibling).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

/-! The distant-commute endpoint matrix `rfl` pin at width 4 exceeds the default heartbeat budget; the raise is a
compute allowance only, every proof term stays congruence-constructor plumbing, axiom-free (uniform with the
r9 `CoxeterUniqueness` / r17 `RunCommuteConv`). -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # U2.A — THE TWO EDGE-LETTER RESHAPES (the U1 unitor spent on the `sigmaAt` edge pads)
    # =========================================================================================
-/

/-- ★ **The leading-pair letter reshape — `sigmaAt 4 0 ~ sigma |> a.a` over the sibling.**  The position-0 letter
`whiskerLeft (a^0 = id point) (whiskerRight sigma (a^2))` sheds its identity-point LEFT whisker via the U1
`bunchedBimonoidSigmaAtZeroUnitorConv 4`, then the whisker `a^2` reshapes to the two-strand word `a.a` via the
r15 `bunchedBimonoidAWordPowTwoIsAaWordConv` (embedded into the sibling) under `whiskerRightWhiskerCongr`.  The
first factor of the r9 `bunchedBimonoidDistantSwapLeftLeg`. -/
theorem bunchedBimonoidSigmaAtLeadingPairReshapeConv :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarScopeWithPointUnitor
      (bunchedBimonoidSigmaAt 4 0)
      (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAaWord) :=
  SaturatedConvOverWithId.trans
    (bunchedBimonoidSigmaAtZeroUnitorConv 4)
    (SaturatedConvOverWithId.whiskerRightWhiskerCongr bunchedBimonoidAddSigmaGen
      (bunchedBimonoidStarScopeEmbedsIntoPointUnitorSibling bunchedBimonoidAWordPowTwoIsAaWordConv))

/-- ★ **The trailing-pair letter reshape — `sigmaAt 4 2 ~ a.a <| sigma` over the sibling.**  The position-2
letter `whiskerLeft (a^2) (whiskerRight sigma (a^0 = id point))` sheds its identity-point RIGHT whisker via the
U1 `bunchedBimonoidRightIdPointUnitorConv bunchedBimonoidAddSigmaGen` under `whiskerLeftCongr`, then the whisker
`a^2` reshapes to `a.a` via `bunchedBimonoidAWordPowTwoIsAaWordConv` under `whiskerLeftWhiskerCongr`.  The second
factor of the r9 `bunchedBimonoidDistantSwapLeftLeg`. -/
theorem bunchedBimonoidSigmaAtTrailingPairReshapeConv :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarScopeWithPointUnitor
      (bunchedBimonoidSigmaAt 4 2)
      (CellExpr.whiskerLeft bunchedBimonoidAaWord bunchedBimonoidAddSigmaGen) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.whiskerLeftCongr (bunchedBimonoidAWordPow 2)
      (bunchedBimonoidRightIdPointUnitorConv bunchedBimonoidAddSigmaGen))
    (SaturatedConvOverWithId.whiskerLeftWhiskerCongr bunchedBimonoidAddSigmaGen
      (bunchedBimonoidStarScopeEmbedsIntoPointUnitorSibling bunchedBimonoidAWordPowTwoIsAaWordConv))

/-! # =========================================================================================
    # U2.B — THE FLAGSHIP DISTANT-COMMUTE ATOM OVER THE SIBLING (the r17 wall instance closed)
    # =========================================================================================
-/

/-- ★★★ **THE DISTANT-COMMUTE ATOM `(4, 0, 2)` OVER THE SIBLING — the r17 wall instance CLOSED.**
`vcomp (sigmaAt 4 0) (sigmaAt 4 2) ~ vcomp (sigmaAt 4 2) (sigmaAt 4 0)` over
`bunchedBimonoidStarScopeWithPointUnitor`: the two edge letters reshape (U2.A) to the r9
`bunchedBimonoidDistantSwapLeftLeg` / `...RightLeg`, the r9
`bunchedBimonoidDistantSwapCommuteViaInterchange` (one Godement `interchange` fire, embedded into the sibling)
identifies the orders, and the reshapes run backwards.  This is the EXACT instance the r17
`RunCommuteConv` (R3) named as gated "by exactly the identity-whisker unitor" — now closed, spending the U1
width-0 identity-point unitor on the `a^0 = id point` edge pads (which the r19 assoc/commute rows do NOT supply).
Non-vacuous: the two endpoints are syntactically distinct trees sharing a `4 x 4` matrix
(`...FourZeroTwoMatrixShared`). -/
theorem bunchedBimonoidDistantSwapCommuteFourZeroTwoOverSibling :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarScopeWithPointUnitor
      (CellExpr.vcomp (bunchedBimonoidSigmaAt 4 0) (bunchedBimonoidSigmaAt 4 2))
      (CellExpr.vcomp (bunchedBimonoidSigmaAt 4 2) (bunchedBimonoidSigmaAt 4 0)) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.vcompCongrLeft (bunchedBimonoidSigmaAt 4 2)
        bunchedBimonoidSigmaAtLeadingPairReshapeConv)
      (SaturatedConvOverWithId.vcompCongrRight
        (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAaWord)
        bunchedBimonoidSigmaAtTrailingPairReshapeConv))
    (SaturatedConvOverWithId.trans
      (bunchedBimonoidStarScopeEmbedsIntoPointUnitorSibling
        bunchedBimonoidDistantSwapCommuteViaInterchange)
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrLeft
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAaWord)
          (SaturatedConvOverWithId.symm bunchedBimonoidSigmaAtTrailingPairReshapeConv))
        (SaturatedConvOverWithId.vcompCongrRight (bunchedBimonoidSigmaAt 4 2)
          (SaturatedConvOverWithId.symm bunchedBimonoidSigmaAtLeadingPairReshapeConv))))

/-- ★ **The distant-commute endpoints share their `4 x 4` matrix (`rfl`)** — both
`vcomp (sigmaAt 4 0) (sigmaAt 4 2)` and `vcomp (sigmaAt 4 2) (sigmaAt 4 0)` evaluate to the same permutation
(swap strands 0-1 and 2-3), so the sibling convertibility above genuinely relates two representatives of one
map (the necessary condition, machine-pinned; matches the r17
`bunchedBimonoidSigmaAtDistantCommuteMatrixSharedFourZeroTwo`). -/
theorem bunchedBimonoidDistantSwapCommuteFourZeroTwoMatrixShared :
    bunchedBimonoidEvalCell
        (CellExpr.vcomp (bunchedBimonoidSigmaAt 4 0) (bunchedBimonoidSigmaAt 4 2))
      = bunchedBimonoidEvalCell
        (CellExpr.vcomp (bunchedBimonoidSigmaAt 4 2) (bunchedBimonoidSigmaAt 4 0)) := rfl

/-! ## The U2 honesty markers -/

/-- ★★★ **ESTABLISHED (U2) — the r17 decisive distant-commute wall instance is CLOSED over the U1 sibling.**
`= true` records `bunchedBimonoidDistantSwapCommuteFourZeroTwoOverSibling`: the atom
`vcomp (sigmaAt 4 0) (sigmaAt 4 2) ~ vcomp (sigmaAt 4 2) (sigmaAt 4 0)` over
`bunchedBimonoidStarScopeWithPointUnitor`, built from the two edge-letter reshapes
(`bunchedBimonoidSigmaAt{Leading,Trailing}PairReshapeConv`, which spend the U1 width-0 identity-point unitor on
the `a^0 = id point` edge pads) + the r9 Godement `interchange` embedded into the sibling.  This is the EXACT
instance the r17 `RunCommuteConv` R3 marker named as gated "by exactly the identity-whisker unitor".
Non-vacuous — the endpoints share a `4 x 4` matrix (`...FourZeroTwoMatrixShared`) but are syntactically distinct.
Zero-axiom (per-decl `#assert_no_axioms` + independent `#print axioms` in the twin). -/
def fxBunchedBimonoid_distantCommuteAtomOverSiblingShipped : Bool := true

/-- ★ **THE FULLY-GENERIC `(w, i, j)` DISTANT-COMMUTE STAYS WALLED — no flip.**  `= false` records that the
generic atom (`vcomp (sigmaAt w i) (sigmaAt w j) ~ vcomp (sigmaAt w j) (sigmaAt w i)` for `i + 2 <= j` at
arbitrary width, with a middle gap block `a^(j-i-2)`) is NOT delivered: the width-4 edge-anchored `(4, 0, 2)`
instance closes via the r9 fixed-block interchange, but arbitrary `(w, i, j)` needs the general block Godement
interchange with arbitrary left / middle / right padding — a fragment of the unproven completeness star, not the
r9 fixed pair.  The r17 `fxBunchedBimonoid_runCommuteConvGatedOnWhiskerAssociatorAndUnitors` (shipped-scope
marker) stays `= false` byte-intact; the four star owners stay `= false`.  No fabricated flip. -/
def fxBunchedBimonoid_distantCommuteGenericPositionStillWalled : Bool := false

end FX1Poly.Polygraph.Omega
