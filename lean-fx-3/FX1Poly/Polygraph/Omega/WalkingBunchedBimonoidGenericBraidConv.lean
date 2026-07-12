import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidRunBelowCommuteConv

/-! # Polygraph/Omega/WalkingBunchedBimonoidGenericBraidConv — the generic-width adjacent-braid CONV atom
`sigmaAt w i ; sigmaAt w (i+1) ; sigmaAt w i ~ sigmaAt w (i+1) ; sigmaAt w i ; sigmaAt w (i+1)`, DERIVED
term-mode from the axiomatic width-3 Yang-Baxter hexagon row over the SHIPPED star scope (WP-PROP r24, THE BRAID
DECISION, branch (a))

★ **THE ADJACENT BRAID IS DERIVABLE — NO NEW ENGINE ROW.**  The r20/r21 census walled the adjacent Coxeter
braid `s_i s_{i+1} s_i = s_{i+1} s_i s_{i+1}` as "compute-walled": its width-4 triple-`vcomp` endpoint `rfl`
exceeds even the 4M-heartbeat budget (a KERNEL-`rfl` wall on wide endpoints).  This file shows that wall was on
the WRONG proof strategy.  The braid is NOT proven by evaluating the two endpoints to matrices; it is DERIVED as
term-mode congruence plumbing that whisker-EMBEDS the AXIOMATIC width-3 Yang-Baxter row
(`BunchedBimonoidHexagonRow.yangBaxter`, already shipped r4) into arbitrary padding.  No wide kernel `rfl` ever
fires — every step is a `StrictAxiomRel` / hexagon-row firing under the one-hole congruences.

The web-literature adjudication (Coxeter minimality via `B_n` infiniteness; Joyal-Street "naturality + hexagons"
for Yang-Baxter; Matsumoto-Tits braid-move connectivity; Mathlib `CoxeterMatrix.Aₙ` encoding) is respected: the
adjacent braid is an INDEPENDENT presentation row, NOT derivable from involution + distant-commutation +
interchange.  Here the WIDTH-3 braid IS a presentation row — the axiomatic `yangBaxter` hexagon
(`Omega/WalkingBunchedBimonoidHexagon.lean`) — and this file lifts that fixed row to GENERIC width by whisker
embedding, exactly as the distant-commute (Coxeter (3.9)) lifts the interchange row.  The genuine content is the
LIFT, not a fresh row: `StrictAxioms.lean` stays CLOSED (the ENGINE LAW is untriggered).

## The reshape skeleton (the OVERLAP handled; the pad-nesting trap sidestepped)

`sigmaAt w k = A^k <| (sigma |> A^(w - k - 2))`.  The three braid letters overlap at position `i+1`, so
distant-commute is irrelevant.  Each letter is reshaped to a COMMON-PAD width-3-core form
`A^i <| (CORE |> A^(w-i-3))`, `CORE = sigmaWhiskerRight` (position `i`) / `sigmaWhiskerLeft` (position `i+1`):

  * **position `i`** (`sigmaAtBraidReshapeRightConv`): `A^(w-i-2) = A . A^(w-i-3)` definitionally once
    `w-i-2 = (w-i-3)+1` is exposed (the one arithmetic fact, threaded propext-clean); one `whiskerAssocRight`.
  * **position `i+1`** (`sigmaAtBraidReshapeLeftConv`): `A^(i+1)` is head-cons, so the naive `whiskerAssocLeft`
    nests the pad the WRONG way; the SNOC reshape `A^(i+1) ~ A^i . A` (from `aWordPowSplitConv` +
    `aWordPowOneIsGenConv`) is required, then `whiskerAssocLeft`, then `symm whiskerLeftRightCommute`.

Then the three whiskered letters COLLAPSE (two firings of the shipped `bunchedBimonoidWhiskerOverVcompConv`) into
one whiskered Yang-Baxter leg, the `yangBaxter` row fires under `whiskerLeftCongr` / `whiskerRightCongr`, and the
expansion reshapes back to the mirror triple.

## The honest scope (NO star flip)

The braid atom being derivable does NOT flip any star owner.  The four star owners (StarAssembly / RiffleAssembly
/ CollisionCanonForm / CoxeterUniqueness) stay `= false` byte-intact — the fold chain F2-F4 + the owner assembly
must actually land (the CARRY unblock uses this braid atom + the shipped
`bunchedBimonoidSigmaAtGenericDistantCommuteConv`, but combInsertConv also needs the r15 append-reshape part (b),
NOT delivered here).  The residual marker
`fxBunchedBimonoid_distantCommuteGenericBraidAndPermWordLiftStillOpen` stays `= false` byte-intact; this file
posts a FRESH delivery marker for the braid atom alone.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

/-! The width-3/4 braid endpoint matrix `rfl` pins evaluate a 3-fold `matMul` whose `whnf` exceeds the default
heartbeat budget; the raise is a compute allowance only — every DERIVATION term stays congruence-constructor
plumbing (axiom-free, no wide kernel `rfl`), and the pins stay `Eq.refl`. -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # A0 — THE PROPEXT-CLEAN ARITHMETIC BACKBONE (the one truncated-subtraction fact)
    # =========================================================================================

★ The ONLY non-definitional arithmetic the braid needs: under `k + 3 <= w`, `w - k - 2 = (w - k - 3) + 1`.
Re-derived STRUCTURAL over a double recursion on `(positionK, wordWidth)` via `Nat.succ_sub_succ` +
`Nat.le_of_succ_le_succ` (the core `Nat.sub` order lemmas leak propext; this structural peel does not — the
identical technique as `ConvFold`'s `commuteHighEq`). -/

private theorem bunchedBimonoidBraidRestSuccConvFold :
    (positionK wordWidth : Nat) → positionK + 3 ≤ wordWidth →
    wordWidth - positionK - 2 = (wordWidth - positionK - 3) + 1
  | 0, 0, hLe => absurd hLe (by decide)
  | 0, 1, hLe => absurd hLe (by decide)
  | 0, 2, hLe => absurd hLe (by decide)
  | 0, _wordWidth + 3, _ => rfl
  | _positionK + 1, 0, hLe => absurd hLe (Nat.not_succ_le_zero _)
  | positionK + 1, wordWidth + 1, hLe => by
      rw [Nat.succ_sub_succ]
      exact bunchedBimonoidBraidRestSuccConvFold positionK wordWidth (Nat.le_of_succ_le_succ hLe)

/-! # =========================================================================================
    # A1 — THE COMMON-PAD WIDTH-3-CORE LETTERS
    # =========================================================================================
-/

/-- ★ The **right-core braid letter** `A^leftPad <| ((sigma |> A) |> A^rightPad)` — the width-3 core
`sigmaWhiskerRight` (`s_1` of the 3-strand core) whiskered by `leftPad` on the left and `rightPad` on the right.
The common-pad form of `sigmaAt w i` (position `i`, sigma on the LEFT of the overlapping triple). -/
def bunchedBimonoidBraidCoreLetterRight (leftPad rightPad : Nat) : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerLeft (bunchedBimonoidAWordPow leftPad)
    (CellExpr.whiskerRight bunchedBimonoidSigmaWhiskerRight (bunchedBimonoidAWordPow rightPad))

/-- ★ The **left-core braid letter** `A^leftPad <| ((A <| sigma) |> A^rightPad)` — the width-3 core
`sigmaWhiskerLeft` (`s_2` of the 3-strand core) whiskered by the same pads.  The common-pad form of
`sigmaAt w (i+1)` (position `i+1`, sigma on the RIGHT of the overlapping triple). -/
def bunchedBimonoidBraidCoreLetterLeft (leftPad rightPad : Nat) : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerLeft (bunchedBimonoidAWordPow leftPad)
    (CellExpr.whiskerRight bunchedBimonoidSigmaWhiskerLeft (bunchedBimonoidAWordPow rightPad))

/-! # =========================================================================================
    # A2 — THE DIM-1 SNOC RESHAPE PRIMITIVE (`A^1 ~ A`)
    # =========================================================================================
-/

/-- ★ **`A^1 ~ A`** — the one-strand word IS the bare generator, over the star scope.  `A^1 = A . id point`
reshapes to `A` by `vcompUnitRight A` (stripping the trailing identity, `id point = id (boundaryTarget A)`).  The
base the position-`i+1` snoc reshape needs (`A^(i+1) ~ A^i . A`). -/
theorem bunchedBimonoidAWordPowOneIsGenConv :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidAWordPow 1) bunchedBimonoidAdditiveGen :=
  bunchedBimonoidStrictAxiomEmbedsIntoStarScope (StrictAxiomRel.vcompUnitRight bunchedBimonoidAdditiveGen)

/-- ★ **THE SNOC RESHAPE `A^(k+1) ~ A^k . A`** — move the head strand of the head-cons word `A^(k+1)` to the
TAIL, over the star scope: `aWordPowSplitConv k 1` splits `A^(k+1) ~ A^k . A^1`, then `vcompCongrRight` fires
`aWordPowOneIsGenConv` on the trailing `A^1`.  The reshape the position-`i+1` letter needs (the naive
head-cons `whiskerAssocLeft` nests the pad the wrong way). -/
theorem bunchedBimonoidAWordPowSnocConv (segmentK : Nat) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidAWordPow (segmentK + 1))
      (CellExpr.vcomp (bunchedBimonoidAWordPow segmentK) bunchedBimonoidAdditiveGen) :=
  SaturatedConvOverWithId.trans
    (bunchedBimonoidAWordPowSplitConv segmentK 1)
    (SaturatedConvOverWithId.vcompCongrRight (bunchedBimonoidAWordPow segmentK)
      bunchedBimonoidAWordPowOneIsGenConv)

/-! # =========================================================================================
    # A3 — THE PER-LETTER RESHAPES TO COMMON-PAD CORE FORM (pure, pad-parameterized)
    # =========================================================================================
-/

/-- ★★ **THE RIGHT-LETTER RESHAPE (pure).**  The `sigmaAt`-shaped cell at a right-pad of `rightRest + 1`
converts, over the star scope, to the right-core letter: one `whiskerAssocRight` (a `StrictAxiomRel` row)
under `whiskerLeftCongr (A^leftPad)`, using `A^(rightRest+1) = A . A^rightRest` definitionally. -/
theorem bunchedBimonoidBraidReshapeRightPure (leftPad rightRest : Nat) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow leftPad)
        (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow (rightRest + 1))))
      (bunchedBimonoidBraidCoreLetterRight leftPad rightRest) :=
  SaturatedConvOverWithId.whiskerLeftCongr (bunchedBimonoidAWordPow leftPad)
    (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
      (StrictAxiomRel.whiskerAssocRight bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen
        (bunchedBimonoidAWordPow rightRest)))

/-- ★★ **THE LEFT-LETTER RESHAPE (pure).**  The `sigmaAt`-shaped cell at a left-pad of `leftPad + 1` converts,
over the star scope, to the left-core letter: the SNOC reshape `A^(leftPad+1) ~ A^leftPad . A` under
`whiskerLeftWhiskerCongr`, then `whiskerAssocLeft`, then `symm whiskerLeftRightCommute` under
`whiskerLeftCongr (A^leftPad)`. -/
theorem bunchedBimonoidBraidReshapeLeftPure (leftPad rightRest : Nat) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow (leftPad + 1))
        (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow rightRest)))
      (bunchedBimonoidBraidCoreLetterLeft leftPad rightRest) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.whiskerLeftWhiskerCongr
      (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow rightRest))
      (bunchedBimonoidAWordPowSnocConv leftPad))
    (SaturatedConvOverWithId.trans
      (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
        (StrictAxiomRel.whiskerAssocLeft (bunchedBimonoidAWordPow leftPad) bunchedBimonoidAdditiveGen
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow rightRest))))
      (SaturatedConvOverWithId.whiskerLeftCongr (bunchedBimonoidAWordPow leftPad)
        (SaturatedConvOverWithId.symm
          (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
            (StrictAxiomRel.whiskerLeftRightCommute bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen
              (bunchedBimonoidAWordPow rightRest))))))

/-! # =========================================================================================
    # A4 — THE TRIPLE COLLAPSE + THE YANG-BAXTER ATOM + THE CORE BRAID
    # =========================================================================================
-/

/-- ★★ **THE TRIPLE COLLAPSE.**  A whiskered triple-`vcomp` core collapses into a `vcomp` of three whiskered
letters, over the star scope, by two firings of the shipped `bunchedBimonoidWhiskerOverVcompConv`:

  `L <| ((cellL . cellM . cellN) |> R) ~ (L <| (cellL |> R)) . (L <| (cellM |> R)) . (L <| (cellN |> R))`.

The whisker distributes over the (left-associated) inner triple — the collapse the braid needs to fold the three
reshaped letters into one whiskered Yang-Baxter leg (and to expand back). -/
theorem bunchedBimonoidBraidTripleCollapse (leftWhisk rightWhisk : CellExpr bunchedBimonoidOmegaComputad 1)
    (cellL cellM cellN : CellExpr bunchedBimonoidOmegaComputad 2) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft leftWhisk
        (CellExpr.whiskerRight (CellExpr.vcomp (CellExpr.vcomp cellL cellM) cellN) rightWhisk))
      (CellExpr.vcomp
        (CellExpr.vcomp (CellExpr.whiskerLeft leftWhisk (CellExpr.whiskerRight cellL rightWhisk))
          (CellExpr.whiskerLeft leftWhisk (CellExpr.whiskerRight cellM rightWhisk)))
        (CellExpr.whiskerLeft leftWhisk (CellExpr.whiskerRight cellN rightWhisk))) :=
  SaturatedConvOverWithId.trans
    (bunchedBimonoidWhiskerOverVcompConv leftWhisk rightWhisk (CellExpr.vcomp cellL cellM) cellN)
    (SaturatedConvOverWithId.vcompCongrLeft
      (CellExpr.whiskerLeft leftWhisk (CellExpr.whiskerRight cellN rightWhisk))
      (bunchedBimonoidWhiskerOverVcompConv leftWhisk rightWhisk cellL cellM))

/-- ★★ **THE YANG-BAXTER ATOM (whiskered).**  The width-3 axiomatic Yang-Baxter row
(`BunchedBimonoidHexagonRow.yangBaxter`, `s_1 s_2 s_1 ~ s_2 s_1 s_2`) fires under an arbitrary pad
`leftWhisk <| (_ |> rightWhisk)`:

  `leftWhisk <| (YangBaxterLeftLeg |> rightWhisk) ~ leftWhisk <| (YangBaxterRightLeg |> rightWhisk)`.

`whiskerLeftCongr` and `whiskerRightCongr` lift the fixed hexagon row (embedded by
`bunchedBimonoidHexagonRowEmbedsIntoStarScope`) to the padded core.  THE single genuine content — no matrix
evaluation, no wide kernel `rfl`. -/
theorem bunchedBimonoidBraidAtomConv (leftWhisk rightWhisk : CellExpr bunchedBimonoidOmegaComputad 1) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft leftWhisk
        (CellExpr.whiskerRight bunchedBimonoidYangBaxterLeftLeg rightWhisk))
      (CellExpr.whiskerLeft leftWhisk
        (CellExpr.whiskerRight bunchedBimonoidYangBaxterRightLeg rightWhisk)) :=
  SaturatedConvOverWithId.whiskerLeftCongr leftWhisk
    (SaturatedConvOverWithId.whiskerRightCongr rightWhisk
      (bunchedBimonoidHexagonRowEmbedsIntoStarScope BunchedBimonoidHexagonRow.yangBaxter))

/-- ★★★ **THE CORE BRAID — `cR ; cL ; cR ~ cL ; cR ; cL` at arbitrary pads.**  The braid on the common-pad core
letters (right-core `cR`, left-core `cL`) over the star scope: collapse both triples into whiskered Yang-Baxter
legs, fire the atom, expand back.  The three sigma-word letters share exactly ONE overlapping strand, so this is
the genuine Coxeter braid, DERIVED — never a matrix `rfl`. -/
theorem bunchedBimonoidBraidCoreConv (leftPad rightPad : Nat) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp
        (CellExpr.vcomp (bunchedBimonoidBraidCoreLetterRight leftPad rightPad)
          (bunchedBimonoidBraidCoreLetterLeft leftPad rightPad))
        (bunchedBimonoidBraidCoreLetterRight leftPad rightPad))
      (CellExpr.vcomp
        (CellExpr.vcomp (bunchedBimonoidBraidCoreLetterLeft leftPad rightPad)
          (bunchedBimonoidBraidCoreLetterRight leftPad rightPad))
        (bunchedBimonoidBraidCoreLetterLeft leftPad rightPad)) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.symm
      (bunchedBimonoidBraidTripleCollapse (bunchedBimonoidAWordPow leftPad) (bunchedBimonoidAWordPow rightPad)
        bunchedBimonoidSigmaWhiskerRight bunchedBimonoidSigmaWhiskerLeft bunchedBimonoidSigmaWhiskerRight))
    (SaturatedConvOverWithId.trans
      (bunchedBimonoidBraidAtomConv (bunchedBimonoidAWordPow leftPad) (bunchedBimonoidAWordPow rightPad))
      (bunchedBimonoidBraidTripleCollapse (bunchedBimonoidAWordPow leftPad) (bunchedBimonoidAWordPow rightPad)
        bunchedBimonoidSigmaWhiskerLeft bunchedBimonoidSigmaWhiskerRight bunchedBimonoidSigmaWhiskerLeft))

/-! # =========================================================================================
    # A5 — THE sigmaAt-CONNECTION (the arithmetic threaded HERE, once)
    # =========================================================================================
-/

/-- ★★ **`sigmaAt w k ~ right-core letter`** (position `k`, under `k + 3 <= w`).  The letter's `sigmaAt` pad
`A^(w-k-2)` is reshaped to `A^((w-k-3)+1)` by the one arithmetic fact `bunchedBimonoidBraidRestSuccConvFold`,
after which `bunchedBimonoidBraidReshapeRightPure` closes it. -/
theorem bunchedBimonoidSigmaAtBraidReshapeRightConv (wordWidth positionK : Nat)
    (inRange : positionK + 3 ≤ wordWidth) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidSigmaAt wordWidth positionK)
      (bunchedBimonoidBraidCoreLetterRight positionK (wordWidth - positionK - 3)) := by
  show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow positionK)
        (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen
          (bunchedBimonoidAWordPow (wordWidth - positionK - 2))))
      (bunchedBimonoidBraidCoreLetterRight positionK (wordWidth - positionK - 3))
  rw [bunchedBimonoidBraidRestSuccConvFold positionK wordWidth inRange]
  exact bunchedBimonoidBraidReshapeRightPure positionK (wordWidth - positionK - 3)

/-- ★★ **`sigmaAt w (k+1) ~ left-core letter`** (position `k+1`).  The letter's `sigmaAt` pad
`A^(w-(k+1)-2)` is DEFINITIONALLY `A^(w-k-3)` (both `pred^3 (w-k)`), so no arithmetic rewrite is needed;
`bunchedBimonoidBraidReshapeLeftPure` closes it directly. -/
theorem bunchedBimonoidSigmaAtBraidReshapeLeftConv (wordWidth positionK : Nat) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidSigmaAt wordWidth (positionK + 1))
      (bunchedBimonoidBraidCoreLetterLeft positionK (wordWidth - positionK - 3)) :=
  bunchedBimonoidBraidReshapeLeftPure positionK (wordWidth - positionK - 3)

/-! # =========================================================================================
    # A6 — THE TRIPLE-RESHAPE CONGRUENCE LEGS + THE GENERIC-WIDTH ADJACENT-BRAID CONV ATOM
    # =========================================================================================
-/

/-- ★★ **THE LEFT-SIDE TRIPLE RESHAPE.**  The `sigmaAt` braid triple `s_i ; s_{i+1} ; s_i` converts, over the
star scope, to the common-pad core triple `cR ; cL ; cR` by three per-letter reshapes
(`sigmaAtBraidReshape{Right,Left}Conv`) threaded under `vcompCongrLeft` / `vcompCongrRight`. -/
theorem bunchedBimonoidBraidTripleReshapeLeftSide (wordWidth positionK : Nat)
    (inRange : positionK + 3 ≤ wordWidth) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp
        (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth positionK)
          (bunchedBimonoidSigmaAt wordWidth (positionK + 1)))
        (bunchedBimonoidSigmaAt wordWidth positionK))
      (CellExpr.vcomp
        (CellExpr.vcomp (bunchedBimonoidBraidCoreLetterRight positionK (wordWidth - positionK - 3))
          (bunchedBimonoidBraidCoreLetterLeft positionK (wordWidth - positionK - 3)))
        (bunchedBimonoidBraidCoreLetterRight positionK (wordWidth - positionK - 3))) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrRight
      (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth positionK)
        (bunchedBimonoidSigmaAt wordWidth (positionK + 1)))
      (bunchedBimonoidSigmaAtBraidReshapeRightConv wordWidth positionK inRange))
    (SaturatedConvOverWithId.vcompCongrLeft
      (bunchedBimonoidBraidCoreLetterRight positionK (wordWidth - positionK - 3))
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrLeft (bunchedBimonoidSigmaAt wordWidth (positionK + 1))
          (bunchedBimonoidSigmaAtBraidReshapeRightConv wordWidth positionK inRange))
        (SaturatedConvOverWithId.vcompCongrRight
          (bunchedBimonoidBraidCoreLetterRight positionK (wordWidth - positionK - 3))
          (bunchedBimonoidSigmaAtBraidReshapeLeftConv wordWidth positionK))))

/-- ★★ **THE RIGHT-SIDE TRIPLE RESHAPE.**  The `sigmaAt` braid mirror triple `s_{i+1} ; s_i ; s_{i+1}` converts,
over the star scope, to the common-pad core mirror triple `cL ; cR ; cL`. -/
theorem bunchedBimonoidBraidTripleReshapeRightSide (wordWidth positionK : Nat)
    (inRange : positionK + 3 ≤ wordWidth) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp
        (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth (positionK + 1))
          (bunchedBimonoidSigmaAt wordWidth positionK))
        (bunchedBimonoidSigmaAt wordWidth (positionK + 1)))
      (CellExpr.vcomp
        (CellExpr.vcomp (bunchedBimonoidBraidCoreLetterLeft positionK (wordWidth - positionK - 3))
          (bunchedBimonoidBraidCoreLetterRight positionK (wordWidth - positionK - 3)))
        (bunchedBimonoidBraidCoreLetterLeft positionK (wordWidth - positionK - 3))) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrRight
      (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth (positionK + 1))
        (bunchedBimonoidSigmaAt wordWidth positionK))
      (bunchedBimonoidSigmaAtBraidReshapeLeftConv wordWidth positionK))
    (SaturatedConvOverWithId.vcompCongrLeft
      (bunchedBimonoidBraidCoreLetterLeft positionK (wordWidth - positionK - 3))
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrLeft (bunchedBimonoidSigmaAt wordWidth positionK)
          (bunchedBimonoidSigmaAtBraidReshapeLeftConv wordWidth positionK))
        (SaturatedConvOverWithId.vcompCongrRight
          (bunchedBimonoidBraidCoreLetterLeft positionK (wordWidth - positionK - 3))
          (bunchedBimonoidSigmaAtBraidReshapeRightConv wordWidth positionK inRange))))

/-- ★★★ **THE GENERIC-WIDTH ADJACENT BRAID `sigmaAt w i ; sigmaAt w (i+1) ; sigmaAt w i ~ sigmaAt w (i+1) ;
sigmaAt w i ; sigmaAt w (i+1)`** — the Coxeter braid relation at ANY position `i` of ANY width `w` (`i + 2 < w`),
over the SHIPPED star scope, DERIVED term-mode from the axiomatic width-3 Yang-Baxter row.  Each `sigmaAt` letter
reshapes to common-pad core form (the two triple-reshape legs, threading the one arithmetic fact), the core braid
fires (`braidCoreConv`), the mirror expands back (`symm` of the right-side reshape).  NO wide kernel `rfl` — the
r20/r21 compute wall was on the endpoint-matrix strategy, which this DERIVATION never uses.  StrictAxioms
untouched.  `inRange : positionK + 2 < wordWidth` is definitionally `positionK + 3 <= wordWidth`. -/
theorem bunchedBimonoidGenericBraidConv (wordWidth positionK : Nat) (inRange : positionK + 2 < wordWidth) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp
        (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth positionK)
          (bunchedBimonoidSigmaAt wordWidth (positionK + 1)))
        (bunchedBimonoidSigmaAt wordWidth positionK))
      (CellExpr.vcomp
        (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth (positionK + 1))
          (bunchedBimonoidSigmaAt wordWidth positionK))
        (bunchedBimonoidSigmaAt wordWidth (positionK + 1))) :=
  SaturatedConvOverWithId.trans
    (bunchedBimonoidBraidTripleReshapeLeftSide wordWidth positionK inRange)
    (SaturatedConvOverWithId.trans
      (bunchedBimonoidBraidCoreConv positionK (wordWidth - positionK - 3))
      (SaturatedConvOverWithId.symm
        (bunchedBimonoidBraidTripleReshapeRightSide wordWidth positionK inRange)))

/-! ## A6 truth-probes (the braid endpoints share their matrix; width <= 4 only, single-sided) -/

#eval bunchedBimonoidEvalCell
  (CellExpr.vcomp (CellExpr.vcomp (bunchedBimonoidSigmaAt 3 0) (bunchedBimonoidSigmaAt 3 1))
    (bunchedBimonoidSigmaAt 3 0))
#eval bunchedBimonoidEvalCell
  (CellExpr.vcomp (CellExpr.vcomp (bunchedBimonoidSigmaAt 3 1) (bunchedBimonoidSigmaAt 3 0))
    (bunchedBimonoidSigmaAt 3 1))

/-- ★★★ **THE BRAID MATRIX PIN (width 3, position 0, `rfl`).**  Both braid triples `s_1 s_2 s_1` and
`s_2 s_1 s_2` at width 3 evaluate to the SAME matrix (the reversal permutation `[[0,0,1],[0,1,0],[1,0,0]]`), the
matrix truth the CONV derivation respects.  Width <= 4 only — the derivation itself is term-mode (no wide kernel
`rfl`); this pin is the small matrix witness. -/
theorem bunchedBimonoidGenericBraidThreeZeroMatrixShared :
    bunchedBimonoidEvalCell
        (CellExpr.vcomp (CellExpr.vcomp (bunchedBimonoidSigmaAt 3 0) (bunchedBimonoidSigmaAt 3 1))
          (bunchedBimonoidSigmaAt 3 0))
      = bunchedBimonoidEvalCell
        (CellExpr.vcomp (CellExpr.vcomp (bunchedBimonoidSigmaAt 3 1) (bunchedBimonoidSigmaAt 3 0))
          (bunchedBimonoidSigmaAt 3 1)) := rfl

/-! ## The A6 delivery marker (a FRESH marker; the residual + star owners stay byte-intact) -/

/-- ★★★ **ESTABLISHED (A6) — the generic-width adjacent-braid CONV atom is DELIVERED.**  `= true` records
`bunchedBimonoidGenericBraidConv`: the Coxeter braid `s_i s_{i+1} s_i ~ s_{i+1} s_i s_{i+1}` at ANY position `i`
of ANY width `w` (`i + 2 < w`), over the shipped star scope, DERIVED term-mode by whisker-embedding the axiomatic
width-3 `yangBaxter` hexagon row (per-letter reshape to common-pad core + the triple collapse + the atom + the
expansion), threading the one propext-clean truncated-subtraction fact.  NO wide kernel `rfl` (the r20/r21
compute wall was on the endpoint-matrix strategy, sidestepped); NO new engine row (`StrictAxioms` CLOSED);
matrix truth pinned at width 3 (`...ThreeZeroMatrixShared`).  This is the braid ingredient the CARRY unblock (F2)
needs; it does NOT itself flip any star owner — the fold chain F2-F4 + the owner assembly must land, and
`combInsertConv` additionally needs the r15 append-reshape part (b) (NOT delivered here).  The residual marker
`fxBunchedBimonoid_distantCommuteGenericBraidAndPermWordLiftStillOpen` and the four star owners
(StarAssembly / RiffleAssembly / CollisionCanonForm / CoxeterUniqueness) keep their names and `= false` values
byte-intact.  Zero-axiom (per-decl `#assert_no_axioms` + independent `#print axioms` in the twin). -/
def fxBunchedBimonoid_genericAdjacentBraidConvShipped : Bool := true

end FX1Poly.Polygraph.Omega
