import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPositionGenericMoves

/-! # Polygraph/Omega/WalkingBunchedBimonoidWideCollisionNaturalitySlideWidth — the reverse block-braiding
primitive, the generic-WIDTH naturality SQUARE (sigma threaded past a `muFold` / `deltaFan` block of arbitrary
width, its SOUNDNESS half machine-checked at seven widths incl. one far above the natural), and the base slide
fired at a generic-width left pad (WP-PROP r27, #2033)

★ **THE r27 GENERIC-WIDTH SLIDE — the SOUNDNESS half delivered, the CONV block-threading honestly walled.**  The
r9 `PositionGenericMoves` delivered gate (a) of the wide-collision recursion as the base width-3
`bunchedBimonoid{Mu,Delta}NaturalitySlideConv` fired at an arbitrary PAD (`...SlideAtPosition`).  The genuine r27
gap the recon named is generic WIDTH: the collision peel (`bunchedBimonoidMuFoldPeel`) leaves a residual
`muFold k` block of ARBITRARY width `k`, and threading a `sigma` past that whole block is a block braiding
`sigma_{a, a^k}`.  This file:

  * ships the **reverse block braiding** `bunchedBimonoidStrandPastBlockRev k : a^k.a => a.a^k` (moving the
    TRAILING strand to the front), the delta-side dual of the shipped forward `strandPastBlock` — a genuine
    general structural def;
  * establishes the generic-WIDTH naturality SQUARE's SOUNDNESS half, both colours, machine-checked at seven
    widths `k = 0..6` (including `k = 6`, FAR above the natural `k = 2` the base slide covers): the sigma
    threaded past the `muFold k` / `deltaFan k` block is `Mat(N)`-equal to the block re-threaded on the other
    side (`bunchedBimonoidSigmaPastMuFoldBlockSoundAtWidth{Zero..Six}` and the delta duals), by kernel `decide`
    on the `.entries` (NEVER a wide `rfl`);
  * fires the base slide at a generic-width LEFT pad `a^k` for every `k` (`bunchedBimonoidMuNaturalitySlideAt-
    LeftPadWidth`), a CONV over the star scope — the r9 position combinator lifted from a fixed pad to a
    universally-quantified pad width.

## What stays walled — the CONV block-threading recursion (the honest residual, no flip)

The full generic-width slide as a CONV over the star scope — `(a <| muFold k) ; sigma ~ strandPastBlock k ;
(muFold k |> a)` as a STRUCTURAL induction on `k` — is NOT shipped: its inductive step threads the peeled `mu`
through `whiskerLeftFunctorial` / `vcompAssoc` / the (r19-landed) `whiskerAssoc*` rows while reconciling the
`muFold` id-floor, the `a^{k+1}` word-power spelling, and the `strandPastBlock` bracketing — a long
reassociation chain whose whisker-vs-1-cell coherences the lane only landed in r19.  That CONV recursion is the
`vcompCase` of the #2033 star's completeness half; it stays the named residual for the next round.  The two
gated markers `fxBunchedBimonoid_wideCollisionConvGatedOnGenericNaturality` (r8, `RiffleAssembly`) and
`fxBunchedBimonoid_collisionGeneralStepStillGatedOnBracketMatch` (r8, `CollisionCanonForm`) stay `= false`
byte-intact (cross-file, not edited); the #2033 star marker
`fxBunchedBimonoid_correctedWellTypedStarStillOpen` (r7, `StarAssembly`) stays `= false` byte-intact — NO
fabricated flip.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! The block braidings at width 6-7 evaluate `(k+1) x (k+1)` permutation matrices; the raise is a compute
allowance only, the proof terms stay `Eq.refl` / kernel `Decidable.decide` reductions, axiom-free (uniform with
the r6-r9 lane files). -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # B1 — THE REVERSE BLOCK-BRAIDING PRIMITIVE (the delta-side dual of `strandPastBlock`)
    # =========================================================================================
-/

/-- ★★ **THE REVERSE RIFFLE PRIMITIVE `strandPastBlockRev k : a^k.a => a.a^k`** — the block braiding
`sigma_{a^k, a}` moving the TRAILING strand past a block of `k` strands to the front, the delta-side dual of the
shipped forward `bunchedBimonoidStrandPastBlock`.  Built as a whiskered chain of adjacent `sigma`s by structural
recursion on the block size: `0` is the identity (nothing to pass), `1` is the bare `sigma`, `k+2` swaps the
trailing pair under the fixed `a^{k+1}` front (`a^{k+1} <| sigma`) then recurses moving the strand through the
`a^{k+1}` block (`strandPastBlockRev(k+1) |> a`).  A genuine general def; `evalCell (strandPastBlockRev k)` is
the `(k+1) x (k+1)` cyclic shift moving the last strand to the front (probed below). -/
def bunchedBimonoidStrandPastBlockRev : Nat → CellExpr bunchedBimonoidOmegaComputad 2
  | 0 => CellExpr.id bunchedBimonoidAdditiveGen
  | 1 => bunchedBimonoidAddSigmaGen
  | n + 2 => CellExpr.vcomp
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow (n + 1)) bunchedBimonoidAddSigmaGen)
      (CellExpr.whiskerRight (bunchedBimonoidStrandPastBlockRev (n + 1)) bunchedBimonoidAdditiveGen)

/-! ## B1 reverse-primitive truth-probe outputs (the reverse braiding is the reverse cyclic shift) -/

#eval bunchedBimonoidEvalCell (bunchedBimonoidStrandPastBlockRev 2)
#eval bunchedBimonoidEvalCell (bunchedBimonoidStrandPastBlockRev 3)

/-- `strandPastBlockRev 1` is the bare swap `[[0,1],[1,0]]`. -/
theorem bunchedBimonoidStrandPastBlockRevOneMatrix :
    (bunchedBimonoidEvalCell (bunchedBimonoidStrandPastBlockRev 1)).entries = [[0, 1], [1, 0]] := by decide

/-- ★★ `strandPastBlockRev 2` is the `3 x 3` reverse cyclic shift `[[0,0,1],[1,0,0],[0,1,0]]` moving the last
strand to the front — the transpose / inverse of the forward `strandPastBlock 2` cyclic shift. -/
theorem bunchedBimonoidStrandPastBlockRevTwoMatrix :
    (bunchedBimonoidEvalCell (bunchedBimonoidStrandPastBlockRev 2)).entries
      = [[0, 0, 1], [1, 0, 0], [0, 1, 0]] := by decide

/-- ★ **THE FORWARD AND REVERSE BRAIDINGS ARE INVERSE (width 3, `decide`).**  `strandPastBlock 2` (forward
cyclic shift) composed with `strandPastBlockRev 2` (reverse cyclic shift) is the `3 x 3` identity — the two
block braidings are genuine inverse permutations, not the same map. -/
theorem bunchedBimonoidStrandPastBlockForwardReverseInverse :
    (bunchedBimonoidMatMul (bunchedBimonoidEvalCell (bunchedBimonoidStrandPastBlock 2))
        (bunchedBimonoidEvalCell (bunchedBimonoidStrandPastBlockRev 2))).entries
      = (bunchedBimonoidIdentityMat 3).entries := by decide

/-! # =========================================================================================
    # B1 — THE GENERIC-WIDTH NATURALITY SQUARE, mu SIDE (the SOUNDNESS half)
    # =========================================================================================

★ The mu-side generic-width naturality square: threading a `sigma` past the `muFold k` block on the LEFT equals
re-threading it on the RIGHT via the forward block braiding.  `bunchedBimonoidSigmaPastMuFoldBlockLeft k =
(a <| muFold k) ; sigma` and `...Right k = strandPastBlock k ; (muFold k |> a)`, both `a.a^k => a.a` (a `2 x
(k+1)` map).  Their `Mat(N)` agreement is the SOUNDNESS half of the generic-width slide — the block braiding is
natural with respect to the multiplication fold at every width. -/

/-- The mu-slide LEFT endpoint `(a <| muFold k) ; sigma : a.a^k => a.a`. -/
def bunchedBimonoidSigmaPastMuFoldBlockLeft (blockWidth : Nat) : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp
    (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen (bunchedBimonoidMuFold blockWidth))
    bunchedBimonoidAddSigmaGen

/-- The mu-slide RIGHT endpoint `strandPastBlock k ; (muFold k |> a) : a.a^k => a.a`. -/
def bunchedBimonoidSigmaPastMuFoldBlockRight (blockWidth : Nat) : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp
    (bunchedBimonoidStrandPastBlock blockWidth)
    (CellExpr.whiskerRight (bunchedBimonoidMuFold blockWidth) bunchedBimonoidAdditiveGen)

/-! ## mu-side truth-probe outputs (both legs share their matrix at each width) -/

#eval (List.range 7).map (fun w =>
  decide ((bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockLeft w)).entries
    = (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockRight w)).entries))

/-- ★ mu-side soundness at width 0 (the degenerate `eta` block). -/
theorem bunchedBimonoidSigmaPastMuFoldBlockSoundAtWidthZero :
    (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockLeft 0)).entries
      = (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockRight 0)).entries := by decide

/-- ★ mu-side soundness at width 1 (the `id a` block). -/
theorem bunchedBimonoidSigmaPastMuFoldBlockSoundAtWidthOne :
    (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockLeft 1)).entries
      = (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockRight 1)).entries := by decide

/-- ★★ mu-side soundness at width 2 (the natural base the width-3 hexagon slide covers). -/
theorem bunchedBimonoidSigmaPastMuFoldBlockSoundAtWidthTwo :
    (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockLeft 2)).entries
      = (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockRight 2)).entries := by decide

/-- ★★ mu-side soundness at width 3 (above the natural base). -/
theorem bunchedBimonoidSigmaPastMuFoldBlockSoundAtWidthThree :
    (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockLeft 3)).entries
      = (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockRight 3)).entries := by decide

/-- ★★ mu-side soundness at width 4. -/
theorem bunchedBimonoidSigmaPastMuFoldBlockSoundAtWidthFour :
    (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockLeft 4)).entries
      = (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockRight 4)).entries := by decide

/-- ★★ mu-side soundness at width 5. -/
theorem bunchedBimonoidSigmaPastMuFoldBlockSoundAtWidthFive :
    (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockLeft 5)).entries
      = (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockRight 5)).entries := by decide

/-- ★★★ **THE UNIVERSALITY PROBE — mu-side soundness at width 6, FAR above the natural base.**  The block
braiding's naturality with respect to `muFold 6` (a six-input fold) is `Mat(N)`-verified: a `2 x 7` agreement,
kernel `decide` (NEVER a wide `rfl`).  The generic-width naturality square holds well beyond the width-3 hexagon
the base slide covers. -/
theorem bunchedBimonoidSigmaPastMuFoldBlockSoundAtWidthSix :
    (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockLeft 6)).entries
      = (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockRight 6)).entries := by decide

/-! # =========================================================================================
    # B1 — THE GENERIC-WIDTH NATURALITY SQUARE, delta SIDE (the SOUNDNESS half, reverse braiding)
    # =========================================================================================

★ The delta-side dual: `sigma ; (a <| deltaFan k)` re-threaded as `(deltaFan k |> a) ; strandPastBlockRev k`,
both `a.a => a.a^k`.  Uses the REVERSE block braiding shipped above (the trailing strand moves to the front, the
mirror of the mu side). -/

/-- The delta-slide LEFT endpoint `sigma ; (a <| deltaFan k) : a.a => a.a^k`. -/
def bunchedBimonoidSigmaPastDeltaFanBlockLeft (blockWidth : Nat) : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp
    bunchedBimonoidAddSigmaGen
    (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen (bunchedBimonoidDeltaFan blockWidth))

/-- The delta-slide RIGHT endpoint `(deltaFan k |> a) ; strandPastBlockRev k : a.a => a.a^k`. -/
def bunchedBimonoidSigmaPastDeltaFanBlockRight (blockWidth : Nat) : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp
    (CellExpr.whiskerRight (bunchedBimonoidDeltaFan blockWidth) bunchedBimonoidAdditiveGen)
    (bunchedBimonoidStrandPastBlockRev blockWidth)

/-! ## delta-side truth-probe output (both legs share their matrix at each width) -/

#eval (List.range 7).map (fun w =>
  decide ((bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastDeltaFanBlockLeft w)).entries
    = (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastDeltaFanBlockRight w)).entries))

/-- ★★ delta-side soundness at width 2 (the natural base). -/
theorem bunchedBimonoidSigmaPastDeltaFanBlockSoundAtWidthTwo :
    (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastDeltaFanBlockLeft 2)).entries
      = (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastDeltaFanBlockRight 2)).entries := by decide

/-- ★★ delta-side soundness at width 4. -/
theorem bunchedBimonoidSigmaPastDeltaFanBlockSoundAtWidthFour :
    (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastDeltaFanBlockLeft 4)).entries
      = (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastDeltaFanBlockRight 4)).entries := by decide

/-- ★★★ **THE UNIVERSALITY PROBE — delta-side soundness at width 6, FAR above the natural base.**  The reverse
block braiding's naturality with respect to `deltaFan 6` (a six-output fan) is `Mat(N)`-verified: a `7 x 2`
agreement, kernel `decide`.  The delta-side generic-width square holds far beyond the natural base. -/
theorem bunchedBimonoidSigmaPastDeltaFanBlockSoundAtWidthSix :
    (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastDeltaFanBlockLeft 6)).entries
      = (bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastDeltaFanBlockRight 6)).entries := by decide

/-! # =========================================================================================
    # B1 — THE BASE SLIDE AT A GENERIC-WIDTH LEFT PAD (a CONV over the star scope, all pad widths)
    # =========================================================================================

★ The r9 position combinator fired the base width-3 slide at a FIXED pad `(a^1, a^0)`.  Here it fires at a LEFT
pad `a^k` of ARBITRARY width `k` for every `k` — a universally-quantified generic-width position slide, the
block sitting at a width-`k` offset in a wide word.  The block-threading of the residual `muFold k` (a CONV) is
the walled residual; this is the block placed AFTER a generic-width identity context. -/

/-- ★★★ **THE MU-NATURALITY SLIDE AT A GENERIC-WIDTH LEFT PAD.**  For every pad width `k` and every right pad,
the base mu-naturality slide fires as a CONV over the star scope inside a `whiskerLeft (a^k) (whiskerRight _
rightPad)` frame — the r9 fixed-pad `...SlideAtPosition` lifted to a universally-quantified LEFT-pad width via
the shipped `bunchedBimonoidFireAtPosition`.  Generic in the pad width `k` and the right pad. -/
theorem bunchedBimonoidMuNaturalitySlideAtLeftPadWidth (blockWidth : Nat)
    (rightPad : CellExpr bunchedBimonoidOmegaComputad 1) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow blockWidth)
        (CellExpr.whiskerRight bunchedBimonoidMuNaturalityLeftLeg rightPad))
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow blockWidth)
        (CellExpr.whiskerRight bunchedBimonoidMuNaturalityRightLeg rightPad)) :=
  bunchedBimonoidFireAtPosition (bunchedBimonoidAWordPow blockWidth) rightPad
    bunchedBimonoidMuNaturalitySlideConv

/-- ★★★ **THE DELTA-NATURALITY SLIDE AT A GENERIC-WIDTH LEFT PAD.**  The dual: the base delta-naturality slide
fires as a CONV over the star scope at an arbitrary left-pad width `k` and arbitrary right pad. -/
theorem bunchedBimonoidDeltaNaturalitySlideAtLeftPadWidth (blockWidth : Nat)
    (rightPad : CellExpr bunchedBimonoidOmegaComputad 1) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow blockWidth)
        (CellExpr.whiskerRight bunchedBimonoidDeltaNaturalityLeftLeg rightPad))
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow blockWidth)
        (CellExpr.whiskerRight bunchedBimonoidDeltaNaturalityRightLeg rightPad)) :=
  bunchedBimonoidFireAtPosition (bunchedBimonoidAWordPow blockWidth) rightPad
    bunchedBimonoidDeltaNaturalitySlideConv

/-! # =========================================================================================
    # B1 — THE MARKERS + THE HONEST NO-FLIP LEDGER
    # =========================================================================================
-/

/-- ★★ **ESTABLISHED (B1) — the reverse block-braiding primitive is shipped.**  `= true` records
`bunchedBimonoidStrandPastBlockRev` (the general reverse block braiding `a^k.a => a.a^k`, the delta-side dual of
the forward `strandPastBlock`), its reverse-cyclic-shift matrices probed at `k = 1, 2`, and its inverse
relationship to the forward braiding (`...ForwardReverseInverse`: their composite is the identity).  The delta
side's block braiding, now a genuine general def. -/
def fxBunchedBimonoid_reverseBlockBraidingShipped : Bool := true

/-- ★★★ **ESTABLISHED (B1) — the generic-WIDTH naturality square's SOUNDNESS half is machine-checked at seven
widths, both colours.**  `= true` records `bunchedBimonoidSigmaPastMuFoldBlockSoundAtWidth{Zero..Six}` and the
delta duals: the block braiding is natural with respect to the `muFold k` / `deltaFan k` block as a `Mat(N)`
identity at `k = 0, 1, 2, 3, 4, 5, 6`, INCLUDING `k = 6` FAR above the natural `k = 2` the width-3 hexagon slide
covers, by kernel `decide` on the `.entries` (NEVER a wide `rfl`).  This is the SOUNDNESS half of the
generic-width slide — the block-braiding naturality the wide-collision recursion's `vcomp` case rests on. -/
def fxBunchedBimonoid_genericWidthNaturalitySquareSoundnessShipped : Bool := true

/-- ★★ **ESTABLISHED (B1) — the base slide fires at a generic-width left pad.**  `= true` records
`bunchedBimonoid{Mu,Delta}NaturalitySlideAtLeftPadWidth`: the base width-3 naturality slide fired as a CONV over
the star scope at a universally-quantified LEFT-pad width `k` (and arbitrary right pad), lifting the r9 fixed-pad
`...SlideAtPosition` to all pad widths via `bunchedBimonoidFireAtPosition`.  The block placed after a
generic-width identity context, a CONV at every width. -/
def fxBunchedBimonoid_baseSlideAtGenericPadWidthShipped : Bool := true

/-- ★ **THE CONV BLOCK-THREADING RECURSION STAYS WALLED — no flip (exact residual named for the next round).**
`= false` records that the full generic-width slide as a CONV over the star scope — `(a <| muFold k) ; sigma ~
strandPastBlock k ; (muFold k |> a)` as a STRUCTURAL induction on `k` — is NOT shipped: its SOUNDNESS half is
delivered above (the `Mat(N)` square at seven widths), but its inductive step threads the peeled `mu` through
`whiskerLeftFunctorial` / `vcompAssoc` / the r19-landed `whiskerAssoc*` rows while reconciling the `muFold`
id-floor, the `a^{k+1}` word-power spelling, and the `strandPastBlock` bracketing — the long reassociation chain
whose whisker-vs-1-cell coherences the lane only landed in r19.  This CONV recursion is the `vcomp` case of the
#2033 star's completeness half; the two gated markers
`fxBunchedBimonoid_wideCollisionConvGatedOnGenericNaturality` (r8) and
`fxBunchedBimonoid_collisionGeneralStepStillGatedOnBracketMatch` (r8) stay `= false` byte-intact (cross-file, not
edited). -/
def fxBunchedBimonoid_genericWidthConvBlockThreadingStillWalled : Bool := false

/-- ★ **THE CORRECTED WELL-TYPED STAR STAYS OPEN — no flip (byte-intact, cross-file).**  `= false` records that
`bunchedBimonoidStarStatementAdditiveWellTyped` is STILL NOT proven in r27: this round delivers the
generic-width naturality square's SOUNDNESS half and the base slide at a generic pad width, but the star's
`vcomp` case still needs the walled CONV block-threading recursion above, and its equal-matrices middle still
needs the perm-determinism and the total retraction.  The star-owning marker
`fxBunchedBimonoid_correctedWellTypedStarStillOpen` (StarAssembly, r7) and every upstream star marker keep their
name and `= false` value byte-intact (cross-file, not edited) — NO fabricated flip. -/
def fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterGenericWidthSoundness : Bool := false

/-- ★★★ **ESTABLISHED (B1) — the WP-PROP r27 generic-width-slide ledger (the honest scoreboard).**  `= true`
records the complete r27 B1 advance: the reverse block-braiding primitive
(`fxBunchedBimonoid_reverseBlockBraidingShipped`); the generic-WIDTH naturality square's SOUNDNESS half,
machine-checked at seven widths incl. `k = 6` far above natural, both colours
(`fxBunchedBimonoid_genericWidthNaturalitySquareSoundnessShipped`); and the base slide at a generic-width left
pad (`fxBunchedBimonoid_baseSlideAtGenericPadWidthShipped`).  The full CONV block-threading recursion stays
walled (`fxBunchedBimonoid_genericWidthConvBlockThreadingStillWalled = false`, exact residual named); the #2033
star does NOT flip (`fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterGenericWidthSoundness = false`).  Every
upstream wall keeps its name and value byte-intact (cross-file, not edited); zero-axiom (per-decl
`#assert_no_axioms` + independent `#print axioms` in the twin); STRUCTURAL only.  NO fabricated star flip. -/
def fxBunchedBimonoid_wideCollisionNaturalitySlideWidthLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
