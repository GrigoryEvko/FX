import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidWideCollisionNaturalitySlideWidth

/-! # Polygraph/Omega/WalkingBunchedBimonoidBlockThreadingConv — the CONV block-threading recursion NAMED as a
generic-width statement and its BASE case delivered as a genuine convertibility over the star scope (both colours,
and lifted to a generic pad position), with the general inductive step honestly walled (WP-PROP r28 B1, #2033)

★ **THE r28 B1 — the CONV half of the generic-width slide, at its base.**  The r27
`WideCollisionNaturalitySlideWidth` shipped the SOUNDNESS half of the generic-width naturality square (the
`Mat(N)` agreement `bunchedBimonoidSigmaPastMuFoldBlockLeft k ≈ ...Right k` at seven widths `k = 0..6`) but left
the CONV half — the actual convertibility `(a <| muFold k) ; sigma ~ strandPastBlock k ; (muFold k |> a)` over the
star scope — walled as a STRUCTURAL induction on `k`.  This file NAMES that CONV statement
(`bunchedBimonoidBlockThreadingConvStatementMu` / `...Delta`) and DELIVERS its base case as a machine-checked
convertibility, keyed on the strict unit / whisker-unit rows through the `SaturatedConvOverWithId` congruence:

  * **mu-side base** (`bunchedBimonoidBlockThreadingConvBaseMu`): at width `1` the `muFold 1 = id a` block makes
    `(a <| id a) ; sigma` and `sigma ; (id a |> a)` BOTH collapse to the bare `sigma` — the left leg by
    `whiskerLeftUnit` + `vcompUnitLeft`, the right leg by `whiskerRightUnit` + `vcompUnitRight`, transitively
    identified.  Pure congruence-constructor plumbing over the star scope (`whiskerLeftUnit` / `whiskerRightUnit`
    / `vcompUnit{Left,Right}` embedded via `bunchedBimonoidStrictAxiomEmbedsIntoStarScope`); NO wide `rfl` (the
    boundaries reduce definitionally: `boundarySource sigma = a.a = vcomp a a`).
  * **delta-side base** (`bunchedBimonoidBlockThreadingConvBaseDelta`): the exact dual at the `deltaFan 1 = id a`
    block, `sigma ; (a <| id a)` and `(id a |> a) ; sigma` both collapsing to `sigma`.
  * **both bases fired at a GENERIC PAD POSITION** (`...BaseMuAtPosition` / `...BaseDeltaAtPosition`) via the
    shipped `bunchedBimonoidFireAtPosition` — the base block-threading holds at any offset in a wide word.

## What stays walled — the general inductive step (the honest residual, no flip)

The general step `blockWidth → blockWidth + 1` — threading the peeled `mu`/`delta` through `whiskerLeftFunctorial`
/ `vcompAssoc` / the r19-landed `whiskerAssoc*` rows while reconciling the `muFold` id-floor, the `a^{blockWidth+1}`
word-power spelling, and the `strandPastBlock` bracketing — is NOT shipped: it is the long reassociation chain the
lane only landed the whisker-vs-1-cell coherences for in r19.  So the named statements
`bunchedBimonoidBlockThreadingConvStatementMu` / `...Delta` remain UNPROVEN in general; only their base instances
are delivered.  The r8 gated marker `fxBunchedBimonoid_wideCollisionConvGatedOnGenericNaturality` (`RiffleAssembly`,
whose bill demands the FULL generic-width slide PLUS the B3 `CoxeterWordUnique` bubble-sort) stays `= false`
byte-intact (cross-file, not edited); the r27
`fxBunchedBimonoid_genericWidthConvBlockThreadingStillWalled` and the #2033 star owner
`fxBunchedBimonoid_correctedWellTypedStarStillOpen` (`StarAssembly`, r7) stay `= false` byte-intact — NO fabricated
flip.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # B1 — THE CONV BLOCK-THREADING STATEMENT, NAMED (both colours)
    # =========================================================================================
-/

/-- ★★ **THE CONV BLOCK-THREADING STATEMENT (mu side), NAMED (NOT proven in general).**  For every block width
`blockWidth`, threading a `sigma` past the `muFold blockWidth` block on the LEFT is convertible over the star scope
to re-threading it on the RIGHT via the forward block braiding: `(a <| muFold k) ; sigma ~ strandPastBlock k ;
(muFold k |> a)`.  This is the CONV half of the r27 generic-width naturality square (whose SOUNDNESS half — the
`Mat(N)` agreement — is machine-checked at seven widths).  The `vcomp` case of the #2033 star's completeness half;
its base is delivered below, its general inductive step is the named residual. -/
def bunchedBimonoidBlockThreadingConvStatementMu : Prop :=
  ∀ (blockWidth : Nat),
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidSigmaPastMuFoldBlockLeft blockWidth)
      (bunchedBimonoidSigmaPastMuFoldBlockRight blockWidth)

/-- ★★ **THE CONV BLOCK-THREADING STATEMENT (delta side), NAMED (NOT proven in general).**  The dual: for every
block width, `sigma ; (a <| deltaFan k) ~ (deltaFan k |> a) ; strandPastBlockRev k` over the star scope, threading
the `sigma` past the `deltaFan k` block via the reverse block braiding. -/
def bunchedBimonoidBlockThreadingConvStatementDelta : Prop :=
  ∀ (blockWidth : Nat),
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidSigmaPastDeltaFanBlockLeft blockWidth)
      (bunchedBimonoidSigmaPastDeltaFanBlockRight blockWidth)

/-! # =========================================================================================
    # B1 — THE mu-SIDE BASE CASE (width 1): both legs collapse to the bare sigma
    # =========================================================================================
-/

/-- The mu-slide LEFT leg at width 1 collapses to the bare `sigma` over the star scope.  `muFold 1 = id a`, so
`whiskerLeft a (id a) ~ id (a.a)` by `whiskerLeftUnit`, placed under the vertical composite by `vcompCongrLeft`,
and the trailing `id (a.a) ; sigma` absorbed by `vcompUnitLeft` (`boundarySource sigma = a.a` definitionally). -/
theorem bunchedBimonoidBlockThreadingConvBaseMuLeftCollapse :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidSigmaPastMuFoldBlockLeft 1) bunchedBimonoidAddSigmaGen :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrLeft bunchedBimonoidAddSigmaGen
      (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
        (StrictAxiomRel.whiskerLeftUnit bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen)))
    (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
      (StrictAxiomRel.vcompUnitLeft bunchedBimonoidAddSigmaGen))

/-- The mu-slide RIGHT leg at width 1 collapses to the bare `sigma` over the star scope.  `strandPastBlock 1 =
sigma` and `muFold 1 = id a`, so `whiskerRight (id a) a ~ id (a.a)` by `whiskerRightUnit`, placed under the
vertical composite by `vcompCongrRight`, and the trailing `sigma ; id (a.a)` absorbed by `vcompUnitRight`. -/
theorem bunchedBimonoidBlockThreadingConvBaseMuRightCollapse :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidSigmaPastMuFoldBlockRight 1) bunchedBimonoidAddSigmaGen :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrRight bunchedBimonoidAddSigmaGen
      (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
        (StrictAxiomRel.whiskerRightUnit bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen)))
    (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
      (StrictAxiomRel.vcompUnitRight bunchedBimonoidAddSigmaGen))

/-- ★★★ **THE mu-SIDE CONV BLOCK-THREADING BASE (width 1) — DELIVERED.**  `(a <| muFold 1) ; sigma ~
strandPastBlock 1 ; (muFold 1 |> a)` over the star scope: both legs collapse to the bare `sigma` (above), so the
transitive composite identifies them.  The CONV half of the r27 generic-width naturality square at its base width,
a genuine convertibility (the r27 file delivered only the `Mat(N)` soundness half). -/
theorem bunchedBimonoidBlockThreadingConvBaseMu :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidSigmaPastMuFoldBlockLeft 1) (bunchedBimonoidSigmaPastMuFoldBlockRight 1) :=
  SaturatedConvOverWithId.trans bunchedBimonoidBlockThreadingConvBaseMuLeftCollapse
    (SaturatedConvOverWithId.symm bunchedBimonoidBlockThreadingConvBaseMuRightCollapse)

/-! # =========================================================================================
    # B1 — THE delta-SIDE BASE CASE (width 1): the exact dual
    # =========================================================================================
-/

/-- The delta-slide LEFT leg at width 1 collapses to the bare `sigma`.  `deltaFan 1 = id a`, so `whiskerLeft a
(id a) ~ id (a.a)` by `whiskerLeftUnit`, placed as the RIGHT factor by `vcompCongrRight`, and the trailing
`sigma ; id (a.a)` absorbed by `vcompUnitRight`. -/
theorem bunchedBimonoidBlockThreadingConvBaseDeltaLeftCollapse :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidSigmaPastDeltaFanBlockLeft 1) bunchedBimonoidAddSigmaGen :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrRight bunchedBimonoidAddSigmaGen
      (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
        (StrictAxiomRel.whiskerLeftUnit bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen)))
    (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
      (StrictAxiomRel.vcompUnitRight bunchedBimonoidAddSigmaGen))

/-- The delta-slide RIGHT leg at width 1 collapses to the bare `sigma`.  `strandPastBlockRev 1 = sigma` and
`deltaFan 1 = id a`, so `whiskerRight (id a) a ~ id (a.a)` by `whiskerRightUnit`, placed as the LEFT factor by
`vcompCongrLeft`, and the trailing `id (a.a) ; sigma` absorbed by `vcompUnitLeft`. -/
theorem bunchedBimonoidBlockThreadingConvBaseDeltaRightCollapse :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidSigmaPastDeltaFanBlockRight 1) bunchedBimonoidAddSigmaGen :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrLeft bunchedBimonoidAddSigmaGen
      (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
        (StrictAxiomRel.whiskerRightUnit bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen)))
    (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
      (StrictAxiomRel.vcompUnitLeft bunchedBimonoidAddSigmaGen))

/-- ★★★ **THE delta-SIDE CONV BLOCK-THREADING BASE (width 1) — DELIVERED.**  `sigma ; (a <| deltaFan 1) ~
(deltaFan 1 |> a) ; strandPastBlockRev 1` over the star scope, the exact dual of the mu-side base: both legs
collapse to the bare `sigma`.  The delta colour of the CONV block-threading base. -/
theorem bunchedBimonoidBlockThreadingConvBaseDelta :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidSigmaPastDeltaFanBlockLeft 1) (bunchedBimonoidSigmaPastDeltaFanBlockRight 1) :=
  SaturatedConvOverWithId.trans bunchedBimonoidBlockThreadingConvBaseDeltaLeftCollapse
    (SaturatedConvOverWithId.symm bunchedBimonoidBlockThreadingConvBaseDeltaRightCollapse)

/-! # =========================================================================================
    # B1 — THE BASE FIRED AT A GENERIC PAD POSITION (both colours)
    # =========================================================================================
-/

/-- ★★★ **THE mu-SIDE CONV BLOCK-THREADING BASE AT A GENERIC PAD.**  For every left/right pad, the width-1 mu-side
base fires as a CONV over the star scope inside a `whiskerLeft leftPad (whiskerRight _ rightPad)` frame — the base
block-threading usable at any offset in a wide word, via the shipped `bunchedBimonoidFireAtPosition`. -/
theorem bunchedBimonoidBlockThreadingConvBaseMuAtPosition
    (leftPad rightPad : CellExpr bunchedBimonoidOmegaComputad 1) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft leftPad
        (CellExpr.whiskerRight (bunchedBimonoidSigmaPastMuFoldBlockLeft 1) rightPad))
      (CellExpr.whiskerLeft leftPad
        (CellExpr.whiskerRight (bunchedBimonoidSigmaPastMuFoldBlockRight 1) rightPad)) :=
  bunchedBimonoidFireAtPosition leftPad rightPad bunchedBimonoidBlockThreadingConvBaseMu

/-- ★★★ **THE delta-SIDE CONV BLOCK-THREADING BASE AT A GENERIC PAD.**  The dual: the width-1 delta-side base
fires as a CONV over the star scope at an arbitrary pad position. -/
theorem bunchedBimonoidBlockThreadingConvBaseDeltaAtPosition
    (leftPad rightPad : CellExpr bunchedBimonoidOmegaComputad 1) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft leftPad
        (CellExpr.whiskerRight (bunchedBimonoidSigmaPastDeltaFanBlockLeft 1) rightPad))
      (CellExpr.whiskerLeft leftPad
        (CellExpr.whiskerRight (bunchedBimonoidSigmaPastDeltaFanBlockRight 1) rightPad)) :=
  bunchedBimonoidFireAtPosition leftPad rightPad bunchedBimonoidBlockThreadingConvBaseDelta

/-! # =========================================================================================
    # B1 — THE MARKERS + THE HONEST NO-FLIP LEDGER
    # =========================================================================================
-/

/-- ★★★ **ESTABLISHED (B1) — the CONV block-threading BASE is delivered, both colours, at any pad.**  `= true`
records `bunchedBimonoidBlockThreadingConvBaseMu` and `bunchedBimonoidBlockThreadingConvBaseDelta` (the width-1
CONV block-threading over the star scope for the mu / delta colours — both legs collapse to the bare `sigma` by
the strict unit / whisker-unit rows) and their generic-pad firings
(`...BaseMuAtPosition` / `...BaseDeltaAtPosition`).  This is the CONV half of the r27 generic-width naturality
square at its base width — the r27 file shipped only the `Mat(N)` soundness half; this shows the base is a genuine
convertibility, at any offset. -/
def fxBunchedBimonoid_blockThreadingConvBaseShipped : Bool := true

/-- ★ **THE CONV BLOCK-THREADING GENERAL STEP STAYS WALLED — no flip (exact residual named for the next round).**
`= false` records that the named statements `bunchedBimonoidBlockThreadingConvStatementMu` / `...Delta` are NOT
proven in general: only the base (width 1) is delivered above.  The general inductive step
`blockWidth → blockWidth + 1` threads the peeled `mu`/`delta` through `whiskerLeftFunctorial` / `vcompAssoc` / the
r19-landed `whiskerAssoc*` rows while reconciling the `muFold` id-floor, the `a^{blockWidth+1}` word-power
spelling, and the `strandPastBlock` bracketing — the long reassociation chain that is the exact r29 residual.  The
r8 gated marker `fxBunchedBimonoid_wideCollisionConvGatedOnGenericNaturality` (`RiffleAssembly`, whose bill demands
the FULL generic-width slide PLUS the B3 `CoxeterWordUnique` bubble-sort) and the r27
`fxBunchedBimonoid_genericWidthConvBlockThreadingStillWalled` stay `= false` byte-intact (cross-file, not
edited). -/
def fxBunchedBimonoid_blockThreadingConvGeneralStepStillWalled : Bool := false

/-- ★ **THE CORRECTED WELL-TYPED STAR STAYS OPEN — no flip (byte-intact, cross-file).**  `= false` records that
`bunchedBimonoidStarStatementAdditiveWellTyped` is STILL NOT proven in r28: this round delivers the CONV
block-threading BASE (the `vcomp` case of the star's completeness half, at width 1, both colours, at any pad), but
the star's `vcomp` case needs the general block-threading step (walled above) and its equal-matrices middle needs
the perm-determinism and total retraction.  The star owner
`fxBunchedBimonoid_correctedWellTypedStarStillOpen` (`StarAssembly`, r7) and every upstream star marker keep their
name and `= false` value byte-intact (cross-file, not edited) — NO fabricated flip. -/
def fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterBlockThreadingBase : Bool := false

/-- ★★★ **ESTABLISHED (B1) — the WP-PROP r28 block-threading-CONV ledger (the honest scoreboard).**  `= true`
records the complete r28 B1 advance: the CONV block-threading statement NAMED for both colours
(`bunchedBimonoidBlockThreadingConvStatement{Mu,Delta}`) and its BASE case delivered as a genuine convertibility
over the star scope, both colours, at width 1, and lifted to a generic pad position
(`fxBunchedBimonoid_blockThreadingConvBaseShipped`).  The general inductive step stays walled
(`fxBunchedBimonoid_blockThreadingConvGeneralStepStillWalled = false`, exact r29 residual named); the #2033 star
does NOT flip (`fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterBlockThreadingBase = false`).  Every upstream
wall (the r8 gated markers, the r27 walls, the star owner) keeps its name and value byte-intact (cross-file, not
edited); zero-axiom (per-decl `#assert_no_axioms` + independent `#print axioms` in the twin); STRUCTURAL only.  NO
fabricated star flip. -/
def fxBunchedBimonoid_blockThreadingConvRoundLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
