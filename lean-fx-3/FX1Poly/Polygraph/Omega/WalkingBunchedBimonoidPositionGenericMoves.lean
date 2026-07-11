import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidRiffleAssembly

/-! # Polygraph/Omega/WalkingBunchedBimonoidPositionGenericMoves — the position-generic move library: fire ANY
base convertibility at an arbitrary pad-position, and the seven shipped base moves lifted to generic position
(the wide-collision recursion's gate (a), the generic-width naturality slide, DELIVERED) (WP-PROP r9, #2033)

★ **THE r9 HEADLINE — every base move becomes a CONV at an arbitrary position, whnf-free.**  The r8
`RiffleAssembly` narrowed the `(m,n)` wide-collision CONV recursion to two named lemmas
(`fxBunchedBimonoid_wideCollisionConvGatedOnGenericNaturality = false`): (a) a GENERIC-WIDTH naturality slide
lifting the width-3 `bunchedBimonoid{Mu,Delta}NaturalitySlideConv` whiskered by the one-hole congruences, and (b)
the B3 `CoxeterWordUnique` bubble-sort.  This file DELIVERS gate (a) as a reusable cell library: the
non-recursive combinator `bunchedBimonoidFireAtPosition` wraps any base convertibility `baseLeft ~ baseRight`
under a `whiskerLeft leftPad (whiskerRight _ rightPad)` frame via the two one-hole congruences of
`SaturatedConvOverWithId`, and the seven shipped base moves (five Coxeter / double-coset + two naturality slides)
are instantiated at arbitrary pads.  Pure congruence-constructor plumbing — NO kernel matrix evaluation, so no
whnf hazard.

## Why this is the right carrier (the strand arithmetic)

The eval equations spell whiskering as the block-diagonal direct sum: `evalCell (whiskerLeft p X) = I_{|p|} (+)
evalCell X` and `evalCell (whiskerRight X q) = evalCell X (+) I_{|q|}`.  So firing a base move `baseLeft ~
baseRight` at position `(leftPad, rightPad)` lands the move in the block `I_{|leftPad|} (+) base (+) I_{|rightPad|}`
— the exact block-offset the wide-collision recursion needs when it slides a generated `sigma` past a `mu`/`delta`
sitting at an arbitrary offset in an `m*n`-strand word.  The move-firing (`whiskerLeftCongr` / `whiskerRightCongr`)
and the cell spelling (`whiskerLeft` / `whiskerRight`) are the same shape, so the combinator is definitional.

## What ships and what stays walled (the honest scope)

Gate (a) of the wide-collision recursion is DELIVERED: the mu / delta naturality slides fire at generic position
(`bunchedBimonoid{Mu,Delta}NaturalitySlideAtPosition`).  Gate (b) — the general `CoxeterWordUnique` — stays walled
(B3 `fxBunchedBimonoid_coxeterWordUniqueGatedOnGenericBraid`, r8), and the full `(m,n)` induction additionally
needs the peel/brick/slide steps ASSEMBLED into a structural recursion plus `whiskerRightFunctorial`
reassociation glue.  The star does NOT flip: no hypothesis-free inhabitant of
`bunchedBimonoidStarStatementAdditiveWellTyped` is produced; every upstream star / recursion marker stays
byte-intact `= false`.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! The position pins evaluate a whiskered permutation matrix at width 3-4, exceeding the default heartbeat
budget; the raise is a compute allowance only, the proof terms stay `Eq.refl` / congruence-constructor plumbing,
axiom-free (uniform with the r6/r7/r8 lane files). -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # L1 — THE POSITION-GENERIC FIRING COMBINATOR (non-recursive, whnf-free)
    # =========================================================================================
-/

/-- ★★★ **THE POSITION-GENERIC FIRING COMBINATOR `bunchedBimonoidFireAtPosition`** — fire ANY base
convertibility `baseLeft ~ baseRight` (a 2-cell equation over the star scope) inside a
`whiskerLeft leftPad (whiskerRight _ rightPad)` frame, for arbitrary 1-cell pads.  Two one-hole congruence
constructors compose: `whiskerRightCongr rightPad` pushes the move under the right pad, then
`whiskerLeftCongr leftPad` under the left pad.  Pure congruence-constructor plumbing — NO kernel matrix
evaluation, so no whnf hazard.  The cell library atom the wide-collision recursion's generic-width slide stands
on: it lands the base move in the block `I_{|leftPad|} (+) base (+) I_{|rightPad|}`. -/
theorem bunchedBimonoidFireAtPosition {dim : Nat}
    (leftPad rightPad : CellExpr bunchedBimonoidOmegaComputad (dim + 1))
    {baseLeft baseRight : CellExpr bunchedBimonoidOmegaComputad (dim + 2)}
    (baseConv : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      baseLeft baseRight) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight baseLeft rightPad))
      (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight baseRight rightPad)) :=
  SaturatedConvOverWithId.whiskerLeftCongr leftPad
    (SaturatedConvOverWithId.whiskerRightCongr rightPad baseConv)

/-! # =========================================================================================
    # L2 — THE SEVEN SHIPPED BASE MOVES, LIFTED TO GENERIC POSITION
    # =========================================================================================

★ Each of the five Coxeter / double-coset moves (`bunchedBimonoidCoxeterMovesAllInScope`, r7) and the two
width-3 naturality slides (`bunchedBimonoid{Mu,Delta}NaturalitySlideConv`, r7) becomes a convertibility at an
arbitrary pad-position by a single `bunchedBimonoidFireAtPosition` application.  Generic in both pads. -/

/-- ★★ **THE ADJACENT-BRAID (Yang-Baxter) MOVE AT GENERIC POSITION.**  `s_1 s_2 s_1 ~ s_2 s_1 s_2` fired inside a
`whiskerLeft leftPad (whiskerRight _ rightPad)` frame — the braid relation usable at any offset in a wide word. -/
theorem bunchedBimonoidYangBaxterAtPosition
    (leftPad rightPad : CellExpr bunchedBimonoidOmegaComputad 1) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight bunchedBimonoidYangBaxterLeftLeg rightPad))
      (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight bunchedBimonoidYangBaxterRightLeg rightPad)) :=
  bunchedBimonoidFireAtPosition leftPad rightPad bunchedBimonoidYangBaxterDeterminismOverStar

/-- ★★ **THE INVOLUTION MOVE `s_1 s_1 = e` AT GENERIC POSITION.**  The swap's own cancellation, firable at any
offset. -/
theorem bunchedBimonoidInvolutionAtPosition
    (leftPad rightPad : CellExpr bunchedBimonoidOmegaComputad 1) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight bunchedBimonoidSigmaInvolutionLeftLeg rightPad))
      (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight bunchedBimonoidSigmaInvolutionRightLeg rightPad)) :=
  bunchedBimonoidFireAtPosition leftPad rightPad bunchedBimonoidInvolutionDeterminismOverStar

/-- ★★ **THE DISTANT-COMMUTATION MOVE `s_1 s_3 = s_3 s_1` AT GENERIC POSITION.**  The disjoint-range swap
(derived from the Godement interchange, r7), firable at any offset — the `|i-j| >= 2` commutation the sort needs
wherever two far-apart transpositions meet. -/
theorem bunchedBimonoidDistantSwapAtPosition
    (leftPad rightPad : CellExpr bunchedBimonoidOmegaComputad 1) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight bunchedBimonoidDistantSwapLeftLeg rightPad))
      (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight bunchedBimonoidDistantSwapRightLeg rightPad)) :=
  bunchedBimonoidFireAtPosition leftPad rightPad bunchedBimonoidDistantSwapCommuteViaInterchange

/-- ★★ **THE COMMUTATIVITY DOUBLE-COSET MOVE `mu.sigma = mu` AT GENERIC POSITION.**  A `mu` absorbs a preceding
swap at any block-offset — one of the two double-coset generators. -/
theorem bunchedBimonoidCommutativityAtPosition
    (leftPad rightPad : CellExpr bunchedBimonoidOmegaComputad 1) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight bunchedBimonoidCommutativityLeftLeg rightPad))
      (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight bunchedBimonoidCommutativityRightLeg rightPad)) :=
  bunchedBimonoidFireAtPosition leftPad rightPad bunchedBimonoidCommutativityOverStar

/-- ★★ **THE COCOMMUTATIVITY DOUBLE-COSET MOVE `sigma.delta = delta` AT GENERIC POSITION.**  The dual
double-coset generator at any block-offset. -/
theorem bunchedBimonoidCocommutativityAtPosition
    (leftPad rightPad : CellExpr bunchedBimonoidOmegaComputad 1) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight bunchedBimonoidCocommutativityLeftLeg rightPad))
      (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight bunchedBimonoidCocommutativityRightLeg rightPad)) :=
  bunchedBimonoidFireAtPosition leftPad rightPad bunchedBimonoidCocommutativityOverStar

/-- ★★★ **THE MU-NATURALITY SLIDE AT GENERIC POSITION (wide-collision gate (a), the mu half).**  The width-3
mu-naturality slide `(a <| mu) ; sigma ~ [(sigma |> a) ; (a <| sigma)] ; (mu |> a)` fired inside a
`whiskerLeft leftPad (whiskerRight _ rightPad)` frame — the generated `sigma` slides past a `mu` block sitting at
an arbitrary offset in a wide word.  This is the GENERIC-WIDTH naturality slide the r8
`fxBunchedBimonoid_wideCollisionConvGatedOnGenericNaturality` named as gate (a): the width-3 slide whiskered by
the one-hole congruences to arbitrary position, NOW a CONV over the star scope. -/
theorem bunchedBimonoidMuNaturalitySlideAtPosition
    (leftPad rightPad : CellExpr bunchedBimonoidOmegaComputad 1) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight bunchedBimonoidMuNaturalityLeftLeg rightPad))
      (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight bunchedBimonoidMuNaturalityRightLeg rightPad)) :=
  bunchedBimonoidFireAtPosition leftPad rightPad bunchedBimonoidMuNaturalitySlideConv

/-- ★★★ **THE DELTA-NATURALITY SLIDE AT GENERIC POSITION (wide-collision gate (a), the delta half).**  The dual
width-3 delta-naturality slide `sigma ; (a <| delta) ~ (delta |> a) ; [(a <| sigma) ; (sigma |> a)]` fired at an
arbitrary offset — the generated `sigma` slides past a `delta` block at any position.  The delta half of gate
(a). -/
theorem bunchedBimonoidDeltaNaturalitySlideAtPosition
    (leftPad rightPad : CellExpr bunchedBimonoidOmegaComputad 1) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight bunchedBimonoidDeltaNaturalityLeftLeg rightPad))
      (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight bunchedBimonoidDeltaNaturalityRightLeg rightPad)) :=
  bunchedBimonoidFireAtPosition leftPad rightPad bunchedBimonoidDeltaNaturalitySlideConv

/-! # =========================================================================================
    # L2 — TRUTH-PROBES: the fired-at-position cells are non-vacuous and matrix-sound (small width)
    # =========================================================================================

★ The position-generic moves relate two cells with the SAME matrix (every base move is matrix-preserving, and
whiskering is a functor of the matrix).  These probes evaluate the fired endpoints at width 3-4 and pin the
soundness `evalCell (fired-left) = evalCell (fired-right)` by `rfl`. -/

/-! ## Truth-probe outputs (the fired endpoints, at concrete small pads) -/

#eval bunchedBimonoidEvalCell
  (CellExpr.whiskerLeft (bunchedBimonoidAWordPow 1)
    (CellExpr.whiskerRight bunchedBimonoidYangBaxterLeftLeg (bunchedBimonoidAWordPow 0)))
#eval bunchedBimonoidEvalCell
  (CellExpr.whiskerLeft (bunchedBimonoidAWordPow 1)
    (CellExpr.whiskerRight bunchedBimonoidYangBaxterRightLeg (bunchedBimonoidAWordPow 0)))
#eval bunchedBimonoidEvalCell
  (CellExpr.whiskerLeft (bunchedBimonoidAWordPow 1)
    (CellExpr.whiskerRight bunchedBimonoidMuNaturalityLeftLeg (bunchedBimonoidAWordPow 0)))
#eval bunchedBimonoidEvalCell
  (CellExpr.whiskerLeft (bunchedBimonoidAWordPow 1)
    (CellExpr.whiskerRight bunchedBimonoidMuNaturalityRightLeg (bunchedBimonoidAWordPow 0)))

/-- ★ **THE YANG-BAXTER-AT-POSITION LEFT ENDPOINT IS `I_1 (+) reversal`** (width 4, `rfl`).  Firing `s_1 s_2 s_1`
at pad `(a^1, a^0)` lands the reversal in the bottom `3 x 3` block, fixing the padded top strand:
`[[1,0,0,0],[0,0,0,1],[0,0,1,0],[0,1,0,0]]`.  The block-offset the recursion relies on, machine-checked. -/
theorem bunchedBimonoidYangBaxterAtPositionOneZeroLeftMatrix :
    bunchedBimonoidEvalCell
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow 1)
        (CellExpr.whiskerRight bunchedBimonoidYangBaxterLeftLeg (bunchedBimonoidAWordPow 0)))
      = { rows := 4, cols := 4, entries := [[1, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0]] } := rfl

/-- ★★ **THE YANG-BAXTER-AT-POSITION MOVE IS MATRIX-SOUND (both endpoints share their matrix)** — `evalCell
(fired-left) = evalCell (fired-right)` at pad `(a^1, a^0)`, `rfl`.  So the position-generic braid move genuinely
relates two representatives of the same permutation, in the padded block — not a vacuous relation. -/
theorem bunchedBimonoidYangBaxterAtPositionOneZeroMatrixShared :
    bunchedBimonoidEvalCell
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow 1)
        (CellExpr.whiskerRight bunchedBimonoidYangBaxterLeftLeg (bunchedBimonoidAWordPow 0)))
      = bunchedBimonoidEvalCell
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow 1)
        (CellExpr.whiskerRight bunchedBimonoidYangBaxterRightLeg (bunchedBimonoidAWordPow 0))) := rfl

/-- ★★ **THE MU-NATURALITY-SLIDE-AT-POSITION MOVE IS MATRIX-SOUND** — `evalCell (fired-left) = evalCell
(fired-right)` at pad `(a^1, a^0)`, `rfl`.  The generic-position mu slide relates two cells with the same `3 x 4`
map (`I_1 (+) [[0,1,1],[1,0,0]]`) — gate (a) is a genuine, non-vacuous CONV. -/
theorem bunchedBimonoidMuNaturalitySlideAtPositionOneZeroMatrixShared :
    bunchedBimonoidEvalCell
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow 1)
        (CellExpr.whiskerRight bunchedBimonoidMuNaturalityLeftLeg (bunchedBimonoidAWordPow 0)))
      = bunchedBimonoidEvalCell
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow 1)
        (CellExpr.whiskerRight bunchedBimonoidMuNaturalityRightLeg (bunchedBimonoidAWordPow 0))) := rfl

/-- ★ **THE COMMUTATIVITY-AT-POSITION MOVE IS MATRIX-SOUND** — `evalCell (fired-left) = evalCell (fired-right)`
at pad `(a^1, a^0)`, `rfl` (width 3 source).  A double-coset generator relating two equal-matrix cells at an
offset. -/
theorem bunchedBimonoidCommutativityAtPositionOneZeroMatrixShared :
    bunchedBimonoidEvalCell
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow 1)
        (CellExpr.whiskerRight bunchedBimonoidCommutativityLeftLeg (bunchedBimonoidAWordPow 0)))
      = bunchedBimonoidEvalCell
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow 1)
        (CellExpr.whiskerRight bunchedBimonoidCommutativityRightLeg (bunchedBimonoidAWordPow 0))) := rfl

/-! # =========================================================================================
    # L2 — THE MARKERS + THE HONEST NO-FLIP LEDGER
    # =========================================================================================
-/

/-- ★★ **ESTABLISHED (L1) — the position-generic firing combinator is shipped.**  `= true` records
`bunchedBimonoidFireAtPosition`: any base convertibility over the star scope is fired inside a
`whiskerLeft leftPad (whiskerRight _ rightPad)` frame by composing the two one-hole congruences of
`SaturatedConvOverWithId`.  Non-recursive, whnf-free (pure congruence-constructor plumbing, no matrix eval), the
cell library atom for the wide-collision recursion's generic-width slide. -/
def fxBunchedBimonoid_fireBaseMoveAtPositionShipped : Bool := true

/-- ★★ **ESTABLISHED (L2) — the seven shipped base moves are firable at generic position.**  `= true` records
`bunchedBimonoid{YangBaxter,Involution,DistantSwap,Commutativity,Cocommutativity}AtPosition` (the five Coxeter /
double-coset moves) and `bunchedBimonoid{Mu,Delta}NaturalitySlideAtPosition` (the two naturality slides), each a
single `bunchedBimonoidFireAtPosition` application over arbitrary pads, matrix-soundness pinned at pad `(a^1,
a^0)` by `rfl`.  The complete r7 move set (`bunchedBimonoidCoxeterMovesAllInScope`) lifted from fixed small width
to generic position. -/
def fxBunchedBimonoid_sevenMovesFirableAtGenericPosition : Bool := true

/-- ★★★ **ESTABLISHED (L2) — the wide-collision recursion's gate (a) [the generic-width naturality slide] is
DELIVERED.**  `= true` records `bunchedBimonoid{Mu,Delta}NaturalitySlideAtPosition`: the width-3
`bunchedBimonoid{Mu,Delta}NaturalitySlideConv` whiskered by the one-hole congruences to an arbitrary
pad-position, a CONV over the star scope, matrix-sound (`...MuNaturalitySlideAtPositionOneZeroMatrixShared`).
This is EXACTLY the (a) lemma the r8 `fxBunchedBimonoid_wideCollisionConvGatedOnGenericNaturality` named — the
generic-width slide the `(m,n)` double induction threads.  It does NOT close the recursion (gate (b) Coxeter + the
induction glue remain — the next marker); it delivers one of the two named gates. -/
def fxBunchedBimonoid_genericPositionNaturalitySlideShipped : Bool := true

/-- ★ **THE `(m,n)` WIDE-COLLISION CONV RECURSION STAYS GATED — no flip (exact residual named).**  `= false`
records that after gate (a) [the generic-position naturality slide, DELIVERED above] the full double induction
`wideCollision m n ~ bialgebraNF m n` over the star scope is STILL NOT shipped: it remains gated on (b) the B3
general `CoxeterWordUnique` (two `permWord`s of one matrix convertible — walled at
`fxBunchedBimonoid_coxeterWordUniqueGatedOnGenericBraid`, r8) AND on the induction GLUE assembling the r7 peel
lemmas (`bunchedBimonoid{MuFold,DeltaFan}Peel`) + the width-2 brick (`bunchedBimonoidWidthTwoCollisionConv`) + the
gate-(a) slide (this file) + `whiskerRightFunctorial` reassociation into a STRUCTURAL `(m,n)` recursion — the
Coxeter-free `collisionCanonForm` retarget the recon named, not built here.  The upstream markers
`fxBunchedBimonoid_wideCollisionConvGatedOnGenericNaturality` (r8) and
`fxBunchedBimonoid_wideCollisionConvRecursionUnbuilt` (r6) stay `= false` byte-intact (cross-file, not edited);
this round narrows their denotation from "gated on (a)+(b)" to "gated on (b) + glue" — gate (a) is off the list. -/
def fxBunchedBimonoid_wideCollisionRecursionStillGatedOnCoxeterAndGlue : Bool := false

/-- ★ **THE CORRECTED WELL-TYPED STAR STAYS OPEN — no flip (byte-intact, cross-file).**  `= false` records that
`bunchedBimonoidStarStatementAdditiveWellTyped` is STILL NOT proven in r9: no literal hypothesis-free inhabitant
is produced (the star's `vcomp` case needs the walled wide-collision recursion, its equal-matrices middle needs
the walled `CoxeterWordUnique`).  The star-owning marker `fxBunchedBimonoid_correctedWellTypedStarStillOpen`
(StarAssembly, r7) and every upstream star marker keep their name and `= false` value byte-intact (cross-file,
not edited) — NO fabricated flip.  This round ships the position-generic move library (gate (a)), not the star. -/
def fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterPositionGeneric : Bool := false

/-- ★★★ **ESTABLISHED (L2) — the WP-PROP r9 position-generic-moves ledger (the honest scoreboard).**  `= true`
records the complete r9 cell-library round: L1 the position-generic firing combinator
(`fxBunchedBimonoid_fireBaseMoveAtPositionShipped` — fire any base move at an arbitrary pad, whnf-free); L2 the
seven shipped base moves lifted to generic position
(`fxBunchedBimonoid_sevenMovesFirableAtGenericPosition`), of which the two naturality slides DELIVER the
wide-collision recursion's gate (a) (`fxBunchedBimonoid_genericPositionNaturalitySlideShipped`).  The `(m,n)` CONV
recursion stays gated on gate (b) Coxeter + the induction glue
(`fxBunchedBimonoid_wideCollisionRecursionStillGatedOnCoxeterAndGlue = false`); the star does NOT flip
(`fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterPositionGeneric = false`).  Every upstream wall keeps its
name and value byte-intact (cross-file, gate (a) narrowed off the list, not flipped); zero-axiom (per-decl
`#assert_no_axioms` + independent `#print axioms` in the twin); STRUCTURAL only (no recursion added — pure
congruence plumbing).  NO fabricated star flip. -/
def fxBunchedBimonoid_positionGenericMovesRoundNineLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
