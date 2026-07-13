import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidBlockThreadingConv

/-! # Polygraph/Omega/WalkingBunchedBimonoidBlockThreadingConvGeneral — ★★★ THE B1 CONV BLOCK-THREADING
RECURSION IS DELIVERED IN FULL: both named generic-width statements inhabited at EVERY width, both colours
(WP-PROP r29, #2033)

★★★ **THE r28 WALL FALLS.**  The r27/r28 residual — the CONV half of the generic-width naturality slide,
`(a <| muFold k) ; sigma ~ strandPastBlock k ; (muFold k |> a)` as a STRUCTURAL induction on `k` — is proven for
ALL `k`, both colours: `bunchedBimonoidBlockThreadingConvStatementMuDelivered` and `...DeltaDelivered` inhabit
the r28-NAMED statements `bunchedBimonoidBlockThreadingConvStatement{Mu,Delta}`.  The three obstacles the r28
wall recorded (the `muFold` id-floor, the `a^{k+1}` word-power spelling, the `strandPastBlock` bracketing) all
dissolve:

  * **the id-floor** — widths `0` and `1` are their own bases: `1` is the shipped r28 collapse-to-`sigma`;
    `0` (the `eta` / `eps` block) closes by the `sigmaEtaNaturality` / `sigmaEpsNaturality` sound rows plus the
    strict units, with `idCongr` bridging the `id a` vs `id (idOne . a)` boundary spellings;
  * **the word-power spelling** — the whiskering-1-cell congruences (`whisker{Left,Right}WhiskerCongr`,
    CongruenceWithId) let DIMENSION-0 strict rows re-spell the whiskering words: the one-step rotation
    `a . a^k ~ a^k . a` (`bunchedBimonoidAWordPowRotateConv`), its left-nested sibling, and the left-nested vs
    right-nested identification (`bunchedBimonoidAWordPowLeftMatchesAWordPowConv`) are all plain
    `vcompAssoc`/`vcompUnit` inductions at the 1-cell level, lifted under the whisker;
  * **the bracketing** — the inductive step peels one `mu` (`muFoldPeel`, `rfl`), fires the width-3 hexagon row,
    commutes the whiskered residual fold past the freed `sigma` with the GODEMENT INTERCHANGE row (the fold's
    boundary words computed by `bunchedBimonoid{MuFold,DeltaFan}Boundary{Source,Target}Is*`), threads the
    induction hypothesis under `whiskerRightCongr`, and re-brackets with `whiskerAssocRight` /
    `whiskerLeftRightCommute` / `whiskerAssocLeft` (the r19 rows) — the mu side additionally re-spells
    `strandPastBlock (k+2)` back-first (`bunchedBimonoidStrandPastBlockPeelBackConv`, its own structural
    induction).

Everything is congruence-constructor plumbing over the star scope — NO wide `rfl`, NO kernel matrix evaluation
(the r27 soundness half already checked the matrices; this file is the pure CONV half).

## Supersessions (new-file content markers; every frozen file byte-intact)

  * r28 `fxBunchedBimonoid_blockThreadingConvGeneralStepStillWalled = false` → SUPERSEDED by
    `fxBunchedBimonoid_blockThreadingConvGeneralStepDelivered = true` (the general step is proven).
  * r27 `fxBunchedBimonoid_genericWidthConvBlockThreadingStillWalled = false` → SUPERSEDED by
    `fxBunchedBimonoid_genericWidthConvBlockThreadingDelivered = true`.
  * The r8 gated marker `fxBunchedBimonoid_wideCollisionConvGatedOnGenericNaturality` does NOT flip: its bill
    demands the full `wideSwap(m,n)` riffle recursion AND the `CoxeterWordUnique` bubble-sort — the
    block-threading here is gate (b) of that bill only.  The #2033 star was DECIDED FALSE in the r29 sibling
    (`StarColourMislabelRefutation`); the corrected dim-2 placement-guarded target consumes THIS file as its
    `vcomp`-case engine.

Raw Lean 4 + Init; STRUCTURAL recursion only (the `k+2` arms recurse on `k+1`); ASCII-only.  Per-declaration
`#assert_no_axioms` AND independent `#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # B1 — THE LEFT-NESTED WORD POWER AND THE FOLD/FAN BOUNDARY CENSUS
    # =========================================================================================
-/

/-- The **left-nested additive word power** — `0` the empty word, `1` the bare colour, `k+2` appends one colour
on the RIGHT of the left-nested `(…(a.a)…).a`.  This is exactly the spelling `boundarySource` produces on
`muFold` (and `boundaryTarget` on `deltaFan`); the shipped `bunchedBimonoidAWordPow` is the RIGHT-nested
spelling with the `idOne` floor.  The two are identified as a CONV below. -/
def bunchedBimonoidAWordPowLeft : Nat → CellExpr bunchedBimonoidOmegaComputad 1
  | 0 => bunchedBimonoidIdOne
  | 1 => bunchedBimonoidAdditiveGen
  | k + 2 => CellExpr.vcomp (bunchedBimonoidAWordPowLeft (k + 1)) bunchedBimonoidAdditiveGen

/-- The mu-fold's declared SOURCE word is the left-nested power (structural induction; the `k+2` layer is
`congrArg` under one appended colour). -/
theorem bunchedBimonoidMuFoldBoundarySourceIsLeftPow :
    ∀ (blockWidth : Nat),
      boundarySource (bunchedBimonoidMuFold (blockWidth + 1)) = bunchedBimonoidAWordPowLeft (blockWidth + 1)
  | 0 => rfl
  | k + 1 =>
      congrArg (fun word => CellExpr.vcomp word bunchedBimonoidAdditiveGen)
        (bunchedBimonoidMuFoldBoundarySourceIsLeftPow k)

/-- The mu-fold's declared TARGET is the bare colour (two-case split on the id-floor vs the peel layer). -/
theorem bunchedBimonoidMuFoldBoundaryTargetIsColour :
    ∀ (blockWidth : Nat),
      boundaryTarget (bunchedBimonoidMuFold (blockWidth + 1)) = bunchedBimonoidAdditiveGen
  | 0 => rfl
  | _ + 1 => rfl

/-- The delta-fan's declared SOURCE is the bare colour (dual two-case split). -/
theorem bunchedBimonoidDeltaFanBoundarySourceIsColour :
    ∀ (blockWidth : Nat),
      boundarySource (bunchedBimonoidDeltaFan (blockWidth + 1)) = bunchedBimonoidAdditiveGen
  | 0 => rfl
  | _ + 1 => rfl

/-- The delta-fan's declared TARGET word is the left-nested power (the dual census). -/
theorem bunchedBimonoidDeltaFanBoundaryTargetIsLeftPow :
    ∀ (blockWidth : Nat),
      boundaryTarget (bunchedBimonoidDeltaFan (blockWidth + 1)) = bunchedBimonoidAWordPowLeft (blockWidth + 1)
  | 0 => rfl
  | k + 1 =>
      congrArg (fun word => CellExpr.vcomp word bunchedBimonoidAdditiveGen)
        (bunchedBimonoidDeltaFanBoundaryTargetIsLeftPow k)

/-! # =========================================================================================
    # B1 — THE 1-CELL WORD CONVs (dimension-0 strict rows re-spell the whiskering words)
    # =========================================================================================
-/

/-- `a . idOne ~ a` — the dimension-0 `vcompUnitRight` row (the word power's `idOne` floor absorbs). -/
theorem bunchedBimonoidWordUnitRightConv :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp bunchedBimonoidAdditiveGen bunchedBimonoidIdOne) bunchedBimonoidAdditiveGen :=
  bunchedBimonoidStrictAxiomEmbedsIntoStarScope (StrictAxiomRel.vcompUnitRight bunchedBimonoidAdditiveGen)

/-- `idOne . a ~ a` — the dimension-0 `vcompUnitLeft` row. -/
theorem bunchedBimonoidWordUnitLeftConv :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp bunchedBimonoidIdOne bunchedBimonoidAdditiveGen) bunchedBimonoidAdditiveGen :=
  bunchedBimonoidStrictAxiomEmbedsIntoStarScope (StrictAxiomRel.vcompUnitLeft bunchedBimonoidAdditiveGen)

/-- ★ **The one-step word rotation** `a . a^k ~ a^k . a` (right-nested powers) — the prepended colour migrates
to an appended colour by dimension-0 units (base) and associativity (step).  The 1-cell fact the whiskering
positions consume through `whiskerRightWhiskerCongr`. -/
theorem bunchedBimonoidAWordPowRotateConv :
    ∀ (wordWidth : Nat),
      SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
        (CellExpr.vcomp bunchedBimonoidAdditiveGen (bunchedBimonoidAWordPow wordWidth))
        (CellExpr.vcomp (bunchedBimonoidAWordPow wordWidth) bunchedBimonoidAdditiveGen)
  | 0 => SaturatedConvOverWithId.trans bunchedBimonoidWordUnitRightConv
      (SaturatedConvOverWithId.symm bunchedBimonoidWordUnitLeftConv)
  | k + 1 =>
      SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrRight bunchedBimonoidAdditiveGen
          (bunchedBimonoidAWordPowRotateConv k))
        (SaturatedConvOverWithId.symm
          (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
            (StrictAxiomRel.vcompAssoc bunchedBimonoidAdditiveGen (bunchedBimonoidAWordPow k)
              bunchedBimonoidAdditiveGen)))

/-- The left-nested sibling rotation `a . leftPow (k+1) ~ leftPow (k+2)` (which is `leftPow (k+1) . a` on the
nose). -/
theorem bunchedBimonoidAWordPowLeftRotateConv :
    ∀ (wordWidth : Nat),
      SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
        (CellExpr.vcomp bunchedBimonoidAdditiveGen (bunchedBimonoidAWordPowLeft (wordWidth + 1)))
        (bunchedBimonoidAWordPowLeft (wordWidth + 2))
  | 0 => SaturatedConvOverWithId.refl
      (CellExpr.vcomp bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen)
  | k + 1 =>
      SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.symm
          (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
            (StrictAxiomRel.vcompAssoc bunchedBimonoidAdditiveGen (bunchedBimonoidAWordPowLeft (k + 1))
              bunchedBimonoidAdditiveGen)))
        (SaturatedConvOverWithId.vcompCongrLeft bunchedBimonoidAdditiveGen
          (bunchedBimonoidAWordPowLeftRotateConv k))

/-- ★ **The left-nested and right-nested word powers are convertible** — `leftPow (k+1) ~ a^{k+1}`.  The
boundary-census spelling meets the `strandPastBlock` spelling; the delta side consumes this under
`whiskerLeftWhiskerCongr`. -/
theorem bunchedBimonoidAWordPowLeftMatchesAWordPowConv :
    ∀ (wordWidth : Nat),
      SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
        (bunchedBimonoidAWordPowLeft (wordWidth + 1)) (bunchedBimonoidAWordPow (wordWidth + 1))
  | 0 => SaturatedConvOverWithId.symm bunchedBimonoidWordUnitRightConv
  | k + 1 =>
      SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.symm (bunchedBimonoidAWordPowLeftRotateConv k))
        (SaturatedConvOverWithId.vcompCongrRight bunchedBimonoidAdditiveGen
          (bunchedBimonoidAWordPowLeftMatchesAWordPowConv k))

/-! # =========================================================================================
    # B1 — THE BACK-FIRST RESPELLING OF THE FORWARD BLOCK BRAIDING
    # =========================================================================================
-/

/-- ★★ **The back-first respelling** — `strandPastBlock (k+2) ~ (strandPastBlock (k+1) |> a) ;
(leftPow (k+1) <| sigma)`: the front-first cyclic-shift word (swap first, then thread under the fixed front
strand) re-spells as "thread past the first `k+1` strands, then swap with the LAST strand under the fixed
left-nested block".  Structural induction: the base re-spells the `a^1` whisker by the unit row; the step
distributes the IH under `a <| _`, commutes with `whiskerLeftRightCommute`, re-brackets the whiskering words
with `whiskerAssocLeft` / `whiskerAssocRight` and the rotations, and re-merges with `whiskerRightFunctorial`.
This is the mu-side bracketing bridge the r28 wall named. -/
theorem bunchedBimonoidStrandPastBlockPeelBackConv :
    ∀ (blockWidth : Nat),
      SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
        (bunchedBimonoidStrandPastBlock (blockWidth + 2))
        (CellExpr.vcomp
          (CellExpr.whiskerRight (bunchedBimonoidStrandPastBlock (blockWidth + 1)) bunchedBimonoidAdditiveGen)
          (CellExpr.whiskerLeft (bunchedBimonoidAWordPowLeft (blockWidth + 1)) bunchedBimonoidAddSigmaGen))
  | 0 =>
      SaturatedConvOverWithId.vcompCongrLeft
        (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)
        (SaturatedConvOverWithId.whiskerRightWhiskerCongr bunchedBimonoidAddSigmaGen
          bunchedBimonoidWordUnitRightConv)
  | k + 1 => by
      have distributeInductionHypothesis :
          SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
            (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen (bunchedBimonoidStrandPastBlock (k + 2)))
            (CellExpr.vcomp
              (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
                (CellExpr.whiskerRight (bunchedBimonoidStrandPastBlock (k + 1)) bunchedBimonoidAdditiveGen))
              (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
                (CellExpr.whiskerLeft (bunchedBimonoidAWordPowLeft (k + 1)) bunchedBimonoidAddSigmaGen))) :=
        SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.whiskerLeftCongr bunchedBimonoidAdditiveGen
            (bunchedBimonoidStrandPastBlockPeelBackConv k))
          (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
            (StrictAxiomRel.whiskerLeftFunctorial bunchedBimonoidAdditiveGen
              (CellExpr.whiskerRight (bunchedBimonoidStrandPastBlock (k + 1)) bunchedBimonoidAdditiveGen)
              (CellExpr.whiskerLeft (bunchedBimonoidAWordPowLeft (k + 1)) bunchedBimonoidAddSigmaGen)))
      have reshapeBothFactors :
          SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
            (CellExpr.vcomp
              (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
                (CellExpr.whiskerRight (bunchedBimonoidStrandPastBlock (k + 1)) bunchedBimonoidAdditiveGen))
              (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
                (CellExpr.whiskerLeft (bunchedBimonoidAWordPowLeft (k + 1)) bunchedBimonoidAddSigmaGen)))
            (CellExpr.vcomp
              (CellExpr.whiskerRight
                (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen (bunchedBimonoidStrandPastBlock (k + 1)))
                bunchedBimonoidAdditiveGen)
              (CellExpr.whiskerLeft
                (CellExpr.vcomp bunchedBimonoidAdditiveGen (bunchedBimonoidAWordPowLeft (k + 1)))
                bunchedBimonoidAddSigmaGen)) :=
        SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.vcompCongrLeft
            (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
              (CellExpr.whiskerLeft (bunchedBimonoidAWordPowLeft (k + 1)) bunchedBimonoidAddSigmaGen))
            (SaturatedConvOverWithId.symm
              (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                (StrictAxiomRel.whiskerLeftRightCommute bunchedBimonoidAdditiveGen
                  (bunchedBimonoidStrandPastBlock (k + 1)) bunchedBimonoidAdditiveGen))))
          (SaturatedConvOverWithId.vcompCongrRight
            (CellExpr.whiskerRight
              (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen (bunchedBimonoidStrandPastBlock (k + 1)))
              bunchedBimonoidAdditiveGen)
            (SaturatedConvOverWithId.symm
              (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                (StrictAxiomRel.whiskerAssocLeft bunchedBimonoidAdditiveGen
                  (bunchedBimonoidAWordPowLeft (k + 1)) bunchedBimonoidAddSigmaGen))))
      have rotateFrontWhisker :
          SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
            (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow (k + 2)))
            (CellExpr.whiskerRight
              (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow (k + 1)))
              bunchedBimonoidAdditiveGen) :=
        SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.whiskerRightWhiskerCongr bunchedBimonoidAddSigmaGen
            (bunchedBimonoidAWordPowRotateConv (k + 1)))
          (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
            (StrictAxiomRel.whiskerAssocRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow (k + 1))
              bunchedBimonoidAdditiveGen))
      exact
        SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.vcompCongrRight
            (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow (k + 2)))
            (SaturatedConvOverWithId.trans distributeInductionHypothesis reshapeBothFactors))
          (SaturatedConvOverWithId.trans
            (SaturatedConvOverWithId.vcompCongrLeft
              (CellExpr.vcomp
                (CellExpr.whiskerRight
                  (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen (bunchedBimonoidStrandPastBlock (k + 1)))
                  bunchedBimonoidAdditiveGen)
                (CellExpr.whiskerLeft
                  (CellExpr.vcomp bunchedBimonoidAdditiveGen (bunchedBimonoidAWordPowLeft (k + 1)))
                  bunchedBimonoidAddSigmaGen))
              rotateFrontWhisker)
            (SaturatedConvOverWithId.trans
              (SaturatedConvOverWithId.symm
                (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                  (StrictAxiomRel.vcompAssoc
                    (CellExpr.whiskerRight
                      (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow (k + 1)))
                      bunchedBimonoidAdditiveGen)
                    (CellExpr.whiskerRight
                      (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
                        (bunchedBimonoidStrandPastBlock (k + 1)))
                      bunchedBimonoidAdditiveGen)
                    (CellExpr.whiskerLeft
                      (CellExpr.vcomp bunchedBimonoidAdditiveGen (bunchedBimonoidAWordPowLeft (k + 1)))
                      bunchedBimonoidAddSigmaGen))))
              (SaturatedConvOverWithId.trans
                (SaturatedConvOverWithId.vcompCongrLeft
                  (CellExpr.whiskerLeft
                    (CellExpr.vcomp bunchedBimonoidAdditiveGen (bunchedBimonoidAWordPowLeft (k + 1)))
                    bunchedBimonoidAddSigmaGen)
                  (SaturatedConvOverWithId.symm
                    (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                      (StrictAxiomRel.whiskerRightFunctorial
                        (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow (k + 1)))
                        (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
                          (bunchedBimonoidStrandPastBlock (k + 1)))
                        bunchedBimonoidAdditiveGen))))
                (SaturatedConvOverWithId.vcompCongrRight
                  (CellExpr.whiskerRight (bunchedBimonoidStrandPastBlock (k + 2)) bunchedBimonoidAdditiveGen)
                  (SaturatedConvOverWithId.whiskerLeftWhiskerCongr bunchedBimonoidAddSigmaGen
                    (bunchedBimonoidAWordPowLeftRotateConv k))))))

/-! # =========================================================================================
    # B1 — THE mu-SIDE GENERAL RECURSION (all widths)
    # =========================================================================================
-/

/-- The width-0 mu base: `(a <| eta) ; sigma ~ (id a) ; (eta |> a)`.  The left leg is EXACTLY the
`sigmaEtaNaturality` sound row; the right leg's `id a` absorbs into the unit row after `idCongr` bridges the
`a` vs `idOne . a` boundary spellings. -/
theorem bunchedBimonoidBlockThreadingConvBaseMuZero :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidSigmaPastMuFoldBlockLeft 0) (bunchedBimonoidSigmaPastMuFoldBlockRight 0) :=
  SaturatedConvOverWithId.trans
    (bunchedBimonoidSoundRowEmbedsIntoStarScope BunchedBimonoidSoundRow.sigmaEtaNaturality)
    (SaturatedConvOverWithId.symm
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrLeft
          (CellExpr.whiskerRight bunchedBimonoidAddEtaGen bunchedBimonoidAdditiveGen)
          (SaturatedConvOverWithId.idCongr
            (SaturatedConvOverWithId.symm bunchedBimonoidWordUnitLeftConv)))
        (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
          (StrictAxiomRel.vcompUnitLeft
            (CellExpr.whiskerRight bunchedBimonoidAddEtaGen bunchedBimonoidAdditiveGen)))))

/-- ★★★ **THE mu-SIDE CONV BLOCK-THREADING, ALL WIDTHS** — `(a <| muFold k) ; sigma ~ strandPastBlock k ;
(muFold k |> a)` over the star scope for EVERY `k`, by structural recursion: width 0 and 1 are the bases; the
`k+2` step peels one `mu`, fires the width-3 hexagon, commutes the residual fold past the freed `sigma` by the
interchange row (boundary words rewritten by the census), threads the IH under the right whisker, and closes
with the back-first respelling.  The r27/r28 walled CONV half, proven. -/
theorem bunchedBimonoidSigmaPastMuFoldBlockThreadConv :
    ∀ (blockWidth : Nat),
      SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
        (bunchedBimonoidSigmaPastMuFoldBlockLeft blockWidth)
        (bunchedBimonoidSigmaPastMuFoldBlockRight blockWidth)
  | 0 => bunchedBimonoidBlockThreadingConvBaseMuZero
  | 1 => bunchedBimonoidBlockThreadingConvBaseMu
  | k + 2 => by
      -- the interchange row with the fold's boundary words rewritten by the census
      have interchangeRow :=
        bunchedBimonoidStrictAxiomEmbedsIntoStarScope
          (StrictAxiomRel.interchange (bunchedBimonoidMuFold (k + 1)) bunchedBimonoidAddSigmaGen)
      rw [bunchedBimonoidMuFoldBoundaryTargetIsColour k, bunchedBimonoidMuFoldBoundarySourceIsLeftPow k]
        at interchangeRow
      -- peel one mu, fire the hexagon, and expose the front pair
      have peelAndFireHexagon :
          SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
            (bunchedBimonoidSigmaPastMuFoldBlockLeft (k + 2))
            (CellExpr.vcomp
              (CellExpr.vcomp
                (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
                  (CellExpr.whiskerRight (bunchedBimonoidMuFold (k + 1)) bunchedBimonoidAdditiveGen))
                (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen))
              (CellExpr.vcomp
                (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)
                (CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidAdditiveGen))) :=
        SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.vcompCongrLeft bunchedBimonoidAddSigmaGen
            (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
              (StrictAxiomRel.whiskerLeftFunctorial bunchedBimonoidAdditiveGen
                (CellExpr.whiskerRight (bunchedBimonoidMuFold (k + 1)) bunchedBimonoidAdditiveGen)
                bunchedBimonoidAddMuGen)))
          (SaturatedConvOverWithId.trans
            (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
              (StrictAxiomRel.vcompAssoc
                (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
                  (CellExpr.whiskerRight (bunchedBimonoidMuFold (k + 1)) bunchedBimonoidAdditiveGen))
                (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddMuGen)
                bunchedBimonoidAddSigmaGen))
            (SaturatedConvOverWithId.trans
              (SaturatedConvOverWithId.vcompCongrRight
                (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
                  (CellExpr.whiskerRight (bunchedBimonoidMuFold (k + 1)) bunchedBimonoidAdditiveGen))
                (SaturatedConvOverWithId.trans
                  (bunchedBimonoidHexagonRowEmbedsIntoStarScope BunchedBimonoidHexagonRow.muNaturality)
                  (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                    (StrictAxiomRel.vcompAssoc
                      (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen)
                      (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)
                      (CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidAdditiveGen)))))
              (SaturatedConvOverWithId.symm
                (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                  (StrictAxiomRel.vcompAssoc
                    (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
                      (CellExpr.whiskerRight (bunchedBimonoidMuFold (k + 1)) bunchedBimonoidAdditiveGen))
                    (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen)
                    (CellExpr.vcomp
                      (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)
                      (CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidAdditiveGen)))))))
      -- the front pair: commute the whiskers, merge, thread the IH, split back
      have threadInductionThroughFront :
          SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
            (CellExpr.vcomp
              (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
                (CellExpr.whiskerRight (bunchedBimonoidMuFold (k + 1)) bunchedBimonoidAdditiveGen))
              (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen))
            (CellExpr.vcomp
              (CellExpr.whiskerRight (bunchedBimonoidStrandPastBlock (k + 1)) bunchedBimonoidAdditiveGen)
              (CellExpr.whiskerRight
                (CellExpr.whiskerRight (bunchedBimonoidMuFold (k + 1)) bunchedBimonoidAdditiveGen)
                bunchedBimonoidAdditiveGen)) :=
        SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.vcompCongrLeft
            (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen)
            (SaturatedConvOverWithId.symm
              (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                (StrictAxiomRel.whiskerLeftRightCommute bunchedBimonoidAdditiveGen
                  (bunchedBimonoidMuFold (k + 1)) bunchedBimonoidAdditiveGen))))
          (SaturatedConvOverWithId.trans
            (SaturatedConvOverWithId.symm
              (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                (StrictAxiomRel.whiskerRightFunctorial
                  (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen (bunchedBimonoidMuFold (k + 1)))
                  bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen)))
            (SaturatedConvOverWithId.trans
              (SaturatedConvOverWithId.whiskerRightCongr bunchedBimonoidAdditiveGen
                (bunchedBimonoidSigmaPastMuFoldBlockThreadConv (k + 1)))
              (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                (StrictAxiomRel.whiskerRightFunctorial (bunchedBimonoidStrandPastBlock (k + 1))
                  (CellExpr.whiskerRight (bunchedBimonoidMuFold (k + 1)) bunchedBimonoidAdditiveGen)
                  bunchedBimonoidAdditiveGen))))
      -- the interchange core: slide the doubly-whiskered fold past the freed middle sigma
      have slideFoldPastMiddleSigma :
          SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
            (CellExpr.vcomp
              (CellExpr.whiskerRight
                (CellExpr.whiskerRight (bunchedBimonoidMuFold (k + 1)) bunchedBimonoidAdditiveGen)
                bunchedBimonoidAdditiveGen)
              (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen))
            (CellExpr.vcomp
              (CellExpr.whiskerLeft (bunchedBimonoidAWordPowLeft (k + 1)) bunchedBimonoidAddSigmaGen)
              (CellExpr.whiskerRight
                (CellExpr.whiskerRight (bunchedBimonoidMuFold (k + 1)) bunchedBimonoidAdditiveGen)
                bunchedBimonoidAdditiveGen)) :=
        SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.vcompCongrLeft
            (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)
            (SaturatedConvOverWithId.symm
              (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                (StrictAxiomRel.whiskerAssocRight (bunchedBimonoidMuFold (k + 1)) bunchedBimonoidAdditiveGen
                  bunchedBimonoidAdditiveGen))))
          (SaturatedConvOverWithId.trans interchangeRow
            (SaturatedConvOverWithId.vcompCongrRight
              (CellExpr.whiskerLeft (bunchedBimonoidAWordPowLeft (k + 1)) bunchedBimonoidAddSigmaGen)
              (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                (StrictAxiomRel.whiskerAssocRight (bunchedBimonoidMuFold (k + 1)) bunchedBimonoidAdditiveGen
                  bunchedBimonoidAdditiveGen))))
      -- assemble
      exact
        SaturatedConvOverWithId.trans peelAndFireHexagon
          (SaturatedConvOverWithId.trans
            (SaturatedConvOverWithId.vcompCongrLeft
              (CellExpr.vcomp
                (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)
                (CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidAdditiveGen))
              threadInductionThroughFront)
            (SaturatedConvOverWithId.trans
              (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                (StrictAxiomRel.vcompAssoc
                  (CellExpr.whiskerRight (bunchedBimonoidStrandPastBlock (k + 1)) bunchedBimonoidAdditiveGen)
                  (CellExpr.whiskerRight
                    (CellExpr.whiskerRight (bunchedBimonoidMuFold (k + 1)) bunchedBimonoidAdditiveGen)
                    bunchedBimonoidAdditiveGen)
                  (CellExpr.vcomp
                    (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)
                    (CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidAdditiveGen))))
              (SaturatedConvOverWithId.trans
                (SaturatedConvOverWithId.vcompCongrRight
                  (CellExpr.whiskerRight (bunchedBimonoidStrandPastBlock (k + 1)) bunchedBimonoidAdditiveGen)
                  (SaturatedConvOverWithId.trans
                    (SaturatedConvOverWithId.symm
                      (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                        (StrictAxiomRel.vcompAssoc
                          (CellExpr.whiskerRight
                            (CellExpr.whiskerRight (bunchedBimonoidMuFold (k + 1))
                              bunchedBimonoidAdditiveGen)
                            bunchedBimonoidAdditiveGen)
                          (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)
                          (CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidAdditiveGen))))
                    (SaturatedConvOverWithId.trans
                      (SaturatedConvOverWithId.vcompCongrLeft
                        (CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidAdditiveGen)
                        slideFoldPastMiddleSigma)
                      (SaturatedConvOverWithId.trans
                        (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                          (StrictAxiomRel.vcompAssoc
                            (CellExpr.whiskerLeft (bunchedBimonoidAWordPowLeft (k + 1))
                              bunchedBimonoidAddSigmaGen)
                            (CellExpr.whiskerRight
                              (CellExpr.whiskerRight (bunchedBimonoidMuFold (k + 1))
                                bunchedBimonoidAdditiveGen)
                              bunchedBimonoidAdditiveGen)
                            (CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidAdditiveGen)))
                        (SaturatedConvOverWithId.vcompCongrRight
                          (CellExpr.whiskerLeft (bunchedBimonoidAWordPowLeft (k + 1))
                            bunchedBimonoidAddSigmaGen)
                          (SaturatedConvOverWithId.symm
                            (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                              (StrictAxiomRel.whiskerRightFunctorial
                                (CellExpr.whiskerRight (bunchedBimonoidMuFold (k + 1))
                                  bunchedBimonoidAdditiveGen)
                                bunchedBimonoidAddMuGen bunchedBimonoidAdditiveGen))))))))
                (SaturatedConvOverWithId.trans
                  (SaturatedConvOverWithId.symm
                    (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                      (StrictAxiomRel.vcompAssoc
                        (CellExpr.whiskerRight (bunchedBimonoidStrandPastBlock (k + 1))
                          bunchedBimonoidAdditiveGen)
                        (CellExpr.whiskerLeft (bunchedBimonoidAWordPowLeft (k + 1))
                          bunchedBimonoidAddSigmaGen)
                        (CellExpr.whiskerRight (bunchedBimonoidMuFold (k + 2)) bunchedBimonoidAdditiveGen))))
                  (SaturatedConvOverWithId.vcompCongrLeft
                    (CellExpr.whiskerRight (bunchedBimonoidMuFold (k + 2)) bunchedBimonoidAdditiveGen)
                    (SaturatedConvOverWithId.symm
                      (bunchedBimonoidStrandPastBlockPeelBackConv k)))))))

/-! # =========================================================================================
    # B1 — THE delta-SIDE GENERAL RECURSION (all widths)
    # =========================================================================================
-/

/-- The width-0 delta base: `sigma ; (a <| eps) ~ (eps |> a) ; (id a)`.  The left leg re-spells through the
`sigmaEpsNaturality` sound row and the `sigmaInvolution` row; the right leg's trailing `id a` absorbs into the
unit row after the `idCongr` bridge. -/
theorem bunchedBimonoidBlockThreadingConvBaseDeltaZero :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidSigmaPastDeltaFanBlockLeft 0) (bunchedBimonoidSigmaPastDeltaFanBlockRight 0) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrRight bunchedBimonoidAddSigmaGen
          (SaturatedConvOverWithId.symm
            (bunchedBimonoidSoundRowEmbedsIntoStarScope BunchedBimonoidSoundRow.sigmaEpsNaturality)))
        (SaturatedConvOverWithId.symm
          (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
            (StrictAxiomRel.vcompAssoc bunchedBimonoidAddSigmaGen bunchedBimonoidAddSigmaGen
              (CellExpr.whiskerRight bunchedBimonoidAddEpsGen bunchedBimonoidAdditiveGen)))))
      (SaturatedConvOverWithId.vcompCongrLeft
        (CellExpr.whiskerRight bunchedBimonoidAddEpsGen bunchedBimonoidAdditiveGen)
        (bunchedBimonoidSoundRowEmbedsIntoStarScope BunchedBimonoidSoundRow.sigmaInvolution)))
    (SaturatedConvOverWithId.trans
      (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
        (StrictAxiomRel.vcompUnitLeft
          (CellExpr.whiskerRight bunchedBimonoidAddEpsGen bunchedBimonoidAdditiveGen)))
      (SaturatedConvOverWithId.symm
        (SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.vcompCongrRight
            (CellExpr.whiskerRight bunchedBimonoidAddEpsGen bunchedBimonoidAdditiveGen)
            (SaturatedConvOverWithId.idCongr
              (SaturatedConvOverWithId.symm bunchedBimonoidWordUnitLeftConv)))
          (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
            (StrictAxiomRel.vcompUnitRight
              (CellExpr.whiskerRight bunchedBimonoidAddEpsGen bunchedBimonoidAdditiveGen))))))

/-- ★★★ **THE delta-SIDE CONV BLOCK-THREADING, ALL WIDTHS** — `sigma ; (a <| deltaFan k) ~ (deltaFan k |> a) ;
strandPastBlockRev k` over the star scope for EVERY `k`, the dual recursion: peel one `delta`, fire the dual
hexagon, thread the IH, slide the doubly-whiskered fan past the middle `sigma` by the interchange row, and
re-spell the whiskering word left-to-right-nested.  No back-first respelling is needed — the REVERSE braiding's
own recursion already matches the interchange output. -/
theorem bunchedBimonoidSigmaPastDeltaFanBlockThreadConv :
    ∀ (blockWidth : Nat),
      SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
        (bunchedBimonoidSigmaPastDeltaFanBlockLeft blockWidth)
        (bunchedBimonoidSigmaPastDeltaFanBlockRight blockWidth)
  | 0 => bunchedBimonoidBlockThreadingConvBaseDeltaZero
  | 1 => bunchedBimonoidBlockThreadingConvBaseDelta
  | k + 2 => by
      have interchangeRow :=
        bunchedBimonoidStrictAxiomEmbedsIntoStarScope
          (StrictAxiomRel.interchange (bunchedBimonoidDeltaFan (k + 1)) bunchedBimonoidAddSigmaGen)
      rw [bunchedBimonoidDeltaFanBoundaryTargetIsLeftPow k, bunchedBimonoidDeltaFanBoundarySourceIsColour k]
        at interchangeRow
      -- peel one delta, fire the dual hexagon, expose the back pair
      have peelAndFireDualHexagon :
          SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
            (bunchedBimonoidSigmaPastDeltaFanBlockLeft (k + 2))
            (CellExpr.vcomp
              (CellExpr.whiskerRight bunchedBimonoidAddDeltaGen bunchedBimonoidAdditiveGen)
              (CellExpr.vcomp
                (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)
                (CellExpr.vcomp
                  (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen)
                  (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
                    (CellExpr.whiskerRight (bunchedBimonoidDeltaFan (k + 1)) bunchedBimonoidAdditiveGen))))) :=
        SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.vcompCongrRight bunchedBimonoidAddSigmaGen
            (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
              (StrictAxiomRel.whiskerLeftFunctorial bunchedBimonoidAdditiveGen bunchedBimonoidAddDeltaGen
                (CellExpr.whiskerRight (bunchedBimonoidDeltaFan (k + 1)) bunchedBimonoidAdditiveGen))))
          (SaturatedConvOverWithId.trans
            (SaturatedConvOverWithId.symm
              (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                (StrictAxiomRel.vcompAssoc bunchedBimonoidAddSigmaGen
                  (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddDeltaGen)
                  (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
                    (CellExpr.whiskerRight (bunchedBimonoidDeltaFan (k + 1)) bunchedBimonoidAdditiveGen)))))
            (SaturatedConvOverWithId.trans
              (SaturatedConvOverWithId.vcompCongrLeft
                (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
                  (CellExpr.whiskerRight (bunchedBimonoidDeltaFan (k + 1)) bunchedBimonoidAdditiveGen))
                (bunchedBimonoidHexagonRowEmbedsIntoStarScope BunchedBimonoidHexagonRow.deltaNaturality))
              (SaturatedConvOverWithId.trans
                (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                  (StrictAxiomRel.vcompAssoc
                    (CellExpr.whiskerRight bunchedBimonoidAddDeltaGen bunchedBimonoidAdditiveGen)
                    (CellExpr.vcomp
                      (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)
                      (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen))
                    (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
                      (CellExpr.whiskerRight (bunchedBimonoidDeltaFan (k + 1)) bunchedBimonoidAdditiveGen))))
                (SaturatedConvOverWithId.vcompCongrRight
                  (CellExpr.whiskerRight bunchedBimonoidAddDeltaGen bunchedBimonoidAdditiveGen)
                  (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                    (StrictAxiomRel.vcompAssoc
                      (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)
                      (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen)
                      (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
                        (CellExpr.whiskerRight (bunchedBimonoidDeltaFan (k + 1))
                          bunchedBimonoidAdditiveGen))))))))
      -- the back pair: commute the whiskers, merge, thread the IH, split back
      have threadInductionThroughBack :
          SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
            (CellExpr.vcomp
              (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen)
              (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
                (CellExpr.whiskerRight (bunchedBimonoidDeltaFan (k + 1)) bunchedBimonoidAdditiveGen)))
            (CellExpr.vcomp
              (CellExpr.whiskerRight
                (CellExpr.whiskerRight (bunchedBimonoidDeltaFan (k + 1)) bunchedBimonoidAdditiveGen)
                bunchedBimonoidAdditiveGen)
              (CellExpr.whiskerRight (bunchedBimonoidStrandPastBlockRev (k + 1))
                bunchedBimonoidAdditiveGen)) :=
        SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.vcompCongrRight
            (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen)
            (SaturatedConvOverWithId.symm
              (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                (StrictAxiomRel.whiskerLeftRightCommute bunchedBimonoidAdditiveGen
                  (bunchedBimonoidDeltaFan (k + 1)) bunchedBimonoidAdditiveGen))))
          (SaturatedConvOverWithId.trans
            (SaturatedConvOverWithId.symm
              (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                (StrictAxiomRel.whiskerRightFunctorial bunchedBimonoidAddSigmaGen
                  (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen (bunchedBimonoidDeltaFan (k + 1)))
                  bunchedBimonoidAdditiveGen)))
            (SaturatedConvOverWithId.trans
              (SaturatedConvOverWithId.whiskerRightCongr bunchedBimonoidAdditiveGen
                (bunchedBimonoidSigmaPastDeltaFanBlockThreadConv (k + 1)))
              (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                (StrictAxiomRel.whiskerRightFunctorial
                  (CellExpr.whiskerRight (bunchedBimonoidDeltaFan (k + 1)) bunchedBimonoidAdditiveGen)
                  (bunchedBimonoidStrandPastBlockRev (k + 1)) bunchedBimonoidAdditiveGen))))
      -- the interchange core: slide the middle sigma past the doubly-whiskered fan
      have slideMiddleSigmaPastFan :
          SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
            (CellExpr.vcomp
              (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)
              (CellExpr.whiskerRight
                (CellExpr.whiskerRight (bunchedBimonoidDeltaFan (k + 1)) bunchedBimonoidAdditiveGen)
                bunchedBimonoidAdditiveGen))
            (CellExpr.vcomp
              (CellExpr.whiskerRight
                (CellExpr.whiskerRight (bunchedBimonoidDeltaFan (k + 1)) bunchedBimonoidAdditiveGen)
                bunchedBimonoidAdditiveGen)
              (CellExpr.whiskerLeft (bunchedBimonoidAWordPowLeft (k + 1)) bunchedBimonoidAddSigmaGen)) :=
        SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.vcompCongrRight
            (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)
            (SaturatedConvOverWithId.symm
              (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                (StrictAxiomRel.whiskerAssocRight (bunchedBimonoidDeltaFan (k + 1))
                  bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen))))
          (SaturatedConvOverWithId.trans (SaturatedConvOverWithId.symm interchangeRow)
            (SaturatedConvOverWithId.vcompCongrLeft
              (CellExpr.whiskerLeft (bunchedBimonoidAWordPowLeft (k + 1)) bunchedBimonoidAddSigmaGen)
              (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                (StrictAxiomRel.whiskerAssocRight (bunchedBimonoidDeltaFan (k + 1))
                  bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen))))
      -- assemble
      exact
        SaturatedConvOverWithId.trans peelAndFireDualHexagon
          (SaturatedConvOverWithId.trans
            (SaturatedConvOverWithId.vcompCongrRight
              (CellExpr.whiskerRight bunchedBimonoidAddDeltaGen bunchedBimonoidAdditiveGen)
              (SaturatedConvOverWithId.trans
                (SaturatedConvOverWithId.vcompCongrRight
                  (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)
                  threadInductionThroughBack)
                (SaturatedConvOverWithId.trans
                  (SaturatedConvOverWithId.symm
                    (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                      (StrictAxiomRel.vcompAssoc
                        (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)
                        (CellExpr.whiskerRight
                          (CellExpr.whiskerRight (bunchedBimonoidDeltaFan (k + 1))
                            bunchedBimonoidAdditiveGen)
                          bunchedBimonoidAdditiveGen)
                        (CellExpr.whiskerRight (bunchedBimonoidStrandPastBlockRev (k + 1))
                          bunchedBimonoidAdditiveGen))))
                  (SaturatedConvOverWithId.trans
                    (SaturatedConvOverWithId.vcompCongrLeft
                      (CellExpr.whiskerRight (bunchedBimonoidStrandPastBlockRev (k + 1))
                        bunchedBimonoidAdditiveGen)
                      slideMiddleSigmaPastFan)
                    (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                      (StrictAxiomRel.vcompAssoc
                        (CellExpr.whiskerRight
                          (CellExpr.whiskerRight (bunchedBimonoidDeltaFan (k + 1))
                            bunchedBimonoidAdditiveGen)
                          bunchedBimonoidAdditiveGen)
                        (CellExpr.whiskerLeft (bunchedBimonoidAWordPowLeft (k + 1))
                          bunchedBimonoidAddSigmaGen)
                        (CellExpr.whiskerRight (bunchedBimonoidStrandPastBlockRev (k + 1))
                          bunchedBimonoidAdditiveGen)))))))
            (SaturatedConvOverWithId.trans
              (SaturatedConvOverWithId.symm
                (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                  (StrictAxiomRel.vcompAssoc
                    (CellExpr.whiskerRight bunchedBimonoidAddDeltaGen bunchedBimonoidAdditiveGen)
                    (CellExpr.whiskerRight
                      (CellExpr.whiskerRight (bunchedBimonoidDeltaFan (k + 1)) bunchedBimonoidAdditiveGen)
                      bunchedBimonoidAdditiveGen)
                    (CellExpr.vcomp
                      (CellExpr.whiskerLeft (bunchedBimonoidAWordPowLeft (k + 1))
                        bunchedBimonoidAddSigmaGen)
                      (CellExpr.whiskerRight (bunchedBimonoidStrandPastBlockRev (k + 1))
                        bunchedBimonoidAdditiveGen)))))
              (SaturatedConvOverWithId.trans
                (SaturatedConvOverWithId.vcompCongrLeft
                  (CellExpr.vcomp
                    (CellExpr.whiskerLeft (bunchedBimonoidAWordPowLeft (k + 1)) bunchedBimonoidAddSigmaGen)
                    (CellExpr.whiskerRight (bunchedBimonoidStrandPastBlockRev (k + 1))
                      bunchedBimonoidAdditiveGen))
                  (SaturatedConvOverWithId.symm
                    (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                      (StrictAxiomRel.whiskerRightFunctorial bunchedBimonoidAddDeltaGen
                        (CellExpr.whiskerRight (bunchedBimonoidDeltaFan (k + 1)) bunchedBimonoidAdditiveGen)
                        bunchedBimonoidAdditiveGen))))
                (SaturatedConvOverWithId.vcompCongrRight
                  (CellExpr.whiskerRight (bunchedBimonoidDeltaFan (k + 2)) bunchedBimonoidAdditiveGen)
                  (SaturatedConvOverWithId.vcompCongrLeft
                    (CellExpr.whiskerRight (bunchedBimonoidStrandPastBlockRev (k + 1))
                      bunchedBimonoidAdditiveGen)
                    (SaturatedConvOverWithId.whiskerLeftWhiskerCongr bunchedBimonoidAddSigmaGen
                      (bunchedBimonoidAWordPowLeftMatchesAWordPowConv k)))))))

/-! # =========================================================================================
    # B1 — THE NAMED STATEMENTS, INHABITED
    # =========================================================================================
-/

/-- ★★★ **THE r28 mu-SIDE STATEMENT IS A THEOREM** — `bunchedBimonoidBlockThreadingConvStatementMu` holds. -/
theorem bunchedBimonoidBlockThreadingConvStatementMuDelivered :
    bunchedBimonoidBlockThreadingConvStatementMu :=
  bunchedBimonoidSigmaPastMuFoldBlockThreadConv

/-- ★★★ **THE r28 delta-SIDE STATEMENT IS A THEOREM** — `bunchedBimonoidBlockThreadingConvStatementDelta`
holds. -/
theorem bunchedBimonoidBlockThreadingConvStatementDeltaDelivered :
    bunchedBimonoidBlockThreadingConvStatementDelta :=
  bunchedBimonoidSigmaPastDeltaFanBlockThreadConv

/-- ★★ **The general slide fires at any pad** — both colours, every width, inside an arbitrary
`whiskerLeft leftPad (whiskerRight _ rightPad)` frame via the shipped `bunchedBimonoidFireAtPosition`. -/
theorem bunchedBimonoidSigmaPastMuFoldBlockThreadConvAtPosition (blockWidth : Nat)
    (leftPad rightPad : CellExpr bunchedBimonoidOmegaComputad 1) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft leftPad
        (CellExpr.whiskerRight (bunchedBimonoidSigmaPastMuFoldBlockLeft blockWidth) rightPad))
      (CellExpr.whiskerLeft leftPad
        (CellExpr.whiskerRight (bunchedBimonoidSigmaPastMuFoldBlockRight blockWidth) rightPad)) :=
  bunchedBimonoidFireAtPosition leftPad rightPad (bunchedBimonoidSigmaPastMuFoldBlockThreadConv blockWidth)

/-- ★★ The delta-side dual of the at-any-pad firing. -/
theorem bunchedBimonoidSigmaPastDeltaFanBlockThreadConvAtPosition (blockWidth : Nat)
    (leftPad rightPad : CellExpr bunchedBimonoidOmegaComputad 1) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft leftPad
        (CellExpr.whiskerRight (bunchedBimonoidSigmaPastDeltaFanBlockLeft blockWidth) rightPad))
      (CellExpr.whiskerLeft leftPad
        (CellExpr.whiskerRight (bunchedBimonoidSigmaPastDeltaFanBlockRight blockWidth) rightPad)) :=
  bunchedBimonoidFireAtPosition leftPad rightPad (bunchedBimonoidSigmaPastDeltaFanBlockThreadConv blockWidth)

/-! # =========================================================================================
    # B1 — THE MARKERS (supersession by content; every frozen file byte-intact)
    # =========================================================================================
-/

/-- ★★★ **ESTABLISHED — THE GENERAL STEP IS DELIVERED (supersedes the r28 wall by content).**  `= true` records
`bunchedBimonoidBlockThreadingConvStatement{Mu,Delta}Delivered`: the r28-NAMED generic-width CONV statements are
THEOREMS at every width, both colours, plus the at-any-pad firings.  This supersedes (new-file vehicle, frozen
files untouched) the r28 `fxBunchedBimonoid_blockThreadingConvGeneralStepStillWalled = false` and the r27
`fxBunchedBimonoid_genericWidthConvBlockThreadingStillWalled = false`: the "long reassociation chain" is built —
peel + hexagon + interchange (boundary census) + IH-threading + the back-first respelling + the dimension-0 word
rotations under the whisker-1-cell congruences. -/
def fxBunchedBimonoid_blockThreadingConvGeneralStepDelivered : Bool := true

/-- ★★ **ESTABLISHED — the generic-width CONV slide is delivered (the r27 wall's content superseded).**
`= true` records that the full generic-width slide `(a <| muFold k) ; sigma ~ strandPastBlock k ; (muFold k |>
a)` (and the delta dual) is now a genuine CONV over the star scope at EVERY width — the SOUNDNESS half (r27,
`Mat(N)` at seven widths) and the CONV half (this file, all widths) are BOTH shipped. -/
def fxBunchedBimonoid_genericWidthConvBlockThreadingDelivered : Bool := true

/-- ★ **The r8 gated wide-collision marker does NOT flip — honest scope.**  `= false` records that
`fxBunchedBimonoid_wideCollisionConvGatedOnGenericNaturality` (r8, `RiffleAssembly`) stays `= false` byte-intact:
its bill demands the full `wideSwap(m,n)` riffle recursion AND the `CoxeterWordUnique` bubble-sort, of which the
block-threading delivered here is gate (b) only.  The general `(m,n)` collision recursion remains the named
residual for the corrected dim-2 star's retract. -/
def fxBunchedBimonoid_wideCollisionStillGatedAfterBlockThreading : Bool := false

/-- ★★★ **ESTABLISHED — the WP-PROP r29 block-threading-general ledger (the honest scoreboard).**  `= true`
records the complete delivery: the left-nested word power + the fold/fan boundary census, the dimension-0 word
rotations and the left/right-nested identification lifted by the whisker-1-cell congruences, the back-first
respelling of the forward braiding, and the two all-width CONV recursions inhabiting the r28-NAMED statements
(with width-0 bases via the `sigmaEta`/`sigmaEps` naturality + `sigmaInvolution` sound rows and the `idCongr`
boundary bridges).  NO wide `rfl`, NO kernel matrix evaluation; STRUCTURAL recursion only; every frozen marker
byte-intact; zero-axiom (per-decl `#assert_no_axioms` + independent `#print axioms` in the twin). -/
def fxBunchedBimonoid_blockThreadingConvGeneralLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
