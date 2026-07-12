import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPositionGenericMoves
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordStaircase

/-! # Polygraph/Omega/WalkingBunchedBimonoidCanonicalWordConvFold — the CONV-fold spelling bridge: the
whisker-over-vcomp `sigmaAt`-chain bridge and the dim-1 word-boundary reshape the r14 staircase walled
(WP-PROP r15, #2033)

★ **THE r15 SPELLING BRIDGE — the two vcomp-vs-whisker gaps the r14
`fxBunchedBimonoid_combInsertStepConvGatedOnSpellingBridge` named, DELIVERED at the letter granularity.**  r14
shipped the PURE `List Nat` permutation-preservation leg (`bunchedBimonoidCombInsertDataRealizesSwap` folded to
`bunchedBimonoidCombNormalizeFormPreservesPerm`) and walled the CONV fold on TWO precisely-named spelling gaps:

  (i)  the whisker-over-vcomp gap — the r9 base legs (`bunchedBimonoidSigmaInvolutionLeftLeg =
       vcomp addSigmaGen addSigmaGen`) are NOT the `sigmaAt`-chain (`vcomp (sigmaAt w k) (sigmaAt w k)`)
       definitionally, only up to `whiskerLeftFunctorial` / `whiskerRightFunctorial` distributing the whisker over
       the inner vcomp;
  (ii) the append-vs-vcomp gap — `permWord (A ++ B) w` is a right-folded vcomp TREE, not
       `vcomp (permWord A w) (permWord B w)` definitionally, needing a `vcompUnitLeft` / `vcompAssoc` reshape whose
       nil case rests on a dim-1 boundary reshape (`aWordPow w` versus the sigma-source tree).

This file ships the honest state of BOTH gaps at letter granularity.  Gap (i) is DELIVERED unconditionally: the
whisker-over-vcomp bridge `bunchedBimonoidSigmaChainInvolutionWhiskerConv` fires
`whiskerRightFunctorial` + `whiskerLeftFunctorial` (both `StrictAxiomRel` rows, `Or.inl` into the star scope) to
convert the `sigmaAt`-chain `vcomp (sigmaAt w k) (sigmaAt w k)` to the fixed r9 base leg
`whiskerLeft (aWordPow k) (whiskerRight SigmaInvolutionLeftLeg (aWordPow (w-k-2)))`.  Composed with the shipped r9
`bunchedBimonoidInvolutionAtPosition`, this fires the CANCEL letter's `s_k s_k = e` at the star scope.  The dim-1
word-boundary facts gap (ii) needs are shipped structurally (`aWordPow`'s boundary is the mode point on the nose,
because `aWordPow`'s head is a plain `gen`, NOT a whisker); the FULL append reshape is the honest residual named at
the foot of this file (the sigma-source tree `vcomp (aWordPow k) (vcomp aaWord (aWordPow (w-k-2)))` reshapes to the
flat `aWordPow w` only through a dim-1 `aWordPow`-split — the exact jamming case).

## What this round is NOT (the honest scope)

The star does NOT flip: no hypothesis-free inhabitant of `bunchedBimonoidStarStatementAdditiveWellTyped` is
produced.  Every star / residual marker (`fxBunchedBimonoid_correctedWellTypedStarStillOpen*`,
`fxBunchedBimonoid_coxeterWordUniqueGatedOnGenericBraid`,
`fxBunchedBimonoid_collisionGeneralStepStillGatedOnBracketMatch`,
`fxBunchedBimonoid_coxeterWordUniqueBubbleSortStillUnbuilt`, the r14
`fxBunchedBimonoid_combInsertStepConvGatedOnSpellingBridge`) keeps its name and `= false` value byte-intact
(cross-file, not edited).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin.  Mirror of the Brauer canonicity lane's `crossingWord` / `recCombConv`;
never imported from it — and genuinely wider (the Brauer `crossingWord` is a flat `List BrauerAtom`, so its
append IS list append; the Omega `permWord` folds into real `CellExpr` vcomp trees with whisker atoms, so the
spelling bridge is genuine CONV content, not a definitional coincidence). -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

/-! The whiskered-endpoint matrix probes evaluate at width 3, exceeding the default heartbeat budget; the raise is
a compute allowance only, the proof terms stay `Eq.refl` / congruence-constructor plumbing, axiom-free (uniform
with the r6-r14 lane files). -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # S0 — THE DIM-1 WORD-BOUNDARY FACTS (structural; the reshape gap (ii) rests on these)
    # =========================================================================================

★ The boundary of an `aWordPow` word is the mode point ON THE NOSE — because `aWordPow`'s head is the plain
1-generator `additiveGen` (a `gen` with declared boundary `point`), NOT a whisker.  This is the exact structural
asymmetry that makes gap (ii) a genuine CONV: the `sigmaAt` letter's head IS a whisker, so its boundary is the
formal `vcomp` tree `vcomp (aWordPow k) (vcomp aaWord (aWordPow (w-k-2)))`, which agrees with `aWordPow w` only up
to the strict laws. -/

/-- ★ **The source boundary of an `aWordPow` word is the mode point** — structural (two cases, both `rfl`): the
empty word `aWordPow 0 = id point` has boundary `point`; the cons `aWordPow (k+1) = vcomp additiveGen (aWordPow k)`
has boundary `boundarySource additiveGen = point` (the plain `gen`'s declared source).  The clean base the append
reshape's nil case would rest on. -/
theorem bunchedBimonoidAWordPowBoundarySource :
    (width : Nat) → boundarySource (bunchedBimonoidAWordPow width) = bunchedBimonoidPoint
  | 0 => rfl
  | _ + 1 => rfl

/-- ★ **The source boundary of a `sigmaAt` letter is the sigma-source tree** — `boundarySource (sigmaAt w k) =
vcomp (aWordPow k) (vcomp aaWord (aWordPow (w-k-2)))` (`rfl`).  The whiskered head of `sigmaAt` yields a formal
`vcomp` tree (the whisker boundary is the formal composite), NOT the flat `aWordPow w` — this is exactly why the
append reshape's nil case is a genuine dim-1 CONV, not a definitional equality. -/
theorem bunchedBimonoidSigmaAtBoundarySource (wordWidth positionK : Nat) :
    boundarySource (bunchedBimonoidSigmaAt wordWidth positionK)
      = CellExpr.vcomp (bunchedBimonoidAWordPow positionK)
          (CellExpr.vcomp bunchedBimonoidAaWord (bunchedBimonoidAWordPow (wordWidth - positionK - 2))) := rfl

/-- ★ **A cons `permWord`'s source boundary reads off its head letter** — `boundarySource (permWord (k :: rest)
width) = boundarySource (sigmaAt width k)` (`rfl`, independent of the tail).  `boundarySource` of a `vcomp` is the
left factor's boundary; the tail `permWord rest width` is invisible to the boundary. -/
theorem bunchedBimonoidPermWordConsBoundarySource (headPosition : Nat) (remainingPositions : List Nat)
    (wordWidth : Nat) :
    boundarySource (bunchedBimonoidPermWord (headPosition :: remainingPositions) wordWidth)
      = boundarySource (bunchedBimonoidSigmaAt wordWidth headPosition) := rfl

/-! # =========================================================================================
    # S1 — THE WHISKER-OVER-VCOMP SPELLING BRIDGE (gap (i), DELIVERED at letter granularity)
    # =========================================================================================

★ The r9 base legs are the FIXED 2-strand cells (`SigmaInvolutionLeftLeg = vcomp addSigmaGen addSigmaGen`), whereas
the `sigmaAt`-chain `vcomp (sigmaAt w k) (sigmaAt w k)` whiskers TWO copies of `addSigmaGen` at position `k`.  The
two agree over the star scope by distributing the whisker over the inner vcomp, via `whiskerRightFunctorial`
(push `whiskerRight` past the inner `vcomp`) then `whiskerLeftFunctorial` (push `whiskerLeft` past it) — both
`StrictAxiomRel` rows embedded by `Or.inl`. -/

/-- ★★ **THE WHISKER-OVER-VCOMP INVOLUTION BRIDGE (gap (i)).**  The r9 involution base leg whiskered at position
`(aWordPow k, aWordPow (w-k-2))` converts, over the star scope, to the `sigmaAt`-chain `s_k s_k`:

  `whiskerLeft (a^k) (whiskerRight (sigma . sigma) (a^(w-k-2))) ~ vcomp (sigmaAt w k) (sigmaAt w k)`.

`whiskerRightFunctorial addSigmaGen addSigmaGen (a^(w-k-2))` distributes the right whisker over the inner vcomp
(under `whiskerLeftCongr (a^k)`), then `whiskerLeftFunctorial (a^k) _ _` distributes the left whisker — landing the
two `sigmaAt` letters.  Both rows are `StrictAxiomRel`, embedded into the star scope by `Or.inl`
(`bunchedBimonoidStrictAxiomEmbedsIntoStarScope`).  This is the genuinely-new content the Brauer flat-`List` lane
never needed. -/
theorem bunchedBimonoidSigmaChainInvolutionWhiskerConv (wordWidth positionK : Nat) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow positionK)
        (CellExpr.whiskerRight bunchedBimonoidSigmaInvolutionLeftLeg
          (bunchedBimonoidAWordPow (wordWidth - positionK - 2))))
      (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth positionK)
        (bunchedBimonoidSigmaAt wordWidth positionK)) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.whiskerLeftCongr (bunchedBimonoidAWordPow positionK)
      (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
        (StrictAxiomRel.whiskerRightFunctorial bunchedBimonoidAddSigmaGen bunchedBimonoidAddSigmaGen
          (bunchedBimonoidAWordPow (wordWidth - positionK - 2)))))
    (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
      (StrictAxiomRel.whiskerLeftFunctorial (bunchedBimonoidAWordPow positionK)
        (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow (wordWidth - positionK - 2)))
        (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow (wordWidth - positionK - 2)))))

/-! ## S1 truth-probes (the bridge relates two cells of the same matrix; width 3) -/

/-- The bridge endpoints share their matrix at width 3, position 0 (`rfl`): both `whiskerLeft (a^0) (whiskerRight
(sigma . sigma) (a^1))` and `vcomp (sigmaAt 3 0) (sigmaAt 3 0)` evaluate to the identity `[[1,0,0],[0,1,0],[0,0,1]]`
(the involution). -/
theorem bunchedBimonoidSigmaChainInvolutionWhiskerMatrixShared :
    bunchedBimonoidEvalCell
        (CellExpr.whiskerLeft (bunchedBimonoidAWordPow 0)
          (CellExpr.whiskerRight bunchedBimonoidSigmaInvolutionLeftLeg (bunchedBimonoidAWordPow 1)))
      = bunchedBimonoidEvalCell
        (CellExpr.vcomp (bunchedBimonoidSigmaAt 3 0) (bunchedBimonoidSigmaAt 3 0)) := rfl

/-! ## The S1 marker -/

/-- ★★★ **ESTABLISHED (S1) — the whisker-over-vcomp spelling bridge (gap (i)) is DELIVERED.**  `= true` records
`bunchedBimonoidSigmaChainInvolutionWhiskerConv`: the fixed r9 base leg
`whiskerLeft (a^k) (whiskerRight (sigma . sigma) (a^(w-k-2)))` is convertible over the star scope to the
`sigmaAt`-chain `vcomp (sigmaAt w k) (sigmaAt w k)`, by `whiskerRightFunctorial` + `whiskerLeftFunctorial` (both
`StrictAxiomRel`, `Or.inl`).  This is EXACTLY gap (i) the r14
`fxBunchedBimonoid_combInsertStepConvGatedOnSpellingBridge` named (the whisker distributing over the inner vcomp);
composed with the shipped r9 `bunchedBimonoidInvolutionAtPosition` it fires the CANCEL letter's `s_k s_k = e` at
the star scope.  Matrix-soundness pinned at width 3 (`...WhiskerMatrixShared`).  The genuinely-new content vs the
Brauer flat-`List` lane.  Zero-axiom (per-decl `#assert_no_axioms` + independent `#print axioms` in the twin). -/
def fxBunchedBimonoid_whiskerOverVcompSpellingBridgeShipped : Bool := true

/-! # =========================================================================================
    # S2 — THE GENERIC WHISKER-OVER-VCOMP BRIDGE + THE CANCEL LETTER CONV (`s_k s_k ~ id`)
    # =========================================================================================

★ The involution bridge S1 is the `upper = lower = addSigmaGen` instance of a GENERIC whisker-over-vcomp bridge:
any inner vertical composite `vcomp upper lower` in whisker position distributes into the vcomp of the two
whiskered factors, over the star scope, by the same two `StrictAxiomRel` rows.  Composed with the shipped r9
`bunchedBimonoidInvolutionAtPosition` and the two strict `id`-whisker units, this fires the CANCEL letter's
`s_k s_k = e` all the way to the identity `id (boundarySource (sigmaAt w k))` — a complete letter-level case
bridge, needing NO append reshape (gap (ii)). -/

/-- ★★ **THE GENERIC WHISKER-OVER-VCOMP BRIDGE.**  For any pads `leftPad`, `rightPad` and any inner factors
`upperCell`, `lowerCell`, the whisker of an inner `vcomp` distributes over the star scope:

  `whiskerLeft L (whiskerRight (upper . lower) R) ~ vcomp (whiskerLeft L (whiskerRight upper R)) (whiskerLeft L
   (whiskerRight lower R))`.

`whiskerRightFunctorial upper lower R` under `whiskerLeftCongr L`, then `whiskerLeftFunctorial L _ _` — both
`StrictAxiomRel`, `Or.inl` into the star scope.  The S1 involution bridge is the `(addSigmaGen, addSigmaGen)`
instance (`SigmaInvolutionLeftLeg = vcomp addSigmaGen addSigmaGen`, and `whiskerLeft (a^k) (whiskerRight
addSigmaGen (a^(w-k-2))) = sigmaAt w k` definitionally). -/
theorem bunchedBimonoidWhiskerOverVcompConv (leftPad rightPad : CellExpr bunchedBimonoidOmegaComputad 1)
    (upperCell lowerCell : CellExpr bunchedBimonoidOmegaComputad 2) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight (CellExpr.vcomp upperCell lowerCell) rightPad))
      (CellExpr.vcomp (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight upperCell rightPad))
        (CellExpr.whiskerLeft leftPad (CellExpr.whiskerRight lowerCell rightPad))) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.whiskerLeftCongr leftPad
      (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
        (StrictAxiomRel.whiskerRightFunctorial upperCell lowerCell rightPad)))
    (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
      (StrictAxiomRel.whiskerLeftFunctorial leftPad
        (CellExpr.whiskerRight upperCell rightPad) (CellExpr.whiskerRight lowerCell rightPad)))

/-- ★★★ **THE CANCEL LETTER CONV — `s_k s_k ~ id` at the star scope, the CANCEL case bridge.**  The `sigmaAt`-chain
`vcomp (sigmaAt w k) (sigmaAt w k)` converts, over the star scope, to the identity on the letter's source word
`id (boundarySource (sigmaAt w k))` (= `id (vcomp (a^k) (vcomp aaWord (a^(w-k-2))))`, by S0):

  1. `symm` of the S1 whisker-over-vcomp bridge lands `whiskerLeft (a^k) (whiskerRight (sigma . sigma) (a^(w-k-2)))`;
  2. the shipped r9 `bunchedBimonoidInvolutionAtPosition` fires `sigma . sigma ~ id_{a.a}`
     (`SigmaInvolutionRightLeg = id aaWord`);
  3. `whiskerRightUnit` absorbs the right whisker of the identity (`whiskerRight (id aaWord) (a^(w-k-2)) ~
     id (vcomp aaWord (a^(w-k-2)))`) under `whiskerLeftCongr (a^k)`;
  4. `whiskerLeftUnit` absorbs the left whisker of the identity — reaching `id (vcomp (a^k) (vcomp aaWord
     (a^(w-k-2))))`.

This is the DATA-level CANCEL branch of `bunchedBimonoidCombInsertDataRealizesSwap` (r14) lifted to a CONV over the
star scope, at letter granularity — no append reshape (gap (ii)) required, because the CANCEL letter's target is a
bare identity whose word is exactly the letter's source boundary. -/
theorem bunchedBimonoidCancelLetterConv (wordWidth positionK : Nat) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth positionK)
        (bunchedBimonoidSigmaAt wordWidth positionK))
      (CellExpr.id (boundarySource (bunchedBimonoidSigmaAt wordWidth positionK))) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.symm (bunchedBimonoidSigmaChainInvolutionWhiskerConv wordWidth positionK))
    (SaturatedConvOverWithId.trans
      (bunchedBimonoidInvolutionAtPosition (bunchedBimonoidAWordPow positionK)
        (bunchedBimonoidAWordPow (wordWidth - positionK - 2)))
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.whiskerLeftCongr (bunchedBimonoidAWordPow positionK)
          (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
            (StrictAxiomRel.whiskerRightUnit bunchedBimonoidAaWord
              (bunchedBimonoidAWordPow (wordWidth - positionK - 2)))))
        (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
          (StrictAxiomRel.whiskerLeftUnit (bunchedBimonoidAWordPow positionK)
            (CellExpr.vcomp bunchedBimonoidAaWord (bunchedBimonoidAWordPow (wordWidth - positionK - 2)))))))

/-! ## S2 truth-probe (the CANCEL letter is matrix-sound: both endpoints are the identity; width 3) -/

/-- The CANCEL letter's endpoints share their matrix at width 3, position 0 (`rfl`): both `vcomp (sigmaAt 3 0)
(sigmaAt 3 0)` and `id (boundarySource (sigmaAt 3 0))` evaluate to the identity `[[1,0,0],[0,1,0],[0,0,1]]`. -/
theorem bunchedBimonoidCancelLetterMatrixShared :
    bunchedBimonoidEvalCell
        (CellExpr.vcomp (bunchedBimonoidSigmaAt 3 0) (bunchedBimonoidSigmaAt 3 0))
      = bunchedBimonoidEvalCell
        (CellExpr.id (boundarySource (bunchedBimonoidSigmaAt 3 0))) := rfl

/-! ## The S2 marker -/

/-- ★★★ **ESTABLISHED (S2) — the generic whisker-over-vcomp bridge + the CANCEL letter CONV are DELIVERED.**
`= true` records `bunchedBimonoidWhiskerOverVcompConv` (the generic distribution of an inner whiskered vcomp over
the star scope) and `bunchedBimonoidCancelLetterConv` (the CANCEL case bridge: `vcomp (sigmaAt w k) (sigmaAt w k)`
converts to `id (boundarySource (sigmaAt w k))` over the star scope, via the S1 bridge + the shipped r9
`bunchedBimonoidInvolutionAtPosition` + the two strict `id`-whisker units).  This is the letter-level CONV realising
the r14 CANCEL branch of `bunchedBimonoidCombInsertDataRealizesSwap` — DELIVERED with NO append reshape (gap (ii))
needed, since the CANCEL target is a bare identity whose word is exactly the letter's source boundary.
Matrix-soundness pinned at width 3 (`...CancelLetterMatrixShared`).  Zero-axiom (per-decl `#assert_no_axioms` +
independent `#print axioms` in the twin). -/
def fxBunchedBimonoid_cancelLetterConvShipped : Bool := true

/-! # =========================================================================================
    # S3 — THE DIM-1 `aWordPow`-SPLIT RESHAPE (the core of gap (ii)) + the honest append residual
    # =========================================================================================

★ Gap (ii) — the append-vs-vcomp reshape — bottoms out at a DIM-1 fact: the flat word `aWordPow (a + b)` is
convertible over the star scope to `vcomp (aWordPow a) (aWordPow b)`.  Unlike the sigmaAt-chain (whose head is a
whisker, giving a tree boundary), `aWordPow`'s head is the plain generator `additiveGen`, so its boundary is the
mode point ON THE NOSE (S0) — the nil case of the split fires `vcompUnitLeft` cleanly.  The `cons` case threads the
IH under `vcompCongrRight` and reassociates with `vcompAssoc`.  This is the exact dim-1 analogue of the CollapseDimOne
`realizePath_composePath_conv`, ported to `aWordPow` + the star scope + `SaturatedConvOverWithId`.

The FULL append reshape `permWord (front ++ back) w ~ vcomp (permWord front w) (permWord back w)` needs, at its nil
case, `aWordPow w ~ boundarySource (permWord back w)` = `aWordPow w ~ vcomp (aWordPow k) (vcomp aaWord (aWordPow
(w-k-2)))` for `back`'s head `k` — a reshape assembled from TWO `aWordPowSplitConv` firings plus the truncated-
subtraction arithmetic `k + (2 + (w-k-2)) = w`, gated on the position-validity `k + 2 ≤ w` threaded from
`mentionsOnlyBelow`.  This round SHIPS the dim-1 split (the core); the front-induction threading is the named
residual. -/

/-! ## S3.arith — the propext-clean Nat backbone for `aWordPow (a + b)` peeling (add is right-recursive) -/

private theorem bunchedBimonoidNatZeroAddConvFold : (value : Nat) → 0 + value = value
  | 0 => rfl
  | value + 1 => congrArg Nat.succ (bunchedBimonoidNatZeroAddConvFold value)

private theorem bunchedBimonoidNatSuccAddConvFold :
    (leadValue offset : Nat) → (leadValue + 1) + offset = (leadValue + offset) + 1
  | _, 0 => rfl
  | leadValue, offset + 1 => congrArg Nat.succ (bunchedBimonoidNatSuccAddConvFold leadValue offset)

/-- ★★★ **THE DIM-1 `aWordPow`-SPLIT RESHAPE (the core of gap (ii)).**  The flat word `aWordPow (a + b)` converts,
over the star scope, to `vcomp (aWordPow a) (aWordPow b)`.  Structural on `a`: the `0` case rewrites `0 + b` to `b`
and fires `vcompUnitLeft (aWordPow b)` (its identity is on `boundarySource (aWordPow b) = point`, by S0, matching
`aWordPow 0 = id point`); the `a+1` case rewrites `(a+1)+b` to `(a+b)+1`, peels `aWordPow ((a+b)+1) = vcomp
additiveGen (aWordPow (a+b))`, threads the IH under `vcompCongrRight additiveGen`, and reassociates with the `symm`
of `vcompAssoc` — landing `vcomp (aWordPow (a+1)) (aWordPow b)`.  The dim-1 analogue of the CollapseDimOne
`realizePath_composePath_conv`, over `SaturatedConvOverWithId` + the star scope (both rows `Or.inl`). -/
theorem bunchedBimonoidAWordPowSplitConv :
    (segmentA segmentB : Nat) →
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidAWordPow (segmentA + segmentB))
      (CellExpr.vcomp (bunchedBimonoidAWordPow segmentA) (bunchedBimonoidAWordPow segmentB))
  | 0, segmentB => by
      rw [bunchedBimonoidNatZeroAddConvFold segmentB]
      have unitRow := bunchedBimonoidStrictAxiomEmbedsIntoStarScope
        (StrictAxiomRel.vcompUnitLeft (bunchedBimonoidAWordPow segmentB))
      rw [bunchedBimonoidAWordPowBoundarySource segmentB] at unitRow
      exact unitRow.symm
  | segmentA + 1, segmentB => by
      rw [bunchedBimonoidNatSuccAddConvFold segmentA segmentB]
      exact SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrRight bunchedBimonoidAdditiveGen
          (bunchedBimonoidAWordPowSplitConv segmentA segmentB))
        (SaturatedConvOverWithId.symm
          (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
            (StrictAxiomRel.vcompAssoc bunchedBimonoidAdditiveGen
              (bunchedBimonoidAWordPow segmentA) (bunchedBimonoidAWordPow segmentB))))

/-- ★★ **`aWordPow 2 ~ aaWord` — the two-strand word identifies its bracketing.**  `aWordPow 2 = vcomp additiveGen
(vcomp additiveGen (id point))` reshapes to `aaWord = vcomp additiveGen additiveGen` over the star scope, by
`vcompUnitRight additiveGen` (stripping the trailing identity, `id point = id (boundaryTarget additiveGen)`) under
`vcompCongrRight additiveGen`.  The base the sigma-source reshape needs (`aaWord = boundarySource addSigmaGen`). -/
theorem bunchedBimonoidAWordPowTwoIsAaWordConv :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidAWordPow 2) bunchedBimonoidAaWord :=
  SaturatedConvOverWithId.vcompCongrRight bunchedBimonoidAdditiveGen
    (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
      (StrictAxiomRel.vcompUnitRight bunchedBimonoidAdditiveGen))

/-! ## S3 truth-probes (the dim-1 split relates two cells of the same width; width 3) -/

/-- The split endpoints share their matrix at `(1, 2)` (`rfl`): both `aWordPow (1 + 2)` and `vcomp (aWordPow 1)
(aWordPow 2)` evaluate to the width-3 identity `[[1,0,0],[0,1,0],[0,0,1]]`. -/
theorem bunchedBimonoidAWordPowSplitMatrixShared :
    bunchedBimonoidEvalCell (bunchedBimonoidAWordPow (1 + 2))
      = bunchedBimonoidEvalCell
        (CellExpr.vcomp (bunchedBimonoidAWordPow 1) (bunchedBimonoidAWordPow 2)) := rfl

/-- `aWordPow 2` and `aaWord` share their matrix (`rfl`, the width-2 identity). -/
theorem bunchedBimonoidAWordPowTwoIsAaWordMatrixShared :
    bunchedBimonoidEvalCell (bunchedBimonoidAWordPow 2) = bunchedBimonoidEvalCell bunchedBimonoidAaWord := rfl

/-! ## The S3 marker + the honest append residual -/

/-- ★★★ **ESTABLISHED (S3) — the dim-1 `aWordPow`-split reshape (the core of gap (ii)) is DELIVERED.**  `= true`
records `bunchedBimonoidAWordPowSplitConv` (the general dim-1 split `aWordPow (a+b) ~ vcomp (aWordPow a) (aWordPow
b)` over the star scope, structural on `a`, resting on the clean `aWordPow`-boundary-is-point fact S0) and
`bunchedBimonoidAWordPowTwoIsAaWordConv` (`aWordPow 2 ~ aaWord`).  Together these are the dim-1 heart of gap (ii):
the sigma-source tree `vcomp (aWordPow k) (vcomp aaWord (aWordPow (w-k-2)))` — which is exactly `boundarySource
(sigmaAt w k)` (S0) — reshapes to the flat `aWordPow w` by two `aWordPowSplitConv` firings.  Matrix-soundness pinned
at width 3.  Zero-axiom (per-decl `#assert_no_axioms` + independent `#print axioms` in the twin). -/
def fxBunchedBimonoid_dimOneWordSplitReshapeShipped : Bool := true

/-- ★ **THE FULL APPEND RESHAPE (gap (ii)) STAYS WALLED (r15) — the exact residual named, no flip.**  `= false`
records the ONE remaining node of the CONV fold: the append-vs-vcomp bridge `permWord (front ++ back) w ~ vcomp
(permWord front w) (permWord back w)` is NOT assembled here.  Its dim-1 core is SHIPPED (S3
`bunchedBimonoidAWordPowSplitConv`), and the whisker-over-vcomp + CANCEL letter case are SHIPPED (S1/S2), so the
residual is precisely: (a) the sigma-source boundary reshape `aWordPow w ~ boundarySource (sigmaAt w k)` under `k +
2 ≤ w` (two `aWordPowSplitConv` firings + the truncated-subtraction arithmetic `k + (2 + (w-k-2)) = w`); (b)
threading it through the FRONT-induction of `permWordAppendConv` via `vcompIdLeft_bridgedWithId`, carrying the
`bunchedBimonoidMentionsOnlyBelow` position-validity (each head `k` satisfies `k + 2 ≤ w`) — the exact jamming case.
With (a)+(b) the four case bridges (COMMUTE / EXTEND / CANCEL / CARRY) fold to `combNormalizeFormConv`, then
`recCombConv` (structural on the generator count), then `coxeterWordUnique`.  The star does NOT flip: no
hypothesis-free inhabitant of `bunchedBimonoidStarStatementAdditiveWellTyped` is produced.  The star / residual
markers (`fxBunchedBimonoid_correctedWellTypedStarStillOpen*`,
`fxBunchedBimonoid_coxeterWordUniqueGatedOnGenericBraid`,
`fxBunchedBimonoid_collisionGeneralStepStillGatedOnBracketMatch`,
`fxBunchedBimonoid_coxeterWordUniqueBubbleSortStillUnbuilt`, the r14
`fxBunchedBimonoid_combInsertStepConvGatedOnSpellingBridge`) keep their names and `= false` values byte-intact
(cross-file, not edited). -/
def fxBunchedBimonoid_appendReshapeGatedOnBoundaryAndValidityThreading : Bool := false

/-- ★★★ **ESTABLISHED — the WP-PROP r15 CONV-fold spelling-bridge ledger (the honest scoreboard).**  `= true`
records the complete r15 round: S0 the dim-1 word-boundary facts; S1 the whisker-over-vcomp spelling bridge (gap
(i) DELIVERED, `fxBunchedBimonoid_whiskerOverVcompSpellingBridgeShipped`); S2 the generic whisker-over-vcomp bridge
+ the CANCEL letter CONV `s_k s_k ~ id` (`fxBunchedBimonoid_cancelLetterConvShipped`, a complete letter-level case
bridge, no append reshape needed); S3 the dim-1 `aWordPow`-split reshape — the core of gap (ii)
(`fxBunchedBimonoid_dimOneWordSplitReshapeShipped`).  The FULL append reshape (gap (ii)) + the four-case fold +
`recCombConv` + `coxeterWordUnique` are precisely named and DEFERRED
(`fxBunchedBimonoid_appendReshapeGatedOnBoundaryAndValidityThreading = false`); the star does NOT flip, and every
upstream star / residual marker keeps its name and value byte-intact (cross-file, not edited).  Zero-axiom (per-decl
`#assert_no_axioms` + independent `#print axioms` in the twin); STRUCTURAL only.  Genuinely wider than the Brauer
flat-`List` lane (the Omega `permWord` folds into real `CellExpr` vcomp trees, so the spelling bridge is genuine
CONV content).  NO fabricated star flip. -/
def fxBunchedBimonoid_canonicalWordConvFoldRoundFifteenLedgerShipped : Bool := true

/-! # =========================================================================================
    # S4 — THE SIGMA-SOURCE BOUNDARY RESHAPE (part (a) of the append residual, DELIVERED)
    # =========================================================================================

★ Part (a) of the named append residual: the sigma-source tree IS convertible to the flat word.  `boundarySource
(sigmaAt w k) = vcomp (aWordPow k) (vcomp aaWord (aWordPow (w-k-2)))` (S0) reshapes to `aWordPow w`, over the star
scope, by two `aWordPowSplitConv` firings (split at `k`, then split off the `aaWord` block via `aWordPowSplitConv 2`
+ `aWordPowTwoIsAaWordConv`), transported along the truncated-subtraction arithmetic `k + (2 + (w-k-2)) = w` under
`k + 2 ≤ w`.  The arithmetic is re-derived propext-clean (the core `Nat.sub` lemmas leak propext; the structural
`commuteHighEq` + `Nat.add_comm`/`Nat.add_assoc` do not).  With this, the append residual narrows to part (b) alone
(the front-induction threading of `mentionsOnlyBelow` position-validity through `permWordAppendConv`). -/

/-! ## S4.arith — the propext-clean truncated-subtraction backbone -/

private theorem bunchedBimonoidSubTwoAddTwoConvFold : (value : Nat) → 2 ≤ value → value - 2 + 2 = value
  | 0, twoLe => absurd twoLe (by decide)
  | 1, twoLe => absurd twoLe (by decide)
  | _ + 2, _ => rfl

private theorem bunchedBimonoidCommuteHighEqConvFold :
    (low high : Nat) → low + 2 ≤ high → low + (high - low - 2) + 2 = high
  | 0, high, hLe => by
      rw [Nat.zero_add]
      exact bunchedBimonoidSubTwoAddTwoConvFold high hLe
  | _ + 1, 0, hLe => absurd hLe (Nat.not_succ_le_zero _)
  | low + 1, high + 1, hLe => by
      have inner : low + (high - low - 2) + 2 = high :=
        bunchedBimonoidCommuteHighEqConvFold low high (Nat.le_of_succ_le_succ hLe)
      rw [Nat.succ_sub_succ, Nat.succ_add, Nat.succ_add]
      exact congrArg Nat.succ inner

private theorem bunchedBimonoidReshapeArithConvFold (positionK wordWidth : Nat)
    (inRange : positionK + 2 ≤ wordWidth) :
    positionK + (2 + (wordWidth - positionK - 2)) = wordWidth := by
  have staircase : positionK + (wordWidth - positionK - 2) + 2 = wordWidth :=
    bunchedBimonoidCommuteHighEqConvFold positionK wordWidth inRange
  rw [Nat.add_comm 2 (wordWidth - positionK - 2), ← Nat.add_assoc]
  exact staircase

/-- ★★★ **THE SIGMA-SOURCE BOUNDARY RESHAPE (append residual part (a), DELIVERED).**  Under `k + 2 ≤ w`, the
letter's source boundary `boundarySource (sigmaAt w k)` (= the tree `vcomp (aWordPow k) (vcomp aaWord (aWordPow
(w-k-2)))`, by S0) converts, over the star scope, to the flat word `aWordPow w`.  `aWordPowSplitConv positionK (2 +
(w-k-2))` splits off the `k`-prefix; `vcompCongrRight` then `aWordPowSplitConv 2 (w-k-2)` splits the `aaWord` block;
`vcompCongrLeft` fires `aWordPowTwoIsAaWordConv`.  The whole is transported along
`bunchedBimonoidReshapeArithConvFold` (`k + (2 + (w-k-2)) = w`), rewriting ONLY the `aWordPow w` argument via
`congrArg`.  Exactly the reshape `permWordAppendConv`'s nil case needs (`aWordPow w ~ boundarySource (permWord back
w)` when `back`'s head is `k`). -/
theorem bunchedBimonoidSigmaAtBoundaryReshapeConv (wordWidth positionK : Nat)
    (inRange : positionK + 2 ≤ wordWidth) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidAWordPow wordWidth)
      (boundarySource (bunchedBimonoidSigmaAt wordWidth positionK)) := by
  show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidAWordPow wordWidth)
      (CellExpr.vcomp (bunchedBimonoidAWordPow positionK)
        (CellExpr.vcomp bunchedBimonoidAaWord (bunchedBimonoidAWordPow (wordWidth - positionK - 2))))
  rw [congrArg bunchedBimonoidAWordPow (bunchedBimonoidReshapeArithConvFold positionK wordWidth inRange).symm]
  exact SaturatedConvOverWithId.trans
    (bunchedBimonoidAWordPowSplitConv positionK (2 + (wordWidth - positionK - 2)))
    (SaturatedConvOverWithId.vcompCongrRight (bunchedBimonoidAWordPow positionK)
      (SaturatedConvOverWithId.trans
        (bunchedBimonoidAWordPowSplitConv 2 (wordWidth - positionK - 2))
        (SaturatedConvOverWithId.vcompCongrLeft (bunchedBimonoidAWordPow (wordWidth - positionK - 2))
          bunchedBimonoidAWordPowTwoIsAaWordConv)))

/-! ## The S4 marker -/

/-- ★★★ **ESTABLISHED (S4) — the sigma-source boundary reshape (append residual part (a)) is DELIVERED.**  `= true`
records `bunchedBimonoidSigmaAtBoundaryReshapeConv`: under `k + 2 ≤ w`, the whiskered `sigmaAt` letter's source
boundary tree converts over the star scope to the flat `aWordPow w`, assembled from the S3 dim-1 split fired twice +
the propext-clean truncated-subtraction arithmetic.  This is EXACTLY part (a) the residual marker
`fxBunchedBimonoid_appendReshapeGatedOnBoundaryAndValidityThreading` named; with it, the FULL append reshape
narrows to part (b) alone — threading `mentionsOnlyBelow` position-validity through `permWordAppendConv`'s
front-induction via `vcompIdLeft_bridgedWithId`.  The star does NOT flip; the residual marker stays `= false`
byte-intact (the full append assembly is still unbuilt).  Zero-axiom (per-decl `#assert_no_axioms` + independent
`#print axioms` in the twin). -/
def fxBunchedBimonoid_sigmaSourceBoundaryReshapeShipped : Bool := true

end FX1Poly.Polygraph.Omega
