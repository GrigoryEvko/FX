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

end FX1Poly.Polygraph.Omega
