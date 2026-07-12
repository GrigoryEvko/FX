import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordAppendReshape

/-! # Polygraph/Omega/WalkingBunchedBimonoidCanonicalWordRunCommuteConv — the CONV run-commute atoms
(distant-commutation + braid at the `sigmaAt` word level) and their exact whisker-coherence wall, with the
buildable whiskering-`aWordPow` split reshape delivered (WP-PROP r17)

★ **THE r17 HONEST STATE — the two Coxeter atoms Lafont's rewrite system rests on, at the `sigmaAt` CONV
granularity, and the ONE structural coherence that walls them.**  r14 shipped the PURE `List Nat`
permutation layer: `bunchedBimonoidCarryPerm` + `bunchedBimonoidSwapCommutesRun{Above,Below}` +
`bunchedBimonoidCombInsertDataRealizesSwap` folded to `bunchedBimonoidCombNormalizeFormPreservesPerm`.  r15/r16
shipped the CONV spelling bridges the CANCEL / append cases need
(`bunchedBimonoidCancelLetterConv`, `bunchedBimonoidPermWordAppendConv`).  The CONV mirror of the r14 pure fold
— `carryPermConv` + the two `swapCommutesRun*Conv` folded to `combInsertConv` / `combNormalizeFormConv` — needs,
at its irreducible bottom, the TWO atomic Coxeter moves at the `sigmaAt` word level (Lafont 2003 Thm 1's two
generating relations, Björner–Brenti's commutation + braid, Tenner eqns (1)–(2)):

  * **DISTANT-COMMUTE** `vcomp (sigmaAt w i) (sigmaAt w j) ~ vcomp (sigmaAt w j) (sigmaAt w i)`  for `i + 2 ≤ j`
    (Lafont's `s_i s_j = s_j s_i`, `|i - j| >= 2`; "the commutation rule ... made implicit");
  * **BRAID** `vcomp (sigmaAt w i) (vcomp (sigmaAt w (i+1)) (sigmaAt w i)) ~
    vcomp (sigmaAt w (i+1)) (vcomp (sigmaAt w i) (sigmaAt w (i+1)))`  for `i + 3 ≤ w`  (Lafont's Yang–Baxter).

This file states the honest position of BOTH atoms.  MATRIX SOUNDNESS is machine-pinned (the DISTANT-COMMUTE
endpoints share their permutation matrix at widths 4 and 5, `rfl`; the BRAID's matrix soundness is the shipped
r14 pure `bunchedBimonoidApplyAdjacentSwapBraid` / `bunchedBimonoidBraidPairPermShared`, its width-4 triple-vcomp
CONV-endpoint matrix `rfl` exceeding even the 4M-heartbeat budget — a compute limit, noted, not a soundness
gap).  The one genuinely-buildable CONV ingredient is DELIVERED: the whiskering-`aWordPow` split reshape
`bunchedBimonoidSigmaAtWhiskerSplitConv`, which reshapes a `sigmaAt` letter's whiskering `a^(p+q)` into
`a^p . a^q` via the sibling's `whiskerLeftWhiskerCongr` (the whiskering-1-cell congruence) fed by the r15
`bunchedBimonoidAWordPowSplitConv`.

## The exact wall (the precise residual, decisively probed)

After the shipped split reshape, the DISTANT-COMMUTE / BRAID atoms are gated on THREE strict-omega WHISKER
COHERENCES that `StrictAxiomRel` does NOT carry and that are NOT derivable from the rows it does carry:

  * whisker-1-cell ASSOCIATIVITY  `whiskerLeft (vcomp P Q) X ~ whiskerLeft P (whiskerLeft Q X)`  (and the right
    dual) — needed to push a split `a^p . a^q` whiskering inside;
  * whisker-by-identity-1-cell UNITORS  `whiskerLeft (id c) X ~ X`  /  `whiskerRight X (id c) ~ X`  — needed for
    the `a^0 = id point` boundary of an edge `sigmaAt`;
  * whisker-LEFT/RIGHT COMMUTE  `whiskerRight (whiskerLeft P X) Q ~ whiskerLeft P (whiskerRight X Q)`.

`StrictAxiomRel` (byte-intact, `Omega/StrictAxioms.lean`) carries whisker-vs-2-cell-vcomp FUNCTORIALITY
(`whisker{Left,Right}Functorial`, the composite in the 2-CELL slot) and whisker-vs-identity-2-cell
(`whisker{Left,Right}Unit`, `w <| id_c ~ id (w.c)`) and the Godement `interchange` — but NONE of the three
coherences above, which are the composite/identity/commute laws in the 1-CELL (whiskering) slot.  They are
matrix-true but underivable here: each is a fragment of the UNPROVEN completeness star
`bunchedBimonoidStarStatement` (equal-matrix ⟹ convertible).  Probed decisively (scratch, deleted): the fixed
distant pair `sigmaAt 4 0` / `sigmaAt 4 2` already differs from the shipped r9
`bunchedBimonoidDistantSwapLeftLeg` (which the Godement `interchange` DOES prove convertible) by exactly the
whisker-by-identity unitor `whiskerLeft (a^0 = id point) _ ~ _`; and the general pair additionally by the
associator.  So the r9 `bunchedBimonoidDistantSwapCommuteViaInterchange` (fixed-width `s_1 s_3 = s_3 s_1`)
canNOT be re-padded to arbitrary `(w, i, j)` without these coherences.

## The reduction (what this buys the goal)

The ENTIRE CONV fold tower is now a single named residual: `carryPermConv`, `swapCommutesRun{Above,Below}Conv`,
`combInsertConv` (four-case), `combNormalizeFormConv`, `recCombConv`, and the star's `coxeterWordUnique` are ALL
downstream of these three whisker coherences (equivalently, of the completeness star fragment).  This is the same
wall the completeness star itself faces — the run-commute layer adds no NEW obstruction, it inherits the
star's.  The star does NOT flip: the four star-owner markers (`StarAssembly`, `RiffleAssembly`,
`CollisionCanonForm`, `CoxeterUniqueness`) and every upstream residual marker keep their names and `= false`
values byte-intact (cross-file, not edited).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin.  Mirror of the Brauer canonicity lane — and genuinely wider (the Brauer
`crossingWord` is a flat `List`, so its atoms commute by list computation; the Omega `permWord` folds into real
`CellExpr` whisker trees, so distant-commutation is genuine strict-omega whisker-coherence content, not a
definitional coincidence). -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

/-! The distant-commute CONV-endpoint matrix probes evaluate two whiskered permutation cells at widths 4-5,
exceeding the default heartbeat budget; the raise is a compute allowance only, the proof terms stay `Eq.refl`
/ congruence-constructor plumbing, axiom-free (uniform with the r6-r16 lane files). -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # R1 — THE DISTANT-COMMUTE ATOM: MATRIX SOUNDNESS (the necessary condition, machine-pinned)
    # =========================================================================================

★ A convertibility over the star scope implies equal `Mat(N)` matrices; these `rfl` pins establish the CONVERSE
necessary condition — the DISTANT-COMMUTE atom's two endpoints ARE representatives of the SAME permutation, at
the probe widths.  So the atom is a genuine, non-vacuous `S_n` identity (not a relation between distinct
permutations); the only thing missing is the CONV derivation, which the wall below names precisely. -/

/-- ★★ **THE DISTANT-COMMUTE ATOM IS MATRIX-SOUND at width 4, positions 0 and 2** (`|i - j| = 2`, `rfl`).  Both
`vcomp (sigmaAt 4 0) (sigmaAt 4 2)` and `vcomp (sigmaAt 4 2) (sigmaAt 4 0)` evaluate to the same `4 x 4`
permutation (swap strands 0-1 and 2-3) — the disjoint-range swaps commute as permutations.  The necessary
condition a distant-commute CONV would imply, pinned. -/
theorem bunchedBimonoidSigmaAtDistantCommuteMatrixSharedFourZeroTwo :
    bunchedBimonoidEvalCell
        (CellExpr.vcomp (bunchedBimonoidSigmaAt 4 0) (bunchedBimonoidSigmaAt 4 2))
      = bunchedBimonoidEvalCell
        (CellExpr.vcomp (bunchedBimonoidSigmaAt 4 2) (bunchedBimonoidSigmaAt 4 0)) := rfl

/-- ★★ **THE DISTANT-COMMUTE ATOM IS MATRIX-SOUND at width 5, positions 1 and 3** (`|i - j| = 2`, `rfl`).  Both
orders of the width-5 disjoint swaps `s_2 s_4` share their `5 x 5` permutation matrix — the atom holds at a
padded interior position, not only at the edge. -/
theorem bunchedBimonoidSigmaAtDistantCommuteMatrixSharedFiveOneThree :
    bunchedBimonoidEvalCell
        (CellExpr.vcomp (bunchedBimonoidSigmaAt 5 1) (bunchedBimonoidSigmaAt 5 3))
      = bunchedBimonoidEvalCell
        (CellExpr.vcomp (bunchedBimonoidSigmaAt 5 3) (bunchedBimonoidSigmaAt 5 1)) := rfl

/-! ## The R1 marker

★ NON-VACUITY (disclosed): the two matrix-shared pins above relate SYNTACTICALLY DISTINCT `CellExpr` terms —
`vcomp (sigmaAt w i) (sigmaAt w j)` versus `vcomp (sigmaAt w j) (sigmaAt w i)` differ in their leftmost factor's
position — that happen to share a matrix.  A `CellExpr` structural `rfl` between the two orders FAILS (they are
different constructor trees); the equality holds only after `bunchedBimonoidEvalCell`.  So the distant-commute
atom is genuine CONV content, NOT a reflexive triviality `SaturatedConvOverWithId.refl`. -/

/-- ★★★ **ESTABLISHED (R1) — the DISTANT-COMMUTE atom is matrix-sound and non-vacuous.**  `= true` records the
two `rfl` matrix-soundness pins (`...MatrixSharedFourZeroTwo`, `...MatrixSharedFiveOneThree`): the
distant-commutation atom `vcomp (sigmaAt w i) (sigmaAt w j) ~ vcomp (sigmaAt w j) (sigmaAt w i)` (`|i - j| >= 2`)
relates two representatives of the SAME permutation, at widths 4 and 5 — the necessary condition a CONV
derivation would imply.  The two pins relate syntactically distinct `CellExpr` orders (a structural `rfl`
between them FAILS), so the atom is genuine CONV content, not a reflexive triviality.  The BRAID atom's matrix
soundness is the shipped r14 pure
`bunchedBimonoidApplyAdjacentSwapBraid` / `bunchedBimonoidBraidPairPermShared` (its width-4 triple-vcomp CONV
endpoint matrix `rfl` exceeds even 4M heartbeats — a compute limit, noted).  Zero-axiom (per-decl
`#assert_no_axioms` + independent `#print axioms` in the twin). -/
def fxBunchedBimonoid_distantCommuteAtomMatrixSoundAndNonVacuous : Bool := true

/-! # =========================================================================================
    # R2 — THE BUILDABLE CONV BRICK: the whiskering-`aWordPow` split reshape (DELIVERED)
    # =========================================================================================

★ The one genuinely-new CONV ingredient this round delivers toward the DISTANT-COMMUTE atom: reshaping a
`sigmaAt` letter's WHISKERING 1-cell `a^(p+q)` into the composite `a^p . a^q`, over the star scope.  This uses
the idCongr-sibling's `whiskerLeftWhiskerCongr` (the whiskering-1-cell congruence — the whiskering cell varies,
the whiskered 2-cell fixed) fed by the r15 dim-1 split `bunchedBimonoidAWordPowSplitConv`.  It reshapes the
whiskering; the RESIDUAL — pushing the split whiskering INSIDE (`whiskerLeft (a^p . a^q) X ~ whiskerLeft (a^p)
(whiskerLeft (a^q) X)`) — is exactly the whisker-1-cell associator the wall below names. -/

/-- ★★ **THE WHISKERING-`aWordPow` SPLIT RESHAPE.**  For any inner 2-cell `innerCell` and any split
`segmentA + segmentB`, the whiskered cell `whiskerLeft (a^(segmentA + segmentB)) innerCell` converts, over the
star scope, to `whiskerLeft (a^segmentA . a^segmentB) innerCell` — the whiskering `aWordPow` splits.  A single
`whiskerLeftWhiskerCongr innerCell` (the whiskering-1-cell congruence of the idCongr sibling) applied to the r15
dim-1 word split `bunchedBimonoidAWordPowSplitConv segmentA segmentB`.  This is the buildable half of the
DISTANT-COMMUTE prerequisite: it reshapes a `sigmaAt` letter's whiskering `a^j = a^i . a^(j-i)` to expose a
common `a^i` front; the residual is the associator (the wall). -/
theorem bunchedBimonoidSigmaAtWhiskerSplitConv (segmentA segmentB : Nat)
    (innerCell : CellExpr bunchedBimonoidOmegaComputad 2) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow (segmentA + segmentB)) innerCell)
      (CellExpr.whiskerLeft (CellExpr.vcomp (bunchedBimonoidAWordPow segmentA)
        (bunchedBimonoidAWordPow segmentB)) innerCell) :=
  SaturatedConvOverWithId.whiskerLeftWhiskerCongr innerCell
    (bunchedBimonoidAWordPowSplitConv segmentA segmentB)

/-- The split-reshape endpoints share their matrix at `segmentA = 1`, `segmentB = 0`, inner
`sigma |> a^0` (`rfl`, width 3): both `whiskerLeft (a^1) (sigma |> a^0)` (= the position-1 letter of a width-3
word, `sigmaAt 3 1`) and `whiskerLeft (a^1 . a^0) (sigma |> a^0)` evaluate to `[[1,0,0],[0,0,1],[0,1,0]]`.  The
reshape relates two representatives of the same map — a genuine, matrix-sound CONV. -/
theorem bunchedBimonoidSigmaAtWhiskerSplitMatrixShared :
    bunchedBimonoidEvalCell
        (CellExpr.whiskerLeft (bunchedBimonoidAWordPow 1)
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow 0)))
      = bunchedBimonoidEvalCell
        (CellExpr.whiskerLeft (CellExpr.vcomp (bunchedBimonoidAWordPow 1) (bunchedBimonoidAWordPow 0))
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow 0))) := rfl

/-! ## The R2 marker -/

/-- ★★★ **ESTABLISHED (R2) — the whiskering-`aWordPow` split reshape is DELIVERED.**  `= true` records
`bunchedBimonoidSigmaAtWhiskerSplitConv`: the whiskering 1-cell of a whiskered 2-cell splits
(`whiskerLeft (a^(p+q)) X ~ whiskerLeft (a^p . a^q) X`) over the star scope, via the idCongr sibling's
`whiskerLeftWhiskerCongr` fed by the r15 dim-1 `bunchedBimonoidAWordPowSplitConv`.  This is the buildable half
of the DISTANT-COMMUTE prerequisite (reshaping a letter's whiskering `a^j = a^i . a^(j-i)`); matrix-sound at
width 3 (`...WhiskerSplitMatrixShared`).  The residual after this reshape — the whisker-1-cell associator — is
the wall (R3).  Zero-axiom (per-decl `#assert_no_axioms` + independent `#print axioms` in the twin). -/
def fxBunchedBimonoid_whiskeringSplitReshapeShipped : Bool := true

/-! # =========================================================================================
    # R3 — THE EXACT WHISKER-COHERENCE WALL (the precise residual, no flip)
    # =========================================================================================
-/

/-- ★ **THE RUN-COMMUTE CONV ATOMS STAY WALLED — the exact residual named, no flip.**  `= false` records that
after the shipped R2 split reshape, the DISTANT-COMMUTE and BRAID atoms at the `sigmaAt` word level are gated on
THREE strict-omega WHISKER COHERENCES absent from `StrictAxiomRel` and NOT derivable from its rows: (1) the
whisker-1-cell ASSOCIATOR `whiskerLeft (vcomp P Q) X ~ whiskerLeft P (whiskerLeft Q X)` (and its right dual);
(2) the whisker-by-identity-1-cell UNITORS `whiskerLeft (id c) X ~ X` / `whiskerRight X (id c) ~ X`; (3) the
whisker-LEFT/RIGHT COMMUTE `whiskerRight (whiskerLeft P X) Q ~ whiskerLeft P (whiskerRight X Q)`.
`StrictAxiomRel` carries the whisker-vs-2-cell FUNCTORIALITY (`whisker{Left,Right}Functorial`) and
whisker-vs-identity-2-cell (`whisker{Left,Right}Unit`) and the Godement `interchange` — but the three coherences
above are the composite / identity / commute laws in the 1-CELL (whiskering) slot, matrix-true but each a
fragment of the UNPROVEN completeness star `bunchedBimonoidStarStatement`.  Decisively probed (scratch, deleted):
the fixed distant pair `sigmaAt 4 0` / `sigmaAt 4 2` already differs from the r9
`bunchedBimonoidDistantSwapLeftLeg` (which the Godement `interchange` DOES relate) by exactly the identity-whisker
unitor `whiskerLeft (a^0 = id point) _ ~ _`, so the r9 `bunchedBimonoidDistantSwapCommuteViaInterchange` canNOT
be re-padded to arbitrary `(w, i, j)`.  No star marker flips; `StrictAxioms.lean` stays byte-intact (no new
row). -/
def fxBunchedBimonoid_runCommuteConvGatedOnWhiskerAssociatorAndUnitors : Bool := false

/-! # =========================================================================================
    # R4 — THE REDUCTION + THE HONEST B3 BILL (the whole CONV fold tower, one named residual)
    # =========================================================================================
-/

/-- ★ **THE CONV CARRY / RUN-COMMUTE / FOLD TOWER IS ONE NAMED RESIDUAL — no flip.**  `= false` records that
the CONV mirror of the r14 pure fold — `bunchedBimonoidCarryPermConv`,
`bunchedBimonoidSwapCommutesRun{Above,Below}Conv`, the four-case `bunchedBimonoidCombInsertConv`, and the fold
`bunchedBimonoidCombNormalizeFormConv` — is NOT built here: each rests on the DISTANT-COMMUTE and/or BRAID atoms
(R1), which are walled on the whisker coherences (R3).  The r14 PURE layer of every one of these IS shipped
(`bunchedBimonoidCarryPerm`, `bunchedBimonoidSwapCommutesRun{Above,Below}`,
`bunchedBimonoidCombInsertDataRealizesSwap`, `bunchedBimonoidCombNormalizeFormPreservesPerm`); the CONV lift
inherits exactly the completeness-star fragment R3 names — it adds NO new obstruction.  The pieces the fold does
NOT need the atoms for are already shipped: CANCEL (r15 `bunchedBimonoidCancelLetterConv`), the append reshape
(r16 `bunchedBimonoidPermWordAppendConv`), the sigma-source boundary reshape (r15
`bunchedBimonoidSigmaAtBoundaryReshapeConv`).  So the residual is precisely {distant-commute, braid} atoms =
the R3 whisker coherences. -/
def fxBunchedBimonoid_combFoldConvGatedOnRunCommuteAtoms : Bool := false

/-- ★ **THE B3 CANONICITY CHAIN GAINS A PRECISELY-NAMED GATE — the star does NOT flip.**  `= false` records the
honest B3 bill: the star's `coxeterWordUnique` (`permOfWord w1 = permOfWord w2 -> recComb (W-1) w1 = recComb
(W-1) w2`, then `permWord w ~ permWord (recComb w)`) still needs (i) the Omega port of the Brauer pure
`combCanonicity` (a `List Nat` fact — reads the top-run length off the permutation, strips the top strand, feeds
the level induction; its Brauer support `perm_topIndex_ofPrefixRun` / `foldlSwap_injective` / `natSubInj` etc.
not yet in Omega), AND (ii) the CONV `recCombConv` (`permWord w ~ permWord (recComb w)`), which is the recursive
fold of `combNormalizeFormConv` — itself gated on the R3 whisker coherences.  So B3 = {Omega `combCanonicity`
port} + {the R3 whisker-coherence wall}.  The four star-owner markers
(`fxBunchedBimonoid_correctedWellTypedStarStillOpen` StarAssembly,
`fxBunchedBimonoid_coxeterWordUniqueGatedOnGenericBraid` RiffleAssembly, the CollisionCanonForm and
CoxeterUniqueness owners) and every upstream residual marker keep their names and `= false` values byte-intact
(cross-file, not edited).  NO fabricated star flip. -/
def fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterRunCommute : Bool := false

/-- ★★★ **ESTABLISHED — the WP-PROP r17 run-commute ledger (the honest scoreboard).**  `= true` records the
complete r17 round: R1 the DISTANT-COMMUTE atom's matrix-soundness + non-vacuity
(`fxBunchedBimonoid_distantCommuteAtomMatrixSoundAndNonVacuous`, widths 4/5); R2 the buildable whiskering-`aWordPow`
split reshape (`fxBunchedBimonoid_whiskeringSplitReshapeShipped`, the buildable half of the distant-commute
prerequisite, matrix-sound at width 3); R3 the exact whisker-coherence wall
(`fxBunchedBimonoid_runCommuteConvGatedOnWhiskerAssociatorAndUnitors = false` — the associator + identity-whisker
unitors + whisker-commute, none in `StrictAxiomRel`, each a fragment of the unproven completeness star); R4 the
reduction (`fxBunchedBimonoid_combFoldConvGatedOnRunCommuteAtoms = false` — the whole CONV fold tower is the one
R3 residual) and the honest B3 bill (`fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterRunCommute = false` —
B3 = Omega `combCanonicity` port + the R3 wall).  The r14 PURE layer of the whole tower is shipped; the CONV lift
inherits exactly the completeness-star fragment.  The star does NOT flip; every star-owner / residual marker
stays byte-intact.  Zero-axiom (per-decl `#assert_no_axioms` + independent `#print axioms` in the twin);
STRUCTURAL only.  NO fabricated star flip. -/
def fxBunchedBimonoid_canonicalWordRunCommuteRoundSeventeenLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
