import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidDistantCommuteOverSibling

/-! # Polygraph/Omega/WalkingBunchedBimonoidRunCommuteConvOverSibling — the first CONV run-commute lemma over the
U1 sibling: the distant pair commutes at the HEAD of any run (`vcompAssoc` + the U2 atom), with the honest
star-chain census after U3 (WP-PROP r20, U3)

★ **THE FIRST RUN-COMMUTE-CONV LEMMA, DELIVERED OVER THE SIBLING.**  r17 named the whole CONV fold tower
(`carryPermConv`, `swapCommutesRun{Above,Below}Conv`, the four-case `combInsertConv`, `combNormalizeFormConv`,
`recCombConv`) as ONE residual, gated at its irreducible bottom on the two atomic Coxeter moves at the `sigmaAt`
word level.  U2 closed the DISTANT-COMMUTE atom `(4, 0, 2)` over the sibling
(`bunchedBimonoidDistantSwapCommuteFourZeroTwoOverSibling`).  This file spends that atom to deliver the FIRST
genuine run-commute-CONV lemma — the `swapCommutesRun`-shaped statement that the distant pair commutes at the
HEAD of an arbitrary trailing run, generic in the run tail, via `vcompAssoc` regrouping.

## The run-head lemma (the `swapCommutesRunBelow` shape)

For any trailing run `runTail : CellExpr .. 2`,
`vcomp (sigmaAt 4 0) (vcomp (sigmaAt 4 2) runTail) ~ vcomp (sigmaAt 4 2) (vcomp (sigmaAt 4 0) runTail)`
over the sibling: regroup left by `vcompAssoc` (`symm`), fire the U2 atom under `vcompCongrLeft runTail`, regroup
right by `vcompAssoc`.  The distant pair slides past each other at the head of any run — the atom's first
consumer up the fold tower, generic in the tail.

## The honest star-chain census AFTER U3 (what remains)

The r17 R4 tower and the star's `coxeterWordUnique` still need, over the sibling:

  1. the DISTANT-COMMUTE atom at GENERIC `(w, i, j)` (`i + 2 <= j`, arbitrary middle gap) — the general block
     Godement interchange, a completeness-star fragment (U2 delivered only the width-4 fixed-block `(4, 0, 2)`);
  2. the BRAID atom `sigmaAt w i . sigmaAt w (i+1) . sigmaAt w i ~ sigmaAt w (i+1) . sigmaAt w i . sigmaAt w (i+1)`
     over the sibling (its width-4 triple-vcomp endpoint matrix `rfl` exceeds even the 4M-heartbeat budget — a
     compute limit, cited as in r14/r17, not a soundness gap);
  3. the TRAILING-BOUNDARY reshape `boundaryTarget (sigmaAt w k) ~ aWordPow w` (a dim-1 word reshape lifting the
     `vcomp`-form run lemmas here to the `permWord [..] w` fold — part of the r15/r16 append tower);
  4. the CONV folds `swapCommutesRun{Above,Below}Conv` / `combInsertConv` / `combNormalizeFormConv` /
     `recCombConv` assembled from (1)-(3) by the fuel-structural bubble sort;
  5. the Omega port of the Brauer pure `combCanonicity` (`perm_topIndex_ofPrefixRun` / `foldlSwap_injective` /
     `natSubInj`) — an orthogonal `List Nat` fact, not a whisker coherence.

The four star owners (`StarAssembly` / `RiffleAssembly` / `CollisionCanonForm` / `CoxeterUniqueness`) stay
`= false` byte-intact; the r17 `fxBunchedBimonoid_runCommuteConvGatedOnWhiskerAssociatorAndUnitors` (the
SHIPPED-scope marker) stays `= false` byte-intact — the SHIPPED star scope still lacks the unitor; U2/U3 close
over the ADDITIVE sibling, which is the honest denotation.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # U3.A — THE FIRST RUN-COMMUTE-CONV LEMMA (the distant pair commutes at the head of a run)
    # =========================================================================================
-/

/-- ★★★ **THE FIRST RUN-COMMUTE-CONV LEMMA OVER THE SIBLING — the distant pair commutes at the HEAD of any run.**
For any trailing run `runTail : CellExpr .. 2`,
`vcomp (sigmaAt 4 0) (vcomp (sigmaAt 4 2) runTail) ~ vcomp (sigmaAt 4 2) (vcomp (sigmaAt 4 0) runTail)` over
`bunchedBimonoidStarScopeWithPointUnitor`: regroup left by `vcompAssoc` (`symm`), fire the U2 atom
`bunchedBimonoidDistantSwapCommuteFourZeroTwoOverSibling` under `vcompCongrLeft runTail`, regroup right by
`vcompAssoc`.  The `swapCommutesRunBelow`-shaped first consumer of the distant-commute atom up the r17 fold
tower — generic in the run tail.  Non-vacuous: at `runTail = id (a^4)` the two heads are the syntactically
distinct atom endpoints (matrix-shared, `bunchedBimonoidDistantSwapCommuteFourZeroTwoMatrixShared`). -/
theorem bunchedBimonoidDistantCommuteRunHeadConvOverSibling
    (runTail : CellExpr bunchedBimonoidOmegaComputad 2) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarScopeWithPointUnitor
      (CellExpr.vcomp (bunchedBimonoidSigmaAt 4 0)
        (CellExpr.vcomp (bunchedBimonoidSigmaAt 4 2) runTail))
      (CellExpr.vcomp (bunchedBimonoidSigmaAt 4 2)
        (CellExpr.vcomp (bunchedBimonoidSigmaAt 4 0) runTail)) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.symm
      (bunchedBimonoidStarScopeEmbedsIntoPointUnitorSibling
        (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
          (StrictAxiomRel.vcompAssoc (bunchedBimonoidSigmaAt 4 0) (bunchedBimonoidSigmaAt 4 2) runTail))))
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.vcompCongrLeft runTail
        bunchedBimonoidDistantSwapCommuteFourZeroTwoOverSibling)
      (bunchedBimonoidStarScopeEmbedsIntoPointUnitorSibling
        (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
          (StrictAxiomRel.vcompAssoc (bunchedBimonoidSigmaAt 4 2) (bunchedBimonoidSigmaAt 4 0) runTail))))

/-- ★ **The run-head endpoints share their matrix at `runTail = id (a^4)` (`rfl`)** — instantiating the run tail
at the width-4 identity, both run heads collapse to the U2 atom endpoints, which share their `4 x 4` permutation
matrix.  A concrete non-vacuity witness for the generic run-head lemma. -/
theorem bunchedBimonoidDistantCommuteRunHeadMatrixShared :
    bunchedBimonoidEvalCell
        (CellExpr.vcomp (bunchedBimonoidSigmaAt 4 0)
          (CellExpr.vcomp (bunchedBimonoidSigmaAt 4 2) (CellExpr.id (bunchedBimonoidAWordPow 4))))
      = bunchedBimonoidEvalCell
        (CellExpr.vcomp (bunchedBimonoidSigmaAt 4 2)
          (CellExpr.vcomp (bunchedBimonoidSigmaAt 4 0) (CellExpr.id (bunchedBimonoidAWordPow 4)))) := rfl

/-! # =========================================================================================
    # U3.B — THE r17-MARKER LITERAL DELIVERY + THE HONEST STAR-CHAIN CENSUS (no fabricated flip)
    # =========================================================================================
-/

/-- ★★★ **ESTABLISHED (U3) — the first run-commute-CONV lemma over the sibling is SHIPPED.**  `= true` records
`bunchedBimonoidDistantCommuteRunHeadConvOverSibling`: the distant pair commutes at the HEAD of an arbitrary
trailing run over `bunchedBimonoidStarScopeWithPointUnitor`, via `vcompAssoc` regrouping around the U2 atom
`bunchedBimonoidDistantSwapCommuteFourZeroTwoOverSibling` — the `swapCommutesRunBelow`-shaped first consumer of
the atom up the r17 CONV fold tower, generic in the run tail, non-vacuous
(`...RunHeadMatrixShared`).  This is the r17-marker LITERAL delivery: a genuine run-commute-CONV lemma, over the
additive sibling, NOT a fabricated flip of a shipped-scope marker.  Zero-axiom (per-decl `#assert_no_axioms` +
independent `#print axioms` in the twin). -/
def fxBunchedBimonoid_distantCommuteRunConvOverSiblingShipped : Bool := true

/-- ★ **THE SHIPPED-SCOPE RUN-COMMUTE MARKER STAYS `false` — byte-intact, honest denotation.**  `= false`
records that the r17 `fxBunchedBimonoid_runCommuteConvGatedOnWhiskerAssociatorAndUnitors` (over the SHIPPED
`bunchedBimonoidStarCongruenceScope`) does NOT flip: the shipped star scope still genuinely LACKS the
identity-whisker unitor (the free form falsifies `linearizeFullSoundness`, machine-refuted r19), so the shipped
scope stays byte-intact and U2/U3 deliver their run-commute lemmas over the ADDITIVE sibling
`bunchedBimonoidStarScopeWithPointUnitor` instead.  The distinction is the whole point of the sibling
presentation — no shipped-marker denotation drift. -/
def fxBunchedBimonoid_shippedScopeRunCommuteStillGatedNoFlip : Bool := false

/-- ★ **THE STAR-CHAIN CENSUS AFTER U3 — the honest remaining bill, no fabricated flip.**  `= false` records the
residual after U3, over the sibling: (1) the DISTANT-COMMUTE atom at GENERIC `(w, i, j)` (the general block
Godement interchange — a completeness-star fragment; U2 delivered only the width-4 fixed-block `(4, 0, 2)`); (2)
the BRAID atom over the sibling (its width-4 triple-vcomp endpoint matrix `rfl` exceeds even 4M heartbeats — a
compute limit, cited as in r14/r17); (3) the TRAILING-BOUNDARY reshape `boundaryTarget (sigmaAt w k) ~ aWordPow
w` lifting the `vcomp`-form run lemmas to the `permWord` fold; (4) the CONV folds
`swapCommutesRun{Above,Below}Conv` / `combInsertConv` / `combNormalizeFormConv` / `recCombConv` assembled from
(1)-(3); (5) the Omega port of the Brauer pure `combCanonicity`.  The four star owners
(`fxBunchedBimonoid_correctedWellTypedStarStillOpen` StarAssembly,
`fxBunchedBimonoid_coxeterWordUniqueGatedOnGenericBraid` RiffleAssembly, and the CollisionCanonForm /
CoxeterUniqueness owners) stay `= false` byte-intact.  No fabricated star flip. -/
def fxBunchedBimonoid_starChainCensusAfterUThreeStillOpen : Bool := false

end FX1Poly.Polygraph.Omega
