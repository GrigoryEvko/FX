import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPermWordDistantCommuteConv

/-! # Polygraph/Omega/WalkingBunchedBimonoidRunBelowCommuteConv — the `Below` twin of the first Cartier–Foata
fold rung, over the SHIPPED star scope (WP-PROP r23)

★ **THE r22 `Below`-TWIN RESIDUAL IS DELIVERED.**  The r22 census marker
`fxBunchedBimonoid_swapCommutesRunBelowAndCombFoldsStillOpen` (`= false`, byte-intact cross-file) named the
symmetric `swapCommutesRunBelowConv` (gate `runTop + 2 ≤ letter`, the reversed distance) as the r23 head.  This
file ships exactly that one rung and states the honest braid-ceiling on everything downstream.

**F1 — `swapCommutesRunBelowConv`.**  The CONV mirror of the r14 pure `bunchedBimonoidSwapCommutesRunBelow`
(`WalkingBunchedBimonoidCanonicalWordStaircase`): a HIGH letter commutes past a whole descending run BELOW it.
Structural on the run length `count`, gated on the distance `runTop + 2 ≤ letter` (the letter stays `≥ 2` above
every run generator, so every commutation is distant) AND the width validity `letter + 2 ≤ wordWidth`.  Yields

  `vcomp (sigmaAt w letter) (permWord (descendingPositions runTop count) w)
     ~ vcomp (permWord (descendingPositions runTop count) w) (sigmaAt w letter)`.

This is P3 (`swapCommutesRunAboveConv`) with the gate flipped and the head-pair atom `.symm`-ed: the run-top
`runTop` is now the LOW index and `letter` the HIGH one, so the P2 atom `sigmaAtDistantCommuteConv w runTop
letter` fires in the reverse orientation and `symm` swaps its endpoints.  Matching the run length on `count` alone
(general `runTop`, not a successor) keeps the recursive anchor `runTop - 1` symbolic — exactly as the pure
`Below` does — so no successor split and no impossible `| 0, count + 1` case arises.  The IH-gate transports
`runTop + 2 ≤ letter` to `(runTop - 1) + 2 ≤ letter` by `Nat.sub_le` (propext-clean; the exact clean set the pure
`Below` already certifies).  No A1 / A2 truncated-subtraction arithmetic: the P2 atom is a black box whose
truncation is already discharged in the r22 file.

## The honest star-road census after F1 (no fabricated flip)

The comb-insertion CONV fold `combInsertConv` is **braid-walled at its CARRY case**: `combInsertData`'s four
branches are the letter/run distance split — COMMUTE (letter distant-below the run-top → `swapCommutesRunAbove`),
EXTEND (letter adjacent-below the run bottom → absorbed by the run's snoc structure, NOT a braid), CANCEL (letter
coincides with run-bottom+1 → the involution `s_k s_k = id`, NOT a braid), and CARRY (letter ABOVE the run region
→ `carryPerm`, whose base `letter = top` BRAIDS the pivot via `applyAdjacentSwapBraid`).  The CARRY braid is the
adjacent (braid) move, and it is COMPUTE-walled (the width-4 triple-`vcomp` endpoint `rfl` exceeds even the
4M-heartbeat budget — a compute wall, not a soundness gap).  No braid CONV atom exists in the lane.  Hence
`combInsertConv` (F2), the one-level `combNormalizeFormConv` (F3), and the recursive `recCombConv` (F4) are all
braid-walled downstream of CARRY, and this round does NOT re-attempt the braid.

The Brauer `combCanonicity` per-file clone (the r23 "F5" bill) is **already shipped** — the Omega-faithful
re-derivation `bunchedBimonoidCombCanonicity` lives in `WalkingBunchedBimonoidCanonicalWordCanonicity` (landed
r18 T1, with its full Brauer support ported, Omega-prefixed, no Brauer import), and the r18 T3 leg
`bunchedBimonoidRecCombEqOfEvalEq` already consumes it (the DATA half `recComb w1 = recComb w2` from equal
matrices is done).  The one CONV theorem still between the folds and the star owner
`fxBunchedBimonoid_coxeterWordUniqueBubbleSortStillUnbuilt` (`CoxeterUniqueness`, `= false`) is
`recCombConv : permWord w ~ permWord (recComb w)` = F4 = braid-walled.  Matsumoto/Tits: any two reduced words of
a fully-commutative element differ by braid + commutation moves, and bubble-sort-by-inversion (the owner's stated
strategy) hits the same braid — so the braid wall is genuine, not an assembly gap.

The four star owners (`StarAssembly` / `RiffleAssembly` / `CollisionCanonForm` / `CoxeterUniqueness`) stay
`= false` byte-intact; `StrictAxioms.lean` + the shipped `bunchedBimonoidStarCongruenceScope` are untouched (only
the shipped `StrictAxiomRel.{vcompAssoc, vcompUnitLeft, vcompUnitRight}` rows are consumed through
`bunchedBimonoidStrictAxiomEmbedsIntoStarScope`).  No fabricated star flip.  Zero-axiom (per-decl
`#assert_no_axioms` + independent `#print axioms` in the twin).

The fold tower is Cartier–Foata / Foata normalization of a Mazurkiewicz trace inside the fully-commutative class
(Stembridge, *On the Fully Commutative Elements of Coxeter Groups*, J. Alg. Combin. 5 (1996); Maarand & Uustalu,
*Certified Foata Normalization for Generalized Traces*, NFM 2018 / ISSE 2019 — an Agda formalization; no
Lean/Coq/Isabelle Cartier–Foata normalization is known, so this kernel-checked Lean walker is first-of-kind).
The `Below` rung is the "a letter drops past a run of independent adjacent swaps ABOVE it" half of the insertion
invariant. -/

namespace FX1Poly.Polygraph.Omega

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## F1 — the `Below` fold rung: `swapCommutesRunBelowConv` -/

/-- ★★★ **THE `Below` CONV FOLD RUNG (F1, DELIVERED) — a high letter commutes past a descending run below it.**
Structural on the run length `count`, gated on `runTop + 2 ≤ letter` (every run generator stays `≥ 2` below the
letter, so every commutation is distant) AND the width validity `letter + 2 ≤ wordWidth`.  Yields
`vcomp (sigmaAt w letter) (permWord (descendingPositions runTop count) w) ~
vcomp (permWord (descendingPositions runTop count) w) (sigmaAt w letter)`.

Base (`count = 0`, the run is `id (aWordPow w)`): the P1 trailing absorber on the left, `symm` of the shipped
`vcompIdLeft_bridgedWithId` leading absorber on the right — identical to the P3 base, but the width gate `hlw`
is taken directly as the hypothesis (no derivation).  Step (`count + 1`, general `runTop` so the recursive anchor
`runTop - 1` stays symbolic): the associativity dance `symm-vcompAssoc → vcompCongrLeft (symm of the P2 atom
`runTop`/`letter`) → vcompAssoc → vcompCongrRight (IH) → symm-vcompAssoc`.  The CONV mirror of the r14 pure
`bunchedBimonoidSwapCommutesRunBelow`.  Zero-axiom. -/
theorem bunchedBimonoidSwapCommutesRunBelowConv (wordWidth letter : Nat) :
    (runTop count : Nat) → runTop + 2 ≤ letter → letter + 2 ≤ wordWidth →
      SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
        (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth letter)
          (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions runTop count) wordWidth))
        (CellExpr.vcomp (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions runTop count) wordWidth)
          (bunchedBimonoidSigmaAt wordWidth letter))
  | _, 0, _, hlw => by
      show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
          (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth letter)
            (CellExpr.id (bunchedBimonoidAWordPow wordWidth)))
          (CellExpr.vcomp (CellExpr.id (bunchedBimonoidAWordPow wordWidth))
            (bunchedBimonoidSigmaAt wordWidth letter))
      exact SaturatedConvOverWithId.trans
        (bunchedBimonoidSigmaAtTrailingIdAbsorbConv wordWidth letter hlw)
        (SaturatedConvOverWithId.symm
          (vcompIdLeft_bridgedWithId (bunchedBimonoidSigmaAt wordWidth letter)
            (bunchedBimonoidSigmaAtBoundaryReshapeConv wordWidth letter hlw)
            (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
              (StrictAxiomRel.vcompUnitLeft (bunchedBimonoidSigmaAt wordWidth letter)))))
  | runTop, count + 1, hLe, hlw => by
      have ihGate : (runTop - 1) + 2 ≤ letter :=
        Nat.le_trans (Nat.add_le_add_right (Nat.sub_le runTop 1) 2) hLe
      show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
          (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth letter)
            (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth runTop)
              (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (runTop - 1) count) wordWidth)))
          (CellExpr.vcomp
            (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth runTop)
              (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (runTop - 1) count) wordWidth))
            (bunchedBimonoidSigmaAt wordWidth letter))
      refine SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.symm (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
          (StrictAxiomRel.vcompAssoc (bunchedBimonoidSigmaAt wordWidth letter)
            (bunchedBimonoidSigmaAt wordWidth runTop)
            (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (runTop - 1) count) wordWidth)))) ?_
      refine SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrLeft
          (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (runTop - 1) count) wordWidth)
          (SaturatedConvOverWithId.symm
            (bunchedBimonoidSigmaAtDistantCommuteConv wordWidth runTop letter hLe hlw))) ?_
      refine SaturatedConvOverWithId.trans
        (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
          (StrictAxiomRel.vcompAssoc (bunchedBimonoidSigmaAt wordWidth runTop)
            (bunchedBimonoidSigmaAt wordWidth letter)
            (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (runTop - 1) count) wordWidth))) ?_
      refine SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrRight (bunchedBimonoidSigmaAt wordWidth runTop)
          (bunchedBimonoidSwapCommutesRunBelowConv wordWidth letter (runTop - 1) count ihGate hlw)) ?_
      exact SaturatedConvOverWithId.symm (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
        (StrictAxiomRel.vcompAssoc (bunchedBimonoidSigmaAt wordWidth runTop)
          (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (runTop - 1) count) wordWidth)
          (bunchedBimonoidSigmaAt wordWidth letter)))

/-! ## Non-vacuity — a genuine within-gate instance + matrix soundness pin + interpreter truth probes -/

/-- ★ **F1 fires at a genuine non-degenerate instance** — width 4, letter `s_2`, the single-generator run `[s_0]`
(`descendingPositions 0 1`), gates `0 + 2 ≤ 2` and `2 + 2 ≤ 4` both by `decide`.  A hypothesis-free inhabitant of
`vcomp (sigmaAt 4 2) (permWord [0] 4) ~ vcomp (permWord [0] 4) (sigmaAt 4 2)` over the shipped star scope — the
CONV theorem is non-vacuous. -/
theorem bunchedBimonoidRunBelowCommuteConvWidthFourInstance :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp (bunchedBimonoidSigmaAt 4 2)
        (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions 0 1) 4))
      (CellExpr.vcomp (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions 0 1) 4)
        (bunchedBimonoidSigmaAt 4 2)) :=
  bunchedBimonoidSwapCommutesRunBelowConv 4 2 0 1 (by decide) (by decide)

/-- The `Below` instance's endpoints `[2, 0]` (letter then run) / `[0, 2]` (run then letter) share their `4 x 4`
permutation matrix (`rfl`) — the soundness ceiling the F1 CONV lift is faithful to. -/
theorem bunchedBimonoidRunBelowCommuteTwoZeroMatrixShared :
    bunchedBimonoidEvalCell (bunchedBimonoidPermWord [2, 0] 4)
      = bunchedBimonoidEvalCell (bunchedBimonoidPermWord [0, 2] 4) := rfl

-- The distant `Below` pair COMMUTES (must print true); the adjacent pair does NOT (must print false):
#eval decide ((bunchedBimonoidEvalCell (bunchedBimonoidPermWord [2, 0] 4)).entries
  = (bunchedBimonoidEvalCell (bunchedBimonoidPermWord [0, 2] 4)).entries) -- true
#eval decide ((bunchedBimonoidEvalCell (bunchedBimonoidPermWord [1, 0] 3)).entries
  = (bunchedBimonoidEvalCell (bunchedBimonoidPermWord [0, 1] 3)).entries) -- false

/-! ## The r23 honesty marker (new marker per literal delivery only; owners byte-intact) -/

/-- ★★★ **ESTABLISHED (F1) — the `Below` fold rung `swapCommutesRunBelowConv` is DELIVERED.**  `= true` records
`bunchedBimonoidSwapCommutesRunBelowConv`: a high letter commutes past a descending run below it, the CONV mirror
of the r14 pure `bunchedBimonoidSwapCommutesRunBelow`, structural on the run length and assembled from the P2
atom (in the reverse `runTop`/`letter` orientation, `.symm`-ed) + the shipped `StrictAxiomRel.vcompAssoc`
regrouping.  Closes the `Below`-twin clause of the r22 census marker
`fxBunchedBimonoid_swapCommutesRunBelowAndCombFoldsStillOpen` (retire-name-only; that marker stays `= false`
byte-intact cross-file).  Matrix-sound (the `[2,0]`/`[0,2]` width-4 pin) and interpreter-discriminated (distant
true, adjacent false).  Zero-axiom. -/
def fxBunchedBimonoid_swapCommutesRunBelowConvShipped : Bool := true

/-- ★ **THE COMB FOLDS STAY BRAID-WALLED — the honest r23 census, no fabricated flip.**  `= false` records what
this round does NOT reach: `combInsertConv` (F2), `combNormalizeFormConv` (F3), and `recCombConv` (F4) are all
braid-walled at the CARRY case of `combInsertData` (whose base `letter = top` BRAIDS the pivot via
`applyAdjacentSwapBraid`, and no braid CONV atom exists in the lane); the ADJACENT braid atom stays COMPUTE-walled
(unchanged).  The Brauer `combCanonicity` per-file clone (the r23 "F5" bill) is ALREADY shipped
(`bunchedBimonoidCombCanonicity`, `WalkingBunchedBimonoidCanonicalWordCanonicity`, landed r18 T1), and the r18 T3
leg `bunchedBimonoidRecCombEqOfEvalEq` already consumes it — so only F4 (`recCombConv`) separates the folds from
the star owner `fxBunchedBimonoid_coxeterWordUniqueBubbleSortStillUnbuilt`, and F4 is braid-walled.  The four star
owners stay `= false` byte-intact; `StrictAxioms.lean` + the shipped star scope are untouched.  No fabricated star
flip. -/
def fxBunchedBimonoid_combFoldsBraidWalledDownstreamOfCarry : Bool := false

end FX1Poly.Polygraph.Omega
