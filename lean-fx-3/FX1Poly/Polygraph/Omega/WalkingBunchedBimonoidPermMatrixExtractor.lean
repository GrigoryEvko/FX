import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCollisionCanonForm

/-! # Polygraph/Omega/WalkingBunchedBimonoidPermMatrixExtractor — the matrix READ-OFF: a sigma-word's `Mat(N)`
matrix IS the permutation matrix of its one-line adjacent-swap fold (WP-PROP r11, #2033)

★ **THE r11 HEADLINE — the matrix side of `CoxeterWordUnique` is the permutation READ-OFF, the Omega mirror of the
Brauer `permutationDiagram_injective`.**  The r8 `RiffleAssembly` shipped the position-indexed transposition
carrier (`bunchedBimonoidSigmaAt`), the word-as-cell fold (`bunchedBimonoidPermWord`), and a fuel-structural
bubble sort — but the sort was machine-REFUTED as a matrix bridge (r10
`bunchedBimonoidBubbleSortNotMatrixPreserving`: integer-sorting positions does NOT preserve the permutation,
`s_2 s_1 != s_1 s_2`).  So the honest bridge is not "sort the word" but "READ the permutation off the matrix and
compare".  This file ships that read-off: a PURE `List Nat` symmetric-group engine
(`bunchedBimonoidApplyAdjacentSwap`, `bunchedBimonoidPermOfWord`) — reused verbatim from the Brauer canonicity
lane (`WiringDescStaircaseCanonical`), re-derived in-namespace because the Omega lane does not import Brauer — plus
the `bunchedBimonoidPermMatrixOf` permutation matrix, and the EXTRACTOR identity

  `bunchedBimonoidEvalCell (bunchedBimonoidPermWord positions width)
     = bunchedBimonoidPermMatrixOf width (bunchedBimonoidPermOfWord positions width)`

which turns the star hypothesis `evalCell alpha = evalCell beta` (a MATRIX) into `permOfWord w1 = permOfWord w2`
(a `List Nat`), exactly as the Brauer completeness turns diagram-equality into `permuteOfCrossingWord`-equality.
Composed with the (portable, r12-deferred) `combCanonicity`, this is the perm-middle determinism the star's
`retract = retract` step needs.

## The truth-probe (run standalone, `lake env lean`, BEFORE any proof)

The extractor holds on the nose (`rfl`) at every VALID word (positions `<= width - 2`): the width-3 braid pair
`[0,1,0]` / `[1,0,1]`, the width-4 `[2,0,1,2]`, the width-5 unify pair `[1,2,0,1,2]` / `[0,1,2,0,1]` (both realizing
`[2,3,1,0,4]`), and the scrambled width-5 `[2,0,3,1,2,0,3]`.  The `sigmaAt`-as-transposition pins and the matMul
column-swap law (`matMul (permMatrixOf p) (transpositionMatrix k) = permMatrixOf (p.map (swapValue k))`) both check.
An out-of-range word (position `= width - 1`) breaks the extractor — a `sigmaAt` boundary cell is not a clean
transposition — so the read-off is scoped to valid words, machine-confirmed.

## This round (B1) — the carrier + the concrete extractor pins

`bunchedBimonoidApplyAdjacentSwap` / `bunchedBimonoidPermOfWord` / `bunchedBimonoidSwapValue` /
`bunchedBimonoidPermMatrixOf`, and the concrete-width `rfl` pins: `sigmaAt`-as-transposition, the matMul
column-swap law, the extractor at four widths, and the r11-pair reduction (matrix-eq AND permOfWord-eq).  The
GENERIC extractor (the induction) and the generic injectivity are the subsequent bricks; the star does NOT flip.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

/-! The width-4/5 permutation-matrix `rfl` reductions exceed the default heartbeat budget; the raise is a compute
allowance only, the proof terms stay `Eq.refl`, axiom-free (uniform with the r6-r10 lane files). -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # B1 — THE PURE `List Nat` SYMMETRIC-GROUP ENGINE + THE PERMUTATION MATRIX (truth-probed)
    # =========================================================================================
-/

/-- ★ **One adjacent swap at a position** — `applyAdjacentSwap perm position` transposes the entries of `perm` at
`position` and `position + 1` (out-of-range positions leave the list fixed).  The elementary generator `s_k` of the
symmetric group acting on a one-line permutation; reused verbatim from the Brauer canonicity lane. -/
def bunchedBimonoidApplyAdjacentSwap : List Nat → Nat → List Nat
  | [], _ => []
  | first :: [], _ => first :: []
  | first :: second :: rest, 0 => second :: first :: rest
  | first :: second :: rest, position + 1 =>
      first :: bunchedBimonoidApplyAdjacentSwap (second :: rest) position

/-- ★ **The one-line permutation realized by a `sigmaAt`-word** — fold the transposition positions onto the
identity one-line notation `List.range width` (head applied first, matching the `permWord` vcomp order where the
head `sigmaAt` is the earlier / right operand of `matMul`).  `permOfWord positions width` is the through-strand
permutation of `bunchedBimonoidPermWord positions width`. -/
def bunchedBimonoidPermOfWord (positions : List Nat) (width : Nat) : List Nat :=
  positions.foldl bunchedBimonoidApplyAdjacentSwap (List.range width)

/-- The **value-level transposition** `swapValue k` — relabel the two values `k` and `k + 1`, fix everything else.
The VALUE relabeling that a right-multiplication by the transposition matrix `s_k` induces (`matMul M (T_k)` swaps
columns `k, k+1`, i.e. relabels each entry of the one-line notation by `swapValue k`). -/
def bunchedBimonoidSwapValue (k value : Nat) : Nat :=
  if value == k then k + 1 else if value == k + 1 then k else value

/-- ★ **The permutation matrix of a one-line permutation** — entry `(rowIndex, colIndex)` is `1` iff
`perm[rowIndex] = colIndex`, else `0`, over a `width x width` grid.  Built via `List.range` and the propext-clean
`bunchedBimonoidNatListGet` (NOT `List.getD`), so closed instances reduce to ground matrices.  `evalCell` of a
`sigmaAt`-word IS this matrix of its `permOfWord` fold (the extractor). -/
def bunchedBimonoidPermMatrixOf (width : Nat) (perm : List Nat) : BunchedBimonoidMat :=
  { rows := width, cols := width,
    entries := (List.range width).map (fun rowIndex =>
      (List.range width).map (fun colIndex =>
        if bunchedBimonoidNatListGet perm rowIndex == colIndex then 1 else 0)) }

/-! ## B1 truth-probe outputs (the pure engine computes) -/

#eval bunchedBimonoidPermOfWord [0, 1, 0] 3
#eval bunchedBimonoidPermOfWord [1, 0, 1] 3
#eval bunchedBimonoidPermOfWord [1, 2, 0, 1, 2] 5
#eval bunchedBimonoidPermOfWord [0, 1, 2, 0, 1] 5
#eval bunchedBimonoidPermMatrixOf 3 (bunchedBimonoidPermOfWord [0, 1, 0] 3)

/-! ## B1.A — the `sigmaAt`-as-transposition pins (`evalCell (sigmaAt) = permMatrixOf (swap range)`) -/

/-- `evalCell (sigmaAt 3 0)` IS the transposition matrix of `applyAdjacentSwap [0,1,2] 0` — the swap of strands
0,1 read as a permutation matrix (`rfl`). -/
theorem bunchedBimonoidSigmaAtIsTranspositionThreeZero :
    (bunchedBimonoidEvalCell (bunchedBimonoidSigmaAt 3 0) : BunchedBimonoidMat)
      = bunchedBimonoidPermMatrixOf 3 (bunchedBimonoidApplyAdjacentSwap (List.range 3) 0) := rfl

/-- `evalCell (sigmaAt 3 1)` IS the transposition matrix of `applyAdjacentSwap [0,1,2] 1` (swap of strands 1,2). -/
theorem bunchedBimonoidSigmaAtIsTranspositionThreeOne :
    (bunchedBimonoidEvalCell (bunchedBimonoidSigmaAt 3 1) : BunchedBimonoidMat)
      = bunchedBimonoidPermMatrixOf 3 (bunchedBimonoidApplyAdjacentSwap (List.range 3) 1) := rfl

/-- `evalCell (sigmaAt 4 1)` IS the transposition matrix of `applyAdjacentSwap [0,1,2,3] 1` at width 4. -/
theorem bunchedBimonoidSigmaAtIsTranspositionFourOne :
    (bunchedBimonoidEvalCell (bunchedBimonoidSigmaAt 4 1) : BunchedBimonoidMat)
      = bunchedBimonoidPermMatrixOf 4 (bunchedBimonoidApplyAdjacentSwap (List.range 4) 1) := rfl

/-! ## B1.B — the matMul column-swap law pins (`matMul (permMatrixOf p) (T_k) = permMatrixOf (p.map (swapValue k))`)

Right-multiplying a permutation matrix by the transposition matrix `T_k = permMatrixOf (swap range k)` swaps
columns `k, k+1`, i.e. relabels each one-line entry by `swapValue k`.  This is the atomic step of the extractor
induction (the head `sigmaAt` is the `matMul`-earlier operand). -/

/-- The matMul column-swap law at width 3, `p = [0,2,1]`, `k = 0` (`rfl`). -/
theorem bunchedBimonoidMatMulColumnSwapLawThreeZero :
    bunchedBimonoidMatMul (bunchedBimonoidPermMatrixOf 3 [0, 2, 1])
        (bunchedBimonoidPermMatrixOf 3 (bunchedBimonoidApplyAdjacentSwap (List.range 3) 0))
      = bunchedBimonoidPermMatrixOf 3 ([0, 2, 1].map (bunchedBimonoidSwapValue 0)) := rfl

/-- The matMul column-swap law at width 4, `p = [2,0,3,1]`, `k = 2` (`rfl`). -/
theorem bunchedBimonoidMatMulColumnSwapLawFourTwo :
    bunchedBimonoidMatMul (bunchedBimonoidPermMatrixOf 4 [2, 0, 3, 1])
        (bunchedBimonoidPermMatrixOf 4 (bunchedBimonoidApplyAdjacentSwap (List.range 4) 2))
      = bunchedBimonoidPermMatrixOf 4 ([2, 0, 3, 1].map (bunchedBimonoidSwapValue 2)) := rfl

/-! ## B1.C — the EXTRACTOR pins (`evalCell (permWord w width) = permMatrixOf width (permOfWord w width)`) -/

/-- ★★ **THE EXTRACTOR AT THE WIDTH-3 BRAID `[0,1,0]`.**  `evalCell (permWord [0,1,0] 3)` IS the permutation matrix
of `permOfWord [0,1,0] 3` (`rfl`) — the `s_1 s_2 s_1` reversal read off as a permutation. -/
theorem bunchedBimonoidExtractorBraidThree :
    (bunchedBimonoidEvalCell (bunchedBimonoidPermWord [0, 1, 0] 3) : BunchedBimonoidMat)
      = bunchedBimonoidPermMatrixOf 3 (bunchedBimonoidPermOfWord [0, 1, 0] 3) := rfl

/-- ★★ **THE EXTRACTOR AT THE OTHER WIDTH-3 BRAID `[1,0,1]`.**  `evalCell (permWord [1,0,1] 3)` IS the permutation
matrix of `permOfWord [1,0,1] 3` (`rfl`) — the `s_2 s_1 s_2` reversal. -/
theorem bunchedBimonoidExtractorBraidThreeOther :
    (bunchedBimonoidEvalCell (bunchedBimonoidPermWord [1, 0, 1] 3) : BunchedBimonoidMat)
      = bunchedBimonoidPermMatrixOf 3 (bunchedBimonoidPermOfWord [1, 0, 1] 3) := rfl

/-- ★★ **THE EXTRACTOR AT THE WIDTH-4 WORD `[2,0,1,2]`** (`rfl`) — the r9 recomb residual word. -/
theorem bunchedBimonoidExtractorFour :
    (bunchedBimonoidEvalCell (bunchedBimonoidPermWord [2, 0, 1, 2] 4) : BunchedBimonoidMat)
      = bunchedBimonoidPermMatrixOf 4 (bunchedBimonoidPermOfWord [2, 0, 1, 2] 4) := rfl

/-- ★★★ **THE EXTRACTOR AT THE WIDTH-5 UNIFY WORD `[1,2,0,1,2]`** (`rfl`) — the left member of the r11 residual
pair (realizing `[2,3,1,0,4]`), where the width-5 permutation matrix is load-bearing. -/
theorem bunchedBimonoidExtractorFiveUnifyLeft :
    (bunchedBimonoidEvalCell (bunchedBimonoidPermWord [1, 2, 0, 1, 2] 5) : BunchedBimonoidMat)
      = bunchedBimonoidPermMatrixOf 5 (bunchedBimonoidPermOfWord [1, 2, 0, 1, 2] 5) := rfl

/-- ★★★ **THE EXTRACTOR AT THE WIDTH-5 UNIFY WORD `[0,1,2,0,1]`** (`rfl`) — the right member of the r11 pair. -/
theorem bunchedBimonoidExtractorFiveUnifyRight :
    (bunchedBimonoidEvalCell (bunchedBimonoidPermWord [0, 1, 2, 0, 1] 5) : BunchedBimonoidMat)
      = bunchedBimonoidPermMatrixOf 5 (bunchedBimonoidPermOfWord [0, 1, 2, 0, 1] 5) := rfl

/-! ## B1.D — the r11-pair reduction: matrix-eq AND permOfWord-eq (the read-off exercised both ways) -/

/-- ★★★ **THE r11 PAIR SHARES ITS ONE-LINE PERMUTATION.**  `permOfWord [1,2,0,1,2] 5 = permOfWord [0,1,2,0,1] 5`
(`rfl`) — the pure `List Nat` read-off that `combCanonicity` then feeds to unify the recursive-comb staircases. -/
theorem bunchedBimonoidR11PairPermShared :
    bunchedBimonoidPermOfWord [1, 2, 0, 1, 2] 5 = bunchedBimonoidPermOfWord [0, 1, 2, 0, 1] 5 := rfl

/-- ★★★ **THE r11 PAIR SHARES ITS MATRIX — DERIVED THROUGH THE READ-OFF.**
`evalCell (permWord [1,2,0,1,2] 5) = evalCell (permWord [0,1,2,0,1] 5)`, obtained NOT by a direct (double-heavy)
`rfl` but by composing the two extractor pins with the one-line read-off: each side is the permutation matrix of
its `permOfWord`, and the two `permOfWord`s agree (`...R11PairPermShared`).  This is exactly the read-off
direction the star needs — matrix-equality of two `sigmaAt`-words follows from the equality of their one-line
permutations. -/
theorem bunchedBimonoidR11PairMatrixShared :
    (bunchedBimonoidEvalCell (bunchedBimonoidPermWord [1, 2, 0, 1, 2] 5) : BunchedBimonoidMat)
      = bunchedBimonoidEvalCell (bunchedBimonoidPermWord [0, 1, 2, 0, 1] 5) :=
  bunchedBimonoidExtractorFiveUnifyLeft.trans
    ((congrArg (bunchedBimonoidPermMatrixOf 5) bunchedBimonoidR11PairPermShared).trans
      bunchedBimonoidExtractorFiveUnifyRight.symm)

/-- Separation / non-vacuity — an UNEQUAL-permutation pair is genuinely separated: `permOfWord [0,1] 3` and
`permOfWord [1,0] 3` differ (`[1,2,0]` vs `[2,0,1]`), so the read-off is not vacuous. -/
theorem bunchedBimonoidPermOfWordSeparatesOrder :
    bunchedBimonoidPermOfWord [0, 1] 3 ≠ bunchedBimonoidPermOfWord [1, 0] 3 := by decide

/-! ## The B1 honesty marker -/

/-- ★★★ **ESTABLISHED (B1) — the permutation-matrix carrier + the concrete extractor pins are SHIPPED and
truth-probed.**  `= true` records the pure `List Nat` symmetric-group engine
(`bunchedBimonoidApplyAdjacentSwap`, `bunchedBimonoidPermOfWord`, `bunchedBimonoidSwapValue`) and the permutation
matrix (`bunchedBimonoidPermMatrixOf`, built with the propext-clean `bunchedBimonoidNatListGet`), together with the
concrete-width `rfl` pins: `sigmaAt`-as-transposition (widths 3, 4), the matMul column-swap law
(`matMul (permMatrixOf p) (T_k) = permMatrixOf (p.map (swapValue k))`, widths 3, 4), the EXTRACTOR
(`evalCell (permWord w width) = permMatrixOf width (permOfWord w width)`) at the width-3 braid pair, a width-4
word, and the width-5 unify pair, and the r11-pair reduction exercised BOTH ways
(`...R11PairMatrixShared`, `...R11PairPermShared`), with an unequal-perm separation for non-vacuity.  This is the
Omega mirror of the Brauer `permutationDiagram`-read-off; the GENERIC extractor + injectivity are the subsequent
bricks.  Zero-axiom (per-decl `#assert_no_axioms` + independent `#print axioms` in the twin). -/
def fxBunchedBimonoid_permMatrixExtractorCarrierAndPinsShipped : Bool := true

end FX1Poly.Polygraph.Omega
