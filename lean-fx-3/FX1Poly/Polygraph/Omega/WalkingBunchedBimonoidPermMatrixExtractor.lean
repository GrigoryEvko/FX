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

/-! # =========================================================================================
    # B2 — THE INJECTIVE READ-OFF: `permMatrixOf width p = permMatrixOf width q -> p = q`
    # =========================================================================================

★ **The GENERIC injectivity — the Omega mirror of the Brauer `permutationDiagram_injective`.**  The concrete
extractor pins (B1) reduce the star hypothesis `evalCell alpha = evalCell beta` to a `permMatrixOf`-equality; this
brick proves that equality forces the underlying one-line permutations equal, by reading each row's unique `1` off
the matrix with the propext-clean `bunchedBimonoidMatEntryAt` (the r10 lesson: NOT `List.getD`).  Together with the
extractor pins, at any pinned width this gives `evalCell (permWord w1) = evalCell (permWord w2) -> permOfWord w1 =
permOfWord w2` — the pure `List Nat` fact `combCanonicity` (portable, r12) then turns into `recComb`-equality.

The clean generic list-algebra (`map` commuting through `applyAdjacentSwap` and through the fold) is shipped here
too: it is the load-bearing congruence of the FUTURE generic extractor induction (the head `sigmaAt` relabels the
one-line entries by `swapValue`), independent of the deferred matrix-arithmetic core. -/

/-! ## B2.A — the propext-clean `Nat`-`beq` bridges -/

/-- `(n == n) = true` for `Nat` — `decide_eq_true rfl`, propext-clean (Init's `beq_self` route leaks). -/
theorem bunchedBimonoidNatBeqSelf (n : Nat) : (n == n) = true := decide_eq_true rfl

/-- `a = b` from `(a == b) = true` for `Nat` — `of_decide_eq_true`, propext-clean (axiom-free, probed). -/
theorem bunchedBimonoidNatEqOfBeqTrue (a b : Nat) (hbeq : (a == b) = true) : a = b :=
  of_decide_eq_true hbeq

/-! ## B2.B — list extensionality by `natListGet` + the append / range indexers (all propext-clean) -/

/-- Two `List Nat` of equal length are equal if `bunchedBimonoidNatListGet` agrees at every in-range index —
structural on both lists, propext-clean (avoids `List.ext_get`). -/
theorem bunchedBimonoidListExtByGet : (left right : List Nat) → left.length = right.length →
    (∀ index, index < left.length →
      bunchedBimonoidNatListGet left index = bunchedBimonoidNatListGet right index) → left = right
  | [], [], _, _ => rfl
  | [], _ :: _, hLen, _ => Nat.noConfusion hLen
  | _ :: _, [], hLen, _ => Nat.noConfusion hLen
  | leftHead :: leftTail, rightHead :: rightTail, hLen, hGet => by
      have hHead : leftHead = rightHead := hGet 0 (Nat.succ_pos _)
      have hTailLen : leftTail.length = rightTail.length := Nat.succ.inj hLen
      have hTail : leftTail = rightTail :=
        bunchedBimonoidListExtByGet leftTail rightTail hTailLen
          (fun index hIndex => hGet (index + 1) (Nat.succ_lt_succ hIndex))
      exact hHead ▸ hTail ▸ rfl

/-- `natListGet (front ++ back) index = natListGet front index` when `index < front.length` — structural on
`front`, `index`. -/
theorem bunchedBimonoidGetAppendLeft : (front back : List Nat) → (index : Nat) →
    index < front.length →
    bunchedBimonoidNatListGet (front ++ back) index = bunchedBimonoidNatListGet front index
  | [], _, index, hIndex => absurd hIndex (Nat.not_lt_zero index)
  | _ :: _, _, 0, _ => rfl
  | _ :: frontTail, back, index + 1, hIndex =>
      bunchedBimonoidGetAppendLeft frontTail back index (Nat.lt_of_succ_lt_succ hIndex)

/-- `natListGet (front ++ [value]) front.length = value` — the appended element sits at the front's length. -/
theorem bunchedBimonoidGetAppendSnoc : (front : List Nat) → (value : Nat) →
    bunchedBimonoidNatListGet (front ++ [value]) front.length = value
  | [], _ => rfl
  | _ :: frontTail, value => bunchedBimonoidGetAppendSnoc frontTail value

/-- `(front ++ mid) ++ back = front ++ (mid ++ back)` — cons-only structural copy (Init's `List.append_assoc`
leaks propext). -/
theorem bunchedBimonoidAppendSnocCons {alpha : Type _} :
    (front rest : List alpha) → (value : alpha) → front ++ (value :: rest) = (front ++ [value]) ++ rest
  | [], _, _ => rfl
  | head :: tail, rest, value => congrArg (head :: ·) (bunchedBimonoidAppendSnocCons tail rest value)

/-- `List.range.loop count acc = List.range.loop count [] ++ acc` — the accumulator factors out (propext-clean). -/
theorem bunchedBimonoidRangeLoopAppend : (count : Nat) → (accumulated : List Nat) →
    List.range.loop count accumulated = List.range.loop count [] ++ accumulated
  | 0, _ => rfl
  | count + 1, accumulated => by
      show List.range.loop count (count :: accumulated)
         = List.range.loop count (count :: []) ++ accumulated
      rw [bunchedBimonoidRangeLoopAppend count (count :: accumulated),
          bunchedBimonoidRangeLoopAppend count (count :: [])]
      exact bunchedBimonoidAppendSnocCons (List.range.loop count []) accumulated count

/-- `List.range (n + 1) = List.range n ++ [n]` — propext-clean replacement for Init's `List.range_succ`. -/
theorem bunchedBimonoidRangeSucc (n : Nat) : List.range (n + 1) = List.range n ++ [n] :=
  bunchedBimonoidRangeLoopAppend n (n :: [])

/-- `(List.range.loop count acc).length = count + acc.length` — propext-clean. -/
theorem bunchedBimonoidRangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      show (List.range.loop count (count :: accumulated)).length = (count + 1) + accumulated.length
      rw [bunchedBimonoidRangeLoopLength count (count :: accumulated)]
      show count + (accumulated.length + 1) = (count + 1) + accumulated.length
      rw [Nat.add_succ, Nat.succ_add]

/-- `(List.range n).length = n`. -/
theorem bunchedBimonoidRangeLength (n : Nat) : (List.range n).length = n :=
  bunchedBimonoidRangeLoopLength n []

/-- `natListGet (List.range width) index = index` when `index < width` — structural on `width` via `rangeSucc`. -/
theorem bunchedBimonoidGetRange : (width index : Nat) → index < width →
    bunchedBimonoidNatListGet (List.range width) index = index
  | 0, index, hIndex => absurd hIndex (Nat.not_lt_zero index)
  | width + 1, index, hIndex => by
      rw [bunchedBimonoidRangeSucc width]
      rcases Nat.lt_or_ge index width with hLt | hGe
      · rw [bunchedBimonoidGetAppendLeft (List.range width) [width] index
              (by rw [bunchedBimonoidRangeLength width]; exact hLt)]
        exact bunchedBimonoidGetRange width index hLt
      · have hEq : index = width := Nat.le_antisymm (Nat.le_of_lt_succ hIndex) hGe
        subst hEq
        have snoc := bunchedBimonoidGetAppendSnoc (List.range index) index
        rw [bunchedBimonoidRangeLength index] at snoc
        exact snoc

/-! ## B2.C — `natListGet` / `rowListGet` commute with `List.map` (in range) -/

/-- `natListGet (List.map f L) index = f (natListGet L index)` when `index < L.length` — structural. -/
theorem bunchedBimonoidGetMapNat (f : Nat → Nat) : (list : List Nat) → (index : Nat) →
    index < list.length →
    bunchedBimonoidNatListGet (list.map f) index = f (bunchedBimonoidNatListGet list index)
  | [], index, hIndex => absurd hIndex (Nat.not_lt_zero index)
  | _ :: _, 0, _ => rfl
  | _ :: listTail, index + 1, hIndex =>
      bunchedBimonoidGetMapNat f listTail index (Nat.lt_of_succ_lt_succ hIndex)

/-- `rowListGet (List.map f L) index = f (natListGet L index)` when `index < L.length` — the row-level analogue. -/
theorem bunchedBimonoidGetMapRow (f : Nat → List Nat) : (list : List Nat) → (index : Nat) →
    index < list.length →
    bunchedBimonoidRowListGet (list.map f) index = f (bunchedBimonoidNatListGet list index)
  | [], index, hIndex => absurd hIndex (Nat.not_lt_zero index)
  | _ :: _, 0, _ => rfl
  | _ :: listTail, index + 1, hIndex =>
      bunchedBimonoidGetMapRow f listTail index (Nat.lt_of_succ_lt_succ hIndex)

/-! ## B2.D — the permutation-matrix entry formula + the injective read-off -/

/-- ★ **The permutation-matrix entry formula.**  For `rowIndex, colIndex < width`,
`matEntryAt (permMatrixOf width perm) rowIndex colIndex` is `1` iff `perm[rowIndex] = colIndex`, else `0` —
the two `List.range` maps read off by `getMapRow` / `getMapNat` / `getRange`. -/
theorem bunchedBimonoidPermMatrixEntryAt (width : Nat) (perm : List Nat) (rowIndex colIndex : Nat)
    (hRow : rowIndex < width) (hCol : colIndex < width) :
    bunchedBimonoidMatEntryAt (bunchedBimonoidPermMatrixOf width perm) rowIndex colIndex
      = (if bunchedBimonoidNatListGet perm rowIndex == colIndex then 1 else 0) := by
  have rowEq : bunchedBimonoidRowListGet (bunchedBimonoidPermMatrixOf width perm).entries rowIndex
      = (List.range width).map
          (fun col => if bunchedBimonoidNatListGet perm rowIndex == col then 1 else 0) := by
    show bunchedBimonoidRowListGet
          ((List.range width).map (fun row =>
            (List.range width).map (fun col => if bunchedBimonoidNatListGet perm row == col then 1 else 0)))
          rowIndex
        = (List.range width).map (fun col => if bunchedBimonoidNatListGet perm rowIndex == col then 1 else 0)
    rw [bunchedBimonoidGetMapRow _ (List.range width) rowIndex
          (by rw [bunchedBimonoidRangeLength width]; exact hRow),
        bunchedBimonoidGetRange width rowIndex hRow]
  show bunchedBimonoidNatListGet
        (bunchedBimonoidRowListGet (bunchedBimonoidPermMatrixOf width perm).entries rowIndex) colIndex
      = (if bunchedBimonoidNatListGet perm rowIndex == colIndex then 1 else 0)
  rw [rowEq,
      bunchedBimonoidGetMapNat _ (List.range width) colIndex
        (by rw [bunchedBimonoidRangeLength width]; exact hCol),
      bunchedBimonoidGetRange width colIndex hCol]

/-- ★★ **THE INJECTIVE READ-OFF (generic).**  Two length-`width` one-line permutations whose entries are all
`< width` and whose permutation matrices agree are EQUAL: each row's unique `1` sits at column `perm[rowIndex]`, so
matrix-equality forces `perm[rowIndex] = perm'[rowIndex]` at every row, and `listExtByGet` concludes.  The Omega
mirror of the Brauer `permutationDiagram_injective`. -/
theorem bunchedBimonoidPermMatrixInjective (width : Nat) (perm otherPerm : List Nat)
    (hLenLeft : perm.length = width) (hLenRight : otherPerm.length = width)
    (hBoundLeft : ∀ index, index < width → bunchedBimonoidNatListGet perm index < width)
    (matrixEq : bunchedBimonoidPermMatrixOf width perm = bunchedBimonoidPermMatrixOf width otherPerm) :
    perm = otherPerm := by
  apply bunchedBimonoidListExtByGet perm otherPerm (hLenLeft.trans hLenRight.symm)
  intro rowIndex hRowLt
  have hRow : rowIndex < width := hLenLeft ▸ hRowLt
  have permEntryBound : bunchedBimonoidNatListGet perm rowIndex < width := hBoundLeft rowIndex hRow
  have entryLeft : bunchedBimonoidMatEntryAt (bunchedBimonoidPermMatrixOf width perm) rowIndex
      (bunchedBimonoidNatListGet perm rowIndex) = 1 := by
    rw [bunchedBimonoidPermMatrixEntryAt width perm rowIndex (bunchedBimonoidNatListGet perm rowIndex)
        hRow permEntryBound]
    exact if_pos (bunchedBimonoidNatBeqSelf (bunchedBimonoidNatListGet perm rowIndex))
  have entryRight : bunchedBimonoidMatEntryAt (bunchedBimonoidPermMatrixOf width otherPerm) rowIndex
      (bunchedBimonoidNatListGet perm rowIndex)
      = (if bunchedBimonoidNatListGet otherPerm rowIndex == bunchedBimonoidNatListGet perm rowIndex
          then 1 else 0) :=
    bunchedBimonoidPermMatrixEntryAt width otherPerm rowIndex (bunchedBimonoidNatListGet perm rowIndex)
      hRow permEntryBound
  have bridged : (if bunchedBimonoidNatListGet otherPerm rowIndex == bunchedBimonoidNatListGet perm rowIndex
      then 1 else 0) = 1 := by
    rw [← entryRight, ← matrixEq]; exact entryLeft
  have beqTrue : (bunchedBimonoidNatListGet otherPerm rowIndex == bunchedBimonoidNatListGet perm rowIndex)
      = true := by
    cases hbeq : bunchedBimonoidNatListGet otherPerm rowIndex == bunchedBimonoidNatListGet perm rowIndex with
    | true => rfl
    | false => rw [hbeq] at bridged; exact Nat.noConfusion bridged
  exact (bunchedBimonoidNatEqOfBeqTrue _ _ beqTrue).symm

/-! ## B2.E — the clean generic list-algebra (the future extractor's congruence) -/

/-- ★ **`List.map` commutes through one adjacent swap** — `map f (applyAdjacentSwap L k) = applyAdjacentSwap
(map f L) k` (values relabel; the swap only moves positions).  Structural on `(L, k)`. -/
theorem bunchedBimonoidMapApplyAdjacentSwapCommute (f : Nat → Nat) :
    (list : List Nat) → (position : Nat) →
    List.map f (bunchedBimonoidApplyAdjacentSwap list position)
      = bunchedBimonoidApplyAdjacentSwap (List.map f list) position
  | [], _ => rfl
  | _ :: [], _ => rfl
  | _ :: _ :: _, 0 => rfl
  | first :: second :: rest, position + 1 =>
      congrArg (f first :: ·)
        (bunchedBimonoidMapApplyAdjacentSwapCommute f (second :: rest) position)

/-- ★ **`List.map` commutes through the whole swap fold** — `foldl applyAdjacentSwap (map f L) positions = map f
(foldl applyAdjacentSwap L positions)`.  Structural on `positions`, one step by the single-swap commute. -/
theorem bunchedBimonoidFoldlApplyAdjacentSwapMapCommute (f : Nat → Nat) :
    (positions : List Nat) → (list : List Nat) →
    List.foldl bunchedBimonoidApplyAdjacentSwap (List.map f list) positions
      = List.map f (List.foldl bunchedBimonoidApplyAdjacentSwap list positions)
  | [], _ => rfl
  | position :: rest, list => by
      show List.foldl bunchedBimonoidApplyAdjacentSwap
            (bunchedBimonoidApplyAdjacentSwap (List.map f list) position) rest
          = List.map f (List.foldl bunchedBimonoidApplyAdjacentSwap
              (bunchedBimonoidApplyAdjacentSwap list position) rest)
      rw [← bunchedBimonoidMapApplyAdjacentSwapCommute f list position]
      exact bunchedBimonoidFoldlApplyAdjacentSwapMapCommute f rest
        (bunchedBimonoidApplyAdjacentSwap list position)

/-! ## The B2 honesty marker -/

/-- ★★ **ESTABLISHED (B2) — the injective read-off is GENERIC + zero-axiom.**  `= true` records
`bunchedBimonoidPermMatrixInjective`: two length-`width` one-line permutations with entries `< width` and equal
permutation matrices are equal (each row's unique `1` read off the propext-clean `bunchedBimonoidMatEntryAt`,
`listExtByGet` concluding) — the Omega mirror of the Brauer `permutationDiagram_injective`, and the injectivity
half of the read-off `evalCell (permWord w1) = evalCell (permWord w2) -> permOfWord w1 = permOfWord w2` (the
extractor half is pinned concretely in B1; the GENERIC extractor is r12).  Also ships the clean generic
list-algebra (`bunchedBimonoidMapApplyAdjacentSwapCommute`, `bunchedBimonoidFoldlApplyAdjacentSwapMapCommute` —
`map` commuting through the swap fold), the congruence the future generic extractor rests on.  Zero-axiom
(per-decl `#assert_no_axioms` + independent `#print axioms` in the twin). -/
def fxBunchedBimonoid_permMatrixInjectiveReadOffShipped : Bool := true

/-! # =========================================================================================
    # THE r11 ROUND LEDGER + the precisely-named residuals (no star flip)
    # =========================================================================================
-/

/-- ★ **THE GENERIC EXTRACTOR STAYS WALLED (r12) — on the matrix-algebra kit, precisely named, no flip.**  `=
false` records the exact remaining node.  The GENERIC extractor
`evalCell (permWord w width) = permMatrixOf width (permOfWord w width)` (currently pinned at widths 3, 4, 5) is
gated on exactly three lemmas at generic width, all clean of the CONV layer: (a) `sigmaAt`-as-transposition —
`evalCell (sigmaAt width k) = permMatrixOf width (applyAdjacentSwap (List.range width) k)` (the block-diagonal
`directSum` of the swap generator equals the transposition matrix); (b) the matMul column-swap law —
`matMul (permMatrixOf width p) (permMatrixOf width (applyAdjacentSwap (List.range width) k))
= permMatrixOf width (p.map (swapValue k))` (a finite-sum-over-`List.range` "indicator picks one term" argument,
the honest `Mat(N)` matrix-algebra kit the r2 `fxBunchedBimonoid_matrixStrictLawExtensionReached = false` wall
already names); and (c) the pure `List Nat` relabel `permOfWord (k :: rest) width = (permOfWord rest width).map
(swapValue k)` (from `bunchedBimonoidFoldlApplyAdjacentSwapMapCommute` (B2) plus the range-relabel
`(List.range width).map (swapValue k) = applyAdjacentSwap (List.range width) k` for `k + 1 < width`).  With (a),
(b), (c) the extractor induction closes; combined with the B2 injective read-off it gives the GENERIC
`evalCell (permWord w1) = evalCell (permWord w2) -> permOfWord w1 = permOfWord w2` on valid words.  NOT shipped
here — the concrete pins stand in for it this round. -/
def fxBunchedBimonoid_genericPermMatrixExtractorGatedOnMatrixAlgebraKit : Bool := false

/-- ★★★ **ESTABLISHED — the WP-PROP r11 permutation-matrix read-off ledger (the honest scoreboard).**  `= true`
records the complete r11 delivery.  B1: the pure `List Nat` symmetric-group engine + `permMatrixOf` + the
concrete extractor pins (`evalCell (permWord w width) = permMatrixOf width (permOfWord w width)`, widths 3/4/5) +
the `sigmaAt`-as-transposition and matMul column-swap pins + the r11-pair reduction derived THROUGH the read-off
(`fxBunchedBimonoid_permMatrixExtractorCarrierAndPinsShipped`).  B2: the GENERIC injective read-off
`permMatrixOf width p = permMatrixOf width q -> p = q` (the Omega mirror of the Brauer
`permutationDiagram_injective`) + the clean generic list-algebra (`map` commuting through the swap fold)
(`fxBunchedBimonoid_permMatrixInjectiveReadOffShipped`).  Together this turns the star hypothesis
`evalCell alpha = evalCell beta` (a MATRIX) into `permOfWord`-equality (a `List Nat`) — the perm-middle
determinism the star's `retract = retract` step needs — at every pinned width, with the injectivity half generic.

The residuals are precisely named and DEFERRED: the GENERIC extractor on the matrix-algebra kit
(`fxBunchedBimonoid_genericPermMatrixExtractorGatedOnMatrixAlgebraKit`); the portable `combCanonicity`
re-derivation (pure `List Nat`, `WiringDescStaircaseCanonical`) turning `permOfWord`-equality into `recComb`-
equality; and the `recCombConv`-mirror CONV fold (the `sigmaAt`-generic braid / distant / involution moves,
`fxBunchedBimonoid_coxeterWordUniqueGatedOnGenericBraid`, r8, byte-intact).  The star does NOT flip: no literal
hypothesis-free inhabitant of `bunchedBimonoidStarStatementAdditiveWellTyped` is produced, and every upstream
star marker (`fxBunchedBimonoid_correctedWellTypedStarStillOpen*`,
`fxBunchedBimonoid_collisionGeneralStepStillGatedOnBracketMatch`,
`fxBunchedBimonoid_coxeterWordUniqueGatedOnGenericBraid`) keeps its name and `= false` value byte-intact
(cross-file, not edited).  Zero-axiom (per-decl `#assert_no_axioms` + independent `#print axioms` in the twin);
STRUCTURAL only.  NO fabricated star flip. -/
def fxBunchedBimonoid_permMatrixReadOffRoundElevenLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
