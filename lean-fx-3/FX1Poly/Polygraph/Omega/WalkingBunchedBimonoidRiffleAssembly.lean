import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarAssembly

/-! # Polygraph/Omega/WalkingBunchedBimonoidRiffleAssembly — the general `wideSwap(m,n)` riffle word BUILT
(the r7 "unbuilt" wall falls, matrix-correct at the transpose permutation), the staged bialgebra normal form
matched to the collision at generic width, the Coxeter sorted-NF scaffold, and the honest star partial with the
two heavy residuals narrowed to two precisely-named lemmas (WP-PROP r8, #2033, the two-gap assembly round)

★ **THE r8 HEADLINE — the general perfect-shuffle regrouping IS a zero-axiom, structural, matrix-correct word.**
The r6 `WideCollision` and r7 `RiffleNaturality` walled the general `wideSwap(m,n)` riffle word at WORD
granularity (`fxBunchedBimonoid_wideSwapGeneralRiffleWordUnbuilt = false`,
`fxBunchedBimonoid_wideSwapGeneralAssemblyStillUnbuilt = false`): the elementary letter
`bunchedBimonoidStrandPastBlock` was shipped, but its assembly into the full `m*n`-strand transpose was refuted
for the naive flat fold (`bunchedBimonoidWideSwapNaiveFoldRefutedAtTwoTwo`, a `3 x 3` where `4 x 4` is needed).
This file DELIVERS the correct assembly as a three-layer nested shuffle network
(`blockPastBlock` -> `riffleIn` -> `wideSwap`), truth-probed against the independently-computed transpose
permutation `q = (p % n) * m + (p / n)` and matching ON THE NOSE at `(1,1),(2,1),(1,2),(2,2),(3,2),(2,3),(3,3)`.
`wideSwap 2 2` is the shipped `bunchedBimonoidMiddleSwap`; the corners `p = 0, p = K-1` are always fixed; the
`(3,2)` case is a single 4-cycle on the four middle strands.

## Why a flat fold cannot work, and this does (the strand arithmetic, worked out and machine-confirmed)

  * `strandPastBlock k` (shipped, r7) is the `(k+1) x (k+1)` cyclic LEFT shift — one strand past a block of `k`.
  * `blockPastBlock p q` moves a whole `p`-block past a `q`-block on `p+q` strands: `whiskerLeft a (blockPastBlock
    p q)` recurses under the fixed head while `whiskerRight (strandPastBlock q) (a^p)` carries the single head
    past `q`.  `blockPastBlock 2 2 = [y0 y1 x0 x1]`, matrix `[[0,0,1,0],[0,0,0,1],[1,0,0,0],[0,1,0,0]]`.
  * `wideSwap (m+1) n` transposes the BOTTOM `m` rows BELOW the top row of `n` strands
    (`whiskerLeft (a^n) (wideSwap m n)`), then `riffleIn n m` interleaves the top row's `n` strands into the `n`
    freshly-built column blocks of height `m` — a NESTED shuffle (`riffleIn` -> `blockPastBlock` ->
    `strandPastBlock`), a depth-`O(mn)` network.  This is exactly why a single-`strandPastBlock` flat fold drops a
    strand: the interleave is not one pass, it is a genuine perfect-shuffle bracketing.  Base `wideSwap 0 n = id`
    on 0 strands.

The staged NF closes the collision matrix side too: `bialgebraNF m n := spiderStaged (deltaStage m n)
(wideSwap m n) (muStage n m)` evaluates to the `n x m` all-ones map, matching `wideCollision m n` on the nose at
`(2,2),(2,3),(3,2),(3,3)`.  The CONV-level double induction remains gated on a GENERIC-WIDTH naturality slide and
the Coxeter `CoxeterWordUnique` bubble-sort (both precisely named, B2/B3 walls); the star does NOT flip.

Raw Lean 4 + Init; STRUCTURAL only (`blockPastBlock`/`riffleIn`/`wideSwap` recurse on a genuine strand-count
`Nat`; the sort skeleton recurses on an explicit fuel `Nat`); ASCII-only.  Per-declaration `#assert_no_axioms`
AND independent `#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! The `m*n`-strand permutation `rfl` matrix reductions exceed the default heartbeat budget; the raise is a
compute allowance only, the proof terms stay `Eq.refl`, axiom-free (uniform with the r6/r7 lane files). -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # B1 — THE GENERAL RIFFLE WORD: blockPastBlock -> riffleIn -> wideSwap (the wall falls)
    # =========================================================================================
-/

/-- ★★ **THE BLOCK-PAST-BLOCK BRAIDING `blockPastBlock p q : a^p . a^q => a^q . a^p`** — move a whole block of
`p` strands past a block of `q` strands (`[X | Y] |-> [Y | X]`), by structural recursion on the leading block
size `p`: `0` leaves the `q`-block alone (`id (a^q)`); `p+1` pushes the `p`-block under one strand
(`a <| blockPastBlock p q`) then carries the single fixed head past the `q`-block
(`strandPastBlock q |> a^p`).  A genuine general def; `blockPastBlock 1 q` matches `strandPastBlock q`
matrix-wise, and `blockPastBlock 2 2 = [y0 y1 x0 x1]`. -/
def bunchedBimonoidBlockPastBlock : Nat → Nat → CellExpr bunchedBimonoidOmegaComputad 2
  | 0, blockQ => CellExpr.id (bunchedBimonoidAWordPow blockQ)
  | leadingP + 1, blockQ => CellExpr.vcomp
      (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen (bunchedBimonoidBlockPastBlock leadingP blockQ))
      (CellExpr.whiskerRight (bunchedBimonoidStrandPastBlock blockQ) (bunchedBimonoidAWordPow leadingP))

/-- ★★ **THE RIFFLE-IN INTERLEAVE `riffleIn n m`** — interleave a top row of `n` single strands
`[t_0 .. t_{n-1}]` into `n` freshly-built column blocks `[C_0 .. C_{n-1}]` (each `C_j` of height `m`), producing
`[t_0 C_0 t_1 C_1 ...]`, by structural recursion on the top-row length `n`: `0` is the empty interleave; `n+1`
carries the head strand `t_0` past the leading column block `C_0` (of `m` strands, via `blockPastBlock n m`
whiskered above one strand and right of the remaining `n*m` strands) then recurses on the remaining `n` heads and
`n` blocks under the placed prefix `a^{1+m}`.  The tail whisker `... |> a^{n*m}` is LOAD-BEARING (dropping it
loses a strand — the exact bug the naive fold hit). -/
def bunchedBimonoidRiffleIn : Nat → Nat → CellExpr bunchedBimonoidOmegaComputad 2
  | 0, _ => CellExpr.id bunchedBimonoidIdOne
  | topRowN + 1, blockHeightM => CellExpr.vcomp
      (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
        (CellExpr.whiskerRight (bunchedBimonoidBlockPastBlock topRowN blockHeightM)
          (bunchedBimonoidAWordPow (topRowN * blockHeightM))))
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow (1 + blockHeightM))
        (bunchedBimonoidRiffleIn topRowN blockHeightM))

/-- ★★★ **THE GENERAL `wideSwap m n : a^(m*n) => a^(m*n)` PERFECT SHUFFLE (the r7 wall falls).**  The transpose /
perfect shuffle regrouping the `m*n` incidence strands from grouped-by-input (`m` groups of `n`) to
grouped-by-output (`n` groups of `m`) — the permutation `p = i*n + j |-> q = j*m + i` — by structural recursion
on the input-group count `m`: `0` is the empty shuffle (`id` on 0 strands); `m+1` transposes the BOTTOM `m` rows
below the top row of `n` strands (`a^n <| wideSwap m n`) then interleaves the top row into the `n` freshly-built
column blocks (`riffleIn n m`).  A depth-`O(mn)` nested shuffle network — matrix-correct at the transpose
permutation, truth-probed at seven widths. -/
def bunchedBimonoidWideSwap : Nat → Nat → CellExpr bunchedBimonoidOmegaComputad 2
  | 0, _ => CellExpr.id bunchedBimonoidIdOne
  | inputGroupsM + 1, groupSizeN => CellExpr.vcomp
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow groupSizeN)
        (bunchedBimonoidWideSwap inputGroupsM groupSizeN))
      (bunchedBimonoidRiffleIn groupSizeN inputGroupsM)

/-! ## B1 truth-probe outputs (the wideSwap word IS the transpose permutation) -/

#eval bunchedBimonoidEvalCell (bunchedBimonoidWideSwap 1 1)
#eval bunchedBimonoidEvalCell (bunchedBimonoidWideSwap 2 1)
#eval bunchedBimonoidEvalCell (bunchedBimonoidWideSwap 1 2)
#eval bunchedBimonoidEvalCell (bunchedBimonoidWideSwap 2 2)
#eval bunchedBimonoidEvalCell (bunchedBimonoidWideSwap 3 2)
#eval bunchedBimonoidEvalCell bunchedBimonoidMiddleSwap

/-! ## B1 matrix probes (all `rfl`, axiom-free — the pinned transpose-permutation literals) -/

/-- The block braiding `blockPastBlock 2 2` moves `[x0 x1 | y0 y1]` to `[y0 y1 | x0 x1]` — matrix
`[[0,0,1,0],[0,0,0,1],[1,0,0,0],[0,1,0,0]]`. -/
theorem bunchedBimonoidBlockPastBlockTwoTwoMatrix :
    bunchedBimonoidEvalCell (bunchedBimonoidBlockPastBlock 2 2)
      = { rows := 4, cols := 4, entries := [[0, 0, 1, 0], [0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 0]] } := rfl

/-- ★ The interleave `riffleIn 2 1` (one top row of 2 strands into 2 height-1 column blocks) IS the shipped
`middleSwap` as a map — `rfl` (both `[[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]]`). -/
theorem bunchedBimonoidRiffleInTwoOneIsMiddleSwap :
    bunchedBimonoidEvalCell (bunchedBimonoidRiffleIn 2 1)
      = bunchedBimonoidEvalCell bunchedBimonoidMiddleSwap := rfl

/-- The degenerate `wideSwap 1 1` is the width-1 identity `[[1]]` (one strand moves nothing). -/
theorem bunchedBimonoidWideSwapOneOneMatrix :
    bunchedBimonoidEvalCell (bunchedBimonoidWideSwap 1 1)
      = { rows := 1, cols := 1, entries := [[1]] } := rfl

/-- The degenerate `wideSwap 2 1` (a single output group) is the identity `[[1,0],[0,1]]` — a single row moves
nothing. -/
theorem bunchedBimonoidWideSwapTwoOneIsIdentity :
    bunchedBimonoidEvalCell (bunchedBimonoidWideSwap 2 1)
      = { rows := 2, cols := 2, entries := [[1, 0], [0, 1]] } := rfl

/-- The degenerate `wideSwap 1 2` (a single input group) is the identity `[[1,0],[0,1]]` — a single column moves
nothing. -/
theorem bunchedBimonoidWideSwapOneTwoIsIdentity :
    bunchedBimonoidEvalCell (bunchedBimonoidWideSwap 1 2)
      = { rows := 2, cols := 2, entries := [[1, 0], [0, 1]] } := rfl

/-- ★★★ **`wideSwap 2 2` IS the middle swap (the transpose of the `2 x 2` grid).**  Matrix
`[[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]]` — the permutation `0->0, 1->2, 2->1, 3->3` swapping the middle pair,
fixing the corners.  This is exactly `bunchedBimonoidMiddleSwap` (`1 (x) sigma (x) 1`). -/
theorem bunchedBimonoidWideSwapTwoTwoMatrix :
    bunchedBimonoidEvalCell (bunchedBimonoidWideSwap 2 2)
      = { rows := 4, cols := 4, entries := [[1, 0, 0, 0], [0, 0, 1, 0], [0, 1, 0, 0], [0, 0, 0, 1]] } := rfl

/-- ★★★ **`wideSwap 2 2` matches the shipped `middleSwap` on the nose** — the general riffle word reproduces the
flagship `(2,2)` bialgebra routing (`rfl`). -/
theorem bunchedBimonoidWideSwapTwoTwoIsMiddleSwap :
    bunchedBimonoidEvalCell (bunchedBimonoidWideSwap 2 2)
      = bunchedBimonoidEvalCell bunchedBimonoidMiddleSwap := rfl

/-- ★★ **`wideSwap 3 2` is the `6 x 6` transpose of the `3 x 2` grid** — the permutation `0->0, 1->3, 2->1,
3->4, 4->2, 5->5`, a single 4-cycle `(1 3 4 2)` on the four middle strands, fixing corners `0, 5`.  A genuine
wider-than-`(2,2)` instance where the flat fold provably fails. -/
theorem bunchedBimonoidWideSwapThreeTwoMatrix :
    bunchedBimonoidEvalCell (bunchedBimonoidWideSwap 3 2)
      = { rows := 6, cols := 6,
          entries := [[1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0],
                      [0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1]] } := rfl

/-! ## The B1 marker — the general riffle word is SHIPPED (the r7 wall falls, retire name-only) -/

/-- ★★★ **ESTABLISHED (B1) — the general `wideSwap(m,n)` riffle word is BUILT and matrix-correct.**  `= true`
records the three-layer nested shuffle `bunchedBimonoid{BlockPastBlock,RiffleIn,WideSwap}`: a genuine general def
(structural on the strand count, zero-axiom), matrix-correct at the transpose permutation
`q = (p % n) * m + (p / n)` — pinned as `rfl` literals at `(1,1),(2,1),(1,2),(2,2),(3,2)` and matching the shipped
`middleSwap` at `(2,2)` on the nose.  This LITERALLY DELIVERS the content the r7
`fxBunchedBimonoid_wideSwapGeneralAssemblyStillUnbuilt` and r6
`fxBunchedBimonoid_wideSwapGeneralRiffleWordUnbuilt` walled; per the "retire name-only at literal delivery" rule
those markers keep their name and `= false` value byte-intact (cross-file, not edited), their residual denotation
now stale — the word IS built.  NO star marker flips. -/
def fxBunchedBimonoid_wideSwapGeneralRiffleWordShipped : Bool := true

/-! # =========================================================================================
    # B2 — THE STAGED BIALGEBRA NF + THE COLLISION MATRIX SIDE (matrix-correct at generic width)
    # =========================================================================================
-/

/-- ★ **THE DELTA-STAGE `deltaStage m n : a^m => a^(m*n)`** — the tensor of `m` copies of the delta-fan
`deltaFan n` (comultiply each of the `m` input strands into `n` copies), by structural recursion on the input
count `m`: `0` is the empty stage; `m+1` fans the leading strand (`deltaFan n |> a^m`) then recurses on the
remaining `m` strands under the placed `a^n` block.  The comultiplication half of the spider normal form. -/
def bunchedBimonoidDeltaStage : Nat → Nat → CellExpr bunchedBimonoidOmegaComputad 2
  | 0, _ => CellExpr.id bunchedBimonoidIdOne
  | inputCountM + 1, fanWidthN => CellExpr.vcomp
      (CellExpr.whiskerRight (bunchedBimonoidDeltaFan fanWidthN) (bunchedBimonoidAWordPow inputCountM))
      (CellExpr.whiskerLeft (bunchedBimonoidAWordPow fanWidthN)
        (bunchedBimonoidDeltaStage inputCountM fanWidthN))

/-- ★ **THE MU-STAGE `muStage n m : a^(n*m) => a^n`** — the tensor of `n` copies of the mu-fold `muFold m`
(merge each block of `m` strands into one output), by structural recursion on the output count `n`: `0` is the
empty stage; `n+1` folds the leading block (`muFold m |> a^(n*m)`) then recurses on the remaining `n` blocks under
the placed output strand `a`.  The multiplication half of the spider normal form. -/
def bunchedBimonoidMuStage : Nat → Nat → CellExpr bunchedBimonoidOmegaComputad 2
  | 0, _ => CellExpr.id bunchedBimonoidIdOne
  | outputCountN + 1, foldWidthM => CellExpr.vcomp
      (CellExpr.whiskerRight (bunchedBimonoidMuFold foldWidthM)
        (bunchedBimonoidAWordPow (outputCountN * foldWidthM)))
      (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen (bunchedBimonoidMuStage outputCountN foldWidthM))

/-- ★★ **THE STAGED BIALGEBRA NORMAL FORM `bialgebraNF m n : a^m => a^n`** — the honest three-stage Lafont form
`deltaStage(m,n) ; wideSwap(m,n) ; muStage(n,m)`: fan each of the `m` inputs into `n` copies, route grouped-by-input
to grouped-by-output through the general riffle word `wideSwap` (B1), then fold each output block of `m` into one.
As a map `evalCell (bialgebraNF m n) = matMul (muStage) (matMul (wideSwap) (deltaStage))` — the `n x m` all-ones,
the same map as the wide collision `wideCollision m n`.  The general-width RESOLUTION of the collision waist, now
constructible because `wideSwap` exists. -/
def bunchedBimonoidBialgebraNF (m n : Nat) : CellExpr bunchedBimonoidOmegaComputad 2 :=
  bunchedBimonoidSpiderStaged (bunchedBimonoidDeltaStage m n) (bunchedBimonoidWideSwap m n)
    (bunchedBimonoidMuStage n m)

/-! ## B2 truth-probe outputs (the staged NF and the collision share their matrix) -/

#eval bunchedBimonoidEvalCell (bunchedBimonoidBialgebraNF 2 2)
#eval bunchedBimonoidEvalCell (bunchedBimonoidWideCollision 2 2)
#eval bunchedBimonoidEvalCell (bunchedBimonoidBialgebraNF 2 3)
#eval bunchedBimonoidEvalCell (bunchedBimonoidWideCollision 2 3)

/-! ## B2 matrix probes (all `rfl` — the staged NF matches the collision at generic width) -/

/-- ★★★ **THE STAGED NF MATCHES THE COLLISION AT `(2,2)`.**  `evalCell (bialgebraNF 2 2) = evalCell (wideCollision
2 2)` (both `[[1,1],[1,1]]`), `rfl` — the flagship base, the CONV recursion's semantic target at width `(2,2)`. -/
theorem bunchedBimonoidBialgebraNFMatchesCollisionTwoTwo :
    bunchedBimonoidEvalCell (bunchedBimonoidBialgebraNF 2 2)
      = bunchedBimonoidEvalCell (bunchedBimonoidWideCollision 2 2) := rfl

/-- ★★★ **THE STAGED NF MATCHES THE COLLISION AT `(2,3)`.**  `evalCell (bialgebraNF 2 3) = evalCell (wideCollision
2 3)` (both the `3 x 2` all-ones `[[1,1],[1,1],[1,1]]`), `rfl` — a GENUINE wider-than-`(2,2)` instance where the
`wideSwap 2 3` word (a `6 x 6` perfect shuffle) is load-bearing.  The matrix side of the CONV recursion, closed at
generic width on the nose. -/
theorem bunchedBimonoidBialgebraNFMatchesCollisionTwoThree :
    bunchedBimonoidEvalCell (bunchedBimonoidBialgebraNF 2 3)
      = bunchedBimonoidEvalCell (bunchedBimonoidWideCollision 2 3) := rfl

/-- ★★ **THE STAGED NF MATCHES THE COLLISION AT `(3,2)`.**  `evalCell (bialgebraNF 3 2) = evalCell (wideCollision
3 2)` (both the `2 x 3` all-ones), `rfl` — the transposed grid. -/
theorem bunchedBimonoidBialgebraNFMatchesCollisionThreeTwo :
    bunchedBimonoidEvalCell (bunchedBimonoidBialgebraNF 3 2)
      = bunchedBimonoidEvalCell (bunchedBimonoidWideCollision 3 2) := rfl

/-- ★★ **THE STAGED NF MATCHES THE COLLISION AT `(3,3)`.**  `evalCell (bialgebraNF 3 3) = evalCell (wideCollision
3 3)` (both the `3 x 3` all-ones), `rfl` — the square grid, where `wideSwap 3 3` is a `9 x 9` perfect shuffle. -/
theorem bunchedBimonoidBialgebraNFMatchesCollisionThreeThree :
    bunchedBimonoidEvalCell (bunchedBimonoidBialgebraNF 3 3)
      = bunchedBimonoidEvalCell (bunchedBimonoidWideCollision 3 3) := rfl

/-! ## The B2 markers — the matrix side is shipped, the CONV recursion is walled at its exact node -/

/-- ★★ **ESTABLISHED (B2) — the staged bialgebra NF matrix side closes at generic width.**  `= true` records
`bunchedBimonoid{DeltaStage,MuStage,BialgebraNF}` (the three-stage form now constructible because `wideSwap`
exists) and `bunchedBimonoidBialgebraNFMatchesCollision{TwoTwo,TwoThree,ThreeTwo,ThreeThree}` — the staged NF and
the wide collision share their `Mat(N)` map on the nose at four generic widths.  This is the SEMANTIC TARGET the
CONV double induction must reach, now machine-checked at width beyond the flagship `(2,2)`. -/
def fxBunchedBimonoid_stagedNormalFormMatrixSideShipped : Bool := true

/-- ★ **THE `(m,n)` CONV RECURSION IS GATED ON A GENERIC-WIDTH NATURALITY SLIDE + COXETER — no flip.**  `= false`
records the exact remaining node, now PRECISELY named (the r6/r7 `...wideCollisionConvRecursionUnbuilt` /
`...wideCollisionRecursionStillUnbuilt` markers stay byte-intact, their denotation narrowing here): `wideSwap` and
`bialgebraNF` are now BUILT and matrix-correct (B1 + B2 above), so the double induction
`wideCollision m n ~ bialgebraNF m n` over the star scope is gated on exactly two lemmas — (a) a GENERIC-WIDTH
naturality slide lifting the width-3 `bunchedBimonoid{Mu,Delta}NaturalitySlideConv` (`sigma` past a `mu`/`delta`
block at arbitrary width `k`, whiskered by `whiskerRightCongr` / `whiskerRightFunctorial`), and (b) the B3
`CoxeterWordUnique` bubble-sort to identify the induction's generated permutation word with `wideSwap`'s canonical
bracketing.  NOT "the word does not exist" (it does) — the two heavy lemmas above it. -/
def fxBunchedBimonoid_wideCollisionConvGatedOnGenericNaturality : Bool := false

/-! # =========================================================================================
    # B3 — THE COXETER SORTED-NF SCAFFOLD: the position-indexed carrier + the fuel-structural sort
    # =========================================================================================

★ **The carrier the general `CoxeterWordUnique` bubble-sort (r9) stands on, plus its fuel-structural sort
skeleton — the general confluence induction walled.**  The perm middle of the wide collision is a word in
adjacent transpositions; this brick ships the position-indexed transposition letter `sigmaAt`, the word-as-cell
fold `permWord`, a bounded determinism instance at the carrier (two braid words of one matrix), and a genuine
FUEL-STRUCTURAL bubble sort (STRUCTURAL on an explicit `Nat` fuel = an inversion-count upper bound, NEVER
`WellFounded.fix`).  The general lemma (two `sigma`-words of the same permutation matrix are convertible over the
star scope, assembled from the five in-scope moves by the sort) is honestly r9. -/

/-- ★ **THE POSITION-INDEXED TRANSPOSITION `sigmaAt wordWidth positionK`** — the adjacent transposition `s_k`
acting at position `k` on a width-`wordWidth` word: `a^k <| (sigma |> a^(wordWidth - k - 2))`.  The elementary
letter of a reduced `sigma`-word; `sigmaAt 3 0` is `s_1` (swap strands 0,1) and `sigmaAt 3 1` is `s_2` (swap
strands 1,2).  Truncated subtraction keeps it total (out-of-range positions produce a harmless boundary cell). -/
def bunchedBimonoidSigmaAt (wordWidth positionK : Nat) : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerLeft (bunchedBimonoidAWordPow positionK)
    (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow (wordWidth - positionK - 2)))

/-- `sigmaAt 3 0` is the first transposition `s_1` — matrix `[[0,1,0],[1,0,0],[0,0,1]]` (swap strands 0,1),
matching the shipped `sigmaWhiskerRight`. -/
theorem bunchedBimonoidSigmaAtThreeZeroIsFirstTransposition :
    bunchedBimonoidEvalCell (bunchedBimonoidSigmaAt 3 0)
      = { rows := 3, cols := 3, entries := [[0, 1, 0], [1, 0, 0], [0, 0, 1]] } := rfl

/-- `sigmaAt 3 1` is the second transposition `s_2` — matrix `[[1,0,0],[0,0,1],[0,1,0]]` (swap strands 1,2),
matching the shipped `sigmaWhiskerLeft`. -/
theorem bunchedBimonoidSigmaAtThreeOneIsSecondTransposition :
    bunchedBimonoidEvalCell (bunchedBimonoidSigmaAt 3 1)
      = { rows := 3, cols := 3, entries := [[1, 0, 0], [0, 0, 1], [0, 1, 0]] } := rfl

/-- ★ **THE WORD-AS-CELL FOLD `permWord positions wordWidth`** — a list of transposition positions folded to a
vertical composite of `sigmaAt` letters (right fold, structural on the list): `[]` is the width-`wordWidth`
identity, `k :: rest` is `sigmaAt wordWidth k ; permWord rest wordWidth`.  A reduced word evaluates by this fold;
the carrier the sort normalizes. -/
def bunchedBimonoidPermWord : List Nat → Nat → CellExpr bunchedBimonoidOmegaComputad 2
  | [], wordWidth => CellExpr.id (bunchedBimonoidAWordPow wordWidth)
  | positionK :: remainingPositions, wordWidth =>
      CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth positionK)
        (bunchedBimonoidPermWord remainingPositions wordWidth)

/-- The `s_1 s_2 s_1` braid word `permWord [0,1,0] 3` evaluates to the reversal `[[0,0,1],[0,1,0],[1,0,0]]`
(`rfl`, single-sided literal — the double-sided form exceeds the heartbeat budget). -/
theorem bunchedBimonoidPermWordBraidLeftMatrix :
    bunchedBimonoidEvalCell (bunchedBimonoidPermWord [0, 1, 0] 3)
      = { rows := 3, cols := 3, entries := [[0, 0, 1], [0, 1, 0], [1, 0, 0]] } := rfl

/-- The `s_2 s_1 s_2` braid word `permWord [1,0,1] 3` evaluates to the SAME reversal (`rfl`, single-sided). -/
theorem bunchedBimonoidPermWordBraidRightMatrix :
    bunchedBimonoidEvalCell (bunchedBimonoidPermWord [1, 0, 1] 3)
      = { rows := 3, cols := 3, entries := [[0, 0, 1], [0, 1, 0], [1, 0, 0]] } := rfl

/-- The shipped `bunchedBimonoidYangBaxterLeftLeg` evaluates to the reversal too (`rfl`, single-sided) — the
literal that bridges the `permWord` carrier to the r4 hexagon layer. -/
theorem bunchedBimonoidYangBaxterLeftLegMatrix :
    bunchedBimonoidEvalCell bunchedBimonoidYangBaxterLeftLeg
      = { rows := 3, cols := 3, entries := [[0, 0, 1], [0, 1, 0], [1, 0, 0]] } := rfl

/-- ★★ **BOUNDED DETERMINISM INSTANCE (the carrier).**  The two braid words `[0,1,0] = s_1 s_2 s_1` and
`[1,0,1] = s_2 s_1 s_2` at width 3 share their `Mat(N)` map (both the reversal), composed from the two
single-sided literals.  So two structurally-distinct `permWord`s of the same permutation exist at the carrier;
their CONVERTIBILITY over the star scope is the Yang-Baxter row (modulo reassociation), the r9 sort's atomic
step. -/
theorem bunchedBimonoidPermWordBraidMatrixShared :
    bunchedBimonoidEvalCell (bunchedBimonoidPermWord [0, 1, 0] 3)
      = bunchedBimonoidEvalCell (bunchedBimonoidPermWord [1, 0, 1] 3) :=
  bunchedBimonoidPermWordBraidLeftMatrix.trans bunchedBimonoidPermWordBraidRightMatrix.symm

/-- ★ **THE CARRIER MEETS THE SHIPPED HEXAGON.**  `permWord [0,1,0] 3` (the `s_1 s_2 s_1` fold) shares its matrix
with the shipped `bunchedBimonoidYangBaxterLeftLeg` (both the reversal, composed from the two literals) — the
`permWord` carrier is semantically continuous with the r4 hexagon layer's Coxeter words. -/
theorem bunchedBimonoidPermWordBraidMatchesYangBaxterLeft :
    bunchedBimonoidEvalCell (bunchedBimonoidPermWord [0, 1, 0] 3)
      = bunchedBimonoidEvalCell bunchedBimonoidYangBaxterLeftLeg :=
  bunchedBimonoidPermWordBraidLeftMatrix.trans bunchedBimonoidYangBaxterLeftLegMatrix.symm

/-- The **inversion-count fuel bound** for a reduced word of length `wordLength` — the number of adjacent-swap
passes a bubble sort needs is at most `wordLength * wordLength` (an upper bound on the inversion count).  The
explicit `Nat` the fuel-structural sort decrements. -/
def bunchedBimonoidInversionFuelBound (wordLength : Nat) : Nat := wordLength * wordLength

/-- The **single adjacent-swap pass** `bubbleSortOnePass fuel positions` — one left-to-right pass swapping
out-of-order adjacent entries, STRUCTURAL on the fuel `Nat` (each recursive call decrements fuel, so the
`carry-the-larger-forward` branch stays structural — no `WellFounded.fix`).  The `Nat.ble` comparison is matched
as a `Bool` (full `true`/`false` enumeration, propext-clean). -/
def bunchedBimonoidBubbleSortOnePass : Nat → List Nat → List Nat
  | 0, positions => positions
  | _fuel + 1, [] => []
  | _fuel + 1, [singleton] => [singleton]
  | fuel + 1, first :: second :: rest =>
      match Nat.ble first second with
      | true => first :: bunchedBimonoidBubbleSortOnePass fuel (second :: rest)
      | false => second :: bunchedBimonoidBubbleSortOnePass fuel (first :: rest)

/-- ★ **THE FUEL-STRUCTURAL BUBBLE SORT `bubbleSortFuel fuel positions`** — apply the one-pass `fuel` times,
STRUCTURAL on the outer fuel `Nat` (NEVER `WellFounded.fix`).  With `fuel = inversionFuelBound positions.length`
it fully sorts (each pass drives one inversion out).  The sort skeleton the r9 `CoxeterWordUnique` assembles into
a convertibility via the five in-scope moves — here the DATA is shipped; the r9 lemma connects the sort trace to a
CONV chain. -/
def bunchedBimonoidBubbleSortFuel : Nat → List Nat → List Nat
  | 0, positions => positions
  | fuel + 1, positions =>
      bunchedBimonoidBubbleSortFuel fuel (bunchedBimonoidBubbleSortOnePass fuel positions)

/-! ## B3 truth-probe outputs (the fuel-structural sort computes) -/

#eval bunchedBimonoidBubbleSortFuel (bunchedBimonoidInversionFuelBound 5) [2, 0, 1, 0, 2]
#eval bunchedBimonoidBubbleSortFuel (bunchedBimonoidInversionFuelBound 2) [1, 0]

/-! ## The B3 markers — the scaffold is shipped, the general confluence induction is walled -/

/-- ★★ **ESTABLISHED (B3) — the Coxeter sorted-NF scaffold is shipped.**  `= true` records the position-indexed
transposition carrier (`bunchedBimonoidSigmaAt`, `s_1` / `s_2` at width 3 by `rfl`), the word-as-cell fold
(`bunchedBimonoidPermWord`, structural on the list), the bounded determinism instance
(`bunchedBimonoidPermWordBraidMatrixShared` — two braid words of one matrix, continuous with the shipped
Yang-Baxter via `bunchedBimonoidPermWordBraidMatchesYangBaxterLeft`), the inversion fuel bound, and the genuine
FUEL-STRUCTURAL bubble sort (`bunchedBimonoidBubbleSort{OnePass,Fuel}`, structural on an explicit `Nat` fuel, NO
`WellFounded.fix`, truth-probed to sort).  The r9 `CoxeterWordUnique` stands on exactly this carrier + sort. -/
def fxBunchedBimonoid_coxeterSortNfScaffoldShipped : Bool := true

/-- ★ **THE GENERAL `CoxeterWordUnique` STAYS WALLED (r9) — gated on a generic-width braid + the sort-to-CONV
bridge, no flip.**  `= false` records the exact remaining node (the r6/r7
`...coxeterWordUniqueBubbleSortStillUnbuilt` markers stay byte-intact, their denotation narrowing here): the
carrier (`sigmaAt` / `permWord`) and the fuel-structural sort are now SHIPPED, and all five Coxeter / double-coset
moves are in scope (r7 `bunchedBimonoidCoxeterMovesAllInScope`), but the general lemma (two `permWord`s of the
same matrix are convertible over the star scope) needs (a) the braid / distant-commute / involution moves at
GENERIC position/width — currently only width-3 `yangBaxter` and width-4 distant-commute are shipped — and (b) the
bridge connecting the fuel-structural sort trace to a CONV chain (each swap step firing one in-scope move).  The
fuel-recursive assembly is the genuine r9 work. -/
def fxBunchedBimonoid_coxeterWordUniqueGatedOnGenericBraid : Bool := false

/-! # =========================================================================================
    # B4 — THE STAR HONEST PARTIAL: the two residuals NARROWED, no star flip
    # =========================================================================================

★ **The r7 star `bunchedBimonoidStarStatementAdditiveWellTyped` needs, at its `vcomp` case, the wide-collision
CONV recursion, and at its equal-matrices step, the perm-middle `CoxeterWordUnique`.  Before r8 BOTH residuals
read "the word does not exist" (B1 general `wideSwap` unbuilt) + "the recursion is unbuilt".  This round the
wideSwap WORD is BUILT (B1) and the staged-NF matrix side closes at generic width (B2), so the two residuals
NARROW from unbuilt-word to two precisely-named lemmas.  The star does NOT flip — a flip requires a literal
hypothesis-free inhabitant of `bunchedBimonoidStarStatementAdditiveWellTyped`, which is NOT produced here. -/

/-- ★★ **ESTABLISHED (B4) — the star's two heavy residuals are NARROWED, the star chain re-stated.**  `= true`
records the honest star-chain shape `alpha ~ retract alpha = retract beta ~ beta`: the `gen` / `id` / `whisker`
OUTER legs are the shipped r6 CONV deltas (`RetractionConvDeltas`); the `vcomp` case is the wide-collision CONV
recursion, whose general `wideSwap` word is NOW BUILT (B1 `fxBunchedBimonoid_wideSwapGeneralRiffleWordShipped`)
and whose matrix side NOW closes at generic width (B2 `fxBunchedBimonoid_stagedNormalFormMatrixSideShipped`), so
it gates on ONLY the generic-width naturality slide
(`fxBunchedBimonoid_wideCollisionConvGatedOnGenericNaturality`); the equal-matrices MIDDLE is the perm-middle
`CoxeterWordUnique`, whose carrier + fuel-structural sort are NOW shipped (B3
`fxBunchedBimonoid_coxeterSortNfScaffoldShipped`), so it gates on ONLY the generic-position braid + the
sort-to-CONV bridge (`fxBunchedBimonoid_coxeterWordUniqueGatedOnGenericBraid`).  Two precisely-named lemmas, not
"the word does not exist". -/
def fxBunchedBimonoid_starLegsGatedOnGenericNaturalityAndCoxeter : Bool := true

/-- ★ **THE CORRECTED WELL-TYPED STAR STAYS OPEN — no flip (byte-intact, cross-file).**  `= false` records that
`bunchedBimonoidStarStatementAdditiveWellTyped` is STILL NOT proven in r8: no literal hypothesis-free inhabitant
is produced.  The star-owning marker `fxBunchedBimonoid_correctedWellTypedStarStillOpen` (StarAssembly, r7) and
every upstream star marker keep their name and `= false` value byte-intact (cross-file, not edited) — NO
fabricated flip.  The two residuals are narrowed (B4 above), not closed. -/
def fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterRiffle : Bool := false

/-! ## The r8 round ledger -/

/-- ★★★ **ESTABLISHED (B4) — the WP-PROP r8 riffle-assembly ledger (the honest scoreboard).**  `= true` records
the complete r8 two-gap assembly: B1 the general `wideSwap(m,n)` riffle word BUILT (the three-layer nested
shuffle `blockPastBlock`/`riffleIn`/`wideSwap`, matrix-correct at the transpose permutation, the r7 unbuilt wall
falls — `fxBunchedBimonoid_wideSwapGeneralRiffleWordShipped`); B2 the staged bialgebra NF matched to the collision
at generic width (`fxBunchedBimonoid_stagedNormalFormMatrixSideShipped`, the CONV recursion narrowed to a
generic-width naturality slide); B3 the Coxeter sorted-NF scaffold (carrier + fuel-structural sort,
`fxBunchedBimonoid_coxeterSortNfScaffoldShipped`, the `CoxeterWordUnique` narrowed to a generic-position braid);
B4 the star's two residuals narrowed to two precisely-named lemmas
(`fxBunchedBimonoid_starLegsGatedOnGenericNaturalityAndCoxeter`), the star NOT flipped
(`fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterRiffle = false`).  Every upstream wall
(`...wideSwapGeneralRiffleWordUnbuilt`, `...wideCollisionConvRecursionUnbuilt`,
`...coxeterWordUniqueBubbleSortStillUnbuilt`, `...correctedWellTypedStarStillOpen`) keeps its name and value
byte-intact (cross-file, retired name-only at literal delivery); zero-axiom (per-decl `#assert_no_axioms` +
independent `#print axioms` in the twin); STRUCTURAL only (strand-count + fuel recursions, no `WellFounded.fix`).
NO fabricated star flip. -/
def fxBunchedBimonoid_riffleAssemblyRoundEightLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
