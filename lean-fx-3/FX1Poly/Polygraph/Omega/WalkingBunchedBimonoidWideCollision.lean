import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarRetractionCensus

/-! # Polygraph/Omega/WalkingBunchedBimonoidWideCollision — the wide bialgebra collision, lifted from a MATRIX
witness to a CONVERTIBILITY witness at the base + the degenerate easy half, with the general `(m,n)` routing
recursion honestly walled (WP-PROP r6, #2033, the 110-percent grind)

★ **The r5 `StarRetractionCensus` shipped the width-2 collision as a MATRIX equality
(`bunchedBimonoidWidthTwoCollisionMatrix : evalCell (mu_a ; delta_a) = [[1,1],[1,1]]`).  This file lifts the
collision to the SYNTACTIC (convertibility) level at the two decidable ends of the collision grid `(m,n)` and
names the wide routing recursion at its exact residual node.**

## The collision family and its two provable ends

  * **The width-2 base `(2,2)` — a ONE-STEP fire.**  `mu_a ; delta_a` (`= bunchedBimonoidBialgebraProductLeftLeg`
    definitionally) is convertible to the staged bialgebra normal form `bunchedBimonoidBialgebraProductRightLeg`
    (`= (mu (x) mu) ; (1 (x) sigma (x) 1) ; (delta (x) delta)`) by a SINGLE `BunchedBimonoidSoundRow.bialgebraProduct`
    row fired through the star scope's `Or.inr (Or.inl ...)` selector.  This is the recon's self-attack (a): the
    (2,2) recursion base is a lone `bialgebraProduct` brick, NOT a routing.
  * **The degenerate `(1,n)` / `(m,1)` ends — unit collapses.**  `muFold 1 = id_a` and `deltaFan 1 = id_a`, so the
    collision `muFold m ; deltaFan n` collapses at `m = 1` to `deltaFan n` (left-unit row) and at `n = 1` to
    `muFold m` (right-unit row) — no routing, the easy half.  The source / target boundary lemmas
    (`bunchedBimonoidDeltaFanSource`, `bunchedBimonoidMuFoldTarget`) discharge the strict-unit row's boundary side.

## The wide routing recursion (the honest residual)

The general `(m,n)` collision `muFold m ; deltaFan n` normalizes to `deltaStage(m,n) ; wideSwap(m,n) ;
muStage(m,n)` where `wideSwap(m,n)` is the riffle permutation regrouping "by input" to "by output" — a word in
whiskered `sigma`s that DOES NOT exist as a general def (the (2,2) instance is the shipped
`bunchedBimonoidMiddleSwap`).  The double induction on `(m,n)` peels one `mu` / `delta`, fires one width-2
`bialgebraProduct` brick, and threads the generated `sigma` across the residual `mu`/`delta` via the hexagon
naturality rows (`muNaturality` / `deltaNaturality`) + whisker congruence.  The MATRIX side of the full collision
is concrete-`rfl` at every fixed width (`bunchedBimonoidWideCollisionMatrixThreeByTwo`, self-attack (b)); the
CONV-level routing recursion is the genuine r6 residual, named at its exact node.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! The width-3 `matMul` `rfl` reduction exceeds the default heartbeat budget; the raise is a compute allowance
only, the proof terms stay `Eq.refl`, axiom-free (uniform with the r4 `PermStage` / `Hexagon` reductions). -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # B1 — THE COLLISION FAMILY + THE WIDTH-2 CONV BASE (the one-step bialgebra fire)
    # =========================================================================================
-/

/-- ★ The **wide collision family** `muFold m ; deltaFan n : a^m => a^n` — fold `m` input strands to one, then
fan the one to `n` outputs.  As a map `evalCell (wideCollision m n) = matMul (deltaFan n)(muFold m)` = the `n x m`
all-ones matrix (every input feeds every output through the single waist strand).  The bialgebra normal form
resolves this waist into the routed `deltaStage ; wideSwap ; muStage`. -/
def bunchedBimonoidWideCollision (m n : Nat) : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (bunchedBimonoidMuFold m) (bunchedBimonoidDeltaFan n)

/-- ★★ **THE WIDTH-2 COLLISION AS CONVERTIBILITY (the one-step fire).**  `mu_a ; delta_a`
(`= bunchedBimonoidBialgebraProductLeftLeg` definitionally) is convertible over the star scope to the staged
bialgebra RHS `bunchedBimonoidBialgebraProductRightLeg` by a SINGLE `BunchedBimonoidSoundRow.bialgebraProduct`
row, fired through the star scope's `Or.inr (Or.inl ...)` selector.  The recon's self-attack (a): the (2,2)
recursion base is a lone `bialgebraProduct` brick.  This is the CONV upgrade of the r5 matrix witness
`bunchedBimonoidWidthTwoCollisionMatrix`. -/
theorem bunchedBimonoidWidthTwoCollisionConv :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp bunchedBimonoidAddMuGen bunchedBimonoidAddDeltaGen)
      bunchedBimonoidBialgebraProductRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr (Or.inl BunchedBimonoidSoundRow.bialgebraProduct))

/-- ★ **The width-2 collision IS the `(2,2)` member of the family** — `wideCollision 2 2 = mu_a ; delta_a` up to
the `muFold 2` / `deltaFan 2` staged spellings (both `[[1,1]]` / `[[1],[1]]` on the nose), so the collision
family's `(2,2)` matrix is the all-ones `[[1,1],[1,1]]`. -/
theorem bunchedBimonoidWideCollisionTwoTwoMatrix :
    bunchedBimonoidEvalCell (bunchedBimonoidWideCollision 2 2)
      = { rows := 2, cols := 2, entries := [[1, 1], [1, 1]] } := rfl

/-! # =========================================================================================
    # B1 — THE BOUNDARY LEMMAS + THE DEGENERATE (1,n) / (m,1) UNIT COLLAPSES (the easy half)
    # =========================================================================================
-/

/-- ★ **The delta-fan sources at `a`** — `boundarySource (deltaFan n) = a` for every `n`.  A three-way case split
(`0` = eps sources at `a`; `1` = `id a` sources at `a`; `k+2` = the leftmost `delta` sources at `a`); each `rfl`,
no recursion (the `vcomp`'s source is read off its left factor). -/
theorem bunchedBimonoidDeltaFanSource : (n : Nat) →
    boundarySource (bunchedBimonoidDeltaFan n) = bunchedBimonoidAdditiveGen
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- ★ **The mu-fold targets at `a`** — `boundaryTarget (muFold m) = a` for every `m`.  The dual three-way split
(`0` = eta targets at `a`; `1` = `id a` targets at `a`; `k+2` = the rightmost `mu` targets at `a`); each `rfl`. -/
theorem bunchedBimonoidMuFoldTarget : (m : Nat) →
    boundaryTarget (bunchedBimonoidMuFold m) = bunchedBimonoidAdditiveGen
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- ★★ **THE DEGENERATE `(1,n)` COLLAPSE (the left easy half).**  At `m = 1` the collision `muFold 1 ; deltaFan n`
collapses to `deltaFan n`: `muFold 1 = id_a`, and the strict left-unit row `vcompUnitLeft` fires on
`(id (boundarySource (deltaFan n))) ; deltaFan n` once the boundary is rewritten to `a` via
`bunchedBimonoidDeltaFanSource`.  No routing — the easy half of the collision recursion. -/
theorem bunchedBimonoidCollisionMuFoldOneCollapse (n : Nat) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidWideCollision 1 n) (bunchedBimonoidDeltaFan n) := by
  have unitRow : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp (CellExpr.id (boundarySource (bunchedBimonoidDeltaFan n))) (bunchedBimonoidDeltaFan n))
      (bunchedBimonoidDeltaFan n) :=
    SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft (bunchedBimonoidDeltaFan n)))
  rw [bunchedBimonoidDeltaFanSource n] at unitRow
  exact unitRow

/-- ★★ **THE DEGENERATE `(m,1)` COLLAPSE (the right easy half).**  At `n = 1` the collision `muFold m ; deltaFan 1`
collapses to `muFold m`: `deltaFan 1 = id_a`, and the strict right-unit row `vcompUnitRight` fires on
`muFold m ; (id (boundaryTarget (muFold m)))` once the boundary is rewritten to `a` via
`bunchedBimonoidMuFoldTarget`.  The dual easy half. -/
theorem bunchedBimonoidCollisionDeltaFanOneCollapse (m : Nat) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidWideCollision m 1) (bunchedBimonoidMuFold m) := by
  have unitRow : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp (bunchedBimonoidMuFold m) (CellExpr.id (boundaryTarget (bunchedBimonoidMuFold m))))
      (bunchedBimonoidMuFold m) :=
    SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitRight (bunchedBimonoidMuFold m)))
  rw [bunchedBimonoidMuFoldTarget m] at unitRow
  exact unitRow

/-! # =========================================================================================
    # B1 — THE STAGED (2,2) NORMAL FORM + THE MATRIX SIDE OF THE WIDE COLLISION (self-attack (b))
    # =========================================================================================
-/

/-- ★ The **staged `(2,2)` bialgebra normal form** `bialgebraNF 2 2 := spiderStaged (delta (x) delta) (middleSwap)
(mu (x) mu)` — the honest three-stage form `deltaStage ; wideSwap ; muStage` at width `(2,2)`, with
`wideSwap(2,2) = bunchedBimonoidMiddleSwap` (the shipped `1 (x) sigma (x) 1`).  It differs from the shipped
`bunchedBimonoidBialgebraProductRightLeg` only by the `vcomp` re-association (`(D ; P) ; M` vs `D ; (P ; M)`),
both convertible via `vcompAssoc`. -/
def bunchedBimonoidBialgebraNormalFormTwoTwo : CellExpr bunchedBimonoidOmegaComputad 2 :=
  bunchedBimonoidSpiderStaged bunchedBimonoidDeltaTensorDelta bunchedBimonoidMiddleSwap
    bunchedBimonoidMuTensorMu

/-- ★ **The staged `(2,2)` NF has the all-ones matrix** — `evalCell (bialgebraNF 2 2) = [[1,1],[1,1]]`, the same
map as the width-2 collision (`bunchedBimonoidWideCollisionTwoTwoMatrix`).  The matrix side of the base
resolution, `rfl`. -/
theorem bunchedBimonoidBialgebraNormalFormTwoTwoMatrix :
    bunchedBimonoidEvalCell bunchedBimonoidBialgebraNormalFormTwoTwo
      = { rows := 2, cols := 2, entries := [[1, 1], [1, 1]] } := rfl

/-- ★★ **THE WIDE COLLISION MATRIX SIDE (self-attack (b), width-3).**  `evalCell (muFold 2 ; deltaFan 3) =
[[1,1],[1,1],[1,1]]` (the `3 x 2` all-ones): the collision waist multiplies the `3 x 1` fan column by the `1 x 2`
fold row.  A genuine wider-than-(2,2) instance where the CONV recursion MUST fire (peel + brick + slide) — the
matrix side is concrete `rfl`, confirming residual (1) is genuine (matrix provable, conv recursion unbuilt). -/
theorem bunchedBimonoidWideCollisionMatrixThreeByTwo :
    bunchedBimonoidEvalCell (bunchedBimonoidWideCollision 2 3)
      = { rows := 3, cols := 2, entries := [[1, 1], [1, 1], [1, 1]] } := rfl

/-- ★★ **THE WIDE COLLISION MATRIX SIDE (self-attack (b), the transposed 2x3).**  `evalCell (muFold 3 ; deltaFan 2)
= [[1,1,1],[1,1,1]]` (the `2 x 3` all-ones) — the transpose grid, again concrete `rfl`. -/
theorem bunchedBimonoidWideCollisionMatrixTwoByThree :
    bunchedBimonoidEvalCell (bunchedBimonoidWideCollision 3 2)
      = { rows := 2, cols := 3, entries := [[1, 1, 1], [1, 1, 1]] } := rfl

/-! ## B1 truth-probe outputs -/

#eval bunchedBimonoidEvalCell (bunchedBimonoidWideCollision 2 2)
#eval bunchedBimonoidEvalCell (bunchedBimonoidWideCollision 2 3)
#eval bunchedBimonoidEvalCell (bunchedBimonoidWideCollision 3 2)

/-! ## The B1 honesty markers -/

/-- ★★ **ESTABLISHED (B1) — the width-2 collision is lifted from a matrix witness to a CONV witness.**  `= true`
records `bunchedBimonoidWidthTwoCollisionConv` (the (2,2) base is a one-step `bialgebraProduct` fire through the
star scope), the staged `(2,2)` normal form `bunchedBimonoidBialgebraNormalFormTwoTwo` (matrix `[[1,1],[1,1]]`),
and the two degenerate collapses `bunchedBimonoidCollision{MuFoldOne,DeltaFanOne}Collapse` (the `(1,n)` / `(m,1)`
unit ends).  The CONV upgrade of the r5 matrix-only `bunchedBimonoidWidthTwoCollisionMatrix`. -/
def fxBunchedBimonoid_widthTwoCollisionLiftedToConv : Bool := true

/-- ★ **ESTABLISHED (B1) — the wide collision matrix side is concrete-`rfl` at width-3 (self-attack (b)).**
`= true` records `bunchedBimonoidWideCollisionMatrix{ThreeByTwo,TwoByThree}` — the `(2,3)` / `(3,2)` collision
grids evaluate to the `3 x 2` / `2 x 3` all-ones on the nose.  These are the genuine wider-than-(2,2) instances
where the CONV routing recursion MUST fire; the matrix side being trivially `rfl` while the conv side is unbuilt
is exactly what makes residual (1) a genuine research node. -/
def fxBunchedBimonoid_wideCollisionMatrixConcreteAtWidthThree : Bool := true

/-! # =========================================================================================
    # B1 — THE HONEST WIDE ROUTING RESIDUAL (the general `(m,n)` recursion, NOT flipped)
    # =========================================================================================
-/

/-- ★ **r6 RESIDUAL (1), RE-STATED at WORD granularity — the general `wideSwap(m,n)` riffle word does NOT exist.**
`= false` records the exact remaining node: the wide swap `wideSwap(m,n) : a^(m*n) => a^(m*n)` (the riffle
permutation `i*n+j |-> j*m+i` regrouping the `m*n` incidence strands "by input" to "by output") is a word in
whiskered `sigma`s that has NO general def — the (2,2) instance is the shipped `bunchedBimonoidMiddleSwap`, and
the width-3 generators are the shipped hexagon rows (`yangBaxter` / `muNaturality` / `deltaNaturality`), but the
general assembly is the routing crux.  Without `wideSwap` the staged `bialgebraNF(m,n) := spiderStaged
(deltaStage m n) (wideSwap m n) (muStage m n)` cannot be built for general `(m,n)`.  Cited byte-intact from
`fxBunchedBimonoid_r6WideCollisionRecursion` (r5 StarRetractionCensus). -/
def fxBunchedBimonoid_wideSwapGeneralRiffleWordUnbuilt : Bool := false

/-- ★ **r6 RESIDUAL (1), the CONV recursion — the `(m,n)` double induction is NOT shipped.**  `= false` records
the exact goal: a double induction on the collision grid `(m,n)` proving `muFold m ; deltaFan n` convertible (over
the star scope) to `bialgebraNF(m,n)`, each step (mu-peel `muFold (m+1) = (muFold m |> a) ; mu_a`, delta-peel
`deltaFan (n+1) = delta_a ; (deltaFan n |> a)`) firing ONE width-2 `bialgebraProduct` brick and threading the
generated `sigma` across the residual `mu`/`delta` via the hexagon naturality rows + `whiskerRightCongr` /
`whiskerRightFunctorial`, recursing on the reduced `(m-1,n)` / `(m,n-1)` sub-grid.  The base (2,2) is shipped
(`bunchedBimonoidWidthTwoCollisionConv`); the degenerate ends are shipped (`...Collapse`); the wide recursion is
the genuine work, gated on `fxBunchedBimonoid_wideSwapGeneralRiffleWordUnbuilt`.  Cited byte-intact from
`fxBunchedBimonoid_r6WideCollisionRecursion`. -/
def fxBunchedBimonoid_wideCollisionConvRecursionUnbuilt : Bool := false

/-- ★★ **ESTABLISHED (B1) — the WP-PROP r6 wide-collision ledger (honest scoreboard).**  `= true` records the
r6 collision advance: the collision family `bunchedBimonoidWideCollision`; the width-2 base lifted from matrix to
CONV (`bunchedBimonoidWidthTwoCollisionConv`, a one-step `bialgebraProduct` fire); the degenerate `(1,n)` / `(m,1)`
unit collapses (`...Collapse` + the boundary lemmas `bunchedBimonoidDeltaFanSource` / `...MuFoldTarget`); the
staged `(2,2)` normal form; and the wide matrix side concrete-`rfl` at width-3 (self-attack (b)).  The general
routing is walled at its exact node: the `wideSwap(m,n)` riffle word
(`fxBunchedBimonoid_wideSwapGeneralRiffleWordUnbuilt`) and the `(m,n)` conv recursion
(`fxBunchedBimonoid_wideCollisionConvRecursionUnbuilt`), both `= false` byte-intact with the r5
`fxBunchedBimonoid_r6WideCollisionRecursion`.  NO star marker flips. -/
def fxBunchedBimonoid_wideCollisionRoundSixLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
