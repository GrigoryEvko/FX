import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPresentation

/-! # Polygraph/Omega/WalkingBunchedBimonoidMatrixSemantics — the Mat(N) matrix semantics of the walking
bunched bimonoid (WP-BI r2, #2188)

★ **The map-level semantics the four-count could not be.**  The r1 walker (`WalkingBunchedBimonoidPresentation`)
shipped a *presentation* invariant — the Frobenius four-count `(#mu, #eta, #delta, #eps)` — which is SOUND over
the transported (co)monoid rows but is deliberately UNSOUND over the bialgebra B1 (it counts generators, so the
doubled `(mu, delta)` of the B1 right leg reads `(2,0,2,0) != (1,0,1,0)`), and which — being a mere occurrence
count — CANNOT tell the self-braiding `sigma_a` from the identity (both count `(0,0,0,0)`).  This file ships the
complementary MAP-level invariant: the free-bicommutative-bimonoid functor into `Mat(N)` (Lafont / Pirashvili /
Fox: bicommutative bimonoids are exactly the PROP of natural-number matrices under matrix multiplication).  Each
2-cell evaluates to a concrete `N`-matrix; convertible-as-maps 2-cells share their matrix.

## The carrier and the dimension-dependent evaluation motive

`BunchedBimonoidMat` is a Nat matrix with EXPLICIT `rows` / `cols` (the width-0 legs `eta : 1x0`, `eps : 0x1`,
the B4 bone `0x0` are otherwise indistinguishable in a bare `List (List Nat)`).  The evaluation motive
`BunchedBimonoidEvalCarrier` mirrors `boundaryMotive` (Carrier): `Unit` at dim 0 (a mode has no matrix), a WIDTH
`Nat` at dim 1 (a 1-cell word is a number of strands), a `BunchedBimonoidMat` at dim 2 (a 2-cell IS a linear
map), `Unit` above.  `bunchedBimonoidEvalCell` is the four-count fold made MATRIX-valued: `vcomp` becomes matrix
multiplication (dim 2) / width addition (dim 1); a generator becomes its declared matrix; and — unlike the
four-count, which ignores the whiskering 1-cell — whiskering becomes identity-block direct-sum (the whisker
WIDTH is faithfully placed as an identity block, first for `whiskerLeft`, last for `whiskerRight`).

## The convention pins (truth-probed, `#eval` + `rfl`)

  * `vcomp f g` = "`f` then `g`" (`boundarySource (vcomp f g) = boundarySource f`), so as a map it is `g` after
    `f`; hence `evalCell (vcomp f g) = matMul (eval g) (eval f)` (right operand applied first).
  * `whiskerLeft w c` = `w` on the LEFT => identity block FIRST; `whiskerRight c w` = `w` on the RIGHT =>
    identity block LAST.  Probed faithful: `whiskerLeft a delta` and `whiskerRight delta a` evaluate to DIFFERENT
    matrices (`[[1,0],[0,1],[0,1]]` vs `[[1,0],[1,0],[0,1]]`), so block placement is genuinely position-sensitive.
  * Generator matrices: `mu = [[1,1]]` (1x2), `eta = [[]]` (1x0), `delta = [[1],[1]]` (2x1), `eps = []` (0x1),
    `sigma = [[0,1],[1,0]]` (2x2); both colours `a`, `m` have WIDTH 1.

## The honest soundness scope (the truth-probe verdict — NOT the recon's naive "sound over all 22")

Evaluating all 22 r1 rows on the nose splits them cleanly:

  * **13 RESPECTED** — both legs evaluate to the SAME matrix (`rfl`): both pentagons, both rootUnitAssoc, the
    copentagon, the rootCounitCoassoc, the four bialgebra rows B1-B4, commutativity, cocommutativity, and the
    sigma-involution.  These are the "balanced" critical pairs (double-operation, or genuine (co)algebra laws).
  * **9 BROKEN** — the two legs evaluate to DIFFERENT matrices (machine-separated below): the single-operation
    whisker-commute pairs `op |> x` vs `x <| op` for `op` a lone (co)monoid generator — `unitUnit`,
    `leftUnitAssoc`, `rightUnitAssoc` (both mu-colours) and `counitCounit`, `leftCounitCoassoc`,
    `rightCounitCoassoc`.  Their legs are `op (x) 1` and `1 (x) op`, which are DISTINCT `Mat(N)` maps (they agree
    only after composing with the dual operation — the actual (co)associativity / (co)unit law).

Hence `Mat(N)` is a model of the 13-row balanced sub-relation but NOT of the full r1 22-row congruence — the
matrix is strictly FINER than the four-count (it separates `sigma` from `id`, which the count cannot) and, being
finer, it breaks on exactly the rows the coarse count survives.  The two invariants are Pareto-incomparable: the
four-count breaks on the bialgebra B1 (where the matrix is sound); the matrix breaks on the 9 op-commute rows
(where the four-count is sound).  This file ships (B1) the carrier + evaluation + the 13 respected equalities +
the 9 separations + the `sigma != id` separation, all `rfl` / `Nat.noConfusion`, zero-axiom.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # B1 — THE MATRIX CARRIER + THE EVALUATION (truth-probed on concrete words FIRST)
    # =========================================================================================
-/

/-! ## The Nat-matrix carrier (explicit dimensions) -/

/-- A **natural-number matrix** with EXPLICIT dimensions.  The `entries` invariant (`entries` has length `rows`,
each inner row has length `cols`) is documented, not indexed — every matrix arising from `bunchedBimonoidEvalCell`
satisfies it by construction, and the width-0 legs (`eta : 1x0`, `eps : 0x1`, the bone `0x0`) are distinguished
only because the dimensions are carried explicitly. -/
structure BunchedBimonoidMat where
  /-- The number of output strands (codomain width). -/
  rows : Nat
  /-- The number of input strands (domain width). -/
  cols : Nat
  /-- The row-major entries: `entries[rowIndex][colIndex]` is the `(rowIndex, colIndex)` coefficient. -/
  entries : List (List Nat)

/-- Structural **`List Nat` indexing** — out-of-range reads `0`.  Hand-rolled (NOT `List.getD`, which leaks
`propext`): a full structural recursion on the list then the index, propext-clean like `natSum`. -/
def bunchedBimonoidNatListGet : List Nat → Nat → Nat
  | [], _ => 0
  | head :: _, 0 => head
  | _ :: tail, colIndex + 1 => bunchedBimonoidNatListGet tail colIndex

/-- Structural **row indexing** into a list of rows — out-of-range reads the empty row.  Hand-rolled for the
same propext-cleanliness reason as `bunchedBimonoidNatListGet`. -/
def bunchedBimonoidRowListGet : List (List Nat) → Nat → List Nat
  | [], _ => []
  | head :: _, 0 => head
  | _ :: tail, rowIndex + 1 => bunchedBimonoidRowListGet tail rowIndex

/-- The **`(rowIndex, colIndex)` entry** of a matrix — out-of-range reads `0`.  Composes the two structural
indexers; propext-clean (`#assert_no_axioms` in the twin). -/
def bunchedBimonoidMatEntryAt (matrix : BunchedBimonoidMat) (rowIndex colIndex : Nat) : Nat :=
  bunchedBimonoidNatListGet (bunchedBimonoidRowListGet matrix.entries rowIndex) colIndex

/-- Structural **sum of a `List Nat`** — the contraction accumulator for matrix multiplication.  Propext-clean. -/
def bunchedBimonoidNatListSum : List Nat → Nat
  | [] => 0
  | head :: tail => head + bunchedBimonoidNatListSum tail

/-! ## The three matrix operations (all fully computational on closed inputs, so per-row facts are `rfl`) -/

/-- The **`n x n` identity matrix** (Kronecker delta).  Built canonically via `List.range`, so on closed inputs
it reduces to a ground `entries` list — the unit for `bunchedBimonoidMatMul`. -/
def bunchedBimonoidIdentityMat (dimension : Nat) : BunchedBimonoidMat :=
  { rows := dimension, cols := dimension,
    entries := (List.range dimension).map (fun rowIndex =>
      (List.range dimension).map (fun colIndex => if rowIndex == colIndex then 1 else 0)) }

/-- **Matrix multiplication** `matMul later earlier` = "apply `earlier` then `later`" (`later` after `earlier`).
Result is `later.rows x earlier.cols`; the contraction ranges over `earlier.rows` (the shared inner dimension).
Built canonically via `List.range`, so closed products reduce to ground matrices.  Composability
(`earlier.rows = later.cols`) is EXTRINSIC — as with `vcomp`, a mismatched product is still defined (the recon's
zero-dim tax), which is exactly what makes the associativity identity hold with fixed contraction ranges. -/
def bunchedBimonoidMatMul (later earlier : BunchedBimonoidMat) : BunchedBimonoidMat :=
  { rows := later.rows, cols := earlier.cols,
    entries := (List.range later.rows).map (fun rowIndex =>
      (List.range earlier.cols).map (fun colIndex =>
        bunchedBimonoidNatListSum ((List.range earlier.rows).map (fun contractionIndex =>
          bunchedBimonoidMatEntryAt later rowIndex contractionIndex
            * bunchedBimonoidMatEntryAt earlier contractionIndex colIndex)))) }

/-- The **block-diagonal direct sum** `[[top, 0], [0, bottom]]` — the whiskering primitive: whiskering a 2-cell
by a 1-cell of width `w` conjugates it by the `identityMat w` block.  `topLeft` occupies the upper-left block,
`bottomRight` the lower-right; the off-diagonal blocks are zero (`List.replicate`).  Zero-dimensional blocks are
handled correctly (an empty block contributes no rows/cols). -/
def bunchedBimonoidMatDirectSum (topLeft bottomRight : BunchedBimonoidMat) : BunchedBimonoidMat :=
  { rows := topLeft.rows + bottomRight.rows, cols := topLeft.cols + bottomRight.cols,
    entries :=
      (topLeft.entries.map (fun row => row ++ List.replicate bottomRight.cols 0)) ++
      (bottomRight.entries.map (fun row => List.replicate topLeft.cols 0 ++ row)) }

/-! ## The evaluation motive and the generator matrices -/

/-- The **evaluation motive**: `Unit` at dim 0 (a mode has no matrix), a WIDTH `Nat` at dim 1 (a 1-cell word is
its number of strands), a `BunchedBimonoidMat` at dim 2 (a 2-cell IS a linear map), `Unit` above.  A
`Nat`-recursive `Type` mirroring `boundaryMotive`; matched inside the total evaluation helpers so no
impossible-case discharge (propext-clean). -/
def BunchedBimonoidEvalCarrier : Nat → Type
  | 0 => Unit
  | 1 => Nat
  | 2 => BunchedBimonoidMat
  | _ + 3 => Unit

/-- The **width of a 1-generator** — both colours `a`, `m` are single strands, so every 1-generator has width 1
(the 2-cell labels never appear at label-dimension 0 in a real cell; the constant `1` is a harmless total
default). -/
def bunchedBimonoidGenWidth : BunchedBIGenLabel → Nat := fun _ => 1

/-- The **generator matrix table** — the declared `Mat(N)` map of each 2-cell generator: `mu = [[1,1]]` (fold two
strands to one), `eta = [[]]` (1x0, the empty product), `delta = [[1],[1]]` (copy one strand to two),
`eps = []` (0x1, discard), `sigma = [[0,1],[1,0]]` (swap two strands); both multiplicative generators mirror
their additive namesakes.  The two colour labels default to `identityMat 1` (they never appear at
label-dimension 1 in a real 2-cell; total default).  Full nine-arm split — propext-clean. -/
def bunchedBimonoidGenMatrix : BunchedBIGenLabel → BunchedBimonoidMat
  | .additiveColour => bunchedBimonoidIdentityMat 1
  | .multColour => bunchedBimonoidIdentityMat 1
  | .addMult => { rows := 1, cols := 2, entries := [[1, 1]] }
  | .addUnit => { rows := 1, cols := 0, entries := [[]] }
  | .addComult => { rows := 2, cols := 1, entries := [[1], [1]] }
  | .addCounit => { rows := 0, cols := 1, entries := [] }
  | .addSwap => { rows := 2, cols := 2, entries := [[0, 1], [1, 0]] }
  | .multMult => { rows := 1, cols := 2, entries := [[1, 1]] }
  | .multUnit => { rows := 1, cols := 0, entries := [[]] }

/-! ## The five evaluation helpers (each a total structural `Nat`-case into the dim-dependent motive) -/

/-- Evaluate a **generator**: width at label-dim 0 (a colour), its matrix at label-dim 1 (a 2-cell operation),
`Unit` above.  The declared source / target evaluations are ignored (the matrix is fixed by the label). -/
def bunchedBimonoidEvalGen : (labelDim : Nat) → BunchedBIGenLabel →
    BunchedBimonoidEvalCarrier labelDim → BunchedBimonoidEvalCarrier labelDim →
    BunchedBimonoidEvalCarrier (labelDim + 1)
  | 0, label, _, _ => bunchedBimonoidGenWidth label
  | 1, label, _, _ => bunchedBimonoidGenMatrix label
  | _ + 2, _, _, _ => ()

/-- Evaluate an **identity cell**: the empty word (width 0) at dim 0->1, the identity matrix on the sub-word's
width at dim 1->2, `Unit` above. -/
def bunchedBimonoidEvalId : (d : Nat) → BunchedBimonoidEvalCarrier d → BunchedBimonoidEvalCarrier (d + 1)
  | 0, _ => (0 : Nat)
  | 1, width => bunchedBimonoidIdentityMat width
  | _ + 2, _ => ()

/-- Evaluate a **vertical composite**: width ADDITION at dim 1 (concatenating 1-cell words), matrix
MULTIPLICATION at dim 2 (`vcomp l r` = `r` after `l`, so the right operand is applied first: `matMul r l`),
`Unit` above.  The width arm uses `Nat.add` directly (the `HAdd` typeclass search does not unfold the motive). -/
def bunchedBimonoidEvalVcomp : (d : Nat) →
    BunchedBimonoidEvalCarrier (d + 1) → BunchedBimonoidEvalCarrier (d + 1) →
    BunchedBimonoidEvalCarrier (d + 1)
  | 0, leftWidth, rightWidth => Nat.add leftWidth rightWidth
  | 1, leftMatrix, rightMatrix => bunchedBimonoidMatMul rightMatrix leftMatrix
  | _ + 2, _, _ => ()

/-- Evaluate a **left whisker**: at dim 2 the whiskered cell is conjugated by the whisker's identity block placed
FIRST (`directSum (identityMat whiskerWidth) cellMatrix`); `Unit` above. -/
def bunchedBimonoidEvalWhiskerLeft : (d : Nat) →
    BunchedBimonoidEvalCarrier (d + 1) → BunchedBimonoidEvalCarrier (d + 2) →
    BunchedBimonoidEvalCarrier (d + 2)
  | 0, whiskerWidth, cellMatrix => bunchedBimonoidMatDirectSum (bunchedBimonoidIdentityMat whiskerWidth) cellMatrix
  | _ + 1, _, _ => ()

/-- Evaluate a **right whisker**: at dim 2 the whiskered cell is conjugated by the whisker's identity block placed
LAST (`directSum cellMatrix (identityMat whiskerWidth)`); `Unit` above. -/
def bunchedBimonoidEvalWhiskerRight : (d : Nat) →
    BunchedBimonoidEvalCarrier (d + 2) → BunchedBimonoidEvalCarrier (d + 1) →
    BunchedBimonoidEvalCarrier (d + 2)
  | 0, cellMatrix, whiskerWidth => bunchedBimonoidMatDirectSum cellMatrix (bunchedBimonoidIdentityMat whiskerWidth)
  | _ + 1, _, _ => ()

/-- ★ **The matrix evaluation** `bunchedBimonoidEvalCell : CellExpr dim -> EvalCarrier dim` — the
free-bicommutative-bimonoid functor into `Mat(N)`.  A total structural fold over all six carrier constructors
into the dimension-dependent motive (mirroring `boundarySourceTotal`); the five helpers carry the per-dimension
operations.  Propext-clean (the `List.getD`-free indexers keep the whole fold axiom-free). -/
def bunchedBimonoidEvalCell : {dim : Nat} → CellExpr bunchedBimonoidOmegaComputad dim →
    BunchedBimonoidEvalCarrier dim
  | _, .ofMode _ => ()
  | _, .gen (dim := labelDim) label source target =>
      bunchedBimonoidEvalGen labelDim label (bunchedBimonoidEvalCell source) (bunchedBimonoidEvalCell target)
  | _, .id (dim := d) cell => bunchedBimonoidEvalId d (bunchedBimonoidEvalCell cell)
  | _, .vcomp (dim := d) leftCell rightCell =>
      bunchedBimonoidEvalVcomp d (bunchedBimonoidEvalCell leftCell) (bunchedBimonoidEvalCell rightCell)
  | _, .whiskerLeft (dim := d) whiskerCell cell =>
      bunchedBimonoidEvalWhiskerLeft d (bunchedBimonoidEvalCell whiskerCell) (bunchedBimonoidEvalCell cell)
  | _, .whiskerRight (dim := d) cell whiskerCell =>
      bunchedBimonoidEvalWhiskerRight d (bunchedBimonoidEvalCell cell) (bunchedBimonoidEvalCell whiskerCell)

/-! ## The concrete generator matrices and 1-cell widths (the B1 truth-probe, machine-checked) -/

/-- The **width of a 1-cell word** — the evaluation at dimension 1, read back at the manifest `Nat` type (the
motive `BunchedBimonoidEvalCarrier 1` is definitionally `Nat`; the declared return type pins it so numeral
comparisons elaborate). -/
def bunchedBimonoidWordWidth (cell : CellExpr bunchedBimonoidOmegaComputad 1) : Nat :=
  bunchedBimonoidEvalCell cell

/-- The additive colour `a` has width 1. -/
theorem bunchedBimonoidAdditiveGen_width :
    bunchedBimonoidWordWidth bunchedBimonoidAdditiveGen = 1 := rfl

/-- The word `a.a` has width 2. -/
theorem bunchedBimonoidAaWord_width :
    bunchedBimonoidWordWidth bunchedBimonoidAaWord = 2 := rfl

/-- The identity 1-cell (empty word) has width 0. -/
theorem bunchedBimonoidIdOne_width :
    bunchedBimonoidWordWidth bunchedBimonoidIdOne = 0 := rfl

/-- `mu_a` evaluates to the 1x2 fold matrix `[[1,1]]`. -/
theorem bunchedBimonoidAddMuGen_matrix :
    bunchedBimonoidEvalCell bunchedBimonoidAddMuGen = { rows := 1, cols := 2, entries := [[1, 1]] } := rfl

/-- `delta_a` evaluates to the 2x1 copy matrix `[[1],[1]]`. -/
theorem bunchedBimonoidAddDeltaGen_matrix :
    bunchedBimonoidEvalCell bunchedBimonoidAddDeltaGen = { rows := 2, cols := 1, entries := [[1], [1]] } := rfl

/-- ★★ `sigma_a` evaluates to the 2x2 swap matrix `[[0,1],[1,0]]` — the genuine non-identity braiding. -/
theorem bunchedBimonoidAddSigmaGen_matrix :
    bunchedBimonoidEvalCell bunchedBimonoidAddSigmaGen = { rows := 2, cols := 2, entries := [[0, 1], [1, 0]] } :=
  rfl

/-! ## The 13 RESPECTED rows — both legs share the same matrix (per-row soundness, `rfl`)

Each theorem is the machine-checked statement "the matrix respects this critical row": the two legs evaluate to
the SAME `Mat(N)` map.  These are the balanced critical pairs — the double-operation associativity pentagons, the
root unit/counit balances, the four bialgebra laws (incl. the tamed B1 4-strand delta-of-product-with-swap, both
legs `[[1,1],[1,1]]`), and the three `sigma` laws (commutativity, cocommutativity, involution). -/

/-- monoid-`m` pentagon: both legs share the matrix. -/
theorem bunchedBimonoidMatrixRespectsMultMonadPentagon :
    bunchedBimonoidEvalCell bunchedBimonoidMultMonadPentagonLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidMultMonadPentagonRightLeg := rfl

/-- monoid-`m` rootUnitAssoc: both legs share the matrix. -/
theorem bunchedBimonoidMatrixRespectsMultMonadRootUnitAssoc :
    bunchedBimonoidEvalCell bunchedBimonoidMultMonadRootUnitAssocLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidMultMonadRootUnitAssocRightLeg := rfl

/-- monoid-`a` pentagon: both legs share the matrix. -/
theorem bunchedBimonoidMatrixRespectsAddMonadPentagon :
    bunchedBimonoidEvalCell bunchedBimonoidAddMonadPentagonLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidAddMonadPentagonRightLeg := rfl

/-- monoid-`a` rootUnitAssoc: both legs share the matrix. -/
theorem bunchedBimonoidMatrixRespectsAddMonadRootUnitAssoc :
    bunchedBimonoidEvalCell bunchedBimonoidAddMonadRootUnitAssocLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidAddMonadRootUnitAssocRightLeg := rfl

/-- comonoid-`a` copentagon (coassociativity): both legs share the matrix. -/
theorem bunchedBimonoidMatrixRespectsComonoidCopentagon :
    bunchedBimonoidEvalCell bunchedBimonoidComonoidCopentagonLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidComonoidCopentagonRightLeg := rfl

/-- comonoid-`a` rootCounitCoassoc: both legs share the matrix. -/
theorem bunchedBimonoidMatrixRespectsComonoidRootCounitCoassoc :
    bunchedBimonoidEvalCell bunchedBimonoidComonoidRootCounitCoassocLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidComonoidRootCounitCoassocRightLeg := rfl

/-- ★★ bialgebra B1 (delta-of-product with the middle swap): both legs evaluate to `[[1,1],[1,1]]` — the tamed
4-strand right leg and the two-generator left leg agree as maps (the four-count, by contrast, BREAKS here). -/
theorem bunchedBimonoidMatrixRespectsBialgebraProduct :
    bunchedBimonoidEvalCell bunchedBimonoidBialgebraProductLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidBialgebraProductRightLeg := rfl

/-- bialgebra B2 (counit-of-product): both legs share the matrix (both `0x2`). -/
theorem bunchedBimonoidMatrixRespectsBialgebraCounit :
    bunchedBimonoidEvalCell bunchedBimonoidBialgebraCounitLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidBialgebraCounitRightLeg := rfl

/-- bialgebra B3 (delta-of-unit): both legs share the matrix (both `2x0`). -/
theorem bunchedBimonoidMatrixRespectsBialgebraUnit :
    bunchedBimonoidEvalCell bunchedBimonoidBialgebraUnitLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidBialgebraUnitRightLeg := rfl

/-- bialgebra B4 (the bone): both legs share the matrix (both `0x0`). -/
theorem bunchedBimonoidMatrixRespectsBialgebraBone :
    bunchedBimonoidEvalCell bunchedBimonoidBialgebraBoneLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidBialgebraBoneRightLeg := rfl

/-- ★ commutativity `mu.sigma = mu`: both legs evaluate to `[[1,1]]` (the fold is symmetric). -/
theorem bunchedBimonoidMatrixRespectsCommutativity :
    bunchedBimonoidEvalCell bunchedBimonoidCommutativityLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidCommutativityRightLeg := rfl

/-- ★ cocommutativity `sigma.delta = delta`: both legs evaluate to `[[1],[1]]` (the copy is cosymmetric). -/
theorem bunchedBimonoidMatrixRespectsCocommutativity :
    bunchedBimonoidEvalCell bunchedBimonoidCocommutativityLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidCocommutativityRightLeg := rfl

/-- ★★ sigma-involution `sigma.sigma = id`: both legs evaluate to `identityMat 2` (the swap squares to the
identity, machine-checked as a matrix identity). -/
theorem bunchedBimonoidMatrixRespectsSigmaInvolution :
    bunchedBimonoidEvalCell bunchedBimonoidSigmaInvolutionLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidSigmaInvolutionRightLeg := rfl

/-! ## The 9 BROKEN rows — the two legs are DIFFERENT matrices (`op (x) 1 != 1 (x) op`)

Each theorem machine-separates the two legs of a single-operation whisker-commute critical row: `op |> x` and
`x <| op` evaluate to `op (x) 1` and `1 (x) op`, which are DISTINCT `Mat(N)` maps (they differ at a named entry).
These rows are asserted convertible in the r1 congruence (via `ofRelation`), so the matrix is NOT a model of the
full 22-row congruence — the honest scope boundary.  The separations are `Nat.noConfusion` on a differing entry
(the r1 four-count-separation idiom), zero-axiom. -/

/-- monoid-`m` unitUnit legs are DIFFERENT matrices (`eta (x) 1` vs `1 (x) eta`; entry `(0,0)` is `0` vs `1`). -/
theorem bunchedBimonoidMatrixSeparatesMultMonadUnitUnit :
    bunchedBimonoidEvalCell bunchedBimonoidMultMonadUnitUnitLeftLeg
      ≠ bunchedBimonoidEvalCell bunchedBimonoidMultMonadUnitUnitRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-- monoid-`m` leftUnitAssoc legs are DIFFERENT (`mu (x) 1` vs `1 (x) mu`; entry `(0,1)` is `1` vs `0`). -/
theorem bunchedBimonoidMatrixSeparatesMultMonadLeftUnitAssoc :
    bunchedBimonoidEvalCell bunchedBimonoidMultMonadLeftUnitAssocLeftLeg
      ≠ bunchedBimonoidEvalCell bunchedBimonoidMultMonadLeftUnitAssocRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 1) hmatrix)

/-- monoid-`m` rightUnitAssoc legs are DIFFERENT (`eta (x) 1` vs `1 (x) eta`; entry `(0,0)` is `0` vs `1`). -/
theorem bunchedBimonoidMatrixSeparatesMultMonadRightUnitAssoc :
    bunchedBimonoidEvalCell bunchedBimonoidMultMonadRightUnitAssocLeftLeg
      ≠ bunchedBimonoidEvalCell bunchedBimonoidMultMonadRightUnitAssocRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-- monoid-`a` unitUnit legs are DIFFERENT (`eta (x) 1` vs `1 (x) eta`; entry `(0,0)` is `0` vs `1`). -/
theorem bunchedBimonoidMatrixSeparatesAddMonadUnitUnit :
    bunchedBimonoidEvalCell bunchedBimonoidAddMonadUnitUnitLeftLeg
      ≠ bunchedBimonoidEvalCell bunchedBimonoidAddMonadUnitUnitRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-- monoid-`a` leftUnitAssoc legs are DIFFERENT (`mu (x) 1` vs `1 (x) mu`; entry `(0,1)` is `1` vs `0`). -/
theorem bunchedBimonoidMatrixSeparatesAddMonadLeftUnitAssoc :
    bunchedBimonoidEvalCell bunchedBimonoidAddMonadLeftUnitAssocLeftLeg
      ≠ bunchedBimonoidEvalCell bunchedBimonoidAddMonadLeftUnitAssocRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 1) hmatrix)

/-- monoid-`a` rightUnitAssoc legs are DIFFERENT (`eta (x) 1` vs `1 (x) eta`; entry `(0,0)` is `0` vs `1`). -/
theorem bunchedBimonoidMatrixSeparatesAddMonadRightUnitAssoc :
    bunchedBimonoidEvalCell bunchedBimonoidAddMonadRightUnitAssocLeftLeg
      ≠ bunchedBimonoidEvalCell bunchedBimonoidAddMonadRightUnitAssocRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-- comonoid-`a` counitCounit legs are DIFFERENT (`eps (x) 1` vs `1 (x) eps`; entry `(0,0)` is `0` vs `1`). -/
theorem bunchedBimonoidMatrixSeparatesComonoidCounitCounit :
    bunchedBimonoidEvalCell bunchedBimonoidComonoidCounitCounitLeftLeg
      ≠ bunchedBimonoidEvalCell bunchedBimonoidComonoidCounitCounitRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-- comonoid-`a` leftCounitCoassoc legs are DIFFERENT (`delta (x) 1` vs `1 (x) delta`; entry `(1,0)` is `1` vs
`0`). -/
theorem bunchedBimonoidMatrixSeparatesComonoidLeftCounitCoassoc :
    bunchedBimonoidEvalCell bunchedBimonoidComonoidLeftCounitCoassocLeftLeg
      ≠ bunchedBimonoidEvalCell bunchedBimonoidComonoidLeftCounitCoassocRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 1 0) hmatrix)

/-- comonoid-`a` rightCounitCoassoc legs are DIFFERENT (`eps (x) 1` vs `1 (x) eps`; entry `(0,0)` is `0` vs `1`).
This is the row the truth-probe caught FIRST — the sole `rfl` failure that revealed the 9-row broken class. -/
theorem bunchedBimonoidMatrixSeparatesComonoidRightCounitCoassoc :
    bunchedBimonoidEvalCell bunchedBimonoidComonoidRightCounitCoassocLeftLeg
      ≠ bunchedBimonoidEvalCell bunchedBimonoidComonoidRightCounitCoassocRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-! ## The separator seed — `sigma_a` is not the identity (a MAP-level separation the four-count cannot make) -/

/-- ★★ **`sigma_a != id_{a.a}` at the matrix level.**  The self-braiding evaluates to the swap `[[0,1],[1,0]]`,
the identity 2-cell to `[[1,0],[0,1]]`; entry `(0,0)` is `0` vs `1`.  This UPGRADES the r1 structural
`bunchedBimonoidSwapGen_notIdentity` (a `cellBeq` inequality) to a SEMANTIC map-level separation, and — unlike
the four-count (which reads `(0,0,0,0)` for BOTH) — the matrix genuinely distinguishes them. -/
theorem bunchedBimonoidMatrixSeparatesSwapFromIdentity :
    bunchedBimonoidEvalCell bunchedBimonoidAddSigmaGen
      ≠ bunchedBimonoidEvalCell (CellExpr.id bunchedBimonoidAaWord) :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-! ## B1 non-vacuity probes (the truth-probe `#eval` outputs) -/

#eval bunchedBimonoidEvalCell bunchedBimonoidBialgebraProductLeftLeg
#eval bunchedBimonoidEvalCell bunchedBimonoidBialgebraProductRightLeg
#eval bunchedBimonoidEvalCell bunchedBimonoidAddSigmaGen
#eval bunchedBimonoidEvalCell (CellExpr.id bunchedBimonoidAaWord)
#eval bunchedBimonoidEvalCell bunchedBimonoidComonoidRightCounitCoassocLeftLeg
#eval bunchedBimonoidEvalCell bunchedBimonoidComonoidRightCounitCoassocRightLeg

/-! ## The B1 honesty markers -/

/-- ★ **ESTABLISHED (B1) — the matrix carrier and evaluation are shipped and truth-probed.**  `= true` records
that `bunchedBimonoidEvalCell` sends every 2-cell to a concrete `Mat(N)` matrix (`vcomp` to `matMul`, generators
to their declared matrices, whiskering to identity-block direct-sum with the whisker WIDTH faithfully placed),
convention-pinned by `#eval` and machine-checked on the generator matrices (`mu = [[1,1]]`, `sigma = [[0,1],
[1,0]]`, etc.).  Zero-axiom (the `List.getD`-free indexers keep the fold propext-clean). -/
def fxBunchedBimonoid_matrixCarrierAndEvaluationShipped : Bool := true

/-- ★★ **ESTABLISHED (B1) — the honest per-row soundness partition: 13 respected, 9 broken.**  `= true` records
the truth-probe verdict: the matrix respects EXACTLY 13 of the 22 r1 rows (both pentagons, both rootUnitAssoc,
copentagon, rootCounitCoassoc, the four bialgebra rows, and the three `sigma` laws — each `rfl`), and BREAKS on
the 9 single-operation whisker-commute rows (`op |> x` vs `x <| op` for a lone (co)monoid generator), whose legs
are the DISTINCT maps `op (x) 1` and `1 (x) op` (each machine-separated).  Hence `Mat(N)` models the 13-row
balanced sub-relation but NOT the full r1 congruence — the matrix is strictly finer than the four-count and, so,
breaks on exactly the rows the coarse count survives.  NOT the recon's naive "sound over all 22": the probe
corrected it. -/
def fxBunchedBimonoid_matrixPerRowPartitionThirteenSoundNineBroken : Bool := true

/-- ★★ **ESTABLISHED (B1) — `sigma != id` at the MAP level.**  `= true` records
`bunchedBimonoidMatrixSeparatesSwapFromIdentity`: the swap and the identity 2-cell evaluate to different
matrices, a semantic separation strictly beyond the r1 structural `cellBeq` inequality and strictly beyond the
four-count (which cannot see the difference — both count `(0,0,0,0)`). -/
def fxBunchedBimonoid_matrixSeparatesSwapFromIdentity : Bool := true

/-! # =========================================================================================
    # B2 — THE PER-ROW SOUNDNESS FOLD over the 13 balanced rows + the congruence induction
    # =========================================================================================

★ **The matrix is a sound invariant of the congruence generated by the 13 balanced rows.**  The per-row `rfl`
equalities of B1 are the GENERATING-row soundness; this brick closes them under the congruence — `matMul` /
`directSum` / `identityMat` CONGRUENCE (mere `congrArg` on the evaluation helpers) propagate matrix equality
through every one-hole context, `idCongr`, and the two whiskering-1-cell congruences.  The fold is the exact
`frobMonadOmegaFourCountAbsorbs` shape with the four-tuple invariant replaced by the matrix, over the SUB-relation
`BunchedBimonoidBalancedRow` (the 13 respected r1 rows, NOT the full 22 — the 9 op-commute rows are excluded
because the matrix legitimately separates their legs).

The strict omega-laws (`vcompAssoc` = matMul associativity, the two units = the identity-matrix unit laws,
whisker-functoriality + interchange = block multiplicativity) hold in `Mat(N)` but their PROOFS need the
matrix-algebra kit (associativity via a finite-sum Fubini over `List.range`); that kit — lifting soundness to
`StrictAxiomRel union R13`, the convergent `Mat(N)` normalizer territory — is the honest r3 wall
(`fxBunchedBimonoid_matrixStrictLawExtensionReached = false`).  This brick ships the CONGRUENCE closure over the
13 rows, exercised BOTH ways (a convertible pair shares the matrix; `sigma` is separated from `id`). -/

/-- ★ The **13 balanced critical rows** the matrix RESPECTS — the sub-relation of `BunchedBimonoidCriticalRow`
(both pentagons, both rootUnitAssoc, the copentagon, the rootCounitCoassoc, the four bialgebra rows, and the
three `sigma` laws) over which `Mat(N)` is a sound model.  The 9 op-commute rows are DELIBERATELY absent (their
legs are separated maps).  Each constructor names the same r1 legs. -/
inductive BunchedBimonoidBalancedRow :
    {d : Nat} → CellExpr bunchedBimonoidOmegaComputad d → CellExpr bunchedBimonoidOmegaComputad d → Prop where
  /-- monoid-`m` pentagon. -/
  | multMonadPentagon : BunchedBimonoidBalancedRow bunchedBimonoidMultMonadPentagonLeftLeg
      bunchedBimonoidMultMonadPentagonRightLeg
  /-- monoid-`m` rootUnitAssoc. -/
  | multMonadRootUnitAssoc : BunchedBimonoidBalancedRow bunchedBimonoidMultMonadRootUnitAssocLeftLeg
      bunchedBimonoidMultMonadRootUnitAssocRightLeg
  /-- monoid-`a` pentagon. -/
  | addMonadPentagon : BunchedBimonoidBalancedRow bunchedBimonoidAddMonadPentagonLeftLeg
      bunchedBimonoidAddMonadPentagonRightLeg
  /-- monoid-`a` rootUnitAssoc. -/
  | addMonadRootUnitAssoc : BunchedBimonoidBalancedRow bunchedBimonoidAddMonadRootUnitAssocLeftLeg
      bunchedBimonoidAddMonadRootUnitAssocRightLeg
  /-- comonoid-`a` copentagon. -/
  | comonoidCopentagon : BunchedBimonoidBalancedRow bunchedBimonoidComonoidCopentagonLeftLeg
      bunchedBimonoidComonoidCopentagonRightLeg
  /-- comonoid-`a` rootCounitCoassoc. -/
  | comonoidRootCounitCoassoc : BunchedBimonoidBalancedRow bunchedBimonoidComonoidRootCounitCoassocLeftLeg
      bunchedBimonoidComonoidRootCounitCoassocRightLeg
  /-- bialgebra B1 (delta-of-product with the middle swap). -/
  | bialgebraProduct : BunchedBimonoidBalancedRow bunchedBimonoidBialgebraProductLeftLeg
      bunchedBimonoidBialgebraProductRightLeg
  /-- bialgebra B2 (counit-of-product). -/
  | bialgebraCounit : BunchedBimonoidBalancedRow bunchedBimonoidBialgebraCounitLeftLeg
      bunchedBimonoidBialgebraCounitRightLeg
  /-- bialgebra B3 (delta-of-unit). -/
  | bialgebraUnit : BunchedBimonoidBalancedRow bunchedBimonoidBialgebraUnitLeftLeg
      bunchedBimonoidBialgebraUnitRightLeg
  /-- bialgebra B4 (the bone). -/
  | bialgebraBone : BunchedBimonoidBalancedRow bunchedBimonoidBialgebraBoneLeftLeg
      bunchedBimonoidBialgebraBoneRightLeg
  /-- commutativity `mu.sigma = mu`. -/
  | commutativity : BunchedBimonoidBalancedRow bunchedBimonoidCommutativityLeftLeg
      bunchedBimonoidCommutativityRightLeg
  /-- cocommutativity `sigma.delta = delta`. -/
  | cocommutativity : BunchedBimonoidBalancedRow bunchedBimonoidCocommutativityLeftLeg
      bunchedBimonoidCocommutativityRightLeg
  /-- sigma-involution `sigma.sigma = id`. -/
  | sigmaInvolution : BunchedBimonoidBalancedRow bunchedBimonoidSigmaInvolutionLeftLeg
      bunchedBimonoidSigmaInvolutionRightLeg

/-- The **matrix-equality relation** — two same-dimension cells relate iff they evaluate to the same matrix.  The
target congruence of the soundness fold. -/
def bunchedBimonoidMatrixEq : CellRelOver bunchedBimonoidOmegaComputad :=
  fun {_dim} cellAlpha cellBeta => bunchedBimonoidEvalCell cellAlpha = bunchedBimonoidEvalCell cellBeta

/-- ★★ **THE MATRIX EVALUATION RESPECTS THE BALANCED CONGRUENCE.**  Matrix equality absorbs the idCongr-extended
saturated congruence over `BunchedBimonoidBalancedRow`: each of the 13 rows relates equal-matrix legs (`rfl`),
and every congruence closure is `congrArg` on the corresponding evaluation helper (`matMul` / `directSum` /
`identityMat` congruence).  The Peiffer-invariance datum the least-congruence UP folds — the matrix analogue of
`frobMonadOmegaFourCountAbsorbs`. -/
def bunchedBimonoidMatrixEvalAbsorbs :
    IsSaturatedCongruenceWithId bunchedBimonoidOmegaComputad BunchedBimonoidBalancedRow bunchedBimonoidMatrixEq where
  ofRelation := by intro _dim _cellAlpha _cellBeta row; cases row <;> rfl
  vcompCongrLeft := by
    intro dim _cellAlpha _cellAlpha' cellBeta hconv
    exact congrArg (fun leftMatrix => bunchedBimonoidEvalVcomp dim leftMatrix (bunchedBimonoidEvalCell cellBeta))
      hconv
  vcompCongrRight := by
    intro dim cellAlpha _cellBeta _cellBeta' hconv
    exact congrArg (fun rightMatrix => bunchedBimonoidEvalVcomp dim (bunchedBimonoidEvalCell cellAlpha)
      rightMatrix) hconv
  whiskerLeftCongr := by
    intro dim whiskeringCell _cellBeta _cellBeta' hconv
    exact congrArg (fun cellMatrix => bunchedBimonoidEvalWhiskerLeft dim
      (bunchedBimonoidEvalCell whiskeringCell) cellMatrix) hconv
  whiskerRightCongr := by
    intro dim _cellAlpha _cellAlpha' whiskeringCell hconv
    exact congrArg (fun cellMatrix => bunchedBimonoidEvalWhiskerRight dim cellMatrix
      (bunchedBimonoidEvalCell whiskeringCell)) hconv
  idCongr := by
    intro dim _cellAlpha _cellBeta hconv
    exact congrArg (fun subMatrix => bunchedBimonoidEvalId dim subMatrix) hconv
  whiskerLeftWhiskerCongr := by
    intro dim _whiskerAlpha _whiskerAlpha' innerCell hconv
    exact congrArg (fun whiskerMatrix => bunchedBimonoidEvalWhiskerLeft dim whiskerMatrix
      (bunchedBimonoidEvalCell innerCell)) hconv
  whiskerRightWhiskerCongr := by
    intro dim innerCell _whiskerAlpha _whiskerAlpha' hconv
    exact congrArg (fun whiskerMatrix => bunchedBimonoidEvalWhiskerRight dim
      (bunchedBimonoidEvalCell innerCell) whiskerMatrix) hconv
  refl := by intro _dim _cell; rfl
  symm := by intro _dim _cellAlpha _cellBeta hconv; exact hconv.symm
  trans := by intro _dim _cellAlpha _cellBeta _cellGamma hleft hright; exact hleft.trans hright

/-- ★★ **SOUNDNESS: convertible over the balanced congruence ⟹ equal matrix.**  Any two cells convertible under
the congruence generated by the 13 balanced rows share their `Mat(N)` matrix — the fold of
`bunchedBimonoidMatrixEvalAbsorbs` through the least-congruence UP `SaturatedConvOverWithId.recInto`.
Machine-checked.  (The r3 extension adds the strict omega-laws via the matrix-algebra kit.) -/
theorem bunchedBimonoidMatrixSoundOverBalanced {dim : Nat}
    {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim}
    (conv : SaturatedConvOverWithId bunchedBimonoidOmegaComputad BunchedBimonoidBalancedRow
      cellAlpha cellBeta) :
    bunchedBimonoidEvalCell cellAlpha = bunchedBimonoidEvalCell cellBeta :=
  SaturatedConvOverWithId.recInto bunchedBimonoidMatrixEvalAbsorbs conv

/-! ## Exercised BOTH ways — a convertible pair shares the matrix; `sigma` is separated from `id` -/

/-- The sigma-involution legs are convertible over the balanced congruence (the row fired through `ofRelation`). -/
theorem bunchedBimonoidSigmaInvolutionConvertibleOverBalanced :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad BunchedBimonoidBalancedRow
      bunchedBimonoidSigmaInvolutionLeftLeg bunchedBimonoidSigmaInvolutionRightLeg :=
  SaturatedConvOverWithId.ofRelation BunchedBimonoidBalancedRow.sigmaInvolution

/-- ★ **EXERCISED (convertible ⟹ shared).**  Soundness DERIVES that the two sigma-involution legs share their
matrix (both `identityMat 2`), obtained from the convertibility, not assumed. -/
theorem bunchedBimonoidSigmaInvolutionMatrixSharedOverBalanced :
    bunchedBimonoidEvalCell bunchedBimonoidSigmaInvolutionLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidSigmaInvolutionRightLeg :=
  bunchedBimonoidMatrixSoundOverBalanced bunchedBimonoidSigmaInvolutionConvertibleOverBalanced

/-- ★★ **THE PROOF-CARRYING SEPARATOR.**  `sigma_a` is NOT convertible to `id_{a.a}` over the balanced
congruence — even though that congruence CONTAINS the three `sigma` laws (commutativity, cocommutativity,
involution), the matrix soundness forbids it: were they convertible, soundness would force equal matrices, but
`bunchedBimonoidMatrixSeparatesSwapFromIdentity` shows the swap and the identity differ.  This is the map-level
non-convertibility the four-count could never deliver (it reads `(0,0,0,0)` for both). -/
theorem bunchedBimonoidSwapNotConvertibleToIdentityOverBalanced :
    ¬ SaturatedConvOverWithId bunchedBimonoidOmegaComputad BunchedBimonoidBalancedRow
        bunchedBimonoidAddSigmaGen (CellExpr.id bunchedBimonoidAaWord) :=
  fun conv => bunchedBimonoidMatrixSeparatesSwapFromIdentity (bunchedBimonoidMatrixSoundOverBalanced conv)

/-! ## The B2 honesty markers -/

/-- ★★ **ESTABLISHED (B2) — the matrix is a sound invariant of the 13-row balanced congruence.**  `= true`
records `bunchedBimonoidMatrixSoundOverBalanced`: convertibility over `BunchedBimonoidBalancedRow` (the 13
respected rows closed under the idCongr-extended one-hole congruences) implies equal matrices, folded through the
least-congruence UP from the respects-congruence datum `bunchedBimonoidMatrixEvalAbsorbs`.  Exercised both ways
(`...SigmaInvolutionMatrixSharedOverBalanced`, `...SwapNotConvertibleToIdentityOverBalanced`). -/
def fxBunchedBimonoid_matrixSoundOverBalancedThirteen : Bool := true

/-- ★ **WALL (honest, r3) — the strict-law extension via the matrix-algebra kit is NOT shipped.**  `= false`
records that lifting soundness from `BunchedBimonoidBalancedRow` to `StrictAxiomRel union R13` requires proving
the strict omega-laws in `Mat(N)`: `matMul` associativity (a finite-sum Fubini over `List.range`), the
identity-matrix unit laws, and block multiplicativity (whisker-functoriality + interchange).  These hold in
`Mat(N)` but the PROOFS are the convergent `Mat(N)` normalizer's matrix-algebra kit, DEFERRED to r3 — the same
wall as `fxBunchedBimonoid_additiveConvergentNormalizerReached`. -/
def fxBunchedBimonoid_matrixStrictLawExtensionReached : Bool := false

end FX1Poly.Polygraph.Omega
