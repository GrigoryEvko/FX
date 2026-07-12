import FX1Poly.Polygraph.Homology.AmalgamMayerVietorisComparisonMap

/-! # FX1Poly/Polygraph/Homology/AmalgamBimonoidBialgebraObstruction — the BIMONOID amalgamation
    obstruction in the PROP grading: a degree-1 homology class nontrivial WITHOUT the bialgebra law and
    KILLED by adding it, both instance-level and zero-axiom (TOWER-MV r3, the bimonoid round)

TOWER-MV r1 (`Homology/AmalgamMultiplicationObstruction`) shipped the DOUBLE-MONOID amalgam and its
first machine-checked amalgamation-obstruction cocycle, and in its B6 no-go showed that putting the
comonoid generators `(eps, delta)` as 2-cells over ONE shared endo `t` (the monad/2-cell grading)
makes the `(mu, delta)` cross cofork break `d d = 0` with defect `-2` (`bimonoidNaiveUnionFailsChain
Condition`).  r2 (`Homology/AmalgamMayerVietorisComparisonMap`) named the bimonoid proper as the r3
bill and conjectured a Cartan-Eilenberg BICOMPLEX (`bimonoidBicomplexIsR3Bill`).

THIS module delivers the bimonoid obstruction, with one honest RE-GRADING.  The r1 B6 wall is a
carrier artefact: the shipped `WalkerPresentationCarrier` is a MONOID-WORD carrier over a SINGLE
object whose `d1` is HARDCODED to the all-zero loop row (`computeBoundaryDimZero`) — every endo
1-generator is a loop with zero boundary.  A bimonoid's generators `eta 0->1`, `mu 2->1`, `eps 1->0`,
`delta 1->2` have NONZERO arity displacement, so they are not loops and cannot be 1-generators of the
walker carrier.  We therefore extend the grading ADDITIVELY to a PROP grading: `eta, mu, eps, delta`
become 1-GENERATORS carrying `(sourceArity, targetArity)`, so `C0 = ZZ` (one object), `C1 = ZZ^4`, and
`d1` is the arity-difference row `[+1, -1, -1, +1]` — which is EXACTLY r1's B6 literal
`bimonoidBoundaryOfDimOne`, re-graded from the (refuted) `d2` grading to `d1`.  The relations move to
`C2`.  In this carrier the bimonoid-without-law IS a genuine chain complex (`d1 . d2 = 0` on every
column), so the r1 B6 defect dissolves under re-grading (no contradiction: r1 B6's `-2` is a fact of a
DIFFERENT carrier — the walker/2-cell grading — and stays true).

## What is PROVED here (all instance-level, all zero-axiom)

  * **B1 — the bunched bimonoid presentation and its complex.**  `d1 = [[1, -1, -1, 1]]` (arity
    displacement; the re-graded r1 literal) and `d2 (without law) : ZZ^6 -> ZZ^4` (the six relations
    `assoc_mu, lunit, runit, coassoc, lcounit, rcounit`); `d1 . d2 = 0` on every column
    (`bimonoidWithoutLawIsChainComplex`) — a genuine chain complex.
  * **B2 — the with-law complex and the two-complex comparison.**  `d2 (with law) : ZZ^7 -> ZZ^4` adds
    the bialgebra column `delta . mu = (mu | mu) . sigma . (delta | delta)`, whose boundary is
    `[0, -1, 0, -1] = -(mu + delta)`; `d1 . d2with = 0` too.  Off unit-only Smith normal forms:
    `rank d1 = 1`, `rank d2without = 2`, `rank d2with = 3`, so the degree-1 homology free rank
    `= (C1 - rank d1) - rank d2 = (4 - 1) - rank d2` is `1` WITHOUT the law and `0` WITH it; no torsion
    either way.
  * **B3 — the probe-decided theorem.**  The class `[mu + delta] = [0, 1, 0, 1]` is a 1-cycle
    (`d1 . class = 0`); WITHOUT the law it ESCAPES the integer span of the six relation boundaries
    (detected by the relative 1-cocycle `phi = eta* - mu* = [1, -1, 0, 0]`, which annihilates every
    relation boundary yet evaluates `-1` on the class — the exact mirror of r1's `phi`), so it is
    NONTRIVIAL in `H1`; WITH the law it becomes a boundary (`class = -(bialgebra column)`), so it dies.
    Each part alone (`monoid` = `(eta, mu)`, `comonoid` = `(eps, delta)`) has `H1 = 0`, so the class is
    genuinely CROSS.

## Honest scoping (READ THIS — the honesty law)

  * **A RE-GRADING, not a refutation.**  The killer hypothesis (nontrivial-without, killed-by-law) is
    CONFIRMED.  The only correction is the DEGREE: the class lives at `H1`, not `H2`, because a
    bimonoid's generators are 1-cells (morphisms of a PROP), where a monad's `mu`/`eta` were 2-cells.
    No bicomplex is needed; a single complex suffices.
  * **The r2 bicomplex marker is NOT flipped.**  `bimonoidBicomplexIsR3Bill` (r2) conjectured a
    Cartan-Eilenberg bicomplex.  The PROP re-grading resolves the obstruction in a SINGLE complex; per
    the flip law that marker stays as it is (its bicomplex bill is not what r3 delivers), and the
    bicomplex remains an honest heavier alternative.  r3 ships NEW markers only.
  * **No contradiction with r1 B6.**  `bimonoidNaiveUnionFailsChainCondition` (`d d = -2`) is the
    walker/2-cell grading and stays true; the PROP grading is a different carrier with a different `d1`.
  * **The cocycle stays RELATIVE.**  `phi` is a cocycle RELATIVE to the (empty-of-cross) relation
    subcomplex — it annihilates the six relation boundaries and detects the class; no absolute-cocycle
    claim is made.
  * **INSTANCE-level.**  Every statement is decided on this bimonoid INSTANCE, not the general
    polygraphic theorem (`Bool` markers only for the forward direction).
  * **NOT an embedding / monoid-homology claim.**  This is the homology of the ABELIANIZED PROP
    presentation as-presented; the monoid amalgam need not embed the parts (Howie 1962), and nothing
    here asserts a monoid-homology identity.  The cross critical-pair set of the monoid vs comonoid
    alphabets is EMPTY without the law (disjoint alphabets), so the obstruction is forced to the
    generator level (`C1`), not a `C3` cross 3-cell.

## The literature anchor (fetched)

  * Lafont, *Towards an Algebraic Theory of Boolean Circuits* (JPAA 184, 2003): the bimonoid
    generators are exactly `tau, delta, epsilon, mu, eta`, with the bialgebra relation
    `delta . mu = (mu | mu) . (id | tau | id) . (delta | delta)`; the oriented system is CANONICAL, and
    that relation is the oriented rule resolving the `mu`/`delta` critical peak.  Lack, *Composing PROPs*
    (TAC 13, 2004): the same law is the Beck distributive law composing the comonoid and monoid PROPs.
    The HOMOLOGICAL reading of the compatibility law as an obstruction class (this module) is an
    ORIGINAL framing, unattested in the fetched literature.

## The r4 bill (NAMED, NOT flipped)

  * the Mayer-Vietoris LONG EXACT SEQUENCE for the bimonoid amalgam and the homology-level connecting
    map (the LES packaging);
  * the general CFND-5 FAILURE-CERTIFICATE interface that WP-AMALG-3 consumes;
  * the full four-law bialgebra (all four compatibility laws map onto the same `H1` generator, so
    `rank d2` saturates at 3 — a corollary);
  * the decidedness / completeness of the PROP critical-pair set (Lafont's coherence: `C3` is empty
    until the law, Lafont-complete after).

## Zero-axiom design decisions

  * Ships `IntMatrix` literals + unimodular Smith certificates only (the r1 B5 / r2 style); NO new
    generic presentation carrier (the walker carrier cannot host a comonoid; a generic PROP carrier is
    deferred to r4/r5).
  * Rank/exactness facts read off unit-only Smith normal forms via `smithRankWithin` (the r2 propext
    dodge); the escape-over-all-integer-combinations upgrade reuses the r1 Fubini / distributivity kit
    (`sumOverIndicesSwap`, `sumOverIndicesLeftDistrib`, `sumOverIndicesCongrEverywhere`,
    `sumOverIndicesZeroWithinBound`) and the repo integer kit (`intMulAssoc`, `intMulComm`, `intMulZero`)
    BY IMPORT, never redeclared (the umbrella duplicate-global trap).
  * Out-of-range indices are refuted by the shipped `columnIndexOutOfRangeAbsurd` peel; `decide`
    appears only on literal off-diagonal / nonnegativity checks and on `(-1 : Int) = 0`, never on a
    Smith-driver expression.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/AmalgamBimonoidBialgebraObstruction.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra
open FX1Poly.Polygraph.Steiner

/-! ## B1 — the bunched bimonoid presentation and its (without-law) chain complex

The PROP-graded bimonoid over ONE shared object.  `C0 = ZZ` (the object), `C1 = ZZ^4` with the four
1-generators ordered `[eta, mu, eps, delta]`, and `C2 = ZZ^6` with the six relations ordered
`[assoc_mu, lunit, runit, coassoc, lcounit, rcounit]`.  Each relation boundary is the abelianized
`(one side) - (other side)` in the generator basis. -/

/-- `d1 : C1 = ZZ^4 -> C0 = ZZ`, the arity displacement `(target arity) - (source arity)` of each
1-generator: `eta 0->1` is `+1`, `mu 2->1` is `-1`, `eps 1->0` is `-1`, `delta 1->2` is `+1`.  This is
EXACTLY r1's B6 literal `bimonoidBoundaryOfDimOne`, re-graded from the refuted `d2` grading to `d1`. -/
def bimonoidArityBoundary : IntMatrix := ⟨[[1, -1, -1, 1]]⟩

/-- **The re-grading is literal** — the r3 PROP `d1` is r1's B6 `bimonoidBoundaryOfDimOne` verbatim,
regraded from `d2` to `d1`.  The r1 defect (`d d = -2` in the walker/2-cell grading) and this
chain-complex (in the PROP grading) are the SAME matrix read in two different carriers. -/
theorem bimonoidArityBoundaryIsR1Regrade :
    bimonoidArityBoundary = bimonoidBoundaryOfDimOne := rfl

/-- `d2 (without the bialgebra law) : C2 = ZZ^6 -> C1 = ZZ^4`.  Columns
`[assoc_mu, lunit, runit, coassoc, lcounit, rcounit]`; rows `[eta, mu, eps, delta]`.  `assoc_mu` and
`coassoc` are homogeneous (`[0,0,0,0]`); `lunit`/`runit` are `{mu, eta}` vs `id = [1,1,0,0]`;
`lcounit`/`rcounit` are `{eps, delta}` vs `id = [0,0,1,1]`.  The monoid alphabet `{eta, mu}` and the
comonoid alphabet `{eps, delta}` are DISJOINT here — no cross column. -/
def bimonoidRelationBoundaryWithoutLaw : IntMatrix :=
  ⟨[ [0, 1, 1, 0, 0, 0]
   , [0, 1, 1, 0, 0, 0]
   , [0, 0, 0, 0, 1, 1]
   , [0, 0, 0, 0, 1, 1] ]⟩

-- Committed census pins (statistics = named defs + kernel #eval):
--   C0 = 1, C1 = 4, C2(without) = 6.
#eval bimonoidArityBoundary.rows                     -- [[1, -1, -1, 1]]
#eval bimonoidRelationBoundaryWithoutLaw.rows        -- the 4 x 6 relation boundary

/-- ★ **The bunched bimonoid (without the bialgebra law) IS a chain complex** — `d1 . d2 = 0` on every
one of the six relation columns (per-column `rfl` over the shipped `comparisonProductEntry`; the
out-of-range peel reuses the shipped `columnIndexOutOfRangeAbsurd`).  Unlike the r1 B6 walker/2-cell
grading (defect `-2`), the PROP grading closes `d d = 0` with no bialgebra law. -/
theorem bimonoidWithoutLawIsChainComplex :
    ∀ colIndex, colIndex < 6 →
      comparisonProductEntry bimonoidArityBoundary bimonoidRelationBoundaryWithoutLaw 4 0 colIndex = 0
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | _ + 6, colBound => columnIndexOutOfRangeAbsurd _ 6 colBound

/-! ## B2 — the with-law complex and the two-complex Smith comparison

Adding the bialgebra law `delta . mu = (mu | mu) . sigma . (delta | delta)` as the seventh relation.
Its LHS is `{mu, delta}`, its RHS `{mu:2, delta:2}`, so its boundary is `{mu:-1, delta:-1} =
[0, -1, 0, -1] = -(mu + delta)`.  The with-law complex is still a chain complex; the ONLY thing that
changes between the two complexes is `rank d2`, which rises from `2` to `3` because the bialgebra
column supplies the one missing independent boundary — the class generator. -/

/-- The bialgebra-law relation boundary column `[0, -1, 0, -1] = -(mu + delta)` in `C1 = ZZ^4`. -/
def bimonoidBialgebraLawColumn : IntMatrix := ⟨[[0], [-1], [0], [-1]]⟩

/-- `d2 (with the bialgebra law) : C2 = ZZ^7 -> C1 = ZZ^4` — the six without-law columns plus the
seventh bialgebra column `[0, -1, 0, -1]`. -/
def bimonoidRelationBoundaryWithLaw : IntMatrix :=
  ⟨[ [0, 1, 1, 0, 0, 0, 0]
   , [0, 1, 1, 0, 0, 0, -1]
   , [0, 0, 0, 0, 1, 1, 0]
   , [0, 0, 0, 0, 1, 1, -1] ]⟩

-- Committed census pins:  C2(with) = 7, and the bialgebra column is the last with-law column.
#eval bimonoidRelationBoundaryWithLaw.rows            -- the 4 x 7 relation boundary
#eval bimonoidBialgebraLawColumn.rows                 -- [[0], [-1], [0], [-1]]

/-- **The bialgebra column is the seventh with-law relation boundary** — the added law's boundary is
exactly `-(mu + delta)` (`rfl` per generator; the out-of-range peel reuses the shipped helper). -/
theorem bimonoidBialgebraColumnIsLastWithLawColumn :
    ∀ generatorIndex, generatorIndex < 4 →
      bimonoidRelationBoundaryWithLaw.entryAt generatorIndex 6
        = bimonoidBialgebraLawColumn.entryAt generatorIndex 0
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | _ + 4, rowBound => columnIndexOutOfRangeAbsurd _ 4 rowBound

/-- ★ **The with-law bimonoid IS a chain complex** — `d1 . d2with = 0` on every one of the seven
relation columns, including the bialgebra column (`d1 . [0,-1,0,-1] = (-1)(-1) + 1(-1) = 0`). -/
theorem bimonoidWithLawIsChainComplex :
    ∀ colIndex, colIndex < 7 →
      comparisonProductEntry bimonoidArityBoundary bimonoidRelationBoundaryWithLaw 4 0 colIndex = 0
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | _ + 7, colBound => columnIndexOutOfRangeAbsurd _ 7 colBound

/-! ### The unimodular Smith reductions (unit-only normal forms) -/

/-- The `d1` reduction certificate `[[1, -1, -1, 1]]` -> `[[1, 0, 0, 0]]` (clear columns 1,2,3 by
`col += -+ col0`). -/
def bimonoidArityBoundarySmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations :=
      [ .columnOperation (.addColumnMultiple 0 1 1)
      , .columnOperation (.addColumnMultiple 0 2 1)
      , .columnOperation (.addColumnMultiple 0 3 (-1)) ] }

/-- The Smith normal form of `d1` — the literal `[[1, 0, 0, 0]]` (rank 1, unit factor). -/
def bimonoidAritySmithNormalForm : IntMatrix := ⟨[[1, 0, 0, 0]]⟩

/-- **The `d1` certificate produces its Smith normal form** — `rfl` bridge. -/
theorem bimonoidArityCertificateProducesSmithNormalForm :
    bimonoidArityBoundary.applyOperations bimonoidArityBoundarySmithCertificate.operations
      = bimonoidAritySmithNormalForm := rfl

/-- **`d1` reduces to Smith normal form** — rank 1 within the `1 x 4` window, unit factor. -/
theorem bimonoidArityBoundaryReducesToSmith :
    bimonoidArityBoundarySmithCertificate.reducesToSmithForm bimonoidArityBoundary 1 4 :=
  show bimonoidAritySmithNormalForm.IsSmithNormalFormWithin 1 4 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 1 → ∀ colIndex, colIndex < 4 →
          rowIndex ≠ colIndex → bimonoidAritySmithNormalForm.entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isPositionBelow)) }

/-- The `d2without` reduction certificate `-> diag(1, 1, 0, 0)`: two unit pivots cleared column-and-row
(the monoid pivot from `lunit`, the comonoid pivot from `lcounit`). -/
def bimonoidWithoutLawSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations :=
      [ .columnOperation (.swapColumns 0 1)
      , .rowOperation (.addRowMultiple 0 1 (-1))
      , .columnOperation (.addColumnMultiple 0 2 (-1))
      , .rowOperation (.addRowMultiple 2 1 1)
      , .rowOperation (.addRowMultiple 1 2 (-1))
      , .rowOperation (.addRowMultiple 1 3 (-1))
      , .columnOperation (.swapColumns 1 4)
      , .columnOperation (.addColumnMultiple 1 5 (-1)) ] }

/-- The Smith normal form of `d2without` — the literal `diag(1, 1, 0, 0)` (`4 x 6`), rank 2. -/
def bimonoidWithoutLawSmithNormalForm : IntMatrix :=
  ⟨[ [1, 0, 0, 0, 0, 0]
   , [0, 1, 0, 0, 0, 0]
   , [0, 0, 0, 0, 0, 0]
   , [0, 0, 0, 0, 0, 0] ]⟩

/-- **The `d2without` certificate produces its Smith normal form** — `rfl` bridge. -/
theorem bimonoidWithoutLawCertificateProducesSmithNormalForm :
    bimonoidRelationBoundaryWithoutLaw.applyOperations bimonoidWithoutLawSmithCertificate.operations
      = bimonoidWithoutLawSmithNormalForm := rfl

/-- **`d2without` reduces to `diag(1, 1, 0, 0)` within its `4 x 6` window** — rank 2, all invariant
factors the unit `1` (no torsion). -/
theorem bimonoidWithoutLawReducesToSmith :
    bimonoidWithoutLawSmithCertificate.reducesToSmithForm bimonoidRelationBoundaryWithoutLaw 4 6 :=
  show bimonoidWithoutLawSmithNormalForm.IsSmithNormalFormWithin 4 6 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 4 → ∀ colIndex, colIndex < 6 →
          rowIndex ≠ colIndex →
          bimonoidWithoutLawSmithNormalForm.entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨1, rfl⟩
      | 1, _ => ⟨0, rfl⟩
      | 2, _ => ⟨0, rfl⟩
      | _ + 3, isBeyond =>
          Nat.noConfusion (natEqZeroOfLeZero
            (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyond))))) }

/-- The `d2with` reduction certificate `-> diag(1, 1, 1, 0)`: three unit pivots, the THIRD driven by
the bialgebra column (its `-1` at `mu`/`delta` becomes the third pivot after column threading). -/
def bimonoidWithLawSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations :=
      [ .columnOperation (.swapColumns 0 1)
      , .rowOperation (.addRowMultiple 0 1 (-1))
      , .columnOperation (.addColumnMultiple 0 2 (-1))
      , .columnOperation (.swapColumns 1 4)
      , .rowOperation (.addRowMultiple 2 1 1)
      , .rowOperation (.addRowMultiple 1 2 (-1))
      , .rowOperation (.addRowMultiple 1 3 (-1))
      , .columnOperation (.addColumnMultiple 1 5 (-1))
      , .columnOperation (.addColumnMultiple 1 6 1)
      , .columnOperation (.swapColumns 2 6) ] }

/-- The Smith normal form of `d2with` — the literal `diag(1, 1, 1, 0)` (`4 x 7`), rank 3. -/
def bimonoidWithLawSmithNormalForm : IntMatrix :=
  ⟨[ [1, 0, 0, 0, 0, 0, 0]
   , [0, 1, 0, 0, 0, 0, 0]
   , [0, 0, 1, 0, 0, 0, 0]
   , [0, 0, 0, 0, 0, 0, 0] ]⟩

/-- **The `d2with` certificate produces its Smith normal form** — `rfl` bridge. -/
theorem bimonoidWithLawCertificateProducesSmithNormalForm :
    bimonoidRelationBoundaryWithLaw.applyOperations bimonoidWithLawSmithCertificate.operations
      = bimonoidWithLawSmithNormalForm := rfl

/-- **`d2with` reduces to `diag(1, 1, 1, 0)` within its `4 x 7` window** — rank 3, all invariant
factors the unit `1` (no torsion).  The rank rises to 3 precisely because the bialgebra column adds the
one missing independent boundary. -/
theorem bimonoidWithLawReducesToSmith :
    bimonoidWithLawSmithCertificate.reducesToSmithForm bimonoidRelationBoundaryWithLaw 4 7 :=
  show bimonoidWithLawSmithNormalForm.IsSmithNormalFormWithin 4 7 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 4 → ∀ colIndex, colIndex < 7 →
          rowIndex ≠ colIndex →
          bimonoidWithLawSmithNormalForm.entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨1, rfl⟩
      | 1, _ => ⟨1, rfl⟩
      | 2, _ => ⟨0, rfl⟩
      | _ + 3, isBeyond =>
          Nat.noConfusion (natEqZeroOfLeZero
            (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyond))))) }

/-! ### The rank + degree-1 homology read-offs (the comparison table) -/

#eval smithRankWithin bimonoidAritySmithNormalForm 1        -- 1  (rank d1)
#eval smithRankWithin bimonoidWithoutLawSmithNormalForm 4   -- 2  (rank d2 without)
#eval smithRankWithin bimonoidWithLawSmithNormalForm 4      -- 3  (rank d2 with)

/-- `rank(d1) = 1` — one nonzero diagonal entry in the `1 x 4` SNF window. -/
theorem bimonoidArityRank : smithRankWithin bimonoidAritySmithNormalForm 1 = 1 := rfl

/-- `rank(d2without) = 2` — two nonzero diagonal entries in the `4 x 6` SNF window. -/
theorem bimonoidWithoutLawRank : smithRankWithin bimonoidWithoutLawSmithNormalForm 4 = 2 := rfl

/-- `rank(d2with) = 3` — three nonzero diagonal entries in the `4 x 7` SNF window (the bialgebra
column supplies the third). -/
theorem bimonoidWithLawRank : smithRankWithin bimonoidWithLawSmithNormalForm 4 = 3 := rfl

/-- The degree-1 homology free rank WITHOUT the law: `(C1 - rank d1) - rank d2without =
(4 - 1) - 2 = 1`. -/
def bimonoidWithoutLawDegreeOneHomologyFreeRank : Nat :=
  (4 - smithRankWithin bimonoidAritySmithNormalForm 1)
    - smithRankWithin bimonoidWithoutLawSmithNormalForm 4

/-- **`H1(without law)` has free rank `1`** — the class survives (`= ZZ`).  By `rfl` on the `Nat`
literals. -/
theorem bimonoidWithoutLawDegreeOneHomologyFreeRankIsOne :
    bimonoidWithoutLawDegreeOneHomologyFreeRank = 1 := rfl

/-- The degree-1 homology free rank WITH the law: `(C1 - rank d1) - rank d2with = (4 - 1) - 3 = 0`. -/
def bimonoidWithLawDegreeOneHomologyFreeRank : Nat :=
  (4 - smithRankWithin bimonoidAritySmithNormalForm 1)
    - smithRankWithin bimonoidWithLawSmithNormalForm 4

/-- **`H1(with law) = 0`** — the class is killed.  By `rfl` on the `Nat` literals. -/
theorem bimonoidWithLawDegreeOneHomologyFreeRankIsZero :
    bimonoidWithLawDegreeOneHomologyFreeRank = 0 := rfl

/-- **No `H1` torsion WITHOUT the law** — `d2without` SNF is `diag(1, 1, 0, 0)`, unit factors. -/
theorem bimonoidWithoutLawHasNoTorsion :
    hasNoSmithTorsionWithin bimonoidWithoutLawSmithNormalForm 4 :=
  ⟨⟨⟨⟨True.intro, Or.inr rfl⟩, Or.inr rfl⟩, Or.inl rfl⟩, Or.inl rfl⟩

/-- **No `H1` torsion WITH the law** — `d2with` SNF is `diag(1, 1, 1, 0)`, unit factors. -/
theorem bimonoidWithLawHasNoTorsion : hasNoSmithTorsionWithin bimonoidWithLawSmithNormalForm 4 :=
  ⟨⟨⟨⟨True.intro, Or.inr rfl⟩, Or.inr rfl⟩, Or.inr rfl⟩, Or.inl rfl⟩

/-- ★ **The two-complex comparison table** — the whole degree-1 census off the unit-only Smith normal
forms: `rank d1 = 1`; `rank d2without = 2`, `rank d2with = 3`; `H1(without) = ZZ` (free rank 1),
`H1(with) = 0`; no torsion either way.  The single number that changes is `rank d2` (2 -> 3), driven by
the bialgebra column. -/
def BimonoidTwoComplexComparisonStatement : Prop :=
  smithRankWithin bimonoidAritySmithNormalForm 1 = 1 ∧
  smithRankWithin bimonoidWithoutLawSmithNormalForm 4 = 2 ∧
  smithRankWithin bimonoidWithLawSmithNormalForm 4 = 3 ∧
  bimonoidWithoutLawDegreeOneHomologyFreeRank = 1 ∧
  bimonoidWithLawDegreeOneHomologyFreeRank = 0 ∧
  hasNoSmithTorsionWithin bimonoidWithoutLawSmithNormalForm 4 ∧
  hasNoSmithTorsionWithin bimonoidWithLawSmithNormalForm 4

/-- ★★ **The comparison table is DECIDED** — every entry proved off the kernel-checked Smith normal
forms. -/
theorem bimonoidTwoComplexComparison : BimonoidTwoComplexComparisonStatement :=
  ⟨bimonoidArityRank, bimonoidWithoutLawRank, bimonoidWithLawRank,
   bimonoidWithoutLawDegreeOneHomologyFreeRankIsOne, bimonoidWithLawDegreeOneHomologyFreeRankIsZero,
   bimonoidWithoutLawHasNoTorsion, bimonoidWithLawHasNoTorsion⟩

end FX1Poly.Polygraph.Homology
