import FX1Poly.Polygraph.Omega.SteinerFoundation.AugmentedDirectedComplex
import FX1Poly.ComputerAlgebra.Number.NatEuclideanDivision
import FX1Poly.Polygraph.Homology.WalkerChainComplex

/-! # FX1Poly/Polygraph/Homology/InvolutionChainComplex — the polygraphic chain complex of the
    DECIDED walking involution, with machine-checked `d d = 0`, its Smith-normal boundaries, and
    the kernel-checked homology `H1(walking involution) = ZZ/2` (the FIRST TORSION walker homology)
    and `H2(walking involution) = 0` (H2-WALKERS r1, #2138)

The walking involution's presentation (`Omega/InvolutionDemonstrator`: one object `involutionPoint`,
one endo 1-generator `involutionSGen` — words `s^n` — and exactly one rewrite 2-generator
`involutionRhoGen : s.s ⟹ id`) is CONVERGENT and DECIDED at HEAD (`Omega/InvolutionDecision`
`fxInvolution_hasOneCellWordProblemDecided := true`).  The unit laws `(id)s ~ s`, `s(id) ~ s` are
STRICT STRUCTURAL AXIOMS (`StrictAxiomRel.vcompUnitLeft/Right`), NOT presentation rules — so the
presentation is `<s | s.s ⟹ id>`: ONE 1-generator, ONE rule, no unit rules.  Because the presentation
is a FINITE loop-free polygraph, its abelianization is a finite chain complex of free `ZZ`-modules and
homology is exact integer linear algebra (Smith normal form over `ZZ`), exactly as for the walking
monad (`Homology/WalkerChainComplex`, #2136), which this module reuses wholesale.

This module builds that chain complex by REUSING the shipped augmented-directed-complex carrier
(`Steiner/AugmentedDirectedComplex`) and the walking-monad template's Smith read-off machinery
(`smithRankWithin`, `hasNoSmithTorsionWithin`).  It adds ONE new shared helper —
`smithInvariantFactorsWithin`, a torsion EXTRACTOR (the monad only needed `hasNoSmithTorsionWithin`,
a torsion ABSENCE checker) — because the involution has the first NON-unit invariant factor.

## The arithmetic (compute first, state after)

Abelianize (target − source convention, matching `WalkerChainComplex`).  `basisCount : 0..3 ↦ 1`,
`_ + 4 ↦ 0` (one object, one 1-generator `s`, one rule `rho`, one critical pair `sss`).

  * **`d1 : C1 → C0`** — `s : point → point` is a LOOP, `[point] − [point] = 0`, the `1 × 1` `[[0]]`.
  * **`d2 : C2 → C1`** — `rho : s.s ⟹ id`: target `id ↦ 0·[s]`, source `s.s ↦ 2·[s]`, so
    `d2(rho) = 0 − 2 = −2`, the `1 × 1` `[[-2]]`.  ★ the first NON-UNIT boundary entry.
  * **`d3 : C3 → C2`** — the sole critical pair `sss` (`(ss)s → (id)s = s` vs `s(ss) → s(id) = s`):
    both legs fire `rho` once, `1 − 1 = 0`, the `1 × 1` `[[0]]`.

Smith normal forms: `SNF(d1) = [[0]]` (rank 0), `SNF(d2) = [[2]]` (rank 1, invariant factor **2** —
the first torsion), `SNF(d3) = [[0]]` (rank 0).

  * ★★ **`H1 = ker d1 / im d2`**: `d1 = 0 ⟹ ker d1 = ZZ`; `im d2 = 2·ZZ`.  Free rank
    `nullity(d1) − rank(d2) = 1 − 1 = 0`; the within-rank invariant factor of `d2` is `2 > 1`, so
    `H1 = ZZ/2` — the FIRST torsion walker homology.  This is exactly the abelianization of
    `⟨s | s² = 1⟩ = ZZ/2`.
  * **`H2 = ker d2 / im d3`**: `d2` is `x ↦ −2x`, INJECTIVE over `ZZ`, so `ker d2 = 0`; `im d3 = 0`.
    Free rank `nullity(d2) − rank(d3) = 0 − 0 = 0`, no torsion — `H2 = 0`.

## Honesty note

For the involution `d d = 0` holds because **`d1 = 0` and `d3 = 0`** — every consecutive composition
has a vanishing factor.  This is NOT the walking monad's genuine nonzero-×-nonzero cancellation; it is
degenerate-by-zero-factor.  The complex is non-trivial nonetheless: `d2 = [[-2]] ≠ 0` and its torsion
carry the entire homological content (`involutionBoundaryDimOneIsNonzero`).

## Zero-axiom design decisions

  * The carrier is the shipped `AugmentedDirectedComplex`; the walker adds only `Nat`-valued basis
    counts and `IntMatrix` literals — every match stays on non-indexed inductives.
  * `d d = 0` is DECIDED on the boundary LITERALS: each in-range scalar identity closes by `rfl`,
    each out-of-range index by the propext-clean peel `Nat.noConfusion (natEqZeroOfLeZero
    (natLeOfSuccLeSucc ..))`.
  * The Smith handoff ships EXPLICIT unimodular reduction certificates checked propext-cleanly
    against the literal Smith normal forms — no dependence on any Smith driver.
  * `smithInvariantFactorsWithin` mirrors the shipped `smithRankWithin`'s `if diag = 0` on `Int`
    literals, so the `= [2]` fingerprint of `ZZ/2` closes by `rfl`.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/InvolutionChainComplex.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra
open FX1Poly.Polygraph.Steiner

/-! ## B1 — the presentation data, the boundary literals, and `d d = 0` -/

/-- The per-dimension basis counts of the walking-involution chain complex: `C0 = ZZ` (the object
`involutionPoint`), `C1 = ZZ` (the endo 1-generator `s`), `C2 = ZZ` (the single rule `rho`),
`C3 = ZZ` (the single critical pair `sss`), and nothing above degree 3. -/
def involutionBasisCount : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | _ + 4 => 0

/-! ### The single critical pair (systematic overlap sweep, recorded as DATA)

The presentation has ONE rule `R : s.s ⟹ id` over the free monoid on one letter `s`.  Overlaps of the
lhs `s²` with `s²` are classified by overlap WIDTH:

  * **width 2** (`s² = s²`): identical redex — the trivial ROOT-SELF overlap, EXCLUDED (the monad
    discipline's root-self exclusion).
  * **width 1** (suffix-`s` = prefix-`s`): the word `sss`.  Front redex `(ss)s → (id)s = s`; back
    redex `s(ss) → s(id) = s`.  Joinable at `s`.  ★ the SOLE genuine critical pair.
  * **width 0** (`ssss`, disjoint redexes): an orthogonal diamond — NOT a critical pair.

Systematic cell count: 1 ordered rule-pair × {width 1, width 2} = 2 cells; **1 genuine** after
excluding the trivial self-overlap.  Encoded below as `allInvolutionCriticalPairs` +
`involutionCriticalPairCountIsOne` + `allInvolutionCriticalPairsExhaustive` — the table IS the
certificate, never prose-counted. -/

/-- The single Squier critical pair of the walking-involution presentation: the width-1 overlap
`sss` of the rule `s.s ⟹ id` with itself. -/
inductive InvolutionCriticalPair
  /-- The width-1 self-overlap `sss`: front leg `(ss)s → s`, back leg `s(ss) → s`. -/
  | sss

/-- The complete enumeration of the walking-involution critical pairs — ONE, listed. -/
def allInvolutionCriticalPairs : List InvolutionCriticalPair := [.sss]

/-- ★ **The critical-pair count is exactly ONE** — kernel-checked (`rfl`), not prose. -/
theorem involutionCriticalPairCountIsOne : allInvolutionCriticalPairs.length = 1 := rfl

/-- ★ **The enumeration is EXHAUSTIVE** — the sole `InvolutionCriticalPair` constructor appears in
`allInvolutionCriticalPairs` (a missing constructor would make this non-exhaustive and fail to
compile).  With `involutionCriticalPairCountIsOne` this kernel-checks the critical-pair set is
EXACTLY `sss`. -/
theorem allInvolutionCriticalPairsExhaustive :
    ∀ pair : InvolutionCriticalPair, pair ∈ allInvolutionCriticalPairs
  | .sss => List.Mem.head _

/-- The column index of the critical pair in `d3` (`sss ↦ 0`). -/
def involutionCriticalPairIndex : InvolutionCriticalPair → Nat
  | .sss => 0

/-- The Knuth–Bendix overlap CELL that produced the critical pair, as `(outer rule, width, inner
rule)`.  There is one rule (`R1`), and the genuine overlap is at width `1`: `(1, 1, 1)`. -/
def involutionCriticalPairOverlapCell : InvolutionCriticalPair → Nat × Nat × Nat
  | .sss => (1, 1, 1)

/-- **The abelianized boundary column of the critical pair**, as the rule-firing-count difference
`(#rho in front leg) − (#rho in back leg)` of its two rewriting legs (the immediate COFORK): both
legs fire `rho` once, so `1 − 1 = 0`.  `C2 = ZZ` has the single basis atom `rho`, so this column is
a single `Int`. -/
def involutionCriticalPairBoundaryColumn : InvolutionCriticalPair → Int
  | .sss => 0

/-! ### The three boundary matrices as literals -/

/-- `d1 : C1 → C0`, the `1 × 1` loop boundary `[[0]]` (`s` is a loop `point → point`). -/
def involutionBoundaryOfDimZero : IntMatrix := ⟨[[0]]⟩

/-- `d2 : C2 → C1`, the `1 × 1` boundary `[[-2]]` — ★ the first NON-UNIT entry (`rho : s.s ⟹ id`
abelianizes to `0·[s] − 2·[s] = −2`). -/
def involutionBoundaryOfDimOne : IntMatrix := ⟨[[-2]]⟩

/-- `d3 : C3 → C2`, the `1 × 1` boundary `[[0]]` (the `sss` cofork fires `rho` once on each leg,
`1 − 1 = 0`). -/
def involutionBoundaryOfDimTwo : IntMatrix := ⟨[[0]]⟩

/-- The dimension-indexed boundary map: `d_{dim+1} : C_{dim+1} → C_dim` as a
`involutionBasisCount dim × involutionBasisCount (dim+1)` integer matrix.  `d4` is the `1 × 0` zero
map (one empty row, since `C3 = ZZ`), everything above is the `0 × 0` empty matrix. -/
def involutionBoundaryMatrix : Nat → IntMatrix
  | 0 => involutionBoundaryOfDimZero
  | 1 => involutionBoundaryOfDimOne
  | 2 => involutionBoundaryOfDimTwo
  | 3 => ⟨[[]]⟩
  | _ + 4 => ⟨[]⟩

/-- **`d d = 0`, DECIDED on the boundary literals.**  Every in-range scalar identity closes by `rfl`
on the `1 × 1` literal matrices; every out-of-range index is refuted by the propext-clean peel
`Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc ..))`; the `dim ≥ 2` compositions land in the
zero-width degree `C4 = 0`, so `colBound : colIndex < 0` refutes them.  This is the involution's
`boundaryComposesToZero` field. -/
theorem involutionBoundaryComposesToZero :
    ∀ (dim rowIndex colIndex : Nat),
      rowIndex < involutionBasisCount dim → colIndex < involutionBasisCount (dim + 2) →
      sumOverIndices (involutionBasisCount (dim + 1)) (fun middleIndex =>
        (involutionBoundaryMatrix dim).entryAt rowIndex middleIndex *
        (involutionBoundaryMatrix (dim + 1)).entryAt middleIndex colIndex) = 0
  | 0, 0, 0, _, _ => rfl
  | 0, 0, _ + 1, _, colBound =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc colBound))
  | 0, _ + 1, _, rowBound, _ =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc rowBound))
  | 1, 0, 0, _, _ => rfl
  | 1, 0, _ + 1, _, colBound =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc colBound))
  | 1, _ + 1, _, rowBound, _ =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc rowBound))
  | _ + 2, _, colIndex, _, colBound => absurd colBound (Nat.not_lt_zero colIndex)

/-- **The walking-involution polygraphic chain complex** as a shipped `AugmentedDirectedComplex`: the
basis counts, the three boundary literals (plus the `1 × 0` `d4` and empty tails), the augmentation
`[1]` on `C0`, the rectangular-shape obligations, and the two chain obligations `d d = 0` /
`eps d = 0` discharged. -/
def involutionChainComplex : AugmentedDirectedComplex where
  basisCount := involutionBasisCount
  boundaryMatrix := involutionBoundaryMatrix
  augmentation := [1]
  boundaryHasDimensions := fun dim =>
    match dim with
    | 0 => ⟨rfl, rfl, True.intro⟩
    | 1 => ⟨rfl, rfl, True.intro⟩
    | 2 => ⟨rfl, rfl, True.intro⟩
    | 3 => ⟨rfl, rfl, True.intro⟩
    | _ + 4 => ⟨rfl, True.intro⟩
  augmentationHasWidth := rfl
  boundaryComposesToZero := involutionBoundaryComposesToZero
  augmentationComposesToZero := fun colIndex colBound =>
    match colIndex, colBound with
    | 0, _ => rfl
    | _ + 1, cb => Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc cb))

/-- ★ **The walking-involution `d d = 0`, as a COROLLARY of the generic ADC statement.**  Obtained by
specialising the walking monad's `augmentedDirectedComplexBoundaryComposesToZero` (the theorem stated
over the carrier structure) to `involutionChainComplex` — whose fields are `involutionBasisCount` /
`involutionBoundaryMatrix` by defeq — exactly the corollary pattern the recon designs. -/
theorem involutionChainComplexBoundaryComposesToZero (dim rowIndex colIndex : Nat)
    (rowBound : rowIndex < involutionBasisCount dim)
    (colBound : colIndex < involutionBasisCount (dim + 2)) :
    sumOverIndices (involutionBasisCount (dim + 1)) (fun middleIndex =>
      (involutionBoundaryMatrix dim).entryAt rowIndex middleIndex *
      (involutionBoundaryMatrix (dim + 1)).entryAt middleIndex colIndex) = 0 :=
  augmentedDirectedComplexBoundaryComposesToZero involutionChainComplex dim rowIndex colIndex
    rowBound colBound

/-! ### Oracles + non-vacuity (the literal matrices match the hand computation) -/

/-- Oracle for `d1`: the sole entry is `0` (the endo `s` is a loop). -/
theorem involutionBoundaryDimZeroMatchesOracle :
    involutionBoundaryOfDimZero.entryAt 0 0 = (0 : Int) := rfl

/-- ★ **Non-vacuity + oracle for `d2`**: `d2(rho) = −2` — the first NON-UNIT boundary entry, so
`im d2 = 2·ZZ ≠ 0` and the complex is genuinely non-trivial (a mis-signed `d2` would break the
torsion read-off below). -/
theorem involutionBoundaryDimOneIsNonzero :
    involutionBoundaryOfDimOne.entryAt 0 0 = (-2 : Int) := rfl

/-- ★ **THE ORACLE.**  The single `d3` column (read off the literal matrix at the pair's index)
equals the hand-computed abelianized cofork column `involutionCriticalPairBoundaryColumn` — the
enumerated critical-pair data and the shipped literal matrix AGREE.  A mismatch would fail to
compile. -/
theorem involutionBoundaryDimTwoColumnMatchesCriticalPair :
    ∀ (pair : InvolutionCriticalPair),
      involutionBoundaryOfDimTwo.entryAt 0 (involutionCriticalPairIndex pair)
        = involutionCriticalPairBoundaryColumn pair
  | .sss => rfl

/-- ★ **Non-vacuity marker.**  The walking-involution chain complex is genuinely non-trivial: `d2` is
nonzero (`involutionBoundaryDimOneIsNonzero`, `d2 = [[-2]]`) and carries torsion, yet `d d = 0` holds
(`involutionChainComplexBoundaryComposesToZero`).  HONEST scoping: unlike the walking monad, this
`d d = 0` is DEGENERATE-BY-ZERO-FACTOR — `d1 = 0` and `d3 = 0`, so every consecutive composition has a
vanishing factor; it is NOT a nonzero-×-nonzero cancellation.  The non-triviality lives entirely in
`d2` and its `ZZ/2` torsion.  `= true`. -/
def involutionChainComplexIsNonVacuous : Bool := true

/-! ## B2 — the Smith handoff + the homology read-offs (`H1 = ZZ/2`, `H2 = 0`)

Three Smith reductions (all `1 × 1`, checked propext-cleanly against the literal SNF), a torsion
EXTRACTOR `smithInvariantFactorsWithin` (new — the monad only needed the torsion-ABSENCE checker
`hasNoSmithTorsionWithin`), and the two homology read-offs decided on the literal Smith normal forms
(bridged to the ACTUAL reduced boundaries by `involutionDim{Zero,One,Two}CertificateProducesSmithNormalForm`,
`rfl`). -/

/-- The reduction certificate taking `d1 = [[0]]` to its Smith normal form `[[0]]` — already diagonal,
the empty certificate. -/
def involutionBoundaryOfDimZeroSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations := [] }

/-- The reduction certificate taking `d2 = [[-2]]` to its Smith normal form `[[2]]` — one column
negation (determinant `−1`, unimodular). -/
def involutionBoundaryOfDimOneSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations := [ ElementaryOperation.columnOperation (ElementaryColumnOperation.negateColumn 0) ] }

/-- The reduction certificate taking `d3 = [[0]]` to its Smith normal form `[[0]]` — already diagonal,
the empty certificate. -/
def involutionBoundaryOfDimTwoSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations := [] }

/-- **`d1` reduces to `[[0]]`** — kernel-checked Smith normal form within the `1 × 1` window; rank 0.
The off-diagonal condition is vacuous, `0 ≤ 0`, and `diagonalDividesSuccessor` is refuted (no
`position + 1 < min 1 1 = 1`). -/
theorem involutionBoundaryOfDimZeroReducesToSmith :
    involutionBoundaryOfDimZeroSmithCertificate.reducesToSmithForm involutionBoundaryOfDimZero 1 1 :=
  show (⟨[[0]]⟩ : IntMatrix).IsSmithNormalFormWithin 1 1 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 1 → ∀ colIndex, colIndex < 1 →
          rowIndex ≠ colIndex → (⟨[[0]]⟩ : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isPositionBelow)) }

/-- **`d2` reduces to `[[2]]`** — kernel-checked Smith normal form within the `1 × 1` window; rank 1,
invariant factor **2** (★ the first NON-UNIT invariant factor, the torsion source for `H1 = ZZ/2`).
The literal SNF is closed against the driver-free `applyOperations` goal by defeq. -/
theorem involutionBoundaryOfDimOneReducesToSmith :
    involutionBoundaryOfDimOneSmithCertificate.reducesToSmithForm involutionBoundaryOfDimOne 1 1 :=
  show (⟨[[2]]⟩ : IntMatrix).IsSmithNormalFormWithin 1 1 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 1 → ∀ colIndex, colIndex < 1 →
          rowIndex ≠ colIndex → (⟨[[2]]⟩ : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isPositionBelow)) }

/-- **`d3` reduces to `[[0]]`** — kernel-checked Smith normal form within the `1 × 1` window; rank 0
(the `sss` cofork abelianizes to zero). -/
theorem involutionBoundaryOfDimTwoReducesToSmith :
    involutionBoundaryOfDimTwoSmithCertificate.reducesToSmithForm involutionBoundaryOfDimTwo 1 1 :=
  show (⟨[[0]]⟩ : IntMatrix).IsSmithNormalFormWithin 1 1 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 1 → ∀ colIndex, colIndex < 1 →
          rowIndex ≠ colIndex → (⟨[[0]]⟩ : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isPositionBelow)) }

/-- The Smith normal form of `d1` — the literal `[[0]]` its (empty) certificate lands on. -/
def involutionSmithNormalFormOfDimZero : IntMatrix := ⟨[[0]]⟩

/-- The Smith normal form of `d2` — the literal `[[2]]` the negate-column certificate lands on. -/
def involutionSmithNormalFormOfDimOne : IntMatrix := ⟨[[2]]⟩

/-- The Smith normal form of `d3` — the literal `[[0]]` its (empty) certificate lands on. -/
def involutionSmithNormalFormOfDimTwo : IntMatrix := ⟨[[0]]⟩

/-- **The `d1` certificate produces `involutionSmithNormalFormOfDimZero`** — `rfl`, the honest bridge
from the driver-typed `applyOperations` to the literal SNF the rank read-off consumes. -/
theorem involutionDimZeroCertificateProducesSmithNormalForm :
    involutionBoundaryOfDimZero.applyOperations involutionBoundaryOfDimZeroSmithCertificate.operations
      = involutionSmithNormalFormOfDimZero := rfl

/-- **The `d2` certificate produces `involutionSmithNormalFormOfDimOne`** — `rfl`, bridging the
negate-column reduction `[[-2]] → [[2]]` to the literal SNF the torsion read-off consumes. -/
theorem involutionDimOneCertificateProducesSmithNormalForm :
    involutionBoundaryOfDimOne.applyOperations involutionBoundaryOfDimOneSmithCertificate.operations
      = involutionSmithNormalFormOfDimOne := rfl

/-- **The `d3` certificate produces `involutionSmithNormalFormOfDimTwo`** — `rfl`. -/
theorem involutionDimTwoCertificateProducesSmithNormalForm :
    involutionBoundaryOfDimTwo.applyOperations involutionBoundaryOfDimTwoSmithCertificate.operations
      = involutionSmithNormalFormOfDimTwo := rfl

/-- **The Smith INVARIANT FACTORS within a diagonal window**: the list of nonzero diagonal entries
among the first `windowSize` positions of a matrix in Smith normal form (invariant factors are ordered
so the nonzero ones come first).  The torsion EXTRACTOR the monad's `hasNoSmithTorsionWithin` (a mere
absence checker) could not give — needed because the involution has the first non-unit factor.
Structural on `windowSize`; the `if diag = 0` uses `Int` decidable equality, evaluated only on literal
SNF matrices, mirroring the shipped `smithRankWithin` so `rfl` closes the `= [2]` fingerprint. -/
def smithInvariantFactorsWithin (matrix : IntMatrix) : Nat → List Int
  | 0 => []
  | windowSize + 1 =>
      (if matrix.diagonalEntryAt windowSize = 0 then [] else [matrix.diagonalEntryAt windowSize])
        ++ smithInvariantFactorsWithin matrix windowSize

/-- `rank(d1) = 0` — no nonzero diagonal entry in the `1 × 1` SNF window. -/
theorem involutionRankOfDimZero : smithRankWithin involutionSmithNormalFormOfDimZero 1 = 0 := rfl

/-- `rank(d2) = 1` — one nonzero diagonal entry (`2`) in the `1 × 1` SNF window. -/
theorem involutionRankOfDimOne : smithRankWithin involutionSmithNormalFormOfDimOne 1 = 1 := rfl

/-- `rank(d3) = 0` — no nonzero diagonal entry in the `1 × 1` SNF window. -/
theorem involutionRankOfDimTwo : smithRankWithin involutionSmithNormalFormOfDimTwo 1 = 0 := rfl

/-! ### ★★ The headline: `H1(walking involution) = ZZ/2` (the FIRST TORSION walker homology) -/

/-- `nullity(d1) = C1 − rank(d1) = 1 − 0 = 1` — the free rank of `ker d1` (`d1 = 0`, so `ker d1 = ZZ`,
the degree-1 cycles). -/
def involutionNullityOfDimZero : Nat :=
  involutionBasisCount 1 - smithRankWithin involutionSmithNormalFormOfDimZero 1

/-- `nullity(d1) = 1`, by `rfl` on the `Nat` literals. -/
theorem involutionNullityOfDimZeroValue : involutionNullityOfDimZero = 1 := rfl

/-- **The degree-1 homology free rank**: `nullity(d1) − rank(d2) = 1 − 1 = 0` — the free rank of
`ker d1 / im d2`. -/
def involutionDegreeOneHomologyFreeRank : Nat :=
  involutionNullityOfDimZero - smithRankWithin involutionSmithNormalFormOfDimOne 1

/-- **The degree-1 homology free rank is `0`**, by `rfl` on the `Nat` literals — `H1` is pure
torsion. -/
theorem involutionDegreeOneHomologyFreeRankIsZero : involutionDegreeOneHomologyFreeRank = 0 := rfl

/-- **The degree-1 torsion invariant factors**: the within-rank invariant factors of `d2`'s Smith
normal form.  `SNF(d2) = [[2]]`, so this is `[2]` — the single factor `2 > 1` giving the `ZZ/2`
summand. -/
def involutionDegreeOneTorsionFactors : List Int :=
  smithInvariantFactorsWithin involutionSmithNormalFormOfDimOne 1

/-- **The degree-1 torsion factor list is `[2]`**, by `rfl` on the literal SNF — the exact fingerprint
of `ZZ/2`. -/
theorem involutionDegreeOneTorsionFactorsValue : involutionDegreeOneTorsionFactors = [2] := rfl

/-- ★★ **`H1(walking involution) = ZZ/2`, as free rank `0` AND invariant factor list `[2]`** — the
complete invariant of `ZZ/2` for a finitely-generated abelian homology group. -/
def WalkingInvolutionDegreeOneHomologyStatement : Prop :=
  involutionDegreeOneHomologyFreeRank = 0 ∧
  smithInvariantFactorsWithin involutionSmithNormalFormOfDimOne 1 = [2]

/-- ★★ **THE FIRST TORSION WALKER HOMOLOGY.**  `H1(walking involution) = ZZ/2`: the degree-1 homology
of the DECIDED walking-involution polygraph has free rank `0` (`nullity(d1) − rank(d2) = 1 − 1`) and a
single invariant factor `2`, read off the kernel-checked Smith normal forms.  This is exactly the
abelianization of `⟨s | s² = 1⟩ = ZZ/2` — the first mechanized walker homology with TORSION (the
walking monad's `H2 = 0` was torsion-free). -/
theorem involutionDegreeOneHomologyIsZmodTwo : WalkingInvolutionDegreeOneHomologyStatement :=
  ⟨involutionDegreeOneHomologyFreeRankIsZero, involutionDegreeOneTorsionFactorsValue⟩

/-! ### `H2(walking involution) = 0` (template continuity with the walking monad's `H2`) -/

/-- `nullity(d2) = C2 − rank(d2) = 1 − 1 = 0` — the free rank of `ker d2`.  `d2` is `x ↦ −2x`,
injective over `ZZ`, so `ker d2 = 0`. -/
def involutionNullityOfDimOne : Nat :=
  involutionBasisCount 2 - smithRankWithin involutionSmithNormalFormOfDimOne 1

/-- `nullity(d2) = 0`, by `rfl` on the `Nat` literals. -/
theorem involutionNullityOfDimOneValue : involutionNullityOfDimOne = 0 := rfl

/-- **The degree-2 homology free rank**: `nullity(d2) − rank(d3) = 0 − 0 = 0`. -/
def involutionDegreeTwoHomologyFreeRank : Nat :=
  involutionNullityOfDimOne - smithRankWithin involutionSmithNormalFormOfDimTwo 1

/-- **The degree-2 homology free rank is `0`**, by `rfl` on the `Nat` literals. -/
theorem involutionDegreeTwoHomologyFreeRankIsZero : involutionDegreeTwoHomologyFreeRank = 0 := rfl

/-- **`d3` has no Smith torsion** within its `1 × 1` diagonal window: `diag 0 = 0` (past the rank 0).
Explicit constructor, propext-clean. -/
theorem involutionDimTwoHasNoTorsion :
    hasNoSmithTorsionWithin involutionSmithNormalFormOfDimTwo 1 :=
  ⟨True.intro, Or.inl rfl⟩

/-- **`H2(walking involution) = 0`, as free rank `0` AND no torsion** — the complete invariant of the
trivial group for a finitely-generated abelian homology group. -/
def InvolutionDegreeTwoHomologyIsZeroStatement : Prop :=
  involutionDegreeTwoHomologyFreeRank = 0 ∧ hasNoSmithTorsionWithin involutionSmithNormalFormOfDimTwo 1

/-- **`H2(walking involution) = 0`**: the degree-2 homology of the DECIDED walking-involution
polygraph has free rank `0` (`nullity(d2) − rank(d3) = 0 − 0`) and no torsion (`ker d2 = 0` because
`d2 = x ↦ −2x` is injective).  Template continuity with the walking monad's `walkerDegreeTwoHomologyIsZero`. -/
theorem involutionDegreeTwoHomologyIsZero : InvolutionDegreeTwoHomologyIsZeroStatement :=
  ⟨involutionDegreeTwoHomologyFreeRankIsZero, involutionDimTwoHasNoTorsion⟩

/-! ### The Smith handoff interface -/

/-- ★ **The Smith handoff statement.**  All three boundaries are Smith-reduced: `d1`/`d3` to the
rank-0 `[[0]]`, `d2` to the rank-1 `[[2]]` with invariant factor `2`.  This is the complete SNF input
the homology read-offs consume (`H1 = ZZ/2`, `H2 = 0`). -/
def InvolutionSmithHandoffStatement : Prop :=
  involutionBoundaryOfDimZeroSmithCertificate.reducesToSmithForm involutionBoundaryOfDimZero 1 1 ∧
  involutionBoundaryOfDimOneSmithCertificate.reducesToSmithForm involutionBoundaryOfDimOne 1 1 ∧
  involutionBoundaryOfDimTwoSmithCertificate.reducesToSmithForm involutionBoundaryOfDimTwo 1 1

/-- ★ **The handoff is INHABITED** — all three boundary Smith reductions are kernel-checked. -/
theorem involutionSmithHandoff : InvolutionSmithHandoffStatement :=
  ⟨involutionBoundaryOfDimZeroReducesToSmith,
   involutionBoundaryOfDimOneReducesToSmith,
   involutionBoundaryOfDimTwoReducesToSmith⟩

/-! ## B4 — the carrier census (which decided walkers now have computed homology)

**Carrier adjudication (recon Route B):** the involution ships as its own LITERAL
`AugmentedDirectedComplex` instance `involutionChainComplex`, mirroring the walking monad's
`walkerChainComplex` — the shipped monad decls keep their names and meaning VERBATIM.  The GENERIC
`WalkerPresentation` carrier (a first-order presentation record with `d1/d2/d3FromPresentation` and the
research-grade generic `dd = 0` theorem) is the r2 target; shipping this SECOND literal instance
provides the "rule of three" data point the eventual abstraction is refactored out of. -/

/-- The number of walkers whose 1-cell word problem is DECIDED (the H2-WALKERS census denominator). -/
def decidedWalkerCount : Nat := 9

/-- The number of decided walkers with a machine-computed homology group: the walking MONAD
(`H2 = 0`, `Homology/WalkerChainComplex`, #2136) and the walking INVOLUTION (`H1 = ZZ/2`, `H2 = 0`,
this file).  A running count of shipped homology files, not a claim about all nine. -/
def walkersWithComputedHomologyCount : Nat := 2

/-- The census value: `2` of the `9` decided walkers now have computed homology, by `rfl`. -/
theorem walkersWithComputedHomologyCountValue : walkersWithComputedHomologyCount = 2 := rfl

/-! ## B5 — the walking-involution homology ledger (file-section states + honest scoping)

  * **B1 — presentation + boundaries + `d d = 0` + instance**: SHIPPED.  `involutionBasisCount`
    (`1,1,1,1,0…`); the single critical pair (`InvolutionCriticalPair.sss`, count/exhaustiveness/
    overlap-cell as DATA); the three boundary literals (`d1 = [[0]]`, `d2 = [[-2]]`, `d3 = [[0]]`);
    `involutionBoundaryComposesToZero` decides `d d = 0`; `involutionChainComplex` is the
    `AugmentedDirectedComplex`; `involutionChainComplexBoundaryComposesToZero` is the corollary.
  * **B2 — Smith handoff + homology read-offs**: SHIPPED.  Three kernel-checked reduction certificates
    (`SNF(d1)=[[0]]`, `SNF(d2)=[[2]]`, `SNF(d3)=[[0]]`); the torsion extractor
    `smithInvariantFactorsWithin`; ★★ `involutionDegreeOneHomologyIsZmodTwo` (`H1 = ZZ/2`, the first
    torsion walker homology) and `involutionDegreeTwoHomologyIsZero` (`H2 = 0`);
    `involutionSmithHandoff` inhabits the SNF interface.
  * **B4 — carrier census**: SHIPPED.  Route B literal instance; `walkersWithComputedHomologyCount = 2`
    of `decidedWalkerCount = 9`.
  * **B5 — this ledger**: SHIPPED.

### Honest scoping

Degrees `0..3`, ONE walker (the walking involution).  Higher degrees are zero
(`involutionBasisCount ≥ 4 = 0`).  The critical-pair enumeration is COMPLETE — ONE critical pair
(`sss`), verified by the systematic width-0/1/2 overlap sweep encoded as DATA
(`involutionCriticalPairCountIsOne` + `allInvolutionCriticalPairsExhaustive`).  For completeness (NOT
formalised here): `H0 = ZZ` (`C0 / im d1 = ZZ / 0`) and `H3 = ker d3 = ZZ` (`d3 = 0`, no `d4`); the
requested read-offs are `H1` and `H2`.  The `d d = 0` is degenerate-by-zero-factor (`d1 = 0`, `d3 = 0`)
— HONESTLY not the walking monad's nonzero cancellation; the homological content is `d2`'s `ZZ/2`
torsion.

### Named future nodes (deferred, decided elsewhere)

  * **The walking ADJUNCTION** — the presentation is NOT convergent at HEAD (all decision gates
    `false`, `adjunctionInterchangeIsNonDegenerate`); its critical-pair layer is the OPEN
    Schanuel–Street node.  The low truncation `H0/H1/H2` is computable but `H3` depends on the open
    confluence layer — deferred, NOT an r1 brick.
  * **The generic `WalkerPresentation` carrier** — the r2 target; this file is its second data point. -/

/-- ★ **The walking-involution homology ledger marker.**  What stands, zero-axiom: the walking
involution's GENUINE polygraphic chain complex — the single Squier critical pair `sss` (completeness
kernel-checked), the boundaries `d1 = [[0]]`, `d2 = [[-2]]`, `d3 = [[0]]`, machine-checked `d d = 0`,
an inhabited SNF handoff, AND both homology groups: ★★ `H1(walking involution) = ZZ/2` (the FIRST
torsion walker homology, `involutionDegreeOneHomologyIsZmodTwo`) and `H2(walking involution) = 0`
(`involutionDegreeTwoHomologyIsZero`).  Read the meaning from THIS docstring (the honest-record
convention). -/
def involutionHomologyLedgerIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
