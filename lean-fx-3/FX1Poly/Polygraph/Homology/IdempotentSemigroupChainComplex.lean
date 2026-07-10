import FX1Poly.ComputerAlgebra.Number.NatEuclideanDivision
import FX1Poly.Polygraph.Homology.WalkerPresentationCarrier

/-! # FX1Poly/Polygraph/Homology/IdempotentSemigroupChainComplex — the polygraphic chain complex of
    the DECIDED idempotent-semigroup walker `⟨e | ee ⟹ e⟩`, with machine-checked `d d = 0`, its
    Smith-normal boundaries, and the kernel-checked homology `H1 = 0` (the UNIT invariant-factor
    endpoint, `ZZ/1 = 0`) and `H2 = 0` (the H2-WALKERS census-maximum round)

The idempotent-semigroup walker presents the single-object polygraph with one endo 1-generator `e`
(words `eⁿ`) and one rewrite 2-generator `mu : ee ⟹ e` — the free idempotent endomorphism.  The
presentation is CONVERGENT and DECIDED (terminating — each rule application drops the word length by 1
— and confluent — the sole width-1 self-overlap `eee` closes at `ee`), so its abelianization is a finite
chain complex of free `ZZ`-modules and homology is exact integer linear algebra (Smith normal form),
exactly as for the walking monad (`Homology/WalkerChainComplex`), the walking involution
(`Homology/InvolutionChainComplex`), and the cyclic-order-three walker
(`Homology/CyclicThreeChainComplex`), whose Smith read-off machinery this module reuses wholesale.

This is the FOURTH literal instance, and the FIRST with a UNIT invariant factor (`|d2| = 1`): the
shipped monad / involution / cyclic complexes stay VERBATIM, this file adds the `⟨e | ee ⟹ e⟩` complex
and recovers it as an EVALUATION of the generic `WalkerPresentation` carrier
(`Homology/WalkerPresentationCarrier`).

## The overlap sweep (systematic — the missed-pair trap avoided)

One rule `mu : ee ⟹ e`, lhs `ee` (length 2) over the free monoid on one letter `e`.  Self-overlaps of
`ee` with `ee` are classified by overlap WIDTH (the involution's single-length-2-rule sweep, so the
missed-pair failure mode cannot recur):

  * **width 2** (`ee = ee`): identical redex — the trivial ROOT-SELF overlap, EXCLUDED.
  * **width 1** (word `eee`, length 3): front redex `(ee)e → (e)e = ee`; back redex `e(ee) → e(e) = ee`.
    Joinable at `ee`, both legs fire `mu` once.  ★ the SOLE genuine critical pair.
  * **width 0** (word `eeee`, disjoint redexes): an orthogonal diamond — NOT a critical pair.

→ **ONE critical pair from ONE rule** (like the involution).  Encoded below as
`allIdempotentSemigroupCriticalPairs` + `idempotentSemigroupCriticalPairCountIsOne` +
`allIdempotentSemigroupCriticalPairsExhaustive` — the table IS the certificate, never prose-counted.

## The arithmetic (compute first, state after)

Abelianize (target − source convention, matching the shipped walkers).  `basisCount : 1, 1, 1, 1, 0`
(one object, one 1-generator `e`, one rule `mu`, ONE critical pair `eee`).

  * **`d1 : C1 → C0`** — `e : point → point` is a LOOP, `[point] − [point] = 0`, the `1 × 1` `[[0]]`.
  * **`d2 : C2 → C1`** — `mu : ee ⟹ e`: target `e ↦ 1·[e]`, source `ee ↦ 2·[e]`, so
    `d2(mu) = 1 − 2 = −1`, the `1 × 1` `[[-1]]`.  ★ the UNIT boundary entry (`|d2| = 1`) — `mu`
    abelianizes to an ISOMORPHISM `ZZ → ZZ`.
  * **`d3 : C3 → C2`** — the sole critical pair `eee` fires `mu` once on each leg, `1 − 1 = 0`, the
    `1 × 1` `[[0]]`.

Smith normal forms: `SNF(d1) = [[0]]` (rank 0), `SNF(d2) = [[1]]` (rank 1, invariant factor **1** — the
UNIT), `SNF(d3) = [[0]]` (rank 0).

  * ★★ **`H1 = ker d1 / im d2`**: `d1 = 0 ⟹ ker d1 = ZZ`; `d2 = x ↦ −x` is an ISOMORPHISM, so
    `im d2 = ZZ`.  Free rank `nullity(d1) − rank(d2) = 1 − 1 = 0`; the within-rank invariant factor of
    `d2` is `1` (a UNIT), so `H1 = ZZ/1 = 0`.  This is the |d2| = 1 UNIT endpoint — distinct from the
    involution's torsion factor `[2]` and the cyclic walker's `[3]`; the abelianization of the free
    idempotent endomorphism collapses in degree 1.
  * **`H2 = ker d2 / im d3`**: `d2` is `x ↦ −x`, INJECTIVE over `ZZ`, so `ker d2 = 0`; `im d3 = 0`.
    Free rank `nullity(d2) − rank(d3) = 0 − 0 = 0`, no torsion — `H2 = 0`.

## Honesty note

For the idempotent-semigroup walker `d d = 0` holds because **`d1 = 0` and `d3 = 0`** — every
consecutive composition has a vanishing factor, exactly like the involution and cyclic walkers
(DEGENERATE-BY-ZERO-FACTOR), NOT the walking monad's genuine nonzero-×-nonzero cancellation.  The
distinctive content is that `d2 = [[-1]]` is a UNIT: `im d2 = ZZ` fills all of `ker d1`, collapsing
`H1` to `0` (the involution and cyclic walkers' `d2` were non-units `−2`, `−3`, leaving `ZZ/2`, `ZZ/3`).
`H0 = ZZ` and the degenerate top `H3 = ker d3 = ZZ` are computable but not formalised here (the
requested read-offs are `H1` and `H2`, matching the sibling scope).

## Zero-axiom design decisions

  * The carrier is the shipped `AugmentedDirectedComplex`; every match stays on non-indexed inductives.
  * `d d = 0` is DECIDED on the boundary LITERALS: in-range identities by `rfl`, out-of-range indices by
    the propext-clean peel `Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc ..))`.
  * The Smith handoff ships EXPLICIT unimodular reduction certificates checked propext-cleanly against
    the literal Smith normal forms; the torsion extractor `smithInvariantFactorsWithin` (reused from
    `InvolutionChainComplex`) yields the `= [1]` UNIT fingerprint by `rfl`, and the trivial-group
    conclusion rides `hasNoSmithTorsionWithin` (the unit `1` passes the no-torsion branch).

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/IdempotentSemigroupChainComplex.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra
open FX1Poly.Polygraph.Steiner

/-! ## B1 — the presentation data, the boundary literals, and `d d = 0` -/

/-- The per-dimension basis counts of the idempotent-semigroup chain complex: `C0 = ZZ` (the object),
`C1 = ZZ` (the endo 1-generator `e`), `C2 = ZZ` (the single rule `mu`), `C3 = ZZ` (the single critical
pair `eee`), and nothing above degree 3. -/
def idempotentSemigroupBasisCount : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | _ + 4 => 0

/-! ### The single critical pair (systematic overlap sweep, recorded as DATA) -/

/-- The single Squier critical pair of the idempotent-semigroup presentation: the width-1 overlap `eee`
of the rule `ee ⟹ e` with itself. -/
inductive IdempotentSemigroupCriticalPair
  /-- The width-1 self-overlap `eee`: front leg `(ee)e → ee`, back leg `e(ee) → ee`. -/
  | eee

/-- The complete enumeration of the idempotent-semigroup critical pairs — ONE, listed. -/
def allIdempotentSemigroupCriticalPairs : List IdempotentSemigroupCriticalPair := [.eee]

/-- ★ **The critical-pair count is exactly ONE** — kernel-checked (`rfl`), not prose. -/
theorem idempotentSemigroupCriticalPairCountIsOne :
    allIdempotentSemigroupCriticalPairs.length = 1 := rfl

/-- ★ **The enumeration is EXHAUSTIVE** — the sole `IdempotentSemigroupCriticalPair` constructor
appears in `allIdempotentSemigroupCriticalPairs` (a missing constructor would fail to compile).  With
`idempotentSemigroupCriticalPairCountIsOne` this kernel-checks the critical-pair set is EXACTLY
`eee`. -/
theorem allIdempotentSemigroupCriticalPairsExhaustive :
    ∀ pair : IdempotentSemigroupCriticalPair, pair ∈ allIdempotentSemigroupCriticalPairs
  | .eee => List.Mem.head _

/-- The column index of the critical pair in `d3` (`eee ↦ 0`). -/
def idempotentSemigroupCriticalPairIndex : IdempotentSemigroupCriticalPair → Nat
  | .eee => 0

/-- The Knuth–Bendix overlap CELL that produced the critical pair, as `(outer rule, width, inner
rule)`.  There is one rule (`R1`), and the genuine overlap is at width `1`: `(1, 1, 1)`. -/
def idempotentSemigroupCriticalPairOverlapCell :
    IdempotentSemigroupCriticalPair → Nat × Nat × Nat
  | .eee => (1, 1, 1)

/-- **The abelianized boundary column of the critical pair**, as the rule-firing-count difference
`(#mu in front leg) − (#mu in back leg)` of its two rewriting legs (the immediate COFORK): both legs
fire `mu` once, so `1 − 1 = 0`.  `C2 = ZZ` has the single basis atom `mu`, so this column is a single
`Int`. -/
def idempotentSemigroupCriticalPairBoundaryColumn : IdempotentSemigroupCriticalPair → Int
  | .eee => 0

/-! ### The three boundary matrices as literals -/

/-- `d1 : C1 → C0`, the `1 × 1` loop boundary `[[0]]` (`e` is a loop `point → point`). -/
def idempotentSemigroupBoundaryOfDimZero : IntMatrix := ⟨[[0]]⟩

/-- `d2 : C2 → C1`, the `1 × 1` boundary `[[-1]]` — ★ the UNIT entry (`mu : ee ⟹ e` abelianizes to
`1·[e] − 2·[e] = −1`, an isomorphism `ZZ → ZZ`). -/
def idempotentSemigroupBoundaryOfDimOne : IntMatrix := ⟨[[-1]]⟩

/-- `d3 : C3 → C2`, the `1 × 1` boundary `[[0]]` (the `eee` cofork fires `mu` once on each leg,
`1 − 1 = 0`). -/
def idempotentSemigroupBoundaryOfDimTwo : IntMatrix := ⟨[[0]]⟩

/-- The dimension-indexed boundary map: `d_{dim+1} : C_{dim+1} → C_dim` as a
`idempotentSemigroupBasisCount dim × idempotentSemigroupBasisCount (dim+1)` integer matrix.  `d4` is
the `1 × 0` zero map (one empty row, since `C3 = ZZ`), everything above is the `0 × 0` empty matrix. -/
def idempotentSemigroupBoundaryMatrix : Nat → IntMatrix
  | 0 => idempotentSemigroupBoundaryOfDimZero
  | 1 => idempotentSemigroupBoundaryOfDimOne
  | 2 => idempotentSemigroupBoundaryOfDimTwo
  | 3 => ⟨[[]]⟩
  | _ + 4 => ⟨[]⟩

/-- **`d d = 0`, DECIDED on the boundary literals.**  Every in-range scalar identity closes by `rfl` on
the `1 × 1` literal matrices; every out-of-range index is refuted by the propext-clean peel
`Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc ..))`; the `dim ≥ 2` compositions land in the
zero-width degree `C4 = 0`, so `colBound : colIndex < 0` refutes them.  This is the idempotent-semigroup
walker's `boundaryComposesToZero` field. -/
theorem idempotentSemigroupBoundaryComposesToZero :
    ∀ (dim rowIndex colIndex : Nat),
      rowIndex < idempotentSemigroupBasisCount dim →
      colIndex < idempotentSemigroupBasisCount (dim + 2) →
      sumOverIndices (idempotentSemigroupBasisCount (dim + 1)) (fun middleIndex =>
        (idempotentSemigroupBoundaryMatrix dim).entryAt rowIndex middleIndex *
        (idempotentSemigroupBoundaryMatrix (dim + 1)).entryAt middleIndex colIndex) = 0
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

/-- **The idempotent-semigroup polygraphic chain complex** as a shipped `AugmentedDirectedComplex`: the
basis counts, the three boundary literals (plus the `1 × 0` `d4` and empty tails), the augmentation
`[1]` on `C0`, the rectangular-shape obligations, and the two chain obligations `d d = 0` / `eps d = 0`
discharged. -/
def idempotentSemigroupChainComplex : AugmentedDirectedComplex where
  basisCount := idempotentSemigroupBasisCount
  boundaryMatrix := idempotentSemigroupBoundaryMatrix
  augmentation := [1]
  boundaryHasDimensions := fun dim =>
    match dim with
    | 0 => ⟨rfl, rfl, True.intro⟩
    | 1 => ⟨rfl, rfl, True.intro⟩
    | 2 => ⟨rfl, rfl, True.intro⟩
    | 3 => ⟨rfl, rfl, True.intro⟩
    | _ + 4 => ⟨rfl, True.intro⟩
  augmentationHasWidth := rfl
  boundaryComposesToZero := idempotentSemigroupBoundaryComposesToZero
  augmentationComposesToZero := fun colIndex colBound =>
    match colIndex, colBound with
    | 0, _ => rfl
    | _ + 1, cb => Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc cb))

/-- ★ **The idempotent-semigroup `d d = 0`, as a COROLLARY of the generic ADC statement.**  Obtained by
specialising the walking monad's `augmentedDirectedComplexBoundaryComposesToZero` (stated over the
carrier structure) to `idempotentSemigroupChainComplex`. -/
theorem idempotentSemigroupChainComplexBoundaryComposesToZero (dim rowIndex colIndex : Nat)
    (rowBound : rowIndex < idempotentSemigroupBasisCount dim)
    (colBound : colIndex < idempotentSemigroupBasisCount (dim + 2)) :
    sumOverIndices (idempotentSemigroupBasisCount (dim + 1)) (fun middleIndex =>
      (idempotentSemigroupBoundaryMatrix dim).entryAt rowIndex middleIndex *
      (idempotentSemigroupBoundaryMatrix (dim + 1)).entryAt middleIndex colIndex) = 0 :=
  augmentedDirectedComplexBoundaryComposesToZero idempotentSemigroupChainComplex dim rowIndex colIndex
    rowBound colBound

/-! ### Oracles + non-vacuity (the literal matrices match the hand computation) -/

/-- Oracle for `d1`: the sole entry is `0` (the endo `e` is a loop). -/
theorem idempotentSemigroupBoundaryDimZeroMatchesOracle :
    idempotentSemigroupBoundaryOfDimZero.entryAt 0 0 = (0 : Int) := rfl

/-- ★ **Non-vacuity + oracle for `d2`**: `d2(mu) = −1` — the UNIT boundary entry, so `im d2 = ZZ` and
the complex collapses `H1` (a mis-signed `d2` would break the read-off below). -/
theorem idempotentSemigroupBoundaryDimOneIsUnit :
    idempotentSemigroupBoundaryOfDimOne.entryAt 0 0 = (-1 : Int) := rfl

/-- ★ **THE ORACLE.**  The single `d3` column (read off the literal matrix at the pair's index) equals
the hand-computed abelianized cofork column `idempotentSemigroupCriticalPairBoundaryColumn` — the
enumerated critical-pair data and the shipped literal matrix AGREE.  `rfl`. -/
theorem idempotentSemigroupBoundaryDimTwoColumnMatchesCriticalPair :
    ∀ (pair : IdempotentSemigroupCriticalPair),
      idempotentSemigroupBoundaryOfDimTwo.entryAt 0 (idempotentSemigroupCriticalPairIndex pair)
        = idempotentSemigroupCriticalPairBoundaryColumn pair
  | .eee => rfl

/-- ★ **Non-vacuity marker.**  The idempotent-semigroup chain complex is genuinely non-trivial: `d2` is
nonzero (`idempotentSemigroupBoundaryDimOneIsUnit`, `d2 = [[-1]]`) and a unit, yet `d d = 0` holds.
HONEST scoping: like the involution and cyclic walkers, this `d d = 0` is DEGENERATE-BY-ZERO-FACTOR
(`d1 = 0` and `d3 = 0`), NOT a nonzero-×-nonzero cancellation; the distinctive content is that `d2` is
a UNIT, collapsing `H1` to `0`.  `= true`. -/
def idempotentSemigroupChainComplexIsNonVacuous : Bool := true

/-! ## B2 — the Smith handoff + the homology read-offs (`H1 = 0`, `H2 = 0`) -/

/-- The reduction certificate taking `d1 = [[0]]` to its Smith normal form `[[0]]` — already diagonal. -/
def idempotentSemigroupBoundaryOfDimZeroSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations := [] }

/-- The reduction certificate taking `d2 = [[-1]]` to its Smith normal form `[[1]]` — one column
negation (determinant `−1`, unimodular). -/
def idempotentSemigroupBoundaryOfDimOneSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations := [ ElementaryOperation.columnOperation (ElementaryColumnOperation.negateColumn 0) ] }

/-- The reduction certificate taking `d3 = [[0]]` to its Smith normal form `[[0]]` — already diagonal. -/
def idempotentSemigroupBoundaryOfDimTwoSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations := [] }

/-- **`d1` reduces to `[[0]]`** — kernel-checked Smith normal form within the `1 × 1` window; rank 0. -/
theorem idempotentSemigroupBoundaryOfDimZeroReducesToSmith :
    idempotentSemigroupBoundaryOfDimZeroSmithCertificate.reducesToSmithForm
      idempotentSemigroupBoundaryOfDimZero 1 1 :=
  show (⟨[[0]]⟩ : IntMatrix).IsSmithNormalFormWithin 1 1 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 1 → ∀ colIndex, colIndex < 1 →
          rowIndex ≠ colIndex → (⟨[[0]]⟩ : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isPositionBelow)) }

/-- **`d2` reduces to `[[1]]`** — kernel-checked Smith normal form within the `1 × 1` window; rank 1,
invariant factor **1** (★ the UNIT invariant factor — `d2` is an isomorphism, giving `H1 = ZZ/1 = 0`). -/
theorem idempotentSemigroupBoundaryOfDimOneReducesToSmith :
    idempotentSemigroupBoundaryOfDimOneSmithCertificate.reducesToSmithForm
      idempotentSemigroupBoundaryOfDimOne 1 1 :=
  show (⟨[[1]]⟩ : IntMatrix).IsSmithNormalFormWithin 1 1 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 1 → ∀ colIndex, colIndex < 1 →
          rowIndex ≠ colIndex → (⟨[[1]]⟩ : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isPositionBelow)) }

/-- **`d3` reduces to `[[0]]`** — kernel-checked Smith normal form within the `1 × 1` window; rank 0. -/
theorem idempotentSemigroupBoundaryOfDimTwoReducesToSmith :
    idempotentSemigroupBoundaryOfDimTwoSmithCertificate.reducesToSmithForm
      idempotentSemigroupBoundaryOfDimTwo 1 1 :=
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
def idempotentSemigroupSmithNormalFormOfDimZero : IntMatrix := ⟨[[0]]⟩

/-- The Smith normal form of `d2` — the literal `[[1]]` the negate-column certificate lands on. -/
def idempotentSemigroupSmithNormalFormOfDimOne : IntMatrix := ⟨[[1]]⟩

/-- The Smith normal form of `d3` — the literal `[[0]]` its (empty) certificate lands on. -/
def idempotentSemigroupSmithNormalFormOfDimTwo : IntMatrix := ⟨[[0]]⟩

/-- **The `d1` certificate produces `idempotentSemigroupSmithNormalFormOfDimZero`** — `rfl`. -/
theorem idempotentSemigroupDimZeroCertificateProducesSmithNormalForm :
    idempotentSemigroupBoundaryOfDimZero.applyOperations
      idempotentSemigroupBoundaryOfDimZeroSmithCertificate.operations
      = idempotentSemigroupSmithNormalFormOfDimZero := rfl

/-- **The `d2` certificate produces `idempotentSemigroupSmithNormalFormOfDimOne`** — `rfl`, bridging the
negate-column reduction `[[-1]] → [[1]]` to the literal SNF the unit-factor read-off consumes. -/
theorem idempotentSemigroupDimOneCertificateProducesSmithNormalForm :
    idempotentSemigroupBoundaryOfDimOne.applyOperations
      idempotentSemigroupBoundaryOfDimOneSmithCertificate.operations
      = idempotentSemigroupSmithNormalFormOfDimOne := rfl

/-- **The `d3` certificate produces `idempotentSemigroupSmithNormalFormOfDimTwo`** — `rfl`. -/
theorem idempotentSemigroupDimTwoCertificateProducesSmithNormalForm :
    idempotentSemigroupBoundaryOfDimTwo.applyOperations
      idempotentSemigroupBoundaryOfDimTwoSmithCertificate.operations
      = idempotentSemigroupSmithNormalFormOfDimTwo := rfl

/-- `rank(d1) = 0` — no nonzero diagonal entry in the `1 × 1` SNF window. -/
theorem idempotentSemigroupRankOfDimZero :
    smithRankWithin idempotentSemigroupSmithNormalFormOfDimZero 1 = 0 := rfl

/-- `rank(d2) = 1` — one nonzero diagonal entry (the unit `1`) in the `1 × 1` SNF window. -/
theorem idempotentSemigroupRankOfDimOne :
    smithRankWithin idempotentSemigroupSmithNormalFormOfDimOne 1 = 1 := rfl

/-- `rank(d3) = 0` — no nonzero diagonal entry in the `1 × 1` SNF window. -/
theorem idempotentSemigroupRankOfDimTwo :
    smithRankWithin idempotentSemigroupSmithNormalFormOfDimTwo 1 = 0 := rfl

/-! ### ★★ The headline: `H1(idempotent semigroup) = 0` (the UNIT invariant-factor endpoint) -/

/-- `nullity(d1) = C1 − rank(d1) = 1 − 0 = 1` — the free rank of `ker d1` (`d1 = 0`, so `ker d1 = ZZ`). -/
def idempotentSemigroupNullityOfDimZero : Nat :=
  idempotentSemigroupBasisCount 1 - smithRankWithin idempotentSemigroupSmithNormalFormOfDimZero 1

/-- `nullity(d1) = 1`, by `rfl` on the `Nat` literals. -/
theorem idempotentSemigroupNullityOfDimZeroValue : idempotentSemigroupNullityOfDimZero = 1 := rfl

/-- **The degree-1 homology free rank**: `nullity(d1) − rank(d2) = 1 − 1 = 0`. -/
def idempotentSemigroupDegreeOneHomologyFreeRank : Nat :=
  idempotentSemigroupNullityOfDimZero - smithRankWithin idempotentSemigroupSmithNormalFormOfDimOne 1

/-- **The degree-1 homology free rank is `0`**, by `rfl` — `H1` is torsion-free (and, since the sole
`d2` factor is a UNIT, trivial). -/
theorem idempotentSemigroupDegreeOneHomologyFreeRankIsZero :
    idempotentSemigroupDegreeOneHomologyFreeRank = 0 := rfl

/-- **The degree-1 invariant factors**: the within-rank invariant factors of `d2`'s Smith normal form.
`SNF(d2) = [[1]]`, so this is `[1]` — the single UNIT factor giving `ZZ/1 = 0` (the |d2| = 1 endpoint,
distinct from the involution's `[2]` and the cyclic walker's `[3]`). -/
def idempotentSemigroupDegreeOneInvariantFactors : List Int :=
  smithInvariantFactorsWithin idempotentSemigroupSmithNormalFormOfDimOne 1

/-- **The degree-1 invariant factor list is `[1]`**, by `rfl` on the literal SNF — the UNIT fingerprint
(`ZZ/1 = 0`). -/
theorem idempotentSemigroupDegreeOneInvariantFactorsValue :
    idempotentSemigroupDegreeOneInvariantFactors = [1] := rfl

/-- **`d2` has no Smith torsion** within its `1 × 1` diagonal window: `diag 0 = 1` (a UNIT, which passes
the no-torsion branch — no factor exceeds `1`).  Explicit constructor, propext-clean.  This is the
degree-1 statement that the UNIT factor produces NO `ZZ/d` summand — `H1` is trivial. -/
theorem idempotentSemigroupDimOneHasNoTorsion :
    hasNoSmithTorsionWithin idempotentSemigroupSmithNormalFormOfDimOne 1 :=
  ⟨True.intro, Or.inr rfl⟩

/-- ★★ **`H1(idempotent semigroup) = 0`, as free rank `0`, invariant factor list `[1]` (the UNIT), AND
no torsion** — the complete invariant of the trivial group, with the distinguishing UNIT-factor
fingerprint. -/
def IdempotentSemigroupDegreeOneHomologyStatement : Prop :=
  idempotentSemigroupDegreeOneHomologyFreeRank = 0 ∧
  smithInvariantFactorsWithin idempotentSemigroupSmithNormalFormOfDimOne 1 = [1] ∧
  hasNoSmithTorsionWithin idempotentSemigroupSmithNormalFormOfDimOne 1

/-- ★★ **THE UNIT-FACTOR WALKER HOMOLOGY.**  `H1(idempotent semigroup) = 0`: the degree-1 homology of
the DECIDED idempotent-semigroup polygraph has free rank `0` (`nullity(d1) − rank(d2) = 1 − 1`) and its
sole invariant factor is the UNIT `1` (`ZZ/1 = 0`), read off the kernel-checked Smith normal forms.
`d2` abelianizes `mu : ee ⟹ e` to an ISOMORPHISM `ZZ → ZZ`, so `im d2 = ker d1` collapses `H1` — the
|d2| = 1 UNIT endpoint of the `⟨s | sⁿ⁺¹ ⟹ id⟩`-style family (the involution's `H1 = ZZ/2` and the
cyclic walker's `H1 = ZZ/3` had non-unit `d2`). -/
theorem idempotentSemigroupDegreeOneHomologyIsTrivial :
    IdempotentSemigroupDegreeOneHomologyStatement :=
  ⟨idempotentSemigroupDegreeOneHomologyFreeRankIsZero,
   idempotentSemigroupDegreeOneInvariantFactorsValue,
   idempotentSemigroupDimOneHasNoTorsion⟩

/-! ### `H2(idempotent semigroup) = 0` (template continuity with the shipped walkers) -/

/-- `nullity(d2) = C2 − rank(d2) = 1 − 1 = 0` — `d2` is `x ↦ −x`, injective over `ZZ`, so
`ker d2 = 0`. -/
def idempotentSemigroupNullityOfDimOne : Nat :=
  idempotentSemigroupBasisCount 2 - smithRankWithin idempotentSemigroupSmithNormalFormOfDimOne 1

/-- `nullity(d2) = 0`, by `rfl` on the `Nat` literals. -/
theorem idempotentSemigroupNullityOfDimOneValue : idempotentSemigroupNullityOfDimOne = 0 := rfl

/-- **The degree-2 homology free rank**: `nullity(d2) − rank(d3) = 0 − 0 = 0`. -/
def idempotentSemigroupDegreeTwoHomologyFreeRank : Nat :=
  idempotentSemigroupNullityOfDimOne - smithRankWithin idempotentSemigroupSmithNormalFormOfDimTwo 1

/-- **The degree-2 homology free rank is `0`**, by `rfl` on the `Nat` literals. -/
theorem idempotentSemigroupDegreeTwoHomologyFreeRankIsZero :
    idempotentSemigroupDegreeTwoHomologyFreeRank = 0 := rfl

/-- **`d3` has no Smith torsion** within its `1 × 1` diagonal window: `diag 0 = 0` (past the rank 0).
Explicit constructor, propext-clean. -/
theorem idempotentSemigroupDimTwoHasNoTorsion :
    hasNoSmithTorsionWithin idempotentSemigroupSmithNormalFormOfDimTwo 1 :=
  ⟨True.intro, Or.inl rfl⟩

/-- **`H2(idempotent semigroup) = 0`, as free rank `0` AND no torsion** — the complete invariant of the
trivial group. -/
def IdempotentSemigroupDegreeTwoHomologyIsZeroStatement : Prop :=
  idempotentSemigroupDegreeTwoHomologyFreeRank = 0 ∧
  hasNoSmithTorsionWithin idempotentSemigroupSmithNormalFormOfDimTwo 1

/-- **`H2(idempotent semigroup) = 0`**: the degree-2 homology of the DECIDED idempotent-semigroup
polygraph has free rank `0` (`nullity(d2) − rank(d3) = 0 − 0`) and no torsion (`ker d2 = 0` because
`d2 = x ↦ −x` is injective).  Template continuity with the shipped walkers' `H2 = 0`. -/
theorem idempotentSemigroupDegreeTwoHomologyIsZero :
    IdempotentSemigroupDegreeTwoHomologyIsZeroStatement :=
  ⟨idempotentSemigroupDegreeTwoHomologyFreeRankIsZero, idempotentSemigroupDimTwoHasNoTorsion⟩

/-! ### The Smith handoff interface -/

/-- ★ **The Smith handoff statement.**  All three boundaries are Smith-reduced: `d1`/`d3` to the rank-0
`[[0]]`, `d2` to the rank-1 `[[1]]` with UNIT invariant factor `1`.  The complete SNF input the homology
read-offs consume (`H1 = 0`, `H2 = 0`). -/
def IdempotentSemigroupSmithHandoffStatement : Prop :=
  idempotentSemigroupBoundaryOfDimZeroSmithCertificate.reducesToSmithForm
    idempotentSemigroupBoundaryOfDimZero 1 1 ∧
  idempotentSemigroupBoundaryOfDimOneSmithCertificate.reducesToSmithForm
    idempotentSemigroupBoundaryOfDimOne 1 1 ∧
  idempotentSemigroupBoundaryOfDimTwoSmithCertificate.reducesToSmithForm
    idempotentSemigroupBoundaryOfDimTwo 1 1

/-- ★ **The handoff is INHABITED** — all three boundary Smith reductions are kernel-checked. -/
theorem idempotentSemigroupSmithHandoff : IdempotentSemigroupSmithHandoffStatement :=
  ⟨idempotentSemigroupBoundaryOfDimZeroReducesToSmith,
   idempotentSemigroupBoundaryOfDimOneReducesToSmith,
   idempotentSemigroupBoundaryOfDimTwoReducesToSmith⟩

/-! ## B3 — the fourth instance recovered as an EVALUATION of the generic carrier

The idempotent-semigroup walker's presentation data, and the proof that evaluating the generic
`WalkerPresentation` compute functions at it reproduces the boundary literals above (all `rfl`) — the
fourth data point validating `Homology/WalkerPresentationCarrier`.  The well-formedness discharge feeds
the generic `walkerPresentationBoundaryComposesToZeroOfWellFormed` to re-derive `d d = 0` THROUGH the
carrier. -/

/-- The idempotent-semigroup presentation: one endo 1-generator `e`; one rule `mu : ee ⟹ e`
(`([0, 0], [0])`); one critical pair `eee`, firing `mu` once on each leg (`overlapWord = []`). -/
def idempotentSemigroupWalkerPresentation : WalkerPresentation :=
  { oneGeneratorCount := 1
  , rules := [([0, 0], [0])]
  , criticalPairs := [([], [1], [1])] }

/-- The idempotent-semigroup presentation's basis counts equal `idempotentSemigroupBasisCount`. -/
theorem idempotentSemigroupPresentationComputesBasisCount :
    ∀ dim, idempotentSemigroupWalkerPresentation.computeBasisCount dim
      = idempotentSemigroupBasisCount dim
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

/-- **The idempotent-semigroup presentation computes the shipped `d1`.** -/
theorem idempotentSemigroupPresentationComputesBoundaryDimZero :
    idempotentSemigroupWalkerPresentation.computeBoundaryDimZero
      = idempotentSemigroupBoundaryOfDimZero := rfl

/-- **The idempotent-semigroup presentation computes the shipped `d2` `[[-1]]`.** -/
theorem idempotentSemigroupPresentationComputesBoundaryDimOne :
    idempotentSemigroupWalkerPresentation.computeBoundaryDimOne
      = idempotentSemigroupBoundaryOfDimOne := rfl

/-- **The idempotent-semigroup presentation computes the shipped `d3` `[[0]]`.** -/
theorem idempotentSemigroupPresentationComputesBoundaryDimTwo :
    idempotentSemigroupWalkerPresentation.computeBoundaryDimTwo
      = idempotentSemigroupBoundaryOfDimTwo := rfl

/-- **The idempotent-semigroup presentation computes the shipped dimension-indexed boundary.** -/
theorem idempotentSemigroupPresentationComputesBoundaryMatrix :
    ∀ dim, idempotentSemigroupWalkerPresentation.computeBoundaryMatrix dim
      = idempotentSemigroupBoundaryMatrix dim
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

/-- ★ **The idempotent-semigroup presentation is well-formed** — the residual dimension-1 obligation is
exactly the shipped `idempotentSemigroupBoundaryComposesToZero` at dimension 1 (defeq through the
agreement above). -/
theorem idempotentSemigroupPresentationIsWellFormed :
    WellFormedWalkerPresentation idempotentSemigroupWalkerPresentation :=
  fun rowIndex colIndex rowBound colBound =>
    idempotentSemigroupBoundaryComposesToZero 1 rowIndex colIndex rowBound colBound

/-- ★ **`d d = 0` for the idempotent-semigroup walker, DERIVED THROUGH THE GENERIC CARRIER.**  Feeding
the well-formedness discharge into `walkerPresentationBoundaryComposesToZeroOfWellFormed` re-proves the
fourth instance's chain obligation from the generic machinery — the generic carrier verified to yield
`d d = 0` for a walker it did not hard-code. -/
theorem idempotentSemigroupGenericCarrierBoundaryComposesToZero
    (dim rowIndex colIndex : Nat)
    (rowBound : rowIndex < idempotentSemigroupWalkerPresentation.computeBasisCount dim)
    (colBound : colIndex < idempotentSemigroupWalkerPresentation.computeBasisCount (dim + 2)) :
    sumOverIndices (idempotentSemigroupWalkerPresentation.computeBasisCount (dim + 1))
      (fun middleIndex =>
        (idempotentSemigroupWalkerPresentation.computeBoundaryMatrix dim).entryAt rowIndex middleIndex *
        (idempotentSemigroupWalkerPresentation.computeBoundaryMatrix (dim + 1)).entryAt middleIndex
          colIndex) = 0 :=
  walkerPresentationBoundaryComposesToZeroOfWellFormed idempotentSemigroupWalkerPresentation
    idempotentSemigroupPresentationIsWellFormed dim rowIndex colIndex rowBound colBound

/-! ## B4 — the carrier census update (the fourth walker with computed homology)

`Homology/WalkerChainComplex` (`H2 = 0`), `Homology/InvolutionChainComplex` (`H1 = ZZ/2`, `H2 = 0`), and
`Homology/CyclicThreeChainComplex` (`H1 = ZZ/3`, `H2 = 0`) recorded three decided walkers with
machine-computed homology; this file adds the FOURTH (`H1 = 0` UNIT endpoint, `H2 = 0`).  The census
denominator is `decidedWalkerCount = 9` (shipped in `InvolutionChainComplex`); the shipped running
counts are NOT mutated — the updated count is a new decl here, honestly recording the count AS OF THIS
FILE. -/

/-- The number of decided walkers with a machine-computed homology group, updated after this file: the
walking MONAD (`H2 = 0`), the walking INVOLUTION (`H1 = ZZ/2`), the cyclic-order-three walker
(`H1 = ZZ/3`), and the idempotent-semigroup walker (`H1 = 0`, `H2 = 0`, this file).  A running count of
shipped homology files, not a claim about all nine. -/
def walkersWithComputedHomologyCountAfterIdempotentSemigroup : Nat := 4

/-- The updated census value: `4` of the `9` decided walkers now have computed homology, by `rfl`. -/
theorem walkersWithComputedHomologyCountAfterIdempotentSemigroupValue :
    walkersWithComputedHomologyCountAfterIdempotentSemigroup = 4 := rfl

/-! ## B5 — the idempotent-semigroup homology ledger (file-section states + honest scoping)

  * **B1 — presentation + boundaries + `d d = 0` + instance**: SHIPPED.  `idempotentSemigroupBasisCount`
    (`1,1,1,1,0…`); the single critical pair (`IdempotentSemigroupCriticalPair.eee`,
    count/exhaustiveness/overlap-cell as DATA); the three boundary literals (`d1 = [[0]]`, `d2 = [[-1]]`,
    `d3 = [[0]]`); `idempotentSemigroupBoundaryComposesToZero` decides `d d = 0`;
    `idempotentSemigroupChainComplex` is the `AugmentedDirectedComplex`;
    `idempotentSemigroupChainComplexBoundaryComposesToZero` is the corollary.
  * **B2 — Smith handoff + homology read-offs**: SHIPPED.  Three kernel-checked reduction certificates
    (`SNF(d1)=[[0]]`, `SNF(d2)=[[1]]`, `SNF(d3)=[[0]]`); ★★ `idempotentSemigroupDegreeOneHomologyIsTrivial`
    (`H1 = 0`, the UNIT invariant-factor `[1]` endpoint) and `idempotentSemigroupDegreeTwoHomologyIsZero`
    (`H2 = 0`); `idempotentSemigroupSmithHandoff` inhabits the SNF interface.
  * **B3 — recovered as an evaluation of the generic carrier**: SHIPPED.
    `idempotentSemigroupWalkerPresentation` + the agreement theorems (all `rfl`) +
    `idempotentSemigroupPresentationIsWellFormed` + `idempotentSemigroupGenericCarrierBoundaryComposesToZero`
    (the fourth instance's `d d = 0` re-derived THROUGH `Homology/WalkerPresentationCarrier`).
  * **B4 — census**: SHIPPED.  `walkersWithComputedHomologyCountAfterIdempotentSemigroup = 4` of `9`.
  * **B5 — this ledger**: SHIPPED.

### Honest scoping

Degrees `0..3`, ONE walker (idempotent semigroup `⟨e | ee ⟹ e⟩`).  Higher degrees are zero
(`idempotentSemigroupBasisCount ≥ 4 = 0`).  The critical-pair enumeration is COMPLETE — ONE critical
pair (`eee`), verified by the systematic width-0/1/2 overlap sweep encoded as DATA
(`idempotentSemigroupCriticalPairCountIsOne` + `allIdempotentSemigroupCriticalPairsExhaustive`).  For
completeness (NOT formalised here): `H0 = ZZ` (`C0 / im d1 = ZZ / 0`) and the degenerate top
`H3 = ker d3 = ZZ` (`d3 = 0`, no `d4`); the requested read-offs are `H1` and `H2`.  The `d d = 0` is
DEGENERATE-BY-ZERO-FACTOR (`d1 = 0`, `d3 = 0`) — HONESTLY not the walking monad's nonzero cancellation;
the distinctive content is that `d2 = [[-1]]` is a UNIT, collapsing `H1` to the trivial group.

### Named future nodes (deferred, decided elsewhere)

  * **The general TOWER-PERIODIC family `⟨s | sⁿ⁺¹ ⟹ id⟩ = ZZ/(n+1)`** — the involution is `n = 1`
    (`ZZ/2`), the cyclic walker `n = 2` (`ZZ/3`).  This file is the `|d2| = 1` UNIT endpoint of the
    invariant-factor spectrum (`ZZ/1 = 0`), reached by the DISTINCT idempotent-semigroup presentation
    `⟨e | ee ⟹ e⟩` (not a member of the `sⁿ⁺¹ ⟹ id` chain, but the same abelianized-`d2` phenomenology).
  * **The walking ADJUNCTION** — NOT convergent at head; its critical-pair layer is the OPEN
    Schanuel–Street node.  Genuinely walled, decided elsewhere. -/

/-- ★ **The idempotent-semigroup homology ledger marker.**  What stands, zero-axiom: the
idempotent-semigroup walker's GENUINE polygraphic chain complex — the single Squier critical pair `eee`
(completeness kernel-checked), the boundaries `d1 = [[0]]`, `d2 = [[-1]]`, `d3 = [[0]]`, machine-checked
`d d = 0`, an inhabited SNF handoff, the fourth-instance recovery through the generic carrier, AND both
homology groups: ★★ `H1(idempotent semigroup) = 0` (the UNIT invariant-factor endpoint,
`idempotentSemigroupDegreeOneHomologyIsTrivial`) and `H2(idempotent semigroup) = 0`
(`idempotentSemigroupDegreeTwoHomologyIsZero`).  Read the meaning from THIS docstring (the honest-record
convention). -/
def idempotentSemigroupHomologyLedgerIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
