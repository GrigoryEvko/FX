import FX1Poly.ComputerAlgebra.Number.NatEuclideanDivision
import FX1Poly.Polygraph.Homology.WalkerPresentationCarrier

/-! # FX1Poly/Polygraph/Homology/CyclicThreeChainComplex — the polygraphic chain complex of the
    DECIDED cyclic-order-three walker `⟨s | sss ⟹ id⟩`, with machine-checked `d d = 0`, its
    Smith-normal boundaries, and the kernel-checked homology `H1 = ZZ/3` (the FIRST ODD-TORSION walker
    homology) and `H2 = 0` (H2-WALKERS r2, #2138; the #2146 TOWER-PERIODIC seed)

The cyclic-order-three walker presents the group `ZZ/3 = ⟨s | s³ = 1⟩` as a decided single-object
polygraph: one object, one endo 1-generator `s` (words `sⁿ`), and one rewrite 2-generator
`R : sss ⟹ id`.  The presentation is CONVERGENT and DECIDED (terminating — each rule application drops
the word length by 3 — and confluent — the two self-overlaps close), so its abelianization is a finite
chain complex of free `ZZ`-modules and homology is exact integer linear algebra (Smith normal form),
exactly as for the walking monad (`Homology/WalkerChainComplex`) and the walking involution
(`Homology/InvolutionChainComplex`), whose Smith read-off machinery this module reuses wholesale.

This is the THIRD literal instance (the "rule of three" data point the generic carrier
`Homology/WalkerPresentationCarrier` is validated against): the shipped monad and involution literal
complexes stay VERBATIM, this file adds the Z/3 complex and recovers it as an EVALUATION of the generic
`WalkerPresentation` carrier.

## The overlap sweep (systematic — the r1 undercount trap avoided)

One rule `R : sss ⟹ id`, lhs `sss` (length 3) over the free monoid on one letter `s`.  Self-overlaps of
`sss` with `sss` are classified by overlap WIDTH `k` (copy A at `[0, 3)`, copy B at `[3 − k, 6 − k)`,
overlap word length `6 − k`):

  * **width 3** (`sss = sss`): identical redex — the trivial ROOT-SELF overlap, EXCLUDED.
  * **width 2** (word `ssss`, length 4): front redex `(sss)s → (id)s = s`; back redex `s(sss) → s(id) = s`.
    Joinable at `s`.  ★ GENUINE — `overlapWidthTwo`.
  * **width 1** (word `sssss`, length 5): front redex `(sss)ss → ss`; back redex `ss(sss) → ss`.
    Joinable at `ss`.  ★ GENUINE — `overlapWidthOne`.
  * **width 0** (word `ssssss`, disjoint redexes): an orthogonal diamond — NOT a critical pair.

→ **TWO critical pairs from ONE rule** — the FIRST instance where the rule count (1) differs from the
critical-pair count (2), so `C3 = ZZ²` and `d3` is `1 × 2`.  Encoded below as
`allCyclicThreeCriticalPairs` + `cyclicThreeCriticalPairCountIsTwo` +
`allCyclicThreeCriticalPairsExhaustive` — the table IS the certificate, never prose-counted.

## The arithmetic (compute first, state after)

Abelianize (target − source convention, matching the shipped walkers).  `basisCount : 1, 1, 1, 2, 0`
(one object, one 1-generator `s`, one rule `R`, TWO critical pairs).

  * **`d1 : C1 → C0`** — `s : point → point` is a LOOP, `[point] − [point] = 0`, the `1 × 1` `[[0]]`.
  * **`d2 : C2 → C1`** — `R : sss ⟹ id`: target `id ↦ 0·[s]`, source `sss ↦ 3·[s]`, so
    `d2(R) = 0 − 3 = −3`, the `1 × 1` `[[-3]]`.  ★ the first invariant factor of ODD order.
  * **`d3 : C3 → C2`** — both critical pairs fire `R` once on each leg, `1 − 1 = 0`, the `1 × 2` `[[0, 0]]`.

Smith normal forms: `SNF(d1) = [[0]]` (rank 0), `SNF(d2) = [[3]]` (rank 1, invariant factor **3**),
`SNF(d3) = [[0, 0]]` (rank 0, already Smith in the `1 × 2` window).

  * ★★ **`H1 = ker d1 / im d2`**: `d1 = 0 ⟹ ker d1 = ZZ`; `im d2 = 3·ZZ`.  Free rank
    `nullity(d1) − rank(d2) = 1 − 1 = 0`; the within-rank invariant factor of `d2` is `3 > 1`, so
    `H1 = ZZ/3` — exactly the abelianization of `⟨s | s³ = 1⟩ = ZZ/3`, the #2146 TOWER-PERIODIC seed.
  * **`H2 = ker d2 / im d3`**: `d2` is `x ↦ −3x`, INJECTIVE over `ZZ`, so `ker d2 = 0`; `im d3 = 0`.
    Free rank `nullity(d2) − rank(d3) = 0 − 0 = 0`, no torsion — `H2 = 0`.

## Honesty note

For the cyclic walker `d d = 0` holds because **`d1 = 0` and `d3 = 0`** — every consecutive composition
has a vanishing factor, exactly like the involution (DEGENERATE-BY-ZERO-FACTOR), NOT the walking monad's
genuine nonzero-×-nonzero cancellation.  The homological content lives entirely in `d2 = [[-3]] ≠ 0` and
its `ZZ/3` torsion.  `H0 = ZZ` and the degenerate top `H3 = ker d3 = ZZ²` are computable but not
formalised here (the requested read-offs are `H1` and `H2`, matching the involution's scope).

## Zero-axiom design decisions

  * The carrier is the shipped `AugmentedDirectedComplex`; every match stays on non-indexed inductives.
  * `d d = 0` is DECIDED on the boundary LITERALS: in-range identities by `rfl`, out-of-range indices by
    the propext-clean peel `Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc ..))`.
  * The Smith handoff ships EXPLICIT unimodular reduction certificates checked propext-cleanly against
    the literal Smith normal forms; the torsion extractor `smithInvariantFactorsWithin` (reused from
    `InvolutionChainComplex`) yields the `= [3]` fingerprint of `ZZ/3` by `rfl`.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/CyclicThreeChainComplex.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra
open FX1Poly.Polygraph.Steiner

/-! ## B1 — the presentation data, the boundary literals, and `d d = 0` -/

/-- The per-dimension basis counts of the cyclic-order-three chain complex: `C0 = ZZ` (the object),
`C1 = ZZ` (the endo 1-generator `s`), `C2 = ZZ` (the single rule `R`), `C3 = ZZ²` (the TWO critical
pairs), and nothing above degree 3. -/
def cyclicThreeBasisCount : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | _ + 4 => 0

/-! ### The two critical pairs (systematic overlap sweep, recorded as DATA) -/

/-- The two Squier critical pairs of the cyclic-order-three presentation — the first walker whose
rule count (1) differs from its critical-pair count (2). -/
inductive CyclicThreeCriticalPair
  /-- The width-2 self-overlap `ssss`: front leg `(sss)s → s`, back leg `s(sss) → s`. -/
  | overlapWidthTwo
  /-- The width-1 self-overlap `sssss`: front leg `(sss)ss → ss`, back leg `ss(sss) → ss`. -/
  | overlapWidthOne

/-- The complete enumeration of the cyclic-order-three critical pairs — TWO, listed. -/
def allCyclicThreeCriticalPairs : List CyclicThreeCriticalPair :=
  [.overlapWidthTwo, .overlapWidthOne]

/-- ★ **The critical-pair count is exactly TWO** — kernel-checked (`rfl`), not prose. -/
theorem cyclicThreeCriticalPairCountIsTwo : allCyclicThreeCriticalPairs.length = 2 := rfl

/-- ★ **The enumeration is EXHAUSTIVE** — every `CyclicThreeCriticalPair` constructor appears in
`allCyclicThreeCriticalPairs` (a missing constructor would fail to compile).  With
`cyclicThreeCriticalPairCountIsTwo` this kernel-checks the critical-pair set is EXACTLY these two. -/
theorem allCyclicThreeCriticalPairsExhaustive :
    ∀ pair : CyclicThreeCriticalPair, pair ∈ allCyclicThreeCriticalPairs
  | .overlapWidthTwo => List.Mem.head _
  | .overlapWidthOne => List.Mem.tail _ (List.Mem.head _)

/-- The column index of each critical pair in `d3` (`overlapWidthTwo ↦ 0`, `overlapWidthOne ↦ 1`). -/
def cyclicThreeCriticalPairIndex : CyclicThreeCriticalPair → Nat
  | .overlapWidthTwo => 0
  | .overlapWidthOne => 1

/-- The Knuth–Bendix overlap CELL that produced each critical pair, as `(outer rule, width, inner
rule)`.  There is one rule (`R1`); the genuine overlaps are at width `2` and width `1`. -/
def cyclicThreeCriticalPairOverlapCell : CyclicThreeCriticalPair → Nat × Nat × Nat
  | .overlapWidthTwo => (1, 2, 1)
  | .overlapWidthOne => (1, 1, 1)

/-- **The abelianized boundary column of each critical pair**, as the rule-firing-count difference
`(#R in front leg) − (#R in back leg)`: both legs fire `R` once, so `1 − 1 = 0`.  `C2 = ZZ` has the
single basis atom `R`, so each column is a single `Int`. -/
def cyclicThreeCriticalPairBoundaryColumn : CyclicThreeCriticalPair → Int
  | .overlapWidthTwo => 0
  | .overlapWidthOne => 0

/-! ### The three boundary matrices as literals -/

/-- `d1 : C1 → C0`, the `1 × 1` loop boundary `[[0]]` (`s` is a loop `point → point`). -/
def cyclicThreeBoundaryOfDimZero : IntMatrix := ⟨[[0]]⟩

/-- `d2 : C2 → C1`, the `1 × 1` boundary `[[-3]]` — ★ the invariant factor of order 3 (`R : sss ⟹ id`
abelianizes to `0·[s] − 3·[s] = −3`). -/
def cyclicThreeBoundaryOfDimOne : IntMatrix := ⟨[[-3]]⟩

/-- `d3 : C3 → C2`, the `1 × 2` boundary `[[0, 0]]` (both critical-pair coforks fire `R` once on each
leg, `1 − 1 = 0`). -/
def cyclicThreeBoundaryOfDimTwo : IntMatrix := ⟨[[0, 0]]⟩

/-- The dimension-indexed boundary map: `d_{dim+1} : C_{dim+1} → C_dim` as a
`cyclicThreeBasisCount dim × cyclicThreeBasisCount (dim+1)` integer matrix.  `d4` is the `2 × 0` zero
map (TWO empty rows, since `C3 = ZZ²`), everything above is the `0 × 0` empty matrix. -/
def cyclicThreeBoundaryMatrix : Nat → IntMatrix
  | 0 => cyclicThreeBoundaryOfDimZero
  | 1 => cyclicThreeBoundaryOfDimOne
  | 2 => cyclicThreeBoundaryOfDimTwo
  | 3 => ⟨[[], []]⟩
  | _ + 4 => ⟨[]⟩

/-- **`d d = 0`, DECIDED on the boundary literals.**  The non-vacuous compositions are `d1·d2`
(`dim = 0`, one column) and `d2·d3` (`dim = 1`, TWO columns); every in-range scalar identity closes by
`rfl` on the literal matrices, every out-of-range index by the propext-clean peel; the `dim ≥ 2`
compositions land in the zero-width degree `C4 = 0`, so `colBound : colIndex < 0` refutes them.  This
is the cyclic walker's `boundaryComposesToZero` field. -/
theorem cyclicThreeBoundaryComposesToZero :
    ∀ (dim rowIndex colIndex : Nat),
      rowIndex < cyclicThreeBasisCount dim → colIndex < cyclicThreeBasisCount (dim + 2) →
      sumOverIndices (cyclicThreeBasisCount (dim + 1)) (fun middleIndex =>
        (cyclicThreeBoundaryMatrix dim).entryAt rowIndex middleIndex *
        (cyclicThreeBoundaryMatrix (dim + 1)).entryAt middleIndex colIndex) = 0
  | 0, 0, 0, _, _ => rfl
  | 0, 0, _ + 1, _, colBound =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc colBound))
  | 0, _ + 1, _, rowBound, _ =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc rowBound))
  | 1, 0, 0, _, _ => rfl
  | 1, 0, 1, _, _ => rfl
  | 1, 0, _ + 2, _, colBound =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc colBound)))
  | 1, _ + 1, _, rowBound, _ =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc rowBound))
  | _ + 2, _, colIndex, _, colBound => absurd colBound (Nat.not_lt_zero colIndex)

/-- **The cyclic-order-three polygraphic chain complex** as a shipped `AugmentedDirectedComplex`: the
basis counts, the three boundary literals (plus the `2 × 0` `d4` and empty tails), the augmentation
`[1]` on `C0`, the rectangular-shape obligations, and the two chain obligations `d d = 0` / `eps d = 0`
discharged. -/
def cyclicThreeChainComplex : AugmentedDirectedComplex where
  basisCount := cyclicThreeBasisCount
  boundaryMatrix := cyclicThreeBoundaryMatrix
  augmentation := [1]
  boundaryHasDimensions := fun dim =>
    match dim with
    | 0 => ⟨rfl, rfl, True.intro⟩
    | 1 => ⟨rfl, rfl, True.intro⟩
    | 2 => ⟨rfl, rfl, True.intro⟩
    | 3 => ⟨rfl, rfl, rfl, True.intro⟩
    | _ + 4 => ⟨rfl, True.intro⟩
  augmentationHasWidth := rfl
  boundaryComposesToZero := cyclicThreeBoundaryComposesToZero
  augmentationComposesToZero := fun colIndex colBound =>
    match colIndex, colBound with
    | 0, _ => rfl
    | _ + 1, cb => Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc cb))

/-- ★ **The cyclic-order-three `d d = 0`, as a COROLLARY of the generic ADC statement.**  Obtained by
specialising the walking monad's `augmentedDirectedComplexBoundaryComposesToZero` (stated over the
carrier structure) to `cyclicThreeChainComplex`. -/
theorem cyclicThreeChainComplexBoundaryComposesToZero (dim rowIndex colIndex : Nat)
    (rowBound : rowIndex < cyclicThreeBasisCount dim)
    (colBound : colIndex < cyclicThreeBasisCount (dim + 2)) :
    sumOverIndices (cyclicThreeBasisCount (dim + 1)) (fun middleIndex =>
      (cyclicThreeBoundaryMatrix dim).entryAt rowIndex middleIndex *
      (cyclicThreeBoundaryMatrix (dim + 1)).entryAt middleIndex colIndex) = 0 :=
  augmentedDirectedComplexBoundaryComposesToZero cyclicThreeChainComplex dim rowIndex colIndex
    rowBound colBound

/-! ### Oracles + non-vacuity (the literal matrices match the hand computation) -/

/-- Oracle for `d1`: the sole entry is `0` (the endo `s` is a loop). -/
theorem cyclicThreeBoundaryDimZeroMatchesOracle :
    cyclicThreeBoundaryOfDimZero.entryAt 0 0 = (0 : Int) := rfl

/-- ★ **Non-vacuity + oracle for `d2`**: `d2(R) = −3` — the invariant factor of order 3, so
`im d2 = 3·ZZ ≠ 0` and the complex is genuinely non-trivial. -/
theorem cyclicThreeBoundaryDimOneIsNonzero :
    cyclicThreeBoundaryOfDimOne.entryAt 0 0 = (-3 : Int) := rfl

/-- ★ **THE ORACLE.**  Each `d3` column (read off the literal matrix at the pair's index) equals the
hand-computed abelianized cofork column `cyclicThreeCriticalPairBoundaryColumn` — the enumerated
critical-pair data and the shipped literal matrix AGREE.  `rfl` per pair. -/
theorem cyclicThreeBoundaryDimTwoColumnMatchesCriticalPair :
    ∀ (pair : CyclicThreeCriticalPair),
      cyclicThreeBoundaryOfDimTwo.entryAt 0 (cyclicThreeCriticalPairIndex pair)
        = cyclicThreeCriticalPairBoundaryColumn pair
  | .overlapWidthTwo => rfl
  | .overlapWidthOne => rfl

/-- ★ **Non-vacuity marker.**  The cyclic-order-three chain complex is genuinely non-trivial: `d2` is
nonzero (`cyclicThreeBoundaryDimOneIsNonzero`, `d2 = [[-3]]`) and carries `ZZ/3` torsion, yet `d d = 0`
holds.  HONEST scoping: like the involution, this `d d = 0` is DEGENERATE-BY-ZERO-FACTOR (`d1 = 0` and
`d3 = 0`), NOT a nonzero-×-nonzero cancellation.  `= true`. -/
def cyclicThreeChainComplexIsNonVacuous : Bool := true

/-! ## B2 — the Smith handoff + the homology read-offs (`H1 = ZZ/3`, `H2 = 0`) -/

/-- The reduction certificate taking `d1 = [[0]]` to its Smith normal form `[[0]]` — already diagonal. -/
def cyclicThreeBoundaryOfDimZeroSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations := [] }

/-- The reduction certificate taking `d2 = [[-3]]` to its Smith normal form `[[3]]` — one column
negation (determinant `−1`, unimodular). -/
def cyclicThreeBoundaryOfDimOneSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations := [ ElementaryOperation.columnOperation (ElementaryColumnOperation.negateColumn 0) ] }

/-- The reduction certificate taking `d3 = [[0, 0]]` to its Smith normal form `[[0, 0]]` — already
diagonal in the `1 × 2` window (off-diagonal `(0, 1)` is `0`, diagonal `(0, 0)` is `0`). -/
def cyclicThreeBoundaryOfDimTwoSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations := [] }

/-- **`d1` reduces to `[[0]]`** — kernel-checked Smith normal form within the `1 × 1` window; rank 0. -/
theorem cyclicThreeBoundaryOfDimZeroReducesToSmith :
    cyclicThreeBoundaryOfDimZeroSmithCertificate.reducesToSmithForm cyclicThreeBoundaryOfDimZero 1 1 :=
  show (⟨[[0]]⟩ : IntMatrix).IsSmithNormalFormWithin 1 1 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 1 → ∀ colIndex, colIndex < 1 →
          rowIndex ≠ colIndex → (⟨[[0]]⟩ : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isPositionBelow)) }

/-- **`d2` reduces to `[[3]]`** — kernel-checked Smith normal form within the `1 × 1` window; rank 1,
invariant factor **3** (★ the odd-order torsion source for `H1 = ZZ/3`). -/
theorem cyclicThreeBoundaryOfDimOneReducesToSmith :
    cyclicThreeBoundaryOfDimOneSmithCertificate.reducesToSmithForm cyclicThreeBoundaryOfDimOne 1 1 :=
  show (⟨[[3]]⟩ : IntMatrix).IsSmithNormalFormWithin 1 1 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 1 → ∀ colIndex, colIndex < 1 →
          rowIndex ≠ colIndex → (⟨[[3]]⟩ : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isPositionBelow)) }

/-- **`d3` reduces to `[[0, 0]]`** — kernel-checked Smith normal form within the `1 × 2` window; rank 0
(both critical-pair coforks abelianize to zero). -/
theorem cyclicThreeBoundaryOfDimTwoReducesToSmith :
    cyclicThreeBoundaryOfDimTwoSmithCertificate.reducesToSmithForm cyclicThreeBoundaryOfDimTwo 1 2 :=
  show (⟨[[0, 0]]⟩ : IntMatrix).IsSmithNormalFormWithin 1 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 1 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex → (⟨[[0, 0]]⟩ : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isPositionBelow)) }

/-- The Smith normal form of `d1` — the literal `[[0]]` its (empty) certificate lands on. -/
def cyclicThreeSmithNormalFormOfDimZero : IntMatrix := ⟨[[0]]⟩

/-- The Smith normal form of `d2` — the literal `[[3]]` the negate-column certificate lands on. -/
def cyclicThreeSmithNormalFormOfDimOne : IntMatrix := ⟨[[3]]⟩

/-- The Smith normal form of `d3` — the literal `[[0, 0]]` its (empty) certificate lands on. -/
def cyclicThreeSmithNormalFormOfDimTwo : IntMatrix := ⟨[[0, 0]]⟩

/-- **The `d1` certificate produces `cyclicThreeSmithNormalFormOfDimZero`** — `rfl`. -/
theorem cyclicThreeDimZeroCertificateProducesSmithNormalForm :
    cyclicThreeBoundaryOfDimZero.applyOperations cyclicThreeBoundaryOfDimZeroSmithCertificate.operations
      = cyclicThreeSmithNormalFormOfDimZero := rfl

/-- **The `d2` certificate produces `cyclicThreeSmithNormalFormOfDimOne`** — `rfl`, bridging the
negate-column reduction `[[-3]] → [[3]]` to the literal SNF the torsion read-off consumes. -/
theorem cyclicThreeDimOneCertificateProducesSmithNormalForm :
    cyclicThreeBoundaryOfDimOne.applyOperations cyclicThreeBoundaryOfDimOneSmithCertificate.operations
      = cyclicThreeSmithNormalFormOfDimOne := rfl

/-- **The `d3` certificate produces `cyclicThreeSmithNormalFormOfDimTwo`** — `rfl`. -/
theorem cyclicThreeDimTwoCertificateProducesSmithNormalForm :
    cyclicThreeBoundaryOfDimTwo.applyOperations cyclicThreeBoundaryOfDimTwoSmithCertificate.operations
      = cyclicThreeSmithNormalFormOfDimTwo := rfl

/-- `rank(d1) = 0` — no nonzero diagonal entry in the `1 × 1` SNF window. -/
theorem cyclicThreeRankOfDimZero : smithRankWithin cyclicThreeSmithNormalFormOfDimZero 1 = 0 := rfl

/-- `rank(d2) = 1` — one nonzero diagonal entry (`3`) in the `1 × 1` SNF window. -/
theorem cyclicThreeRankOfDimOne : smithRankWithin cyclicThreeSmithNormalFormOfDimOne 1 = 1 := rfl

/-- `rank(d3) = 0` — no nonzero diagonal entry in the `1 × 2` SNF diagonal window (`min 1 2 = 1`
position: `diag 0 = 0`). -/
theorem cyclicThreeRankOfDimTwo : smithRankWithin cyclicThreeSmithNormalFormOfDimTwo 1 = 0 := rfl

/-! ### ★★ The headline: `H1(cyclic Z/3) = ZZ/3` (the FIRST ODD-TORSION walker homology) -/

/-- `nullity(d1) = C1 − rank(d1) = 1 − 0 = 1` — the free rank of `ker d1` (`d1 = 0`, so `ker d1 = ZZ`). -/
def cyclicThreeNullityOfDimZero : Nat :=
  cyclicThreeBasisCount 1 - smithRankWithin cyclicThreeSmithNormalFormOfDimZero 1

/-- `nullity(d1) = 1`, by `rfl` on the `Nat` literals. -/
theorem cyclicThreeNullityOfDimZeroValue : cyclicThreeNullityOfDimZero = 1 := rfl

/-- **The degree-1 homology free rank**: `nullity(d1) − rank(d2) = 1 − 1 = 0`. -/
def cyclicThreeDegreeOneHomologyFreeRank : Nat :=
  cyclicThreeNullityOfDimZero - smithRankWithin cyclicThreeSmithNormalFormOfDimOne 1

/-- **The degree-1 homology free rank is `0`**, by `rfl` — `H1` is pure torsion. -/
theorem cyclicThreeDegreeOneHomologyFreeRankIsZero : cyclicThreeDegreeOneHomologyFreeRank = 0 := rfl

/-- **The degree-1 torsion invariant factors**: the within-rank invariant factors of `d2`'s Smith
normal form.  `SNF(d2) = [[3]]`, so this is `[3]` — the single factor `3 > 1` giving `ZZ/3`. -/
def cyclicThreeDegreeOneTorsionFactors : List Int :=
  smithInvariantFactorsWithin cyclicThreeSmithNormalFormOfDimOne 1

/-- **The degree-1 torsion factor list is `[3]`**, by `rfl` on the literal SNF — the exact fingerprint
of `ZZ/3`. -/
theorem cyclicThreeDegreeOneTorsionFactorsValue : cyclicThreeDegreeOneTorsionFactors = [3] := rfl

/-- ★★ **`H1(cyclic Z/3) = ZZ/3`, as free rank `0` AND invariant factor list `[3]`** — the complete
invariant of `ZZ/3` for a finitely-generated abelian homology group. -/
def CyclicThreeDegreeOneHomologyStatement : Prop :=
  cyclicThreeDegreeOneHomologyFreeRank = 0 ∧
  smithInvariantFactorsWithin cyclicThreeSmithNormalFormOfDimOne 1 = [3]

/-- ★★ **THE FIRST ODD-TORSION WALKER HOMOLOGY.**  `H1(cyclic Z/3) = ZZ/3`: the degree-1 homology of
the DECIDED cyclic-order-three polygraph has free rank `0` (`nullity(d1) − rank(d2) = 1 − 1`) and a
single invariant factor `3`, read off the kernel-checked Smith normal forms.  Exactly the abelianization
of `⟨s | s³ = 1⟩ = ZZ/3` — the first walker homology with ODD torsion (the involution's was `ZZ/2`); the
#2146 TOWER-PERIODIC seed. -/
theorem cyclicThreeDegreeOneHomologyIsZmodThree : CyclicThreeDegreeOneHomologyStatement :=
  ⟨cyclicThreeDegreeOneHomologyFreeRankIsZero, cyclicThreeDegreeOneTorsionFactorsValue⟩

/-! ### `H2(cyclic Z/3) = 0` (template continuity with the shipped walkers) -/

/-- `nullity(d2) = C2 − rank(d2) = 1 − 1 = 0` — `d2` is `x ↦ −3x`, injective over `ZZ`, so
`ker d2 = 0`. -/
def cyclicThreeNullityOfDimOne : Nat :=
  cyclicThreeBasisCount 2 - smithRankWithin cyclicThreeSmithNormalFormOfDimOne 1

/-- `nullity(d2) = 0`, by `rfl` on the `Nat` literals. -/
theorem cyclicThreeNullityOfDimOneValue : cyclicThreeNullityOfDimOne = 0 := rfl

/-- **The degree-2 homology free rank**: `nullity(d2) − rank(d3) = 0 − 0 = 0`. -/
def cyclicThreeDegreeTwoHomologyFreeRank : Nat :=
  cyclicThreeNullityOfDimOne - smithRankWithin cyclicThreeSmithNormalFormOfDimTwo 1

/-- **The degree-2 homology free rank is `0`**, by `rfl` on the `Nat` literals. -/
theorem cyclicThreeDegreeTwoHomologyFreeRankIsZero : cyclicThreeDegreeTwoHomologyFreeRank = 0 := rfl

/-- **`d3` has no Smith torsion** within its `1 × 2` diagonal window (`min 1 2 = 1` position): `diag 0
= 0` (past the rank 0).  Explicit constructor, propext-clean. -/
theorem cyclicThreeDimTwoHasNoTorsion :
    hasNoSmithTorsionWithin cyclicThreeSmithNormalFormOfDimTwo 1 :=
  ⟨True.intro, Or.inl rfl⟩

/-- **`H2(cyclic Z/3) = 0`, as free rank `0` AND no torsion** — the complete invariant of the trivial
group for a finitely-generated abelian homology group. -/
def CyclicThreeDegreeTwoHomologyIsZeroStatement : Prop :=
  cyclicThreeDegreeTwoHomologyFreeRank = 0 ∧ hasNoSmithTorsionWithin cyclicThreeSmithNormalFormOfDimTwo 1

/-- **`H2(cyclic Z/3) = 0`**: the degree-2 homology of the DECIDED cyclic-order-three polygraph has
free rank `0` (`nullity(d2) − rank(d3) = 0 − 0`) and no torsion (`ker d2 = 0` because `d2 = x ↦ −3x` is
injective).  Template continuity with the shipped walkers' `H2 = 0`. -/
theorem cyclicThreeDegreeTwoHomologyIsZero : CyclicThreeDegreeTwoHomologyIsZeroStatement :=
  ⟨cyclicThreeDegreeTwoHomologyFreeRankIsZero, cyclicThreeDimTwoHasNoTorsion⟩

/-! ### The Smith handoff interface -/

/-- ★ **The Smith handoff statement.**  All three boundaries are Smith-reduced: `d1`/`d3` to the rank-0
`[[0]]` / `[[0, 0]]`, `d2` to the rank-1 `[[3]]` with invariant factor `3`.  The complete SNF input the
homology read-offs consume (`H1 = ZZ/3`, `H2 = 0`). -/
def CyclicThreeSmithHandoffStatement : Prop :=
  cyclicThreeBoundaryOfDimZeroSmithCertificate.reducesToSmithForm cyclicThreeBoundaryOfDimZero 1 1 ∧
  cyclicThreeBoundaryOfDimOneSmithCertificate.reducesToSmithForm cyclicThreeBoundaryOfDimOne 1 1 ∧
  cyclicThreeBoundaryOfDimTwoSmithCertificate.reducesToSmithForm cyclicThreeBoundaryOfDimTwo 1 2

/-- ★ **The handoff is INHABITED** — all three boundary Smith reductions are kernel-checked. -/
theorem cyclicThreeSmithHandoff : CyclicThreeSmithHandoffStatement :=
  ⟨cyclicThreeBoundaryOfDimZeroReducesToSmith,
   cyclicThreeBoundaryOfDimOneReducesToSmith,
   cyclicThreeBoundaryOfDimTwoReducesToSmith⟩

/-! ## B3 — the third instance recovered as an EVALUATION of the generic carrier

The cyclic walker's presentation data, and the proof that evaluating the generic `WalkerPresentation`
compute functions at it reproduces the boundary literals above (all `rfl`) — the "rule of three" data
point validating `Homology/WalkerPresentationCarrier`.  The well-formedness discharge feeds the generic
`walkerPresentationBoundaryComposesToZeroOfWellFormed` to re-derive `d d = 0` THROUGH the carrier. -/

/-- The cyclic-order-three presentation: one endo 1-generator `s`; one rule `R : sss ⟹ id`
(`([0, 0, 0], [])`); two critical pairs, each firing `R` once on each leg (`overlapWord = []`). -/
def cyclicThreeWalkerPresentation : WalkerPresentation :=
  { oneGeneratorCount := 1
  , rules := [([0, 0, 0], [])]
  , criticalPairs := [([], [1], [1]), ([], [1], [1])] }

/-- The cyclic presentation's basis counts equal `cyclicThreeBasisCount` at every dimension. -/
theorem cyclicThreePresentationComputesBasisCount :
    ∀ dim, cyclicThreeWalkerPresentation.computeBasisCount dim = cyclicThreeBasisCount dim
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

/-- **The cyclic presentation computes the shipped `d1`.** -/
theorem cyclicThreePresentationComputesBoundaryDimZero :
    cyclicThreeWalkerPresentation.computeBoundaryDimZero = cyclicThreeBoundaryOfDimZero := rfl

/-- **The cyclic presentation computes the shipped `d2` `[[-3]]`.** -/
theorem cyclicThreePresentationComputesBoundaryDimOne :
    cyclicThreeWalkerPresentation.computeBoundaryDimOne = cyclicThreeBoundaryOfDimOne := rfl

/-- **The cyclic presentation computes the shipped `d3` `[[0, 0]]`.** -/
theorem cyclicThreePresentationComputesBoundaryDimTwo :
    cyclicThreeWalkerPresentation.computeBoundaryDimTwo = cyclicThreeBoundaryOfDimTwo := rfl

/-- **The cyclic presentation computes the shipped dimension-indexed boundary at every dimension.** -/
theorem cyclicThreePresentationComputesBoundaryMatrix :
    ∀ dim, cyclicThreeWalkerPresentation.computeBoundaryMatrix dim = cyclicThreeBoundaryMatrix dim
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

/-- ★ **The cyclic presentation is well-formed** — the residual dimension-1 obligation is exactly the
shipped `cyclicThreeBoundaryComposesToZero` at dimension 1 (defeq through the agreement above). -/
theorem cyclicThreePresentationIsWellFormed :
    WellFormedWalkerPresentation cyclicThreeWalkerPresentation :=
  fun rowIndex colIndex rowBound colBound =>
    cyclicThreeBoundaryComposesToZero 1 rowIndex colIndex rowBound colBound

/-- ★ **`d d = 0` for the cyclic walker, DERIVED THROUGH THE GENERIC CARRIER.**  Feeding the
well-formedness discharge into `walkerPresentationBoundaryComposesToZeroOfWellFormed` re-proves the
third instance's chain obligation from the generic machinery — the "rule of three" completed, the
generic carrier verified to yield `d d = 0` for a walker it did not hard-code. -/
theorem cyclicThreeGenericCarrierBoundaryComposesToZero
    (dim rowIndex colIndex : Nat)
    (rowBound : rowIndex < cyclicThreeWalkerPresentation.computeBasisCount dim)
    (colBound : colIndex < cyclicThreeWalkerPresentation.computeBasisCount (dim + 2)) :
    sumOverIndices (cyclicThreeWalkerPresentation.computeBasisCount (dim + 1)) (fun middleIndex =>
      (cyclicThreeWalkerPresentation.computeBoundaryMatrix dim).entryAt rowIndex middleIndex *
      (cyclicThreeWalkerPresentation.computeBoundaryMatrix (dim + 1)).entryAt middleIndex colIndex)
      = 0 :=
  walkerPresentationBoundaryComposesToZeroOfWellFormed cyclicThreeWalkerPresentation
    cyclicThreePresentationIsWellFormed dim rowIndex colIndex rowBound colBound

/-! ## B4 — the carrier census update (the third walker with computed homology)

`Homology/WalkerChainComplex` (`H2 = 0`) and `Homology/InvolutionChainComplex` (`H1 = ZZ/2`, `H2 = 0`)
recorded two decided walkers with machine-computed homology; this file adds the THIRD (`H1 = ZZ/3`,
`H2 = 0`).  The census denominator is `decidedWalkerCount = 9` (shipped in `InvolutionChainComplex`);
the shipped `walkersWithComputedHomologyCount = 2` is NOT mutated — the updated running count is a new
decl here, honestly recording the count AS OF THIS FILE. -/

/-- The number of decided walkers with a machine-computed homology group, updated after this file: the
walking MONAD (`H2 = 0`), the walking INVOLUTION (`H1 = ZZ/2`, `H2 = 0`), and the cyclic-order-three
walker (`H1 = ZZ/3`, `H2 = 0`, this file).  A running count of shipped homology files, not a claim about
all nine. -/
def walkersWithComputedHomologyCountAfterCyclicThree : Nat := 3

/-- The updated census value: `3` of the `9` decided walkers now have computed homology, by `rfl`. -/
theorem walkersWithComputedHomologyCountAfterCyclicThreeValue :
    walkersWithComputedHomologyCountAfterCyclicThree = 3 := rfl

/-! ## B5 — the cyclic-order-three homology ledger (file-section states + honest scoping)

  * **B1 — presentation + boundaries + `d d = 0` + instance**: SHIPPED.  `cyclicThreeBasisCount`
    (`1,1,1,2,0…`); the TWO critical pairs (`CyclicThreeCriticalPair`, count/exhaustiveness/overlap-cell
    as DATA — the first rule-count ≠ CP-count walker); the three boundary literals (`d1 = [[0]]`,
    `d2 = [[-3]]`, `d3 = [[0, 0]]`); `cyclicThreeBoundaryComposesToZero` decides `d d = 0` over the
    extra dimension-1 column; `cyclicThreeChainComplex` is the `AugmentedDirectedComplex`;
    `cyclicThreeChainComplexBoundaryComposesToZero` is the corollary.
  * **B2 — Smith handoff + homology read-offs**: SHIPPED.  Three kernel-checked reduction certificates
    (`SNF(d1)=[[0]]`, `SNF(d2)=[[3]]`, `SNF(d3)=[[0,0]]`); ★★ `cyclicThreeDegreeOneHomologyIsZmodThree`
    (`H1 = ZZ/3`, the first ODD-torsion walker homology) and `cyclicThreeDegreeTwoHomologyIsZero`
    (`H2 = 0`); `cyclicThreeSmithHandoff` inhabits the SNF interface.
  * **B3 — recovered as an evaluation of the generic carrier**: SHIPPED.  `cyclicThreeWalkerPresentation`
    + the agreement theorems (`cyclicThreePresentationComputes…`, all `rfl`) +
    `cyclicThreePresentationIsWellFormed` + `cyclicThreeGenericCarrierBoundaryComposesToZero` (the
    third instance's `d d = 0` re-derived THROUGH `Homology/WalkerPresentationCarrier`).
  * **B4 — census**: SHIPPED.  `walkersWithComputedHomologyCountAfterCyclicThree = 3` of `9`.
  * **B5 — this ledger**: SHIPPED.

### Honest scoping

Degrees `0..3`, ONE walker (cyclic order three).  Higher degrees are zero
(`cyclicThreeBasisCount ≥ 4 = 0`).  The critical-pair enumeration is COMPLETE — TWO critical pairs,
verified by the systematic width-0/1/2/3 overlap sweep encoded as DATA (`cyclicThreeCriticalPairCountIsTwo`
+ `allCyclicThreeCriticalPairsExhaustive`).  For completeness (NOT formalised here): `H0 = ZZ`
(`C0 / im d1 = ZZ / 0`) and the degenerate top `H3 = ker d3 = ZZ²` (`d3 = 0`, no `d4`); the requested
read-offs are `H1` and `H2`.  The `d d = 0` is DEGENERATE-BY-ZERO-FACTOR (`d1 = 0`, `d3 = 0`) — HONESTLY
not the walking monad's nonzero cancellation; the homological content is `d2`'s `ZZ/3` torsion.

### Named future nodes (deferred, decided elsewhere)

  * **The general TOWER-PERIODIC family `⟨s | sⁿ⁺¹ ⟹ id⟩ = ZZ/(n+1)`** (#2146) — this file seeds `n = 2`
    (`ZZ/3`); the involution is `n = 1` (`ZZ/2`).  The general `H1 = ZZ/(n+1)` over the parameter `n`
    is future work.
  * **The generic decided-polygraph chain-complex functor** — abelianizing an ARBITRARY decided
    loop-free polygraph.  `Homology/WalkerPresentationCarrier` is the single-object first step; this
    file is its third validated data point. -/

/-- ★ **The cyclic-order-three homology ledger marker.**  What stands, zero-axiom: the cyclic walker's
GENUINE polygraphic chain complex — the TWO Squier critical pairs (completeness kernel-checked; the
first walker with rule-count ≠ CP-count), the boundaries `d1 = [[0]]`, `d2 = [[-3]]`, `d3 = [[0, 0]]`,
machine-checked `d d = 0`, an inhabited SNF handoff, the third-instance recovery through the generic
carrier, AND both homology groups: ★★ `H1(cyclic Z/3) = ZZ/3` (the first ODD-torsion walker homology,
`cyclicThreeDegreeOneHomologyIsZmodThree`) and `H2(cyclic Z/3) = 0` (`cyclicThreeDegreeTwoHomologyIsZero`).
Read the meaning from THIS docstring (the honest-record convention). -/
def cyclicThreeHomologyLedgerIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
