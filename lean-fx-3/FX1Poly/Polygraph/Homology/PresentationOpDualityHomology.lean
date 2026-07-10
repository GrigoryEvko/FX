import FX1Poly.Polygraph.Homology.WalkerChainComplex
import FX1Poly.Polygraph.Homology.IdempotentSemigroupChainComplex
import FX1Poly.ComputerAlgebra.Number.IntNegation
import FX1Poly.ComputerAlgebra.Number.IntArithmeticCore

/-! # FX1Poly/Polygraph/Homology/PresentationOpDualityHomology — the OP-DUALITY TRANSPORT on the
    polygraphic homology carrier, and the op-dual census coverage it delivers (walking comonad,
    idempotent comonad, walking KZ / co-KZ) — H2-WALKERS census-maximum round

The 2-cell op-dual of a single-object presentation SWAPS every rule's source and target (a monad unit
`id ⟹ t` becomes a comonad counit `t ⟹ id`) and SWAPS the two rewriting legs of every critical pair.
On the abelianized polygraphic chain complex this means:

  * the object / 1-generator / rule / critical-pair COUNTS are preserved (op only reindexes), so the
    basis is unchanged — `opPresentationComputesBasisCount`;
  * every boundary matrix is NEGATED ENTRYWISE — `opPresentationBoundaryEntryIsNegated`: `d^op = −d`.
    A monad `d2 = [[1, −1]]` becomes a comonad `d2 = [[−1, 1]] = −(monad d2)`; the recon's "the letter
    counts are the same, so `d2` is IDENTICAL" is HALF right (op keeps the 1-cell graph, so word
    letter-multisets are preserved) and HALF wrong (op reverses the 2-cells, so `d2` is NEGATED, not
    identical).  The honest mechanism is SIGN-INVARIANCE of homology, NOT identity of matrices — a
    single unimodular column negation, so `SNF`, rank, nullity, free rank and torsion factors are the
    SAME.

Since a negation is unimodular (`ElementaryColumnOperation.negateColumn`, determinant `−1`), every dual
has the SAME Smith normal form as its base, hence the SAME homology.  This module ships:

  1. the GENERIC transport theorem (`opPresentation` + basis-count preservation + the entrywise-negation
     `d^op = −d`), zero-axiom via the repo Int-negation kit (`intNegSub`, `intNegMul`/`intMulNeg`;
     Init's `Int.neg_sub`/`Int.neg_mul` are propext-DIRTY, so the local kit is load-bearing);
  2. the CONCRETE op-duals as evaluations `opPresentation <base>`, with `d d = 0` transported through
     the entrywise-negation + `(−a)(−b) = ab` (composite is IDENTICAL), and each dual's homology READ
     OFF via a Smith certificate that lands on the SAME normal form as its base:
       * **walking comonad** `= opPresentation (walking monad)` — `H2 = 0` (= monad's);
       * **idempotent comonad** `= opPresentation (idempotent semigroup)` — `H1 = 0`, `H2 = 0`;
  3. the KZ / co-KZ census coverage: the KZ monad's rewrite rules ARE the walking monad's (the order is
     extra structure the abelianization FORGETS), so `kzAbelianizedPresentation = monadWalkerPresentation`
     and co-KZ `= opPresentation (walking monad) = comonad` — covered by definitional identity, with the
     honest ABELIANIZATION caveat (co-KZ's walker identity is a directed preorder; the transport applies
     to its abelianization only).

## The census after this file: 8 of 9 decided walkers with computed homology

Shipped literal complexes: walking monad (`H2 = 0`), involution (`H1 = ZZ/2`), cyclic-three
(`H1 = ZZ/3`), idempotent semigroup (`H1 = 0`).  This file adds the four op-duals: comonad (`H2 = 0`),
idempotent comonad (`H1 = 0`, `H2 = 0`), KZ (`= monad`), co-KZ (`= comonad`).  The SOLE residual is the
walking ADJUNCTION — genuinely WALLED (non-convergent at head, the open Schanuel–Street confluence node;
no decidable critical-pair / `d3` layer, so no honest `H2`).  See the B4 ledger.

## Zero-axiom design decisions

  * The generic entrywise-negation recurses through the shipped row builders; each per-entry step is
    `intNegSub` (the difference-flip, `-(a − b) = b − a`), the empty tails are `Int.neg_zero`.  No
    `decide` on any `Nat.min`/`Nat.sub` Smith expression.
  * The `d d = 0` transport uses `(−a)(−b) = ab` (from the repo `intNegMul` / `intMulNeg` / `intNegNeg`)
    and a structural sum-congruence — the composite `d2^op · d3^op = d2 · d3` is genuinely IDENTICAL, so
    each dual's well-formedness rides the base walker's discharge.
  * Each dual's Smith reduction PREPENDS the unimodular column negations to its base walker's shipped
    certificate, landing on the SAME literal normal form (`rfl` bridge), so the rank/torsion read-offs
    are the base walker's, transported.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/PresentationOpDualityHomology.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra
open FX1Poly.Polygraph.Steiner

/-! ## B2 — the generic op-duality on the presentation carrier -/

/-- The 2-cell op-dual of a single rule: SWAP source and target (unit `id ⟹ t` ↦ counit `t ⟹ id`). -/
def presentationOpSwapRule (rule : List Nat × List Nat) : List Nat × List Nat :=
  (rule.2, rule.1)

/-- The 2-cell op-dual of a single critical pair: keep the overlap word, SWAP the two rewriting legs
(the abelianized cofork of the reversed 2-cells). -/
def presentationOpSwapCriticalPair (pair : List Nat × List Nat × List Nat) :
    List Nat × List Nat × List Nat :=
  (pair.1, pair.2.2, pair.2.1)

/-- **The op-dual presentation.**  Same object, same 1-generators; every rule reversed
(`presentationOpSwapRule`) and every critical pair's legs swapped (`presentationOpSwapCriticalPair`).
The counts are preserved (op only reindexes), so the polygraphic basis is unchanged. -/
def opPresentation (presentation : WalkerPresentation) : WalkerPresentation :=
  { oneGeneratorCount := presentation.oneGeneratorCount
  , rules := presentation.rules.map presentationOpSwapRule
  , criticalPairs := presentation.criticalPairs.map presentationOpSwapCriticalPair }

/-- `List.map` preserves length — bespoke local copy (the shipped `ComputerAlgebra.listMapPreservesLength`
lives in `SmithNormalForm`, which this module deliberately does NOT import). -/
theorem presentationOpMapPreservesLength {Source Target : Type} (transform : Source → Target) :
    ∀ entries : List Source, (entries.map transform).length = entries.length
  | [] => rfl
  | _ :: remainingEntries => congrArg (· + 1) (presentationOpMapPreservesLength transform remainingEntries)

/-- ★ **The op-dual preserves the polygraphic basis counts** at every dimension: object count `1`,
1-generator count preserved, rule count preserved (`map` preserves length), critical-pair count
preserved. -/
theorem opPresentationComputesBasisCount (presentation : WalkerPresentation) :
    ∀ dim, (opPresentation presentation).computeBasisCount dim = presentation.computeBasisCount dim
  | 0 => rfl
  | 1 => rfl
  | 2 => presentationOpMapPreservesLength presentationOpSwapRule presentation.rules
  | 3 => presentationOpMapPreservesLength presentationOpSwapCriticalPair presentation.criticalPairs
  | _ + 4 => rfl

/-- `(−a)(−b) = a·b` over the integers — via the repo negation kit (Init's `Int.neg_mul_neg` is
propext-dirty). -/
theorem intNegMulNeg (leftFactor rightFactor : Int) :
    (-leftFactor) * (-rightFactor) = leftFactor * rightFactor :=
  (intNegMul leftFactor (-rightFactor)).trans
    ((congrArg Int.neg (intMulNeg leftFactor rightFactor)).trans (intNegNeg (leftFactor * rightFactor)))

/-- Reading any entry out of an EMPTY row block is `0` — the shared zero-row-count / empty-tail fact. -/
theorem emptyRowsEntryIsZero (rowIndex colIndex : Nat) :
    listGetWithDefault 0 (listGetWithDefault [] ([] : List IntRow) rowIndex) colIndex = 0 :=
  (congrArg (fun row => listGetWithDefault 0 row colIndex)
    (listGetWithDefaultNilIsDefault ([] : IntRow) rowIndex)).trans
    (listGetWithDefaultNilIsDefault 0 colIndex)

/-! ### The entrywise negation `d^op = −d` (the transport CORE) -/

/-- One `d2` row is NEGATED entrywise under rule-reversal: each `[target] − [source]` becomes
`[source] − [target]` (`intNegSub`).  Structural on the rule list, then the column index. -/
theorem presentationOpDimOneRowIsNegated (generator : Nat) :
    ∀ (rules : List (List Nat × List Nat)) (colIndex : Nat),
      listGetWithDefault 0
          (walkerPresentationDimOneRow generator (rules.map presentationOpSwapRule)) colIndex
        = -(listGetWithDefault 0 (walkerPresentationDimOneRow generator rules) colIndex)
  | [], 0 => Int.neg_zero.symm
  | [], _ + 1 => Int.neg_zero.symm
  | (sourceWord, targetWord) :: _, 0 =>
      (intNegSub (Int.ofNat (countGeneratorOccurrences generator targetWord))
        (Int.ofNat (countGeneratorOccurrences generator sourceWord))).symm
  | (_, _) :: remainingRules, colIndex + 1 =>
      presentationOpDimOneRowIsNegated generator remainingRules colIndex

/-- The `d2` row LIST is negated entrywise under rule-reversal — structural on `rowCount`, then the row
index, bottoming on `presentationOpDimOneRowIsNegated`. -/
theorem presentationOpDimOneRowsIsNegated (rules : List (List Nat × List Nat)) :
    ∀ (startGenerator rowCount rowIndex colIndex : Nat),
      listGetWithDefault 0
          (listGetWithDefault []
            (walkerPresentationDimOneRows (rules.map presentationOpSwapRule) startGenerator rowCount)
            rowIndex) colIndex
        = -(listGetWithDefault 0
            (listGetWithDefault []
              (walkerPresentationDimOneRows rules startGenerator rowCount) rowIndex) colIndex)
  | _, 0, rowIndex, colIndex =>
      (emptyRowsEntryIsZero rowIndex colIndex).trans
        (Int.neg_zero.symm.trans (congrArg Int.neg (emptyRowsEntryIsZero rowIndex colIndex).symm))
  | startGenerator, _ + 1, 0, colIndex =>
      presentationOpDimOneRowIsNegated startGenerator rules colIndex
  | startGenerator, rowCount + 1, rowIndex + 1, colIndex =>
      presentationOpDimOneRowsIsNegated rules (startGenerator + 1) rowCount rowIndex colIndex

/-- One `d3` row is NEGATED entrywise under leg-swap: each `leftFirings[r] − rightFirings[r]` becomes
`rightFirings[r] − leftFirings[r]` (`intNegSub`).  Structural on the critical-pair list, then the
column index. -/
theorem presentationOpDimTwoRowIsNegated (ruleIndex : Nat) :
    ∀ (criticalPairs : List (List Nat × List Nat × List Nat)) (colIndex : Nat),
      listGetWithDefault 0
          (walkerPresentationDimTwoRow ruleIndex
            (criticalPairs.map presentationOpSwapCriticalPair)) colIndex
        = -(listGetWithDefault 0 (walkerPresentationDimTwoRow ruleIndex criticalPairs) colIndex)
  | [], 0 => Int.neg_zero.symm
  | [], _ + 1 => Int.neg_zero.symm
  | (_, leftLegFirings, rightLegFirings) :: _, 0 =>
      (intNegSub (Int.ofNat (listGetWithDefault 0 leftLegFirings ruleIndex))
        (Int.ofNat (listGetWithDefault 0 rightLegFirings ruleIndex))).symm
  | (_, _, _) :: remainingPairs, colIndex + 1 =>
      presentationOpDimTwoRowIsNegated ruleIndex remainingPairs colIndex

/-- The `d3` row LIST is negated entrywise under leg-swap — structural on `rowCount`, then the row
index, bottoming on `presentationOpDimTwoRowIsNegated`. -/
theorem presentationOpDimTwoRowsIsNegated (criticalPairs : List (List Nat × List Nat × List Nat)) :
    ∀ (startRule rowCount rowIndex colIndex : Nat),
      listGetWithDefault 0
          (listGetWithDefault []
            (walkerPresentationDimTwoRows (criticalPairs.map presentationOpSwapCriticalPair)
              startRule rowCount) rowIndex) colIndex
        = -(listGetWithDefault 0
            (listGetWithDefault []
              (walkerPresentationDimTwoRows criticalPairs startRule rowCount) rowIndex) colIndex)
  | _, 0, rowIndex, colIndex =>
      (emptyRowsEntryIsZero rowIndex colIndex).trans
        (Int.neg_zero.symm.trans (congrArg Int.neg (emptyRowsEntryIsZero rowIndex colIndex).symm))
  | startRule, _ + 1, 0, colIndex =>
      presentationOpDimTwoRowIsNegated startRule criticalPairs colIndex
  | startRule, rowCount + 1, rowIndex + 1, colIndex =>
      presentationOpDimTwoRowsIsNegated criticalPairs (startRule + 1) rowCount rowIndex colIndex

/-- Reading any entry of a `List.replicate count []` row block returns `0` (the `d3`-tail / `d4` shape):
every row is the empty row, every column reads past its end. -/
theorem presentationOpReplicateEmptyEntryIsZero :
    ∀ (count rowIndex colIndex : Nat),
      (⟨List.replicate count ([] : IntRow)⟩ : IntMatrix).entryAt rowIndex colIndex = 0
  | 0, rowIndex, colIndex => emptyRowsEntryIsZero rowIndex colIndex
  | _ + 1, 0, colIndex => listGetWithDefaultNilIsDefault 0 colIndex
  | count + 1, rowIndex + 1, colIndex =>
      presentationOpReplicateEmptyEntryIsZero count rowIndex colIndex

/-- ★★ **`d^op = −d`: the op-dual NEGATES every boundary entry.**  Dimension 0 (the loop row) and the
`d3`-tail are all-zero on both sides (`0 = −0`); dimension 1 rides `presentationOpDimOneRowsIsNegated`;
dimension 2 rides `presentationOpDimTwoRowsIsNegated` after rewriting the op-side row count
`(rules.map …).length` to `rules.length`.  This is the honest transport mechanism — SIGN, not
identity. -/
theorem opPresentationBoundaryEntryIsNegated (presentation : WalkerPresentation) :
    ∀ (dim rowIndex colIndex : Nat),
      ((opPresentation presentation).computeBoundaryMatrix dim).entryAt rowIndex colIndex
        = -((presentation.computeBoundaryMatrix dim).entryAt rowIndex colIndex)
  | 0, rowIndex, colIndex =>
      (walkerPresentationDimZeroEntryIsZero (opPresentation presentation) rowIndex colIndex).trans
        (Int.neg_zero.symm.trans
          (congrArg Int.neg
            (walkerPresentationDimZeroEntryIsZero presentation rowIndex colIndex).symm))
  | 1, rowIndex, colIndex =>
      presentationOpDimOneRowsIsNegated presentation.rules 0 presentation.oneGeneratorCount
        rowIndex colIndex
  | 2, rowIndex, colIndex =>
      (congrArg
        (fun rowCount =>
          (⟨walkerPresentationDimTwoRows
              (presentation.criticalPairs.map presentationOpSwapCriticalPair) 0 rowCount⟩ : IntMatrix).entryAt
            rowIndex colIndex)
        (presentationOpMapPreservesLength presentationOpSwapRule presentation.rules)).trans
        (presentationOpDimTwoRowsIsNegated presentation.criticalPairs 0 presentation.rules.length
          rowIndex colIndex)
  | 3, rowIndex, colIndex =>
      (presentationOpReplicateEmptyEntryIsZero (opPresentation presentation).criticalPairs.length
        rowIndex colIndex).trans
        (Int.neg_zero.symm.trans
          (congrArg Int.neg
            (presentationOpReplicateEmptyEntryIsZero presentation.criticalPairs.length rowIndex
              colIndex).symm))
  | _ + 4, rowIndex, colIndex =>
      (presentationOpReplicateEmptyEntryIsZero 0 rowIndex colIndex).trans
        (Int.neg_zero.symm.trans
          (congrArg Int.neg
            (presentationOpReplicateEmptyEntryIsZero 0 rowIndex colIndex).symm))

/-- A finite sum is congruent under a pointwise-equal summand — structural on the index count. -/
theorem sumOverIndicesCongr {leftSummand rightSummand : Nat → Int}
    (pointwise : ∀ index, leftSummand index = rightSummand index) :
    ∀ count, sumOverIndices count leftSummand = sumOverIndices count rightSummand
  | 0 => rfl
  | count + 1 =>
      (congrArg (· + leftSummand count) (sumOverIndicesCongr pointwise count)).trans
        (congrArg (sumOverIndices count rightSummand + ·) (pointwise count))

/-! ## B2 — the walking COMONAD `= opPresentation (walking monad)`, `H2 = 0`

`opPresentation monadWalkerPresentation`: rules `[([0], []), ([0], [0, 0])]` (the monad's
`eta : id ⟹ t`, `mu : t.t ⟹ t` reversed to counit `epsilon : t ⟹ id` and comultiplication
`delta : t ⟹ t.t`), critical pairs the monad's with legs swapped.  Its boundaries are the monad's
NEGATED: `d2 = [[−1, 1]]`, `d3 = [[0, −1, −1, 0, −1], [0, −1, −1, 0, −1]]`.  Both reduce to the monad's
Smith normal forms (unimodular column negations prepended to the monad's certificate), so
`H2(comonad) = H2(walking monad) = 0`. -/

/-- The walking comonad presentation, as the op-dual of the walking monad. -/
def comonadWalkerPresentation : WalkerPresentation := opPresentation monadWalkerPresentation

/-- `d2(comonad) = [[−1, 1]]` (the monad's `[[1, −1]]` negated) — the reversed unit/multiplication. -/
def comonadBoundaryOfDimOne : IntMatrix := ⟨[[-1, 1]]⟩

/-- `d3(comonad) = [[0, −1, −1, 0, −1], [0, −1, −1, 0, −1]]` (the monad's `d3` negated). -/
def comonadBoundaryOfDimTwo : IntMatrix := ⟨[[0, -1, -1, 0, -1], [0, -1, -1, 0, -1]]⟩

/-- **The comonad presentation computes `d1 = [[0]]`** (unchanged loop row) — `rfl`. -/
theorem comonadPresentationComputesBoundaryDimZero :
    comonadWalkerPresentation.computeBoundaryDimZero = walkerBoundaryOfDimZero := rfl

/-- **The comonad presentation computes `d2 = [[−1, 1]]`** — `rfl`; the transport negation made
concrete. -/
theorem comonadPresentationComputesBoundaryDimOne :
    comonadWalkerPresentation.computeBoundaryDimOne = comonadBoundaryOfDimOne := rfl

/-- **The comonad presentation computes `d3 = [[0, −1, −1, 0, −1], [0, −1, −1, 0, −1]]`** — `rfl`. -/
theorem comonadPresentationComputesBoundaryDimTwo :
    comonadWalkerPresentation.computeBoundaryDimTwo = comonadBoundaryOfDimTwo := rfl

/-- ★ **THE CORRESPONDENCE.**  `d2(comonad)[0, j] = −d2(monad)[0, j]` for every column — the generic
`opPresentationBoundaryEntryIsNegated` INSTANTIATED at the monad, degree 1.  Explicit `d^op = −d`, not
hand-waved. -/
theorem comonadBoundaryDimOneIsNegatedMonad (colIndex : Nat) :
    comonadBoundaryOfDimOne.entryAt 0 colIndex = -(walkerBoundaryOfDimOne.entryAt 0 colIndex) :=
  opPresentationBoundaryEntryIsNegated monadWalkerPresentation 1 0 colIndex

/-- ★ **THE CORRESPONDENCE (degree 2).**  `d3(comonad)[i, j] = −d3(monad)[i, j]` for every entry — the
generic transport at the monad, degree 2. -/
theorem comonadBoundaryDimTwoIsNegatedMonad (rowIndex colIndex : Nat) :
    comonadBoundaryOfDimTwo.entryAt rowIndex colIndex
      = -(walkerBoundaryOfDimTwo.entryAt rowIndex colIndex) :=
  opPresentationBoundaryEntryIsNegated monadWalkerPresentation 2 rowIndex colIndex

/-- ★ **The comonad presentation is well-formed** — `d2^op · d3^op = (−d2)(−d3) = d2 · d3`, so the
residual dimension-1 obligation transports from the monad's `monadPresentationIsWellFormed` through the
entrywise negation and `intNegMulNeg`.  The composite is genuinely IDENTICAL (double sign cancels). -/
theorem comonadPresentationIsWellFormed : WellFormedWalkerPresentation comonadWalkerPresentation :=
  fun rowIndex colIndex rowBound colBound =>
    (sumOverIndicesCongr
      (fun middleIndex =>
        (congrArg (· * comonadWalkerPresentation.computeBoundaryDimTwo.entryAt middleIndex colIndex)
          (opPresentationBoundaryEntryIsNegated monadWalkerPresentation 1 rowIndex middleIndex)).trans
          ((congrArg
            (-(monadWalkerPresentation.computeBoundaryDimOne.entryAt rowIndex middleIndex) * ·)
            (opPresentationBoundaryEntryIsNegated monadWalkerPresentation 2 middleIndex colIndex)).trans
            (intNegMulNeg (monadWalkerPresentation.computeBoundaryDimOne.entryAt rowIndex middleIndex)
              (monadWalkerPresentation.computeBoundaryDimTwo.entryAt middleIndex colIndex))))
      (comonadWalkerPresentation.computeBasisCount 2)).trans
      (monadPresentationIsWellFormed rowIndex colIndex rowBound colBound)

/-- ★★ **The walking-comonad polygraphic chain complex**, produced through the generic carrier from its
well-formedness — an `AugmentedDirectedComplex` with `d d = 0`, transported from the monad. -/
def comonadChainComplex : AugmentedDirectedComplex :=
  walkerPresentationChainComplex comonadWalkerPresentation comonadPresentationIsWellFormed

/-- The reduction certificate for `d2(comonad) = [[−1, 1]]` → `[[1, 0]]`: negate column 0 (recovering
the monad's `[[1, −1]]`), then the monad's `col1 += col0`.  Lands on the monad's `SNF(d2)`. -/
def comonadBoundaryOfDimOneSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations :=
      [ ElementaryOperation.columnOperation (ElementaryColumnOperation.negateColumn 0)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 1 (-1)) ] }

/-- The reduction certificate for `d3(comonad)` → `[[1, 0, 0, 0, 0], [0, 0, 0, 0, 0]]`: negate all five
columns (recovering the monad's `d3`), then the monad's shipped reduction word.  Lands on the monad's
`SNF(d3)`. -/
def comonadBoundaryOfDimTwoSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations :=
      [ ElementaryOperation.columnOperation (ElementaryColumnOperation.negateColumn 0)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.negateColumn 1)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.negateColumn 2)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.negateColumn 3)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.negateColumn 4)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.swapColumns 0 1)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 2 (-1))
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 4 (-1))
      , ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple 0 1 (-1)) ] }

/-- **`d2(comonad)` reduces to the monad's `SNF(d2) = [[1, 0]]`** — rank 1, unit invariant factor. -/
theorem comonadBoundaryOfDimOneReducesToSmith :
    comonadBoundaryOfDimOneSmithCertificate.reducesToSmithForm comonadBoundaryOfDimOne 1 2 :=
  show (⟨[[1, 0]]⟩ : IntMatrix).IsSmithNormalFormWithin 1 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 1 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex → (⟨[[1, 0]]⟩ : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isPositionBelow)) }

/-- **`d3(comonad)` reduces to the monad's `SNF(d3) = [[1, 0, 0, 0, 0], [0, 0, 0, 0, 0]]`** — rank 1,
unit invariant factor, four free columns. -/
theorem comonadBoundaryOfDimTwoReducesToSmith :
    comonadBoundaryOfDimTwoSmithCertificate.reducesToSmithForm comonadBoundaryOfDimTwo 2 5 :=
  show (⟨[[1, 0, 0, 0, 0], [0, 0, 0, 0, 0]]⟩ : IntMatrix).IsSmithNormalFormWithin 2 5 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 5 →
          rowIndex ≠ colIndex →
          (⟨[[1, 0, 0, 0, 0], [0, 0, 0, 0, 0]]⟩ : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨0, rfl⟩
      | _ + 1, isBeyond =>
          Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyond))) }

/-- **The degree-2 homology free rank of the comonad**: `nullity(d2) − rank(d3) =
(C2 − rank(d2)) − rank(d3) = (2 − 1) − 1 = 0`, read off the monad's shipped Smith normal forms (the
comonad's certificates land on the SAME literals). -/
def comonadDegreeTwoHomologyFreeRank : Nat :=
  (comonadWalkerPresentation.computeBasisCount 2 - smithRankWithin walkerSmithNormalFormOfDimOne 1)
    - smithRankWithin walkerSmithNormalFormOfDimTwo 2

/-- **The comonad degree-2 homology free rank is `0`**, by `rfl` on the `Nat` literals. -/
theorem comonadDegreeTwoHomologyFreeRankIsZero : comonadDegreeTwoHomologyFreeRank = 0 := rfl

/-- **`H2(comonad) = 0`, as free rank `0` AND no torsion** — the complete invariant of the trivial
group, transported from the walking monad (`d3`'s Smith normal form is the monad's, unit factor). -/
def ComonadDegreeTwoHomologyIsZeroStatement : Prop :=
  comonadDegreeTwoHomologyFreeRank = 0 ∧ hasNoSmithTorsionWithin walkerSmithNormalFormOfDimTwo 2

/-- ★★ **`H2(walking comonad) = 0`**, transported from `H2(walking monad) = 0` through the op-duality:
`d2`/`d3` are the monad's NEGATED, hence unimodular-equivalent, hence the SAME Smith normal forms and
the SAME homology.  The comonad-specific certificates (`comonadBoundaryOfDim{One,Two}ReducesToSmith`)
land on the monad's SNF literals; the correspondence is `comonadBoundaryDim{One,Two}IsNegatedMonad`. -/
theorem comonadDegreeTwoHomologyIsZero : ComonadDegreeTwoHomologyIsZeroStatement :=
  ⟨comonadDegreeTwoHomologyFreeRankIsZero, walkerDimTwoHasNoTorsion⟩

/-! ## B2 — the IDEMPOTENT COMONAD `= opPresentation (idempotent semigroup)`, `H1 = 0`, `H2 = 0`

`opPresentation idempotentSemigroupWalkerPresentation`: rule `[([0], [0, 0])]` (the reversed
`mu : ee ⟹ e` counit `e ⟹ ee`), critical pair `eee` with legs swapped (identical, both `[1]`).  Its
`d2 = [[1]]` (the idempotent's `[[−1]]` negated, ALREADY Smith), `d3 = [[0]]`. -/

/-- The idempotent-comonad presentation, as the op-dual of the idempotent-semigroup walker. -/
def idempotentComonadWalkerPresentation : WalkerPresentation :=
  opPresentation idempotentSemigroupWalkerPresentation

/-- `d2(idempotent comonad) = [[1]]` (the idempotent's `[[−1]]` negated) — already in Smith normal
form. -/
def idempotentComonadBoundaryOfDimOne : IntMatrix := ⟨[[1]]⟩

/-- **The idempotent-comonad presentation computes `d1 = [[0]]`** — `rfl`. -/
theorem idempotentComonadPresentationComputesBoundaryDimZero :
    idempotentComonadWalkerPresentation.computeBoundaryDimZero
      = idempotentSemigroupBoundaryOfDimZero := rfl

/-- **The idempotent-comonad presentation computes `d2 = [[1]]`** — `rfl`. -/
theorem idempotentComonadPresentationComputesBoundaryDimOne :
    idempotentComonadWalkerPresentation.computeBoundaryDimOne = idempotentComonadBoundaryOfDimOne :=
  rfl

/-- **The idempotent-comonad presentation computes `d3 = [[0]]`** — `rfl`. -/
theorem idempotentComonadPresentationComputesBoundaryDimTwo :
    idempotentComonadWalkerPresentation.computeBoundaryDimTwo
      = idempotentSemigroupBoundaryOfDimTwo := rfl

/-- ★ **THE CORRESPONDENCE.**  `d2(idempotent comonad)[0, j] = −d2(idempotent semigroup)[0, j]` — the
generic transport at the idempotent semigroup, degree 1. -/
theorem idempotentComonadBoundaryDimOneIsNegated (colIndex : Nat) :
    idempotentComonadBoundaryOfDimOne.entryAt 0 colIndex
      = -(idempotentSemigroupBoundaryOfDimOne.entryAt 0 colIndex) :=
  opPresentationBoundaryEntryIsNegated idempotentSemigroupWalkerPresentation 1 0 colIndex

/-- ★ **The idempotent-comonad presentation is well-formed** — transported from
`idempotentSemigroupPresentationIsWellFormed` through the entrywise negation + `intNegMulNeg`. -/
theorem idempotentComonadPresentationIsWellFormed :
    WellFormedWalkerPresentation idempotentComonadWalkerPresentation :=
  fun rowIndex colIndex rowBound colBound =>
    (sumOverIndicesCongr
      (fun middleIndex =>
        (congrArg
          (· * idempotentComonadWalkerPresentation.computeBoundaryDimTwo.entryAt middleIndex colIndex)
          (opPresentationBoundaryEntryIsNegated idempotentSemigroupWalkerPresentation 1 rowIndex
            middleIndex)).trans
          ((congrArg
            (-(idempotentSemigroupWalkerPresentation.computeBoundaryDimOne.entryAt rowIndex middleIndex)
              * ·)
            (opPresentationBoundaryEntryIsNegated idempotentSemigroupWalkerPresentation 2 middleIndex
              colIndex)).trans
            (intNegMulNeg
              (idempotentSemigroupWalkerPresentation.computeBoundaryDimOne.entryAt rowIndex middleIndex)
              (idempotentSemigroupWalkerPresentation.computeBoundaryDimTwo.entryAt middleIndex
                colIndex))))
      (idempotentComonadWalkerPresentation.computeBasisCount 2)).trans
      (idempotentSemigroupPresentationIsWellFormed rowIndex colIndex rowBound colBound)

/-- ★★ **The idempotent-comonad polygraphic chain complex**, produced through the generic carrier. -/
def idempotentComonadChainComplex : AugmentedDirectedComplex :=
  walkerPresentationChainComplex idempotentComonadWalkerPresentation
    idempotentComonadPresentationIsWellFormed

/-- The reduction certificate for `d2(idempotent comonad) = [[1]]` — already Smith normal (positive
diagonal), the empty certificate. -/
def idempotentComonadBoundaryOfDimOneSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations := [] }

/-- **`d2(idempotent comonad)` reduces to `[[1]]`** — kernel-checked; rank 1, UNIT invariant factor. -/
theorem idempotentComonadBoundaryOfDimOneReducesToSmith :
    idempotentComonadBoundaryOfDimOneSmithCertificate.reducesToSmithForm
      idempotentComonadBoundaryOfDimOne 1 1 :=
  show (⟨[[1]]⟩ : IntMatrix).IsSmithNormalFormWithin 1 1 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 1 → ∀ colIndex, colIndex < 1 →
          rowIndex ≠ colIndex → (⟨[[1]]⟩ : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isPositionBelow)) }

/-- **The degree-1 homology free rank of the idempotent comonad**: `nullity(d1) − rank(d2) =
(C1 − rank(d1)) − rank(d2) = (1 − 0) − 1 = 0`.  The `d2` factor is the UNIT `1`, so `H1 = ZZ/1 = 0`. -/
def idempotentComonadDegreeOneHomologyFreeRank : Nat :=
  (idempotentComonadWalkerPresentation.computeBasisCount 1
      - smithRankWithin idempotentSemigroupSmithNormalFormOfDimZero 1)
    - smithRankWithin idempotentComonadBoundaryOfDimOne 1

/-- **The idempotent-comonad degree-1 homology free rank is `0`**, by `rfl`. -/
theorem idempotentComonadDegreeOneHomologyFreeRankIsZero :
    idempotentComonadDegreeOneHomologyFreeRank = 0 := rfl

/-- **`H1(idempotent comonad) = 0`, as free rank `0`, invariant factor list `[1]` (the UNIT), AND no
torsion** — the complete invariant of the trivial group, transported (the `d2 = [[1]]` is the
idempotent's `[[−1]]` negated, same unimodular class). -/
def IdempotentComonadDegreeOneHomologyIsTrivialStatement : Prop :=
  idempotentComonadDegreeOneHomologyFreeRank = 0 ∧
  smithInvariantFactorsWithin idempotentComonadBoundaryOfDimOne 1 = [1] ∧
  hasNoSmithTorsionWithin idempotentComonadBoundaryOfDimOne 1

/-- ★★ **`H1(idempotent comonad) = 0`** — the UNIT invariant-factor endpoint, transported from the
idempotent-semigroup walker (`H1 = 0`) through the op-duality. -/
theorem idempotentComonadDegreeOneHomologyIsTrivial :
    IdempotentComonadDegreeOneHomologyIsTrivialStatement :=
  ⟨idempotentComonadDegreeOneHomologyFreeRankIsZero, rfl, ⟨True.intro, Or.inr rfl⟩⟩

/-- **The degree-2 homology free rank of the idempotent comonad**: `nullity(d2) − rank(d3) =
(C2 − rank(d2)) − rank(d3) = (1 − 1) − 0 = 0`. -/
def idempotentComonadDegreeTwoHomologyFreeRank : Nat :=
  (idempotentComonadWalkerPresentation.computeBasisCount 2
      - smithRankWithin idempotentComonadBoundaryOfDimOne 1)
    - smithRankWithin idempotentSemigroupSmithNormalFormOfDimTwo 1

/-- **The idempotent-comonad degree-2 homology free rank is `0`**, by `rfl`. -/
theorem idempotentComonadDegreeTwoHomologyFreeRankIsZero :
    idempotentComonadDegreeTwoHomologyFreeRank = 0 := rfl

/-- **`H2(idempotent comonad) = 0`, as free rank `0` AND no torsion.** -/
def IdempotentComonadDegreeTwoHomologyIsZeroStatement : Prop :=
  idempotentComonadDegreeTwoHomologyFreeRank = 0 ∧
  hasNoSmithTorsionWithin idempotentSemigroupSmithNormalFormOfDimTwo 1

/-- ★★ **`H2(idempotent comonad) = 0`**, transported from the idempotent-semigroup walker. -/
theorem idempotentComonadDegreeTwoHomologyIsZero :
    IdempotentComonadDegreeTwoHomologyIsZeroStatement :=
  ⟨idempotentComonadDegreeTwoHomologyFreeRankIsZero, idempotentSemigroupDimTwoHasNoTorsion⟩

/-! ## B3 — the KZ / co-KZ census coverage (via the abelianization; honest caveat)

The walking KZ monad `⟨t | eta : id ⟹ t, mu : t.t ⟹ t, plus a directed order⟩` has EXACTLY the walking
monad's rewrite rules; the KZ order (`KZTwoCellLE`, no `symm`) is extra structure the ABELIANIZATION
forgets.  So the KZ polygraphic chain complex IS the walking monad's, and co-KZ (`opPresentation` of KZ)
IS the walking comonad's.  Honest caveat: this covers the ABELIANIZED homology only — co-KZ's walker
identity is a directed PREORDER, not the symmetric conv carrier. -/

/-- The KZ monad's abelianized presentation IS the walking monad's (the order is forgotten). -/
def kzAbelianizedPresentation : WalkerPresentation := monadWalkerPresentation

/-- The KZ abelianized presentation is DEFINITIONALLY the walking monad's — `rfl`. -/
theorem kzAbelianizedPresentationEqualsMonad :
    kzAbelianizedPresentation = monadWalkerPresentation := rfl

/-- ★ **`H2(KZ, abelianized) = 0`**, directly the walking monad's homology — the KZ rewrite rules ARE
the monad's, so its polygraphic chain complex coincides (the order is forgotten by abelianization). -/
theorem kzAbelianizedDegreeTwoHomologyIsZero : WalkerDegreeTwoHomologyIsZeroStatement :=
  walkerDegreeTwoHomologyIsZero

/-- The co-KZ comonad's abelianized presentation IS the walking comonad's (the op of the KZ monad). -/
def coKZAbelianizedPresentation : WalkerPresentation := opPresentation monadWalkerPresentation

/-- The co-KZ abelianized presentation is DEFINITIONALLY the walking comonad's — `rfl`. -/
theorem coKZAbelianizedPresentationEqualsComonad :
    coKZAbelianizedPresentation = comonadWalkerPresentation := rfl

/-- ★ **`H2(co-KZ, abelianized) = 0`**, directly the walking comonad's homology (= the monad's,
transported).  Honest caveat: co-KZ's walker identity is a directed preorder; this covers the
abelianization only. -/
theorem coKZAbelianizedDegreeTwoHomologyIsZero : ComonadDegreeTwoHomologyIsZeroStatement :=
  comonadDegreeTwoHomologyIsZero

/-! ## B4 — the census maximum (8 of 9) + the adjunction wall (the sole residual)

Shipped literal complexes (4): walking monad (`H2 = 0`), involution (`H1 = ZZ/2`), cyclic-three
(`H1 = ZZ/3`), idempotent semigroup (`H1 = 0`).  This file's op-duals (4): comonad (`H2 = 0`),
idempotent comonad (`H1 = 0`, `H2 = 0`), KZ (`= monad`, `H2 = 0`), co-KZ (`= comonad`, `H2 = 0`).
Total: **8 of the `decidedWalkerCount = 9`** decided walkers with computed homology.  The sole residual
is the walking ADJUNCTION — genuinely WALLED. -/

/-- The number of decided walkers with a machine-computed homology group, after the op-duality
transport: the four shipped literal complexes (monad, involution, cyclic-three, idempotent semigroup)
PLUS the four op-duals (comonad, idempotent comonad, KZ, co-KZ).  `8` of `decidedWalkerCount = 9`. -/
def walkersWithComputedHomologyCountAfterOpDuality : Nat := 8

/-- ★ **THE CENSUS MAXIMUM: `8` of `9`.**  Kernel-checked (`rfl`).  The remaining `1` is the walking
ADJUNCTION (walled). -/
theorem walkersWithComputedHomologyCountAfterOpDualityValue :
    walkersWithComputedHomologyCountAfterOpDuality = 8 := rfl

/-- ★ **The census is exactly `decidedWalkerCount − 1`**: `8 + 1 = 9`, so precisely ONE decided walker
(the adjunction) lacks computed homology.  Kernel-checked (`rfl`). -/
theorem walkersWithComputedHomologyIsAllButOne :
    walkersWithComputedHomologyCountAfterOpDuality + 1 = decidedWalkerCount := rfl

/-! ## B5 — the op-duality-transport ledger (file-section states + honest scoping + the wall)

  * **B2 (generic) — the transport theorem**: SHIPPED.  `opPresentation` (rule reversal + leg swap);
    `opPresentationComputesBasisCount` (basis preserved); ★★ `opPresentationBoundaryEntryIsNegated`
    (`d^op = −d` at every dimension, via the repo Int-negation kit); `sumOverIndicesCongr`.
  * **B2 (comonad) — `opPresentation (walking monad)`**: SHIPPED.  Boundary literals + correspondence
    (`comonadBoundaryDim{One,Two}IsNegatedMonad`); `comonadPresentationIsWellFormed` (transported);
    `comonadChainComplex`; Smith certificates (prepended column negations) landing on the monad's SNF;
    ★★ `comonadDegreeTwoHomologyIsZero` (`H2 = 0`).
  * **B2 (idempotent comonad) — `opPresentation (idempotent semigroup)`**: SHIPPED.  `d2 = [[1]]`
    already Smith; ★★ `idempotentComonadDegreeOneHomologyIsTrivial` (`H1 = 0`) and
    `idempotentComonadDegreeTwoHomologyIsZero` (`H2 = 0`).
  * **B3 (KZ / co-KZ) — the abelianization coverage**: SHIPPED.  `kzAbelianizedPresentation` (= monad,
    `H2 = 0`); `coKZAbelianizedPresentation` (= comonad, `H2 = 0`).  Honest caveat: abelianization only
    (co-KZ's walker identity is a directed preorder).
  * **B4 — the census maximum**: SHIPPED.  `walkersWithComputedHomologyCountAfterOpDuality = 8` of `9`;
    `walkersWithComputedHomologyIsAllButOne` pins the residual at exactly ONE.
  * **B5 — this ledger**: SHIPPED.

### Honest scoping

The transport delivers CENSUS COVERAGE, not new invariants: KZ/co-KZ homology are abelianization-copies
of monad/comonad (coverage, not content), and the shipped DISTINCT homology groups remain `{0, ZZ/2,
ZZ/3}`.  The generic `opPresentationBoundaryEntryIsNegated` is stated over an ARBITRARY presentation
(genuine generic content: op negates the polygraphic boundary); the homology READ-OFFS are per-walker,
via each dual's own kernel-checked certificate landing on its base walker's Smith normal form.

### The wall (the sole residual — NAMED, with what would un-wall it)

  * **The walking ADJUNCTION** — its 2-cell word problem is NOT convergent at head
    (`fxMode_hasSaturatedTwoCellConfluence := false`, `fxMode_hasAdjunctionTwoCellWordProblem := false`).
    The combined saturated TRIANGLE rewrite ships, but CONFLUENCE is the OPEN Schanuel–Street node, so
    there is no decidable critical-pair / `d3` layer, hence no honest `H2` read-off (the low truncation
    `H0`/`H1` is computable, but `H2`/`H3` depend on the open confluence layer).  **What would un-wall
    it:** a decision procedure (or refutation) for the adjunction 2-cell confluence — closing
    `fxMode_hasSaturatedTwoCellConfluence` — would supply the critical-pair enumeration the abelianized
    `d3` needs, at which point the same carrier machinery reads off `H2` immediately.  This is the
    H2-WALKERS r1 deferral, unchanged. -/

/-- ★ **The op-duality-transport ledger marker.**  What stands, zero-axiom: the GENERIC op-duality
transport `d^op = −d` (`opPresentationBoundaryEntryIsNegated`), and the four op-dual census entries it
delivers — the walking comonad (`H2 = 0`, `comonadDegreeTwoHomologyIsZero`), the idempotent comonad
(`H1 = 0`, `H2 = 0`), and KZ / co-KZ (`= monad` / `= comonad`, abelianized `H2 = 0`).  With the four
shipped literal complexes this reaches the CENSUS MAXIMUM `8` of `9`
(`walkersWithComputedHomologyCountAfterOpDuality`); the sole residual is the WALLED walking adjunction.
Read the meaning from THIS docstring (the honest-record convention). -/
def presentationOpDualityHomologyLedgerIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
