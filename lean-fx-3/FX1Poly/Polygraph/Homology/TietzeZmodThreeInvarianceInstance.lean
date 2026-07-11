import FX1Poly.Polygraph.Homology.CyclicThreeChainComplex
import FX1Poly.Polygraph.Homology.SquierNoGoInterface

/-! # FX1Poly/Polygraph/Homology/TietzeZmodThreeInvarianceInstance — the EXPANDED convergent
    presentation `⟨s, t | ss ⟹ t, st ⟹ e, ts ⟹ e, tt ⟹ s⟩` of `ZZ/3`, its kernel-checked homology
    (`H1 = ZZ/3`, `H2 = 0`), the degree-≤2 AGREEMENT with the shipped `⟨s | sss⟩` presentation, and the
    first genuine CROSS-PRESENTATION inhabitant of the Squier invariance interface
    (H2-SQUIER-NOGO r2, #2139)

## What this file is

The shipped `Homology/CyclicThreeChainComplex` presents `ZZ/3 = ⟨s | s³ = 1⟩` as a one-generator
one-rule decided polygraph (`H1 = ZZ/3`, `H2 = 0`).  This file presents the SAME group `ZZ/3` through a
DIFFERENT convergent rewriting system — the Tietze-EXPANDED presentation on TWO generators — computes its
homology through the SAME shipped generic Smith read-off, and records that the two presentations agree in
every degree `≤ 2`.  It is the FIRST multi-generator (`oneGeneratorCount = 2`) instance of the generic
`WalkerPresentation` carrier, and the FIRST genuine cross-presentation inhabitant of
`HomologyPresentationInvariance` (the Squier no-go interface's invariance field) — a strict strengthening
of the r1 op-duality witness (which related two SAME-SHAPE presentations by a sign flip; this relates two
GENUINELY DIFFERENT presentations, `1 gen / 1 rule / 2 CP` vs `2 gen / 4 rule / 8 CP`).

## The Tietze move and the completion (all critical pairs join — the B1 truth probe)

`ZZ/3 = ⟨s | s³⟩`; adjoin `t := s²`.  The expanded presentation is `⟨s, t | s² = t, s·t = 1⟩`, oriented
and completed to the length-reducing convergent system (`s = 0`, `t = 1`, `e = []`):

  * `R1 : ss ⟹ t`   (`s² = t`)
  * `R2 : st ⟹ e`   (`s·t = s³ = 1`)
  * `R3 : ts ⟹ e`   (`t·s = s³ = 1`)
  * `R4 : tt ⟹ s`   (`t·t = s⁴ = s`)

Every left-hand side has length 2 and every right-hand side length `≤ 1`, so the system is length-reducing
and terminating.  All four length-2 words are left-hand sides, so the width-1 overlaps are EXACTLY the
eight length-3 words `{s, t}³`; each joins (`tietzeCriticalPairsJoin`, the eight legs reaching a common
normal form by structural evaluation).  Terminating + all critical pairs join ⟹ (Newman) convergent; the
irreducible words are `{e, s, t} = ZZ/3` (`tietzeRewritingNormalFormsAreThree`).

## Zero-axiom design decisions

  * The rewriting probe is a self-defined structural normalizer over `List Nat` words (`s = 0`, `t = 1`);
    every match is FULLY ENUMERATED on `Nat` (`0`, `1`, `_ + 2`) and `List` constructors — NO wildcard
    over a literal-`Nat` head, so no propext leak (a bare `_` catch-all overlapping `0 :: _` DOES leak).
  * The boundary agreement, the well-formedness discharge, and every read-off close by `rfl` / explicit
    peel on literal matrices, exactly the shipped `CyclicThreeChainComplex` discipline (`decide` only on
    literal-`Int` SNF cells and disequalities, never a `Nat.min` / `Nat.sub` Smith-driver expression).
  * The two Smith reduction certificates ship EXPLICIT unimodular operation words checked propext-cleanly
    against the literal Smith normal forms `diag(1, 3)` and `diag(1, 1, 0, 0)`.
  * The normal-form monoid iso `{e, s, ss} ≅ {e, s, t}` is over two 3-constructor inductives, full-enum.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/TietzeZmodThreeInvarianceInstance.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra
open FX1Poly.Polygraph.Steiner

/-! ## B1 — the expanded presentation record -/

/-- The Tietze-EXPANDED presentation of `ZZ/3` on TWO endo 1-generators `s` (`= 0`) and `t` (`= 1`): the
four rules `ss ⟹ t`, `st ⟹ e`, `ts ⟹ e`, `tt ⟹ s`, and the eight Squier critical pairs `{s, t}³`, each
recorded as `(overlapWord, leftLegFirings, rightLegFirings)` with the firing lists indexed by rule.  The
FIRST `oneGeneratorCount = 2` instance of the generic `WalkerPresentation` carrier. -/
def tietzeZmodThreePresentation : WalkerPresentation :=
  { oneGeneratorCount := 2
  , rules := [([0, 0], [1]), ([0, 1], []), ([1, 0], []), ([1, 1], [0])]
  , criticalPairs :=
      [ ([], [1, 0, 1, 0], [1, 1, 0, 0])    -- CP1  sss  : (ss)s ⟹ ts ⟹ e  |  s(ss) ⟹ st ⟹ e
      , ([], [1, 0, 0, 1], [0, 1, 0, 0])    -- CP2  sst  : (ss)t ⟹ tt ⟹ s  |  s(st) ⟹ s
      , ([], [0, 1, 0, 0], [0, 0, 1, 0])    -- CP3  sts  : (st)s ⟹ s        |  s(ts) ⟹ s
      , ([], [0, 0, 1, 0], [1, 0, 0, 1])    -- CP4  tss  : (ts)s ⟹ s        |  t(ss) ⟹ tt ⟹ s
      , ([], [0, 0, 1, 0], [0, 1, 0, 0])    -- CP5  tst  : (ts)t ⟹ t        |  t(st) ⟹ t
      , ([], [0, 1, 0, 0], [1, 0, 0, 1])    -- CP6  stt  : (st)t ⟹ t        |  s(tt) ⟹ ss ⟹ t
      , ([], [1, 0, 0, 1], [0, 0, 1, 0])    -- CP7  tts  : (tt)s ⟹ ss ⟹ t  |  t(ts) ⟹ t
      , ([], [0, 1, 0, 1], [0, 0, 1, 1]) ] } -- CP8  ttt : (tt)t ⟹ st ⟹ e  |  t(tt) ⟹ ts ⟹ e

/-! ## B1 — the confluence TRUTH PROBE (the completion is correct: all critical pairs join)

A self-defined structural rewriting normalizer over words `List Nat` (`s = 0`, `t = 1`, `e = []`).  The
one-step head reduction is fully enumerated on the `Nat` head (`0`, `1`, `_ + 2`) so no propext leaks. -/

/-- Rewrite the length-2 redex at the head of a word (identity when there is none) — fully enumerated on
the two leading letters (`0`, `1`, `_ + 2`), so no wildcard-over-literal-`Nat` propext leak. -/
def tietzeRewriteReduceRedexAtHead : List Nat → List Nat
  | [] => []
  | [singleLetter] => [singleLetter]
  | 0 :: 0 :: remainingLetters => 1 :: remainingLetters                              -- ss ⟹ t
  | 0 :: 1 :: remainingLetters => remainingLetters                                    -- st ⟹ e
  | 0 :: (secondPlusTwo + 2) :: remainingLetters => 0 :: (secondPlusTwo + 2) :: remainingLetters
  | 1 :: 0 :: remainingLetters => remainingLetters                                    -- ts ⟹ e
  | 1 :: 1 :: remainingLetters => 0 :: remainingLetters                               -- tt ⟹ s
  | 1 :: (secondPlusTwo + 2) :: remainingLetters => 1 :: (secondPlusTwo + 2) :: remainingLetters
  | (headPlusTwo + 2) :: secondLetter :: remainingLetters =>
      (headPlusTwo + 2) :: secondLetter :: remainingLetters

/-- Normalize a word by iterating the head reduction `fuel` times — structural on the fuel `Nat`.  Every
rule strictly reduces length, so `fuel = 8` normalizes every word arising in the eight critical pairs. -/
def tietzeNormalizeWord : Nat → List Nat → List Nat
  | 0, word => word
  | fuel + 1, word => tietzeNormalizeWord fuel (tietzeRewriteReduceRedexAtHead word)

/-- The FRONT leg of a critical pair: rewrite the redex at position `0`. -/
def tietzeRewriteFrontLegStep (word : List Nat) : List Nat := tietzeRewriteReduceRedexAtHead word

/-- The BACK leg of a critical pair: keep the head letter, rewrite the redex at position `1`. -/
def tietzeRewriteBackLegStep : List Nat → List Nat
  | [] => []
  | headLetter :: remainingLetters => headLetter :: tietzeRewriteReduceRedexAtHead remainingLetters

/-- ★ **The irreducible words are `{e, s, t} = ZZ/3`** — the three normal forms are fixpoints of the
normalizer (`e = []`, `s = [0]`, `t = [1]`), by `rfl`. -/
theorem tietzeRewritingNormalFormsAreThree :
    tietzeNormalizeWord 8 [] = [] ∧
    tietzeNormalizeWord 8 [0] = [0] ∧
    tietzeNormalizeWord 8 [1] = [1] :=
  ⟨rfl, rfl, rfl⟩

/-- The eight length-3 overlap words `{s, t}³` (`s = 0`, `t = 1`), in the `CP1 … CP8` order of
`tietzeZmodThreePresentation.criticalPairs`. -/
def tietzeCriticalPairOverlapWords : List (List Nat) :=
  [[0, 0, 0], [0, 0, 1], [0, 1, 0], [1, 0, 0], [1, 0, 1], [0, 1, 1], [1, 1, 0], [1, 1, 1]]

/-- ★ **Each critical-pair overlap word normalizes to its join** — `sss ⟹ e`, `sst ⟹ s`, `sts ⟹ s`,
`tss ⟹ s`, `tst ⟹ t`, `stt ⟹ t`, `tts ⟹ t`, `ttt ⟹ e` — the join column of the completion table, by
`rfl`. -/
theorem tietzeCriticalPairJoinTargets :
    tietzeNormalizeWord 8 [0, 0, 0] = [] ∧
    tietzeNormalizeWord 8 [0, 0, 1] = [0] ∧
    tietzeNormalizeWord 8 [0, 1, 0] = [0] ∧
    tietzeNormalizeWord 8 [1, 0, 0] = [0] ∧
    tietzeNormalizeWord 8 [1, 0, 1] = [1] ∧
    tietzeNormalizeWord 8 [0, 1, 1] = [1] ∧
    tietzeNormalizeWord 8 [1, 1, 0] = [1] ∧
    tietzeNormalizeWord 8 [1, 1, 1] = [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ★★ **ALL EIGHT CRITICAL PAIRS JOIN.**  For every overlap word `{s, t}³`, the FRONT leg (redex at
position 0) and the BACK leg (redex at position 1) normalize to the SAME word.  Terminating + all
critical pairs joining ⟹ (Newman) the expanded presentation is CONVERGENT — the B1 truth probe that the
Tietze completion is correct.  Enumerated by `List.Mem` decomposition, each leg-agreement by `rfl`. -/
theorem tietzeCriticalPairsJoin :
    ∀ word, word ∈ tietzeCriticalPairOverlapWords →
      tietzeNormalizeWord 8 (tietzeRewriteFrontLegStep word)
        = tietzeNormalizeWord 8 (tietzeRewriteBackLegStep word)
  | _, .head _ => rfl
  | _, .tail _ (.head _) => rfl
  | _, .tail _ (.tail _ (.head _)) => rfl
  | _, .tail _ (.tail _ (.tail _ (.head _))) => rfl
  | _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))) => rfl
  | _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) => rfl
  | _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) => rfl
  | _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) => rfl

/-! ## B1 — the boundary literals and the carrier-fit (the presentation COMPUTES them) -/

/-- `d1 : C1 → C0`, the `1 × 2` all-zero loop row `[[0, 0]]` (both `s` and `t` are loops
`point → point`). -/
def tietzeBoundaryOfDimZero : IntMatrix := ⟨[[0, 0]]⟩

/-- `d2 : C2 → C1`, the `2 × 4` abelianized boundary.  Row `s`: `[−2, −1, −1, 1]`; row `t`:
`[1, −1, −1, −2]` (each entry `(#gen in target) − (#gen in source)` per rule). -/
def tietzeBoundaryOfDimOne : IntMatrix := ⟨[[-2, -1, -1, 1], [1, -1, -1, -2]]⟩

/-- `d3 : C3 → C2`, the `4 × 8` abelianized cofork boundary — row `Rk`, column `CPj` is
`(leftFirings CPj)[Rk] − (rightFirings CPj)[Rk]`. -/
def tietzeBoundaryOfDimTwo : IntMatrix :=
  ⟨[ [0, 1, 0, -1, 0, -1, 1, 0]
   , [-1, -1, 1, 0, -1, 1, 0, 1]
   , [1, 0, -1, 1, 1, 0, -1, -1]
   , [0, 1, 0, -1, 0, -1, 1, 0] ]⟩

/-- ★ **The `oneGeneratorCount = 2` genericity, nailed as data**: the basis counts are
`C0 = 1`, `C1 = 2`, `C2 = 4`, `C3 = 8` — the generic carrier builds the two-generator rows with no
hardcoded `1`. -/
theorem tietzePresentationBasisCounts :
    tietzeZmodThreePresentation.computeBasisCount 0 = 1 ∧
    tietzeZmodThreePresentation.computeBasisCount 1 = 2 ∧
    tietzeZmodThreePresentation.computeBasisCount 2 = 4 ∧
    tietzeZmodThreePresentation.computeBasisCount 3 = 8 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **The presentation computes `d1`.** -/
theorem tietzePresentationComputesBoundaryDimZero :
    tietzeZmodThreePresentation.computeBoundaryDimZero = tietzeBoundaryOfDimZero := rfl

/-- ★ **The presentation computes `d2` `[[-2,-1,-1,1],[1,-1,-1,-2]]`** — the `oneGeneratorCount = 2`
carrier reproduces the hand-computed two-row abelianized boundary EXACTLY. -/
theorem tietzePresentationComputesBoundaryDimOne :
    tietzeZmodThreePresentation.computeBoundaryDimOne = tietzeBoundaryOfDimOne := rfl

/-- ★ **The presentation computes `d3`** — the `4 × 8` cofork boundary. -/
theorem tietzePresentationComputesBoundaryDimTwo :
    tietzeZmodThreePresentation.computeBoundaryDimTwo = tietzeBoundaryOfDimTwo := rfl

/-! ## B1 — the well-formedness discharge (`d2 · d3 = 0`) -/

/-- A column index `≥ 8` cannot be below `8` — the eight-fold successor peel refuting the out-of-range
`d3` column arms of the well-formedness match. -/
theorem tietzeColumnIndexBelowEightIsAbsurd {value : Nat} (isBelow : value + 8 < 8) : False :=
  Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc
    (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc
    (natLeOfSuccLeSucc isBelow)))))))))

/-- ★★ **The expanded presentation is WELL-FORMED** — `d2 · d3 = 0`, the residual dimension-1 cofork
coherence.  All `2 × 8 = 16` in-range column sums `Σ_r d2[gen, r] · d3[r, cp]` close by `rfl` on the
literal boundaries; the out-of-range row (`≥ 2`) and column (`≥ 8`) arms are refuted by the propext-clean
successor peels.  This is the ONLY non-generic half of `d d = 0`; discharging it feeds the generic
`walkerPresentationChainComplex`. -/
theorem tietzeZmodThreePresentationIsWellFormed :
    WellFormedWalkerPresentation tietzeZmodThreePresentation
  | 0, 0, _, _ => rfl
  | 0, 1, _, _ => rfl
  | 0, 2, _, _ => rfl
  | 0, 3, _, _ => rfl
  | 0, 4, _, _ => rfl
  | 0, 5, _, _ => rfl
  | 0, 6, _, _ => rfl
  | 0, 7, _, _ => rfl
  | 1, 0, _, _ => rfl
  | 1, 1, _, _ => rfl
  | 1, 2, _, _ => rfl
  | 1, 3, _, _ => rfl
  | 1, 4, _, _ => rfl
  | 1, 5, _, _ => rfl
  | 1, 6, _, _ => rfl
  | 1, 7, _, _ => rfl
  | 0, _ + 8, _, colBound => absurd colBound (fun tooLarge => tietzeColumnIndexBelowEightIsAbsurd tooLarge)
  | 1, _ + 8, _, colBound => absurd colBound (fun tooLarge => tietzeColumnIndexBelowEightIsAbsurd tooLarge)
  | _ + 2, _, rowBound, _ =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc rowBound)))

/-- ★★ **The expanded presentation yields a full `AugmentedDirectedComplex`** — through the shipped
generic `walkerPresentationChainComplex`, gated on the well-formedness discharge.  The first
two-generator inhabitant of the generic carrier. -/
def tietzeZmodThreeChainComplex : AugmentedDirectedComplex :=
  walkerPresentationChainComplex tietzeZmodThreePresentation tietzeZmodThreePresentationIsWellFormed

/-- ★ **`d d = 0` for the expanded presentation, DERIVED THROUGH THE GENERIC CARRIER** — feeding the
well-formedness discharge into `walkerPresentationBoundaryComposesToZeroOfWellFormed`. -/
theorem tietzeGenericCarrierBoundaryComposesToZero
    (dim rowIndex colIndex : Nat)
    (rowBound : rowIndex < tietzeZmodThreePresentation.computeBasisCount dim)
    (colBound : colIndex < tietzeZmodThreePresentation.computeBasisCount (dim + 2)) :
    sumOverIndices (tietzeZmodThreePresentation.computeBasisCount (dim + 1)) (fun middleIndex =>
      (tietzeZmodThreePresentation.computeBoundaryMatrix dim).entryAt rowIndex middleIndex *
      (tietzeZmodThreePresentation.computeBoundaryMatrix (dim + 1)).entryAt middleIndex colIndex)
      = 0 :=
  walkerPresentationBoundaryComposesToZeroOfWellFormed tietzeZmodThreePresentation
    tietzeZmodThreePresentationIsWellFormed dim rowIndex colIndex rowBound colBound

/-! ## B2 — the Smith handoff + the homology read-offs (`H1 = ZZ/3`, `H2 = 0`)

The two non-trivial boundaries `d2` (`2 × 4`) and `d3` (`4 × 8`) carry EXPLICIT unimodular reduction
certificates to `diag(1, 3)` and `diag(1, 1, 0, 0)`; the homology is read off the SHIPPED generic
`SmithHomologyData.homologyInvariant` with NO new reader.  `H1 = ZZ/3` — the invariant factors `(0, [3])`
the round DEMANDS. -/

/-- The reduction certificate taking `d1 = [[0, 0]]` to its Smith normal form `[[0, 0]]` — already
diagonal (rank 0). -/
def tietzeBoundaryOfDimZeroSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations := [] }

/-- The reduction certificate taking `d2 = [[-2,-1,-1,1],[1,-1,-1,-2]]` to its Smith normal form
`diag(1, 3)` — a row swap, one row transvection, five column transvections, one column negation
(each unimodular; determinant `±1`). -/
def tietzeBoundaryOfDimOneSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations :=
      [ ElementaryOperation.rowOperation (ElementaryRowOperation.swapRows 0 1)
      , ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple 0 1 2)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 1 1)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 2 1)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 3 2)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 1 2 (-1))
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 1 3 (-1))
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.negateColumn 1) ] }

/-- The reduction certificate taking `d3` (`4 × 8`) to its Smith normal form `diag(1, 1, 0, 0)` — a row
swap to a unit pivot, two row transvections, and ten column transvections / one column negation. -/
def tietzeBoundaryOfDimTwoSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations :=
      [ ElementaryOperation.rowOperation (ElementaryRowOperation.swapRows 0 2)
      , ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple 0 1 1)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 2 1)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 3 (-1))
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 4 (-1))
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 6 1)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 7 1)
      , ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple 1 2 1)
      , ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple 1 3 1)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 1 3 1)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 1 5 1)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 1 6 (-1))
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.negateColumn 1) ] }

/-- The Smith normal form of `d1` — `[[0, 0]]` (rank 0). -/
def tietzeSmithNormalFormOfDimZero : IntMatrix := ⟨[[0, 0]]⟩

/-- The Smith normal form of `d2` — `diag(1, 3)` = `[[1,0,0,0],[0,3,0,0]]`: rank 2, one UNIT factor and
one factor `3 > 1` (★ the source of the `ZZ/3` torsion). -/
def tietzeSmithNormalFormOfDimOne : IntMatrix := ⟨[[1, 0, 0, 0], [0, 3, 0, 0]]⟩

/-- The Smith normal form of `d3` — `diag(1, 1, 0, 0)`: rank 2, both invariant factors UNITS. -/
def tietzeSmithNormalFormOfDimTwo : IntMatrix :=
  ⟨[ [1, 0, 0, 0, 0, 0, 0, 0]
   , [0, 1, 0, 0, 0, 0, 0, 0]
   , [0, 0, 0, 0, 0, 0, 0, 0]
   , [0, 0, 0, 0, 0, 0, 0, 0] ]⟩

/-- **The `d1` certificate produces `tietzeSmithNormalFormOfDimZero`** — `rfl`. -/
theorem tietzeDimZeroCertificateProducesSmithNormalForm :
    tietzeBoundaryOfDimZero.applyOperations tietzeBoundaryOfDimZeroSmithCertificate.operations
      = tietzeSmithNormalFormOfDimZero := rfl

/-- ★ **The `d2` certificate produces `diag(1, 3)`** — `rfl`, the eight unimodular operations checked to
land on the literal Smith normal form. -/
theorem tietzeDimOneCertificateProducesSmithNormalForm :
    tietzeBoundaryOfDimOne.applyOperations tietzeBoundaryOfDimOneSmithCertificate.operations
      = tietzeSmithNormalFormOfDimOne := rfl

/-- ★ **The `d3` certificate produces `diag(1, 1, 0, 0)`** — `rfl`, the thirteen unimodular operations
checked to land on the literal Smith normal form. -/
theorem tietzeDimTwoCertificateProducesSmithNormalForm :
    tietzeBoundaryOfDimTwo.applyOperations tietzeBoundaryOfDimTwoSmithCertificate.operations
      = tietzeSmithNormalFormOfDimTwo := rfl

/-- **`d1` reduces to `[[0, 0]]`** — kernel-checked Smith normal form within the `1 × 2` window; rank 0. -/
theorem tietzeBoundaryOfDimZeroReducesToSmith :
    tietzeBoundaryOfDimZeroSmithCertificate.reducesToSmithForm tietzeBoundaryOfDimZero 1 2 :=
  show tietzeSmithNormalFormOfDimZero.IsSmithNormalFormWithin 1 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 1 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex → tietzeSmithNormalFormOfDimZero.entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isPositionBelow)) }

/-- ★★ **`d2` reduces to `diag(1, 3)`** — kernel-checked Smith normal form within the `2 × 4` window;
rank 2, invariant factors `[1, 3]`.  The `1 | 3` divisibility witness is explicit. -/
theorem tietzeBoundaryOfDimOneReducesToSmith :
    tietzeBoundaryOfDimOneSmithCertificate.reducesToSmithForm tietzeBoundaryOfDimOne 2 4 :=
  show tietzeSmithNormalFormOfDimOne.IsSmithNormalFormWithin 2 4 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 4 →
          rowIndex ≠ colIndex → tietzeSmithNormalFormOfDimOne.entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨3, by decide⟩
      | _ + 1, isSuccBelow =>
          Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isSuccBelow))) }

/-- ★ **`d3` reduces to `diag(1, 1, 0, 0)`** — kernel-checked Smith normal form within the `4 × 8`
window; rank 2, both invariant factors UNITS (`1 | 1`, `1 | 0`, `0 | 0` witnessed explicitly). -/
theorem tietzeBoundaryOfDimTwoReducesToSmith :
    tietzeBoundaryOfDimTwoSmithCertificate.reducesToSmithForm tietzeBoundaryOfDimTwo 4 8 :=
  show tietzeSmithNormalFormOfDimTwo.IsSmithNormalFormWithin 4 8 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 4 → ∀ colIndex, colIndex < 8 →
          rowIndex ≠ colIndex → tietzeSmithNormalFormOfDimTwo.entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨1, by decide⟩
      | 1, _ => ⟨0, by decide⟩
      | 2, _ => ⟨0, by decide⟩
      | _ + 3, isSuccBelow =>
          Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc
            (natLeOfSuccLeSucc (natLeOfSuccLeSucc isSuccBelow))))) }

/-- The Smith data for `H1(expanded ZZ/3)`: `C_1 = 2`, `SNF(d_1) = [[0, 0]]` (window `1`),
`SNF(d_2) = diag(1, 3)` (window `2`). -/
def tietzeDegreeOneSmithData : SmithHomologyData :=
  { chainBasisCount := 2
  , smithBoundaryIntoLower := tietzeSmithNormalFormOfDimZero
  , windowIntoLower := 1
  , smithBoundaryFromHigher := tietzeSmithNormalFormOfDimOne
  , windowFromHigher := 2 }

/-- `H1(expanded ZZ/3) = ZZ/3` as a `HomologyInvariant`: free rank `0`, torsion factor `[3]`. -/
def tietzeDegreeOneHomologyInvariant : HomologyInvariant := ⟨0, [3]⟩

/-- ★★ **`H1(expanded ZZ/3) = ZZ/3` — the invariant `(0, [3])` the round DEMANDS**, read off the SHIPPED
generic `SmithHomologyData.homologyInvariant` with NO new reader: free rank `(2 − rank(SNF d1)) −
rank(SNF d2) = (2 − 0) − 2 = 0`, torsion `nonUnit([3, 1]) = [3]`.  Exactly `H1(⟨s | sss⟩) = ZZ/3` through
a genuinely different presentation. -/
theorem tietzeDegreeOneHomologyIsZmodThree :
    tietzeDegreeOneSmithData.homologyInvariant = tietzeDegreeOneHomologyInvariant := rfl

/-- The Smith data for `H2(expanded ZZ/3)`: `C_2 = 4`, `SNF(d_2) = diag(1, 3)` (window `2`),
`SNF(d_3) = diag(1, 1, 0, 0)` (window `4`). -/
def tietzeDegreeTwoSmithData : SmithHomologyData :=
  { chainBasisCount := 4
  , smithBoundaryIntoLower := tietzeSmithNormalFormOfDimOne
  , windowIntoLower := 2
  , smithBoundaryFromHigher := tietzeSmithNormalFormOfDimTwo
  , windowFromHigher := 4 }

/-- `H2(expanded ZZ/3) = 0` as a `HomologyInvariant`: free rank `0`, no torsion. -/
def tietzeDegreeTwoHomologyInvariant : HomologyInvariant := ⟨0, []⟩

/-- ★ **`H2(expanded ZZ/3) = 0`**, read off the SHIPPED generic reader: free rank
`(4 − rank(SNF d2)) − rank(SNF d3) = (4 − 2) − 2 = 0`, torsion `nonUnit([1, 1]) = []`.  Template
continuity with `H2(⟨s | sss⟩) = 0`. -/
theorem tietzeDegreeTwoHomologyIsZero :
    tietzeDegreeTwoSmithData.homologyInvariant = tietzeDegreeTwoHomologyInvariant := rfl

/-- ★ **The Smith handoff is INHABITED** — all three boundary Smith reductions are kernel-checked
(`d1 → [[0,0]]`, `d2 → diag(1,3)`, `d3 → diag(1,1,0,0)`). -/
def TietzeSmithHandoffStatement : Prop :=
  tietzeBoundaryOfDimZeroSmithCertificate.reducesToSmithForm tietzeBoundaryOfDimZero 1 2 ∧
  tietzeBoundaryOfDimOneSmithCertificate.reducesToSmithForm tietzeBoundaryOfDimOne 2 4 ∧
  tietzeBoundaryOfDimTwoSmithCertificate.reducesToSmithForm tietzeBoundaryOfDimTwo 4 8

/-- ★ **The handoff is inhabited** — the complete SNF input the homology read-offs consume. -/
theorem tietzeSmithHandoff : TietzeSmithHandoffStatement :=
  ⟨tietzeBoundaryOfDimZeroReducesToSmith,
   tietzeBoundaryOfDimOneReducesToSmith,
   tietzeBoundaryOfDimTwoReducesToSmith⟩

/-! ## B3 — the AGREEMENT record (both presentations, equal invariants, the finite monoid iso)

The two presentations of `ZZ/3` — `⟨s | sss⟩` (`cyclicThreeWalkerPresentation`) and the expanded
`⟨s, t | ss, st, ts, tt⟩` (`tietzeZmodThreePresentation`) — receive the SAME homology invariant in every
degree `≤ 2`, read through the shipped generic reader, AND their normal-form monoids `{e, s, ss}` and
`{e, s, t}` are isomorphic as a decidable 3-element monoid iso `φ(ss) = t`.  This is the finite
monoid-correspondence witness the substrate cannot give at MONOID level (the JOB-2 wall) but CAN give at
NORMAL-FORM granularity for this worked instance. -/

/-- Cyclic's degree-two Smith read-off (`⟨s | sss⟩`): `C_2 = 1`, `SNF(d_2) = [[3]]` (window `1`),
`SNF(d_3) = [[0, 0]]` (window `1`) — reads `H2 = 0`. -/
def cyclicThreeDegreeTwoSmithData : SmithHomologyData :=
  { chainBasisCount := cyclicThreeBasisCount 2
  , smithBoundaryIntoLower := cyclicThreeSmithNormalFormOfDimOne
  , windowIntoLower := 1
  , smithBoundaryFromHigher := cyclicThreeSmithNormalFormOfDimTwo
  , windowFromHigher := 1 }

/-- The normal forms of the compact presentation `⟨s | sss⟩`: `{e, s, ss}`, as a 3-constructor
inductive (full-enum, propext-clean). -/
inductive CyclicThreeNormalForm
  /-- The identity `e`. -/
  | identityElement
  /-- The generator `s`. -/
  | generatorS
  /-- The square `ss` (`= s²`). -/
  | generatorSquared

/-- The normal forms of the expanded presentation `⟨s, t | …⟩`: `{e, s, t}`, as a 3-constructor
inductive (full-enum, propext-clean). -/
inductive TietzeZmodThreeNormalForm
  /-- The identity `e`. -/
  | identityElement
  /-- The generator `s`. -/
  | generatorS
  /-- The generator `t` (`= s²`). -/
  | generatorT

/-- The monoid iso `φ : {e, s, ss} → {e, s, t}`, `φ(ss) = t`. -/
def cyclicThreeNormalFormToTietze : CyclicThreeNormalForm → TietzeZmodThreeNormalForm
  | .identityElement => .identityElement
  | .generatorS => .generatorS
  | .generatorSquared => .generatorT

/-- The inverse iso `φ⁻¹ : {e, s, t} → {e, s, ss}`, `φ⁻¹(t) = ss`. -/
def tietzeNormalFormToCyclicThree : TietzeZmodThreeNormalForm → CyclicThreeNormalForm
  | .identityElement => .identityElement
  | .generatorS => .generatorS
  | .generatorT => .generatorSquared

/-- The normal-form multiplication table of `⟨s | sss⟩` (exponent addition mod 3): `s·s = ss`,
`s·ss = e`, `ss·s = e`, `ss·ss = s`. -/
def multiplyCyclicThreeNormalForm : CyclicThreeNormalForm → CyclicThreeNormalForm → CyclicThreeNormalForm
  | .identityElement, rightForm => rightForm
  | .generatorS, .identityElement => .generatorS
  | .generatorS, .generatorS => .generatorSquared
  | .generatorS, .generatorSquared => .identityElement
  | .generatorSquared, .identityElement => .generatorSquared
  | .generatorSquared, .generatorS => .identityElement
  | .generatorSquared, .generatorSquared => .generatorS

/-- The normal-form multiplication table of the expanded `⟨s, t | …⟩`: `s·s = t`, `s·t = e`, `t·s = e`,
`t·t = s` — read straight off the rewriting rules. -/
def multiplyTietzeNormalForm :
    TietzeZmodThreeNormalForm → TietzeZmodThreeNormalForm → TietzeZmodThreeNormalForm
  | .identityElement, rightForm => rightForm
  | .generatorS, .identityElement => .generatorS
  | .generatorS, .generatorS => .generatorT
  | .generatorS, .generatorT => .identityElement
  | .generatorT, .identityElement => .generatorT
  | .generatorT, .generatorS => .identityElement
  | .generatorT, .generatorT => .generatorS

/-- ★ **The proof-carrying degree-≤2 agreement record.**  Two presentations of `ZZ/3`, their EQUAL
degree-1 and degree-2 homology invariants (read through the shipped reader), and the mutually-inverse
normal-form monoid iso respecting multiplication. -/
structure TietzePairAgreement where
  /-- The compact presentation `⟨s | sss⟩`. -/
  presentationA : WalkerPresentation
  /-- The expanded presentation `⟨s, t | …⟩`. -/
  presentationB : WalkerPresentation
  /-- `H1(A)` read through the generic reader. -/
  degreeOneReadOffA : HomologyInvariant
  /-- `H1(B)` read through the generic reader. -/
  degreeOneReadOffB : HomologyInvariant
  /-- ★ `H1(A) = H1(B)` (both `ZZ/3 = (0, [3])`). -/
  degreeOneInvariantsAgree : degreeOneReadOffA = degreeOneReadOffB
  /-- `H2(A)` read through the generic reader. -/
  degreeTwoReadOffA : HomologyInvariant
  /-- `H2(B)` read through the generic reader. -/
  degreeTwoReadOffB : HomologyInvariant
  /-- ★ `H2(A) = H2(B)` (both `0 = (0, [])`). -/
  degreeTwoInvariantsAgree : degreeTwoReadOffA = degreeTwoReadOffB
  /-- The monoid iso `{e, s, ss} → {e, s, t}`. -/
  normalFormMapAtoB : CyclicThreeNormalForm → TietzeZmodThreeNormalForm
  /-- The inverse `{e, s, t} → {e, s, ss}`. -/
  normalFormMapBtoA : TietzeZmodThreeNormalForm → CyclicThreeNormalForm
  /-- `φ⁻¹ ∘ φ = id`. -/
  normalFormRoundTripA : ∀ formA, normalFormMapBtoA (normalFormMapAtoB formA) = formA
  /-- `φ ∘ φ⁻¹ = id`. -/
  normalFormRoundTripB : ∀ formB, normalFormMapAtoB (normalFormMapBtoA formB) = formB
  /-- ★ `φ` is a monoid homomorphism: `φ(a · b) = φ(a) · φ(b)`. -/
  multiplicationCorrespondence : ∀ leftForm rightForm,
      normalFormMapAtoB (multiplyCyclicThreeNormalForm leftForm rightForm)
        = multiplyTietzeNormalForm (normalFormMapAtoB leftForm) (normalFormMapAtoB rightForm)

/-- ★★ **THE AGREEMENT RECORD, inhabited.**  The compact and expanded presentations of `ZZ/3` agree at
`H1` (both `ZZ/3`) and `H2` (both `0`) through the shipped reader, and their normal-form monoids are
isomorphic (`φ(ss) = t`, mutually inverse, multiplication-respecting).  Every field is
`rfl`/full-enum — proof-carrying and decidable. -/
def tietzeCyclicPairAgreement : TietzePairAgreement :=
  { presentationA := cyclicThreeWalkerPresentation
  , presentationB := tietzeZmodThreePresentation
  , degreeOneReadOffA := cyclicThreeDegreeOneSmithData.homologyInvariant
  , degreeOneReadOffB := tietzeDegreeOneSmithData.homologyInvariant
  , degreeOneInvariantsAgree := rfl
  , degreeTwoReadOffA := cyclicThreeDegreeTwoSmithData.homologyInvariant
  , degreeTwoReadOffB := tietzeDegreeTwoSmithData.homologyInvariant
  , degreeTwoInvariantsAgree := rfl
  , normalFormMapAtoB := cyclicThreeNormalFormToTietze
  , normalFormMapBtoA := tietzeNormalFormToCyclicThree
  , normalFormRoundTripA := fun formA =>
      match formA with
      | .identityElement => rfl
      | .generatorS => rfl
      | .generatorSquared => rfl
  , normalFormRoundTripB := fun formB =>
      match formB with
      | .identityElement => rfl
      | .generatorS => rfl
      | .generatorT => rfl
  , multiplicationCorrespondence := fun leftForm rightForm =>
      match leftForm, rightForm with
      | .identityElement, .identityElement => rfl
      | .identityElement, .generatorS => rfl
      | .identityElement, .generatorSquared => rfl
      | .generatorS, .identityElement => rfl
      | .generatorS, .generatorS => rfl
      | .generatorS, .generatorSquared => rfl
      | .generatorSquared, .identityElement => rfl
      | .generatorSquared, .generatorS => rfl
      | .generatorSquared, .generatorSquared => rfl }

/-- ★ **HONEST degree scoping: the agreement is a degree-≤2 phenomenon.**  At degree 3 the two truncated
Squier complexes DIVERGE — the compact presentation has `C_3 = 2` critical pairs, the expanded one has
`C_3 = 8`, so their `ker d3` (the truncation-artifact `H3`) differ (`ZZ²` vs `ZZ⁶`).  The agreement is
scoped to degrees `≤ 2` — the degrees where both truncated complexes compute the true group homology —
and the H3 divergence is named, NOT papered.  `2 ≠ 8` by `decide`. -/
theorem tietzeAndCyclicDegreeThreeChainCountsDiffer :
    cyclicThreeWalkerPresentation.computeBasisCount 3 ≠ tietzeZmodThreePresentation.computeBasisCount 3 :=
  by decide

end FX1Poly.Polygraph.Homology
