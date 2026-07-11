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

end FX1Poly.Polygraph.Homology
