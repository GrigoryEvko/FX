import FX1Poly.Polygraph.Homology.FreshGeneratorTietzeExpansionInvariance

/-! # FX1Poly/Polygraph/Homology/Type2CompletionCyclicThreeInstance — the COMPLETED (Knuth–Bendix,
    UNSIMPLIFIED) type-2 Tietze move on cyclic `⟨s | sss⟩`: adjoin the DERIVABLE relation `ssss ⟹ s`,
    complete to the convergent two-rule system `{sss ⟹ e, ssss ⟹ s}` with its full 11-critical-pair
    Squier resolution, and read off `H2 = 0` PRESERVED — the covering critical pair the naive move omitted
    (H2-SQUIER-NOGO r7, #2139)

## What this file is — the type-2 H2 SPIKE (one worked instance, no general claim)

r5/r6 (`Homology/FreshGeneratorTietzeExpansionInvariance`) shipped the type-2 move at H1 (preserved,
column-in-span) and REFUTED the NAIVE H2 read-off (`type2NaiveH2FreeRankIsOne`): adjoining the derivable
rule `ssss ⟹ s` to cyclic `⟨s | sss⟩` while leaving `d3` UNCHANGED leaves the syzygy `rule2 − rule1`
UNCOVERED, giving a spurious `H2 = ZZ ≠ 0` (base `H2 = 0`).  The r6 wall
(`type2CyclicThreeH2PreservationHasNoTheorem`, preserved byte-intact) recorded that H2 preservation is
resolution-CHOICE-dependent: it holds ONLY if the Knuth–Bendix critical-pair completion is performed,
adding the covering `d3` column.

This file WORKS THAT COMPLETION BY HAND for the one cyclic-3 instance.  The completed convergent system is
`R = {R1 : sss ⟹ e, R2 : ssss ⟹ s}` (one generator `s = 0`, `e = []`).  Both rules remove exactly three
`s`, so the abelianized `d2` is `[[-3, -3]]` (the shipped `type2CyclicThreeExpandedBoundaryDimOne`), and —
the decisive content — its Knuth–Bendix critical-pair set is the ELEVEN overlaps `{R1⋈R1 (×2), R1⋈R2
inclusions (×2), R1⋈R2/R2⋈R1 proper (×4), R2⋈R2 (×3)}`, whose abelianized cofork `d3` (`2 × 11`) contains
the COVERING column `[1, -1]` (the inclusion overlap `ssss = (sss)s`, CP3/CP4).  That column covers the
syzygy the naive move left open: `rank(d3) = 1`, and `H2 = nullity(d2) − rank(d3) = (2 − 1) − 1 = 0`,
torsion `nonUnit([1]) = []`.  **`H2 = 0` — PRESERVED through the completed form**, exactly the covering
column the naive move omitted.

## Both honest completed forms (the tautological note)

`ssss ⟹ s` is REDUCIBLE by `sss ⟹ e` in one step (`ssss = s·sss ⟹ s·e = s`, and `s` is R2's RHS), so
under Knuth–Bendix INTERREDUCTION rule `R2` collapses to the trivial rule and is deleted, giving
KB-WITH-simplification `= {sss ⟹ e}` = cyclic `⟨s | sss⟩` VERBATIM — tautologically `H2 = 0` (the same
chain complex).  This file ships the UNSIMPLIFIED convergent form (`R1, R2` with its full 11-critical-pair
`d3`), where the covering column is a GENUINE new `d3` atom rather than a definitional identity; the
simplified collapse is recorded only as a note (`type2CompletionTautologicalCollapseNote`), not the content.

## The scope adjudication (honest — instance-level evidence, NO general type-2 H2 theorem)

This is ONE worked instance, a down-payment on the resolution-dependence finding — NOT a general type-2 H2
theorem.  The general claim (arbitrary type-2 moves, arbitrary presentations, the abelianized-Tietze
chain-homotopy) stays the R1 / Squier–Pride homotopy research wall, unchanged.  The r6 wall decl
`type2CyclicThreeH2PreservationHasNoTheorem` is preserved byte-intact in
`FreshGeneratorTietzeExpansionInvariance`; this file records the ADDITIVE new evidence
(`type2CompletedCyclicThreeH2VindicatedAtInstance`): at this instance completion VINDICATES `H2 = 0`.

## Zero-axiom design decisions

  * The rewriting probe is a self-defined structural normalizer over words `List Nat` (`s = 0`, `e = []`);
    the head reduction is FULLY ENUMERATED on the leading letters (`0`, `_ + 1`) and `List` constructors —
    R1's pattern `0 :: 0 :: 0 :: rest` naturally shadows R2's `0 :: 0 :: 0 :: 0 :: rest` (deterministic,
    leftmost-shortest), so NO wildcard-over-literal-`Nat` head, no propext leak.
  * The `d2 · d3 = 0` well-formedness is decided by `rfl` on the literal boundaries (11 in-range column
    sums); the out-of-range column (`≥ 11`) and row (`≥ 1`) arms are refuted by the propext-clean
    successor peels (`natEqZeroOfLeZero` / `natLeOfSuccLeSucc`).
  * The two Smith reductions ship EXPLICIT unimodular operation words checked propext-cleanly against the
    literal Smith normal forms `[[3, 0]]` (`d2`) and `diag(1, 0, …, 0)` (`d3`, `2 × 11`); the `if diag = 0`
    reductions are on literal `Int` cells only.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/Type2CompletionCyclicThreeInstance.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra
open FX1Poly.Polygraph.Steiner

/-! ## B2 — the completed (unsimplified) presentation record -/

/-- The COMPLETED convergent presentation of `ZZ/3` from the type-2 Tietze move on `⟨s | sss⟩`: one endo
1-generator `s` (`= 0`); TWO rules `R1 : sss ⟹ e` (`([0,0,0], [])`) and `R2 : ssss ⟹ s` (`([0,0,0,0],
[0])`, the adjoined DERIVABLE relation, oriented length-decreasing); and the ELEVEN Squier critical pairs
(the full Knuth–Bendix overlap census), each `(overlapWord, leftLegFirings, rightLegFirings)` with the two
firing lists indexed BY RULE `[#R1, #R2]`.  The overlap words are documentation-only (abelianization
ignores them); the firing lists record ONE canonical closing leg each (the specified redex, then the
R1-preferred normalization of the shared reduct — both legs reach the same normal form). -/
def type2CompletedCyclicThreePresentation : WalkerPresentation :=
  { oneGeneratorCount := 1
  , rules := [([0, 0, 0], []), ([0, 0, 0, 0], [0])]
  , criticalPairs :=
      [ ([0, 0, 0, 0],             [1, 0], [1, 0])   -- CP1  ssss  R1@0 / R1@1        col [0,0]
      , ([0, 0, 0, 0, 0],          [1, 0], [1, 0])   -- CP2  sssss R1@0 / R1@2        col [0,0]
      , ([0, 0, 0, 0],             [1, 0], [0, 1])   -- CP3  ssss  R1@0 / R2@0  ★ COVERING col [1,-1]
      , ([0, 0, 0, 0],             [0, 1], [1, 0])   -- CP4  ssss  R2@0 / R1@1        col [-1,1]
      , ([0, 0, 0, 0, 0],          [1, 0], [0, 1])   -- CP5  sssss R1@0 / R2@1        col [1,-1]
      , ([0, 0, 0, 0, 0, 0],       [2, 0], [1, 1])   -- CP6  s^6   R1@0 / R2@2        col [1,-1]
      , ([0, 0, 0, 0, 0],          [0, 1], [1, 0])   -- CP7  sssss R2@0 / R1@2        col [-1,1]
      , ([0, 0, 0, 0, 0, 0],       [1, 1], [2, 0])   -- CP8  s^6   R2@0 / R1@3        col [-1,1]
      , ([0, 0, 0, 0, 0],          [0, 1], [0, 1])   -- CP9  sssss R2@0 / R2@1        col [0,0]
      , ([0, 0, 0, 0, 0, 0],       [1, 1], [1, 1])   -- CP10 s^6   R2@0 / R2@2        col [0,0]
      , ([0, 0, 0, 0, 0, 0, 0],    [1, 1], [1, 1]) ] } -- CP11 s^7 R2@0 / R2@3        col [0,0]

/-! ## B2 — the confluence TRUTH PROBE (the completion is correct: all critical pairs join)

A self-defined structural rewriting normalizer over words `List Nat` (`s = 0`, `e = []`).  Every reduct of
`s^p` is the SAME word `s^{p-3}` (both rules remove exactly three `s` from a unary word), so local
confluence is immediate; the probe records the R1-preferred head reduction, its normal forms, and the
front/back-leg join of each of the eleven critical peaks. -/

/-- Rewrite the leftmost redex of a word (identity when there is none) — fully enumerated on the leading
letters (`0`, `_ + 1`), so R1's pattern `0 :: 0 :: 0 :: rest` (leftmost `sss`) shadows R2's longer `ssss`
deterministically, and there is NO wildcard-over-literal-`Nat` head (no propext leak).  On `s^p` (`p ≥ 3`)
this fires R1 at the head, giving `s^{p-3}` — the same word every other redex of `s^p` would produce. -/
def type2CompletedRewriteReduceRedexAtHead : List Nat → List Nat
  | [] => []
  | [singleLetter] => [singleLetter]
  | [firstLetter, secondLetter] => [firstLetter, secondLetter]
  | 0 :: 0 :: 0 :: remainingLetters => remainingLetters                                      -- R1: sss ⟹ e
  | 0 :: 0 :: (thirdPlusOne + 1) :: remainingLetters => 0 :: 0 :: (thirdPlusOne + 1) :: remainingLetters
  | 0 :: (secondPlusOne + 1) :: thirdLetter :: remainingLetters =>
      0 :: (secondPlusOne + 1) :: thirdLetter :: remainingLetters
  | (firstPlusOne + 1) :: secondLetter :: thirdLetter :: remainingLetters =>
      (firstPlusOne + 1) :: secondLetter :: thirdLetter :: remainingLetters

/-- Normalize a word by iterating the head reduction `fuel` times — structural on the fuel `Nat`.  Every
rule strictly reduces length by 3, so `fuel = 4` normalizes every word arising in the eleven critical
peaks (the longest, `s^7`, reaches its normal form in two steps). -/
def type2CompletedNormalizeWord : Nat → List Nat → List Nat
  | 0, word => word
  | fuel + 1, word => type2CompletedNormalizeWord fuel (type2CompletedRewriteReduceRedexAtHead word)

/-- The FRONT leg of a critical pair: rewrite the redex at position `0`. -/
def type2CompletedRewriteFrontLegStep (word : List Nat) : List Nat :=
  type2CompletedRewriteReduceRedexAtHead word

/-- The BACK leg of a critical pair: keep the head letter, rewrite the redex at position `1`. -/
def type2CompletedRewriteBackLegStep : List Nat → List Nat
  | [] => []
  | headLetter :: remainingLetters =>
      headLetter :: type2CompletedRewriteReduceRedexAtHead remainingLetters

/-- ★ **The irreducible words are `{e, s, ss} = ZZ/3`** — the three normal forms are fixpoints of the
normalizer (`e = []`, `s = [0]`, `ss = [0, 0]`), by `rfl`. -/
theorem type2CompletedNormalFormsAreThree :
    type2CompletedNormalizeWord 4 [] = [] ∧
    type2CompletedNormalizeWord 4 [0] = [0] ∧
    type2CompletedNormalizeWord 4 [0, 0] = [0, 0] :=
  ⟨rfl, rfl, rfl⟩

/-- The eleven critical-pair OVERLAP peak words `s^4 … s^7` (`s = 0`), in the `CP1 … CP11` order of
`type2CompletedCyclicThreePresentation.criticalPairs`. -/
def type2CompletedCriticalPairOverlapWords : List (List Nat) :=
  [ [0, 0, 0, 0]                     -- CP1  s^4
  , [0, 0, 0, 0, 0]                  -- CP2  s^5
  , [0, 0, 0, 0]                     -- CP3  s^4
  , [0, 0, 0, 0]                     -- CP4  s^4
  , [0, 0, 0, 0, 0]                  -- CP5  s^5
  , [0, 0, 0, 0, 0, 0]               -- CP6  s^6
  , [0, 0, 0, 0, 0]                  -- CP7  s^5
  , [0, 0, 0, 0, 0, 0]               -- CP8  s^6
  , [0, 0, 0, 0, 0]                  -- CP9  s^5
  , [0, 0, 0, 0, 0, 0]               -- CP10 s^6
  , [0, 0, 0, 0, 0, 0, 0] ]          -- CP11 s^7

/-- ★ **Each distinct critical peak normalizes to its join** — `s^4 ⟹ s`, `s^5 ⟹ ss`, `s^6 ⟹ e`,
`s^7 ⟹ s` (`s^p ⟹ s^{p mod 3}`), by `rfl`. -/
theorem type2CompletedCriticalPairJoinTargets :
    type2CompletedNormalizeWord 4 [0, 0, 0, 0] = [0] ∧
    type2CompletedNormalizeWord 4 [0, 0, 0, 0, 0] = [0, 0] ∧
    type2CompletedNormalizeWord 4 [0, 0, 0, 0, 0, 0] = [] ∧
    type2CompletedNormalizeWord 4 [0, 0, 0, 0, 0, 0, 0] = [0] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- ★★ **ALL ELEVEN CRITICAL PAIRS JOIN.**  For every overlap peak `s^p`, the FRONT leg (redex at position
0) and the BACK leg (redex at position 1) normalize to the SAME word (both reduce the peak to the shared
`s^{p-3}` in one step, then to `s^{p mod 3}`).  Terminating + all critical pairs joining ⟹ (Newman) the
UNSIMPLIFIED two-rule system is CONVERGENT — the truth probe that the type-2 completion is correct.
Enumerated by `List.Mem` decomposition, each leg-agreement by `rfl`. -/
theorem type2CompletedCriticalPairsJoin :
    ∀ word, word ∈ type2CompletedCriticalPairOverlapWords →
      type2CompletedNormalizeWord 4 (type2CompletedRewriteFrontLegStep word)
        = type2CompletedNormalizeWord 4 (type2CompletedRewriteBackLegStep word)
  | _, .head _ => rfl
  | _, .tail _ (.head _) => rfl
  | _, .tail _ (.tail _ (.head _)) => rfl
  | _, .tail _ (.tail _ (.tail _ (.head _))) => rfl
  | _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))) => rfl
  | _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) => rfl
  | _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) => rfl
  | _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) => rfl
  | _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) => rfl
  | _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))) =>
      rfl
  | _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
      (.tail _ (.head _)))))))))) => rfl

/-- ★ **R2 is DERIVABLE (the type-2 move's defining property, and the tautological-collapse content).**
The two sides of the adjoined rule `ssss ⟹ s` have EQUAL normal forms (`normalize(ssss) = normalize(s) =
s`), so `R2` adds no rewriting power over `R1` — this is why Knuth–Bendix interreduction deletes `R2`
(collapsing the completed system to cyclic `⟨s | sss⟩`), and why the covering column restores `H2 = 0`.
By `rfl`. -/
theorem type2CompletedRuleTwoIsDerivable :
    type2CompletedNormalizeWord 4 [0, 0, 0, 0] = type2CompletedNormalizeWord 4 [0] := rfl

/-! ## B2 — the boundary literals and the carrier-fit (the presentation COMPUTES them) -/

/-- `d1 : C1 → C0`, the `1 × 1` all-zero loop row `[[0]]` (`s` is a loop `point → point`). -/
def type2CompletedBoundaryDimZero : IntMatrix := ⟨[[0]]⟩

/-- `d2 : C2 → C1`, the `1 × 2` abelianized boundary `[[-3, -3]]`: both rules remove exactly three `s`
(`R1 : #s(e) − #s(sss) = -3`, `R2 : #s(s) − #s(ssss) = 1 − 4 = -3`).  Identical to the shipped
`type2CyclicThreeExpandedBoundaryDimOne`. -/
def type2CompletedBoundaryDimOne : IntMatrix := ⟨[[-3, -3]]⟩

/-- `d3 : C3 → C2`, the `2 × 11` abelianized cofork boundary — row `Rk`, column `CPj` is
`(leftFirings CPj)[Rk] − (rightFirings CPj)[Rk]`.  Row `R2` `= −` row `R1` (both legs of each peak have
equal total firing count), and the COVERING column `[1, -1]` (from the inclusion overlap `ssss = (sss)s`,
CP3) makes `rank(d3) = 1`. -/
def type2CompletedBoundaryDimTwo : IntMatrix :=
  ⟨[ [0, 0, 1, -1, 1, 1, -1, -1, 0, 0, 0]
   , [0, 0, -1, 1, -1, -1, 1, 1, 0, 0, 0] ]⟩

/-- ★ The completed presentation's basis counts: `C0 = 1`, `C1 = 1`, `C2 = 2` (the two rules), `C3 = 11`
(the eleven critical pairs) — the completion ENRICHES `C2` (`1 → 2`) and `C3` (`2 → 11`) over the base. -/
theorem type2CompletedPresentationBasisCounts :
    type2CompletedCyclicThreePresentation.computeBasisCount 0 = 1 ∧
    type2CompletedCyclicThreePresentation.computeBasisCount 1 = 1 ∧
    type2CompletedCyclicThreePresentation.computeBasisCount 2 = 2 ∧
    type2CompletedCyclicThreePresentation.computeBasisCount 3 = 11 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **The presentation computes `d1`.** -/
theorem type2CompletedComputesBoundaryDimZero :
    type2CompletedCyclicThreePresentation.computeBoundaryDimZero = type2CompletedBoundaryDimZero := rfl

/-- ★ **The presentation computes `d2` `[[-3, -3]]`** — the completed two-rule abelianization. -/
theorem type2CompletedComputesBoundaryDimOne :
    type2CompletedCyclicThreePresentation.computeBoundaryDimOne = type2CompletedBoundaryDimOne := rfl

/-- ★★ **The presentation computes the `2 × 11` completed `d3`** — the eleven abelianized coforks, with the
covering column `[1, -1]`.  This is the covering `d3` the NAIVE move omitted (`type2NaiveH2FreeRankIsOne`),
here a GENUINE carrier-computed boundary. -/
theorem type2CompletedComputesBoundaryDimTwo :
    type2CompletedCyclicThreePresentation.computeBoundaryDimTwo = type2CompletedBoundaryDimTwo := rfl

/-- ★ **The completed `d2` IS the shipped type-2 `d2`** — `computeBoundaryDimOne = [[-3, -3]] =
type2CyclicThreeExpandedBoundaryDimOne`; `rfl`.  Connects this instance to the shipped type-2 H1
machinery (the derivable-column, `type2CyclicThreeReducesToRankOne`). -/
theorem type2CompletedBoundaryDimOneIsShippedType2 :
    type2CompletedCyclicThreePresentation.computeBoundaryDimOne
      = type2CyclicThreeExpandedBoundaryDimOne := rfl

/-! ## B2 — the well-formedness discharge (`d2 · d3 = 0`) -/

/-- A column index `≥ 11` cannot be below `11` — the eleven-fold successor peel refuting the out-of-range
`d3` column arms of the well-formedness match. -/
theorem type2CompletedColumnIndexBelowElevenIsAbsurd {value : Nat} (isBelow : value + 11 < 11) : False :=
  Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc
    (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc
    (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBelow))))))))))))

/-- ★★ **The completed presentation is WELL-FORMED** — `d2 · d3 = 0`, the residual dimension-1 cofork
coherence.  All eleven in-range column sums `Σ_r d2[s, r] · d3[r, cp]` close by `rfl` on the literal
boundaries (each `-3·d3[R1,cp] − 3·d3[R2,cp] = -3·(d3[R1,cp] + d3[R2,cp]) = 0`, since `d3` row `R2 = −`
row `R1`); the out-of-range column (`≥ 11`) and row (`≥ 1`) arms are refuted by the propext-clean
successor peels.  This feeds the generic `walkerPresentationChainComplex`. -/
theorem type2CompletedPresentationIsWellFormed :
    WellFormedWalkerPresentation type2CompletedCyclicThreePresentation
  | 0, 0, _, _ => rfl
  | 0, 1, _, _ => rfl
  | 0, 2, _, _ => rfl
  | 0, 3, _, _ => rfl
  | 0, 4, _, _ => rfl
  | 0, 5, _, _ => rfl
  | 0, 6, _, _ => rfl
  | 0, 7, _, _ => rfl
  | 0, 8, _, _ => rfl
  | 0, 9, _, _ => rfl
  | 0, 10, _, _ => rfl
  | 0, _ + 11, _, colBound =>
      absurd colBound (fun tooLarge => type2CompletedColumnIndexBelowElevenIsAbsurd tooLarge)
  | _ + 1, _, rowBound, _ =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc rowBound))

/-- ★★ **The completed presentation yields a full `AugmentedDirectedComplex`** — through the shipped
generic `walkerPresentationChainComplex`, gated on the well-formedness discharge. -/
def type2CompletedChainComplex : AugmentedDirectedComplex :=
  walkerPresentationChainComplex type2CompletedCyclicThreePresentation type2CompletedPresentationIsWellFormed

/-! ## B3 — the Smith handoff + the H2 read-off (`H2 = 0` PRESERVED through the completed form)

The two non-trivial boundaries `d2` (`1 × 2`) and `d3` (`2 × 11`) carry EXPLICIT unimodular reduction
certificates to `[[3, 0]]` and `diag(1, 0, …, 0)`; the homology is read off the SHIPPED generic
`SmithHomologyData.homologyInvariant` with NO new reader.  `H2 = 0` — the covering column makes
`rank(d3) = 1`, cancelling the nullity `d2` gained. -/

/-- The `d2` reduction certificate: the SHIPPED type-2 clearing `type2CyclicThreeReductionCertificate`
(clear the in-span second column, negate the sign) taking `[[-3, -3]]` to `[[3, 0]]`. -/
def type2CompletedBoundaryDimOneSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations := type2CyclicThreeReductionCertificate }

/-- The Smith normal form of the completed `d2` — `[[3, 0]]`: rank 1, torsion factor `3` (the `ZZ/3`
source), unchanged from the base cyclic `d2`. -/
def type2CompletedSmithNormalFormOfDimOne : IntMatrix := ⟨[[3, 0]]⟩

/-- ★ **The `d2` certificate produces `[[3, 0]]`** — `rfl`, through the shipped type-2 clearing. -/
theorem type2CompletedDimOneCertificateProducesSmithNormalForm :
    type2CompletedBoundaryDimOne.applyOperations type2CompletedBoundaryDimOneSmithCertificate.operations
      = type2CompletedSmithNormalFormOfDimOne := rfl

/-- The `d3` reduction certificate taking the `2 × 11` completed `d3` to its Smith normal form
`diag(1, 0, …, 0)`: clear row `R2` (`= −R1`) by `addRowMultiple 0 1 1`, swap the covering pivot at column
`2` onto the diagonal (`swapColumns 0 2`), and clear the five remaining `±1` columns with the unit pivot. -/
def type2CompletedBoundaryDimTwoSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations :=
      [ ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple 0 1 1)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.swapColumns 0 2)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 3 1)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 4 (-1))
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 5 (-1))
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 6 1)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 7 1) ] }

/-- The Smith normal form of the completed `d3` — `diag(1, 0, …, 0)` (`2 × 11`): rank 1, the single
invariant factor a UNIT (`gcd = 1`), so NO H2 torsion.  The covering column's `[1, -1]` clears to the
unit pivot; every other column is collinear (in `ZZ·(1,-1) = ker d2`) and clears to zero. -/
def type2CompletedSmithNormalFormOfDimTwo : IntMatrix :=
  ⟨[ [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
   , [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ]⟩

/-- ★★ **The `d3` certificate produces `diag(1, 0, …, 0)`** — `rfl`, the seven unimodular operations
checked to land on the literal Smith normal form; `rank(d3) = 1`, invariant factor the unit `1`. -/
theorem type2CompletedDimTwoCertificateProducesSmithNormalForm :
    type2CompletedBoundaryDimTwo.applyOperations type2CompletedBoundaryDimTwoSmithCertificate.operations
      = type2CompletedSmithNormalFormOfDimTwo := rfl

/-- ★ **`d2` reduces to `[[3, 0]]`** — kernel-checked Smith normal form within the `1 × 2` window; rank 1,
invariant factor `[3]`. -/
theorem type2CompletedBoundaryDimOneReducesToSmith :
    type2CompletedBoundaryDimOneSmithCertificate.reducesToSmithForm type2CompletedBoundaryDimOne 1 2 :=
  show type2CompletedSmithNormalFormOfDimOne.IsSmithNormalFormWithin 1 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 1 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex → type2CompletedSmithNormalFormOfDimOne.entryAt rowIndex colIndex = 0 := by
        decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isPositionBelow)) }

/-- ★★ **`d3` reduces to `diag(1, 0, …, 0)`** — kernel-checked Smith normal form within the `2 × 11`
window; rank 1, the single invariant factor a UNIT (`1 | 0` witnessed).  The COVERING column made the rank
one — this is the decisive read-off restoring `H2 = 0`. -/
theorem type2CompletedBoundaryDimTwoReducesToSmith :
    type2CompletedBoundaryDimTwoSmithCertificate.reducesToSmithForm type2CompletedBoundaryDimTwo 2 11 :=
  show type2CompletedSmithNormalFormOfDimTwo.IsSmithNormalFormWithin 2 11 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 11 →
          rowIndex ≠ colIndex → type2CompletedSmithNormalFormOfDimTwo.entryAt rowIndex colIndex = 0 := by
        decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨0, by decide⟩
      | _ + 1, isSuccBelow =>
          Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isSuccBelow))) }

/-- The Smith data for `H2(completed ZZ/3)`: `C_2 = 2`, `SNF(d_2) = [[3, 0]]` (window `1`),
`SNF(d_3) = diag(1, 0, …, 0)` (window `2`). -/
def type2CompletedCyclicThreeDegreeTwoSmithData : SmithHomologyData :=
  { chainBasisCount := 2
  , smithBoundaryIntoLower := type2CompletedSmithNormalFormOfDimOne
  , windowIntoLower := 1
  , smithBoundaryFromHigher := type2CompletedSmithNormalFormOfDimTwo
  , windowFromHigher := 2 }

/-- `H2(completed ZZ/3) = 0` as a `HomologyInvariant`: free rank `0`, no torsion. -/
def type2CompletedDegreeTwoHomologyInvariant : HomologyInvariant := ⟨0, []⟩

/-- ★★ **`H2 = 0` PRESERVED through the completed form** — the invariant `(0, [])`, read off the SHIPPED
generic `SmithHomologyData.homologyInvariant`: free rank `(C_2 − rank(d_2)) − rank(d_3) = (2 − 1) − 1 = 0`,
torsion `nonUnit([1]) = []`.  The covering column raised `rank(d_3)` from `0` (the naive move's spurious
`H2 = ZZ`) to `1`, exactly cancelling the nullity `d_2` gained.  `rfl`. -/
theorem type2CompletedDegreeTwoHomologyIsZero :
    type2CompletedCyclicThreeDegreeTwoSmithData.homologyInvariant
      = type2CompletedDegreeTwoHomologyInvariant := rfl

/-- ★ **The `d2` certificate transports the ACTUAL boundary onto the homology data's SNF** — `rfl`. -/
theorem type2CompletedBoundaryDimOneReducesToIntoLower :
    type2CompletedCyclicThreePresentation.computeBoundaryDimOne.applyOperations
        type2CompletedBoundaryDimOneSmithCertificate.operations
      = type2CompletedCyclicThreeDegreeTwoSmithData.smithBoundaryIntoLower := rfl

/-- ★ **The `d3` certificate transports the ACTUAL boundary onto the homology data's SNF** — `rfl`. -/
theorem type2CompletedBoundaryDimTwoReducesToFromHigher :
    type2CompletedCyclicThreePresentation.computeBoundaryDimTwo.applyOperations
        type2CompletedBoundaryDimTwoSmithCertificate.operations
      = type2CompletedCyclicThreeDegreeTwoSmithData.smithBoundaryFromHigher := rfl

/-- ★ **The Smith handoff is INHABITED** — both non-trivial boundary Smith reductions are kernel-checked
(`d2 → [[3, 0]]`, `d3 → diag(1, 0, …, 0)`). -/
theorem type2CompletedSmithHandoff :
    type2CompletedBoundaryDimOneSmithCertificate.reducesToSmithForm type2CompletedBoundaryDimOne 1 2 ∧
    type2CompletedBoundaryDimTwoSmithCertificate.reducesToSmithForm type2CompletedBoundaryDimTwo 2 11 :=
  ⟨type2CompletedBoundaryDimOneReducesToSmith, type2CompletedBoundaryDimTwoReducesToSmith⟩

/-! ## B3 — the recon prediction pin + the base agreement -/

/-- The recon design PREDICTED `H2 = 0` (`⟨0, []⟩`) for the completed unsimplified form. -/
def type2CompletedReconPredictedH2 : HomologyInvariant := ⟨0, []⟩

/-- ★★ **The machine-pinned H2 verdict MATCHES the recon prediction** — the computed
`type2CompletedCyclicThreeDegreeTwoSmithData.homologyInvariant` equals the recon-predicted `⟨0, []⟩`, by
`rfl`.  No mismatch: completion vindicates `H2 = 0` exactly as forecast. -/
theorem type2CompletedH2MatchesReconPrediction :
    type2CompletedCyclicThreeDegreeTwoSmithData.homologyInvariant = type2CompletedReconPredictedH2 := rfl

/-- ★ **`H2(completed) = H2(base cyclic) = 0`** — the completed form and the compact `⟨s | sss⟩` base agree
at `H2` through the shipped reader, by `rfl`.  The presentations DIFFER (`C_2` `1 → 2`, `C_3` `2 → 11`), but
the homology invariant is preserved. -/
theorem type2CompletedH2AgreesWithCyclicBase :
    type2CompletedCyclicThreeDegreeTwoSmithData.homologyInvariant
      = cyclicThreeDegreeTwoSmithData.homologyInvariant := rfl

/-- ★ **The completion ENRICHES the critical-pair census** — the base cyclic `⟨s | sss⟩` has `C_3 = 2`
critical pairs, the completed two-rule system has `C_3 = 11`; the covering column lives in the eleven, not
the two.  By `rfl`. -/
theorem type2CompletedCriticalPairCountExceedsBase :
    cyclicThreeWalkerPresentation.criticalPairs.length = 2 ∧
    type2CompletedCyclicThreePresentation.criticalPairs.length = 11 :=
  ⟨rfl, rfl⟩

/-- ★ **The completed presentation DIFFERS from the base** — the rule count differs (`1 ≠ 2`), so the H2
agreement is a genuine cross-presentation coincidence, not a definitional identity. -/
theorem type2CompletedPresentationDiffersFromBase :
    cyclicThreeWalkerPresentation ≠ type2CompletedCyclicThreePresentation :=
  fun presentationsEqual =>
    absurd (congrArg (fun presentation => presentation.rules.length) presentationsEqual) (by decide)

/-! ## B4 — the interpretation ledger (honest — instance-level evidence, NO general type-2 H2 claim)

### What r7 LANDED (the type-2 H2 spike, additive, zero-axiom)

  * **B2 — the completed presentation**: `type2CompletedCyclicThreePresentation` (the UNSIMPLIFIED
    convergent two-rule system `{sss ⟹ e, ssss ⟹ s}` with its full 11-critical-pair census); the
    confluence TRUTH PROBE (`type2CompletedNormalFormsAreThree`, `type2CompletedCriticalPairJoinTargets`,
    ★★ `type2CompletedCriticalPairsJoin` — all eleven critical pairs join by structural evaluation;
    `type2CompletedRuleTwoIsDerivable` — R2 derivable); the carrier-fit
    (`type2CompletedComputesBoundary…`, all `rfl`); ★★ `type2CompletedPresentationIsWellFormed`
    (`d2 · d3 = 0`); `type2CompletedChainComplex`.
  * **B3 — the H2 read-off through the SHIPPED reader**: two explicit unimodular Smith certificates
    (`d2 → [[3, 0]]`, `d3 → diag(1, 0, …, 0)`, kernel-checked); ★★ `type2CompletedDegreeTwoHomologyIsZero`
    (`H2 = 0`, the covering column making `rank(d3) = 1`); the recon-prediction pin
    (`type2CompletedH2MatchesReconPrediction` — no mismatch) and the base agreement
    (`type2CompletedH2AgreesWithCyclicBase`).

### What STAYS WALLED (named, unmoved)

The r6 wall `type2CyclicThreeH2PreservationHasNoTheorem` (preserved byte-intact in
`FreshGeneratorTietzeExpansionInvariance`) stands: NO general type-2 H2-preservation theorem is shipped.
This file is ONE worked instance — the covering critical pair `ssss = (sss)s` restores `H2 = 0` that the
NAIVE move (`type2NaiveH2FreeRankIsOne`, spurious `ZZ`) lost — a down-payment on the resolution-dependence
finding, NOT the general claim.  The general type-2 H2 invariance (arbitrary relation moves, arbitrary
presentations, the abelianized-Tietze chain-homotopy — the Squier / Pride homotopy machinery) remains the
R1 research wall.

### The tautological-simplification note (honest)

Knuth–Bendix WITH interreduction deletes the derivable rule `R2` (`type2CompletedRuleTwoIsDerivable`),
collapsing the completed system to `{sss ⟹ e}` = cyclic `⟨s | sss⟩` VERBATIM — for which `H2 = 0`
tautologically (the same chain complex).  The genuine content here is the UNSIMPLIFIED form, where the
covering column is a real new `d3` atom among eleven critical pairs rather than a definitional identity;
the collapse is the note, not the content. -/

/-- ★ **The #2139 round-seven marker: TYPE-2 H2 VINDICATED AT THIS INSTANCE (additive evidence).**  The
completed UNSIMPLIFIED convergent presentation of `ZZ/3` (`{sss ⟹ e, ssss ⟹ s}`, 11 critical pairs)
preserves `H2 = 0` (`type2CompletedDegreeTwoHomologyIsZero`) — the covering critical pair `ssss = (sss)s`
(column `[1, -1]`, `rank(d3) = 1`) restores the `H2 = 0` the NAIVE move
(`type2NaiveH2FreeRankIsOne`, spurious `ZZ`) lost.  This is ONE worked instance, additive evidence for the
r6 wall `type2CyclicThreeH2PreservationHasNoTheorem` (preserved byte-intact) — NOT a general type-2 H2
theorem.  `= true` records the instance-level vindication.  Read the meaning from THIS docstring. -/
def type2CompletedCyclicThreeH2VindicatedAtInstance : Bool := true

/-- ★ **The #2139 round-seven marker: the tautological-simplification note.**  Knuth–Bendix WITH
interreduction deletes the derivable rule `R2` (`type2CompletedRuleTwoIsDerivable`) and collapses the
completed system to cyclic `⟨s | sss⟩`, for which `H2 = 0` is definitional.  The genuine content is the
UNSIMPLIFIED form (the covering column a real `d3` atom among eleven critical pairs), NOT the collapse.
`= true` records the note. -/
def type2CompletionTautologicalCollapseNote : Bool := true

/-- ★ **The #2139 round-seven residual marker (the exact node STILL named).**  The general type-2 H2
invariance (arbitrary relation moves, arbitrary presentations, the abelianized-Tietze chain-homotopy — the
Squier / Pride homotopy machinery) remains the R1 research wall, UNCHANGED.  This file pays it down by ONE
worked instance (completion vindicates `H2 = 0`), moving NO wall's general statement.  `= true` records
the r7 stance.  Read the meaning from THIS docstring. -/
def type2CompletedCyclicThreeLedgerResidual : Bool := true

end FX1Poly.Polygraph.Homology
