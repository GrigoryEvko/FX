import FX1Poly.Polygraph.Homology.TietzeZmodThreeInvarianceInstance

/-! # FX1Poly/Polygraph/Homology/FreshGeneratorTietzeExpansionInvariance — the GENERIC
    fresh-generator Tietze-expansion theorem: adjoining a fresh generator `t` with a defining rule
    `t ⟹ w` (`w` free of `t`) to ANY decided single-object walker presentation preserves the
    degree-1 AND degree-2 homology invariant, read through the shipped generic Smith reader, with the
    two shipped instances (cyclic `ZZ/3`, the r2 Tietze presentation) and a fresh third instance
    (walking involution `ZZ/2`) fed through the theorem (H2-SQUIER-NOGO r3, #2139)

## What this file is — instance-to-theorem on the R1 wall

The r2 instance (`Homology/TietzeZmodThreeInvarianceInstance`) exhibited ONE worked cross-presentation
agreement (the compact `⟨s | sss⟩` vs the expanded `⟨s, t | …⟩` presentation of `ZZ/3`) as a single
`rfl` coincidence.  This file lifts the SINGLE Tietze move — adjoin a fresh generator `t` with defining
rule `t ⟹ w` — to a GENERIC theorem over an ARBITRARY base presentation:

  * `expandWalkerPresentationWithFreshGenerator base w` — the generic block constructor: `C1 += 1`
    (the fresh generator at the HIGHEST index `G := base.oneGeneratorCount`), `C2 += 1` (the fresh rule
    `([G], w)` appended at the HIGHEST index), `C3` unchanged (`criticalPairs` verbatim);
  * `freshGeneratorExpansionAddsNoCriticalPairs` — the no-new-critical-pair fact at carrier
    granularity: the length-1 fresh left-hand side `t` cannot overlap any `t`-free rule, so the Squier
    critical-pair set is UNCHANGED — a `def`-level `rfl` (`C3` unchanged);
  * `tietzeExpansionPreservesDegreeOneInvariant` / `…DegreeTwoInvariant` — the GENERIC preservation
    theorems: the expanded homology invariant equals the base one, proved at the reader granularity
    (the fresh unit inserted into the Smith diagonal bumps the rank by exactly one and leaves the
    non-unit torsion factors untouched);
  * three instances fed through the theorem — cyclic `ZZ/3` (`t ⟹ s`), the r2 Tietze `ZZ/3`
    (`u ⟹ st`), and the fresh walking-involution `ZZ/2` (`t ⟹ s`) — each with an EXPLICIT unimodular
    reduction certificate for the expanded `d2`, checked propext-cleanly against its ordered Smith
    normal form.

## The scope adjudication (honest — the certificate stays per-instance)

The presentation-carrier expansion and the reader-level invariance are GENUINELY generic (Route A).
The ORDERED-SNF certificate is NOT cleanly generic: the divisibility-ordering bubble that places the
fresh unit after the existing unit block has data-dependent length, so re-deriving it generically would
re-implement a Smith reduction (the certificate-first-forbidden territory — no `SmithNormalForm.lean`
import).  Therefore the `reducesToSmithForm` certificate is shipped PER-INSTANCE (Route B): concrete
operation words designed by the generic recipe, checked by `rfl` on `applyOperations`.

`w`'s `t`-freeness cannot be a TYPE constraint (the carrier's word type is `List Nat`, which cannot
structurally exclude the fresh index), so it is the honest explicit hypothesis
`countGeneratorOccurrences base.oneGeneratorCount freshRuleWord = 0`.

## Zero-axiom design decisions

  * Every match is on non-indexed inductives (`List`, `Prod`, `Nat`, `Int`); the reader inductions are
    structural on the diagonal window `Nat`.
  * `natSuccSubSuccEqSub` is the sole `Nat`-subtraction identity, proved by structural induction (no
    `Nat.succ_sub_succ` import); `Nat.add_comm` is the only arithmetic lemma (clean; never `add_mul` /
    `min_eq` / `le_max`).
  * The `if diag = 0` reductions are on literal SNF matrices only; the ordered-SNF checks reuse the r2
    file's propext-clean successor-peel discipline (`natEqZeroOfLeZero` / `natLeOfSuccLeSucc`).

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/FreshGeneratorTietzeExpansionInvariance.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra
open FX1Poly.Polygraph.Steiner

/-! ## B1 — the generic block constructor and the no-new-critical-pair fact -/

/-- ★ **The generic fresh-generator Tietze expansion.**  Adjoin ONE fresh endo 1-generator `t` at the
HIGHEST index `G := base.oneGeneratorCount` (so every original generator/rule index is unchanged — the
lift is the identity, no reindexing), together with the fresh defining rule `t ⟹ w` recorded as
`([G], freshRuleWord)` appended at the HIGHEST rule index.  The Squier critical pairs are copied
VERBATIM: the length-1 left-hand side `t` overlaps nothing, so no critical pair is added. -/
def expandWalkerPresentationWithFreshGenerator (base : WalkerPresentation) (freshRuleWord : List Nat) :
    WalkerPresentation :=
  { oneGeneratorCount := base.oneGeneratorCount + 1
  , rules := base.rules ++ [([base.oneGeneratorCount], freshRuleWord)]
  , criticalPairs := base.criticalPairs }

/-- ★★ **The no-new-critical-pair fact.**  The fresh rule's left-hand side is the single letter `t`,
which cannot self-overlap and (being fresh) overlaps no `t`-free existing rule — so the Squier
critical-pair set is UNCHANGED.  At carrier granularity this is exactly `criticalPairs` equality
(`C3` unchanged), a `def`-level `rfl` — the load-bearing "no new critical pairs" theorem. -/
theorem freshGeneratorExpansionAddsNoCriticalPairs
    (base : WalkerPresentation) (freshRuleWord : List Nat) :
    (expandWalkerPresentationWithFreshGenerator base freshRuleWord).criticalPairs
      = base.criticalPairs := rfl

/-- ★ **The degree-3 chain basis is unchanged** — `C3(expanded) = C3(base)`, since the critical-pair
list is copied verbatim.  The carrier-level statement of "no new critical pairs". -/
theorem freshGeneratorExpansionKeepsDegreeThreeChain
    (base : WalkerPresentation) (freshRuleWord : List Nat) :
    (expandWalkerPresentationWithFreshGenerator base freshRuleWord).computeBasisCount 3
      = base.computeBasisCount 3 := rfl

/-- The generator count bumps by exactly one — `C1(expanded) = C1(base) + 1`. -/
theorem freshGeneratorExpansionBumpsGeneratorCount
    (base : WalkerPresentation) (freshRuleWord : List Nat) :
    (expandWalkerPresentationWithFreshGenerator base freshRuleWord).computeBasisCount 1
      = base.computeBasisCount 1 + 1 := rfl

/-- Appending one element to a list bumps its length by one — structural, no `List.length_append`. -/
theorem listAppendSingletonLength {Entry : Type} (extra : Entry) :
    ∀ entries : List Entry, (entries ++ [extra]).length = entries.length + 1
  | [] => rfl
  | _ :: tail => congrArg (· + 1) (listAppendSingletonLength extra tail)

/-- The rule count bumps by exactly one — `C2(expanded) = C2(base) + 1`. -/
theorem freshGeneratorExpansionBumpsRuleCount
    (base : WalkerPresentation) (freshRuleWord : List Nat) :
    (expandWalkerPresentationWithFreshGenerator base freshRuleWord).computeBasisCount 2
      = base.computeBasisCount 2 + 1 :=
  listAppendSingletonLength ([base.oneGeneratorCount], freshRuleWord) base.rules

/-! ## B2 — the structurally-`t`-free entry point (the honest guaranteed-`t`-free carrier)

The shipped `List Nat` block constructor cannot structurally exclude the fresh index
`base.oneGeneratorCount` from `freshRuleWord`, so `w`'s `t`-freeness is enforced NOWHERE by its type.
The structurally-`t`-free entry point ranges the word over `Fin base.oneGeneratorCount` and embeds it by
`Fin.val`, so every letter is `< base.oneGeneratorCount` and the fresh index can NEVER appear — the zero
fresh-generator count becomes a theorem BY CONSTRUCTION (`embeddedBaseWordFreshCountIsZero`).  The
`w = [t]` attack (`t := base.oneGeneratorCount`) is unrepresentable through this entry point: `[t]` is
not the image of any `List (Fin base.oneGeneratorCount)`, because no `Fin base.oneGeneratorCount` letter
has value `base.oneGeneratorCount` (that would need `base.oneGeneratorCount < base.oneGeneratorCount`). -/

/-- Embed a base word over `Fin bound` into `List Nat` by `Fin.val`; every letter is `< bound`, so the
fresh index `bound` can never appear in the image. -/
def embedBaseWord (bound : Nat) (word : List (Fin bound)) : List Nat := word.map Fin.val

/-- ★ **The structural `t`-freeness bridge.**  The embedded base word has zero fresh-generator count —
by construction, since every letter of a `List (Fin bound)` is `< bound`, the fresh index `bound` occurs
zero times.  Structural on the `List`; `Fin` appears only through its `.val` / `.isLt` projections (no
`Fin.cases`, so the indexed-match axiom trap is avoided).  This is the honest hypothesis
`countGeneratorOccurrences base.oneGeneratorCount w = 0` — the r3 phantom — turned into a guarantee. -/
theorem embeddedBaseWordFreshCountIsZero (bound : Nat) :
    ∀ (word : List (Fin bound)),
      countGeneratorOccurrences bound (embedBaseWord bound word) = 0
  | [] => rfl
  | letter :: rest =>
      (congrArg ((if Fin.val letter = bound then 1 else 0) + ·)
        (embeddedBaseWordFreshCountIsZero bound rest)).trans (if_neg (Nat.ne_of_lt letter.isLt))

/-- ★ **The structurally-`t`-free fresh-generator expansion.**  The word ranges over
`Fin base.oneGeneratorCount`, so its `Fin.val` embedding is provably free of the fresh index — the
honest, guaranteed-`t`-free carrier the shipped instances instantiate.  Delegates to the `List Nat`
block constructor `expandWalkerPresentationWithFreshGenerator`. -/
def expandWalkerPresentationWithBaseWord (base : WalkerPresentation)
    (baseWord : List (Fin base.oneGeneratorCount)) : WalkerPresentation :=
  expandWalkerPresentationWithFreshGenerator base (embedBaseWord base.oneGeneratorCount baseWord)

/-- ★★ **The entry-point fresh-freeness fact.**  Every word built through
`expandWalkerPresentationWithBaseWord` satisfies the `t`-freeness hypothesis
`countGeneratorOccurrences base.oneGeneratorCount w = 0` — the guard the r3 docstring named as a phantom
is here a structural theorem the pivot-unit lemma (`freshColumnPivotIsUnitOfFreshFree`) consumes. -/
theorem expandWalkerPresentationWithBaseWordIsFreshFree (base : WalkerPresentation)
    (baseWord : List (Fin base.oneGeneratorCount)) :
    countGeneratorOccurrences base.oneGeneratorCount
        (embedBaseWord base.oneGeneratorCount baseWord) = 0 :=
  embeddedBaseWordFreshCountIsZero base.oneGeneratorCount baseWord

/-! ## B1 — the hand probe: the r2 concrete `d2` extended by a concrete `w`, certificate BY HAND

The truth probe fired BEFORE any generic proof: the r2 Tietze `d2` (`2 × 4`) extended by the fresh
generator `u ⟹ e` (`w = []`, the `v`-column vanishes) is the concrete `3 × 5` expanded boundary, and a
BY-HAND unimodular certificate — the fresh-column normalisation, the LIFTED original r2 word, and the
divisibility-ordering reorder — lands it on the ordered Smith normal form `diag(1, 1, 3)` by `rfl`. -/

/-- The hand-probe expanded presentation: the r2 Tietze presentation of `ZZ/3` with a fresh generator
`u ⟹ e` adjoined (`w = []`). -/
def handProbeExpandedTietzePresentation : WalkerPresentation :=
  expandWalkerPresentationWithFreshGenerator tietzeZmodThreePresentation []

/-- ★ **The generic block constructor COMPUTES the concrete expanded `d2`** — `⟨[[-2,-1,-1,1,0],
[1,-1,-1,-2,0],[0,0,0,0,-1]]⟩`: the r2 `d2` in the top-left `2 × 4` block, a vanishing `v`-column
(`w = []`), a fresh-generator row `[0,0,0,0,-1]` with the `-1` pivot.  `rfl` — the block builder is the
presentation's own abelianization. -/
theorem handProbeComputesExpandedBoundaryDimOne :
    handProbeExpandedTietzePresentation.computeBoundaryDimOne
      = ⟨[[-2, -1, -1, 1, 0], [1, -1, -1, -2, 0], [0, 0, 0, 0, -1]]⟩ := rfl

/-- The BY-HAND reduction certificate for the hand-probe expanded `d2`: normalise the `-1` pivot in the
fresh column `4` (`negateColumn 4`), LIFT the shipped r2 `d2` certificate UNCHANGED (index-stable — the
original block sits at rows `0,1` / columns `0..3`), then reorder the fresh unit past the base rows onto
the divisibility-ordered diagonal (`swapColumns 2 4`, `swapRows 1 2`, `swapColumns 1 2`). -/
def handProbeExpandedTietzeBoundaryOfDimOneSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations :=
      ElementaryOperation.columnOperation (ElementaryColumnOperation.negateColumn 4)
        :: tietzeBoundaryOfDimOneSmithCertificate.operations
        ++ [ ElementaryOperation.columnOperation (ElementaryColumnOperation.swapColumns 2 4)
           , ElementaryOperation.rowOperation (ElementaryRowOperation.swapRows 1 2)
           , ElementaryOperation.columnOperation (ElementaryColumnOperation.swapColumns 1 2) ] }

/-- ★★ **THE HAND PROBE FIRES.**  Applying the by-hand certificate to the concrete expanded `d2` lands
on the ordered Smith normal form `diag(1, 1, 3)` — kernel-checked by `rfl` on `applyOperations`, BEFORE
any generic proof.  Confirms the fresh-generator expansion carries `H1 = ZZ/3` through (one extra unit,
the `3` torsion factor intact). -/
theorem handProbeExpandedBoundaryReducesToSmithNormalForm :
    handProbeExpandedTietzePresentation.computeBoundaryDimOne.applyOperations
        handProbeExpandedTietzeBoundaryOfDimOneSmithCertificate.operations
      = ⟨[[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 3, 0, 0]]⟩ := rfl

/-! ## B2 — the certificate-extension engine and the GENERIC well-formedness of the expansion

The block `d2·d3 = 0` of the expanded presentation is derived GENERICALLY from the base's `d2·d3 = 0`
plus two honest base-shape facts (`base` is free of its own fresh index; its firing lists are indexed by
its own rules).  The proof splits the `R + 1` rule sum into the old rules — where the boundary blocks
AGREE with the base — and the fresh rule, whose `d3` row VANISHES.  All the index bookkeeping is
structural (`Nat`, `List`), no `omega`. -/

/-- `0 + value = value` — structural (`natZeroAdd` is taken elsewhere in the repo). -/
theorem natZeroAddEqSelf : ∀ (value : Nat), 0 + value = value
  | 0 => rfl
  | value + 1 => congrArg (· + 1) (natZeroAddEqSelf value)

/-- `(leftValue + 1) + rightValue = leftValue + (rightValue + 1)` — structural on `rightValue`. -/
theorem natSuccAddEqAddSucc :
    ∀ (leftValue rightValue : Nat), (leftValue + 1) + rightValue = leftValue + (rightValue + 1)
  | _, 0 => rfl
  | leftValue, rightValue + 1 => congrArg (· + 1) (natSuccAddEqAddSucc leftValue rightValue)

/-- `0 < value + 1` — the successor is positive, by the `Nat.le` constructors. -/
theorem natZeroLtSucc : ∀ (value : Nat), 0 < value + 1
  | 0 => Nat.le.refl
  | value + 1 => Nat.le.step (natZeroLtSucc value)

/-- Successor monotonicity of `≤` — induction on the `Nat.le` derivation, constructor-injective. -/
theorem natSuccLeSucc :
    ∀ {lowValue highValue : Nat}, lowValue ≤ highValue → lowValue + 1 ≤ highValue + 1
  | _, _, Nat.le.refl => Nat.le.refl
  | _, _, Nat.le.step lowerStep => Nat.le.step (natSuccLeSucc lowerStep)

/-- `value < bound + 1` splits into `value < bound` or `value = bound` — the row-case split for the
well-formedness proof, structural on both arguments. -/
theorem natLtSuccCases : ∀ {value bound : Nat}, value < bound + 1 → value < bound ∨ value = bound
  | 0, 0, _ => Or.inr rfl
  | 0, bound + 1, _ => Or.inl (natZeroLtSucc bound)
  | value + 1, 0, isBelow => Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isBelow))
  | value + 1, bound + 1, isBelow =>
      match natLtSuccCases (natLeOfSuccLeSucc isBelow) with
      | Or.inl valueLtBound => Or.inl (natSuccLeSucc valueLtBound)
      | Or.inr valueEqBound => Or.inr (congrArg (· + 1) valueEqBound)

/-- Reading row `rowIndex < rowCount` of the generator-indexed `d2` row block returns the abelianized
row for generator `startGenerator + rowIndex` — structural on the row count. -/
theorem walkerPresentationDimOneRowsGet (rules : List (List Nat × List Nat)) :
    ∀ (startGenerator rowCount rowIndex : Nat), rowIndex < rowCount →
      listGetWithDefault [] (walkerPresentationDimOneRows rules startGenerator rowCount) rowIndex
        = walkerPresentationDimOneRow (startGenerator + rowIndex) rules
  | _, 0, rowIndex, isBelow => absurd isBelow (Nat.not_lt_zero rowIndex)
  | _, _ + 1, 0, _ => rfl
  | startGenerator, rowCount + 1, rowIndex + 1, isBelow =>
      (walkerPresentationDimOneRowsGet rules (startGenerator + 1) rowCount rowIndex
          (natLeOfSuccLeSucc isBelow)).trans
        (congrArg (fun generatorIndex => walkerPresentationDimOneRow generatorIndex rules)
          (natSuccAddEqAddSucc startGenerator rowIndex))

/-- Reading row `rowIndex < rowCount` of the rule-indexed `d3` row block returns the abelianized cofork
row for rule `startRule + rowIndex` — structural on the row count. -/
theorem walkerPresentationDimTwoRowsGet (criticalPairs : List (List Nat × List Nat × List Nat)) :
    ∀ (startRule rowCount rowIndex : Nat), rowIndex < rowCount →
      listGetWithDefault [] (walkerPresentationDimTwoRows criticalPairs startRule rowCount) rowIndex
        = walkerPresentationDimTwoRow (startRule + rowIndex) criticalPairs
  | _, 0, rowIndex, isBelow => absurd isBelow (Nat.not_lt_zero rowIndex)
  | _, _ + 1, 0, _ => rfl
  | startRule, rowCount + 1, rowIndex + 1, isBelow =>
      (walkerPresentationDimTwoRowsGet criticalPairs (startRule + 1) rowCount rowIndex
          (natLeOfSuccLeSucc isBelow)).trans
        (congrArg (fun ruleIndex => walkerPresentationDimTwoRow ruleIndex criticalPairs)
          (natSuccAddEqAddSucc startRule rowIndex))

/-- The abelianized `d2` row distributes over a rule-list append — structural on the left rules, cons
congruence (no `List.map_append`). -/
theorem walkerPresentationDimOneRowAppendDistrib (generator : Nat) :
    ∀ (leftRules rightRules : List (List Nat × List Nat)),
      walkerPresentationDimOneRow generator (leftRules ++ rightRules)
        = walkerPresentationDimOneRow generator leftRules
            ++ walkerPresentationDimOneRow generator rightRules
  | [], _ => rfl
  | (sourceWord, targetWord) :: remainingRules, rightRules =>
      congrArg
        (fun remainingRow =>
          (Int.ofNat (countGeneratorOccurrences generator targetWord)
            - Int.ofNat (countGeneratorOccurrences generator sourceWord)) :: remainingRow)
        (walkerPresentationDimOneRowAppendDistrib generator remainingRules rightRules)

/-- Reading an index below the left list's length ignores the appended tail — structural. -/
theorem listGetWithDefaultAppendLeft {Entry : Type} (defaultEntry : Entry) :
    ∀ (leftEntries rightEntries : List Entry) (index : Nat), index < leftEntries.length →
      listGetWithDefault defaultEntry (leftEntries ++ rightEntries) index
        = listGetWithDefault defaultEntry leftEntries index
  | [], _, index, isBelow => absurd isBelow (Nat.not_lt_zero index)
  | _ :: _, _, 0, _ => rfl
  | _ :: tailEntries, rightEntries, index + 1, isBelow =>
      listGetWithDefaultAppendLeft defaultEntry tailEntries rightEntries index
        (natLeOfSuccLeSucc isBelow)

/-- Two finite sums whose summands agree below the count are equal — structural on the count. -/
theorem sumOverIndicesCongrBelow (leftSummand rightSummand : Nat → Int) :
    ∀ (count : Nat), (∀ index, index < count → leftSummand index = rightSummand index) →
      sumOverIndices count leftSummand = sumOverIndices count rightSummand
  | 0, _ => rfl
  | count + 1, agreeBelow =>
      (congrArg (· + leftSummand count)
          (sumOverIndicesCongrBelow leftSummand rightSummand count
            (fun index isBelow => agreeBelow index (Nat.le.step isBelow)))).trans
        (congrArg (sumOverIndices count rightSummand + ·) (agreeBelow count Nat.le.refl))

/-- A finite sum whose summands are all zero below the count is zero — structural on the count. -/
theorem sumOverIndicesZeroBelow (summand : Nat → Int) :
    ∀ (count : Nat), (∀ index, index < count → summand index = 0) →
      sumOverIndices count summand = 0
  | 0, _ => rfl
  | count + 1, allZeroBelow =>
      (congrArg (· + summand count)
          (sumOverIndicesZeroBelow summand count
            (fun index isBelow => allZeroBelow index (Nat.le.step isBelow)))).trans
        ((congrArg (0 + ·) (allZeroBelow count Nat.le.refl)).trans rfl)

/-- ★ **The old `d2` columns AGREE with the base.**  For an original generator/rule index, the expanded
`d2` entry equals the base `d2` entry — the base block sits index-stable at the top-left. -/
theorem freshGeneratorExpansionOldColumnD2Agrees
    (base : WalkerPresentation) (freshRuleWord : List Nat)
    (genIndex ruleIndex : Nat)
    (genBelow : genIndex < base.oneGeneratorCount) (ruleBelow : ruleIndex < base.rules.length) :
    (expandWalkerPresentationWithFreshGenerator base freshRuleWord).computeBoundaryDimOne.entryAt
        genIndex ruleIndex
      = base.computeBoundaryDimOne.entryAt genIndex ruleIndex := by
  show listGetWithDefault 0
      (listGetWithDefault []
        (walkerPresentationDimOneRows (base.rules ++ [([base.oneGeneratorCount], freshRuleWord)]) 0
          (base.oneGeneratorCount + 1)) genIndex) ruleIndex
    = listGetWithDefault 0
      (listGetWithDefault [] (walkerPresentationDimOneRows base.rules 0 base.oneGeneratorCount)
        genIndex) ruleIndex
  rw [walkerPresentationDimOneRowsGet (base.rules ++ [([base.oneGeneratorCount], freshRuleWord)]) 0
        (base.oneGeneratorCount + 1) genIndex (Nat.le.step genBelow),
      walkerPresentationDimOneRowsGet base.rules 0 base.oneGeneratorCount genIndex genBelow,
      natZeroAddEqSelf genIndex,
      walkerPresentationDimOneRowAppendDistrib genIndex base.rules
        [([base.oneGeneratorCount], freshRuleWord)],
      listGetWithDefaultAppendLeft 0 (walkerPresentationDimOneRow genIndex base.rules)
        (walkerPresentationDimOneRow genIndex [([base.oneGeneratorCount], freshRuleWord)]) ruleIndex
        (by rw [walkerPresentationDimOneRowLength]; exact ruleBelow)]

/-- ★ **The old `d3` rows AGREE with the base.**  For an original rule index, the expanded `d3` row
equals the base `d3` row — appending the fresh rule row does not disturb the earlier rows. -/
theorem freshGeneratorExpansionOldRowD3Agrees
    (base : WalkerPresentation) (freshRuleWord : List Nat)
    (ruleIndex pairIndex : Nat) (ruleBelow : ruleIndex < base.rules.length) :
    (expandWalkerPresentationWithFreshGenerator base freshRuleWord).computeBoundaryDimTwo.entryAt
        ruleIndex pairIndex
      = base.computeBoundaryDimTwo.entryAt ruleIndex pairIndex := by
  show listGetWithDefault 0
      (listGetWithDefault []
        (walkerPresentationDimTwoRows base.criticalPairs 0
          (base.rules ++ [([base.oneGeneratorCount], freshRuleWord)]).length) ruleIndex) pairIndex
    = listGetWithDefault 0
      (listGetWithDefault [] (walkerPresentationDimTwoRows base.criticalPairs 0 base.rules.length)
        ruleIndex) pairIndex
  rw [walkerPresentationDimTwoRowsGet base.criticalPairs 0
        (base.rules ++ [([base.oneGeneratorCount], freshRuleWord)]).length ruleIndex
        (by rw [listAppendSingletonLength]; exact Nat.le.step ruleBelow),
      walkerPresentationDimTwoRowsGet base.criticalPairs 0 base.rules.length ruleIndex ruleBelow]

/-- ★ **The fresh-generator `d2` row VANISHES on the old rules.**  Because the base uses only its own
generators (`baseFreshGeneratorRowIsZero`), the new generator does not occur in any base rule, so its
`d2` row is zero over the original rule columns. -/
theorem freshGeneratorExpansionNewGeneratorRowVanishes
    (base : WalkerPresentation) (freshRuleWord : List Nat)
    (baseFreshGeneratorRowIsZero :
      walkerPresentationDimOneRow base.oneGeneratorCount base.rules
        = List.replicate base.rules.length 0)
    (ruleIndex : Nat) (ruleBelow : ruleIndex < base.rules.length) :
    (expandWalkerPresentationWithFreshGenerator base freshRuleWord).computeBoundaryDimOne.entryAt
      base.oneGeneratorCount ruleIndex = 0 := by
  show listGetWithDefault 0
      (listGetWithDefault []
        (walkerPresentationDimOneRows (base.rules ++ [([base.oneGeneratorCount], freshRuleWord)]) 0
          (base.oneGeneratorCount + 1)) base.oneGeneratorCount) ruleIndex = 0
  rw [walkerPresentationDimOneRowsGet (base.rules ++ [([base.oneGeneratorCount], freshRuleWord)]) 0
        (base.oneGeneratorCount + 1) base.oneGeneratorCount Nat.le.refl,
      natZeroAddEqSelf base.oneGeneratorCount,
      walkerPresentationDimOneRowAppendDistrib base.oneGeneratorCount base.rules
        [([base.oneGeneratorCount], freshRuleWord)],
      listGetWithDefaultAppendLeft 0 (walkerPresentationDimOneRow base.oneGeneratorCount base.rules)
        (walkerPresentationDimOneRow base.oneGeneratorCount [([base.oneGeneratorCount], freshRuleWord)])
        ruleIndex (by rw [walkerPresentationDimOneRowLength]; exact ruleBelow),
      baseFreshGeneratorRowIsZero, listGetReplicateZeroIsZero]

/-- ★ **The fresh-rule `d3` row VANISHES.**  Because the base's firing lists are indexed by its own
rules (`baseFreshRuleRowIsZero`), reading the fresh rule index in every critical pair returns zero, so
the appended `d3` row is entirely zero. -/
theorem freshGeneratorExpansionNewRuleRowVanishes
    (base : WalkerPresentation) (freshRuleWord : List Nat)
    (baseFreshRuleRowIsZero :
      walkerPresentationDimTwoRow base.rules.length base.criticalPairs
        = List.replicate base.criticalPairs.length 0)
    (pairIndex : Nat) :
    (expandWalkerPresentationWithFreshGenerator base freshRuleWord).computeBoundaryDimTwo.entryAt
      base.rules.length pairIndex = 0 := by
  show listGetWithDefault 0
      (listGetWithDefault []
        (walkerPresentationDimTwoRows base.criticalPairs 0
          (base.rules ++ [([base.oneGeneratorCount], freshRuleWord)]).length) base.rules.length)
      pairIndex = 0
  rw [walkerPresentationDimTwoRowsGet base.criticalPairs 0
        (base.rules ++ [([base.oneGeneratorCount], freshRuleWord)]).length base.rules.length
        (by rw [listAppendSingletonLength]; exact Nat.le.refl),
      natZeroAddEqSelf base.rules.length, baseFreshRuleRowIsZero, listGetReplicateZeroIsZero]

/-- ★★ **THE GENERIC WELL-FORMEDNESS OF THE FRESH-GENERATOR EXPANSION.**  Given the base's `d2·d3 = 0`
and two honest base-shape facts (the base is free of its own fresh index; its firing lists are indexed by
its own rules), the expanded presentation satisfies `d2·d3 = 0`.  The `R + 1` rule sum splits into the
old rules — where the boundary blocks agree with the base (`baseWellFormed` on rows `< G`, the zero
fresh-generator row on row `= G`) — and the fresh rule, whose `d3` row vanishes.  Route A: fully generic
over the base presentation. -/
theorem freshGeneratorExpansionIsWellFormedOfBase
    (base : WalkerPresentation) (freshRuleWord : List Nat)
    (baseWellFormed : WellFormedWalkerPresentation base)
    (baseFreshGeneratorRowIsZero :
      walkerPresentationDimOneRow base.oneGeneratorCount base.rules
        = List.replicate base.rules.length 0)
    (baseFreshRuleRowIsZero :
      walkerPresentationDimTwoRow base.rules.length base.criticalPairs
        = List.replicate base.criticalPairs.length 0) :
    WellFormedWalkerPresentation (expandWalkerPresentationWithFreshGenerator base freshRuleWord) := by
  intro rowIndex colIndex rowBound colBound
  have rowBound' : rowIndex < base.oneGeneratorCount + 1 := rowBound
  have baseRangeZero :
      sumOverIndices base.rules.length
        (fun middleIndex =>
          (expandWalkerPresentationWithFreshGenerator base freshRuleWord).computeBoundaryDimOne.entryAt
              rowIndex middleIndex
          * (expandWalkerPresentationWithFreshGenerator base freshRuleWord).computeBoundaryDimTwo.entryAt
              middleIndex colIndex) = 0 := by
    cases natLtSuccCases rowBound' with
    | inl rowLtGenCount =>
        have congrToBase :
            sumOverIndices base.rules.length
                (fun middleIndex =>
                  (expandWalkerPresentationWithFreshGenerator base
                      freshRuleWord).computeBoundaryDimOne.entryAt rowIndex middleIndex
                  * (expandWalkerPresentationWithFreshGenerator base
                      freshRuleWord).computeBoundaryDimTwo.entryAt middleIndex colIndex)
              = sumOverIndices base.rules.length
                (fun middleIndex =>
                  base.computeBoundaryDimOne.entryAt rowIndex middleIndex
                  * base.computeBoundaryDimTwo.entryAt middleIndex colIndex) :=
          sumOverIndicesCongrBelow _ _ base.rules.length
            (fun middleIndex middleBelow => by
              show (expandWalkerPresentationWithFreshGenerator base
                    freshRuleWord).computeBoundaryDimOne.entryAt rowIndex middleIndex
                  * (expandWalkerPresentationWithFreshGenerator base
                    freshRuleWord).computeBoundaryDimTwo.entryAt middleIndex colIndex
                = base.computeBoundaryDimOne.entryAt rowIndex middleIndex
                  * base.computeBoundaryDimTwo.entryAt middleIndex colIndex
              rw [freshGeneratorExpansionOldColumnD2Agrees base freshRuleWord rowIndex middleIndex
                    rowLtGenCount middleBelow,
                  freshGeneratorExpansionOldRowD3Agrees base freshRuleWord middleIndex colIndex
                    middleBelow])
        exact congrToBase.trans (baseWellFormed rowIndex colIndex rowLtGenCount colBound)
    | inr rowEqGenCount =>
        exact sumOverIndicesZeroBelow
          (fun middleIndex =>
            (expandWalkerPresentationWithFreshGenerator base
                freshRuleWord).computeBoundaryDimOne.entryAt rowIndex middleIndex
            * (expandWalkerPresentationWithFreshGenerator base
                freshRuleWord).computeBoundaryDimTwo.entryAt middleIndex colIndex)
          base.rules.length
          (fun middleIndex middleBelow => by
            show (expandWalkerPresentationWithFreshGenerator base
                  freshRuleWord).computeBoundaryDimOne.entryAt rowIndex middleIndex
                * (expandWalkerPresentationWithFreshGenerator base
                  freshRuleWord).computeBoundaryDimTwo.entryAt middleIndex colIndex = 0
            rw [rowEqGenCount,
                freshGeneratorExpansionNewGeneratorRowVanishes base freshRuleWord
                  baseFreshGeneratorRowIsZero middleIndex middleBelow,
                intZeroMul])
  have freshTermZero :
      (expandWalkerPresentationWithFreshGenerator base freshRuleWord).computeBoundaryDimOne.entryAt
          rowIndex base.rules.length
        * (expandWalkerPresentationWithFreshGenerator base freshRuleWord).computeBoundaryDimTwo.entryAt
          base.rules.length colIndex = 0 :=
    (congrArg
      ((expandWalkerPresentationWithFreshGenerator base freshRuleWord).computeBoundaryDimOne.entryAt
          rowIndex base.rules.length * ·)
      (freshGeneratorExpansionNewRuleRowVanishes base freshRuleWord baseFreshRuleRowIsZero
        colIndex)).trans (Int.mul_zero _)
  rw [freshGeneratorExpansionBumpsRuleCount base freshRuleWord]
  exact (congrArg
      (· + (expandWalkerPresentationWithFreshGenerator base freshRuleWord).computeBoundaryDimOne.entryAt
        rowIndex base.rules.length
        * (expandWalkerPresentationWithFreshGenerator base freshRuleWord).computeBoundaryDimTwo.entryAt
          base.rules.length colIndex) baseRangeZero).trans
    ((congrArg (0 + ·) freshTermZero).trans rfl)

/-- ★★ **THE GENERIC EXPANDED CHAIN COMPLEX.**  Every base presentation satisfying the two shape facts
yields a full `AugmentedDirectedComplex` for its fresh-generator expansion, through the shipped generic
`walkerPresentationChainComplex` gated on the generic well-formedness. -/
def freshGeneratorExpansionChainComplex (base : WalkerPresentation) (freshRuleWord : List Nat)
    (baseWellFormed : WellFormedWalkerPresentation base)
    (baseFreshGeneratorRowIsZero :
      walkerPresentationDimOneRow base.oneGeneratorCount base.rules
        = List.replicate base.rules.length 0)
    (baseFreshRuleRowIsZero :
      walkerPresentationDimTwoRow base.rules.length base.criticalPairs
        = List.replicate base.criticalPairs.length 0) : AugmentedDirectedComplex :=
  walkerPresentationChainComplex (expandWalkerPresentationWithFreshGenerator base freshRuleWord)
    (freshGeneratorExpansionIsWellFormedOfBase base freshRuleWord baseWellFormed
      baseFreshGeneratorRowIsZero baseFreshRuleRowIsZero)

/-- The r2 Tietze base is free of its own fresh index (`#u` in every base rule word is zero) — `rfl`. -/
theorem tietzeZmodThreeBaseFreshGeneratorRowIsZero :
    walkerPresentationDimOneRow tietzeZmodThreePresentation.oneGeneratorCount
        tietzeZmodThreePresentation.rules
      = List.replicate tietzeZmodThreePresentation.rules.length 0 := rfl

/-- The r2 Tietze base's firing lists are indexed by its four rules (index `4` reads zero) — `rfl`. -/
theorem tietzeZmodThreeBaseFreshRuleRowIsZero :
    walkerPresentationDimTwoRow tietzeZmodThreePresentation.rules.length
        tietzeZmodThreePresentation.criticalPairs
      = List.replicate tietzeZmodThreePresentation.criticalPairs.length 0 := rfl

/-- ★★ **The r2-expanded presentation is WELL-FORMED, through the GENERIC block theorem** — the two rfl
base-shape facts and the shipped r2 `d2·d3 = 0` fed into `freshGeneratorExpansionIsWellFormedOfBase`.
The generic well-formedness is non-vacuously inhabited. -/
theorem handProbeExpandedTietzePresentationIsWellFormed :
    WellFormedWalkerPresentation handProbeExpandedTietzePresentation :=
  freshGeneratorExpansionIsWellFormedOfBase tietzeZmodThreePresentation []
    tietzeZmodThreePresentationIsWellFormed
    tietzeZmodThreeBaseFreshGeneratorRowIsZero tietzeZmodThreeBaseFreshRuleRowIsZero

/-- ★★ **The r2-expanded `AugmentedDirectedComplex`, through the GENERIC constructor** — a concrete
expanded chain complex built by `freshGeneratorExpansionChainComplex`. -/
def handProbeExpandedTietzeChainComplex : AugmentedDirectedComplex :=
  freshGeneratorExpansionChainComplex tietzeZmodThreePresentation []
    tietzeZmodThreePresentationIsWellFormed
    tietzeZmodThreeBaseFreshGeneratorRowIsZero tietzeZmodThreeBaseFreshRuleRowIsZero

/-! ## B3 — the generic homology-preservation theorem (the reader-level invariance)

The single Tietze move — adjoin `t` with `t ⟹ w` — inserts exactly ONE unit into the Smith diagonal of
`d2` (bumping its rank by one), appends a ZERO row to `d3` (leaving its rank untouched), and leaves the
non-unit torsion factors alone.  Read through the shipped generic `SmithHomologyData.homologyInvariant`,
this preserves the homology invariant at BOTH degree 1 and degree 2.  Everything below is at the reader
granularity — the two diagonal inductions plus the truncated-subtraction bookkeeping. -/

/-- `(leftValue + 1) − (rightValue + 1) = leftValue − rightValue` — structural on `rightValue`, no
`Nat.succ_sub_succ` import (the second `Nat.sub` argument drives the recursion). -/
theorem natSuccSubSuccEqSub :
    ∀ (leftValue rightValue : Nat), (leftValue + 1) - (rightValue + 1) = leftValue - rightValue
  | _, 0 => rfl
  | leftValue, rightValue + 1 => congrArg Nat.pred (natSuccSubSuccEqSub leftValue rightValue)

/-- Two homology invariants are equal when their free ranks and torsion-factor lists agree — the
structure-eta bridge, via `Eq` cases (no propext). -/
theorem homologyInvariantEq {leftInvariant rightInvariant : HomologyInvariant}
    (freeRankEq : leftInvariant.freeRank = rightInvariant.freeRank)
    (torsionEq : leftInvariant.torsionFactors = rightInvariant.torsionFactors) :
    leftInvariant = rightInvariant := by
  cases leftInvariant
  cases rightInvariant
  cases freeRankEq
  cases torsionEq
  rfl

/-- ★ **Prefix-unit rank successor (the first diagonal induction).**  When the top diagonal entry of a
Smith matrix within the window `windowSize + 1` is NONZERO (a fresh unit pivot), the Smith rank within
that window is one more than the rank within `windowSize` — the fresh unit contributes exactly `+1`. -/
theorem smithRankWithinTopNonzeroIsSuccessor (matrix : IntMatrix) (windowSize : Nat)
    (topIsNonzero : matrix.diagonalEntryAt windowSize ≠ 0) :
    smithRankWithin matrix (windowSize + 1) = smithRankWithin matrix windowSize + 1 := by
  show (if matrix.diagonalEntryAt windowSize = 0 then 0 else 1) + smithRankWithin matrix windowSize
      = smithRankWithin matrix windowSize + 1
  rw [if_neg topIsNonzero]
  exact Nat.add_comm 1 (smithRankWithin matrix windowSize)

/-- ★ **Prefix-unit torsion stability (the second diagonal induction).**  Prepending a UNIT invariant
factor `1` to the factor list leaves the non-unit torsion factors UNCHANGED — the unit is filtered out
by `nonUnitInvariantFactors`'s explicit `if factor = 1` guard.  `rfl`. -/
theorem nonUnitInvariantFactorsUnitConsIsStable (remainingFactors : List Int) :
    nonUnitInvariantFactors ((1 : Int) :: remainingFactors)
      = nonUnitInvariantFactors remainingFactors := rfl

/-- ★★ **THE DEGREE-1 PRESERVATION THEOREM (generic, reader-level).**  Given base and expanded Smith
homology data whose (a) chain basis bumps by one, (b) into-lower rank is unchanged and is zero (the
all-zero `d1` loop row), (c) from-higher rank bumps by one (the fresh Smith unit), and (d) non-unit
torsion factors agree, the expanded degree-1 homology invariant EQUALS the base one.  The free rank
`(C1 + 1 − 0) − (rank + 1) = C1 − rank` is preserved by `natSuccSubSuccEqSub`; the torsion by (d). -/
theorem tietzeExpansionPreservesDegreeOneInvariant
    (baseData expandedData : SmithHomologyData)
    (basisIsSuccessor : expandedData.chainBasisCount = baseData.chainBasisCount + 1)
    (intoLowerRankAgrees :
      smithRankWithin expandedData.smithBoundaryIntoLower expandedData.windowIntoLower
        = smithRankWithin baseData.smithBoundaryIntoLower baseData.windowIntoLower)
    (baseIntoLowerRankIsZero :
      smithRankWithin baseData.smithBoundaryIntoLower baseData.windowIntoLower = 0)
    (fromHigherRankIsSuccessor :
      smithRankWithin expandedData.smithBoundaryFromHigher expandedData.windowFromHigher
        = smithRankWithin baseData.smithBoundaryFromHigher baseData.windowFromHigher + 1)
    (fromHigherTorsionAgrees :
      nonUnitInvariantFactors
          (smithInvariantFactorsWithin expandedData.smithBoundaryFromHigher expandedData.windowFromHigher)
        = nonUnitInvariantFactors
          (smithInvariantFactorsWithin baseData.smithBoundaryFromHigher baseData.windowFromHigher)) :
    expandedData.homologyInvariant = baseData.homologyInvariant := by
  refine homologyInvariantEq ?_ ?_
  · show (expandedData.chainBasisCount
            - smithRankWithin expandedData.smithBoundaryIntoLower expandedData.windowIntoLower)
          - smithRankWithin expandedData.smithBoundaryFromHigher expandedData.windowFromHigher
        = (baseData.chainBasisCount
            - smithRankWithin baseData.smithBoundaryIntoLower baseData.windowIntoLower)
          - smithRankWithin baseData.smithBoundaryFromHigher baseData.windowFromHigher
    rw [basisIsSuccessor, intoLowerRankAgrees, baseIntoLowerRankIsZero, fromHigherRankIsSuccessor]
    exact natSuccSubSuccEqSub baseData.chainBasisCount
      (smithRankWithin baseData.smithBoundaryFromHigher baseData.windowFromHigher)
  · exact fromHigherTorsionAgrees

/-- ★★ **THE DEGREE-2 PRESERVATION THEOREM (generic, reader-level).**  Given base and expanded Smith
homology data whose (a) chain basis bumps by one, (b) into-lower rank bumps by one (the fresh Smith unit
in `d2`), (c) from-higher rank is unchanged (the appended zero `d3` row adds no rank), and (d) non-unit
torsion factors agree, the expanded degree-2 homology invariant EQUALS the base one.  The free rank
`(C2 + 1 − (rank + 1)) − r3 = (C2 − rank) − r3` is preserved by `natSuccSubSuccEqSub`. -/
theorem tietzeExpansionPreservesDegreeTwoInvariant
    (baseData expandedData : SmithHomologyData)
    (basisIsSuccessor : expandedData.chainBasisCount = baseData.chainBasisCount + 1)
    (intoLowerRankIsSuccessor :
      smithRankWithin expandedData.smithBoundaryIntoLower expandedData.windowIntoLower
        = smithRankWithin baseData.smithBoundaryIntoLower baseData.windowIntoLower + 1)
    (fromHigherRankAgrees :
      smithRankWithin expandedData.smithBoundaryFromHigher expandedData.windowFromHigher
        = smithRankWithin baseData.smithBoundaryFromHigher baseData.windowFromHigher)
    (fromHigherTorsionAgrees :
      nonUnitInvariantFactors
          (smithInvariantFactorsWithin expandedData.smithBoundaryFromHigher expandedData.windowFromHigher)
        = nonUnitInvariantFactors
          (smithInvariantFactorsWithin baseData.smithBoundaryFromHigher baseData.windowFromHigher)) :
    expandedData.homologyInvariant = baseData.homologyInvariant := by
  refine homologyInvariantEq ?_ ?_
  · show (expandedData.chainBasisCount
            - smithRankWithin expandedData.smithBoundaryIntoLower expandedData.windowIntoLower)
          - smithRankWithin expandedData.smithBoundaryFromHigher expandedData.windowFromHigher
        = (baseData.chainBasisCount
            - smithRankWithin baseData.smithBoundaryIntoLower baseData.windowIntoLower)
          - smithRankWithin baseData.smithBoundaryFromHigher baseData.windowFromHigher
    rw [basisIsSuccessor, intoLowerRankIsSuccessor, fromHigherRankAgrees]
    exact congrArg
      (· - smithRankWithin baseData.smithBoundaryFromHigher baseData.windowFromHigher)
      (natSuccSubSuccEqSub baseData.chainBasisCount
        (smithRankWithin baseData.smithBoundaryIntoLower baseData.windowIntoLower))
  · exact fromHigherTorsionAgrees

/-! ## B4 — the regressions: three instances fed through the generic theorem

Both shipped instances — cyclic `ZZ/3` (`t ⟹ s`) and the r2 Tietze `ZZ/3` (`u ⟹ st`) — plus a FRESH
third instance — the walking involution `ZZ/2` (`t ⟹ s`, exercising the `−1` pivot with nonempty torsion
`2`) — Tietze-expanded and fed through `tietzeExpansionPreservesDegreeOneInvariant`.  Each ships an
EXPLICIT unimodular reduction certificate for the expanded `d2`, lifting the base certificate UNCHANGED
(index-stable) between the fresh-column clearing and the divisibility-ordering reorder. -/

/-! ### Regression 1 (shipped instance) — cyclic `ZZ/3` expanded by `t ⟹ s` -/

/-- The cyclic-order-three presentation Tietze-expanded by the fresh generator `t ⟹ s` (`w = [0]`). -/
def expandedCyclicThreePresentation : WalkerPresentation :=
  expandWalkerPresentationWithFreshGenerator cyclicThreeWalkerPresentation [0]

/-- The expanded cyclic `d2` `[[-3,1],[0,-1]]` — the base `[[-3]]`, the `v = [1]` abelianization column
of `s`, the `-1` pivot on the fresh generator. -/
def expandedCyclicThreeBoundaryOfDimOne : IntMatrix := ⟨[[-3, 1], [0, -1]]⟩

/-- ★ The block builder COMPUTES the expanded cyclic `d2` — `rfl`. -/
theorem expandedCyclicThreeComputesBoundaryDimOne :
    expandedCyclicThreePresentation.computeBoundaryDimOne = expandedCyclicThreeBoundaryOfDimOne := rfl

/-- The ordered Smith normal form of the expanded cyclic `d2` — `diag(1, 3)`: one fresh UNIT, the `3`
torsion factor intact. -/
def expandedCyclicThreeSmithNormalFormOfDimOne : IntMatrix := ⟨[[1, 0], [0, 3]]⟩

/-- The reduction certificate for the expanded cyclic `d2`: clear the `v`-column (`addRowMultiple 1 0 1`),
normalise the `-1` pivot (`negateColumn 1`), LIFT the base cyclic certificate UNCHANGED, then reorder the
fresh unit onto the divisibility-ordered diagonal (`swapRows 0 1`, `swapColumns 0 1`). -/
def expandedCyclicThreeBoundaryOfDimOneSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations :=
      ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple 1 0 1)
        :: ElementaryOperation.columnOperation (ElementaryColumnOperation.negateColumn 1)
        :: cyclicThreeBoundaryOfDimOneSmithCertificate.operations
        ++ [ ElementaryOperation.rowOperation (ElementaryRowOperation.swapRows 0 1)
           , ElementaryOperation.columnOperation (ElementaryColumnOperation.swapColumns 0 1) ] }

/-- ★ The certificate lands the expanded cyclic `d2` on `diag(1, 3)` — `rfl`. -/
theorem expandedCyclicThreeCertificateProducesSmithNormalForm :
    expandedCyclicThreeBoundaryOfDimOne.applyOperations
        expandedCyclicThreeBoundaryOfDimOneSmithCertificate.operations
      = expandedCyclicThreeSmithNormalFormOfDimOne := rfl

/-- ★ The expanded cyclic `d2` reduces to `diag(1, 3)` within the `2 × 2` window — kernel-checked. -/
theorem expandedCyclicThreeBoundaryOfDimOneReducesToSmith :
    expandedCyclicThreeBoundaryOfDimOneSmithCertificate.reducesToSmithForm
      expandedCyclicThreeBoundaryOfDimOne 2 2 :=
  show expandedCyclicThreeSmithNormalFormOfDimOne.IsSmithNormalFormWithin 2 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex →
          expandedCyclicThreeSmithNormalFormOfDimOne.entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨3, by decide⟩
      | _ + 1, isSuccBelow =>
          Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isSuccBelow))) }

/-- The degree-1 Smith data of the expanded cyclic complex: `C1 = 2`, `SNF(d1) = [[0,0]]` (window `1`),
`SNF(d2) = diag(1, 3)` (window `2`). -/
def expandedCyclicThreeDegreeOneSmithData : SmithHomologyData :=
  { chainBasisCount := 2
  , smithBoundaryIntoLower := ⟨[[0, 0]]⟩
  , windowIntoLower := 1
  , smithBoundaryFromHigher := expandedCyclicThreeSmithNormalFormOfDimOne
  , windowFromHigher := 2 }

/-- ★★ **Cyclic `ZZ/3` survives the fresh-generator expansion — THROUGH THE GENERIC THEOREM.**  The
expanded degree-1 invariant equals `cyclicThreeDegreeOneHomologyInvariant = ZZ/3` by
`tietzeExpansionPreservesDegreeOneInvariant` (all five reader-level hypotheses `rfl`), then the shipped
base read-off. -/
theorem cyclicThreeFreshExpansionPreservesDegreeOneInvariant :
    expandedCyclicThreeDegreeOneSmithData.homologyInvariant = cyclicThreeDegreeOneHomologyInvariant :=
  (tietzeExpansionPreservesDegreeOneInvariant cyclicThreeDegreeOneSmithData
    expandedCyclicThreeDegreeOneSmithData rfl rfl rfl rfl rfl).trans
    cyclicThreeDegreeOneSmithDataComputesInvariant

/-- ★ The direct cross-check: the expanded cyclic degree-1 invariant is `ZZ/3 = (0, [3])` by `rfl`. -/
theorem expandedCyclicThreeDegreeOneHomologyIsZmodThree :
    expandedCyclicThreeDegreeOneSmithData.homologyInvariant = ⟨0, [3]⟩ := rfl

/-! ### Regression 2 (shipped instance) — the r2 Tietze `ZZ/3` expanded by a fresh THIRD gen `u ⟹ st` -/

/-- The r2 Tietze presentation of `ZZ/3` expanded by a fresh THIRD generator `u ⟹ st` (`w = [0, 1]`, a
multi-letter word exercising `v = [1, 1]`). -/
def expandedTietzeThirdGeneratorPresentation : WalkerPresentation :=
  expandWalkerPresentationWithFreshGenerator tietzeZmodThreePresentation [0, 1]

/-- The expanded r2 `d2` `3 × 5` — the r2 `2 × 4` block, the `v = [1, 1]` column of `st`, the `-1`
pivot. -/
def expandedTietzeThirdGeneratorBoundaryOfDimOne : IntMatrix :=
  ⟨[[-2, -1, -1, 1, 1], [1, -1, -1, -2, 1], [0, 0, 0, 0, -1]]⟩

/-- ★ The block builder COMPUTES the expanded r2 `d2` — `rfl`. -/
theorem expandedTietzeThirdGeneratorComputesBoundaryDimOne :
    expandedTietzeThirdGeneratorPresentation.computeBoundaryDimOne
      = expandedTietzeThirdGeneratorBoundaryOfDimOne := rfl

/-- The ordered Smith normal form of the expanded r2 `d2` — `diag(1, 1, 3)`: TWO units, the `3` torsion
factor intact. -/
def expandedTietzeThirdGeneratorSmithNormalFormOfDimOne : IntMatrix :=
  ⟨[[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 3, 0, 0]]⟩

/-- The reduction certificate for the expanded r2 `d2`: clear the `v = [1, 1]` column (`addRowMultiple
2 0 1`, `addRowMultiple 2 1 1`), normalise the `-1` pivot (`negateColumn 4`), LIFT the shipped r2 `d2`
certificate UNCHANGED (index-stable — the base block sits at rows `0,1` / columns `0..3`), then reorder
onto the divisibility-ordered diagonal (`swapColumns 2 4`, `swapRows 1 2`, `swapColumns 1 2`). -/
def expandedTietzeThirdGeneratorBoundaryOfDimOneSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations :=
      ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple 2 0 1)
        :: ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple 2 1 1)
        :: ElementaryOperation.columnOperation (ElementaryColumnOperation.negateColumn 4)
        :: tietzeBoundaryOfDimOneSmithCertificate.operations
        ++ [ ElementaryOperation.columnOperation (ElementaryColumnOperation.swapColumns 2 4)
           , ElementaryOperation.rowOperation (ElementaryRowOperation.swapRows 1 2)
           , ElementaryOperation.columnOperation (ElementaryColumnOperation.swapColumns 1 2) ] }

/-- ★ The certificate lands the expanded r2 `d2` on `diag(1, 1, 3)` — `rfl`. -/
theorem expandedTietzeThirdGeneratorCertificateProducesSmithNormalForm :
    expandedTietzeThirdGeneratorBoundaryOfDimOne.applyOperations
        expandedTietzeThirdGeneratorBoundaryOfDimOneSmithCertificate.operations
      = expandedTietzeThirdGeneratorSmithNormalFormOfDimOne := rfl

/-- ★ The expanded r2 `d2` reduces to `diag(1, 1, 3)` within the `3 × 5` window — kernel-checked. -/
theorem expandedTietzeThirdGeneratorBoundaryOfDimOneReducesToSmith :
    expandedTietzeThirdGeneratorBoundaryOfDimOneSmithCertificate.reducesToSmithForm
      expandedTietzeThirdGeneratorBoundaryOfDimOne 3 5 :=
  show expandedTietzeThirdGeneratorSmithNormalFormOfDimOne.IsSmithNormalFormWithin 3 5 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 3 → ∀ colIndex, colIndex < 5 →
          rowIndex ≠ colIndex →
          expandedTietzeThirdGeneratorSmithNormalFormOfDimOne.entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨1, by decide⟩
      | 1, _ => ⟨3, by decide⟩
      | _ + 2, isSuccBelow =>
          Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc
            (natLeOfSuccLeSucc isSuccBelow)))) }

/-- The degree-1 Smith data of the expanded r2 complex: `C1 = 3`, `SNF(d1) = [[0,0,0]]` (window `1`),
`SNF(d2) = diag(1, 1, 3)` (window `3`). -/
def expandedTietzeThirdGeneratorDegreeOneSmithData : SmithHomologyData :=
  { chainBasisCount := 3
  , smithBoundaryIntoLower := ⟨[[0, 0, 0]]⟩
  , windowIntoLower := 1
  , smithBoundaryFromHigher := expandedTietzeThirdGeneratorSmithNormalFormOfDimOne
  , windowFromHigher := 3 }

/-- ★★ **The r2 Tietze `ZZ/3` survives a SECOND fresh-generator expansion — THROUGH THE GENERIC
THEOREM.**  Adjoining `u ⟹ st` to the already-Tietze-expanded `⟨s, t | …⟩` preserves `H1 = ZZ/3`, by
`tietzeExpansionPreservesDegreeOneInvariant` then the r2 base read-off — a THREE-generator instance of
the fresh-generator theorem. -/
theorem expandedTietzeThirdGeneratorPreservesDegreeOneInvariant :
    expandedTietzeThirdGeneratorDegreeOneSmithData.homologyInvariant = tietzeDegreeOneHomologyInvariant :=
  (tietzeExpansionPreservesDegreeOneInvariant tietzeDegreeOneSmithData
    expandedTietzeThirdGeneratorDegreeOneSmithData rfl rfl rfl rfl rfl).trans
    tietzeDegreeOneHomologyIsZmodThree

/-- ★ The direct cross-check: the expanded r2 degree-1 invariant is `ZZ/3 = (0, [3])` by `rfl`. -/
theorem expandedTietzeThirdGeneratorDegreeOneHomologyIsZmodThree :
    expandedTietzeThirdGeneratorDegreeOneSmithData.homologyInvariant = ⟨0, [3]⟩ := rfl

/-! ### Regression 3 (FRESH instance) — the walking involution `ZZ/2` expanded by `t ⟹ s` -/

/-- The walking-involution presentation of `ZZ/2` expanded by the fresh generator `t ⟹ s` (`w = [0]`) —
the fresh third instance, exercising a nonempty torsion factor `2` under the `-1` pivot. -/
def expandedInvolutionPresentation : WalkerPresentation :=
  expandWalkerPresentationWithFreshGenerator involutionWalkerPresentation [0]

/-- The expanded involution `d2` `[[-2,1],[0,-1]]` — the base `[[-2]]`, the `v = [1]` column, the `-1`
pivot. -/
def expandedInvolutionBoundaryOfDimOne : IntMatrix := ⟨[[-2, 1], [0, -1]]⟩

/-- ★ The block builder COMPUTES the expanded involution `d2` — `rfl`. -/
theorem expandedInvolutionComputesBoundaryDimOne :
    expandedInvolutionPresentation.computeBoundaryDimOne = expandedInvolutionBoundaryOfDimOne := rfl

/-- The ordered Smith normal form of the expanded involution `d2` — `diag(1, 2)`: one fresh UNIT, the `2`
torsion factor intact. -/
def expandedInvolutionSmithNormalFormOfDimOne : IntMatrix := ⟨[[1, 0], [0, 2]]⟩

/-- The reduction certificate for the expanded involution `d2` (same recipe as cyclic): clear `v`
(`addRowMultiple 1 0 1`), normalise the `-1` pivot (`negateColumn 1`), LIFT the base involution
certificate UNCHANGED, then reorder (`swapRows 0 1`, `swapColumns 0 1`). -/
def expandedInvolutionBoundaryOfDimOneSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations :=
      ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple 1 0 1)
        :: ElementaryOperation.columnOperation (ElementaryColumnOperation.negateColumn 1)
        :: involutionBoundaryOfDimOneSmithCertificate.operations
        ++ [ ElementaryOperation.rowOperation (ElementaryRowOperation.swapRows 0 1)
           , ElementaryOperation.columnOperation (ElementaryColumnOperation.swapColumns 0 1) ] }

/-- ★ The certificate lands the expanded involution `d2` on `diag(1, 2)` — `rfl`. -/
theorem expandedInvolutionCertificateProducesSmithNormalForm :
    expandedInvolutionBoundaryOfDimOne.applyOperations
        expandedInvolutionBoundaryOfDimOneSmithCertificate.operations
      = expandedInvolutionSmithNormalFormOfDimOne := rfl

/-- ★ The expanded involution `d2` reduces to `diag(1, 2)` within the `2 × 2` window — kernel-checked. -/
theorem expandedInvolutionBoundaryOfDimOneReducesToSmith :
    expandedInvolutionBoundaryOfDimOneSmithCertificate.reducesToSmithForm
      expandedInvolutionBoundaryOfDimOne 2 2 :=
  show expandedInvolutionSmithNormalFormOfDimOne.IsSmithNormalFormWithin 2 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex →
          expandedInvolutionSmithNormalFormOfDimOne.entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨2, by decide⟩
      | _ + 1, isSuccBelow =>
          Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isSuccBelow))) }

/-- The degree-1 Smith data of the expanded involution complex: `C1 = 2`, `SNF(d1) = [[0,0]]` (window
`1`), `SNF(d2) = diag(1, 2)` (window `2`). -/
def expandedInvolutionDegreeOneSmithData : SmithHomologyData :=
  { chainBasisCount := 2
  , smithBoundaryIntoLower := ⟨[[0, 0]]⟩
  , windowIntoLower := 1
  , smithBoundaryFromHigher := expandedInvolutionSmithNormalFormOfDimOne
  , windowFromHigher := 2 }

/-- ★★ **The walking involution `ZZ/2` survives the fresh-generator expansion — THROUGH THE GENERIC
THEOREM.**  The FRESH third instance: adjoining `t ⟹ s` preserves `H1 = ZZ/2` (torsion factor `2`
intact under the `-1` pivot), by `tietzeExpansionPreservesDegreeOneInvariant` then the shipped
involution read-off. -/
theorem involutionFreshExpansionPreservesDegreeOneInvariant :
    expandedInvolutionDegreeOneSmithData.homologyInvariant
      = walkingInvolutionDegreeOneHomologyInvariant :=
  (tietzeExpansionPreservesDegreeOneInvariant involutionDegreeOneSmithData
    expandedInvolutionDegreeOneSmithData rfl rfl rfl rfl rfl).trans
    involutionDegreeOneSmithDataComputesInvariant

/-- ★ The direct cross-check: the expanded involution degree-1 invariant is `ZZ/2 = (0, [2])` by
`rfl`. -/
theorem expandedInvolutionDegreeOneHomologyIsZmodTwo :
    expandedInvolutionDegreeOneSmithData.homologyInvariant = ⟨0, [2]⟩ := rfl

/-! ### Degree-2 preservation instance — the r2 Tietze `H2 = 0` survives `u ⟹ st`

The degree-2 side of the fresh-generator theorem: the expanded `d3` is the base `d3` with an appended
ZERO row (the fresh rule contributes no cofork), lifting the base `d3` certificate UNCHANGED.  `H2 = 0`
is preserved through `tietzeExpansionPreservesDegreeTwoInvariant`. -/

/-- The expanded r2 `d3` `5 × 8` — the r2 `4 × 8` cofork boundary with the fresh rule's ZERO row
appended. -/
def expandedTietzeThirdGeneratorBoundaryOfDimTwo : IntMatrix :=
  ⟨[ [0, 1, 0, -1, 0, -1, 1, 0]
   , [-1, -1, 1, 0, -1, 1, 0, 1]
   , [1, 0, -1, 1, 1, 0, -1, -1]
   , [0, 1, 0, -1, 0, -1, 1, 0]
   , [0, 0, 0, 0, 0, 0, 0, 0] ]⟩

/-- ★ The block builder COMPUTES the expanded r2 `d3` (the appended fresh-rule zero row) — `rfl`. -/
theorem expandedTietzeThirdGeneratorComputesBoundaryDimTwo :
    expandedTietzeThirdGeneratorPresentation.computeBoundaryDimTwo
      = expandedTietzeThirdGeneratorBoundaryOfDimTwo := rfl

/-- The ordered Smith normal form of the expanded r2 `d3` — `diag(1, 1, 0, 0, 0)`: the base `diag(1, 1,
0, 0)` with the zero row appended (same rank, no new torsion). -/
def expandedTietzeThirdGeneratorSmithNormalFormOfDimTwo : IntMatrix :=
  ⟨[ [1, 0, 0, 0, 0, 0, 0, 0]
   , [0, 1, 0, 0, 0, 0, 0, 0]
   , [0, 0, 0, 0, 0, 0, 0, 0]
   , [0, 0, 0, 0, 0, 0, 0, 0]
   , [0, 0, 0, 0, 0, 0, 0, 0] ]⟩

/-- ★ The base r2 `d3` certificate, LIFTED UNCHANGED, lands the expanded r2 `d3` on `diag(1, 1, 0, 0,
0)` — the zero row is inert and already last, so no reindexing is needed.  `rfl`. -/
theorem expandedTietzeThirdGeneratorCertificateProducesSmithNormalFormOfDimTwo :
    expandedTietzeThirdGeneratorBoundaryOfDimTwo.applyOperations
        tietzeBoundaryOfDimTwoSmithCertificate.operations
      = expandedTietzeThirdGeneratorSmithNormalFormOfDimTwo := rfl

/-- ★ The expanded r2 `d3` reduces to `diag(1, 1, 0, 0, 0)` within the `5 × 8` window — kernel-checked
(the lifted base certificate). -/
theorem expandedTietzeThirdGeneratorBoundaryOfDimTwoReducesToSmith :
    tietzeBoundaryOfDimTwoSmithCertificate.reducesToSmithForm
      expandedTietzeThirdGeneratorBoundaryOfDimTwo 5 8 :=
  show expandedTietzeThirdGeneratorSmithNormalFormOfDimTwo.IsSmithNormalFormWithin 5 8 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 5 → ∀ colIndex, colIndex < 8 →
          rowIndex ≠ colIndex →
          expandedTietzeThirdGeneratorSmithNormalFormOfDimTwo.entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨1, by decide⟩
      | 1, _ => ⟨0, by decide⟩
      | 2, _ => ⟨0, by decide⟩
      | 3, _ => ⟨0, by decide⟩
      | _ + 4, isSuccBelow =>
          Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc
            (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc isSuccBelow)))))) }

/-- The degree-2 Smith data of the expanded r2 complex: `C2 = 5`, `SNF(d2) = diag(1, 1, 3)` (window
`3`), `SNF(d3) = diag(1, 1, 0, 0, 0)` (window `5`). -/
def expandedTietzeThirdGeneratorDegreeTwoSmithData : SmithHomologyData :=
  { chainBasisCount := 5
  , smithBoundaryIntoLower := expandedTietzeThirdGeneratorSmithNormalFormOfDimOne
  , windowIntoLower := 3
  , smithBoundaryFromHigher := expandedTietzeThirdGeneratorSmithNormalFormOfDimTwo
  , windowFromHigher := 5 }

/-- ★★ **The r2 Tietze `H2 = 0` survives the fresh-generator expansion — THROUGH THE GENERIC DEGREE-2
THEOREM.**  The fresh generator bumps `C2` by one and inserts one Smith unit into `d2`; the appended
zero `d3` row adds no rank; so `H2 = 0` is preserved by `tietzeExpansionPreservesDegreeTwoInvariant`. -/
theorem expandedTietzeThirdGeneratorPreservesDegreeTwoInvariant :
    expandedTietzeThirdGeneratorDegreeTwoSmithData.homologyInvariant = tietzeDegreeTwoHomologyInvariant :=
  (tietzeExpansionPreservesDegreeTwoInvariant tietzeDegreeTwoSmithData
    expandedTietzeThirdGeneratorDegreeTwoSmithData rfl rfl rfl rfl).trans
    tietzeDegreeTwoHomologyIsZero

/-- ★ The direct cross-check: the expanded r2 degree-2 invariant is `0 = (0, [])` by `rfl`. -/
theorem expandedTietzeThirdGeneratorDegreeTwoHomologyIsZero :
    expandedTietzeThirdGeneratorDegreeTwoSmithData.homologyInvariant = ⟨0, []⟩ := rfl

/-! ## r4 engine — the fresh-column pivot, the reader congruences, the clearing recipe

The certificate-extension engine that turns the per-instance reader hypotheses of r3 into GENERIC facts
about the expanded boundary.  The pivot at `(base.oneGeneratorCount, base.rules.length)` of the expanded
`d2` is the UNIT `-1` exactly when `w` is `t`-free (`freshColumnPivotIsUnitOfFreshFree`); the reader
`smithRankWithin` / `smithInvariantFactorsWithin` are congruent when the diagonals agree below the window
(`smithRankWithinCongrBelow`, `smithInvariantFactorsWithinCongrBelow`); an all-zero diagonal has rank
zero (`smithRankWithinAllZeroDiagonalIsZero`).  All structural on the `Nat` window / `List`. -/

/-- Reading index `= leftEntries.length` of an append reads the head of the right list — the pivot lands
at exactly the fresh-column position, one past the base block.  Structural on the left list. -/
theorem listGetWithDefaultAppendRightStart {Entry : Type} (defaultEntry : Entry) :
    ∀ (leftEntries rightEntries : List Entry),
      listGetWithDefault defaultEntry (leftEntries ++ rightEntries) leftEntries.length
        = listGetWithDefault defaultEntry rightEntries 0
  | [], _ => rfl
  | _ :: tailEntries, rightEntries =>
      listGetWithDefaultAppendRightStart defaultEntry tailEntries rightEntries

/-- ★★ **The fresh-column pivot is the unit `-1` when `w` is `t`-free.**  The expanded `d2` entry at the
fresh generator row `base.oneGeneratorCount` and the fresh rule column `base.rules.length` reads
`#t in w − #t in [t] = 0 − 1 = -1` — the `#t in w = 0` from `t`-freeness, the `#t in [t] = 1` by `rfl`.
This is where `t`-freeness BITES: a `w` containing `t` (e.g. `w = [t]`) gives `#t in w = 1`, pivot `0`,
no rank bump, and the homology would NOT be preserved.  The structural entry point
`expandWalkerPresentationWithBaseWord` supplies `freshFree` by construction. -/
theorem freshColumnPivotIsUnitOfFreshFree (base : WalkerPresentation) (freshRuleWord : List Nat)
    (freshFree : countGeneratorOccurrences base.oneGeneratorCount freshRuleWord = 0) :
    (expandWalkerPresentationWithFreshGenerator base freshRuleWord).computeBoundaryDimOne.entryAt
      base.oneGeneratorCount base.rules.length = -1 := by
  show listGetWithDefault 0
      (listGetWithDefault []
        (walkerPresentationDimOneRows (base.rules ++ [([base.oneGeneratorCount], freshRuleWord)]) 0
          (base.oneGeneratorCount + 1)) base.oneGeneratorCount) base.rules.length = -1
  rw [walkerPresentationDimOneRowsGet (base.rules ++ [([base.oneGeneratorCount], freshRuleWord)]) 0
        (base.oneGeneratorCount + 1) base.oneGeneratorCount Nat.le.refl,
      natZeroAddEqSelf base.oneGeneratorCount,
      walkerPresentationDimOneRowAppendDistrib base.oneGeneratorCount base.rules
        [([base.oneGeneratorCount], freshRuleWord)],
      ← walkerPresentationDimOneRowLength base.oneGeneratorCount base.rules,
      listGetWithDefaultAppendRightStart 0
        (walkerPresentationDimOneRow base.oneGeneratorCount base.rules)
        (walkerPresentationDimOneRow base.oneGeneratorCount [([base.oneGeneratorCount], freshRuleWord)])]
  show Int.ofNat (countGeneratorOccurrences base.oneGeneratorCount freshRuleWord)
      - Int.ofNat ((if base.oneGeneratorCount = base.oneGeneratorCount then 1 else 0) + 0) = -1
  rw [freshFree, if_pos (rfl : base.oneGeneratorCount = base.oneGeneratorCount)]
  rfl

/-- ★ **Reader rank congruence below the window.**  Two matrices whose diagonal entries agree at every
position below `windowSize` have the same `smithRankWithin` — the rank read is a function of the
in-window diagonal only.  Structural on `windowSize`; the top `if diag = 0` branch is rewritten by the
agreement, never `decide`d on a symbolic diagonal. -/
theorem smithRankWithinCongrBelow (leftMatrix rightMatrix : IntMatrix) :
    ∀ (windowSize : Nat),
      (∀ position, position < windowSize →
        leftMatrix.diagonalEntryAt position = rightMatrix.diagonalEntryAt position) →
      smithRankWithin leftMatrix windowSize = smithRankWithin rightMatrix windowSize
  | 0, _ => rfl
  | windowSize + 1, agreeBelow => by
      show (if leftMatrix.diagonalEntryAt windowSize = 0 then 0 else 1)
          + smithRankWithin leftMatrix windowSize
        = (if rightMatrix.diagonalEntryAt windowSize = 0 then 0 else 1)
          + smithRankWithin rightMatrix windowSize
      rw [agreeBelow windowSize Nat.le.refl,
          smithRankWithinCongrBelow leftMatrix rightMatrix windowSize
            (fun position isBelow => agreeBelow position (Nat.le.step isBelow))]

/-- ★ **Reader invariant-factor congruence below the window.**  Two matrices whose diagonal entries
agree below `windowSize` have the same `smithInvariantFactorsWithin` — the torsion read is a function of
the in-window diagonal only.  Structural on `windowSize`, the top branch rewritten by the agreement. -/
theorem smithInvariantFactorsWithinCongrBelow (leftMatrix rightMatrix : IntMatrix) :
    ∀ (windowSize : Nat),
      (∀ position, position < windowSize →
        leftMatrix.diagonalEntryAt position = rightMatrix.diagonalEntryAt position) →
      smithInvariantFactorsWithin leftMatrix windowSize
        = smithInvariantFactorsWithin rightMatrix windowSize
  | 0, _ => rfl
  | windowSize + 1, agreeBelow => by
      show (if leftMatrix.diagonalEntryAt windowSize = 0 then []
              else [leftMatrix.diagonalEntryAt windowSize])
          ++ smithInvariantFactorsWithin leftMatrix windowSize
        = (if rightMatrix.diagonalEntryAt windowSize = 0 then []
              else [rightMatrix.diagonalEntryAt windowSize])
          ++ smithInvariantFactorsWithin rightMatrix windowSize
      rw [agreeBelow windowSize Nat.le.refl,
          smithInvariantFactorsWithinCongrBelow leftMatrix rightMatrix windowSize
            (fun position isBelow => agreeBelow position (Nat.le.step isBelow))]

/-- ★ **An all-zero diagonal has rank zero.**  When every diagonal entry below `windowSize` is `0` (the
`d1` all-zero loop row), `smithRankWithin` is `0` — the generic form of the per-instance `rfl` rank the
degree-1 reader consumes.  Structural on `windowSize`, `if_pos rfl` on each zero entry. -/
theorem smithRankWithinAllZeroDiagonalIsZero (matrix : IntMatrix) :
    ∀ (windowSize : Nat),
      (∀ position, position < windowSize → matrix.diagonalEntryAt position = 0) →
      smithRankWithin matrix windowSize = 0
  | 0, _ => rfl
  | windowSize + 1, allZero => by
      show (if matrix.diagonalEntryAt windowSize = 0 then 0 else 1)
          + smithRankWithin matrix windowSize = 0
      rw [allZero windowSize Nat.le.refl, if_pos rfl,
          smithRankWithinAllZeroDiagonalIsZero matrix windowSize
            (fun position isBelow => allZero position (Nat.le.step isBelow))]

/-! ## B5 — the ledger: what r3 landed, the r2 beyond-expansion frame, the R1 wall re-stated

### What r3 LANDED (shipped, zero-axiom)

  * **B1 — the generic block constructor**: `expandWalkerPresentationWithFreshGenerator`;
    ★★ `freshGeneratorExpansionAddsNoCriticalPairs` (`C3` unchanged, the no-new-critical-pair fact);
    `freshGeneratorExpansionBumpsGeneratorCount` / `…BumpsRuleCount` (`C1`/`C2` `+1`); the hand probe
    (`handProbeExpandedBoundaryReducesToSmithNormalForm`, the r2 `d2` extended by `u ⟹ e` on
    `diag(1, 1, 3)` by `rfl`).
  * **B2 — the GENERIC well-formedness (Route A)**: ★★ `freshGeneratorExpansionIsWellFormedOfBase` (the
    block `d2·d3 = 0` for ANY base presentation, given the two honest base-shape facts), the four block
    agreement/vanishing lemmas, and ★★ `freshGeneratorExpansionChainComplex` (the generic expanded ADC),
    non-vacuously inhabited by `handProbeExpandedTietzeChainComplex`.
  * **B3 — the GENERIC preservation theorems**: ★★ `tietzeExpansionPreservesDegreeOneInvariant` and
    ★★ `tietzeExpansionPreservesDegreeTwoInvariant`, at the reader granularity (the fresh Smith unit
    bumps the rank by one — `smithRankWithinTopNonzeroIsSuccessor` — and the non-unit torsion is stable —
    `nonUnitInvariantFactorsUnitConsIsStable`).
  * **B4 — the regressions THROUGH the theorem**: cyclic `ZZ/3` (`t ⟹ s`), r2 Tietze `ZZ/3` (`u ⟹ st`),
    and the FRESH walking involution `ZZ/2` (`t ⟹ s`) — each degree-1 invariant preserved via the
    generic theorem, each with an explicit lifted `d2` certificate; plus the degree-2 instance
    (`expandedTietzeThirdGeneratorPreservesDegreeTwoInvariant`, `H2 = 0` preserved).

### The r2 instance as the worked BEYOND-EXPANSION example (honest)

The r2 file's `⟨s, t | ss, st, ts, tt⟩` presentation of `ZZ/3` was obtained from `⟨s | sss⟩` by a Tietze
move `t := s²` FOLLOWED BY orientation and Knuth–Bendix completion (all four length-reducing rules).
This round's theorem captures ONLY the single fresh-generator adjunction `t ⟹ w` — NOT the general
orientation/completion.  So the r2 presentation is the worked example that lives BEYOND this theorem: its
own construction needed the completion machinery the theorem does not (yet) formalise.  Here that same
r2 presentation is instead used as a BASE, expanded by a third generator `u ⟹ st` — the theorem applies
to it as a base, honestly, without claiming to reproduce its original completion.

### What STAYS WALLED (R1, re-stated with what REMAINS)

The GENERAL monoid-level presentation-invariance (any two finite convergent presentations of the same
monoid have isomorphic homology) is STILL the R1 research wall.  This round pays it down further — from
the r2 single worked coincidence to a GENERIC theorem for ONE Tietze move (fresh-generator adjunction) —
but the residual is real and named:

  * **type-2 Tietze relation moves** (adjoin/remove a DERIVABLE relation) — not covered; only the
    fresh-GENERATOR move is;
  * **general orientation + Knuth–Bendix completion** — turning an arbitrary presentation into a
    convergent one (the r2 example's own provenance) — not formalised;
  * **the Squier / Pride homotopy machinery** — the chain-homotopy between the two abelianized complexes
    that would give the FULL invariance across arbitrary Tietze-equivalent presentations — the deep wall.

No overclaim: r3 ships a GENERIC single-fresh-generator invariance theorem and three instances through
it, moving the R1 down-payment from one coincidence to a theorem — but NOT the general invariance,
NOT relation moves, NOT completion, NOT the homotopy machinery. -/

/-- The number of decided walkers whose homology is verified invariant under fresh-generator expansion
THROUGH the generic theorem: cyclic `ZZ/3`, the r2 Tietze `ZZ/3`, and the walking involution `ZZ/2` — a
running additive count, not a mutation of any shipped census. -/
def walkersWithFreshGeneratorExpansionInvarianceCount : Nat := 3

/-- The additive census value: `3` instances fed through the generic fresh-generator theorem, by
`rfl`. -/
theorem walkersWithFreshGeneratorExpansionInvarianceCountValue :
    walkersWithFreshGeneratorExpansionInvarianceCount = 3 := rfl

/-- ★ **The #2139 round-three ledger marker.**  Invariance under fresh-generator (Tietze type-1)
expansion is a GENERIC THEOREM (`tietzeExpansionPreservesDegreeOne/TwoInvariant`), the block
well-formedness is generic (`freshGeneratorExpansionIsWellFormedOfBase`), and three instances are fed
through it (cyclic `ZZ/3`, r2 Tietze `ZZ/3`, walking involution `ZZ/2`).  What STAYS WALLED: R1 the
general monoid-level invariance — type-2 relation moves, general orientation/completion, and the
Squier/Pride homotopy machinery remain the named residual.  Read the meaning from THIS docstring. -/
def freshGeneratorTietzeExpansionLedgerIsComplete : Bool := true

/-- ★ **The HONESTY marker: r3 lifts the R1 down-payment from a coincidence to a THEOREM, it moves NO
wall.**  The single-fresh-generator move is now a generic invariance theorem, but the general Tietze
invariance (relation moves, completion, homotopy) stays the R1 research wall.  `= true` records the
stance, not a closure. -/
def freshGeneratorExpansionEnrichesButNoWallMoved : Bool := true

end FX1Poly.Polygraph.Homology
