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

end FX1Poly.Polygraph.Homology
