import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScan
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute

/-! # MatchingBoundaryIndexCensus — the carrier-free boundary-index census + partner INVOLUTION
(Track B, positivity-free involution infrastructure for b#1)

The censused partner matching is a fixed-point-free involution on the ARC carrier
(`partnerIndexOf_isInvolution`, over `ArcWireState`, discharged by the token-form `ArcBoundaryCensus`).
Transporting it to the plain `matchingOf` carrier via the shipped bridge (`matchingOf_partner_isInvolution`)
needs `0 < bottomCount` and is DEAD at the width-0 seed.

This file re-derives the involution DIRECTLY over the abstract union-find data `(links, boundaryNodes,
total)`, carrier-free: `partnerIndexOf`, `findPartnerScan`, `isSameComponent` all operate only on `links`
and `boundaryNodes`, so the whole forward-soundness + census-uniqueness chain restates verbatim, with the
census in a plain INDEX form (no `ArcEndToken`, no seed-boundary split).  Instantiated at the width-0
matching state's `(state.links, List.range 0 ++ openWires, 0 + openWires.length)`, this yields the width-0
partner involution POSITIVITY-FREE — provided the boundary-index census (each component has at most two
boundary indices) is supplied for that state.

  * ★ `BoundaryIndexCensus` — the carrier-free three-index pigeonhole: no three distinct in-range boundary
    indices pairwise share a `links`-component.

  * ★ `partnerIndexOf_below_generic` / `partnerIndexOf_sameComponent_or_fixed_generic` — the census-free
    range and forward-soundness of the scan (verbatim ports of `partnerIndexOf_below` /
    `partnerIndexOf_sameComponent_or_fixed`).

  * ★ `partnerIndexOf_uniqueSameComponent_generic` — the census pins any exhibited same-component candidate
    to the scan result (verbatim port, census applied directly in index form).

  * ★ `partnerIndexOf_isInvolution_ofBoundaryIndexCensus` — the fixed-point-free involution on the abstract
    carrier, given the census.  The exact consumer interface the width-0 LOCATE snake exclusion needs, once
    the width-0 pure-cup census is discharged.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (per-file copies) -/

private theorem rangeLoopMem_ofAccumulated : (count : Nat) → (accumulated : List Nat) →
    (target : Nat) → target ∈ accumulated → target ∈ List.range.loop count accumulated
  | 0, _, _, targetMem => targetMem
  | count + 1, accumulated, target, targetMem =>
      rangeLoopMem_ofAccumulated count (count :: accumulated) target (List.Mem.tail _ targetMem)

private theorem rangeLoopMem_ofLt : (count : Nat) → (accumulated : List Nat) →
    (target : Nat) → target < count → target ∈ List.range.loop count accumulated
  | count + 1, accumulated, target, targetBelow => by
      cases Nat.lt_or_ge target count with
      | inl below => exact rangeLoopMem_ofLt count (count :: accumulated) target below
      | inr atLeast =>
          have targetEq : target = count :=
            Nat.le_antisymm (Nat.le_of_lt_succ targetBelow) atLeast
          exact rangeLoopMem_ofAccumulated count (count :: accumulated) target
            (targetEq ▸ List.Mem.head _)

private theorem rangeMem_ofLt (count target : Nat) (targetBelow : target < count) :
    target ∈ List.range count :=
  rangeLoopMem_ofLt count [] target targetBelow

private theorem findPartnerScan_memOrExclude (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (rootHere excludeIndex : Nat) : (scanned : List Nat) →
    findPartnerScan links boundaryNodes rootHere excludeIndex scanned = excludeIndex
      ∨ findPartnerScan links boundaryNodes rootHere excludeIndex scanned ∈ scanned
  | [] => Or.inl rfl
  | candidate :: rest => by
      rw [findPartnerScan_cons]
      cases headTest : (candidate != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere) with
      | true => exact Or.inr (List.Mem.head rest)
      | false =>
          cases findPartnerScan_memOrExclude links boundaryNodes rootHere excludeIndex rest with
          | inl isExclude => exact Or.inl isExclude
          | inr isMember => exact Or.inr (List.Mem.tail candidate isMember)

/-! ## The carrier-free boundary-index census -/

/-- ★ **The carrier-free two-endpoint boundary census (index form).**  No three DISTINCT in-range
boundary indices pairwise share a `links`-component.  Every union-find component of a planar diagram is a
path with two ends, hence at most two boundary indices; this is the zero-dep pigeonhole rendering, stated
directly over indices into `boundaryNodes` (the plain analogue of `ArcBoundaryCensus`, with no token
split and no seed boundary). -/
def BoundaryIndexCensus (links : List (Nat × Nat)) (boundaryNodes : List Nat) (total : Nat) : Prop :=
  ∀ indexOne indexTwo indexThree : Nat,
    indexOne < total → indexTwo < total → indexThree < total →
    indexOne ≠ indexTwo → indexOne ≠ indexThree → indexTwo ≠ indexThree →
    isSameComponent links (natListGetAt boundaryNodes indexOne)
        (natListGetAt boundaryNodes indexTwo) = true →
    isSameComponent links (natListGetAt boundaryNodes indexOne)
        (natListGetAt boundaryNodes indexThree) = true →
    False

/-! ## The census-free range + forward soundness of the scan -/

/-- ★ **The partner index stays in range (carrier-free).**  The scan returns `index` (in range) or a
member of the scanned `List.range total` (in range).  Verbatim port of `partnerIndexOf_below`. -/
theorem partnerIndexOf_below_generic (links : List (Nat × Nat)) (boundaryNodes : List Nat)
    (total index : Nat) (indexBelow : index < total) :
    partnerIndexOf links boundaryNodes total index < total := by
  cases findPartnerScan_memOrExclude links boundaryNodes
      (unionFindRootOf links (natListGetAt boundaryNodes index)) index (List.range total) with
  | inl isExclude =>
      have partnerEq : partnerIndexOf links boundaryNodes total index = index := isExclude
      rw [partnerEq]; exact indexBelow
  | inr isMember => exact mem_range_imp_lt isMember

/-- ★ **Each partner arc is a same-component pair (or a fixed point), carrier-free.**  The scan returns
either `index` itself or a boundary index whose read shares `index`'s component.  Verbatim port of
`partnerIndexOf_sameComponent_or_fixed`. -/
theorem partnerIndexOf_sameComponent_or_fixed_generic (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (total index : Nat) :
    partnerIndexOf links boundaryNodes total index = index
      ∨ isSameComponent links
          (natListGetAt boundaryNodes index)
          (natListGetAt boundaryNodes (partnerIndexOf links boundaryNodes total index)) = true := by
  cases Nat.decEq (partnerIndexOf links boundaryNodes total index) index with
  | isTrue isFixed => exact Or.inl isFixed
  | isFalse notFixed =>
      refine Or.inr ?_
      have rootEq := findPartnerScan_root_ofFound links boundaryNodes
        (unionFindRootOf links (natListGetAt boundaryNodes index))
        index (List.range total) notFixed
      exact decide_eq_true rootEq.symm

/-! ## The census-pinned uniqueness -/

/-- ★ **The census pins the partner: any same-component candidate IS the scan result (carrier-free).**  An
in-range boundary index other than the probe whose read shares the probe's component equals
`partnerIndexOf` at the probe — a different scan result would also pass the root test in range, and three
pairwise-distinct same-component indices violate the census.  Verbatim port of
`partnerIndexOf_uniqueSameComponent`, with the census applied directly in index form. -/
theorem partnerIndexOf_uniqueSameComponent_generic (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (total : Nat)
    (census : BoundaryIndexCensus links boundaryNodes total)
    (excludeIndex partnerCandidate : Nat)
    (excludeInRange : excludeIndex < total) (candidateInRange : partnerCandidate < total)
    (candidateNeExclude : partnerCandidate ≠ excludeIndex)
    (sameReads : isSameComponent links
      (natListGetAt boundaryNodes excludeIndex)
      (natListGetAt boundaryNodes partnerCandidate) = true) :
    partnerIndexOf links boundaryNodes total excludeIndex = partnerCandidate := by
  have rootsEqual : unionFindRootOf links (natListGetAt boundaryNodes excludeIndex)
      = unionFindRootOf links (natListGetAt boundaryNodes partnerCandidate) :=
    of_decide_eq_true sameReads
  have candidateMem : partnerCandidate ∈ List.range total :=
    rangeMem_ofLt total partnerCandidate candidateInRange
  have resultNeExclude : findPartnerScan links boundaryNodes
      (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex))
      excludeIndex (List.range total) ≠ excludeIndex :=
    findPartnerScan_neExclude_ofTarget links boundaryNodes
      (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex))
      excludeIndex (List.range total)
      partnerCandidate candidateMem candidateNeExclude rootsEqual.symm
  have resultRoot := findPartnerScan_root_ofFound links boundaryNodes
    (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex))
    excludeIndex (List.range total) resultNeExclude
  have resultMem : findPartnerScan links boundaryNodes
      (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex))
      excludeIndex (List.range total) ∈ List.range total := by
    cases findPartnerScan_memOrExclude links boundaryNodes
        (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex))
        excludeIndex (List.range total) with
    | inl isExclude => exact absurd isExclude resultNeExclude
    | inr isMember => exact isMember
  have resultInRange : findPartnerScan links boundaryNodes
      (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex))
      excludeIndex (List.range total) < total := mem_range_imp_lt resultMem
  show findPartnerScan links boundaryNodes
      (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex))
      excludeIndex (List.range total) = partnerCandidate
  cases Nat.decEq (findPartnerScan links boundaryNodes
      (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex))
      excludeIndex (List.range total)) partnerCandidate with
  | isTrue resultEqCandidate => exact resultEqCandidate
  | isFalse resultNeCandidate =>
      have sameExcludeResult : isSameComponent links
          (natListGetAt boundaryNodes excludeIndex)
          (natListGetAt boundaryNodes
            (findPartnerScan links boundaryNodes
              (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex))
              excludeIndex (List.range total))) = true :=
        decide_eq_true resultRoot.symm
      exact False.elim (census
        excludeIndex partnerCandidate
        (findPartnerScan links boundaryNodes
          (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex))
          excludeIndex (List.range total))
        excludeInRange candidateInRange resultInRange
        (fun excludeEqCandidate => candidateNeExclude excludeEqCandidate.symm)
        (fun excludeEqResult => resultNeExclude excludeEqResult.symm)
        (fun candidateEqResult => resultNeCandidate candidateEqResult.symm)
        sameReads sameExcludeResult)

/-! ## The involution -/

/-- ★ **The censused partner matching is a fixed-point-free involution (carrier-free).**  At a state with
the boundary-index census, if `index`'s partner `j` is genuine (`j ≠ index`), applying `partnerIndexOf`
again returns `index`: `j` shares `index`'s component (forward soundness), so `index` is a distinct in-range
same-component candidate for `j`, and the census pins `partnerIndexOf … j = index`.  The exact consumer
interface the width-0 LOCATE snake exclusion needs — a plain-carrier re-derivation of
`partnerIndexOf_isInvolution`, positivity-free, awaiting the width-0 pure-cup census. -/
theorem partnerIndexOf_isInvolution_ofBoundaryIndexCensus (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (total : Nat)
    (census : BoundaryIndexCensus links boundaryNodes total)
    (index : Nat) (indexInRange : index < total)
    (notFixed : partnerIndexOf links boundaryNodes total index ≠ index) :
    partnerIndexOf links boundaryNodes total
        (partnerIndexOf links boundaryNodes total index)
      = index := by
  have partnerBelow : partnerIndexOf links boundaryNodes total index < total :=
    partnerIndexOf_below_generic links boundaryNodes total index indexInRange
  have sameForward : isSameComponent links
      (natListGetAt boundaryNodes index)
      (natListGetAt boundaryNodes (partnerIndexOf links boundaryNodes total index)) = true := by
    cases partnerIndexOf_sameComponent_or_fixed_generic links boundaryNodes total index with
    | inl isFixed => exact absurd isFixed notFixed
    | inr sound => exact sound
  exact partnerIndexOf_uniqueSameComponent_generic links boundaryNodes total census
    (partnerIndexOf links boundaryNodes total index) index partnerBelow indexInRange
    (fun indexEqPartner => notFixed indexEqPartner.symm)
    (isSameComponent_flip links _ _ sameForward)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the boundary matching partner INVOLUTION is re-derived carrier-free, positivity-free
(Track B, b#1 infrastructure).**  `partnerIndexOf_isInvolution_ofBoundaryIndexCensus` gives the
fixed-point-free involution over abstract `(links, boundaryNodes, total)` from the carrier-free index-form
`BoundaryIndexCensus`, through the census-free range/forward-soundness (`partnerIndexOf_below_generic`,
`partnerIndexOf_sameComponent_or_fixed_generic`) and the census-pinned uniqueness
(`partnerIndexOf_uniqueSameComponent_generic`).  Verbatim ports of the shipped `ArcWireState`-bound
lemmas, with the census in plain index form so the width-0 seed's `List.range 0 ++ openWires` boundary
plugs straight in — NO `arcDiagram_eq_matching` bridge, NO `0 < bottomCount`.

  What this marker does NOT itself close (the residual for the full width-0 involution — no gate flag is
  flipped): the DISCHARGE of `BoundaryIndexCensus` for the width-0 pure-cup matching state (each fresh cup
  pair is its own size-2 component, disjoint from the rest — a positivity-free `stepCup_links_freshCons`
  root-class fold with pure-cup open-wire distinctness).  Given that discharge, the width-0 partner
  involution is immediate.  `convOfMapEq` and the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasMatchingBoundaryIndexCensus : Bool := true

end FX1Poly.Polygraph
