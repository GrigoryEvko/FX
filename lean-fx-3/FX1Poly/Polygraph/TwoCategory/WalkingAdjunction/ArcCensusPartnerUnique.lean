import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusIndexForm
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScan

/-! # ArcCensusPartnerUnique — the census pins the partner scan's answer (peel campaign H, cup rung 2d-v)

At a censused state the canonical partner scan has NO choice: any in-range boundary index other
than the probe whose read shares the probe's component IS the scan result.  Were the scan to
return a different index, that result also passes the root test (`findPartnerScan_root_ofFound`)
and lies in range, giving three pairwise-distinct same-component boundary indices — impossible
by the index-form census.  This is the dispatch weapon of the fused-component rewiring: to
evaluate a partner it suffices to EXHIBIT one same-component candidate.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range membership plumbing (per-file copy, following the codebase pattern) -/

private theorem rangeLoopMem_ofAccumulated : (count : Nat) → (accumulated : List Nat) →
    (target : Nat) → target ∈ accumulated → target ∈ List.range.loop count accumulated
  | 0, _, _, targetMem => targetMem
  | count + 1, accumulated, target, targetMem =>
      rangeLoopMem_ofAccumulated count (count :: accumulated) target
        (List.Mem.tail count targetMem)

private theorem rangeLoopMem_ofLt : (count : Nat) → (accumulated : List Nat) →
    (target : Nat) → target < count → target ∈ List.range.loop count accumulated
  | 0, _, target, targetBelow => absurd targetBelow (Nat.not_lt_zero target)
  | count + 1, accumulated, target, targetBelow => by
      cases Nat.lt_or_ge target count with
      | inl below => exact rangeLoopMem_ofLt count (count :: accumulated) target below
      | inr atLeast =>
          have targetEq : target = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ targetBelow) atLeast
          rw [targetEq]
          exact rangeLoopMem_ofAccumulated count (count :: accumulated) count
            (List.Mem.head accumulated)

private theorem rangeMem_ofLt (count target : Nat) (targetBelow : target < count) :
    target ∈ List.range count :=
  rangeLoopMem_ofLt count [] target targetBelow

/-! ## The scan result is a scanned candidate (or the fallback) -/

/-- The partner scan returns either the exclude fallback or a member of the scanned list. -/
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
          cases findPartnerScan_memOrExclude links boundaryNodes rootHere excludeIndex
              rest with
          | inl isExclude => exact Or.inl isExclude
          | inr isMember => exact Or.inr (List.Mem.tail candidate isMember)

/-! ## The uniqueness -/

/-- ★ **The census pins the partner: any same-component candidate IS the scan result.**  At a
censused state, an in-range boundary index other than the probe whose read shares the probe's
component equals `partnerIndexOf` at the probe — a different scan result would also pass the
root test in range, and three pairwise-distinct same-component indices violate the census. -/
theorem partnerIndexOf_uniqueSameComponent (seedBoundary : Nat) (state : ArcWireState)
    (census : ArcBoundaryCensus seedBoundary state)
    (excludeIndex partnerCandidate : Nat)
    (excludeInRange : excludeIndex < seedBoundary + state.openWires.length)
    (candidateInRange : partnerCandidate < seedBoundary + state.openWires.length)
    (candidateNeExclude : partnerCandidate ≠ excludeIndex)
    (sameReads : isSameComponent state.links
      (natListGetAt (List.range seedBoundary ++ state.openWires) excludeIndex)
      (natListGetAt (List.range seedBoundary ++ state.openWires) partnerCandidate) = true) :
    partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
      (seedBoundary + state.openWires.length) excludeIndex = partnerCandidate := by
  have rootsEqual : unionFindRootOf state.links
        (natListGetAt (List.range seedBoundary ++ state.openWires) excludeIndex)
      = unionFindRootOf state.links
        (natListGetAt (List.range seedBoundary ++ state.openWires) partnerCandidate) :=
    of_decide_eq_true sameReads
  have candidateMem : partnerCandidate
      ∈ List.range (seedBoundary + state.openWires.length) :=
    rangeMem_ofLt (seedBoundary + state.openWires.length) partnerCandidate candidateInRange
  have resultNeExclude : findPartnerScan state.links
      (List.range seedBoundary ++ state.openWires)
      (unionFindRootOf state.links
        (natListGetAt (List.range seedBoundary ++ state.openWires) excludeIndex))
      excludeIndex (List.range (seedBoundary + state.openWires.length)) ≠ excludeIndex :=
    findPartnerScan_neExclude_ofTarget state.links
      (List.range seedBoundary ++ state.openWires)
      (unionFindRootOf state.links
        (natListGetAt (List.range seedBoundary ++ state.openWires) excludeIndex))
      excludeIndex (List.range (seedBoundary + state.openWires.length))
      partnerCandidate candidateMem candidateNeExclude rootsEqual.symm
  have resultRoot := findPartnerScan_root_ofFound state.links
    (List.range seedBoundary ++ state.openWires)
    (unionFindRootOf state.links
      (natListGetAt (List.range seedBoundary ++ state.openWires) excludeIndex))
    excludeIndex (List.range (seedBoundary + state.openWires.length)) resultNeExclude
  have resultMem : findPartnerScan state.links
      (List.range seedBoundary ++ state.openWires)
      (unionFindRootOf state.links
        (natListGetAt (List.range seedBoundary ++ state.openWires) excludeIndex))
      excludeIndex (List.range (seedBoundary + state.openWires.length))
      ∈ List.range (seedBoundary + state.openWires.length) := by
    cases findPartnerScan_memOrExclude state.links
        (List.range seedBoundary ++ state.openWires)
        (unionFindRootOf state.links
          (natListGetAt (List.range seedBoundary ++ state.openWires) excludeIndex))
        excludeIndex (List.range (seedBoundary + state.openWires.length)) with
    | inl isExclude => exact absurd isExclude resultNeExclude
    | inr isMember => exact isMember
  have resultInRange : findPartnerScan state.links
      (List.range seedBoundary ++ state.openWires)
      (unionFindRootOf state.links
        (natListGetAt (List.range seedBoundary ++ state.openWires) excludeIndex))
      excludeIndex (List.range (seedBoundary + state.openWires.length))
      < seedBoundary + state.openWires.length := mem_range_imp_lt resultMem
  show findPartnerScan state.links (List.range seedBoundary ++ state.openWires)
      (unionFindRootOf state.links
        (natListGetAt (List.range seedBoundary ++ state.openWires) excludeIndex))
      excludeIndex (List.range (seedBoundary + state.openWires.length)) = partnerCandidate
  cases Nat.decEq (findPartnerScan state.links (List.range seedBoundary ++ state.openWires)
      (unionFindRootOf state.links
        (natListGetAt (List.range seedBoundary ++ state.openWires) excludeIndex))
      excludeIndex (List.range (seedBoundary + state.openWires.length)))
      partnerCandidate with
  | isTrue resultEqCandidate => exact resultEqCandidate
  | isFalse resultNeCandidate =>
      have sameExcludeResult : isSameComponent state.links
          (natListGetAt (List.range seedBoundary ++ state.openWires) excludeIndex)
          (natListGetAt (List.range seedBoundary ++ state.openWires)
            (findPartnerScan state.links (List.range seedBoundary ++ state.openWires)
              (unionFindRootOf state.links
                (natListGetAt (List.range seedBoundary ++ state.openWires) excludeIndex))
              excludeIndex (List.range (seedBoundary + state.openWires.length)))) = true :=
        decide_eq_true resultRoot.symm
      exact False.elim (arcBoundaryCensus_boundaryNodes seedBoundary state census
        excludeIndex partnerCandidate
        (findPartnerScan state.links (List.range seedBoundary ++ state.openWires)
          (unionFindRootOf state.links
            (natListGetAt (List.range seedBoundary ++ state.openWires) excludeIndex))
          excludeIndex (List.range (seedBoundary + state.openWires.length)))
        excludeInRange candidateInRange resultInRange
        (fun excludeEqCandidate => candidateNeExclude excludeEqCandidate.symm)
        (fun excludeEqResult => resultNeExclude excludeEqResult.symm)
        (fun candidateEqResult => resultNeCandidate candidateEqResult.symm)
        sameReads sameExcludeResult)

/-- **Honesty marker — the census PARTNER UNIQUENESS is SHIPPED (peel campaign H, cup rung
2d-v).**  At a censused state the canonical partner scan's answer is pinned by any exhibited
same-component candidate (`partnerIndexOf_uniqueSameComponent`).  What this marker does NOT
claim: the fused-component leg rewiring built on this pin (the composite partner of a leg
attachment jumping to the other leg's attachment) and the cup-cancellation endgame.
`= true`. -/
def fxMode_hasArcCensusPartnerUnique : Bool := true

end FX1Poly.Polygraph
