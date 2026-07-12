import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingEquivariantTransport
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusPartnerUnique
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPerfectMatching
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingExtract

/-! # MODE-COMMUTE r9 — the partner field σ-CONJUGATES in the perfect-matching regime

`ArcCrossingEquivariantTransport` (r8) closed the COUNT-field half of the crossing equivariance transport
UNCONDITIONALLY and left the PARTNER-field half as an explicitly-regime-gated open arm: the σ-conjugation
`conjugatePartner` holds on a genuine perfect matching (`crossing_paired_partner_eq_conjugate`) but is
REFUTED off it (`crossing_triComponent_partner_ne_conjugate`, three ports in one component — `findPartnerScan`'s
MIN-index answer does not commute with the transposition there).  So the r8 marker
`fxMode_hasArcCrossingPartnerEquivariantTransport` legitimately stays `false`: it is the UNCONDITIONAL ∀-state
claim, which is genuinely false.

This file lands the CONDITIONAL claim.  For a state satisfying the two shipped fold-preserved invariants
— the boundary census `ArcBoundaryCensus` (≤ 2 boundary ends per component) and the perfect matching
`ArcPerfectMatching` (each boundary index has a distinct same-component partner) — the crossing at `position`
conjugates the whole `diagram.partner` list by the boundary transposition `transposeAdjacent (bottomCount +
position)`:

  ★ **`partner_stepCrossArc_eq_conjugate`** (the headline):
    `(extractArc bc (stepCrossArc st p)).diagram.partner = conjugatePartner (extractArc bc st).diagram.partner
    (bc + p)`, under `window`, `census`, and `perfect` on `st`.

The mechanism.  In the perfect-matching regime every boundary port has a UNIQUE partner, so `findPartnerScan`'s
"first match" IS the "only match", and min-index becomes irrelevant.  The uniqueness is the shipped
`partnerIndexOf_uniqueSameComponent` (census pins the scan).  The transport of the connectivity reads across the
swap is the shipped boundary anchor `natListGetAt_boundaryNodes_stepCrossArc` (root-equivariance under σ), and
the perfect-matching no-fixed-point bridge (`partnerIndexOf_neSelf_ofPerfectMatching`) rules out the degenerate
disjunct.  Crucially, only the UNCROSSED census + matching (both fold-delivered on `st`) are used — no crossed-
state regime preservation is needed for the flip.

## What this file does NOT do (the pins stay false)

It does NOT wire the faithful crossing into `arcSwapCorePackage_of_adjunctionSwap` and it does NOT flip the
general-signature peel.  `fxMode_hasArcPeelGeneralSignature` (the arity ceiling — no builder for `crossAtom`)
and the #2043 / WP-AMALG residual `fxMode_hasArcGodementSamePartitionFreshProof` stay `false`; the shipped
`stepArcAtom` / `extractArc` are never edited.  The r8 UNCONDITIONAL partner marker
`fxMode_hasArcCrossingPartnerEquivariantTransport` also stays `false` — this file introduces a DISTINCTLY-named
regime-conditional marker `fxMode_hasArcCrossingPartnerConjugationInMatchingRegime` instead (a duplicate global
would be invisible to isolated builds).  This certificate is strictly ADDITIVE.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.  The transposition is the
r8 `transposeAdjacent` (joint structural recursion, `rfl`-clean); the one genuinely new transposition fact here
is its INVOLUTIVITY, proved by the same joint recursion.  Per-declaration `#assert_no_axioms` gated in the audit
twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (per-file copies, following the codebase pattern) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

private theorem rangeLoopGetAt_past : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAt_past count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAt_below : (count : Nat) → (accumulated : List Nat) → (index : Nat) →
    index < count → natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAt_below count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAt_past count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAt_below (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAt_below count [] index indexBelow

private theorem listMapLength (mapFunction : Nat → Nat) :
    (entries : List Nat) → (entries.map mapFunction).length = entries.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (listMapLength mapFunction rest)

private theorem rangeLoopMem_ofAccumulated : (count : Nat) → (accumulated : List Nat) →
    (target : Nat) → target ∈ accumulated → target ∈ List.range.loop count accumulated
  | 0, _, _, targetMem => targetMem
  | count + 1, accumulated, target, targetMem =>
      rangeLoopMem_ofAccumulated count (count :: accumulated) target (List.Mem.tail count targetMem)

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
          exact rangeLoopMem_ofAccumulated count (count :: accumulated) count (List.Mem.head accumulated)

private theorem rangeMem_ofLt (count target : Nat) (targetBelow : target < count) :
    target ∈ List.range count :=
  rangeLoopMem_ofLt count [] target targetBelow

/-- The partner scan returns either the exclude fallback or a member of the scanned list (per-file copy
of the shipped private membership lemma). -/
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

/-! ## NODE 1 — the adjacent transposition is an involution (structural, `rfl`-clean)

The one genuinely-new transposition fact.  Proved by the SAME joint structural recursion as the r8 equational
lemmas (`transposeAdjacent_pivot` / `_succ`): each of the five leaves reduces definitionally, the recursive
leaf under the `+1` shift by the inductive hypothesis. -/

/-- ★ **`transposeAdjacent pivot` is an involution.**  Swapping `pivot` and `pivot + 1` twice returns every
index — the R2 relation at the index level. -/
theorem transposeAdjacent_involutive : (pivot target : Nat) →
    transposeAdjacent pivot (transposeAdjacent pivot target) = target
  | 0, 0 => rfl
  | 0, 1 => rfl
  | 0, _ + 2 => rfl
  | _ + 1, 0 => rfl
  | pivot + 1, target + 1 => by
      show transposeAdjacent pivot (transposeAdjacent pivot target) + 1 = target + 1
      rw [transposeAdjacent_involutive pivot target]

/-- ★ **`transposeAdjacent pivot` is injective** — from the involution: apply the transposition to both sides. -/
theorem transposeAdjacent_injective (pivot firstTarget secondTarget : Nat)
    (imagesEqual : transposeAdjacent pivot firstTarget = transposeAdjacent pivot secondTarget) :
    firstTarget = secondTarget := by
  have lifted := congrArg (transposeAdjacent pivot) imagesEqual
  rw [transposeAdjacent_involutive pivot firstTarget, transposeAdjacent_involutive pivot secondTarget] at lifted
  exact lifted

/-! ## NODE 2 — the census-free min-index PIN over an arbitrary boundary

A state-free, census-free generalization of the shipped `partnerIndexOf_uniqueSameComponent`, built purely from
the shipped scan kit: given ONE in-range same-root candidate that is moreover the UNIQUE such, the min-index
scan is pinned to it (min-index is irrelevant once the candidate is unique). -/

/-- ★ **The partner scan lands on a unique candidate.**  If `candidate` is in range, differs from the probe,
shares the probe's root, and is the ONLY in-range non-probe index sharing that root, then `partnerIndexOf` at
the probe equals `candidate` — the scan's min-index preference never comes into play. -/
theorem partnerIndexOf_eq_of_uniqueCandidate (links : List (Nat × Nat)) (boundaryNodes : List Nat)
    (total excludeIndex candidate : Nat)
    (candidateInRange : candidate < total) (candidateNeExclude : candidate ≠ excludeIndex)
    (sameRoot : unionFindRootOf links (natListGetAt boundaryNodes candidate)
      = unionFindRootOf links (natListGetAt boundaryNodes excludeIndex))
    (unique : ∀ other, other < total → other ≠ excludeIndex →
      unionFindRootOf links (natListGetAt boundaryNodes other)
        = unionFindRootOf links (natListGetAt boundaryNodes excludeIndex) → other = candidate) :
    partnerIndexOf links boundaryNodes total excludeIndex = candidate := by
  show findPartnerScan links boundaryNodes
      (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex)) excludeIndex (List.range total)
    = candidate
  have candidateMem : candidate ∈ List.range total := rangeMem_ofLt total candidate candidateInRange
  have resultNeExclude : findPartnerScan links boundaryNodes
      (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex)) excludeIndex (List.range total)
      ≠ excludeIndex :=
    findPartnerScan_neExclude_ofTarget links boundaryNodes
      (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex)) excludeIndex (List.range total)
      candidate candidateMem candidateNeExclude sameRoot
  have resultRoot := findPartnerScan_root_ofFound links boundaryNodes
    (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex)) excludeIndex (List.range total)
    resultNeExclude
  have resultMem : findPartnerScan links boundaryNodes
      (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex)) excludeIndex (List.range total)
      ∈ List.range total := by
    cases findPartnerScan_memOrExclude links boundaryNodes
        (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex)) excludeIndex (List.range total) with
    | inl isExclude => exact absurd isExclude resultNeExclude
    | inr isMember => exact isMember
  exact unique (findPartnerScan links boundaryNodes
      (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex)) excludeIndex (List.range total))
    (mem_range_imp_lt resultMem) resultNeExclude resultRoot

/-! ## NODE 3 — the pointwise conjugation (the σ-transfer of a single partner)

The load-bearing lemma.  Writing `sigma := transposeAdjacent (bottomCount + position)`, the crossed partner of
`index` equals `sigma` of the UNCROSSED partner of `sigma index`.  Existence and uniqueness of that candidate
come entirely from the uncrossed census + matching; the connectivity reads transfer by the boundary anchor. -/

/-- ★ **The pointwise partner conjugation.**  Under the perfect-matching regime on `state`, the crossed scan at
`index` returns `transposeAdjacent (bottomCount + position)` of the uncrossed scan at
`transposeAdjacent (bottomCount + position) index`. -/
theorem partnerIndexOf_stepCrossArc_eq_conjugate (bottomCount position index : Nat)
    (state : ArcWireState) (window : position + 1 < state.openWires.length)
    (census : ArcBoundaryCensus bottomCount state)
    (perfect : ArcPerfectMatching bottomCount state)
    (indexInRange : index < bottomCount + state.openWires.length) :
    partnerIndexOf state.links (List.range bottomCount ++ natListSwapTwoAt state.openWires position)
        (bottomCount + state.openWires.length) index
      = transposeAdjacent (bottomCount + position)
          (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
            (bottomCount + state.openWires.length)
            (transposeAdjacent (bottomCount + position) index)) := by
  have pivotBound : bottomCount + position + 1 < bottomCount + state.openWires.length := by
    have base := Nat.add_lt_add_left window bottomCount
    rw [← Nat.add_assoc] at base
    exact base
  have sigmaIndexLtTotal : transposeAdjacent (bottomCount + position) index
      < bottomCount + state.openWires.length :=
    transposeAdjacent_lt (bottomCount + position) index (bottomCount + state.openWires.length)
      indexInRange pivotBound
  have partnerLtTotal : partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length) (transposeAdjacent (bottomCount + position) index)
      < bottomCount + state.openWires.length :=
    partnerIndexOf_below state bottomCount (transposeAdjacent (bottomCount + position) index) sigmaIndexLtTotal
  have pNeSigmaIndex : partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length) (transposeAdjacent (bottomCount + position) index)
      ≠ transposeAdjacent (bottomCount + position) index :=
    partnerIndexOf_neSelf_ofPerfectMatching bottomCount state perfect
      (transposeAdjacent (bottomCount + position) index) sigmaIndexLtTotal
  have candidateInRange : transposeAdjacent (bottomCount + position)
        (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
          (bottomCount + state.openWires.length) (transposeAdjacent (bottomCount + position) index))
      < bottomCount + state.openWires.length :=
    transposeAdjacent_lt (bottomCount + position)
      (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length) (transposeAdjacent (bottomCount + position) index))
      (bottomCount + state.openWires.length) partnerLtTotal pivotBound
  have candidateNeExclude : transposeAdjacent (bottomCount + position)
        (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
          (bottomCount + state.openWires.length) (transposeAdjacent (bottomCount + position) index))
      ≠ index := by
    intro cEqIndex
    apply pNeSigmaIndex
    have lifted := congrArg (transposeAdjacent (bottomCount + position)) cEqIndex
    rw [transposeAdjacent_involutive (bottomCount + position)
      (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length) (transposeAdjacent (bottomCount + position) index))] at lifted
    exact lifted
  have sameRoot : unionFindRootOf state.links
        (natListGetAt (List.range bottomCount ++ natListSwapTwoAt state.openWires position)
          (transposeAdjacent (bottomCount + position)
            (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
              (bottomCount + state.openWires.length) (transposeAdjacent (bottomCount + position) index))))
      = unionFindRootOf state.links
        (natListGetAt (List.range bottomCount ++ natListSwapTwoAt state.openWires position) index) := by
    rw [natListGetAt_boundaryNodes_stepCrossArc bottomCount state.openWires position
          (transposeAdjacent (bottomCount + position)
            (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
              (bottomCount + state.openWires.length) (transposeAdjacent (bottomCount + position) index)))
          window,
        natListGetAt_boundaryNodes_stepCrossArc bottomCount state.openWires position index window,
        transposeAdjacent_involutive (bottomCount + position)
          (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
            (bottomCount + state.openWires.length) (transposeAdjacent (bottomCount + position) index))]
    cases partnerIndexOf_sameComponent_or_fixed state bottomCount
        (transposeAdjacent (bottomCount + position) index) with
    | inl fixed => exact absurd fixed pNeSigmaIndex
    | inr same => exact (of_decide_eq_true same).symm
  have unique : ∀ other, other < bottomCount + state.openWires.length → other ≠ index →
      unionFindRootOf state.links
          (natListGetAt (List.range bottomCount ++ natListSwapTwoAt state.openWires position) other)
        = unionFindRootOf state.links
          (natListGetAt (List.range bottomCount ++ natListSwapTwoAt state.openWires position) index) →
      other = transposeAdjacent (bottomCount + position)
        (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
          (bottomCount + state.openWires.length) (transposeAdjacent (bottomCount + position) index)) := by
    intro other otherLtTotal otherNeIndex hroot
    rw [natListGetAt_boundaryNodes_stepCrossArc bottomCount state.openWires position other window,
        natListGetAt_boundaryNodes_stepCrossArc bottomCount state.openWires position index window] at hroot
    have sigmaOtherLtTotal : transposeAdjacent (bottomCount + position) other
        < bottomCount + state.openWires.length :=
      transposeAdjacent_lt (bottomCount + position) other (bottomCount + state.openWires.length)
        otherLtTotal pivotBound
    have sigmaOtherNeSigmaIndex : transposeAdjacent (bottomCount + position) other
        ≠ transposeAdjacent (bottomCount + position) index :=
      fun eq => otherNeIndex (transposeAdjacent_injective (bottomCount + position) other index eq)
    have pEqSigmaOther : partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length) (transposeAdjacent (bottomCount + position) index)
        = transposeAdjacent (bottomCount + position) other :=
      partnerIndexOf_uniqueSameComponent bottomCount state census
        (transposeAdjacent (bottomCount + position) index) (transposeAdjacent (bottomCount + position) other)
        sigmaIndexLtTotal sigmaOtherLtTotal sigmaOtherNeSigmaIndex (decide_eq_true hroot.symm)
    have sigmaPEqOther : transposeAdjacent (bottomCount + position)
        (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
          (bottomCount + state.openWires.length) (transposeAdjacent (bottomCount + position) index)) = other := by
      rw [pEqSigmaOther, transposeAdjacent_involutive (bottomCount + position) other]
    exact sigmaPEqOther.symm
  exact partnerIndexOf_eq_of_uniqueCandidate state.links
    (List.range bottomCount ++ natListSwapTwoAt state.openWires position)
    (bottomCount + state.openWires.length) index
    (transposeAdjacent (bottomCount + position)
      (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length) (transposeAdjacent (bottomCount + position) index)))
    candidateInRange candidateNeExclude sameRoot unique

/-! ## NODE 4 — the whole-list conjugation + the regime marker

Lift the pointwise conjugation to the whole `diagram.partner` list by the same list-extensionality skeleton as
the r8 count-field swap (`natListEqOfPointwiseGetAt` over the per-index equivariance). -/

/-- ★ **The crossing σ-CONJUGATES the whole partner list, in the perfect-matching regime.**  For a state with
the boundary census and the perfect matching, `(extractArc bc (stepCrossArc st p)).diagram.partner =
conjugatePartner (extractArc bc st).diagram.partner (bc + p)` — positions permuted by `transposeAdjacent (bc + p)`
AND values remapped by it.  The r9 partner-field half of the crossing equivariance transport. -/
theorem partner_stepCrossArc_eq_conjugate (bottomCount position : Nat) (state : ArcWireState)
    (window : position + 1 < state.openWires.length)
    (census : ArcBoundaryCensus bottomCount state)
    (perfect : ArcPerfectMatching bottomCount state) :
    (extractArc bottomCount (stepCrossArc state position)).diagram.partner
      = conjugatePartner (extractArc bottomCount state).diagram.partner (bottomCount + position) := by
  have lenEq : (natListSwapTwoAt state.openWires position).length = state.openWires.length :=
    natListSwapTwoAt_length state.openWires position window
  have pivotBound : bottomCount + position + 1 < bottomCount + state.openWires.length := by
    have base := Nat.add_lt_add_left window bottomCount
    rw [← Nat.add_assoc] at base
    exact base
  have pivotBoundMapped : bottomCount + position + 1
      < ((List.range (bottomCount + state.openWires.length)).map
        (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
          (bottomCount + state.openWires.length))).length := by
    rw [listMapLength, rangeLength]
    exact pivotBound
  show (List.range (bottomCount + (natListSwapTwoAt state.openWires position).length)).map
      (partnerIndexOf state.links (List.range bottomCount ++ natListSwapTwoAt state.openWires position)
        (bottomCount + (natListSwapTwoAt state.openWires position).length))
    = (natListSwapTwoAt
        ((List.range (bottomCount + state.openWires.length)).map
          (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
            (bottomCount + state.openWires.length)))
        (bottomCount + position)).map (transposeAdjacent (bottomCount + position))
  rw [lenEq]
  refine natListEqOfPointwiseGetAt _ _ ?_ ?_
  · rw [listMapLength, listMapLength,
      natListSwapTwoAt_length
        ((List.range (bottomCount + state.openWires.length)).map
          (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
            (bottomCount + state.openWires.length)))
        (bottomCount + position) pivotBoundMapped,
      listMapLength]
  · intro index indexBound
    have indexLtTotal : index < bottomCount + state.openWires.length := by
      rw [listMapLength, rangeLength] at indexBound
      exact indexBound
    have indexLtRange : index < (List.range (bottomCount + state.openWires.length)).length := by
      rw [rangeLength]
      exact indexLtTotal
    have swapLtTotal : index
        < (natListSwapTwoAt
            ((List.range (bottomCount + state.openWires.length)).map
              (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
                (bottomCount + state.openWires.length)))
            (bottomCount + position)).length := by
      rw [natListSwapTwoAt_length
            ((List.range (bottomCount + state.openWires.length)).map
              (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
                (bottomCount + state.openWires.length)))
            (bottomCount + position) pivotBoundMapped,
        listMapLength, rangeLength]
      exact indexLtTotal
    have sigmaIndexLtTotal : transposeAdjacent (bottomCount + position) index
        < bottomCount + state.openWires.length :=
      transposeAdjacent_lt (bottomCount + position) index (bottomCount + state.openWires.length)
        indexLtTotal pivotBound
    have sigmaIndexLtRange : transposeAdjacent (bottomCount + position) index
        < (List.range (bottomCount + state.openWires.length)).length := by
      rw [rangeLength]
      exact sigmaIndexLtTotal
    rw [natListGetAt_map_inRange
        (partnerIndexOf state.links (List.range bottomCount ++ natListSwapTwoAt state.openWires position)
          (bottomCount + state.openWires.length))
        (List.range (bottomCount + state.openWires.length)) index indexLtRange,
      rangeGetAt_below (bottomCount + state.openWires.length) index indexLtTotal,
      natListGetAt_map_inRange (transposeAdjacent (bottomCount + position))
        (natListSwapTwoAt
          ((List.range (bottomCount + state.openWires.length)).map
            (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
              (bottomCount + state.openWires.length)))
          (bottomCount + position))
        index swapLtTotal,
      natListGetAt_natListSwapTwoAt
        ((List.range (bottomCount + state.openWires.length)).map
          (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
            (bottomCount + state.openWires.length)))
        (bottomCount + position) index pivotBoundMapped,
      natListGetAt_map_inRange
        (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
          (bottomCount + state.openWires.length))
        (List.range (bottomCount + state.openWires.length))
        (transposeAdjacent (bottomCount + position) index) sigmaIndexLtRange,
      rangeGetAt_below (bottomCount + state.openWires.length)
        (transposeAdjacent (bottomCount + position) index) sigmaIndexLtTotal]
    exact partnerIndexOf_stepCrossArc_eq_conjugate bottomCount position index state window census perfect
      indexLtTotal

/-! ## Non-vacuity witnesses (the flip fires at the fresh seed) + the honest wall -/

/-- ★ **The regime marker is non-vacuous: the flip fires at EVERY fresh seed crossing.**  At the seed
`openWires = List.range bottomCount` (all singleton components), the census and the perfect matching are the
shipped `arcBoundaryCensus_initial` / `arcPerfectMatching_initial`, so the general conjugation applies for every
in-window `position`.  A genuine, parameterized application — not a hand fixture. -/
theorem arcCrossingPartnerConjugation_seed_confirms (bottomCount position : Nat)
    (window : position + 1 < bottomCount) :
    (extractArc bottomCount
        (stepCrossArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) position)).diagram.partner
      = conjugatePartner
          (extractArc bottomCount (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])).diagram.partner
          (bottomCount + position) :=
  partner_stepCrossArc_eq_conjugate bottomCount position
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
    (by
      show position + 1 < (List.range bottomCount).length
      rw [rangeLength]
      exact window)
    (arcBoundaryCensus_initial bottomCount)
    (arcPerfectMatching_initial bottomCount)

/-- A concrete instance (width-2 seed, front crossing) derived from the general seed theorem — no brute
`decide` over `extractArc`, just the specialization. -/
theorem arcCrossingPartnerConjugation_seed2_confirms :
    (extractArc 2 (stepCrossArc (ArcWireState.mk (List.range 2) [] 2 0 [] []) 0)).diagram.partner
      = conjugatePartner (extractArc 2 (ArcWireState.mk (List.range 2) [] 2 0 [] [])).diagram.partner (2 + 0) :=
  arcCrossingPartnerConjugation_seed_confirms 2 0 (by decide)

/-- ★ **The jamming arm stays REFUTED — the honest wall.**  Off the perfect-matching regime the conjugation
FAILS: on the three-port component `crossingTriComponentState` (which violates `ArcPerfectMatching` — nodes
`41`/`42` share `40`'s component, so the min-index answer does not commute with the transposition), the r8
refutation `crossing_triComponent_partner_ne_conjugate` still holds.  The general theorem simply does not apply
there (its `perfect`/`census` hypotheses genuinely fail), so no over-generalization has occurred. -/
theorem arcCrossingPartnerConjugation_triComponent_stays_refuted :
    (extractArc 0 (stepCrossArc crossingTriComponentState 0)).diagram.partner
      ≠ conjugatePartner (extractArc 0 crossingTriComponentState).diagram.partner 0 :=
  crossing_triComponent_partner_ne_conjugate

/-! ## Honesty markers + pins -/

/-- **Honesty marker — the PARTNER-field conjugation is PROVED in the perfect-matching regime (the r9 arm).**
`partner_stepCrossArc_eq_conjugate` establishes `(extractArc bc (stepCrossArc st p)).diagram.partner =
conjugatePartner (extractArc bc st).diagram.partner (bc + p)` under `window`, `census` (`ArcBoundaryCensus`), and
`perfect` (`ArcPerfectMatching`) on `st` — both shipped, fold-preserved invariants.  Built from NODE 1
(`transposeAdjacent_involutive` / `_injective`), NODE 2 (`partnerIndexOf_eq_of_uniqueCandidate`, the census-free
min-index pin), NODE 3 (`partnerIndexOf_stepCrossArc_eq_conjugate`, the pointwise σ-transfer via the shipped
census-uniqueness + no-fixed-point bridge + boundary anchor), and NODE 4 (the whole-list lift).  Non-vacuous:
`arcCrossingPartnerConjugation_seed_confirms` fires the flip at every fresh-seed crossing via the shipped initial
census + matching.  What this marker does NOT claim: the UNCONDITIONAL ∀-state conjugation (genuinely FALSE off
the regime — `arcCrossingPartnerConjugation_triComponent_stays_refuted`, so the r8
`fxMode_hasArcCrossingPartnerEquivariantTransport` correctly stays `false`), the general-signature peel
dispatcher, and any crossed-state regime preservation (route B needs only the uncrossed invariants).  `= true`. -/
def fxMode_hasArcCrossingPartnerConjugationInMatchingRegime : Bool := true

/-- **Honesty pin — the r8 UNCONDITIONAL partner marker stays `false`.**  This file lands the regime-CONDITIONAL
claim; the ∀-state claim `fxMode_hasArcCrossingPartnerEquivariantTransport` is genuinely refuted off the regime
and is untouched.  `rfl`. -/
theorem arcCrossingPartnerConjugation_unconditionalPartner_stays_false :
    fxMode_hasArcCrossingPartnerEquivariantTransport = false := rfl

/-- **Honesty pin — the count-field marker stays `true`.**  The r8 unconditional count-field transport is
untouched.  `rfl`. -/
theorem arcCrossingPartnerConjugation_countField_stays_true :
    fxMode_hasArcCrossingCountEquivariantTransport = true := rfl

/-- **Honesty pin — the general-signature peel stays the open keystone.**  This arm supplies the partner-field
half of a general-signature peel's transport machinery in the perfect-matching regime; it does not build the
dispatcher.  `fxMode_hasArcPeelGeneralSignature` stays `false`.  `rfl`. -/
theorem arcCrossingPartnerConjugation_generalSignature_stays_false :
    fxMode_hasArcPeelGeneralSignature = false := rfl

/-- **Honesty pin — the #2043 / WP-AMALG fresh-partition keystone is untouched.**
`fxMode_hasArcGodementSamePartitionFreshProof` stays `false`.  `rfl`. -/
theorem arcCrossingPartnerConjugation_samePartitionFreshProof_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
