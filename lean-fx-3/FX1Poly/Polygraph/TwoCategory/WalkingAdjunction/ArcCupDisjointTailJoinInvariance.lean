import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupDisjointCapWindowPin

/-! # ArcCupDisjointTailJoinInvariance — the head cup's census survives an ARBITRARY window-disjoint tail

`ArcCupDisjointCapWindowPin` shipped the R1 head-cup window read-off lifted past ONE window-disjoint cap
(`singleCupHeadWindowPinned_pastDisjointCap`): the cup event's same-component view survives the single cap's
TWO joins, because both cap wires sit below the bottom boundary and the cap event sits above the leg strand
(`cupEventComponent_reduce_pastDisjointCap`, via the reusable single-join `isSameComponent_unionFindJoin_offProbe`).
This brick lifts the JOIN side of that peel from ONE cap to an ARBITRARY window-disjoint tail — the exact
Forest–Mimram "epimorphisms are stable by pushouts … by induction on `k`" step (arXiv:2109.05369, proof of
Prop. 4.2.4): a probe's component is invariant under folding a WHOLE LIST of joins, each of whose endpoints
avoids the probe's component.

## The route-around is the FINER invariant, not the raw arc field

`ArcCupHeadWindowUniversalRefuted` machine-checked that the head-cup window is NOT a universal function of
the arc structure — the two independent-cup witnesses share the WHOLE `FullArcStructure`, `internalCupCounts`
INCLUDED, yet their head cups sit at windows `0 ≠ 2` (`headCupWindowReadoff_isFalse`).  So the census read-off
is sound ONLY inside the leg-strand-fixed regime: a lone cup, or a cup whose tail events are all WINDOW-DISJOINT
(their wires and events land OUTSIDE the cup's three-node leg strand `[bottomCount, bottomCount + 3)`).  This
file does NOT contradict that refutation — it stays strictly inside the leg-strand-fixed regime, where the
cup event's census is genuinely arc-visible, and generalizes the JOIN side of the peel to arbitrary tail length.

  * ★ `foldJoins` — fold a list of join-pairs onto a base partition (the arc-fold's link evolution as a
    homogeneous `unionFindJoin` fold, cf. `stepCap_links_eq_unionFindJoin`).
  * ★ `isUnionFindForest_foldJoins` — the fold stays a forest (each `unionFindJoin` preserves acyclicity).
  * ★ `isSameComponent_foldJoins_offProbe` — the ★ kernel: if every pair in `joins` has BOTH endpoints off
    `probe`'s component (in the base partition), the fold leaves `probe`'s same-component view pointwise
    unchanged.  Structural induction on `joins`, threading the single-join `isSameComponent_unionFindJoin_offProbe`
    and the forest/off-probe preservation across each step (off-probe-in-base is off-probe-throughout, exactly
    because the view is preserved).
  * ★ `isSameComponent_foldJoins_offZone` — the windowPin-anchored corollary: with `probe` off every node
    strictly below `lowerBound` and off every node at or above `upperBound`, a fold of joins whose endpoints
    all live OUTSIDE the zone `[lowerBound, upperBound)` leaves `probe`'s view unchanged.  Instantiated with the
    cup event `bottomCount + 2` and its leg strand `[bottomCount, bottomCount + 3)`, this says the head cup's
    census view survives an arbitrarily long window-disjoint tail — the `k`-cap generalization of the shipped
    single-cap `cupEventComponent_reduce_pastDisjointCap`.

Raw Lean 4 + Init; the same union-find kit, structural on the join list, no `omega` / `simp`-AC /
`WellFounded.fix`.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- Fold a list of join-pairs onto a base partition: each pair `(a, b)` contributes `unionFindJoin · a b`.
This is the arc-fold's link evolution — every step's link update is a uniform `unionFindJoin` (the cup on its
two fresh legs, a cap on its two read wires; `stepCap_links_eq_unionFindJoin`). -/
def foldJoins (links : List (Nat × Nat)) (joins : List (Nat × Nat)) : List (Nat × Nat) :=
  joins.foldl (fun accumulatedLinks pair => unionFindJoin accumulatedLinks pair.1 pair.2) links

/-- The fold onto a forest stays a forest — each `unionFindJoin` preserves acyclicity. -/
theorem isUnionFindForest_foldJoins :
    (joins : List (Nat × Nat)) → (links : List (Nat × Nat)) → isUnionFindForest links →
    isUnionFindForest (foldJoins links joins)
  | [], _, baseForest => baseForest
  | pair :: remainingJoins, links, baseForest =>
      isUnionFindForest_foldJoins remainingJoins (unionFindJoin links pair.1 pair.2)
        (isUnionFindForest_unionFindJoin links pair.1 pair.2 baseForest)

/-- ★ **The head cup's census survives an ARBITRARY off-strand join fold.**  If every pair in `joins` has BOTH
endpoints off `probe`'s component (in the base partition), then folding all of `joins` leaves `probe`'s
same-component view pointwise unchanged: `isSameComponent (foldJoins links joins) probe other = isSameComponent
links probe other`.  Structural induction on `joins`, reusing the single-join `isSameComponent_unionFindJoin_offProbe`
at the head; the tail's off-probe hypotheses are re-established in the joined partition precisely because the
view is preserved.  This is the FM Prop. 4.2.4 "stable under pushouts by induction on `k`" step. -/
theorem isSameComponent_foldJoins_offProbe (probe : Nat) :
    (joins : List (Nat × Nat)) → (links : List (Nat × Nat)) → isUnionFindForest links →
    (∀ pair, pair ∈ joins →
      isSameComponent links pair.1 probe = false ∧ isSameComponent links pair.2 probe = false) →
    ∀ other, isSameComponent (foldJoins links joins) probe other = isSameComponent links probe other
  | [], _, _, _, _ => rfl
  | pair :: remainingJoins, links, baseForest, endpointsOffProbe, other => by
      have headOff := endpointsOffProbe pair (List.Mem.head remainingJoins)
      have forestStep := isUnionFindForest_unionFindJoin links pair.1 pair.2 baseForest
      have tailOff : ∀ laterPair, laterPair ∈ remainingJoins →
          isSameComponent (unionFindJoin links pair.1 pair.2) laterPair.1 probe = false
          ∧ isSameComponent (unionFindJoin links pair.1 pair.2) laterPair.2 probe = false := by
        intro laterPair laterMember
        have laterFull := endpointsOffProbe laterPair (List.Mem.tail pair laterMember)
        refine ⟨?_, ?_⟩
        · rw [isSameComponent_symm, isSameComponent_unionFindJoin_offProbe links baseForest pair.1 pair.2
              probe laterPair.1 headOff.1 headOff.2, isSameComponent_symm]
          exact laterFull.1
        · rw [isSameComponent_symm, isSameComponent_unionFindJoin_offProbe links baseForest pair.1 pair.2
              probe laterPair.2 headOff.1 headOff.2, isSameComponent_symm]
          exact laterFull.2
      have inductiveStep := isSameComponent_foldJoins_offProbe probe remainingJoins
        (unionFindJoin links pair.1 pair.2) forestStep tailOff other
      show isSameComponent (foldJoins (unionFindJoin links pair.1 pair.2) remainingJoins) probe other
        = isSameComponent links probe other
      rw [inductiveStep, isSameComponent_unionFindJoin_offProbe links baseForest pair.1 pair.2 probe other
        headOff.1 headOff.2]

/-- ★ **The window-disjoint tail is arc-invisible to the head cup — for ANY tail length.**  With `probe` off
every node strictly below `lowerBound` and off every node at or above `upperBound`, a fold of joins whose
endpoints all live OUTSIDE the zone `[lowerBound, upperBound)` leaves `probe`'s same-component view unchanged.
Instantiate with the cup event `bottomCount + 2` and its leg strand zone `[bottomCount, bottomCount + 3)`: a
window-disjoint tail (every cap wire below `bottomCount`, every cap event at/above `bottomCount + 3`) leaves
the head cup's census view untouched, generalizing the single-cap `cupEventComponent_reduce_pastDisjointCap`
to arbitrary length. -/
theorem isSameComponent_foldJoins_offZone (probe lowerBound upperBound : Nat)
    (links : List (Nat × Nat)) (baseForest : isUnionFindForest links)
    (belowOff : ∀ node, node < lowerBound → isSameComponent links node probe = false)
    (aboveOff : ∀ node, upperBound ≤ node → isSameComponent links node probe = false)
    (joins : List (Nat × Nat))
    (endpointsZoned : ∀ pair, pair ∈ joins →
      (pair.1 < lowerBound ∨ upperBound ≤ pair.1) ∧ (pair.2 < lowerBound ∨ upperBound ≤ pair.2))
    (other : Nat) :
    isSameComponent (foldJoins links joins) probe other = isSameComponent links probe other :=
  isSameComponent_foldJoins_offProbe probe joins links baseForest
    (fun pair pairMember =>
      ⟨(endpointsZoned pair pairMember).1.elim (belowOff pair.1) (aboveOff pair.1),
        (endpointsZoned pair pairMember).2.elim (belowOff pair.2) (aboveOff pair.2)⟩)
    other

/-! ## Honesty marker -/

/-- **Honesty marker — the JOIN side of the census read-off holds past an ARBITRARY window-disjoint tail.**
`isSameComponent_foldJoins_offProbe` lifts the single-cap `cupEventComponent_reduce_pastDisjointCap` from ONE
cap's two joins to a fold of arbitrarily many joins, each off the head cup's leg strand; `isSameComponent_foldJoins_offZone`
packages it as the leg-strand zone `[bottomCount, bottomCount + 3)` corollary — a window-disjoint tail of ANY
length leaves the head cup's `internalCupCounts` census view untouched.  This is the FM Prop. 4.2.4
"epimorphisms stable under pushouts, by induction on `k`" step, and it stays STRICTLY inside the leg-strand-fixed
regime, so it does NOT contradict `ArcCupHeadWindowUniversalRefuted` / `headCupWindowReadoff_isFalse` (which
refutes the census read-off only in the general, moved-strand regime — two INDEPENDENT cups reordered).

What this marker does NOT claim, and what the census inversion still needs to reach `windowPin`:
  (1) the BOUNDARY-READ side for a `k`-cap tail — the `k`-fold composition of `natListRemoveTwoAt` disjoint
      removals leaving the leg read `1` and the below-window reads `0` (the shipped single-cap
      `twoAtomBoundaryRead_atLeftLeg` / `_belowWindow` handle one removal; the `k`-fold splice is open);
  (2) `tailsCancel` — the INTERACTING cap (gap `0`/`1`, where cup and cap ARE a zigzag and CANCEL via the
      snake, not a census read-off);
  (3) the SNAKE reconciliation — reconciling the cancelled zigzag's window with the fronted cup's window
      (the `arcCupReselection_exists` orbit-representative content refuted as an arc-field readoff).
No gate flip: `fxMode_hasArcStructureReconstruction` and `fxMode_hasModeRelativeConvDecision` stay as is —
this is the join-side ingredient, not the full `windowPin`.  `= true`. -/
def fxMode_hasArcCupDisjointTailJoinInvariance : Bool := true

end FX1Poly.Polygraph
