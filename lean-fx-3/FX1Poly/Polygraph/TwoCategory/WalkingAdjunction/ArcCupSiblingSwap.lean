import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.DisjointWindowSwap
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapPeel
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupTransfer
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPeelFoundations
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain

/-! # WalkingAdjunction/ArcCupSiblingSwap — the pure-cup sort's transposition atoms (#2184)

The pure-cup sort reorders one pure-cup spine into any arc-equal pure-cup spine by a chain of
disjoint-window sibling-cup transpositions.  This file ships the SAFE assembly atoms of that
sort, all riding shipped ingredients:

  * `pureCupSpine_sort_nil` — the empty base case: an arc-equal pure-cup spine to `[]` is `[]`
    (equal arc forces equal length, `pureCupSpines_sameLength_ofArcEqual`), so trace
    equivalence is reflexivity;
  * `cupSwapStep` — the load-bearing atom: swapping two adjacent disjoint-window sibling cups
    is BOTH a `SpineTraceEquiv` step (through the realized disjoint-window swap
    `adjunctionSpineAtomSwap_of_disjointWindows`, wrapped into the atomic closure) AND
    arc-preserving (through the shipped peel `extractArc_eq_of_atomicTraceEquiv` at the
    initial state).

The crux locate/tails-cancel machinery is NOT touched here — these are the composable
transposition atoms the sort driver iterates.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- A list of length zero is nil — a `noConfusion` peel on the cons case's `succ`-headed length,
staying `propext`-free where `List.eq_nil_of_length_eq_zero` (an iff-backed lemma) could leak. -/
private theorem listEqNilOfLengthZero {carrier : Type _} :
    (elems : List carrier) → elems.length = 0 → elems = []
  | [], _ => rfl
  | _ :: _, lengthZero => Nat.noConfusion lengthZero

/-- `(List.range count).length = count` — hand-rolled off the range-loop count (core
`List.length_range` leaks `propext` in this Init-only setting). -/
private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

/-- **A pure-cup head atom carries cup codomain arity `2`.**  Every walking-adjunction atom is a
cup or a cap (`adjunctionSpineAtom_isCupOrCap`); a cap head would contribute one to the cap tally
(`capAtomCount_ofAllCupArity` forces zero), refuting `= 0`.  Routed through the cap count rather
than an indexed `cases` on `AllCupArity`, so it stays `propext`-free. -/
private theorem headCupCodArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    {headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (pureCup : AllCupArity (headAtom :: rest)) :
    headAtom.generatorCod.length = 2 := by
  have consCapZero : capAtomCount (headAtom :: rest) = 0 :=
    capAtomCount_ofAllCupArity (headAtom :: rest) pureCup
  cases adjunctionSpineAtom_isCupOrCap headAtom with
  | inl cupArity => exact cupArity.2
  | inr capArity =>
      exfalso
      have guardTrue :
          (headAtom.generatorDom.length == 2 && headAtom.generatorCod.length == 0) = true := by
        rw [capArity.1, capArity.2]
        rfl
      dsimp only [capAtomCount] at consCapZero
      rw [if_pos guardTrue] at consCapZero
      exact Nat.noConfusion (Nat.add_comm 1 (capAtomCount rest) ▸ consCapZero)

/-- ★ **The empty base case of the pure-cup sort.**  A pure-cup spine whose arc structure equals
the empty spine's is itself empty: equal arc forces equal length
(`pureCupSpines_sameLength_ofArcEqual` with the empty side pure-cup by `AllCupArity.nil`), a
zero-length list is nil (`listEqNilOfLengthZero`), and trace equivalence to `[]` collapses to
reflexivity. -/
theorem pureCupSpine_sort_nil
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (secondPureCup : AllCupArity secondList)
    (arcEqual : arcStructureOfSpineList bottomCount
        ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
      = arcStructureOfSpineList bottomCount secondList) :
    SpineTraceEquiv adjunctionModeSignature [] secondList := by
  have secondNil : secondList = [] :=
    listEqNilOfLengthZero secondList
      (pureCupSpines_sameLength_ofArcEqual bottomCount [] secondList AllCupArity.nil
        secondPureCup arcEqual).symm
  rw [secondNil]
  exact SpineTraceEquiv.refl []

/-- ★ **The load-bearing sibling-cup transposition.**  Two adjacent disjoint-window sibling cups
at the running boundary transpose: the pair is a genuine `SpineTraceEquiv` step AND the swap
preserves the arc structure.

The EQUIV half rides the realized disjoint-window swap
(`adjunctionSpineAtomSwap_of_disjointWindows`) — the boundary adjacency it needs is read off the
chain discipline (`spineBoundaryChained_tail` twice), and the head cup's codomain arity `2`
(`headCupCodArity`) matches the window-gap spelling — wrapped into the atomic closure
(`AtomicTraceEquiv.ofSwap`) and included into the block-level equivalence
(`toSpineTraceEquiv`).

The ARC half rides the shipped peel `extractArc_eq_of_atomicTraceEquiv` at the initial arc state
(`arcStructureOfSpineList` is `extractArc` after `processArcSpine` from that state): the state is
fresh (`arcStateFresh_initial`), forest-rooted (`isUnionFindForest_nil`), has `nextFresh =
bottomCount > 0`, boundary-bounded on the nose, and its open-wire count is `bottomCount`
(`rangeLength`); the chain discipline supplies the peel's window fit.  The moved pair is the swap's
explicit record updates. -/
theorem cupSwapStep
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (atomFirst atomSecond : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (bothCup : AllCupArity (atomFirst :: atomSecond :: rest))
    (chained : SpineBoundaryChained bottomCount (atomFirst :: atomSecond :: rest))
    (bottomPositive : 0 < bottomCount)
    (windowGap : Nat)
    (windowsDisjoint :
      atomFirst.leftContext.length + 2 + windowGap = atomSecond.leftContext.length) :
    ∃ movedPair,
      SpineTraceEquiv adjunctionModeSignature (atomFirst :: atomSecond :: rest)
          (movedPair ++ rest)
        ∧ arcStructureOfSpineList bottomCount (atomFirst :: atomSecond :: rest)
            = arcStructureOfSpineList bottomCount (movedPair ++ rest) := by
  have headCod : atomFirst.generatorCod.length = 2 := headCupCodArity bothCup
  have boundariesChain : atomSecond.domBoundaryLength = atomFirst.codBoundaryLength := by
    obtain ⟨_, tailChained⟩ := spineBoundaryChained_tail chained
    exact (spineBoundaryChained_tail tailChained).1
  have windowsDisjoint' :
      atomFirst.leftContext.length + atomFirst.generatorCod.length + windowGap
        = atomSecond.leftContext.length := by
    rw [headCod]
    exact windowsDisjoint
  obtain ⟨inertPath, _, swapStep⟩ :=
    adjunctionSpineAtomSwap_of_disjointWindows atomFirst atomSecond rest boundariesChain
      windowGap windowsDisjoint'
  refine ⟨[{ atomSecond with
              leftContext :=
                composePath (composePath atomFirst.leftContext atomFirst.generatorDom)
                  inertPath },
            { atomFirst with
              rightContext :=
                composePath (composePath inertPath atomSecond.generatorCod)
                  atomSecond.rightContext }], ?_, ?_⟩
  · exact (AtomicTraceEquiv.ofSwap swapStep).toSpineTraceEquiv
  · exact extractArc_eq_of_atomicTraceEquiv (AtomicTraceEquiv.ofSwap swapStep)
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount bottomCount
      (arcStateFresh_initial bottomCount) isUnionFindForest_nil bottomPositive
      (Nat.le_refl bottomCount) (rangeLength bottomCount) chained

/-! ## Honesty marker -/

/-- **Honesty marker — the pure-cup sort's transposition atoms are SHIPPED.**
`pureCupSpine_sort_nil` (empty base case) and `cupSwapStep` (the sibling-cup transposition, both
a trace step and arc-preserving) are the composable atoms the pure-cup sort driver iterates.
What this marker does NOT claim: the locate/tails-cancel crux, the prefix-bubbling iteration
(`bubbleCupToFront`), or the full sort assembly. -/
def fxMode_hasArcCupSiblingSwap : Bool := true

end FX1Poly.Polygraph
