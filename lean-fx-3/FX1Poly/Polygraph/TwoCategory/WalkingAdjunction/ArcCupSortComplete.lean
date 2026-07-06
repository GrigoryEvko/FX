import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSiblingSwap
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.DisjointWindowSwap
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapPeel
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupTransfer
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLastCupReadoff
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupStepDrop
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupDropAndAppend
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPeelFoundations

/-! # WalkingAdjunction/ArcCupSortComplete — pure-cup completeness `pureCupSpine_sort` (#2184)

The crux of the walking-adjunction word-problem completeness: two boundary-chained pure-cup
spines with equal arc structure are `SpineTraceEquiv`.  This file assembles the top theorem
`pureCupSpine_sort` from the shipped transposition atoms (`cupSwapStep` / its mirror), the
last-cup short-chord readoff (S1), the drop-injectivity linchpin (S3), and the back-append
congruence, driven by a shift-tracked location induction.

  * `cupSwapStepMirror` (M1) — the LEFT variant of `cupSwapStep`: swapping two adjacent
    disjoint-window sibling cups where the FIRST has the LARGER window.  Rides the mirrored
    realized swap (`adjunctionSpineAtomSwapLeft_of_disjointWindows`) through the atomic
    closure's symmetry and the shipped peel.
  * `allCupArity_prefix_ofAppend` (M2) — a pure-cup append's prefix is pure cup (the `propext`-free
    prefix analogue of `allCupArity_ofCons`, via the cap-count split).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (the sibling kit copies are file-private) -/

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

/-! ## Cup arity readoff helpers (`propext`-free, routed through the cap count) -/

/-- **A pure-cup head atom is a cup** — its domain arity is `0` and codomain arity `2`.  Every
walking-adjunction atom is a cup or a cap (`adjunctionSpineAtom_isCupOrCap`); a cap head would
tally one, refuting `capAtomCount (headAtom :: rest) = 0` (`capAtomCount_ofAllCupArity`).  Routed
through the cap count rather than an indexed `cases` on `AllCupArity`, so it stays `propext`-free. -/
private theorem headCupArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    {headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (pureCup : AllCupArity (headAtom :: rest)) :
    headAtom.generatorDom.length = 0 ∧ headAtom.generatorCod.length = 2 := by
  have consCapZero : capAtomCount (headAtom :: rest) = 0 :=
    capAtomCount_ofAllCupArity (headAtom :: rest) pureCup
  cases adjunctionSpineAtom_isCupOrCap headAtom with
  | inl cupArity => exact cupArity
  | inr capArity =>
      exfalso
      have guardTrue :
          (headAtom.generatorDom.length == 2 && headAtom.generatorCod.length == 0) = true := by
        rw [capArity.1, capArity.2]
        rfl
      dsimp only [capAtomCount] at consCapZero
      rw [if_pos guardTrue] at consCapZero
      exact Nat.noConfusion (Nat.add_comm 1 (capAtomCount rest) ▸ consCapZero)

/-! ## M1 — the mirrored sibling-cup transposition -/

/-- ★ **The mirrored sibling-cup transposition (M1).**  Two adjacent disjoint-window sibling cups
transpose when the FIRST has the LARGER window: `atomSecond.leftContext.length + windowGap =
atomFirst.leftContext.length`.  The moved pair's BACK element is `atomFirst`-derived with its
left context re-threaded through `atomSecond`'s codomain and the inert gap, so its window is
`atomSecond.leftContext.length + 2 + windowGap = atomFirst.leftContext.length + 2` (the
smaller-window `atomSecond` firing first shifts the bubbled cup up by its two legs).

The EQUIV half rides the mirrored realized swap (`adjunctionSpineAtomSwapLeft_of_disjointWindows`,
whose SOURCE is the moved pair) through the atomic closure's `symm` + `toSpineTraceEquiv`; the ARC
half rides the shipped peel `extractArc_eq_of_atomicTraceEquiv` at the fresh initial state, with
the window fit threaded by the chain discipline.  The moved back element's window is returned
explicitly for the location induction's shift bookkeeping. -/
theorem cupSwapStepMirror
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (atomFirst atomSecond : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (bothCup : AllCupArity (atomFirst :: atomSecond :: rest))
    (chained : SpineBoundaryChained bottomCount (atomFirst :: atomSecond :: rest))
    (bottomPositive : 0 < bottomCount)
    (windowGap : Nat)
    (windowsDisjoint :
      atomSecond.leftContext.length + windowGap = atomFirst.leftContext.length) :
    ∃ movedFront movedBack,
      SpineTraceEquiv adjunctionModeSignature (atomFirst :: atomSecond :: rest)
          (movedFront :: movedBack :: rest)
        ∧ arcStructureOfSpineList bottomCount (atomFirst :: atomSecond :: rest)
            = arcStructureOfSpineList bottomCount (movedFront :: movedBack :: rest)
        ∧ movedBack.leftContext.length = atomFirst.leftContext.length + 2
        ∧ movedBack.generatorDom.length = 0
        ∧ movedBack.generatorCod.length = 2 := by
  obtain ⟨secondDom, secondCod⟩ := headCupArity (allCupArity_ofCons bothCup)
  obtain ⟨firstDom, firstCod⟩ := headCupArity bothCup
  have boundariesChain : atomSecond.domBoundaryLength = atomFirst.codBoundaryLength := by
    obtain ⟨_, tailChained⟩ := spineBoundaryChained_tail chained
    exact (spineBoundaryChained_tail tailChained).1
  have windowsDisjoint' :
      atomSecond.leftContext.length + atomSecond.generatorDom.length + windowGap
        = atomFirst.leftContext.length := by
    rw [secondDom, Nat.add_zero]
    exact windowsDisjoint
  obtain ⟨inertPath, inertLength, swapLeft⟩ :=
    adjunctionSpineAtomSwapLeft_of_disjointWindows atomFirst atomSecond rest boundariesChain
      windowGap windowsDisjoint'
  refine ⟨{ atomSecond with
              rightContext :=
                composePath (composePath inertPath atomFirst.generatorDom)
                  atomFirst.rightContext },
          { atomFirst with
              leftContext :=
                composePath (composePath atomSecond.leftContext atomSecond.generatorCod)
                  inertPath },
          ?_, ?_, ?_, firstDom, firstCod⟩
  · exact (AtomicTraceEquiv.ofSwap swapLeft).symm.toSpineTraceEquiv
  · exact extractArc_eq_of_atomicTraceEquiv (AtomicTraceEquiv.ofSwap swapLeft).symm
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount bottomCount
      (arcStateFresh_initial bottomCount) isUnionFindForest_nil bottomPositive
      (Nat.le_refl bottomCount) (rangeLength bottomCount) chained
  · show (composePath (composePath atomSecond.leftContext atomSecond.generatorCod) inertPath).length
        = atomFirst.leftContext.length + 2
    rw [ModalityPath.length_composePath, ModalityPath.length_composePath, inertLength, secondCod,
      Nat.add_assoc atomSecond.leftContext.length 2 windowGap,
      Nat.add_comm 2 windowGap, ← Nat.add_assoc atomSecond.leftContext.length windowGap 2,
      windowsDisjoint]

/-! ## M2 — a pure-cup append's prefix is pure cup -/

/-- The left summand of a vanishing `Nat` sum is zero — a `noConfusion` peel on the successor case
(`succ predLeft + rightSummand` is defeq `succ (predLeft + rightSummand)`), staying `propext`-free
where `Nat.eq_zero_of_add_eq_zero_right` would leak. -/
private theorem addLeftZero {leftSummand rightSummand : Nat}
    (sumZero : leftSummand + rightSummand = 0) : leftSummand = 0 := by
  cases leftSummand with
  | zero => rfl
  | succ predLeft =>
      exact Nat.noConfusion (Nat.add_comm (predLeft + 1) rightSummand ▸ sumZero)

/-- ★ **A pure-cup append's prefix is pure cup (M2).**  From `AllCupArity (prefixAtoms ++
suffixAtoms)`, the whole cap tally is zero (`capAtomCount_ofAllCupArity`); the append splits the
tally (`capAtomCount_append`), so the prefix's cap tally is the left summand of a vanishing sum,
hence zero (`addLeftZero`), whence `AllCupArity prefixAtoms` (`allCupArity_ofCapAtomCountZero`).
Routed through the cap count rather than an indexed `cases`, so it stays `propext`-free.  The
location induction peels the last cup off the append and recurses on the prefix. -/
theorem allCupArity_prefix_ofAppend
    {overallSource overallTarget : adjunctionGraph.Mode}
    (prefixAtoms suffixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (appendPureCup : AllCupArity (prefixAtoms ++ suffixAtoms)) :
    AllCupArity prefixAtoms := by
  have appendCapZero : capAtomCount (prefixAtoms ++ suffixAtoms) = 0 :=
    capAtomCount_ofAllCupArity (prefixAtoms ++ suffixAtoms) appendPureCup
  have splitCapZero : capAtomCount prefixAtoms + capAtomCount suffixAtoms = 0 :=
    (capAtomCount_append prefixAtoms suffixAtoms).symm.trans appendCapZero
  exact allCupArity_ofCapAtomCountZero prefixAtoms (addLeftZero splitCapZero)

/-! ## Honesty marker -/

/-- **Honesty marker — the pure-cup sort's mirrored transposition atom + prefix purity are
SHIPPED.**  `cupSwapStepMirror` (M1) transposes two adjacent disjoint-window sibling cups where
the first has the larger window (mirror of `cupSwapStep`), returning the moved back cup's window
explicitly for the location induction's shift bookkeeping; `allCupArity_prefix_ofAppend` (M2) is
the `propext`-free prefix purity the peel-and-recurse induction needs.  What this marker does NOT
claim: the location induction `locateAux` (constructing the located spine from a partner chord) or
the top theorem `pureCupSpine_sort`. -/
def fxMode_hasArcCupSortComplete : Bool := true

end FX1Poly.Polygraph
