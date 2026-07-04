import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceDecision
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionModeParity

/-! # ArcOpenEndsDiscipline — the typed-ends invariant of the arc fold (peel campaign C, rung 2a)

The circle-freedom heart of the cup/cap peel: along the arc fold of a chained walking-adjunction
spine, every union-find component's open ends are TYPED by position parity (`base`-parity
positions carry the `left` edge, `tip`-parity the `right` edge), and a component never holds two
open ends in the wrong order — pairwise: any two same-component open positions `x < y` have
`x` at `base` parity and `y` at `tip` parity.  The pairwise form self-limits components to at
most two open ends (three pairwise-disciplined ends are contradictory), and it refutes the
same-component cap directly: a cap fires at a `tip`-parity position, but the discipline would
demand `base` there — so `loops` never increments and the legs of a cup are never re-merged.

This brick ships the STATEMENT layer: the discipline, its truth at the fresh seed state, the
parity two-shift stability (window shifts are by two, so parities survive the fold), and the
atom window pins (a cup atom's window sits at `base` parity, a cap atom's at `tip` parity —
through the absolute mode formula).  The cup/cap PRESERVATION steps and the loop-freedom
consequences are the campaign's next rungs.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (per-file copy, following the codebase pattern) -/

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

private theorem rangeLoopGetAt_past : (count : Nat) → (accumulated : List Nat) →
    (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count)
      = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAt_past count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAt_below : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAt_below count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAt_past count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAt_below (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAt_below count [] index indexBelow

/-! ## Parity stability under the fold's window shifts -/

/-- Position parity survives a two-shift: every cup inserts two wires and every cap removes
two, so a surviving open end's mode is unchanged by the reindexing. -/
theorem adjunctionModeAtDistance_stableUnderTwoShift (startMode : AdjunctionMode)
    (distance : Nat) :
    adjunctionModeAtDistance startMode (distance + 2)
      = adjunctionModeAtDistance startMode distance :=
  adjunctionOppositeMode_isInvolutive (adjunctionModeAtDistance startMode distance)

/-! ## The atom window pins — cups fire at base parity, caps at tip parity -/

/-- ★ A cup atom's window position has `base` parity: the unit's source boundary is the empty
path at `base`, so the left context lands on `base`, and the absolute mode formula turns that
into the position's parity. -/
theorem adjunctionCupAtom_windowPositionMode
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : atom.generatorDom.length = 0) :
    adjunctionModeAtDistance overallSource atom.leftContext.length = AdjunctionMode.base := by
  obtain ⟨leftMidMode, rightMidMode, leftContext, generatorDom, generatorCod, generator,
    rightContext⟩ := atom
  dsimp only at hasCupDomArity ⊢
  cases generator with
  | unit => exact (adjunctionPath_targetMode_eq_modeAtDistance leftContext).symm
  | counit => nomatch hasCupDomArity

/-- ★ A cap atom's window position has `tip` parity: the counit's source boundary is the
`right`-then-`left` path at `tip`, so the left context lands on `tip`. -/
theorem adjunctionCapAtom_windowPositionMode
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCapDomArity : atom.generatorDom.length = 2) :
    adjunctionModeAtDistance overallSource atom.leftContext.length = AdjunctionMode.tip := by
  obtain ⟨leftMidMode, rightMidMode, leftContext, generatorDom, generatorCod, generator,
    rightContext⟩ := atom
  dsimp only at hasCapDomArity ⊢
  cases generator with
  | unit => nomatch hasCapDomArity
  | counit => exact (adjunctionPath_targetMode_eq_modeAtDistance leftContext).symm

/-! ## The open-ends discipline -/

/-- ★ **The typed open-ends discipline.**  Any two open positions of the SAME union-find
component are ordered-and-typed: the lower position has `base` parity (it carries the `left`
edge) and the higher has `tip` parity (the `right` edge).  Pairwise, so it self-limits
components to at most two open ends, and it refutes the same-component cap (a cap consumes a
`tip`-parity position where the discipline would demand `base`) — the circle-freedom engine. -/
def ArcOpenEndsDiscipline (sourceMode : AdjunctionMode) (state : ArcWireState) : Prop :=
  ∀ lowPosition highPosition : Nat,
    lowPosition < highPosition →
    highPosition < state.openWires.length →
    isSameComponent state.links (natListGetAt state.openWires lowPosition)
        (natListGetAt state.openWires highPosition) = true →
    adjunctionModeAtDistance sourceMode lowPosition = AdjunctionMode.base
      ∧ adjunctionModeAtDistance sourceMode highPosition = AdjunctionMode.tip

/-- With no links, every node is its own root. -/
private theorem unionFindRootOf_nil (node : Nat) : unionFindRootOf [] node = node := rfl

/-- The fresh seed state satisfies the discipline vacuously: with no links every root is the
node itself, and distinct range positions read distinct wires — no same-component pair
exists. -/
theorem arcOpenEndsDiscipline_initial (sourceMode : AdjunctionMode) (bottomCount : Nat) :
    ArcOpenEndsDiscipline sourceMode
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) := by
  intro lowPosition highPosition lowBelowHigh highInRange sameComponentHolds
  have highBelowLength : highPosition < (List.range bottomCount).length := highInRange
  rw [rangeLength bottomCount] at highBelowLength
  have sameOnRange :
      isSameComponent [] (natListGetAt (List.range bottomCount) lowPosition)
        (natListGetAt (List.range bottomCount) highPosition) = true := sameComponentHolds
  rw [rangeGetAt_below bottomCount lowPosition (Nat.lt_trans lowBelowHigh highBelowLength),
    rangeGetAt_below bottomCount highPosition highBelowLength] at sameOnRange
  have rootsEqualTrue :
      (unionFindRootOf [] lowPosition == unionFindRootOf [] highPosition) = true :=
    sameOnRange
  rw [unionFindRootOf_nil lowPosition, unionFindRootOf_nil highPosition] at rootsEqualTrue
  have positionsDecideTrue : decide (lowPosition = highPosition) = true := rootsEqualTrue
  rw [of_decide_eq_true positionsDecideTrue] at lowBelowHigh
  exact absurd lowBelowHigh (Nat.lt_irrefl highPosition)

/-- **Honesty marker — the open-ends discipline STATEMENT layer is SHIPPED (peel campaign C,
rung 2a).**  The pairwise typed-ends discipline, its vacuous truth at the fresh seed, the
two-shift parity stability, and the cup/cap window pins (base/tip parity through the absolute
mode formula).  What this marker does NOT claim: preservation of the discipline through
`stepCupArc` / `stepCapArc` (rungs 2b/2c — the union-find transfer work) and the loop-freedom
and leg-separation consequences (rung 3) — the circle-freedom payoff stays pending on those.
`= true`. -/
def fxMode_hasArcOpenEndsDisciplineSeed : Bool := true

end FX1Poly.Polygraph
