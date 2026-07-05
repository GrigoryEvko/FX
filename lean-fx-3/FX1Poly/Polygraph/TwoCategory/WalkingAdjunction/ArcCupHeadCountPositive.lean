import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold

/-! # ArcCupHeadCountPositive — a cup-headed spine has a positive cup total

The cup case of the chained head extraction (`#2152`) needs the second spine's cup total
positive to feed the cup locator (`arcCupLocateAndBubble_ofCupCountPos`).  That positivity
comes from the FIRST spine's cup head and arc-structure equality: the head cup fires a cup
event (`stepCupArc` prepends one to `cupEventNodes`), and no walking-adjunction step ever
removes cup events (`stepCapArc` leaves `cupEventNodes` fixed), so the cup total — which is
exactly `cupEventNodes.length` — is at least one for any cup-headed spine.

  * `cupEventNodes_length_monotone` — the cup-event list never shrinks through the fold (the
    cup/cap arity dichotomy: cups prepend one, caps leave it fixed);
  * ★ `arcCupHead_cupCount_pos` — a cup-headed spine has `0 < cupCount`.

Consumed by the cup case: transporting this across arc-structure equality gives
`0 < cupCount secondList`, the `arcCupLocateAndBubble_ofCupCountPos` premise.

Raw Lean 4 + Init; structural recursion + the arity dichotomy; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- A cup step prepends exactly one cup-event node. -/
private theorem stepCupArc_cupEventNodes (state : ArcWireState) (position : Nat) :
    (stepCupArc state position).cupEventNodes = (state.nextFresh + 2) :: state.cupEventNodes :=
  rfl

/-- A cap step leaves the cup-event list untouched. -/
private theorem stepCapArc_cupEventNodes (state : ArcWireState) (position : Nat) :
    (stepCapArc state position).cupEventNodes = state.cupEventNodes :=
  rfl

/-- **The cup-event list never shrinks through the fold.**  Structural recursion on the spine
using the walking-adjunction arity dichotomy: a cup step prepends one cup-event node, a cap step
leaves the list fixed, so each step's cup-event length is at least the entry's, and the fold
composes the inequalities. -/
theorem cupEventNodes_length_monotone
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    ∀ (state : ArcWireState),
      state.cupEventNodes.length ≤ (processArcSpine state atoms).cupEventNodes.length := by
  induction atoms with
  | nil =>
      intro state
      exact Nat.le_refl _
  | cons atom rest inductionHypothesis =>
      intro state
      have stepMono : state.cupEventNodes.length
          ≤ (stepArcAtom state atom).cupEventNodes.length := by
        cases adjunctionSpineAtom_hasCupOrCapArity atom with
        | inl cupArity =>
            rw [stepArcAtom_eq_stepCupArc state atom cupArity.1 cupArity.2,
              stepCupArc_cupEventNodes]
            exact Nat.le_succ state.cupEventNodes.length
        | inr capArity =>
            rw [stepArcAtom_eq_stepCapArc state atom capArity.1 capArity.2,
              stepCapArc_cupEventNodes]
            exact Nat.le_refl state.cupEventNodes.length
      exact Nat.le_trans stepMono (inductionHypothesis (stepArcAtom state atom))

/-- ★ **A cup-headed spine has a positive cup total.**  The head cup fires a cup event
(`stepCupArc` prepends one), so the state entering the tail fold already has a nonempty
cup-event list; the fold never shrinks it (`cupEventNodes_length_monotone`), so the final
`cupCount` (= `cupEventNodes.length`) is at least one. -/
theorem arcCupHead_cupCount_pos (bottomCount : Nat)
    {overallSource overallTarget : adjunctionGraph.Mode}
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    0 < (arcStructureOfSpineList bottomCount (headAtom :: tailList)).cupCount := by
  have startPos : 0 < (stepArcAtom
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      headAtom).cupEventNodes.length := by
    rw [stepArcAtom_eq_stepCupArc
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) headAtom
      hasCupDomArity hasCupCodArity, stepCupArc_cupEventNodes]
    exact Nat.succ_pos _
  have mono := cupEventNodes_length_monotone tailList
    (stepArcAtom (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) headAtom)
  exact Nat.lt_of_lt_of_le startPos mono

/-! ## Honesty marker -/

/-- **Honesty marker — cup-headed positivity is SHIPPED.**  `arcCupHead_cupCount_pos`: a
cup-headed walking-adjunction spine has `0 < cupCount`, because the head cup fires a cup event
that the fold never removes (`cupEventNodes_length_monotone` — cups prepend, caps leave fixed).
Transported across arc-structure equality this gives `0 < cupCount secondList`, the premise of
`arcCupLocateAndBubble_ofCupCountPos`.  What this marker does NOT claim: `windowPin` or
`tailsCancel` — the orbit pins.  `= true`. -/
def fxMode_hasArcCupHeadCountPositive : Bool := true

end FX1Poly.Polygraph
