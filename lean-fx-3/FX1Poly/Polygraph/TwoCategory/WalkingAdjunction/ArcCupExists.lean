import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold

/-! # ArcCupExists — a positive cup total locates a cup atom in the spine

The cup-head discharge (`#2152`) opens by LOCATING the realizing cup in the second spine.
The cap side reads its consuming cap off a tracked pair; the cup side has no pair to track —
but it has the cup TOTAL.  This brick ships the existence half of the cup locator: if the
arc-structure of a walking-adjunction spine records at least one cup event, the spine splits
at a cup atom.

The key fact is that `cupCount` counts cup EVENTS, and cup events come only from cup atoms:
`stepCupArc` prepends one cup-event node, while the only other walking-adjunction step
(`stepCapArc`, the cap) leaves `cupEventNodes` untouched.  So a strictly-grown cup-event list
forces a cup atom somewhere in the fold — a structural recursion that peels caps (which don't
grow the list) until it meets the cup that did.

  * `arcSpine_cupSplit_of_cupEventGrowth` — the fold form: a run whose cup-event list grew
    strictly past the entry state's splits at a cup atom;
  * ★ `arcSpine_hasCup_of_cupCount_pos` — the read-off: `0 < cupCount` locates a cup atom.

Used by the reconstruction's cup case: `arcStructureOfSpineList bc (headCup :: tail)
= arcStructureOfSpineList bc secondList` with `headCup` a cup forces `0 < cupCount secondList`,
so `secondList` contains a cup to bubble to the front (the input the cup bubble producer
`adjunctionCup_bubblesThroughPrefix` consumes).

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **A grown cup-event list locates a cup atom.**  If processing `atoms` from `state` grows
the cup-event list strictly past `state`'s, then `atoms` splits at a cup atom.  Structural
recursion on `atoms` using the walking-adjunction arity dichotomy: the head is a cup (done,
empty prefix) or a cap (`stepCapArc` leaves `cupEventNodes` fixed, so the growth persists past
the step and the tail carries the cup — prepend the cap to the prefix). -/
theorem arcSpine_cupSplit_of_cupEventGrowth
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    ∀ (state : ArcWireState),
      state.cupEventNodes.length < (processArcSpine state atoms).cupEventNodes.length →
      ∃ (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
        (cupAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
        (suffixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
        atoms = prefixAtoms ++ cupAtom :: suffixAtoms
          ∧ cupAtom.generatorDom.length = 0 ∧ cupAtom.generatorCod.length = 2 := by
  induction atoms with
  | nil =>
      intro state growth
      exact absurd growth (Nat.lt_irrefl _)
  | cons atom rest inductionHypothesis =>
      intro state growth
      cases adjunctionSpineAtom_hasCupOrCapArity atom with
      | inl cupArity =>
          exact ⟨[], atom, rest, rfl, cupArity.1, cupArity.2⟩
      | inr capArity =>
          have stepEq : (stepArcAtom state atom).cupEventNodes = state.cupEventNodes := by
            rw [stepArcAtom_eq_stepCapArc state atom capArity.1 capArity.2]
            rfl
          have growthAtStep : (stepArcAtom state atom).cupEventNodes.length
              < (processArcSpine (stepArcAtom state atom) rest).cupEventNodes.length := by
            rw [stepEq]
            exact growth
          obtain ⟨prefixAtoms, cupAtom, suffixAtoms, splitRest, cupDom, cupCod⟩ :=
            inductionHypothesis (stepArcAtom state atom) growthAtStep
          exact ⟨atom :: prefixAtoms, cupAtom, suffixAtoms,
            congrArg (fun restTail => atom :: restTail) splitRest, cupDom, cupCod⟩

/-- ★ **A positive cup total locates a cup atom.**  If the arc-structure of a spine (read from
the canonical `bottomCount` seed) records at least one cup event, the spine splits at a cup
atom.  Direct instance of `arcSpine_cupSplit_of_cupEventGrowth` at the seed, whose cup-event
list is empty, so `0 < cupCount` is exactly the strict-growth premise. -/
theorem arcSpine_hasCup_of_cupCount_pos
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (cupCountPos : 0 < (arcStructureOfSpineList bottomCount atoms).cupCount) :
    ∃ (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
      (cupAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
      (suffixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
      atoms = prefixAtoms ++ cupAtom :: suffixAtoms
        ∧ cupAtom.generatorDom.length = 0 ∧ cupAtom.generatorCod.length = 2 := by
  apply arcSpine_cupSplit_of_cupEventGrowth atoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
  exact cupCountPos

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-existence half of the cup locator is SHIPPED.**
`arcSpine_hasCup_of_cupCount_pos`: a positive cup total locates a cup atom in the spine, by
structural recursion peeling caps (which never grow the cup-event list) to the cup that did.
This is the existence input to the cup-head discharge (`#2152`): arc-structure equality with a
cup-headed reference forces the second spine's cup total positive, hence a locatable cup.  What
this marker does NOT claim: that the located cup is at the head's WINDOW (the window read-off,
coupled to the bubble's window-shift), nor `tailsCancel` (the orbit).  `= true`. -/
def fxMode_hasArcCupExists : Bool := true

end FX1Poly.Polygraph
