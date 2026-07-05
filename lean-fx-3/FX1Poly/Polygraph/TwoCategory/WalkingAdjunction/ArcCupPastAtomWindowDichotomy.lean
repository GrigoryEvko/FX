import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupWindowParityDichotomy
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking

/-! # ArcCupPastAtomWindowDichotomy — a cup descends past ANY prefix atom, below-or-past

The cup bubble producer (#2152) descends a realizing cup back through a prefix, and at each
passed atom `P` the `SpineAtomSwap` step (`DisjointWindowSwap.lean`) needs one of the two
window-gap equations that make the swap disjoint:

  * **past** (`adjunctionSpineAtomSwap_of_disjointWindows`, `P` fires first):
    `P.leftContext.length + P.generatorCod.length + gap = cup.leftContext.length`;
  * **below** (`adjunctionSpineAtomSwapLeft_of_disjointWindows`): with the cup's `generatorDom`
    empty, `cup.leftContext.length + gap = P.leftContext.length`.

For a CUP target (`generatorDom.length = 0`), those collapse to `wP + P.cod + gap = w` (past) and
`w + gap = wP` (below), i.e. `w ≤ wP ∨ wP + P.cod ≤ w`.  This file discharges that dichotomy
past ANY cup-or-cap atom by dispatching on `P`'s arity:

  * `P` a **cup** (`cod = 2`): the strictly-interior window `wP + 1` is parity-forbidden
    (`adjunctionCupAtomWindowDichotomy`, brick 1) — a cup can't nest between another cup's legs.
  * `P` a **cap** (`cod = 0`): `P.cod` vanishes, so past needs `w ≥ wP` and below `w ≤ wP` —
    Nat totality, ALWAYS one holds.  The snake case `w = wP + 1` (a cup feeding a leg into a
    following cap) is parity-consistent but does NOT obstruct the swap: with the cap's empty
    codomain the two swap windows abut with no interior gap.

So a cup descends past EVERY prefix atom with a clean below/past choice, unconditionally — the
per-step disjointness for the whole cup bubble producer.  The residual orbit lives entirely in
the CANCEL (matching the peeled remainder to the tail), not in the bubble's descent.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The cup descent step's clean dichotomy past any atom.**  A cup atom
(`targetIsCup : generatorDom.length = 0`) and any cup-or-cap prefix atom `passedAtom` have
windows ordered below-or-past: the cup's window is at or below `passedAtom`'s, or at least
`passedAtom.generatorCod.length` beyond it.  Dispatches on `passedAtom`'s arity
(`adjunctionSpineAtom_hasCupOrCapArity`): the cup branch is the parity dichotomy
(`adjunctionCupAtomWindowDichotomy`), the cap branch is Nat totality (the cap's empty codomain
abuts the two swap windows with no interior gap).  This is the per-step disjointness the cup
bubble producer's descent consumes at every passed atom. -/
theorem adjunctionCupPastAtomWindowDichotomy
    {overallSource overallTarget : adjunctionGraph.Mode}
    (targetAtom passedAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (targetIsCup : targetAtom.generatorDom.length = 0) :
    targetAtom.leftContext.length ≤ passedAtom.leftContext.length
      ∨ passedAtom.leftContext.length + passedAtom.generatorCod.length
          ≤ targetAtom.leftContext.length := by
  cases adjunctionSpineAtom_hasCupOrCapArity passedAtom with
  | inl cupArity =>
      rw [cupArity.2]
      exact adjunctionCupAtomWindowDichotomy targetAtom passedAtom targetIsCup cupArity.1
  | inr capArity =>
      rw [capArity.2, Nat.add_zero]
      exact Nat.le_total targetAtom.leftContext.length passedAtom.leftContext.length

/-! ## Honesty marker -/

/-- **Honesty marker — the cup descends past any prefix atom, below-or-past (SHIPPED).**
`adjunctionCupPastAtomWindowDichotomy` gives the clean below/past window dichotomy a cup enjoys
past ANY cup-or-cap atom: the cup case rides the parity dichotomy (brick 1,
`adjunctionCupWindowParityDichotomy`), the cap case is Nat totality (empty codomain, no interior
gap).  This is the per-step disjointness for the whole cup bubble producer's descent — no atom
obstructs the swap.  What this marker does NOT claim: the front-first descent recursion
assembling `BubblesToFront` (the inert-path minting + `SpineAtomSwap` iteration), nor the CANCEL
(the residual orbit: the peeled remainder matching the tail's arc structure).  `= true`. -/
def fxMode_hasArcCupPastAtomWindowDichotomy : Bool := true

end FX1Poly.Polygraph
