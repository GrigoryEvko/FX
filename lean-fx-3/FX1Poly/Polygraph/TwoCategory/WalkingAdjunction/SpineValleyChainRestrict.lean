import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineArityDiscipline
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCapSpine

/-! # SpineValleyChainRestrict — the Piece-I suffix-chain restriction (Tier B)

The clean whole-valley theorem `valleysWithEqualMatching_spineTraceEquiv` consumes, per valley, the CUP-block
boundary-chaining read at the mid-width: `SpineBoundaryChained (processSpine ⟨…⟩ capBlock).openWires.length
cupBlock`.  The whole cell only supplies the WHOLE chain `SpineBoundaryChained bottomCount (capBlock ++ cupBlock)`
(via `RawTwoCellExpr.spineBoundaryChained_spine`).  This file restricts the whole chain to the cup suffix — the
dual of the shipped prefix restriction `spineBoundaryChained_prefix_ofAppend`:

  * ★ `spineBoundaryChained_cupSuffix_ofCapPrefix` — over a PURE-CAP prefix (`AllCapArity`, so each atom's
    open-wire count tracks its boundary via `stepAtom_openWires_tracksBoundary`), the whole chain
    `SpineBoundaryChained state.openWires.length (capBlock ++ cupBlock)` restricts to the cup suffix
    `SpineBoundaryChained (processSpine state capBlock).openWires.length cupBlock`.

Structural induction on the cap prefix: the head cap fires at the running boundary (chain inversion), and by the
arity tracker the stepped state's open-wire count is exactly the head's target boundary, at which the tail chain
continues.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The cup-suffix chain restriction.**  A whole valley chained from `state.openWires.length` restricts, over
its pure-cap prefix, to the cup suffix chained from the mid-width `(processSpine state capBlock).openWires.length`.
Each cap fires at the running boundary (chain inversion) and `stepAtom_openWires_tracksBoundary` shows the stepped
open-wire count equals the head's target boundary, at which the tail chain continues — so the induction threads the
mid-width to the cup block. -/
theorem spineBoundaryChained_cupSuffix_ofCapPrefix
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (capBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    AllCapArity capBlock →
    (cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    (state : WireState) →
    SpineBoundaryChained state.openWires.length (capBlock ++ cupBlock) →
    SpineBoundaryChained (processSpine state capBlock).openWires.length cupBlock
  | [], _, _, _, chained => chained
  | atom :: rest, capPure, cupBlock, state, chained => by
      cases capPure with
      | cons capDom capCod restCap =>
          obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
          have arity : AtomHasCupOrCapArity atom := Or.inr ⟨capDom, capCod⟩
          have stepTracks : (stepAtom state atom).openWires.length = atom.codBoundaryLength :=
            stepAtom_openWires_tracksBoundary state atom arity headFires.symm
          have tailChainedAtStep :
              SpineBoundaryChained (stepAtom state atom).openWires.length (rest ++ cupBlock) := by
            rw [stepTracks]; exact tailChained
          show SpineBoundaryChained (processSpine (stepAtom state atom) rest).openWires.length cupBlock
          exact spineBoundaryChained_cupSuffix_ofCapPrefix rest restCap cupBlock
            (stepAtom state atom) tailChainedAtStep

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the Piece-I cup-suffix chain restriction is SHIPPED, zero-axiom.**
`spineBoundaryChained_cupSuffix_ofCapPrefix` restricts a whole-valley boundary chain to the cup suffix (read at the
mid-width) over a pure-cap prefix — the dual of the shipped prefix restriction, producing the `cupChained` premise
the whole-valley theorem `valleysWithEqualMatching_spineTraceEquiv` consumes.

  What this marker does NOT itself close: the mid-width equality from equal matching, the whole-valley final-width
  equality, and the positivity dispatch for degenerate valleys — the remaining rungs of the cell-level
  `CellValleyTraceEquiv` bridge.  No gate flag is flipped.  `= true`. -/
def fxMode_hasSpineValleyChainRestrict : Bool := true

end FX1Poly.Polygraph
