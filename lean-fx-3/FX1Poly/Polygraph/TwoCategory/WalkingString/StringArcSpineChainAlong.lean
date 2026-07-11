import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcArity
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking

/-! # WalkingString/StringArcSpineChainAlong — the boundary chain advances along the arc fold (FC-3 r22, B2 P3)

The read-off's split-state seat bound needs the length-only boundary chain to survive folding a prefix segment
of the spine.  This is the string clone of `WalkingAdjunction/ArcCapWindowSeedReadoff`'s
`spineBoundaryChained_alongArcSpine`.  The ONLY colour-specific input is the arity classifier: the arc original
calls `adjunctionSpineAtom_hasCupOrCapArity`; the string calls the shipped four-generator
`adjointTripleSpineAtom_hasCupOrCapArity` (`StringArcArity`).  Everything else — `stepArcAtom`,
`processArcSpine`, `stepArcAtom_openWires_tracksBoundary`, `SpineBoundaryChained` — is signature-GENERIC arc-fold
machinery over the colour-blind `ArcWireState` (a `Nat` open-wire count), so NO length-rigidity is used and the
lemma is TRUE at the adjoint triple.

Raw Lean 4 + Init; structural recursion on the folded prefix.  `propext`/`Quot.sound`/`Classical`/`sorry`/
`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The boundary chain advances along the arc fold.**  Chained at the entry state's open-wire count, the
remainder after folding a prefix segment is chained at the advanced state's open-wire count — each cup/cap step
tracks its boundary (`stepArcAtom_openWires_tracksBoundary`), and every walking-adjoint-triple atom has the
required cup-or-cap arity (`adjointTripleSpineAtom_hasCupOrCapArity`).  The string clone of the walking-adjunction
`spineBoundaryChained_alongArcSpine`, its only delta the arity classifier. -/
theorem stringSpineBoundaryChained_alongArcSpine
    {sourceMode targetMode : adjointTripleGraph.Mode} :
    (atoms rest : List (SpineAtom adjointTripleModeSignature sourceMode targetMode)) →
    (state : ArcWireState) →
    SpineBoundaryChained state.openWires.length (atoms ++ rest) →
    SpineBoundaryChained (processArcSpine state atoms).openWires.length rest
  | [], _, _, chained => chained
  | headAtom :: tailAtoms, rest, state, chained => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      rw [← stepArcAtom_openWires_tracksBoundary state headAtom
        (adjointTripleSpineAtom_hasCupOrCapArity headAtom) headFires.symm] at tailChained
      exact stringSpineBoundaryChained_alongArcSpine tailAtoms rest (stepArcAtom state headAtom)
        tailChained

/-- **Honesty marker — the arc-fold chain advance is SHIPPED (FC-3 r22, B2 P3).**
`stringSpineBoundaryChained_alongArcSpine` threads the length-only boundary chain through a folded prefix segment
at the adjoint triple, the clone of the walking-adjunction `spineBoundaryChained_alongArcSpine` with the shipped
four-generator arity classifier in place of the two-generator one.  Colour-blind arc-fold machinery, no
length-rigidity.  This is the split-state seat bound the (still-open) read-off master consumes.  What this marker
does NOT claim: the read-off itself (the word descent master, phantom-locked at the arc source, is the standing
residual) or the head discharge.  `= true`. -/
def fxString_hasArcSpineChainAlong : Bool := true

end FX1Poly.Polygraph
