import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSeed
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix

/-! # WalkingString/StringArcArity — the four-generator cup/cap arity dispatch (FC-3 item 1 foundation)

The arc-preservation peel (`extractArc_eq_of_atomicTraceEquiv` at the walking adjunction) rests on ONE
signature-keyed classification: every spine atom is a CUP (`0 ⇒ 2`, a unit) or a CAP (`2 ⇒ 0`, a counit), so the
arc fold's generic-box arm never fires and the boundary-tracking / window-suffix kit (`AtomHasCupOrCapArity`)
discharges wholesale.

The walking ADJOINT TRIPLE has FOUR generators (two units `unitLower`/`unitUpper`, two counits
`counitLower`/`counitUpper`) rather than two, so the dispatch grows to four arms — but it stays entirely
COLOUR-BLIND: it reads only the cup-vs-cap arity (a `Nat` length pair), never which colour.  `stepArcAtom`
dispatches on `(generatorDom.length, generatorCod.length)`, so a string cup (dom length `0`, cod length `2`)
reduces to `stepCupArc` exactly as an adjunction unit does; no length-rigidity is used anywhere here.  This is the
cheapest of the FC-3 chain's five items and the shared foundation both the peel (item 1) and the bubble-to-front
driver (item 2, via `allCupArity_preservedOfAtomicTraceEquiv`) consume.

Raw Lean 4 + Init; the classification is a four-way `cases` on `StringTwoCell`, each arm a defeq arity pair.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Seed classification — every string spine atom is a cup or a cap -/

/-- ★ **Seed classification (four generators)**: every walking-adjoint-triple spine atom is a cup (`0 ⇒ 2`, a unit)
or a cap (`2 ⇒ 0`, a counit).  The two units (`unitLower : id ⇒ F·G`, `unitUpper : id ⇒ G·H`) are cups; the two
counits (`counitLower : G·F ⇒ id`, `counitUpper : H·G ⇒ id`) are caps.  The arc fold's generic-box arm never fires
at the seed, so cup/cap event reasoning is exhaustive — the colour-blind arity split the peel consumes. -/
theorem adjointTripleSpineAtom_isCupOrCap
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (atom : SpineAtom adjointTripleModeSignature overallSource overallTarget) :
    (atom.generatorDom.length = 0 ∧ atom.generatorCod.length = 2)
      ∨ (atom.generatorDom.length = 2 ∧ atom.generatorCod.length = 0) := by
  obtain ⟨leftMid, rightMid, leftContext, generatorDom, generatorCod, generator,
    rightContext⟩ := atom
  dsimp only
  cases generator with
  | unitLower => exact Or.inl ⟨rfl, rfl⟩
  | counitLower => exact Or.inr ⟨rfl, rfl⟩
  | unitUpper => exact Or.inl ⟨rfl, rfl⟩
  | counitUpper => exact Or.inr ⟨rfl, rfl⟩

/-- ★ **Every walking-adjoint-triple atom has cup-or-cap arity** — the seed's only generators are the two units
(`0 ⇒ 2`) and the two counits (`2 ⇒ 0`), so the arity hypothesis of the boundary-tracking and window-suffix kit
(`AtomHasCupOrCapArity`) discharges wholesale at the string signature.  Delegates to the four-way classification,
which IS `AtomHasCupOrCapArity` unfolded — the direct four-generator analog of
`adjunctionSpineAtom_hasCupOrCapArity`. -/
theorem adjointTripleSpineAtom_hasCupOrCapArity
    {sourceMode targetMode : adjointTripleModeSignature.graph.Mode}
    (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode) :
    AtomHasCupOrCapArity atom :=
  adjointTripleSpineAtom_isCupOrCap atom

/-! ## Non-vacuity — the four generators, as bare spine atoms, land their arity -/

/-- Non-vacuity: the lower unit `η` as a bare spine atom (empty whiskering) is a CUP (`generatorDom.length = 0`,
`generatorCod.length = 2`). -/
theorem stringUnitLowerSpineAtom_isCup :
    (⟨AdjointTripleMode.base, AdjointTripleMode.base,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base, stringFG,
        StringTwoCell.unitLower,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base⟩ :
      SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base).generatorDom.length = 0
    ∧ (⟨AdjointTripleMode.base, AdjointTripleMode.base,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base, stringFG,
        StringTwoCell.unitLower,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base⟩ :
      SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base).generatorCod.length = 2 :=
  ⟨rfl, rfl⟩

/-- Non-vacuity: the upper counit `ε'` as a bare spine atom is a CAP (`generatorDom.length = 2`,
`generatorCod.length = 0`). -/
theorem stringCounitUpperSpineAtom_isCap :
    (⟨AdjointTripleMode.base, AdjointTripleMode.base,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base, stringHG,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
        StringTwoCell.counitUpper,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base⟩ :
      SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base).generatorDom.length = 2
    ∧ (⟨AdjointTripleMode.base, AdjointTripleMode.base,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base, stringHG,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
        StringTwoCell.counitUpper,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base⟩ :
      SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base).generatorCod.length = 0 :=
  ⟨rfl, rfl⟩

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the four-generator cup/cap arity dispatch is machine-checked (FC-3 item 1 foundation).**
`adjointTripleSpineAtom_isCupOrCap` classifies every string spine atom as a cup (unit) or a cap (counit) by a
four-way `cases` on `StringTwoCell`, and `adjointTripleSpineAtom_hasCupOrCapArity` delegates the boundary-tracking /
window-suffix arity hypothesis `AtomHasCupOrCapArity` wholesale — the direct four-generator analog of
`adjunctionSpineAtom_hasCupOrCapArity`.  The dispatch is COLOUR-BLIND (reads only arity, a `Nat` length pair, never
colour) and uses NO length-rigidity, so it ports the adjunction's item-1 foundation to the three-generator seed
without touching the length-rigidity failure.  Both units land as cups and both counits as caps
(`stringUnitLowerSpineAtom_isCup`, `stringCounitUpperSpineAtom_isCap`).  `= true`. -/
def fxString_hasArcArityDispatch : Bool := true

end FX1Poly.Polygraph
