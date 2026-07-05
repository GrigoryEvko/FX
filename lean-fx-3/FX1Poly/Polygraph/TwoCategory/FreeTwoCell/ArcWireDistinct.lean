import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWireDistinct
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshDecision

/-! # ArcWireDistinct — the open-wire distinctness invariant through the ARC fold

The arc fold's open-wire list never repeats a node id — the arc-side port of
`MatchingWireDistinct`.  This is the consumption-safety prerequisite for locating a head's
realizing atom inside a second spine from arc-structure equality: a cap firing at a position
disjoint from a tracked adjacent wire pair provably does not consume that pair's nodes,
because equal wire VALUES pin equal positions.

* `stepCupArc_wireListDistinct` / `stepCapArc_wireListDistinct` /
  `stepArcAtom_wireListDistinct` — the per-step preservation, mirroring the matching fold's
  lemmas over the SHARED public splice/removal kit (`wireListDistinct_insertFreshBlockAnyPosition`,
  `wireListDistinct_natListRemoveTwoAt`); the wires-below-bound hypothesis is the first
  `ArcStateFresh` conjunct, so no separate freshness predicate is threaded;
* ★ `processArcSpine_wireListDistinct` + `processArcSpine_fromInitial_wireListDistinct` —
  the fold invariant threading `ArcStateFresh` alone (no positivity side condition: the arc
  freshness step lemmas are unconditional), instantiated at the canonical initial arc state
  whose open wires are `List.range bottomCount`.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The per-step preservation -/

/-- An arc CUP step preserves positional distinctness — the two spliced legs are successive
fresh ids, above every existing wire by the first `ArcStateFresh` conjunct. -/
theorem stepCupArc_wireListDistinct (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (distinct : WireListDistinct state.openWires) :
    WireListDistinct (stepCupArc state position).openWires := by
  show WireListDistinct
    (natListInsertAt state.openWires position [state.nextFresh, state.nextFresh + 1])
  refine wireListDistinct_insertFreshBlockAnyPosition state.openWires position
    [state.nextFresh, state.nextFresh + 1] state.nextFresh distinct
    (wireListDistinct_cupLegs state.nextFresh) fresh.1 ?_
  intro leg legMem
  cases legMem with
  | head => exact Nat.le_refl state.nextFresh
  | tail _ legInTail =>
      cases legInTail with
      | head => exact Nat.le_succ state.nextFresh
      | tail _ legDeeper => nomatch legDeeper

/-- An arc CAP step preserves positional distinctness — the removal keeps a positional
subsequence (no freshness needed). -/
theorem stepCapArc_wireListDistinct (state : ArcWireState) (position : Nat)
    (distinct : WireListDistinct state.openWires) :
    WireListDistinct (stepCapArc state position).openWires := by
  show WireListDistinct (natListRemoveTwoAt state.openWires position)
  exact wireListDistinct_natListRemoveTwoAt state.openWires position distinct

/-- One arc fold step preserves positional distinctness — cup and cap by their lemmas, the
generic-box arm by iterated removal then a fresh-block splice. -/
theorem stepArcAtom_wireListDistinct {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (fresh : ArcStateFresh state) (distinct : WireListDistinct state.openWires) :
    WireListDistinct (stepArcAtom state atom).openWires := by
  unfold stepArcAtom
  split
  · exact stepCupArc_wireListDistinct state _ fresh distinct
  · exact stepCapArc_wireListDistinct state _ distinct
  · refine wireListDistinct_insertFreshBlockAnyPosition _ atom.leftContext.length
      ((List.range atom.generatorCod.length).map (· + state.nextFresh)) state.nextFresh
      (wireListDistinct_droppedWires atom.leftContext.length atom.generatorDom.length
        state.openWires distinct)
      (wireListDistinct_freshBlock state.nextFresh atom.generatorCod.length) ?_ ?_
    · exact fun wire wireMem => fresh.1 wire
        (mem_droppedWires atom.leftContext.length atom.generatorDom.length state.openWires
          wire wireMem)
    · exact fun leg legMem =>
        mem_mapAdd_ge state.nextFresh (List.range atom.generatorCod.length) leg legMem

/-! ## The fold invariant -/

/-- ★ **The whole arc fold keeps the open-wire list positionally distinct** — structural
recursion threading `ArcStateFresh` alone (the arc freshness step lemmas carry no positivity
side condition). -/
theorem processArcSpine_wireListDistinct {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : ArcWireState) →
    ArcStateFresh state → WireListDistinct state.openWires →
    WireListDistinct (processArcSpine state atoms).openWires
  | [], _, _, distinct => distinct
  | atom :: rest, state, fresh, distinct => by
      show WireListDistinct (processArcSpine (stepArcAtom state atom) rest).openWires
      exact processArcSpine_wireListDistinct rest (stepArcAtom state atom)
        (arcStateFresh_stepArcAtom state atom fresh)
        (stepArcAtom_wireListDistinct state atom fresh distinct)

/-- The canonical initial arc state's open wires (`List.range bottomCount`) are positionally
distinct — definitionally the matching seed's open-wire list, so its lemma transports. -/
theorem arcInitialState_wireListDistinct (bottomCount : Nat) :
    WireListDistinct
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []).openWires :=
  canonicalMatchingSeed_wireListDistinct bottomCount

/-- ★ **Every arc mid-state reachable from the canonical initial state has positionally
distinct open wires** — the fold invariant at the seed `arcStructureOfSpineList` folds from. -/
theorem processArcSpine_fromInitial_wireListDistinct {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (atoms : List (SpineAtom signature sourceMode targetMode)) :
    WireListDistinct
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        atoms).openWires :=
  processArcSpine_wireListDistinct atoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
    (arcStateFresh_initial bottomCount)
    (arcInitialState_wireListDistinct bottomCount)

/-! ## Honesty marker -/

/-- **Honesty marker — the ARC-fold open-wire distinctness invariant is SHIPPED.**  Positional
(`getAt`-based) distinctness is preserved by every arc step unconditionally in the position,
folds through whole spines threading only `ArcStateFresh`, and holds at every mid-state
reachable from the canonical initial arc state.  This is the consumption-safety prerequisite
for the head-location scan (equal wire values pin equal positions) — NOT yet shipped: the
untouched-adjacent-pair invariant and the scan itself.  `= true`. -/
def fxMode_hasArcWireDistinctness : Bool := true

end FX1Poly.Polygraph
