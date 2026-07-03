import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRelativeDynamics
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWireDistinct

/-! # MatchingRelativeZone — the mid-state wire map is a zone-disciplined injection (MODE3-D)

The mid-state wire map `sigma := relativeWireMap midState.openWires midState.nextFresh` splits
`Nat` into two zones — PORT identifiers (below the wire count, reading the wire list
positionally) and FRESH identifiers (at or above it, shifting into the fresh block) — and this
file packages the discipline the vcompRight gluing equivariance runs on:

* `relativeWireMap_portImageBelow` — port images land strictly below the fresh base (the
  positional read is a member of the wire list, and every wire is below the base);
* `relativeWireMap_freshImageAtOrAbove` — fresh images land at or above the fresh base
  (subtraction-free `Nat.le.dest` decomposition through `relativeWireMap_shiftsAbove`);
* ★ `relativeWireMap_isInjective` — the map is injective: port/port collisions contradict the
  open-wire distinctness invariant, fresh/fresh collisions cancel to equal offsets, and mixed
  collisions are separated by the base;
* `RelativeWireZoneDiscipline` + its builders — the three facts bundled, instantiated at any
  fresh+distinct state and, via the provenance package, at every composite mid-state
  `processSpine (canonicalMatchingSeed bottomCount) alphaAtoms` with a positive boundary.

This is exactly the hypothesis bundle the canonical-side equivariance lemmas (the component
view under a fresh rename, the loop-count congruence over renamed join events) consume in the
interface-gluing legs.  Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private kit (hand-rolled; the core cancellation lemmas leak `propext`) -/

/-- An in-range positional read is a member (private copy — the distinctness file's kit is
file-private). -/
private theorem natListGetAt_mem_inRange : (wires : List Nat) → (index : Nat) →
    index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (natListGetAt_mem_inRange rest index (Nat.lt_of_succ_lt_succ indexInRange))

private theorem natAddRightCancel : (added : Nat) → {leftSide rightSide : Nat} →
    leftSide + added = rightSide + added → leftSide = rightSide
  | 0, _, _, sumsEqual => sumsEqual
  | added + 1, _, _, sumsEqual => natAddRightCancel added (Nat.succ.inj sumsEqual)

private theorem natAddLeftCancel (base : Nat) {leftSide rightSide : Nat}
    (sumsEqual : base + leftSide = base + rightSide) : leftSide = rightSide := by
  rw [Nat.add_comm base leftSide, Nat.add_comm base rightSide] at sumsEqual
  exact natAddRightCancel base sumsEqual

/-! ## The zone bounds -/

/-- A PORT identifier's image lands strictly below the fresh base: the map reads the wire list
positionally, the read is a member, and every wire is below the base.  (Membership replaces the
`0 < freshBase` default threading — no positivity hypothesis needed.) -/
theorem relativeWireMap_portImageBelow (wires : List Nat) (freshBase index : Nat)
    (indexInRange : index < wires.length)
    (wiresBelowBase : ∀ wire ∈ wires, wire < freshBase) :
    relativeWireMap wires freshBase index < freshBase := by
  rw [relativeWireMap_readsBelow wires freshBase index indexInRange]
  exact wiresBelowBase _ (natListGetAt_mem_inRange wires index indexInRange)

/-- A FRESH identifier's image lands at or above the fresh base: decompose the identifier as
`count + offset` (subtraction-free) and the map shifts it to `freshBase + offset`. -/
theorem relativeWireMap_freshImageAtOrAbove (wires : List Nat) (freshBase identifier : Nat)
    (atOrPastCount : wires.length ≤ identifier) :
    freshBase ≤ relativeWireMap wires freshBase identifier := by
  obtain ⟨offset, offsetEq⟩ := Nat.le.dest atOrPastCount
  rw [← offsetEq, relativeWireMap_shiftsAbove wires freshBase offset]
  exact Nat.le_add_right freshBase offset

/-! ## Injectivity -/

/-- ★ **The mid-state wire map is injective** (given distinct wires below the base): port/port
collisions read two positions of a positionally distinct list, fresh/fresh collisions cancel
the base to equal offsets, and mixed collisions would put one value both below and at-or-above
the base. -/
theorem relativeWireMap_isInjective (wires : List Nat) (freshBase : Nat)
    (wiresDistinct : WireListDistinct wires)
    (wiresBelowBase : ∀ wire ∈ wires, wire < freshBase) :
    ∀ identifierOne identifierTwo : Nat,
      relativeWireMap wires freshBase identifierOne
        = relativeWireMap wires freshBase identifierTwo →
      identifierOne = identifierTwo := by
  intro identifierOne identifierTwo imagesEqual
  cases Nat.lt_or_ge identifierOne wires.length with
  | inl oneBelow =>
      cases Nat.lt_or_ge identifierTwo wires.length with
      | inl twoBelow =>
          have readsEqual : natListGetAt wires identifierOne
              = natListGetAt wires identifierTwo := by
            rw [← relativeWireMap_readsBelow wires freshBase identifierOne oneBelow,
              ← relativeWireMap_readsBelow wires freshBase identifierTwo twoBelow]
            exact imagesEqual
          cases Nat.lt_or_ge identifierOne identifierTwo with
          | inl oneLtTwo =>
              exact absurd readsEqual (wiresDistinct identifierOne identifierTwo oneLtTwo twoBelow)
          | inr twoLeOne =>
              cases Nat.lt_or_ge identifierTwo identifierOne with
              | inl twoLtOne =>
                  exact absurd readsEqual.symm
                    (wiresDistinct identifierTwo identifierOne twoLtOne oneBelow)
              | inr oneLeTwo => exact Nat.le_antisymm oneLeTwo twoLeOne
      | inr twoAtOrPast =>
          have oneImageBelow : relativeWireMap wires freshBase identifierOne < freshBase :=
            relativeWireMap_portImageBelow wires freshBase identifierOne oneBelow wiresBelowBase
          have oneImageAtOrAbove : freshBase ≤ relativeWireMap wires freshBase identifierOne := by
            rw [imagesEqual]
            exact relativeWireMap_freshImageAtOrAbove wires freshBase identifierTwo twoAtOrPast
          exact absurd (Nat.lt_of_lt_of_le oneImageBelow oneImageAtOrAbove) (Nat.lt_irrefl _)
  | inr oneAtOrPast =>
      cases Nat.lt_or_ge identifierTwo wires.length with
      | inl twoBelow =>
          have twoImageBelow : relativeWireMap wires freshBase identifierTwo < freshBase :=
            relativeWireMap_portImageBelow wires freshBase identifierTwo twoBelow wiresBelowBase
          have twoImageAtOrAbove : freshBase ≤ relativeWireMap wires freshBase identifierTwo := by
            rw [← imagesEqual]
            exact relativeWireMap_freshImageAtOrAbove wires freshBase identifierOne oneAtOrPast
          exact absurd (Nat.lt_of_lt_of_le twoImageBelow twoImageAtOrAbove) (Nat.lt_irrefl _)
      | inr twoAtOrPast =>
          obtain ⟨oneOffset, oneOffsetEq⟩ := Nat.le.dest oneAtOrPast
          obtain ⟨twoOffset, twoOffsetEq⟩ := Nat.le.dest twoAtOrPast
          have imagesForm : freshBase + oneOffset = freshBase + twoOffset := by
            rw [← relativeWireMap_shiftsAbove wires freshBase oneOffset,
              ← relativeWireMap_shiftsAbove wires freshBase twoOffset,
              oneOffsetEq, twoOffsetEq]
            exact imagesEqual
          rw [← oneOffsetEq, ← twoOffsetEq, natAddLeftCancel freshBase imagesForm]

/-! ## The bundle -/

/-- The **zone discipline** of a mid-state wire map: port images below the fresh base, fresh
images at or above it, and injectivity — the exact hypothesis bundle the canonical-side
equivariance lemmas consume. -/
structure RelativeWireZoneDiscipline (wires : List Nat) (freshBase : Nat) : Prop where
  /-- Port identifiers (below the wire count) map strictly below the fresh base. -/
  portImageBelow : ∀ index : Nat, index < wires.length →
    relativeWireMap wires freshBase index < freshBase
  /-- Fresh identifiers (at or above the wire count) map at or above the fresh base. -/
  freshImageAtOrAbove : ∀ identifier : Nat, wires.length ≤ identifier →
    freshBase ≤ relativeWireMap wires freshBase identifier
  /-- The map never collides. -/
  isInjective : ∀ identifierOne identifierTwo : Nat,
    relativeWireMap wires freshBase identifierOne
      = relativeWireMap wires freshBase identifierTwo →
    identifierOne = identifierTwo

/-- The discipline holds whenever the wires are positionally distinct and bounded by the
base. -/
theorem relativeWireZoneDiscipline_ofFreshDistinct (wires : List Nat) (freshBase : Nat)
    (wiresDistinct : WireListDistinct wires)
    (wiresBelowBase : ∀ wire ∈ wires, wire < freshBase) :
    RelativeWireZoneDiscipline wires freshBase :=
  { portImageBelow := fun index indexInRange =>
      relativeWireMap_portImageBelow wires freshBase index indexInRange wiresBelowBase
    freshImageAtOrAbove := fun identifier atOrPastCount =>
      relativeWireMap_freshImageAtOrAbove wires freshBase identifier atOrPastCount
    isInjective := relativeWireMap_isInjective wires freshBase wiresDistinct wiresBelowBase }

/-- The discipline at a fresh state with distinct wires — the `WireState`-level form. -/
theorem relativeWireZoneDiscipline_ofState (state : WireState)
    (fresh : WireStateFresh state) (distinct : WireListDistinct state.openWires) :
    RelativeWireZoneDiscipline state.openWires state.nextFresh :=
  relativeWireZoneDiscipline_ofFreshDistinct state.openWires state.nextFresh distinct fresh.1

/-- ★ **Every composite mid-state's wire map is a zone-disciplined injection** — the
provenance package (freshness + distinctness from a positive-boundary canonical seed)
discharges both hypotheses. -/
theorem relativeWireZoneDiscipline_ofMidState {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (bottomPos : 0 < bottomCount)
    (alphaAtoms : List (SpineAtom signature sourceMode targetMode)) :
    RelativeWireZoneDiscipline
      (processSpine (canonicalMatchingSeed bottomCount) alphaAtoms).openWires
      (processSpine (canonicalMatchingSeed bottomCount) alphaAtoms).nextFresh :=
  relativeWireZoneDiscipline_ofState (processSpine (canonicalMatchingSeed bottomCount) alphaAtoms)
    (processSpine_fromSeed_wireStateFresh bottomCount bottomPos alphaAtoms)
    (processSpine_fromSeed_wireListDistinct bottomCount bottomPos alphaAtoms)

/-! ## Honesty marker -/

/-- **Honesty marker — the mid-state wire map's zone discipline is SHIPPED.**  Port images
below the fresh base, fresh images at or above it, injectivity from the distinctness
invariant, bundled and instantiated at every composite mid-state with a positive boundary.
NOT yet shipped: the gluing legs themselves — the component-view and loop-count equivariance
over the mid-state links that consume this bundle.  `= true`. -/
def fxMode_hasRelativeWireZoneDiscipline : Bool := true

end FX1Poly.Polygraph
