import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcFreshBlockTransposition

/-! # ArcFreshSelfSimulation — a fresh-range renaming relates a state to ITSELF (ARC-2b brick iii-1c)

The singleton swap's simulation starts from the state at the swap point, which the fresh-block
transposition does not touch: every open wire, link endpoint, and event node sits strictly
below `nextFresh` (`ArcStateFresh`), and the transposition only moves identifiers at or above
it.  This brick packages that observation as the base `ArcStepSimCount sigma state state` —
the k = 0 case of the two-step core simulation, and the source of the reusable complement
atoms (an injective renaming fixing everything below `nextFresh` maps the at-or-above range
into itself; roots of fresh identifiers are themselves; per-root event counts vanish at fresh
roots) that the two-step legs cite.

The instantiation corollary plugs in `arcFreshBlockTransposition` itself, snapping the iii-1b
interface into the parked `ArcStepSimCount` scaffold end-to-end.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- An injective renaming that fixes everything below a bound maps the at-or-above range into
itself: an image below the bound would be a fixed point, forcing the preimage below the bound
by injectivity. -/
theorem sigmaAtOrAbove_of_fixesBelow (sigma : Nat → Nat)
    (inj : ∀ a b, sigma a = sigma b → a = b) (bound : Nat)
    (fixesBelow : ∀ identifier, identifier < bound → sigma identifier = identifier)
    (identifier : Nat) (isAtOrAbove : bound ≤ identifier) : bound ≤ sigma identifier := by
  cases Nat.lt_or_ge (sigma identifier) bound with
  | inl imageBelow =>
      have imageEqIdentifier : sigma identifier = identifier :=
        inj (sigma identifier) identifier (fixesBelow (sigma identifier) imageBelow)
      rw [imageEqIdentifier] at imageBelow
      exact absurd (Nat.lt_of_lt_of_le imageBelow isAtOrAbove) (Nat.lt_irrefl identifier)
  | inr imageAtOrAbove => exact imageAtOrAbove

/-- **Per-root event counts vanish at fresh roots**: when every link parent and every event
node lies strictly below the bound, no event's root can reach a root at or above it. -/
theorem countEventsInRoot_eq_zero_of_freshRoot (links : List (Nat × Nat)) (bound : Nat)
    (allParentsBelow : ∀ edge ∈ links, edge.2 < bound)
    (rootHere : Nat) (isAtOrAbove : bound ≤ rootHere) :
    (eventNodes : List Nat) → (∀ node ∈ eventNodes, node < bound) →
    countEventsInRoot links rootHere eventNodes = 0
  | [], _ => rfl
  | eventNode :: rest, allEventsBelow => by
      show (if unionFindRootOf links eventNode == rootHere then (1 : Nat) else 0)
          + countEventsInRoot links rootHere rest = 0
      have eventRootBelow : unionFindRootOf links eventNode < bound :=
        unionFindRootOf_lt_of_fresh links bound allParentsBelow eventNode
          (allEventsBelow eventNode (List.Mem.head _))
      have rootNotHere : ¬ (unionFindRootOf links eventNode == rootHere) = true :=
        fun beqTrue =>
          absurd (Nat.lt_of_lt_of_le (of_decide_eq_true beqTrue ▸ eventRootBelow) isAtOrAbove)
            (Nat.lt_irrefl rootHere)
      rw [if_neg rootNotHere, Nat.zero_add]
      exact countEventsInRoot_eq_zero_of_freshRoot links bound allParentsBelow rootHere
        isAtOrAbove rest (fun node nodeInRest => allEventsBelow node (List.Mem.tail _ nodeInRest))

/-- ★ **A fresh-range renaming relates a state to itself.**  Any injective renaming fixing
everything strictly below `nextFresh` is an `ArcStepSimCount` from a fresh forest state to
itself: the open wires are fixed pointwise, roots commute (fixed below, parentless at or
above), and per-root event counts agree (fixed roots verbatim, fresh roots both zero). -/
theorem arcStepSimCount_self_ofFixesBelow (sigma : Nat → Nat)
    (inj : ∀ a b, sigma a = sigma b → a = b)
    (state : ArcWireState) (fresh : ArcStateFresh state)
    (forest : isUnionFindForest state.links)
    (fixesBelow : ∀ identifier, identifier < state.nextFresh → sigma identifier = identifier) :
    ArcStepSimCount sigma state state where
  openMap := (mapFixedOn sigma state.openWires
    (fun wire wireInList => fixesBelow wire (fresh.1 wire wireInList))).symm
  nfEq := rfl
  rootComm := fun node => by
    cases Nat.lt_or_ge node state.nextFresh with
    | inl nodeBelow =>
        rw [fixesBelow node nodeBelow, fixesBelow (unionFindRootOf state.links node)
          (unionFindRootOf_lt_of_fresh state.links state.nextFresh
            (fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2) node nodeBelow)]
    | inr nodeAtOrAbove =>
        rw [unionFindRootOf_of_parentless state.links (sigma node)
            (unionFindParent_none_of_freshNode state fresh (sigma node)
              (sigmaAtOrAbove_of_fixesBelow sigma inj state.nextFresh fixesBelow node
                nodeAtOrAbove)),
          unionFindRootOf_of_parentless state.links node
            (unionFindParent_none_of_freshNode state fresh node nodeAtOrAbove)]
  loopsEq := rfl
  cupCorr := fun root => by
    cases Nat.lt_or_ge root state.nextFresh with
    | inl rootBelow => rw [fixesBelow root rootBelow]
    | inr rootAtOrAbove =>
        rw [countEventsInRoot_eq_zero_of_freshRoot state.links state.nextFresh
            (fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2) (sigma root)
            (sigmaAtOrAbove_of_fixesBelow sigma inj state.nextFresh fixesBelow root
              rootAtOrAbove) state.cupEventNodes fresh.2.2.1,
          countEventsInRoot_eq_zero_of_freshRoot state.links state.nextFresh
            (fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2) root rootAtOrAbove
            state.cupEventNodes fresh.2.2.1]
  capCorr := fun root => by
    cases Nat.lt_or_ge root state.nextFresh with
    | inl rootBelow => rw [fixesBelow root rootBelow]
    | inr rootAtOrAbove =>
        rw [countEventsInRoot_eq_zero_of_freshRoot state.links state.nextFresh
            (fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2) (sigma root)
            (sigmaAtOrAbove_of_fixesBelow sigma inj state.nextFresh fixesBelow root
              rootAtOrAbove) state.capEventNodes fresh.2.2.2,
          countEventsInRoot_eq_zero_of_freshRoot state.links state.nextFresh
            (fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2) root rootAtOrAbove
            state.capEventNodes fresh.2.2.2]
  forestS := forest
  forestT := forest

/-- ★ **The fresh-block transposition relates the swap-point state to itself** — the iii-1b
interface snapped into the `ArcStepSimCount` scaffold: injectivity and the below-base fixing
law instantiate the self-simulation at `baseFresh = state.nextFresh`. -/
theorem arcStepSimCount_self_transposition (widthFirst widthSecond : Nat)
    (state : ArcWireState) (fresh : ArcStateFresh state)
    (forest : isUnionFindForest state.links) :
    ArcStepSimCount (arcFreshBlockTransposition state.nextFresh widthFirst widthSecond)
      state state :=
  arcStepSimCount_self_ofFixesBelow
    (arcFreshBlockTransposition state.nextFresh widthFirst widthSecond)
    (arcFreshBlockTransposition_injective state.nextFresh widthFirst widthSecond)
    state fresh forest
    (arcFreshBlockTransposition_ofBelow state.nextFresh widthFirst widthSecond)

/-! ## Honesty marker -/

/-- **Honesty marker — the fresh self-simulation is SHIPPED (ARC-2b brick iii-1c).**  An
injective renaming fixing everything below `nextFresh` is an `ArcStepSimCount` from a fresh
forest state to itself (`arcStepSimCount_self_ofFixesBelow`), instantiated at the fresh-block
transposition (`arcStepSimCount_self_transposition`); with the reusable complement atoms
(at-or-above closure of the renaming, count vanishing at fresh roots).  NOT yet shipped: the
TWO-STEP core simulation over the realized swap pairs — the genuine Mazurkiewicz content where
the two run orders fire DIFFERENT atoms and the transposition reconciles the swapped fresh
allocations (per cup/cap arity case, consuming the iii-1a commutation kit for the wire lists
and the join lemmas for the links).  `= true`. -/
def fxMode_hasArcFreshSelfSimulation : Bool := true

end FX1Poly.Polygraph
