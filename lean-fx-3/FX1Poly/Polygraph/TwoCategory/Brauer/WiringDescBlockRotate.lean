import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescComponentSim
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescJoinEvents
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.BlockRotation

/-! # KEYSTONE4 leg 1 — `wiringArcEvents` is `blockRotate`-equivariant + the two fresh output-block images

The cross-order disjoint-window witness (`Brauer/WiringDescComponentSim.lean`) rides
`sigma = blockRotate state.nextFresh descA.outputCount descB.outputCount`.  Its `componentComm` / `loopsEq` fields
reduce (through the KEYSTONE3 reification `stepWiring_links_eq_applyJoinEvents`) to relating the two firing orders'
decoded arc traces `wiringArcEvents` under `sigma`.  This file ships the two purely-combinatorial legs of that
correspondence — the ones that need NO window geometry:

  * ★ **`wiringArcEvents_map`** — decoding a generator's arc list through `sigma`-relabeled input / output node
    lists is the pointwise `sigma`-image of the decoded trace (the fold of the shipped `wiringEndpointNode_map`
    over the arcs; needs only `sigma 0 = 0`).  This is brick B1: it reduces each block's trace correspondence to
    the correspondence of its two NODE lists.
  * ★ **`rangeMapAdd_map_blockRotate_first` / `rangeMapAdd_map_blockRotate_second`** — the two fresh output-block
    images.  A generator's fresh output block is `(List.range width).map (· + base)`.  Firing order moves the
    base counter; `blockRotate` transports the two output blocks between the two orders:
      - the FIRST block `[lo, lo+wA)` (order AB's `descA` outputs) shifts up to `[lo+wB, lo+wB+wA)` (order BA's
        `descA` outputs) — `blockRotate_firstBlock` pointwise over the range;
      - the SECOND block `[lo+wA, lo+wA+wB)` (order AB's `descB` outputs) shifts down to `[lo, lo+wB)` (order
        BA's `descB` outputs) — `blockRotate_secondBlock` pointwise, the truncated subtraction exact via the
        shipped `addSubCancelRight`.
    This is brick B2: the OUTPUT-node halves of the two block trace correspondences, discharged by pure
    arithmetic over `List.range`.

The remaining leg (the INPUT-node halves — that both orders read `blockRotate`-corresponding boundary wires) is
the window-locality geometry over `natListSliceAt`, shipped separately.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide`.  Per-declaration
`#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Brick B1 — the arc-trace decode is `sigma`-equivariant -/

/-- ★ **`wiringArcEvents` decodes `sigma`-equivariantly.**  Reading a generator's arc list through node lists that
are the `sigma`-images of the source node lists yields the pointwise `sigma`-image of the decoded trace — the fold
of the shipped `wiringEndpointNode_map` (which needs only the past-end sentinel `sigma 0 = 0`) over the arcs.
Structural on the arc list.  Reduces each block's trace correspondence to the correspondence of its two NODE
lists (input slice + fresh output block). -/
theorem wiringArcEvents_map (sigma : Nat → Nat) (sigmaFixesZero : sigma 0 = 0)
    (inputNodes outputNodes : List Nat) (inputCount : Nat) :
    (arcs : List (Nat × Nat)) →
    wiringArcEvents (inputNodes.map sigma) (outputNodes.map sigma) inputCount arcs
      = (wiringArcEvents inputNodes outputNodes inputCount arcs).map
          (fun event => (sigma event.1, sigma event.2))
  | [] => rfl
  | (firstTag, secondTag) :: rest => by
      show (wiringEndpointNode (inputNodes.map sigma) (outputNodes.map sigma) inputCount firstTag,
            wiringEndpointNode (inputNodes.map sigma) (outputNodes.map sigma) inputCount secondTag)
            :: wiringArcEvents (inputNodes.map sigma) (outputNodes.map sigma) inputCount rest
          = (sigma (wiringEndpointNode inputNodes outputNodes inputCount firstTag),
             sigma (wiringEndpointNode inputNodes outputNodes inputCount secondTag))
            :: (wiringArcEvents inputNodes outputNodes inputCount rest).map
                (fun event => (sigma event.1, sigma event.2))
      rw [wiringEndpointNode_map sigma sigmaFixesZero inputNodes outputNodes inputCount firstTag,
        wiringEndpointNode_map sigma sigmaFixesZero inputNodes outputNodes inputCount secondTag,
        wiringArcEvents_map sigma sigmaFixesZero inputNodes outputNodes inputCount rest]

/-! ## Brick B2 — the two fresh output-block images under `blockRotate` -/

/-- ★ **The FIRST block shifts up by `secondWidth`.**  Mapping `blockRotate lo firstWidth secondWidth` over the
fresh output block `indices.map (· + lo)` (with every index `< firstWidth`) shifts it up to
`indices.map (· + (lo + secondWidth))` — order AB's `descA` output range `[lo, lo+wA)` mapped to order BA's
`descA` output range `[lo+wB, lo+wB+wA)`.  Pointwise `blockRotate_firstBlock` over the index list. -/
theorem rangeMapAdd_map_blockRotate_first (lo firstWidth secondWidth : Nat) :
    (indices : List Nat) → (∀ index ∈ indices, index < firstWidth) →
    (indices.map (· + lo)).map (blockRotate lo firstWidth secondWidth)
      = indices.map (· + (lo + secondWidth))
  | [], _ => rfl
  | headIndex :: restIndices, allBelow => by
      show blockRotate lo firstWidth secondWidth (headIndex + lo)
            :: (restIndices.map (· + lo)).map (blockRotate lo firstWidth secondWidth)
          = (headIndex + (lo + secondWidth)) :: restIndices.map (· + (lo + secondWidth))
      have headBelow : headIndex < firstWidth := allBelow headIndex (List.Mem.head restIndices)
      rw [blockRotate_firstBlock lo firstWidth secondWidth (headIndex + lo)
          (Nat.le_add_left lo headIndex)
          (by rw [Nat.add_comm headIndex lo]; exact Nat.add_lt_add_left headBelow lo),
        Nat.add_assoc headIndex lo secondWidth,
        rangeMapAdd_map_blockRotate_first lo firstWidth secondWidth restIndices
          (fun index indexInRest => allBelow index (List.Mem.tail headIndex indexInRest))]

/-- ★ **The SECOND block shifts down by `firstWidth`.**  Mapping `blockRotate lo firstWidth secondWidth` over the
fresh output block `indices.map (· + (lo + firstWidth))` (with every index `< secondWidth`) shifts it down to
`indices.map (· + lo)` — order AB's `descB` output range `[lo+wA, lo+wA+wB)` mapped to order BA's `descB` output
range `[lo, lo+wB)`.  Pointwise `blockRotate_secondBlock`, the truncated subtraction exact via
`addSubCancelRight`. -/
theorem rangeMapAdd_map_blockRotate_second (lo firstWidth secondWidth : Nat) :
    (indices : List Nat) → (∀ index ∈ indices, index < secondWidth) →
    (indices.map (· + (lo + firstWidth))).map (blockRotate lo firstWidth secondWidth)
      = indices.map (· + lo)
  | [], _ => rfl
  | headIndex :: restIndices, allBelow => by
      show blockRotate lo firstWidth secondWidth (headIndex + (lo + firstWidth))
            :: (restIndices.map (· + (lo + firstWidth))).map (blockRotate lo firstWidth secondWidth)
          = (headIndex + lo) :: restIndices.map (· + lo)
      have headBelow : headIndex < secondWidth := allBelow headIndex (List.Mem.head restIndices)
      have atOrAboveFirst : lo + firstWidth ≤ headIndex + (lo + firstWidth) :=
        Nat.le_add_left (lo + firstWidth) headIndex
      have belowWindowTop : headIndex + (lo + firstWidth) < lo + firstWidth + secondWidth := by
        rw [Nat.add_comm headIndex (lo + firstWidth)]
        exact Nat.add_lt_add_left headBelow (lo + firstWidth)
      rw [blockRotate_secondBlock lo firstWidth secondWidth (headIndex + (lo + firstWidth))
          atOrAboveFirst belowWindowTop,
        ← Nat.add_assoc headIndex lo firstWidth, addSubCancelRight (headIndex + lo) firstWidth,
        rangeMapAdd_map_blockRotate_second lo firstWidth secondWidth restIndices
          (fun index indexInRest => allBelow index (List.Mem.tail headIndex indexInRest))]

/-! ## Honesty marker -/

/-- **Honesty marker — the combinatorial legs of the cross-order trace correspondence are SHIPPED.**
`wiringArcEvents_map` (B1: the arc-trace decode is `sigma`-equivariant, reducing each block's trace correspondence
to its two node-list correspondences) and `rangeMapAdd_map_blockRotate_first` / `_second` (B2: the two fresh
output-block images under `blockRotate` — first block up by `wB`, second block down by `wA`).  What remains for the
cross-order trace correspondence: the INPUT-node halves (both orders read `blockRotate`-corresponding boundary
wires — the `natListSliceAt` window-locality geometry).  `= true`. -/
def fxBrauer_hasWiringArcEventsBlockRotateLegs : Bool := true

end FX1Poly.Polygraph
