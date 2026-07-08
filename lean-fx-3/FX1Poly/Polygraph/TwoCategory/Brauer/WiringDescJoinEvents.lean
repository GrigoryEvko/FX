import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDesc
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEvents

/-! # KEYSTONE3 — the generic `stepWiring` engine reifies its links / loops as a join-event fold

The adjunction route expresses a cell's union-find links as an unconditional event fold
(`runMatchingCell_links_eq_applyJoinEvents`), which is what lets the shipped block-exchange
lemmas (`applyJoinEvents_append`, `componentView_applyJoinEvents_append_comm`,
`countJoinEventLoops_append_comm`) drive the cross-order `componentComm` / `loopsEq`.  The generic
`stepWiring` engine (`Brauer/WiringDesc.lean`, crossing included) had NO such reification — its arc
fold `stepWiringArcs` threads a loop accumulator and CONDITIONALLY skips the join when the two
endpoints are already connected, so on its face it is not an `applyJoinEvents`.

The bridge is one structural fact about the union-find primitive: `unionFindJoin links a b` is a
NO-OP exactly when `a`, `b` already share a root (its definition is
`if firstRoot == secondRoot then links else …`).  So the conditional skip in `stepWiringArcs` and
the unconditional `unionFindJoin` in `applyJoinEvents` AGREE on the resulting link list — the skip
only avoids a join that would have been a no-op anyway — and the loops the skip counts are exactly
the `countJoinEventLoops` increments of the decoded trace.

This file ships:

  * ★ `wiringArcEvents` — the decoded join-event trace of a generator's arcs: each arc's two
    endpoint tags decoded to wire nodes through the FIXED input / output node lists.
  * ★ `stepWiringArcs_fst_eq_applyJoinEvents` — the generic arc fold's LINK output IS the
    unconditional event fold of its decoded trace (the no-op bridge, structural on the arcs).
  * ★ `stepWiringArcs_snd_eq_countJoinEventLoops` — its LOOP output is the accumulator plus the
    trace's `countJoinEventLoops` (multiplicity-faithful).
  * ★ `stepWiring_links_eq_applyJoinEvents` / `stepWiring_loops_eq` — the one-step corollaries at
    the `WireState` level: the generic engine's links / loops as a join-event fold over the
    incoming state, ready to feed the shipped block-exchange machinery for the cross-order
    disjoint-window witness.

Raw Lean 4 + Init; reuses the shipped `WireState` / union-find primitives verbatim.  Structural
recursion, no `omega` / `simp`-AC / `native_decide`.  Per-declaration `#assert_no_axioms` in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The union-find no-op bridge -/

/-- `unionFindJoin` is a NO-OP on already-connected nodes: when the two roots agree the definition
returns the link list unchanged.  The bridge between `stepWiringArcs`' conditional skip and
`applyJoinEvents`' unconditional join. -/
theorem unionFindJoin_of_isSameComponent (links : List (Nat × Nat)) (firstNode secondNode : Nat)
    (connected : isSameComponent links firstNode secondNode = true) :
    unionFindJoin links firstNode secondNode = links := by
  show (if (unionFindRootOf links firstNode == unionFindRootOf links secondNode) = true then links
      else (unionFindRootOf links firstNode, unionFindRootOf links secondNode) :: links) = links
  exact if_pos connected

/-! ## The decoded join-event trace of a generator's arcs -/

/-- ★ **The decoded join-event trace of a generator's arcs.**  Each arc `(firstTag, secondTag)` is
decoded to the wire node pair `(wiringEndpointNode … firstTag, wiringEndpointNode … secondTag)`
through the FIXED input / output node lists — the trace the arc fold plays into the union-find. -/
def wiringArcEvents (inputNodes outputNodes : List Nat) (inputCount : Nat) :
    List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | (firstTag, secondTag) :: rest =>
      (wiringEndpointNode inputNodes outputNodes inputCount firstTag,
        wiringEndpointNode inputNodes outputNodes inputCount secondTag)
        :: wiringArcEvents inputNodes outputNodes inputCount rest

/-! ## The reification: links = event fold, loops = accumulator + count -/

/-- ★ **The generic arc fold's LINK output is the unconditional event fold of its decoded trace.**
Structural on the arcs: the join branch matches `applyJoinEvents` on the nose; the loop branch
(already connected) leaves `links` untouched and `applyJoinEvents` would `unionFindJoin` the same
pair — a no-op by `unionFindJoin_of_isSameComponent` — so both sides agree.  The loop accumulator is
irrelevant to the link output, so this holds for ANY accumulator. -/
theorem stepWiringArcs_fst_eq_applyJoinEvents (inputNodes outputNodes : List Nat) (inputCount : Nat) :
    (arcs : List (Nat × Nat)) → (loopsAcc : Nat) → (links : List (Nat × Nat)) →
    (stepWiringArcs inputNodes outputNodes inputCount arcs loopsAcc links).fst
      = applyJoinEvents (wiringArcEvents inputNodes outputNodes inputCount arcs) links
  | [], _, _ => rfl
  | (firstTag, secondTag) :: rest, loopsAcc, links => by
      dsimp only [stepWiringArcs]
      cases hcomp : isSameComponent links
          (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
          (wiringEndpointNode inputNodes outputNodes inputCount secondTag) with
      | true =>
          show (stepWiringArcs inputNodes outputNodes inputCount rest (loopsAcc + 1) links).fst
            = applyJoinEvents (wiringArcEvents inputNodes outputNodes inputCount
                ((firstTag, secondTag) :: rest)) links
          rw [stepWiringArcs_fst_eq_applyJoinEvents inputNodes outputNodes inputCount rest
            (loopsAcc + 1) links]
          show applyJoinEvents (wiringArcEvents inputNodes outputNodes inputCount rest) links
            = applyJoinEvents (wiringArcEvents inputNodes outputNodes inputCount rest)
                (unionFindJoin links
                  (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
                  (wiringEndpointNode inputNodes outputNodes inputCount secondTag))
          rw [unionFindJoin_of_isSameComponent links _ _ hcomp]
      | false =>
          show (stepWiringArcs inputNodes outputNodes inputCount rest loopsAcc
                (unionFindJoin links
                  (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
                  (wiringEndpointNode inputNodes outputNodes inputCount secondTag))).fst
            = applyJoinEvents (wiringArcEvents inputNodes outputNodes inputCount
                ((firstTag, secondTag) :: rest)) links
          exact stepWiringArcs_fst_eq_applyJoinEvents inputNodes outputNodes inputCount rest loopsAcc
            (unionFindJoin links
              (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
              (wiringEndpointNode inputNodes outputNodes inputCount secondTag))

/-- ★ **The generic arc fold's LOOP output is the accumulator plus the decoded trace's loop count.**
Structural on the arcs: each already-connected arc contributes exactly one to both the accumulator
(`loopsAcc + 1`) and to `countJoinEventLoops` (`(isSameComponent …).toNat = 1`); each fresh join
contributes zero to both and advances the same `unionFindJoin` link list (the skip's no-op keeping
the two folds in lock-step). -/
theorem stepWiringArcs_snd_eq_countJoinEventLoops (inputNodes outputNodes : List Nat)
    (inputCount : Nat) :
    (arcs : List (Nat × Nat)) → (loopsAcc : Nat) → (links : List (Nat × Nat)) →
    (stepWiringArcs inputNodes outputNodes inputCount arcs loopsAcc links).snd
      = loopsAcc + countJoinEventLoops (wiringArcEvents inputNodes outputNodes inputCount arcs) links
  | [], loopsAcc, links => by
      show loopsAcc = loopsAcc + 0
      rw [Nat.add_zero]
  | (firstTag, secondTag) :: rest, loopsAcc, links => by
      dsimp only [stepWiringArcs]
      cases hcomp : isSameComponent links
          (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
          (wiringEndpointNode inputNodes outputNodes inputCount secondTag) with
      | true =>
          show (stepWiringArcs inputNodes outputNodes inputCount rest (loopsAcc + 1) links).snd
            = loopsAcc + countJoinEventLoops (wiringArcEvents inputNodes outputNodes inputCount
                ((firstTag, secondTag) :: rest)) links
          rw [stepWiringArcs_snd_eq_countJoinEventLoops inputNodes outputNodes inputCount rest
            (loopsAcc + 1) links]
          show loopsAcc + 1
              + countJoinEventLoops (wiringArcEvents inputNodes outputNodes inputCount rest) links
            = loopsAcc + ((isSameComponent links
                  (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
                  (wiringEndpointNode inputNodes outputNodes inputCount secondTag)).toNat
                + countJoinEventLoops (wiringArcEvents inputNodes outputNodes inputCount rest)
                    (unionFindJoin links
                      (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
                      (wiringEndpointNode inputNodes outputNodes inputCount secondTag)))
          rw [hcomp, unionFindJoin_of_isSameComponent links _ _ hcomp]
          show loopsAcc + 1
              + countJoinEventLoops (wiringArcEvents inputNodes outputNodes inputCount rest) links
            = loopsAcc + (1
                + countJoinEventLoops (wiringArcEvents inputNodes outputNodes inputCount rest) links)
          rw [Nat.add_assoc]
      | false =>
          show (stepWiringArcs inputNodes outputNodes inputCount rest loopsAcc
                (unionFindJoin links
                  (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
                  (wiringEndpointNode inputNodes outputNodes inputCount secondTag))).snd
            = loopsAcc + countJoinEventLoops (wiringArcEvents inputNodes outputNodes inputCount
                ((firstTag, secondTag) :: rest)) links
          rw [stepWiringArcs_snd_eq_countJoinEventLoops inputNodes outputNodes inputCount rest loopsAcc
            (unionFindJoin links
              (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
              (wiringEndpointNode inputNodes outputNodes inputCount secondTag))]
          show loopsAcc
              + countJoinEventLoops (wiringArcEvents inputNodes outputNodes inputCount rest)
                  (unionFindJoin links
                    (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
                    (wiringEndpointNode inputNodes outputNodes inputCount secondTag))
            = loopsAcc + ((isSameComponent links
                  (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
                  (wiringEndpointNode inputNodes outputNodes inputCount secondTag)).toNat
                + countJoinEventLoops (wiringArcEvents inputNodes outputNodes inputCount rest)
                    (unionFindJoin links
                      (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
                      (wiringEndpointNode inputNodes outputNodes inputCount secondTag)))
          rw [hcomp]
          show loopsAcc
              + countJoinEventLoops (wiringArcEvents inputNodes outputNodes inputCount rest)
                  (unionFindJoin links
                    (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
                    (wiringEndpointNode inputNodes outputNodes inputCount secondTag))
            = loopsAcc + (0
                + countJoinEventLoops (wiringArcEvents inputNodes outputNodes inputCount rest)
                    (unionFindJoin links
                      (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
                      (wiringEndpointNode inputNodes outputNodes inputCount secondTag)))
          rw [Nat.zero_add]

/-! ## One-step corollaries at the `WireState` level -/

/-- The FIXED input node list a generator reads at a live position. -/
def stepWiringInputNodes (state : WireState) (position : Nat) (desc : WiringDesc) : List Nat :=
  natListSliceAt state.openWires position desc.inputCount

/-- The FIXED fresh output node block a generator allocates. -/
def stepWiringOutputNodes (state : WireState) (desc : WiringDesc) : List Nat :=
  (List.range desc.outputCount).map (· + state.nextFresh)

/-- ★ **One `stepWiring` step's LINKS are the event fold of the generator's decoded arc trace over
the incoming links.**  The generic-engine analog of `runMatchingCell_links_eq_applyJoinEvents`:
`stepWiring`'s link field IS `stepWiringArcs … .fst`, reified by
`stepWiringArcs_fst_eq_applyJoinEvents`. -/
theorem stepWiring_links_eq_applyJoinEvents (state : WireState) (position : Nat) (desc : WiringDesc) :
    (stepWiring state position desc).links
      = applyJoinEvents
          (wiringArcEvents (stepWiringInputNodes state position desc)
            (stepWiringOutputNodes state desc) desc.inputCount desc.arcs)
          state.links :=
  stepWiringArcs_fst_eq_applyJoinEvents (stepWiringInputNodes state position desc)
    (stepWiringOutputNodes state desc) desc.inputCount desc.arcs 0 state.links

/-- ★ **One `stepWiring` step's LOOP count is the incoming loops plus the decoded trace's
`countJoinEventLoops` plus the generator's internal loops.**  `stepWiring`'s loop field is
`state.loops + foldResult.snd + desc.internalLoops`, and `foldResult.snd` reifies (from accumulator
`0`) to `countJoinEventLoops` of the decoded trace. -/
theorem stepWiring_loops_eq (state : WireState) (position : Nat) (desc : WiringDesc) :
    (stepWiring state position desc).loops
      = state.loops
        + countJoinEventLoops
            (wiringArcEvents (stepWiringInputNodes state position desc)
              (stepWiringOutputNodes state desc) desc.inputCount desc.arcs)
            state.links
        + desc.internalLoops := by
  show state.loops
      + (stepWiringArcs (stepWiringInputNodes state position desc)
          (stepWiringOutputNodes state desc) desc.inputCount desc.arcs 0 state.links).snd
      + desc.internalLoops
    = state.loops
      + countJoinEventLoops
          (wiringArcEvents (stepWiringInputNodes state position desc)
            (stepWiringOutputNodes state desc) desc.inputCount desc.arcs)
          state.links
      + desc.internalLoops
  rw [stepWiringArcs_snd_eq_countJoinEventLoops (stepWiringInputNodes state position desc)
      (stepWiringOutputNodes state desc) desc.inputCount desc.arcs 0 state.links, Nat.zero_add]

/-! ## Honesty marker -/

/-- **Honesty marker — the generic `stepWiring` engine reifies its links / loops as a join-event
fold.**  `stepWiring_links_eq_applyJoinEvents` / `stepWiring_loops_eq` express the union-find link
list and the loop count of ANY generator firing (crossing included) as an unconditional
`applyJoinEvents` / `countJoinEventLoops` of the decoded arc trace `wiringArcEvents`, bridged by the
`unionFindJoin` no-op on already-connected nodes (`unionFindJoin_of_isSameComponent`).  This is the
generic-engine analog of the adjunction route's `runMatchingCell_links_eq_applyJoinEvents` — the
missing hook that lets the shipped block-exchange lemmas
(`componentView_applyJoinEvents_append_comm`, `countJoinEventLoops_append_comm`) drive the
cross-order disjoint-window `componentComm` / `loopsEq`.  `= true`. -/
def fxBrauer_hasWiringDescJoinEventReification : Bool := true

end FX1Poly.Polygraph
