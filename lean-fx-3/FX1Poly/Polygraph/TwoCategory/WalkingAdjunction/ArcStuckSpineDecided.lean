import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcStuckSpineSwapConnected

/-! # ArcStuckSpineDecided — RUNNING the two-directional decider on the STUCK residual (isTrue)

`ArcStuckSpineSwapConnected` proved `spineTraceEquiv_doubleSnake_nestedSnake` from ONE direction only —
membership in the saturated class plus `saturateClass_isSound` (the UNCONDITIONAL soundness half).  That
certifies the double and nested stuck snakes ARE trace-equivalent, but it does not run the actual DECISION
procedure `decideAtomicTraceEquivViaSaturation` (`ClassSaturation`, FREE-6c): the gated two-directional decider
that, given the computable frontier-exhaustion witness, returns `isTrue`/`isFalse` for `AtomicTraceEquiv` using
soundness on the accept side AND completeness on the reject side.

This file RUNS that decider on the two `ArcStuckSpineNonSingleton` witnesses and records the verdict.

  * ★ `stuckSnakes_didExhaustFrontier` — the computable exhaustion gate: the double snake's swap saturation
    empties its frontier within `fuel = 8` (`didExhaustFrontier ... = true`, kernel `decide`).  This is the
    completeness precondition the decider consumes; with it in hand the `isFalse` branch is a genuine refutation
    (nothing swap-reachable is missed), so the decision is TWO-directional, not just accept-if-member.
  * ★ `decideAtomicTraceEquivStuck` — the decider TERM: `decideAtomicTraceEquivViaSaturation` applied to the
    double snake (seed) and the nested snake (target) at `fuel = 8`, discharged by the exhaustion gate.
  * ★ `decideAtomicTraceEquivStuck_isAccepting` — the VERDICT: the decision procedure returns `isTrue` (kernel
    `decide` on `isAcceptingDecision`, the structural accept/reject reader).  So the machine, running the full
    two-directional decider, DECIDES the two stuck spines ARE `AtomicTraceEquiv`.
  * ★ `atomicTraceEquiv_doubleSnake_nestedSnake_byDecider` — the `AtomicTraceEquiv` proof extracted straight
    from the decider (`isTrue` branch), the atom-granularity companion of the shipped block-level
    `spineTraceEquiv_doubleSnake_nestedSnake`.

## The verdict for flag-B: isTrue, NO falsification

The decision is `isTrue`.  The two DISTINCT arc-equal four-atom stuck spines — the DOUBLE snake
`[cup@0, cap@1, cup@0, cap@1]` and the NESTED snake `[cup@0, cup@2, cap@3, cap@1]` — ARE related by the
swaps-only interchange closure.  So on the hardest known instance of the reconstruction the arc structure is a
sound-AND-complete trace invariant, and the "sequential vs nested arches" content is a genuine finite swap chain
(a five-element Temperley-Lieb ~-class), NOT a counterexample.

This is decisive for how flag-B is walled.  It is NOT a wall-by-falsification (unlike SAT-CONF's refuted local
confluence or SAT-NF's refuted whiskered-snake normal form): the machine says the witnesses ARE equivalent, so
there is no honest counterexample to `arcCupReselection_exists` here — a falsification would be a fabrication.
`fxMode_hasArcStructureReconstruction` stays `false` for a DIFFERENT, honest reason: the GENERAL completeness gap
(arc-equal parallel spines ⟹ swap-connected, over ALL realizable cup/cap configs) remains open, and the
peel-DECOMPOSITION strategy is separately refuted (`ArcStuckHeadLeftCancel`: the shared-head tails are NOT
`AtomicTraceEquiv`, so the spine atoms are a DYNAMIC trace, not a static Mazurkiewicz monoid, and "peel shared
head, recurse on tails" is dead).  The single hardest witness is confirmed swap-connected; the general theorem is
not.

Raw Lean 4 + Init; the exhaustion gate and the accept verdict close by kernel `decide` on the fuel-bounded BFS
saturation, the extracted proof by matching the decider's `isTrue`.  Per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

open AdjunctionMode AdjunctionModality

/-! ## The computable exhaustion gate -/

set_option maxHeartbeats 4000000 in
/-- ★ **The double snake's swap saturation EXHAUSTS its frontier at `fuel = 8`** — the computable completeness
precondition of the two-directional decider.  A kernel `decide` mirroring the BFS worker step for step: after the
five-element class is discovered the frontier empties, so nothing swap-reachable is missed and the decider's
`isFalse` branch becomes a genuine refutation. -/
theorem stuckSnakes_didExhaustFrontier :
    didExhaustFrontier adjunctionModeDecEq adjunctionModalityDecEq adjunctionTwoCellDecEq 8
      [doubleSnakeOnLeft.spine] [doubleSnakeOnLeft.spine] = true := by
  decide

/-! ## Running the decider -/

/-- Read a decision's accept/reject bit — the structural accept-branch reader used to certify that the decision
procedure returned `isTrue` (propext-free: a bare `casesOn` on the `Decidable`). -/
def isAcceptingDecision {statement : Prop} : Decidable statement → Bool
  | Decidable.isTrue _ => true
  | Decidable.isFalse _ => false

/-- ★ **The decider TERM.**  The gated two-directional `AtomicTraceEquiv` decider
(`decideAtomicTraceEquivViaSaturation`, FREE-6c) applied to the double snake (seed) and the nested snake
(target) at `fuel = 8`, discharged by `stuckSnakes_didExhaustFrontier`.  Evaluating this term IS running the
machine decision. -/
def decideAtomicTraceEquivStuck :
    Decidable (AtomicTraceEquiv adjunctionModeSignature doubleSnakeOnLeft.spine nestedSnakeOnLeft.spine) :=
  decideAtomicTraceEquivViaSaturation adjunctionModeDecEq adjunctionModalityDecEq adjunctionTwoCellDecEq 8
    doubleSnakeOnLeft.spine nestedSnakeOnLeft.spine stuckSnakes_didExhaustFrontier

set_option maxHeartbeats 4000000 in
/-- ★ **THE VERDICT — the two-directional decider returns `isTrue`.**  Running the full FREE-6c decision on the
two `ArcStuckSpineNonSingleton` witnesses ACCEPTS: `isAcceptingDecision decideAtomicTraceEquivStuck = true`
(kernel `decide` on the fuel-bounded saturation membership).  So the machine, with the exhaustion gate in hand
(making the reject branch a genuine refutation), DECIDES the double and nested stuck snakes ARE `AtomicTraceEquiv`
— NOT a falsification.  This is the decisive computation flag-B round 11 turns on. -/
theorem decideAtomicTraceEquivStuck_isAccepting : isAcceptingDecision decideAtomicTraceEquivStuck = true := by
  decide

/-- ★ **The `AtomicTraceEquiv` proof, extracted straight from the decider.**  The atom-granularity companion of
the block-level `spineTraceEquiv_doubleSnake_nestedSnake`: read the proof off the decider's `isTrue`; the
`isFalse` branch is impossible and is discharged by the shipped soundness witness
(`saturateClass_isSound nestedSnake_spine_mem_doubleSnakeSwapClass`). -/
theorem atomicTraceEquiv_doubleSnake_nestedSnake_byDecider :
    AtomicTraceEquiv adjunctionModeSignature doubleSnakeOnLeft.spine nestedSnakeOnLeft.spine :=
  match decideAtomicTraceEquivStuck with
  | Decidable.isTrue equiv => equiv
  | Decidable.isFalse notEquiv =>
      absurd
        (saturateClass_isSound adjunctionModeDecEq adjunctionModalityDecEq adjunctionTwoCellDecEq
          nestedSnake_spine_mem_doubleSnakeSwapClass)
        notEquiv

/-! ## Honesty marker -/

/-- **Honesty marker — the two-directional decider DECIDES the stuck residual `isTrue` (no falsification).**
`decideAtomicTraceEquivStuck_isAccepting` runs the full gated FREE-6c decision procedure
(`decideAtomicTraceEquivViaSaturation`, with the computable exhaustion gate `stuckSnakes_didExhaustFrontier`
making the reject branch a genuine refutation) on the two `ArcStuckSpineNonSingleton` witnesses and it returns
`isTrue`; `atomicTraceEquiv_doubleSnake_nestedSnake_byDecider` reads the `AtomicTraceEquiv` proof out of the
decider.  Verdict: the double and nested stuck snakes ARE interchange-equivalent, so flag-B is NOT walled by
falsification — there is no honest counterexample to `arcCupReselection_exists` on the hardest known instance, and
fabricating one would be dishonest.

What this marker does NOT claim: any flip.  `fxMode_hasArcStructureReconstruction` stays `false` on its own honest
grounds — the GENERAL completeness (arc-equal parallel spines ⟹ swap-connected over ALL realizable cup/cap
configs) is open, and the peel-DECOMPOSITION is separately refuted (`ArcStuckHeadLeftCancel`: shared-head tails
NOT `AtomicTraceEquiv` ⟹ dynamic, not static Mazurkiewicz, trace).  Single hardest witness confirmed
swap-connected; general theorem unproved.  `= true`. -/
def fxMode_hasArcStuckSpineDecidedTrue : Bool := true

end FX1Poly.Polygraph
