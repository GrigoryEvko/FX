import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.TraceReducer
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Confluence
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedConvergence

/-! # mode-3 floor — the ORIENTED single-atom Godement swap: a concrete strongly-normalizing sub-relation

`FreeTwoCellTraceReducer` refuted the SN obligation of the FULL positionwise Godement step
(`SpineGodementAtAnyPosition` is REFLEXIVE — `adjunctionGodementSelfLoopAtAnyPosition` — so no element is
`Acc`-essible) and shipped the corrected harness `adjunctionTraceDecisionViaOrientedReducer`, which decides
`SpineTraceEquiv` from a sound + complete + TERMINATING + CONFLUENT reducer for an ORIENTED sub-relation
`orientedSwap` sandwiched between the positionwise Godement step and its own equational theory.  This file
builds the first concrete such sub-relation and discharges its STRONG NORMALIZATION zero-axiom.

## The decisive choice: orient by an EXPANDING left atom (and the measure that then works)

The prior pass warned that the naive sum-of-context-lengths measure is NON-monotone (a counit transposition
LENGTHENS the moved atom's whisker context).  The resolution here is to ORIENT the swap so a simple measure
DOES decrease, rather than to chase the global source-anchored coordinate:

  * `AdjunctionOrientedSwap` is the single-atom Godement transposition (`singleAtomGodementStep` shape,
    positionwise via `under`) RESTRICTED to an **expanding left atom** — the fired left atom `genX` has
    `genDomX.length < genCodX.length` (its target 1-cell is strictly longer than its source).  At the seed
    every generator has `|genDom| ≠ |genCod|` (unit is `nil ⇒ LR`, counit is `RL ⇒ nil`), so `expanding`
    holds exactly for the UNIT-led pairs — the swap pushes a unit rightward past an independent neighbour.
  * **`adjunctionLeftContextLengthSum`** — the sum of every atom's left-whisker-context length — then STRICTLY
    DECREASES on each oriented swap: the transposition replaces left contexts `lcX`, `lcX ∘ genCodX` by
    `lcX ∘ genDomX`, `lcX`, a net change of `|genDomX| − |genCodX| < 0`.  No source-anchor trace, no global
    recomputation: the orientation makes a one-line `Nat` measure work, contradicting the non-monotone worry
    for THIS sub-relation.  `adjunctionOrientedSwapTerminating` is then fuel-bounded `Acc` descent on it (no
    `WellFounded.fix`), exactly the `twoCellStep_isStronglyNormalizing` recipe.

## What this file ships (each piece zero-axiom)

  ★ `AdjunctionOrientedSwap` — the expanding-oriented single-atom Godement transposition, positionwise.
  ★ `adjunctionOrientedSwapIsGodement` — every oriented swap IS a positionwise Godement step (the EASY sandwich
    leg `orientedIsGodement`, realized through `singleAtomGodementStep`).  CLOSED.
  ★ `adjunctionLeftContextLengthSum` + `adjunctionOrientedSwap_leftContextSum_lt` +
    `adjunctionOrientedSwapTerminating` — the **strong-normalization measure and the SN proof** (the design-lock's
    "genuine remaining content").  CLOSED.
  ★ `adjunctionOrientedSwapConfluentOfWeaklyConfluent` — reduces the harness's `confluent` obligation to LOCAL
    confluence via Newman's lemma (the SN witness is supplied).  CLOSED.
  ★ `adjunctionOrientedTheory_consCongr` — the oriented theory passes through a head atom (the `under`-recursion
    ingredient of the completeness leg).  CLOSED.
  ★ `adjunctionParallelUnits_orientedSwap` (+ measure smokes) — the canonical Eckmann–Hilton witness's redex
    spine oriented-swaps to its reduct spine, and `adjunctionLeftContextLengthSum` drops `2 → 0`.
  ★ `adjunctionTraceDecisionViaExpandingReducer` — the harness with `terminating`, `orientedIsGodement`, and
    `confluent` (via Newman) DISCHARGED, leaving a deterministic reducer (sound + complete), LOCAL confluence,
    and `godementInOrientedTheory` as the named residuals.

## What is DEFERRED — and the honest INCOMPLETENESS finding (`= false` marker)

The expanding orientation is **provably incomplete** for the trace word problem, so it does NOT by itself
inhabit `godementInOrientedTheory`:

  * `adjunctionCounitGodementStep` — a concrete CONTRACTING (counit/counit) single-atom Godement step at the
    seed.  Its left atom is a counit, so `genDomX.length = 2 > 0 = genCodX.length`
    (`adjunctionCounitGate_isContracting`): it FAILS the `expanding` gate.  A two-element list has only the head
    position, so neither this step's source nor its reduct is an `AdjunctionOrientedSwap` redex — both are
    oriented-normal yet one positionwise Godement step apart.  Hence `EquationalTheory AdjunctionOrientedSwap`
    does NOT contain this Godement step, i.e. `godementInOrientedTheory` is not merely unproven but FALSE for
    the expanding restriction.

So the SN measure here is genuine, but a COMPLETE convergent reducer cannot be a strongly-normalizing
sub-relation of the (directional) raw Godement steps alone: the contracting steps are uphill in every linear
context-length measure, and their reverses are not Godement-shaped.  The complete convergent system therefore
needs CONTEXT-RECOMPUTATION rules (the source-anchored Foata canonicalisation that rewrites an atom's
left/right whisker presentation), which sit OUTSIDE the `orientedSwap ⊆ SpineGodementAtAnyPosition` interface —
the genuine deferred core.  `fxMode_hasModeRelativeConvDecision` / `fxMode_hasDecidableTwoCellEquality` stay
`false`; the spine route flips no decision gate, only records `fxMode_hasOrientedTraceCanonicalForm := false`.

## Part II — the `RawTwoCellExpr` route: the interchange NON-CONFLUENCE, mechanized + the decision assembly

The second half attacks the SAME keystone `Decidable (SaturatedTwoCellConv c1 c2)` by the convergent-rewriting
route on `RawTwoCellExpr` (the combined triangle rewrite `SaturatedTwoCellStep` of
`FreeTwoCellSaturatedConvergence`, already SN + Newman-reduced to LOCAL confluence).  `FreeTwoCellConfluence` only
ASSERTED (prose) that this local confluence is false; here it becomes a THEOREM:

  ★ a reusable abstract non-confluence toolkit (`notConfluent_of_divergentNormalForms`,
    `notWeaklyConfluent_of_notConfluent` — Newman contrapositively, over any relation);
  ★ a minimal witness 2-polygraph (`interchangeWitnessSignature`) hosting the Godement square, whose peak reduces
    to two DISTINCT interchange-normal forms — proving `interchangeWitness_notLocallyConfluent`
    (`¬ TwoCellLocallyConfluent`).  This is the rigorous "which interchange critical pairs join vs not": the
    triangle-layer pairs JOIN (`FreeTwoCellSaturatedConvergence`), the `interchange × whiskerRightVcomp` pair does
    NOT;
  ★ the saturated DECISION assembled modulo a rewriting normal form
    (`adjunctionDecideSaturatedConvViaRewriteNormalForm`) with the YES-direction discharged
    (`saturatedConv_of_joinable`), leaving only `complete` (a confluent normalizer) residual —
    `fxMode_hasSaturatedRewriteNormalFormDecision := false`.

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free
(the SN measure is a `Nat` fold + structural `Nat` arithmetic via a hand-built associative-commutative
rearrangement; the SN proof is fuel-bounded `Acc` descent; `isGodement` is `singleAtomGodementStep`; the
confluence reduction is `newman`).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Tier0

open FX1Poly.Core (EquationalTheory Confluent WeaklyConfluent newman ReflTransClosure Joinable)

/-! ## The expanding-oriented single-atom Godement swap -/

/-- The **oriented single-atom Godement transposition**, positionwise, restricted to an EXPANDING left atom.
The `here` constructor is exactly the `singleAtomGodementStep` redex shape — the left atom `genX` with right
context factoring through the right atom's source generator, the right atom `genY` with left context factoring
through the left atom's target generator — with the orientation gate `expanding : genDomX.length <
genCodX.length` (the left generator's target 1-cell strictly longer than its source).  `under` slides a swap
past an independent prefix atom.  This is a sub-relation of `SpineGodementAtAnyPosition`
(`adjunctionOrientedSwapIsGodement`) on which the left-context-length sum strictly decreases. -/
inductive AdjunctionOrientedSwap :
    {sourceMode targetMode : AdjunctionMode} →
    List (SpineAtom adjunctionModeSignature sourceMode targetMode) →
    List (SpineAtom adjunctionModeSignature sourceMode targetMode) → Prop where
  /-- Fire an expanding single-atom Godement transposition at the head. -/
  | here {sourceMode targetMode : AdjunctionMode}
      {leftMidX middleMode rightMidY : AdjunctionMode}
      (leftContextX : ModalityPath adjunctionGraph sourceMode leftMidX)
      (genDomX genCodX : ModalityPath adjunctionGraph leftMidX middleMode)
      (genX : adjunctionModeSignature.twoCell genDomX genCodX)
      (genDomY genCodY : ModalityPath adjunctionGraph middleMode rightMidY)
      (genY : adjunctionModeSignature.twoCell genDomY genCodY)
      (rightContextY : ModalityPath adjunctionGraph rightMidY targetMode)
      (rest : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
      (expanding : genDomX.length < genCodX.length) :
      AdjunctionOrientedSwap
        (⟨leftMidX, middleMode, leftContextX, genDomX, genCodX, genX,
            composePath genDomY rightContextY⟩ ::
          ⟨middleMode, rightMidY, composePath leftContextX genCodX, genDomY, genCodY, genY,
            rightContextY⟩ :: rest)
        (⟨middleMode, rightMidY, composePath leftContextX genDomX, genDomY, genCodY, genY,
            rightContextY⟩ ::
          ⟨leftMidX, middleMode, leftContextX, genDomX, genCodX, genX,
            composePath genCodY rightContextY⟩ :: rest)
  /-- Slide an oriented swap past one independent prefix atom. -/
  | under {sourceMode targetMode : AdjunctionMode}
      (atom : SpineAtom adjunctionModeSignature sourceMode targetMode)
      {firstList secondList : List (SpineAtom adjunctionModeSignature sourceMode targetMode)} :
      AdjunctionOrientedSwap firstList secondList →
      AdjunctionOrientedSwap (atom :: firstList) (atom :: secondList)

/-- ★ **Every oriented swap is a positionwise Godement step** (the `orientedIsGodement` sandwich leg).  The
`here` case is one `singleAtomGodementStep` lifted through `SpineGodementAtAnyPosition.here`; the `under` case
is `SpineGodementAtAnyPosition.under`.  The `expanding` gate is discarded — orientation never widens the
relation. -/
theorem adjunctionOrientedSwapIsGodement {sourceMode targetMode : AdjunctionMode}
    {origin reduct : List (SpineAtom adjunctionModeSignature sourceMode targetMode)}
    (swap : AdjunctionOrientedSwap origin reduct) :
    SpineGodementAtAnyPosition adjunctionModeSignature origin reduct := by
  induction swap with
  | here leftContextX genDomX genCodX genX genDomY genCodY genY rightContextY rest _ =>
      exact SpineGodementAtAnyPosition.here
        (singleAtomGodementStep leftContextX genDomX genCodX genX genDomY genCodY genY rightContextY rest)
  | under atom _ inductionHypothesis => exact SpineGodementAtAnyPosition.under atom inductionHypothesis

/-! ## The strong-normalization measure -/

/-- The **left-whisker-context-length sum** of a spine list — the termination measure for the oriented swap.
The sum of every atom's `leftContext.length`. -/
def adjunctionLeftContextLengthSum {sourceMode targetMode : AdjunctionMode} :
    List (SpineAtom adjunctionModeSignature sourceMode targetMode) → Nat
  | [] => 0
  | atom :: rest => atom.leftContext.length + adjunctionLeftContextLengthSum rest

/-- Transpose the inner-and-trailing summands of a four-fold sum onto the left boundary — the rearrangement the
redex's left-context sum needs (`(B + I) + (B + S) = (B + (B + S)) + I`).  `Nat.add_assoc`/`add_comm`,
propext-free. -/
private theorem natRearrangeLeft (boundary inputLen restSum : Nat) :
    (boundary + inputLen) + (boundary + restSum) = (boundary + (boundary + restSum)) + inputLen := by
  rw [Nat.add_assoc boundary inputLen (boundary + restSum),
      Nat.add_comm inputLen (boundary + restSum), ← Nat.add_assoc boundary (boundary + restSum) inputLen]

/-- The mirror rearrangement for the origin's left-context sum (`B + ((B + O) + S) = (B + (B + S)) + O`).
`Nat.add_right_comm`/`add_assoc`, propext-free. -/
private theorem natRearrangeRight (boundary outputLen restSum : Nat) :
    boundary + ((boundary + outputLen) + restSum) = (boundary + (boundary + restSum)) + outputLen := by
  rw [Nat.add_right_comm boundary outputLen restSum, ← Nat.add_assoc boundary (boundary + restSum) outputLen]

/-- The single strict-decrease identity behind the SN measure: with a common boundary `B` and tail sum `S`, a
shorter input than output strictly lowers the sum — `(B + inputLen) + (B + S) < B + ((B + outputLen) + S)`
whenever `inputLen < outputLen`.  Both sides rearrange to `(B + (B + S)) + ·`, then `Nat.add_lt_add_left`. -/
private theorem natHereDecrease (boundary inputLen outputLen restSum : Nat) (h : inputLen < outputLen) :
    (boundary + inputLen) + (boundary + restSum) < boundary + ((boundary + outputLen) + restSum) := by
  rw [natRearrangeLeft boundary inputLen restSum, natRearrangeRight boundary outputLen restSum]
  exact Nat.add_lt_add_left h _

/-- ★ **Each oriented swap strictly decreases the left-context-length sum.**  In the `here` case the
transposition replaces the two left contexts `lcX` (length `B`) and `lcX ∘ genCodX` (length `B + |genCodX|`) by
`lcX ∘ genDomX` (length `B + |genDomX|`) and `lcX` (length `B`); since `expanding : |genDomX| < |genCodX|`, the
sum drops by `|genCodX| − |genDomX| > 0` (`natHereDecrease` after `ModalityPath.length_composePath`).  The
`under` case adds the unchanged head length to a smaller tail sum. -/
theorem adjunctionOrientedSwap_leftContextSum_lt {sourceMode targetMode : AdjunctionMode}
    {origin reduct : List (SpineAtom adjunctionModeSignature sourceMode targetMode)}
    (swap : AdjunctionOrientedSwap origin reduct) :
    adjunctionLeftContextLengthSum reduct < adjunctionLeftContextLengthSum origin := by
  induction swap with
  | here leftContextX genDomX genCodX genX genDomY genCodY genY rightContextY rest expanding =>
      dsimp only [adjunctionLeftContextLengthSum]
      rw [ModalityPath.length_composePath, ModalityPath.length_composePath]
      exact natHereDecrease leftContextX.length genDomX.length genCodX.length
        (adjunctionLeftContextLengthSum rest) expanding
  | under atom _ inductionHypothesis =>
      dsimp only [adjunctionLeftContextLengthSum]
      exact Nat.add_lt_add_left inductionHypothesis _

/-- ★ **The oriented swap relation is strongly normalizing.**  Every spine list is `Acc`-essible under the
flipped oriented swap — there is no infinite oriented reduction.  Proven by fuel-bounded structural `Nat`
induction on a bound exceeding `adjunctionLeftContextLengthSum`, descending via
`adjunctionOrientedSwap_leftContextSum_lt`; never `WellFounded.fix`.  This is the harness's `terminating`
obligation for `AdjunctionOrientedSwap` — the reflexive self-loops that refuted the un-oriented step live only
in the full `SpineGodementAtAnyPosition`, NOT in this measure-decreasing sub-relation. -/
theorem adjunctionOrientedSwapTerminating {sourceMode targetMode : AdjunctionMode}
    (value : List (SpineAtom adjunctionModeSignature sourceMode targetMode)) :
    Acc (fun reduct origin => AdjunctionOrientedSwap origin reduct) value := by
  suffices fueled : ∀ (fuel : Nat) {innerSource innerTarget : AdjunctionMode}
      (innerValue : List (SpineAtom adjunctionModeSignature innerSource innerTarget)),
      adjunctionLeftContextLengthSum innerValue < fuel →
      Acc (fun reduct origin => AdjunctionOrientedSwap origin reduct) innerValue by
    exact fueled (adjunctionLeftContextLengthSum value + 1) value (Nat.lt_succ_self _)
  intro fuel
  induction fuel with
  | zero => intro _ _ innerValue weightBelowZero; exact absurd weightBelowZero (Nat.not_lt_zero _)
  | succ fuel ihFuel =>
      intro _ _ innerValue weightBelowSucc
      refine Acc.intro innerValue (fun reduct stepToReduct => ?_)
      exact ihFuel reduct
        (Nat.lt_of_lt_of_le (adjunctionOrientedSwap_leftContextSum_lt stepToReduct)
          (Nat.le_of_lt_succ weightBelowSucc))

/-- ★ **Confluence reduces to LOCAL confluence** for the oriented swap: Newman's lemma turns the supplied SN
witness (`adjunctionOrientedSwapTerminating`, as `WellFounded` of the flipped relation) plus weak confluence
into full Church-Rosser confluence — the form `adjunctionTraceDecisionViaOrientedReducer` consumes.  So the
remaining confluence obligation is the textbook LOCAL one (the critical pairs), not the global hexagon. -/
theorem adjunctionOrientedSwapConfluentOfWeaklyConfluent {sourceMode targetMode : AdjunctionMode}
    (weaklyConfluent :
      WeaklyConfluent (AdjunctionOrientedSwap (sourceMode := sourceMode) (targetMode := targetMode))) :
    Confluent (AdjunctionOrientedSwap (sourceMode := sourceMode) (targetMode := targetMode)) :=
  newman ⟨adjunctionOrientedSwapTerminating⟩ weaklyConfluent

/-- The oriented theory passes through a head atom — the `under`-recursion ingredient of the completeness leg
(`godementInOrientedTheory`): a positionwise Godement step's `under` case threads `AdjunctionOrientedSwap.under`
through the equivalence closure. -/
theorem adjunctionOrientedTheory_consCongr {sourceMode targetMode : AdjunctionMode}
    (atom : SpineAtom adjunctionModeSignature sourceMode targetMode)
    {firstList secondList : List (SpineAtom adjunctionModeSignature sourceMode targetMode)}
    (conv : EquationalTheory
      (AdjunctionOrientedSwap (sourceMode := sourceMode) (targetMode := targetMode)) firstList secondList) :
    EquationalTheory (AdjunctionOrientedSwap (sourceMode := sourceMode) (targetMode := targetMode))
      (atom :: firstList) (atom :: secondList) := by
  induction conv with
  | rule step => exact EquationalTheory.rule (AdjunctionOrientedSwap.under atom step)
  | refl _ => exact EquationalTheory.refl _
  | symm _ inductionHypothesis => exact EquationalTheory.symm inductionHypothesis
  | trans _ _ firstHypothesis secondHypothesis => exact EquationalTheory.trans firstHypothesis secondHypothesis

/-! ## Witnesses: the oriented swap fires on the Eckmann–Hilton case; the contracting case is excluded -/

/-- ★ **The canonical Eckmann–Hilton witness oriented-swaps.**  The two parallel units' redex spine `[U1, U2]`
(left contexts `nil`, `LR`) reduces by one oriented swap to the reduct spine `[V1, V2]` (left contexts `nil`,
`nil`) — the expanding (unit) left atom fires.  Both spines compute by definitional reduction, so the swap is
the single `here` constructor at the unit instance. -/
theorem adjunctionParallelUnits_orientedSwap :
    AdjunctionOrientedSwap adjunctionParallelUnitsRedex.spine adjunctionParallelUnitsReduct.spine :=
  AdjunctionOrientedSwap.here
    (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) adjunctionLeftThenRight
    AdjunctionTwoCell.unit
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) adjunctionLeftThenRight
    AdjunctionTwoCell.unit
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) [] (by decide)

/-- Smoke: the measure on the Eckmann–Hilton redex spine is `2` (left contexts `nil`, `LR`). -/
theorem adjunctionParallelUnits_measure_redex :
    adjunctionLeftContextLengthSum adjunctionParallelUnitsRedex.spine = 2 := rfl

/-- Smoke: and on the reduct spine it is `0` (left contexts `nil`, `nil`) — the oriented swap dropped it `2 → 0`. -/
theorem adjunctionParallelUnits_measure_reduct :
    adjunctionLeftContextLengthSum adjunctionParallelUnitsReduct.spine = 0 := rfl

/-- ★ **The contracting (counit/counit) Godement step the expanding orientation does NOT cover.**  A genuine
positionwise Godement step at the seed whose left atom is a COUNIT (`adjunctionRightThenLeft ⇒ nil`).  Its two
endpoints are distinct spine lists, but the left atom is contracting (`adjunctionCounitGate_isContracting`), so
the step fails the `expanding` gate and — being on a two-element list, whose only position is the head — neither
endpoint is an `AdjunctionOrientedSwap` redex.  Hence this Godement step is NOT in `EquationalTheory
AdjunctionOrientedSwap`: the expanding orientation is INCOMPLETE for the trace word problem. -/
def adjunctionCounitGodementStep :=
  SpineGodementAtAnyPosition.here
    (singleAtomGodementStep (signature := adjunctionModeSignature)
      (identityPath (graph := adjunctionGraph) AdjunctionMode.tip)
      adjunctionRightThenLeft (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      AdjunctionTwoCell.counit
      adjunctionRightThenLeft (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      AdjunctionTwoCell.counit
      (identityPath (graph := adjunctionGraph) AdjunctionMode.tip) [])

/-- The counit's source 1-cell (`adjunctionRightThenLeft`, length `2`) is NOT shorter than its target 1-cell
(`nil`, length `0`): a counit-led pair is CONTRACTING, never `expanding`, so `AdjunctionOrientedSwap.here`
cannot fire on it.  This is the exact gate that excludes `adjunctionCounitGodementStep`. -/
theorem adjunctionCounitGate_isContracting :
    ¬ (adjunctionRightThenLeft.length <
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip).length) := by decide

/-! ## The harness with SN + isGodement + confluence-via-Newman discharged -/

/-- ★ **The trace-decision harness for the expanding orientation.**  Feeds `AdjunctionOrientedSwap` to
`adjunctionTraceDecisionViaOrientedReducer` with `terminating` (`adjunctionOrientedSwapTerminating`),
`orientedIsGodement` (`adjunctionOrientedSwapIsGodement`), and `confluent` (via Newman from local confluence)
DISCHARGED — leaving a deterministic reducer (`reduceStep` sound + complete), LOCAL confluence
(`weaklyConfluent`), and the completeness leg `godementInOrientedTheory` as the named residual obligations.

HONESTY: this assembly's `godementInOrientedTheory` premise is NOT free for the expanding restriction —
`adjunctionCounitGodementStep` exhibits a Godement step it cannot realize.  A USABLE decision therefore needs a
DIFFERENT, complete `orientedSwap` (the source-anchored canonicalisation with context-recomputation rules); the
discharged `terminating` / `orientedIsGodement` / `confluent` machinery is the reusable scaffold that any such
relation, once its rules also decrease a structural measure, will plug into. -/
@[reducible] def adjunctionTraceDecisionViaExpandingReducer
    (reduceStep : {sourceMode targetMode : AdjunctionMode} →
      List (SpineAtom adjunctionModeSignature sourceMode targetMode) →
      Option (List (SpineAtom adjunctionModeSignature sourceMode targetMode)))
    (reduceStep_sound : {sourceMode targetMode : AdjunctionMode} →
      {origin reduct : List (SpineAtom adjunctionModeSignature sourceMode targetMode)} →
      reduceStep origin = some reduct → AdjunctionOrientedSwap origin reduct)
    (reduceStep_complete : {sourceMode targetMode : AdjunctionMode} →
      {origin : List (SpineAtom adjunctionModeSignature sourceMode targetMode)} →
      reduceStep origin = none → ∀ next, ¬ AdjunctionOrientedSwap origin next)
    (weaklyConfluent : {sourceMode targetMode : AdjunctionMode} →
      WeaklyConfluent (AdjunctionOrientedSwap (sourceMode := sourceMode) (targetMode := targetMode)))
    (godementInOrientedTheory : {sourceMode targetMode : AdjunctionMode} →
      {origin reduct : List (SpineAtom adjunctionModeSignature sourceMode targetMode)} →
      SpineGodementAtAnyPosition adjunctionModeSignature origin reduct →
      EquationalTheory (AdjunctionOrientedSwap (sourceMode := sourceMode) (targetMode := targetMode))
        origin reduct) :
    AdjunctionSpineTraceDecision :=
  adjunctionTraceDecisionViaOrientedReducer
    AdjunctionOrientedSwap reduceStep reduceStep_sound reduceStep_complete
    adjunctionOrientedSwapTerminating
    (fun {sourceMode targetMode} =>
      adjunctionOrientedSwapConfluentOfWeaklyConfluent
        (weaklyConfluent (sourceMode := sourceMode) (targetMode := targetMode)))
    adjunctionOrientedSwapIsGodement godementInOrientedTheory

/-! ## Honesty marker -/

/-- **Honesty marker.**  The expanding-oriented single-atom Godement swap `AdjunctionOrientedSwap` is STRONGLY
NORMALIZING (`adjunctionOrientedSwapTerminating`, a one-line `Nat` measure — the design-lock's hard content,
resolving the non-monotone-measure worry FOR THIS sub-relation) and is a Godement sub-relation
(`adjunctionOrientedSwapIsGodement`), with confluence reduced to LOCAL confluence (Newman).  But it is
INCOMPLETE for the trace word problem (`adjunctionCounitGodementStep` + `adjunctionCounitGate_isContracting`):
the contracting counit-led Godement steps are uphill in the measure and their reverses are not Godement-shaped,
so no strongly-normalizing sub-relation of the raw Godement steps captures all of `SpineTraceEquiv`.  A full
oriented CANONICAL FORM needs context-recomputation rules outside the
`orientedSwap ⊆ SpineGodementAtAnyPosition` interface — the deferred Gratzer confluence-modulo-interchange
core.  Hence `fxMode_hasModeRelativeConvDecision` / `fxMode_hasDecidableTwoCellEquality` stay `false`.
`= false`. -/
def fxMode_hasOrientedTraceCanonicalForm : Bool := false

/-! ## ★ The RawTwoCellExpr route: mechanizing the central interchange NON-CONFLUENCE obstruction

The spine route above orients the Godement transposition and stalls on the contracting-counit incompleteness.
The keystone's OTHER convergent-rewriting route works directly on `RawTwoCellExpr` (the `SaturatedTwoCellStep`
combined triangle rewrite of `FreeTwoCellSaturatedConvergence`), and `FreeTwoCellConfluence` already reduced its
convergence — via the abstract `Core.newman` — to LOCAL confluence `TwoCellLocallyConfluent`, then documented IN
PROSE that this is FALSE: the free `interchange × whiskerRightVcomp` critical pair has two distinct terminal
normal forms (the classic Godement / Eckmann–Hilton non-confluence of the naive interchange orientation).

That negative result was never MECHANIZED — neither `FreeTwoCellConfluence` nor `FreeTwoCellSaturatedConvergence`
exhibits a zero-axiom non-joining witness; they only assert it.  This section closes that gap: it constructs the
concrete divergent peak, drives BOTH branches to distinct interchange-NORMAL forms, and proves
`¬ TwoCellLocallyConfluent` outright (zero-axiom).  This is the rigorous form of "which interchange critical pairs
join vs not": the triangle-layer pairs all JOIN (`FreeTwoCellSaturatedConvergence`), the interchange pair does
NOT — proven, not asserted.

### The abstract non-confluence toolkit (reusable over any relation)

Three generic lemmas, then one assembly: an irreducible source only reduces to itself; two distinct irreducible
forms cannot join; and (Newman, contrapositively) a strongly-normalizing relation with two divergent normal
forms is NOT locally confluent. -/

/-- A reflexive-transitive reduction OUT of an irreducible point goes nowhere: if no single step leaves `normal`,
then `normal` reduces only to itself.  `cases` on the closure (its indices are free variables — propext-clean);
the `head` case contradicts irreducibility. -/
theorem reflTransClosure_eq_of_irreducibleSource {Carrier : Type _} {rel : Carrier → Carrier → Prop}
    {normal reduct : Carrier} (irreducible : ∀ next, ¬ rel normal next)
    (chain : ReflTransClosure rel normal reduct) : reduct = normal := by
  cases chain with
  | refl _ => rfl
  | head firstStep _ => exact absurd firstStep (irreducible _)

/-- Two DISTINCT irreducible points are NOT joinable: any common reduct equals each of them (by
`reflTransClosure_eq_of_irreducibleSource`), forcing them equal — contradiction. -/
theorem notJoinable_of_distinctIrreducible {Carrier : Type _} {rel : Carrier → Carrier → Prop}
    {leftNormal rightNormal : Carrier}
    (leftIrreducible : ∀ next, ¬ rel leftNormal next)
    (rightIrreducible : ∀ next, ¬ rel rightNormal next)
    (distinct : leftNormal ≠ rightNormal) : ¬ Joinable rel leftNormal rightNormal := by
  intro joinable
  obtain ⟨commonReduct, leftChain, rightChain⟩ := joinable
  exact distinct
    ((reflTransClosure_eq_of_irreducibleSource leftIrreducible leftChain).symm.trans
      (reflTransClosure_eq_of_irreducibleSource rightIrreducible rightChain))

/-- A common source reducing to two DISTINCT irreducible forms refutes CONFLUENCE: confluence would join the two
divergent reductions, but distinct irreducibles do not join. -/
theorem notConfluent_of_divergentNormalForms {Carrier : Type _} {rel : Carrier → Carrier → Prop}
    {peak leftNormal rightNormal : Carrier}
    (leftReduces : ReflTransClosure rel peak leftNormal)
    (rightReduces : ReflTransClosure rel peak rightNormal)
    (leftIrreducible : ∀ next, ¬ rel leftNormal next)
    (rightIrreducible : ∀ next, ¬ rel rightNormal next)
    (distinct : leftNormal ≠ rightNormal) : ¬ Confluent rel :=
  fun confluent =>
    notJoinable_of_distinctIrreducible leftIrreducible rightIrreducible distinct
      (confluent leftReduces rightReduces)

/-- **Newman, contrapositively.**  A strongly-normalizing (`WellFounded` of the flipped relation) relation that is
NOT confluent cannot be locally (weakly) confluent — else `Core.newman` would make it confluent. -/
theorem notWeaklyConfluent_of_notConfluent {Carrier : Type _} {rel : Carrier → Carrier → Prop}
    (terminating : WellFounded (fun reduct origin => rel origin reduct))
    (notConfluent : ¬ Confluent rel) : ¬ WeaklyConfluent rel :=
  fun weaklyConfluent => notConfluent (newman terminating weaklyConfluent)

/-! ### Structural whisker-head probes (the propext-clean distinguisher of the two normal forms)

Single-level, full-coverage, constant-`Bool`-motive recognizers (the `isIdentityCell` / `isVcompCell` shape, so
propext-free): the two divergent normal forms share their head `vcomp atom1 _` and differ only at the LEFT factor
of the SECOND vcomp factor (a left-whiskering on one branch, a right-whiskering on the other). -/

/-- Whether a 2-cell's head constructor is a LEFT whiskering. -/
def RawTwoCellExpr.isWhiskerLeftHead {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Bool
  | _, _, _, _, .whiskerLeft _ _ => true
  | _, _, _, _, .gen _ => false
  | _, _, _, _, .id _ => false
  | _, _, _, _, .vcomp _ _ => false
  | _, _, _, _, .whiskerRight _ _ => false

/-- Whether the LEFT factor of a vertical composite has a left-whiskering head (else `false`). -/
def RawTwoCellExpr.leftFactorIsWhiskerLeft {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Bool
  | _, _, _, _, .vcomp leftFactor _ => leftFactor.isWhiskerLeftHead
  | _, _, _, _, .gen _ => false
  | _, _, _, _, .id _ => false
  | _, _, _, _, .whiskerLeft _ _ => false
  | _, _, _, _, .whiskerRight _ _ => false

/-- Whether the SECOND factor's left factor has a left-whiskering head — the depth-2 probe distinguishing the two
interchange normal forms. -/
def RawTwoCellExpr.secondLeftIsWhiskerLeft {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Bool
  | _, _, _, _, .vcomp _ secondFactor => secondFactor.leftFactorIsWhiskerLeft
  | _, _, _, _, .gen _ => false
  | _, _, _, _, .id _ => false
  | _, _, _, _, .whiskerLeft _ _ => false
  | _, _, _, _, .whiskerRight _ _ => false

/-! ### The minimal witness signature: one mode, three parallel endo-1-cells, two stacked 2-cell generators

The adjunction seed cannot host a clean Godement square (it has NO non-identity 2-cell out of `L R`, so every
non-trivial vertical composite is a snake).  But the free-2-category non-confluence is signature-GENERIC, so a
minimal independent signature exhibits it cleanly: one mode `pt`, three parallel endo-1-cells `low`, `mid`,
`high`, and two vertically-stacked generators `lower : low ⇒ mid`, `upper : mid ⇒ high`.  Their horizontal square
`(lower ⊟ upper) ⊠ (lower ⊟ upper)` is the divergent peak. -/

/-- The single mode of the witness signature. -/
inductive InterchangeWitnessMode where
  /-- The only object. -/
  | pt

/-- Three parallel endo-1-cell generators at `pt` — the source/middle/target 1-cells of the vertical stack. -/
inductive InterchangeWitnessModality : InterchangeWitnessMode → InterchangeWitnessMode → Type where
  /-- The bottom 1-cell. -/
  | edgeLow : InterchangeWitnessModality InterchangeWitnessMode.pt InterchangeWitnessMode.pt
  /-- The middle 1-cell. -/
  | edgeMid : InterchangeWitnessModality InterchangeWitnessMode.pt InterchangeWitnessMode.pt
  /-- The top 1-cell. -/
  | edgeHigh : InterchangeWitnessModality InterchangeWitnessMode.pt InterchangeWitnessMode.pt

/-- The witness quiver: one mode, three endo-modality generators. -/
def interchangeWitnessGraph : ModeGraph where
  Mode := InterchangeWitnessMode
  Modality := InterchangeWitnessModality

/-- The bottom 1-cell as a length-1 path. -/
def witnessPathLow : ModalityPath interchangeWitnessGraph InterchangeWitnessMode.pt InterchangeWitnessMode.pt :=
  singletonModalityPath InterchangeWitnessModality.edgeLow

/-- The middle 1-cell as a length-1 path. -/
def witnessPathMid : ModalityPath interchangeWitnessGraph InterchangeWitnessMode.pt InterchangeWitnessMode.pt :=
  singletonModalityPath InterchangeWitnessModality.edgeMid

/-- The top 1-cell as a length-1 path. -/
def witnessPathHigh : ModalityPath interchangeWitnessGraph InterchangeWitnessMode.pt InterchangeWitnessMode.pt :=
  singletonModalityPath InterchangeWitnessModality.edgeHigh

/-- Two vertically-stacked generating 2-cells `lower : low ⇒ mid`, `upper : mid ⇒ high` between parallel 1-cells. -/
inductive InterchangeWitnessTwoCell :
    {sourceMode targetMode : InterchangeWitnessMode} →
    ModalityPath interchangeWitnessGraph sourceMode targetMode →
    ModalityPath interchangeWitnessGraph sourceMode targetMode → Type where
  /-- The bottom 2-cell `low ⇒ mid`. -/
  | lower : InterchangeWitnessTwoCell witnessPathLow witnessPathMid
  /-- The top 2-cell `mid ⇒ high`. -/
  | upper : InterchangeWitnessTwoCell witnessPathMid witnessPathHigh

/-- The minimal witness 2-polygraph hosting the Godement square. -/
def interchangeWitnessSignature : ModeSignature where
  graph := interchangeWitnessGraph
  twoCell := fun firstPath secondPath => InterchangeWitnessTwoCell firstPath secondPath

/-- The bottom generator as a free 2-cell `low ⇒ mid`. -/
def witnessLower : RawTwoCellExpr interchangeWitnessSignature witnessPathLow witnessPathMid :=
  RawTwoCellExpr.gen InterchangeWitnessTwoCell.lower

/-- The top generator as a free 2-cell `mid ⇒ high`. -/
def witnessUpper : RawTwoCellExpr interchangeWitnessSignature witnessPathMid witnessPathHigh :=
  RawTwoCellExpr.gen InterchangeWitnessTwoCell.upper

/-- The vertical stack `lower ⊟ upper : low ⇒ high`. -/
def witnessVerticalStack : RawTwoCellExpr interchangeWitnessSignature witnessPathLow witnessPathHigh :=
  RawTwoCellExpr.vcomp witnessLower witnessUpper

/-- ★ The **divergent peak**: the horizontal Godement square `(lower ⊟ upper) ⊠ (lower ⊟ upper)` of two copies of
the vertical stack — the source of both the `interchange` redex and the `whiskerRightVcomp` redex. -/
def interchangeWitnessPeak :
    RawTwoCellExpr interchangeWitnessSignature
      (composePath witnessPathLow witnessPathLow) (composePath witnessPathHigh witnessPathHigh) :=
  RawTwoCellExpr.hcomp witnessVerticalStack witnessVerticalStack

/-- The **interchange-branch normal form** `n₁`: the vcomp-spine `[low▷low, mid◁low, mid▷high, high◁high]` — the
2×2 pasting decomposed COLUMN-then-row.  Firing `interchange` at the peak, then `vcompAssoc`, reaches it. -/
def interchangeWitnessNormalInterchange :
    RawTwoCellExpr interchangeWitnessSignature
      (composePath witnessPathLow witnessPathLow) (composePath witnessPathHigh witnessPathHigh) :=
  RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight witnessPathLow witnessLower)
    (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft witnessPathMid witnessLower)
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight witnessPathMid witnessUpper)
        (RawTwoCellExpr.whiskerLeft witnessPathHigh witnessUpper)))

/-- The **whisker-branch normal form** `n₂`: the vcomp-spine `[low▷low, low▷high, high◁low, high◁high]` — the SAME
2×2 pasting decomposed ROW-then-column.  Firing `whiskerRightVcomp` then `whiskerLeftVcomp` then `vcompAssoc` at
the peak reaches it.  Differs from `n₁` at the second spine position (`low▷high` vs `mid◁low`) and in every
whiskering 1-cell — the genuine Godement / Eckmann–Hilton divergence. -/
def interchangeWitnessNormalWhisker :
    RawTwoCellExpr interchangeWitnessSignature
      (composePath witnessPathLow witnessPathLow) (composePath witnessPathHigh witnessPathHigh) :=
  RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight witnessPathLow witnessLower)
    (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight witnessPathLow witnessUpper)
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft witnessPathHigh witnessLower)
        (RawTwoCellExpr.whiskerLeft witnessPathHigh witnessUpper)))

/-! ### The two reductions, the irreducibility of both normal forms, and their distinctness -/

/-- The peak unfolds (`rfl`) to the explicit vertical composite of two whiskerings — the form the whisker-branch
redexes act on (exposes `hcomp` for the unifier). -/
theorem interchangeWitnessPeak_unfold :
    interchangeWitnessPeak = RawTwoCellExpr.vcomp
      (RawTwoCellExpr.whiskerRight witnessPathLow witnessVerticalStack)
      (RawTwoCellExpr.whiskerLeft witnessPathHigh witnessVerticalStack) := rfl

/-- ★ **Interchange branch**: the peak reduces to `n₁` by `interchange` then `vcompAssoc` (two steps).  Built in
tactic mode (`refine ... ?_` keeps each goal concrete so `exact` unfolds `hcomp` via `isDefEq`). -/
theorem interchangeWitnessPeak_reducesTo_interchangeNormal :
    ReflTransClosure (fun (a b : RawTwoCellExpr interchangeWitnessSignature
        (composePath witnessPathLow witnessPathLow) (composePath witnessPathHigh witnessPathHigh)) =>
      TwoCellStep interchangeWitnessSignature a b)
      interchangeWitnessPeak interchangeWitnessNormalInterchange := by
  refine ReflTransClosure.head
    (TwoCellStep.interchange witnessLower witnessUpper witnessLower witnessUpper) ?_
  refine ReflTransClosure.single ?_
  exact TwoCellStep.vcompAssoc
    (RawTwoCellExpr.whiskerRight witnessPathLow witnessLower)
    (RawTwoCellExpr.whiskerLeft witnessPathMid witnessLower)
    (RawTwoCellExpr.hcomp witnessUpper witnessUpper)

/-- ★ **Whisker branch**: the peak reduces to `n₂` by `whiskerRightVcomp`, `whiskerLeftVcomp`, `vcompAssoc`
(three steps). -/
theorem interchangeWitnessPeak_reducesTo_whiskerNormal :
    ReflTransClosure (fun (a b : RawTwoCellExpr interchangeWitnessSignature
        (composePath witnessPathLow witnessPathLow) (composePath witnessPathHigh witnessPathHigh)) =>
      TwoCellStep interchangeWitnessSignature a b)
      interchangeWitnessPeak interchangeWitnessNormalWhisker := by
  rw [interchangeWitnessPeak_unfold]
  refine ReflTransClosure.head
    (TwoCellStep.vcompCongrLeft
      (RawTwoCellExpr.whiskerLeft witnessPathHigh witnessVerticalStack)
      (TwoCellStep.whiskerRightVcomp witnessPathLow witnessLower witnessUpper)) ?_
  refine ReflTransClosure.head
    (TwoCellStep.vcompCongrRight
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight witnessPathLow witnessLower)
        (RawTwoCellExpr.whiskerRight witnessPathLow witnessUpper))
      (TwoCellStep.whiskerLeftVcomp witnessPathHigh witnessLower witnessUpper)) ?_
  refine ReflTransClosure.single ?_
  exact TwoCellStep.vcompAssoc
    (RawTwoCellExpr.whiskerRight witnessPathLow witnessLower)
    (RawTwoCellExpr.whiskerRight witnessPathLow witnessUpper)
    (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft witnessPathHigh witnessLower)
      (RawTwoCellExpr.whiskerLeft witnessPathHigh witnessUpper))

/-- `n₁` is an interchange normal form (computes by `rfl`). -/
theorem interchangeWitnessNormalInterchange_isInterchangeNormal :
    interchangeWitnessNormalInterchange.isInterchangeNormal = true := rfl

/-- `n₂` is an interchange normal form (computes by `rfl`). -/
theorem interchangeWitnessNormalWhisker_isInterchangeNormal :
    interchangeWitnessNormalWhisker.isInterchangeNormal = true := rfl

/-- ★ `n₁` is `TwoCellStep`-IRREDUCIBLE: every step's source is non-normal
(`TwoCellStep.source_not_interchangeNormal`), but `n₁` is normal. -/
theorem interchangeWitnessNormalInterchange_irreducible
    (next : RawTwoCellExpr interchangeWitnessSignature
      (composePath witnessPathLow witnessPathLow) (composePath witnessPathHigh witnessPathHigh)) :
    ¬ TwoCellStep interchangeWitnessSignature interchangeWitnessNormalInterchange next :=
  fun step =>
    Bool.noConfusion
      (interchangeWitnessNormalInterchange_isInterchangeNormal.symm.trans
        step.source_not_interchangeNormal)

/-- ★ `n₂` is `TwoCellStep`-IRREDUCIBLE — same argument, dual normal form. -/
theorem interchangeWitnessNormalWhisker_irreducible
    (next : RawTwoCellExpr interchangeWitnessSignature
      (composePath witnessPathLow witnessPathLow) (composePath witnessPathHigh witnessPathHigh)) :
    ¬ TwoCellStep interchangeWitnessSignature interchangeWitnessNormalWhisker next :=
  fun step =>
    Bool.noConfusion
      (interchangeWitnessNormalWhisker_isInterchangeNormal.symm.trans
        step.source_not_interchangeNormal)

/-- ★ The two normal forms are DISTINCT: the depth-2 whisker-head probe reads `true` on `n₁`
(`mid◁low` is a left whiskering) and `false` on `n₂` (`low▷high` is a right whiskering). -/
theorem interchangeWitness_normalForms_distinct :
    interchangeWitnessNormalInterchange ≠ interchangeWitnessNormalWhisker := by
  intro equalForms
  have probeEqual :
      interchangeWitnessNormalInterchange.secondLeftIsWhiskerLeft
        = interchangeWitnessNormalWhisker.secondLeftIsWhiskerLeft :=
    congrArg RawTwoCellExpr.secondLeftIsWhiskerLeft equalForms
  rw [show interchangeWitnessNormalInterchange.secondLeftIsWhiskerLeft = true from rfl,
      show interchangeWitnessNormalWhisker.secondLeftIsWhiskerLeft = false from rfl] at probeEqual
  exact Bool.noConfusion probeEqual

/-! ### ★ The mechanized obstruction: the free 3-polygraph is NOT confluent, hence NOT locally confluent -/

/-- ★★ **The free `TwoCellStep` 3-polygraph is NOT confluent** at the witness boundary: the peak reduces to two
DISTINCT irreducible normal forms (`n₁` via interchange, `n₂` via whisker distribution), which cannot join.  This
is the classic Godement / Eckmann–Hilton non-confluence of the naive interchange orientation, finally MECHANIZED
(zero-axiom) rather than asserted. -/
theorem interchangeWitness_notConfluent :
    ¬ Confluent (fun (a b : RawTwoCellExpr interchangeWitnessSignature
        (composePath witnessPathLow witnessPathLow) (composePath witnessPathHigh witnessPathHigh)) =>
      TwoCellStep interchangeWitnessSignature a b) :=
  notConfluent_of_divergentNormalForms
    interchangeWitnessPeak_reducesTo_interchangeNormal
    interchangeWitnessPeak_reducesTo_whiskerNormal
    interchangeWitnessNormalInterchange_irreducible
    interchangeWitnessNormalWhisker_irreducible
    interchangeWitness_normalForms_distinct

/-- ★★★ **The free 3-polygraph is NOT locally confluent** — `¬ TwoCellLocallyConfluent`.  By Newman
contrapositively: `TwoCellStep` IS strongly normalizing (`twoCellStep_isStronglyNormalizing`), so were it locally
confluent it would be confluent (`Core.newman`), contradicting `interchangeWitness_notConfluent`.  This converts
`FreeTwoCellConfluence`'s PROSE obstruction (`TwoCellLocallyConfluent` "is provably FALSE") into a THEOREM, and is
the precise residual the keystone's rewriting route is blocked on: the `interchange × whiskerRightVcomp` critical
pair does NOT join (contrast the triangle-layer pairs, which all DO —
`FreeTwoCellSaturatedConvergence.saturated*AssocCriticalPair_joins`). -/
theorem interchangeWitness_notLocallyConfluent :
    ¬ TwoCellLocallyConfluent interchangeWitnessSignature := by
  intro locallyConfluent
  exact notWeaklyConfluent_of_notConfluent
    (WellFounded.intro
      (fun cell => twoCellStep_isStronglyNormalizing
        (signature := interchangeWitnessSignature)
        (sourcePath := composePath witnessPathLow witnessPathLow)
        (targetPath := composePath witnessPathHigh witnessPathHigh) cell))
    interchangeWitness_notConfluent
    (locallyConfluent
      (sourcePath := composePath witnessPathLow witnessPathLow)
      (targetPath := composePath witnessPathHigh witnessPathHigh))

/-! ## ★ The constructive half: the saturated DECISION via a rewriting normal form (the "different strategy")

The semantic route (`FreeTwoCellSaturatedDecision`) decides `SaturatedTwoCellConv` modulo the Schanuel–Street
MONOTONE MAP, owing BOTH `mapEqOfConv` and `convOfMapEq`.  The convergent-rewriting route assembles the SAME
decision modulo a rewriting NORMAL FORM — but with the YES-direction GROUNDED in actual `SaturatedTwoCellStep`
reductions, hence sound BY CONSTRUCTION (`saturatedTwoCellReduces_toSaturatedConv`, `FreeTwoCellSaturated
Convergence`).  So only the NO-direction (`complete`: convertible cells share a normal form — exactly confluence +
whisker functoriality) is owed — one residual, not two.  That residual is precisely the
`interchangeWitness_notLocallyConfluent` obstruction above promoted to a normalizer; the triangle layer adds
none (`FreeTwoCellSaturatedConvergence`'s four `*AssocCriticalPair_joins`). -/

/-- ★ **Joinable ⟹ convertible** — the bedrock soundness of the rewriting decision's YES-branch (fully
discharged).  A common reduct makes both endpoints convertible to it (reductions are sound,
`saturatedTwoCellReduces_toSaturatedConv`), hence to each other. -/
theorem saturatedConv_of_joinable {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (joinable : Joinable
      (fun (a b : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) => SaturatedTwoCellStep a b)
      cellA cellB) :
    SaturatedTwoCellConv cellA cellB := by
  obtain ⟨commonReduct, leftChain, rightChain⟩ := joinable
  exact SaturatedTwoCellConv.trans
    (saturatedTwoCellReduces_toSaturatedConv leftChain)
    (SaturatedTwoCellConv.symm (saturatedTwoCellReduces_toSaturatedConv rightChain))

/-- The seed's **saturated rewriting canonicalization** — a normal-form map for the combined triangle rewrite
`SaturatedTwoCellStep`, packaged with its two honest fields: `reducesToNormal` (every cell `SaturatedTwoCellStep`-
reduces to its normal form — the YES-direction, dischargeable from a concrete normalizer) and `complete`
(convertible cells share a normal form — the NO-direction residual, i.e. confluence modulo interchange +
whisker functoriality).  Compare `AdjunctionSaturatedCanonicalization` (the monotone-map structure), which owes
soundness too; here soundness is structural. -/
structure AdjunctionSaturatedRewriteCanonicalization where
  /-- The rewriting normal form of a saturated 2-cell. -/
  normalize : {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath
  /-- The cell `SaturatedTwoCellStep`-reduces to its normal form (grounds the YES-direction soundly). -/
  reducesToNormal : {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
    ReflTransClosure
      (fun (a b : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) => SaturatedTwoCellStep a b)
      cell (normalize cell)
  /-- COMPLETENESS (the residual): convertible cells share a normal form — confluence modulo interchange. -/
  complete : {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} →
    SaturatedTwoCellConv cellA cellB → normalize cellA = normalize cellB

/-- ★ **Decide saturated convertibility via the rewriting normal form.**  Given the canonicalization and a
decidable equality on normal forms, compare `normalize cellA` and `normalize cellB`: equal normal forms ⟹
`isTrue` (each cell is convertible to its normal form by `reducesToNormal` + reduction-soundness, and the two
normal forms coincide); unequal ⟹ `isFalse` (`complete` would force them equal).  The YES-branch is discharged
from the rewrite reductions themselves; only `complete` is residual. -/
def adjunctionDecideSaturatedConvViaRewriteNormalForm
    (canon : AdjunctionSaturatedRewriteCanonicalization)
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (decEqNormalForms : (cellX cellY : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
      Decidable (cellX = cellY))
    (cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Decidable (SaturatedTwoCellConv cellA cellB) :=
  match decEqNormalForms (canon.normalize cellA) (canon.normalize cellB) with
  | isTrue normalFormsEqual =>
      isTrue (by
        have convToNormalA := saturatedTwoCellReduces_toSaturatedConv (canon.reducesToNormal cellA)
        have convToNormalB := saturatedTwoCellReduces_toSaturatedConv (canon.reducesToNormal cellB)
        rw [normalFormsEqual] at convToNormalA
        exact SaturatedTwoCellConv.trans convToNormalA (SaturatedTwoCellConv.symm convToNormalB))
  | isFalse normalFormsDiffer =>
      isFalse (fun conv => normalFormsDiffer (canon.complete conv))

/-- The seed's **saturated 2-cell word problem, modulo the rewriting canonicalization** — the rewriting analog of
`adjunctionSaturatedWordProblemModuloCanonicalization`.  Supplying the canonicalization (+ decidable normal-form
equality) decides EVERY parallel pair. -/
@[reducible] def adjunctionSaturatedWordProblemModuloRewriteNormalForm
    (canon : AdjunctionSaturatedRewriteCanonicalization)
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (decEqNormalForms : (cellX cellY : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
      Decidable (cellX = cellY)) :
    (cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
    Decidable (SaturatedTwoCellConv cellA cellB) :=
  fun cellA cellB => adjunctionDecideSaturatedConvViaRewriteNormalForm canon decEqNormalForms cellA cellB

/-- Smoke: under any rewriting canonicalization, the left snake and `id_L` share a normal form (`complete` honours
the left triangle's bubble collapse) — the decision sees the bubble straighten, just as
`adjunctionDecideSaturated_leftSnake_isTrue` does for the monotone map. -/
theorem adjunctionRewriteNormalForm_leftSnake_collapses
    (canon : AdjunctionSaturatedRewriteCanonicalization) :
    canon.normalize adjunctionSeedLeftSnake
      = canon.normalize (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left)) :=
  canon.complete SaturatedTwoCellConv.triangleLeft

/-! ## Honesty marker for the rewriting route -/

/-- **Honesty marker.**  The `RawTwoCellExpr` convergent-rewriting route to the saturated keystone: the combined
triangle rewrite `SaturatedTwoCellStep` is strongly normalizing and SOUND for `SaturatedTwoCellConv`
(`FreeTwoCellSaturatedConvergence`); its decision assembles modulo a rewriting normal form
(`adjunctionDecideSaturatedConvViaRewriteNormalForm`) with the YES-direction discharged
(`saturatedConv_of_joinable`, `reducesToNormal`).  But the NO-direction (`complete` = a CONFLUENT normalizer) is
blocked: the rewrite is NOT locally confluent (`interchangeWitness_notLocallyConfluent` — the
`interchange × whiskerRightVcomp` pair does NOT join, now a THEOREM), and `TwoCellConvFull` additionally posits
whisker functoriality (whisker-by-unit / -composite) that the rewrite does not orient.  So the convergent route is
confluence MODULO interchange + whisker functoriality — the pre-existing `fxMode_hasInterchangeAndWhisker
Functoriality` floor, NOT anything triangle-specific (the triangle critical pairs all join).
`fxMode_hasModeRelativeConvDecision` / `fxMode_hasDecidableTwoCellEquality` stay `false` (parent-owned).
`= false`. -/
def fxMode_hasSaturatedRewriteNormalFormDecision : Bool := false

end FX1Poly.Tier0
