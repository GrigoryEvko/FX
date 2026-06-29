import FX1Poly.Tier0.Mode.FreeTwoCellTraceReducer

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
`false`; this file flips no decision gate, only records `fxMode_hasOrientedTraceCanonicalForm := false`.

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free
(the SN measure is a `Nat` fold + structural `Nat` arithmetic via a hand-built associative-commutative
rearrangement; the SN proof is fuel-bounded `Acc` descent; `isGodement` is `singleAtomGodementStep`; the
confluence reduction is `newman`).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Tier0

open FX1Poly.Core (EquationalTheory Confluent WeaklyConfluent newman)

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

end FX1Poly.Tier0
