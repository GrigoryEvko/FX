import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineArityDiscipline
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCapSpine
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupSpine
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSeed

/-! # WalkingString/StringSpineValleyWidthTelescope — the Piece-I length-determinacy core over the
walking ADJOINT-TRIPLE (`F ⊣ G ⊣ H`) signature (FC-3 r28, the M2 width telescopes)

The string clone of the walking-adjunction `SpineValleyWidthTelescope`.  The clean whole-valley producer
`stringMidZeroSameMatchingValleys_spineTraceEquiv` (`StringMidZeroValleyReassembly`, FC-3 r27) consumes two side
conditions on top of the arity / chain data: the cap blocks have equal LENGTH (`capLengthEq`) and the cup blocks
have equal LENGTH (`cupLengthEq`).  These are NOT free — they are the genuinely-new content of the string
`StringMidZeroValleyTraceEquiv` bridge: they must be DERIVED from the equal boundary matching (which forces the
two mid-widths equal) plus the two boundaries.  This file ships the two width TELESCOPES that make them derivable,
plus the two length-determinacy corollaries, all at the three-colour `adjointTripleModeSignature`.

The width accounting is signature-BLIND: a cap consumes `2` bottom wires and a cup opens `2` top wires regardless
of which colour (`F`/`G`/`H`) the generator carries — the telescope reads only the arity `(2, 0)` / `(0, 2)`, never
the length-rigidity-breaking `F ≠ H` species distinction.  So every one of the four ports below is a byte-identical
token-swap of the walking-adjunction original over `{signature}`-generic per-atom lemmas
(`stepAtom_openWires_tracksBoundary`, `spineBoundaryChained_tail`, `AtomHasCupOrCapArity`), with the signature token
alone rerouted `adjunctionModeSignature → adjointTripleModeSignature`.

  * ★ `stringPureCapBlock_widthTelescope` — over a boundary-chained pure-cap block, each cap drops the open-wire
    count by exactly `2` (`stepAtom_openWires_tracksBoundary`: `codBoundary + 2 = domBoundary`), so the final width
    plus `2 · len` recovers the entry width.
  * ★ `stringPureCupBlock_widthTelescope` — DUAL: each cup RAISES the width by `2`.
  * ★ `stringCapLength_eq_of_midWidth_eq` — cap length-determinacy: two cap blocks chained from the SAME bottom
    count whose mid-widths agree have equal length (cancel `2 ·` in the telescope).
  * ★ `stringCupLength_eq_of_midWidth_eq_of_finalWidth_eq` — cup length-determinacy, parametric in the two whole
    valleys' FINAL widths agreeing (which the assembly supplies from the shared top boundary `targetPath`).

All four are clean structural inductions / Nat cancellations.  No arc readoff, no reconstruction — pure boundary
arithmetic riding the shipped per-atom tracker.  Concrete truth-probes fire the two telescopes on a genuine string
cap `ε : G·F ⇒ id_tip` (width `2 → 0`) and a genuine string cup `η' : id_tip ⇒ G·H` (width `0 → 2`), so neither
port is vacuous on a real string valley.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Propext-free Nat cancellation (local; the core `Nat.add_left_cancel` leaks propext) -/

/-- Right-cancellation for Nat addition, structural and propext-free (the `+ 0` base is defeq, the
`+ (n+1)` step is `Nat.succ.inj`).  Local `WT`-suffixed copy to keep the umbrella build's global table
duplicate-free against the walking-adjunction twin. -/
private theorem natAddRightCancelWT : (cancelled : Nat) → {leftSum rightSum : Nat} →
    leftSum + cancelled = rightSum + cancelled → leftSum = rightSum
  | 0, _, _, sumsEq => sumsEq
  | cancelled + 1, _, _, sumsEq => natAddRightCancelWT cancelled (Nat.succ.inj sumsEq)

/-- Left-cancellation for Nat addition, propext-free via `Nat.add_comm` (itself axiom-free) plus the local
right-cancellation. -/
private theorem natAddLeftCancelWT {sharedLeft leftSum rightSum : Nat}
    (equalSums : sharedLeft + leftSum = sharedLeft + rightSum) : leftSum = rightSum :=
  natAddRightCancelWT sharedLeft
    ((Nat.add_comm leftSum sharedLeft).trans (equalSums.trans (Nat.add_comm sharedLeft rightSum)))

/-- The `List.range` accumulator length, structural and propext-free (the core `List.length_range` leaks). -/
private theorem rangeLoopLengthWT : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLengthWT count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

/-- `(List.range count).length = count`, propext-free (local copy; the core lemma leaks). -/
private theorem rangeLengthWT (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLengthWT count []]
  exact Nat.add_zero count

/-! ## The two width telescopes -/

/-- ★ **String cap-block width telescope.**  A boundary-chained pure-cap block drops the open-wire count by exactly
`2` per cap; additively, the final width plus twice the block length is the entry width.  Structural induction: the
head cap fires at the running boundary (`stepAtom_openWires_tracksBoundary`), leaving `codBoundary = domBoundary −
2 = entryWidth − 2`, and the tail is chained at that new boundary.  Colour-blind — reads only the cap arity. -/
theorem stringPureCapBlock_widthTelescope
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (capBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    AllCapArity capBlock →
    (state : WireState) →
    SpineBoundaryChained state.openWires.length capBlock →
    (processSpine state capBlock).openWires.length + 2 * capBlock.length = state.openWires.length
  | [], _, state, _ => by
      dsimp only [processSpine, List.foldl, List.length]
      rw [Nat.mul_zero, Nat.add_zero]
  | atom :: rest, capPure, state, chained => by
      cases capPure with
      | cons capDom capCod restCap =>
          obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
          have arity : AtomHasCupOrCapArity atom := Or.inr ⟨capDom, capCod⟩
          have stepTracks : (stepAtom state atom).openWires.length = atom.codBoundaryLength :=
            stepAtom_openWires_tracksBoundary state atom arity headFires.symm
          -- Each cap: codBoundary + 2 = domBoundary = entry width.
          have hcod : atom.codBoundaryLength = atom.leftContext.length + atom.rightContext.length := by
            dsimp only [SpineAtom.codBoundaryLength]
            rw [capCod, Nat.add_zero]
          have hdom : atom.domBoundaryLength
              = atom.leftContext.length + atom.rightContext.length + 2 := by
            dsimp only [SpineAtom.domBoundaryLength]
            rw [capDom]
            exact Nat.add_right_comm atom.leftContext.length 2 atom.rightContext.length
          have dropTwo : atom.codBoundaryLength + 2 = state.openWires.length := by
            rw [hcod, ← headFires, hdom]
          have tailChainedAtStep :
              SpineBoundaryChained (stepAtom state atom).openWires.length rest := by
            rw [stepTracks]; exact tailChained
          have ih := stringPureCapBlock_widthTelescope rest restCap (stepAtom state atom) tailChainedAtStep
          -- `processSpine state (atom :: rest) = processSpine (stepAtom state atom) rest`.
          show (processSpine (stepAtom state atom) rest).openWires.length + 2 * (rest.length + 1)
            = state.openWires.length
          rw [Nat.mul_succ, ← Nat.add_assoc, ih, stepTracks, dropTwo]

/-- ★ **String cup-block width telescope.**  DUAL of the cap telescope: a boundary-chained pure-cup block RAISES
the open-wire count by exactly `2` per cup, so the final width is the entry width plus twice the block length. -/
theorem stringPureCupBlock_widthTelescope
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    AllCupArity cupBlock →
    (state : WireState) →
    SpineBoundaryChained state.openWires.length cupBlock →
    (processSpine state cupBlock).openWires.length = state.openWires.length + 2 * cupBlock.length
  | [], _, state, _ => by
      dsimp only [processSpine, List.foldl, List.length]
      rw [Nat.mul_zero, Nat.add_zero]
  | atom :: rest, cupPure, state, chained => by
      cases cupPure with
      | cons cupDom cupCod restCup =>
          obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
          have arity : AtomHasCupOrCapArity atom := Or.inl ⟨cupDom, cupCod⟩
          have stepTracks : (stepAtom state atom).openWires.length = atom.codBoundaryLength :=
            stepAtom_openWires_tracksBoundary state atom arity headFires.symm
          -- Each cup: codBoundary = domBoundary + 2 = entry width + 2.
          have hcod : atom.codBoundaryLength
              = atom.leftContext.length + atom.rightContext.length + 2 := by
            dsimp only [SpineAtom.codBoundaryLength]
            rw [cupCod]
            exact Nat.add_right_comm atom.leftContext.length 2 atom.rightContext.length
          have hdom : atom.domBoundaryLength = atom.leftContext.length + atom.rightContext.length := by
            dsimp only [SpineAtom.domBoundaryLength]
            rw [cupDom, Nat.add_zero]
          have raiseTwo : atom.codBoundaryLength = state.openWires.length + 2 := by
            rw [hcod, ← headFires, hdom]
          have tailChainedAtStep :
              SpineBoundaryChained (stepAtom state atom).openWires.length rest := by
            rw [stepTracks]; exact tailChained
          have ih := stringPureCupBlock_widthTelescope rest restCup (stepAtom state atom) tailChainedAtStep
          show (processSpine (stepAtom state atom) rest).openWires.length
            = state.openWires.length + 2 * (rest.length + 1)
          rw [ih, stepTracks, raiseTwo, Nat.mul_succ, Nat.add_comm (2 * rest.length) 2,
            ← Nat.add_assoc]

/-! ## The length-determinacy corollaries -/

/-- The from-scratch seed for a bottom count: `bottomCount` open wires `0 … bottomCount-1`, no links.  String
`WT`-suffixed copy (signature-free carrier; distinct global name from the walking-adjunction `bottomSeed`). -/
private def stringBottomSeed (bottomCount : Nat) : WireState :=
  ⟨List.range bottomCount, [], bottomCount, 0⟩

/-- The seed's open-wire count is the bottom count. -/
private theorem stringBottomSeed_openWiresLength (bottomCount : Nat) :
    (stringBottomSeed bottomCount).openWires.length = bottomCount := by
  dsimp only [stringBottomSeed]
  exact rangeLengthWT bottomCount

/-- ★ **String cap length-determinacy.**  Two pure-cap blocks chained from the same bottom count whose mid-widths
(the open-wire counts after processing) agree have equal length: the cap telescope gives `midWidth + 2 · capLength
= bottomCount` for each, so equal mid-widths cancel to equal lengths. -/
theorem stringCapLength_eq_of_midWidth_eq
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (capBlockFirst capBlockSecond :
      List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (capPureFirst : AllCapArity capBlockFirst) (capPureSecond : AllCapArity capBlockSecond)
    (capChainedFirst : SpineBoundaryChained bottomCount capBlockFirst)
    (capChainedSecond : SpineBoundaryChained bottomCount capBlockSecond)
    (midEq : (processSpine (stringBottomSeed bottomCount) capBlockFirst).openWires.length
      = (processSpine (stringBottomSeed bottomCount) capBlockSecond).openWires.length) :
    capBlockFirst.length = capBlockSecond.length := by
  have seedLen := stringBottomSeed_openWiresLength bottomCount
  have telescopeFirst :
      (processSpine (stringBottomSeed bottomCount) capBlockFirst).openWires.length
        + 2 * capBlockFirst.length = bottomCount := by
    have chained : SpineBoundaryChained (stringBottomSeed bottomCount).openWires.length capBlockFirst := by
      rw [seedLen]; exact capChainedFirst
    have telescope :=
      stringPureCapBlock_widthTelescope capBlockFirst capPureFirst (stringBottomSeed bottomCount) chained
    rw [seedLen] at telescope
    exact telescope
  have telescopeSecond :
      (processSpine (stringBottomSeed bottomCount) capBlockSecond).openWires.length
        + 2 * capBlockSecond.length = bottomCount := by
    have chained : SpineBoundaryChained (stringBottomSeed bottomCount).openWires.length capBlockSecond := by
      rw [seedLen]; exact capChainedSecond
    have telescope :=
      stringPureCapBlock_widthTelescope capBlockSecond capPureSecond (stringBottomSeed bottomCount) chained
    rw [seedLen] at telescope
    exact telescope
  -- `midB + 2·lenA = bc = midB + 2·lenB` (after `midEq`), so `2·lenA = 2·lenB`, hence `lenA = lenB`.
  have doubled : 2 * capBlockFirst.length = 2 * capBlockSecond.length := by
    rw [midEq] at telescopeFirst
    refine natAddLeftCancelWT
      (sharedLeft := (processSpine (stringBottomSeed bottomCount) capBlockSecond).openWires.length) ?_
    rw [telescopeFirst, telescopeSecond]
  exact Nat.eq_of_mul_eq_mul_left (by decide) doubled

/-- ★ **String cup length-determinacy.**  Two pure-cup blocks chained from their respective mid-widths, with equal
mid-widths AND equal whole-valley FINAL widths, have equal length: the cup telescope gives `finalWidth = midWidth +
2 · cupLength` for each, so equal mid- and final-widths cancel to equal lengths.  The final-width equality is
supplied by the assembly from the shared top boundary. -/
theorem stringCupLength_eq_of_midWidth_eq_of_finalWidth_eq
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (midStateFirst midStateSecond : WireState)
    (cupBlockFirst cupBlockSecond :
      List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (cupPureFirst : AllCupArity cupBlockFirst) (cupPureSecond : AllCupArity cupBlockSecond)
    (cupChainedFirst : SpineBoundaryChained midStateFirst.openWires.length cupBlockFirst)
    (cupChainedSecond : SpineBoundaryChained midStateSecond.openWires.length cupBlockSecond)
    (midEq : midStateFirst.openWires.length = midStateSecond.openWires.length)
    (finalEq : (processSpine midStateFirst cupBlockFirst).openWires.length
      = (processSpine midStateSecond cupBlockSecond).openWires.length) :
    cupBlockFirst.length = cupBlockSecond.length := by
  have telescopeFirst :
      (processSpine midStateFirst cupBlockFirst).openWires.length
        = midStateFirst.openWires.length + 2 * cupBlockFirst.length :=
    stringPureCupBlock_widthTelescope cupBlockFirst cupPureFirst midStateFirst cupChainedFirst
  have telescopeSecond :
      (processSpine midStateSecond cupBlockSecond).openWires.length
        = midStateSecond.openWires.length + 2 * cupBlockSecond.length :=
    stringPureCupBlock_widthTelescope cupBlockSecond cupPureSecond midStateSecond cupChainedSecond
  -- `mid + 2·lenA = finalA = finalB = mid + 2·lenB` (after `midEq`), so `2·lenA = 2·lenB`.
  have doubled : 2 * cupBlockFirst.length = 2 * cupBlockSecond.length := by
    refine natAddLeftCancelWT (sharedLeft := midStateSecond.openWires.length) ?_
    rw [← midEq, ← telescopeFirst, finalEq, telescopeSecond, midEq]
  exact Nat.eq_of_mul_eq_mul_left (by decide) doubled

/-! ## Concrete truth-probes (anti-vacuity) — genuine string cap `ε` and cup `η'` at `tip` -/

/-- A concrete CAP spine atom at `tip`: the lower counit `ε : G·F ⇒ id_tip` with empty whiskering contexts.  Dom
`G·F` (length `2`), cod `id_tip` (length `0`), window `2` — a genuine cap. -/
def stringWidthTelescopeProbeCapAtom :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip :=
  ⟨AdjointTripleMode.tip, AdjointTripleMode.tip,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    stringGF, ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    StringTwoCell.counitLower,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip⟩

/-- A concrete CUP spine atom at `tip`: the upper unit `η' : id_tip ⇒ G·H` with empty whiskering contexts.  Dom
`id_tip` (length `0`), cod `G·H` (length `2`), window `0` — a genuine cup, the same-endpoint partner of the cap
probe. -/
def stringWidthTelescopeProbeCupAtom :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip :=
  ⟨AdjointTripleMode.tip, AdjointTripleMode.tip,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    stringGH, StringTwoCell.unitUpper,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip⟩

/-- The cap-probe seed at width `2`: two open wires `0, 1`, no links — the entry boundary a single cap `ε`
consumes. -/
def stringWidthTelescopeProbeCapSeed : WireState := ⟨[0, 1], [], 2, 0⟩

/-- The cup-probe seed at width `0`: no open wires — the mid boundary a single cup `η'` opens two wires from. -/
def stringWidthTelescopeProbeCupSeed : WireState := ⟨[], [], 0, 0⟩

/-- ★ **The cap width telescope FIRES on a genuine string cap.**  On the concrete cap `[ε]` from the width-`2`
seed, the telescope yields `finalWidth + 2 · 1 = 2` — the cap really does drop the open-wire count by two, computed
end-to-end through `processSpine`.  A machine-checked non-vacuity witness that the cap telescope is not vacuous on a
real string cap. -/
theorem stringPureCapBlock_widthTelescope_firesOnCapProbe :
    (processSpine stringWidthTelescopeProbeCapSeed [stringWidthTelescopeProbeCapAtom]).openWires.length
      + 2 * [stringWidthTelescopeProbeCapAtom].length
      = stringWidthTelescopeProbeCapSeed.openWires.length :=
  stringPureCapBlock_widthTelescope [stringWidthTelescopeProbeCapAtom]
    (AllCapArity.cons rfl rfl AllCapArity.nil) stringWidthTelescopeProbeCapSeed
    (SpineBoundaryChained.cons stringWidthTelescopeProbeCapAtom rfl (SpineBoundaryChained.nil 0))

/-- ★ **The cup width telescope FIRES on a genuine string cup.**  On the concrete cup `[η']` from the width-`0`
seed, the telescope yields `finalWidth = 0 + 2 · 1` — the cup really does raise the open-wire count by two,
computed end-to-end through `processSpine`.  A machine-checked non-vacuity witness that the cup telescope is not
vacuous on a real string cup. -/
theorem stringPureCupBlock_widthTelescope_firesOnCupProbe :
    (processSpine stringWidthTelescopeProbeCupSeed [stringWidthTelescopeProbeCupAtom]).openWires.length
      = stringWidthTelescopeProbeCupSeed.openWires.length + 2 * [stringWidthTelescopeProbeCupAtom].length :=
  stringPureCupBlock_widthTelescope [stringWidthTelescopeProbeCupAtom]
    (AllCupArity.cons rfl rfl AllCupArity.nil) stringWidthTelescopeProbeCupSeed
    (SpineBoundaryChained.cons stringWidthTelescopeProbeCupAtom rfl (SpineBoundaryChained.nil 2))

/-- ★ **The cap length-determinacy FIRES on genuine string caps.**  Instantiating `stringCapLength_eq_of_midWidth_eq`
on the concrete cap block `[ε]` (as both arguments, equal mid-widths by `rfl`) runs the full corollary machinery —
both telescopes and the `2 ·` cancellation — on a real string cap, confirming the corollary is instantiable (not
vacuous) at the three-colour signature. -/
theorem stringCapLength_eq_of_midWidth_eq_firesOnCapProbe :
    [stringWidthTelescopeProbeCapAtom].length = [stringWidthTelescopeProbeCapAtom].length :=
  stringCapLength_eq_of_midWidth_eq 2
    [stringWidthTelescopeProbeCapAtom] [stringWidthTelescopeProbeCapAtom]
    (AllCapArity.cons rfl rfl AllCapArity.nil) (AllCapArity.cons rfl rfl AllCapArity.nil)
    (SpineBoundaryChained.cons stringWidthTelescopeProbeCapAtom rfl (SpineBoundaryChained.nil 0))
    (SpineBoundaryChained.cons stringWidthTelescopeProbeCapAtom rfl (SpineBoundaryChained.nil 0))
    rfl

/-- ★ **The cup length-determinacy FIRES on genuine string cups.**  Instantiating
`stringCupLength_eq_of_midWidth_eq_of_finalWidth_eq` on the concrete cup block `[η']` (as both arguments, equal mid-
and final-widths by `rfl`) runs the full corollary machinery — both telescopes and the `2 ·` cancellation — on a
real string cup, confirming the corollary is instantiable (not vacuous) at the three-colour signature. -/
theorem stringCupLength_eq_of_midWidth_eq_of_finalWidth_eq_firesOnCupProbe :
    [stringWidthTelescopeProbeCupAtom].length = [stringWidthTelescopeProbeCupAtom].length :=
  stringCupLength_eq_of_midWidth_eq_of_finalWidth_eq
    stringWidthTelescopeProbeCupSeed stringWidthTelescopeProbeCupSeed
    [stringWidthTelescopeProbeCupAtom] [stringWidthTelescopeProbeCupAtom]
    (AllCupArity.cons rfl rfl AllCupArity.nil) (AllCupArity.cons rfl rfl AllCupArity.nil)
    (SpineBoundaryChained.cons stringWidthTelescopeProbeCupAtom rfl (SpineBoundaryChained.nil 2))
    (SpineBoundaryChained.cons stringWidthTelescopeProbeCupAtom rfl (SpineBoundaryChained.nil 2))
    rfl rfl

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the string Piece-I length-determinacy core (M2 width telescopes) is SHIPPED, zero-axiom.**
The two width telescopes (`stringPureCapBlock_widthTelescope` / `stringPureCupBlock_widthTelescope`) turn a
boundary-chained pure-cap / pure-cup block over the walking ADJOINT-TRIPLE signature into the exact additive width
shift (`∓ 2 · length`), riding the shipped `{signature}`-generic per-atom boundary tracker
`stepAtom_openWires_tracksBoundary`.  The two determinacy corollaries (`stringCapLength_eq_of_midWidth_eq`,
`stringCupLength_eq_of_midWidth_eq_of_finalWidth_eq`) cancel the telescopes to force `capLengthEq` / `cupLengthEq`
from equal mid-widths (and, for cups, equal whole-valley final widths).  The width accounting is colour-BLIND — it
reads only the arity `(2, 0)` / `(0, 2)`, never the `F ≠ H` species distinction — so each is a byte-identical
token-swap of the walking-adjunction original.  The truth-probes fire both telescopes on a genuine string cap
`ε : G·F ⇒ id_tip` (width `2 → 0`) and a genuine string cup `η' : id_tip ⇒ G·H` (width `0 → 2`), and instantiate
both corollaries on real string blocks, so no port is vacuous.

  What this marker does NOT close (honestly), and what `StringMidZeroValleyTraceEquiv`
  (`StringValleyDegenerateSplit`) still needs to inhabit:
    * the mid-width equality from equal boundary matching — the string clone of `survivorTopTotal_eq_midWidth`,
      whose ~800-line seed-fact subtree (`processSpine_*_ofAll{Cap,Cup}Arity_seed`) is un-cloned (M2's remaining leg);
    * the two whole-matching-to-block splitters `stringSameWholeMatching_{cap,cup}BlockMatchingEq` (the cap half
      rides the ~1556-line colour-blind `capRestrict_reconstructs` subtree, still un-cloned);
    * the floor-`0` cup-block reconstruct `StringMidZeroCupBlockReconstruct` (the ~560-line shift-simulation port, M3).

  So `StringMidZeroValleyTraceEquiv` stays UNINHABITED, and `fxString_hasAdjointTripleCompleteness`
  (`StringMatchingCompleteness`) and `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) stay `false`.  This
  round flips ONLY this NEW marker: the M2 width telescopes are shipped as one brick beneath one of the mid-zero
  producer's three residuals.  `= true`. -/
def fxString_hasSpineValleyWidthTelescope : Bool := true

end FX1Poly.Polygraph
