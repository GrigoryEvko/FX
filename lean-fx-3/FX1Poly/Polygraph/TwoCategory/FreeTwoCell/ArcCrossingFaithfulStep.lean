import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingBoxArmCorruption
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking

/-! # MODE-COMMUTE — the CORRECTED crossing arm as an additive sibling (faithful `2⇒2` transposition)

`ArcCrossingBoxArmCorruption` (r6) machine-witnessed that `stepArcAtom`'s generic box arm is ACTIVELY WRONG on
a `2⇒2` crossing: on the width-4 probe state `[10,11,12,13]` it collapses the open wires to two fresh
disconnected ids `[20,21]` (width `4 ⇒ 2`) and bypasses the union-find forest entirely.  The arc engine is
INTENTIONALLY cup/cap-locked, so the box arm is never reached at the walking-adjunction seed; but reached it
would return a wrong extract.

This file ships the FAITHFUL crossing arm as a strictly ADDITIVE SIBLING.  The shipped `stepArcAtom` is NEVER
edited.  `stepArcAtomFaithful` is a byte-for-byte copy of `stepArcAtom` with ONE new arm inserted before the
catch-all: a `2⇒2` generator fires `stepCrossArc`, an adjacent transposition of the two live open wires that
PRESERVES width, leaves the forest untouched, and allocates no fresh id and no arc event.  This is the
geometrically-faithful model of a SYMMETRIC crossing (a genuine braid's over/under sign is extra data the
position swap does not carry — that lives in the Brauer `stepWiring` / `WiringDesc` engine; out of scope here).

## Why the position swap, adjudicated

`extractArc` / `SameArcPartition` read the boundary through `natListGetAt boundaryNodes index` — POSITIONALLY,
so they are sensitive to `openWires` order precisely up to same-component reordering.  An adjacent transposition
of two open wires therefore produces a genuinely distinct extract exactly when the two crossed strands lie in
different components (two ports of one component are interchangeable; two strands in different components are
not).  A no-op crossing arm would falsely identify a crossing with the identity; the position swap is the
faithful model.

## The conservative-refinement theorem

The corrected engine AGREES with the shipped one everywhere the shipped one is faithful (every cup / cap atom:
`stepArcAtomFaithful_eq_stepArcAtom_of_cupOrCap`) and diverges only where the shipped one is CORRUPT (the `2⇒2`
box arm).  At the walking-adjunction seed every spine atom is a cup or a cap
(`adjunctionSpineAtom_hasCupOrCapArity`), so the two extracts coincide there
(`arcStructureOfFaithful_eq_arcStructureOf_adjunction`) — the shipped soundness (`snake_arcStructureOf`,
`identityOnLeft_arcStructureOf`) transports through the agreement.

## What this file does NOT do

It does NOT extend the general-signature peel to crossings and it does NOT flip the general keystone.  The
general-signature peel `ArcGodementSamePartitionFresh signature` stays open
(`fxMode_hasArcGodementSamePartitionFreshProof` stays `false`, the #2043 / WP-AMALG residual), and
`fxMode_hasArcPeelGeneralSignature` stays `false`.  Wiring the faithful crossing arm into
`arcSwapCorePackage_of_adjunctionSwap` (a general-signature dispatcher plus re-proving the partition
independence for crossings) is the next round.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `WellFounded.fix`.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The faithful transposition on the open-wire list -/

/-- Swap the two open wires at `position` and `position + 1` — a faithful adjacent transposition, built from the
shipped `natListGetAt` / `natListRemoveTwoAt` / `natListInsertAt` helpers.  Remove the pair, then splice back the
same two ids in swapped order.  Structural, propext-free (only the shipped helpers). -/
def natListSwapTwoAt (openWires : List Nat) (position : Nat) : List Nat :=
  natListInsertAt (natListRemoveTwoAt openWires position) position
    [natListGetAt openWires (position + 1), natListGetAt openWires position]

/-- Process a single CROSSING (a faithful `2⇒2` symmetric braid generator): transpose the two live open wires
at `position`.  Width is PRESERVED (two consumed, two produced), the union-find forest is UNTOUCHED (a symmetric
crossing permutes the two strands' boundary positions, not their connectivity), no fresh id is allocated and NO
arc event is recorded (a crossing is not a turnback).  Contrast the shipped box arm, which drops four wires,
splices two fresh disconnected ids, and bypasses the forest.  This transposition acts on `extractArc` by the
boundary-index adjacent transposition `transposeAdjacent (bottomCount + position)` of the two crossed ports: it
UNCONDITIONALLY swaps the two per-port internal cup/cap count entries and conjugates the same-component relation
(`internalCupCounts_stepCrossArc_eq_swap` / `crossBoundarySameComponent_equivariant` in
`ArcCrossingEquivariantTransport`), while the `partner` field follows that σ-conjugation only in the
perfect-matching regime (each boundary component ≤ 2 ports) — the equivariance content the r8 transport lands. -/
def stepCrossArc (state : ArcWireState) (position : Nat) : ArcWireState :=
  { state with openWires := natListSwapTwoAt state.openWires position }

/-- Process one spine atom with the CORRECTED crossing arm: a `0⇒2` cup and a `2⇒0` cap fire exactly as the
shipped `stepArcAtom` does (`stepCupArc` / `stepCapArc`), a `2⇒2` crossing fires the faithful `stepCrossArc`, and
any OTHER arity keeps the shipped generic box arm verbatim as the opaque-box fallback.  The `| 2, 2 =>` arm is a
concrete literal pair (not a wildcard) so the match stays propext-free.  Additive sibling of `stepArcAtom`; the
shipped dispatcher is never edited. -/
def stepArcAtomFaithful {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode) : ArcWireState :=
  let position := atom.leftContext.length
  match atom.generatorDom.length, atom.generatorCod.length with
  | 0, 2 => stepCupArc state position
  | 2, 0 => stepCapArc state position
  | 2, 2 => stepCrossArc state position
  | numConsumed, numProduced =>
      let droppedWires :=
        Nat.rec state.openWires (fun _ shorter => natListRemoveTwoAt shorter position) numConsumed
      { openWires := natListInsertAt droppedWires position (List.range numProduced |>.map (· + state.nextFresh)),
        links := state.links,
        nextFresh := state.nextFresh + numProduced,
        loops := state.loops,
        cupEventNodes := state.cupEventNodes,
        capEventNodes := state.capEventNodes }

/-- Fold the corrected per-atom step over a whole spine, bottom-to-top (head first) — the faithful twin of
`processArcSpine`. -/
def processArcSpineFaithful {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atoms : List (SpineAtom signature sourceMode targetMode)) : ArcWireState :=
  atoms.foldl stepArcAtomFaithful state

/-- Read a flat spine list into its `FullArcStructure` via the corrected fold — the faithful twin of
`arcStructureOfSpineList`. -/
def arcStructureOfSpineListFaithful {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (atoms : List (SpineAtom signature sourceMode targetMode)) : FullArcStructure :=
  extractArc bottomCount
    (processArcSpineFaithful (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms)

/-- The full planar-arc structure of a free 2-cell read through the CORRECTED crossing engine — the faithful
twin of `arcStructureOf`. -/
def arcStructureOfFaithful {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) : FullArcStructure :=
  arcStructureOfSpineListFaithful sourcePath.length cell.spine

/-! ## The corrected crossing PRESERVES width and the forest (machine-witnessed on the r6 probe) -/

/-- ★ **The faithful crossing PRESERVES wire width** — on the r6 width-4 probe state the corrected arm keeps
`4` open wires (contrast the box arm's `4 ⇒ 2` deficit).  `rfl`. -/
theorem crossAtom_stepArcAtomFaithful_openWires_widthPreserved :
    (stepArcAtomFaithful crossingBoxProbeState crossAtom).openWires.length
      = crossingBoxProbeState.openWires.length := rfl

/-- ★ **The faithful crossing is an adjacent transposition** — on the probe the two front wires `10, 11` swap to
`[11, 10, 12, 13]` (the original ids survive, only their positions move; contrast the box arm's fresh pair
`[20, 21]`).  `rfl`. -/
theorem crossAtom_stepArcAtomFaithful_openWires_transposed :
    (stepArcAtomFaithful crossingBoxProbeState crossAtom).openWires = [11, 10, 12, 13] := rfl

/-- ★ **The faithful crossing leaves the union-find forest UNTOUCHED** — for EVERY state (the `2⇒2` arm only
permutes `openWires`).  A symmetric crossing permutes the two strands' boundary positions, not their
connectivity; the ids stay in exactly the components they were in.  General-state `rfl`. -/
theorem crossAtom_stepArcAtomFaithful_links_untouched (state : ArcWireState) :
    (stepArcAtomFaithful state crossAtom).links = state.links := rfl

/-- ★ **The faithful crossing allocates NO fresh id** — `nextFresh` is unchanged for EVERY state (contrast the
box arm's `+2` bump for its two disconnected fresh outputs).  General-state `rfl`. -/
theorem crossAtom_stepArcAtomFaithful_nextFresh_untouched (state : ArcWireState) :
    (stepArcAtomFaithful state crossAtom).nextFresh = state.nextFresh := rfl

/-- The faithful crossing records NO cup event (a crossing is not a turnback) — for every state.  `rfl`. -/
theorem crossAtom_stepArcAtomFaithful_recordsNoCupEvent (state : ArcWireState) :
    (stepArcAtomFaithful state crossAtom).cupEventNodes = state.cupEventNodes := rfl

/-- The faithful crossing records NO cap event — for every state.  `rfl`. -/
theorem crossAtom_stepArcAtomFaithful_recordsNoCapEvent (state : ArcWireState) :
    (stepArcAtomFaithful state crossAtom).capEventNodes = state.capEventNodes := rfl

/-! ## The symmetric R2 (double-crossing) involution — machine-witnessed on the probe -/

/-- ★ **Double crossing at the same position is the identity on the open wires** — the SYMMETRIC (Brauer / R2)
relation, definitional on the r6 probe state (`[10,11,12,13]` crossed twice returns to `[10,11,12,13]`).  The
position swap models a symmetric crossing; a genuine braid's over/under sign is extra data the position swap
does not carry (out of scope — that lives in the Brauer `stepWiring` engine).  `rfl`. -/
theorem stepCrossArc_involution_onProbe :
    (stepCrossArc (stepCrossArc crossingBoxProbeState 0) 0).openWires
      = crossingBoxProbeState.openWires := rfl

/-! ## Observability — the faithful crossing IS visible to the extract exactly up to same-component reordering

`extractArc` reads the boundary positionally, so it is sensitive to `openWires` order precisely up to
same-component reordering: crossing two ports of ONE component is invisible; crossing two strands of DIFFERENT
components changes the extract. -/

/-- A concrete DIFFERENT-component observability fixture: wire `10` carries cup-event `7`, wire `12` carries
cap-event `8`, wire `11` is its own component.  Crossing `10 ↔ 11` at the front moves the cup turnback from
port `0` to port `1`. -/
def crossingObservableState : ArcWireState :=
  { openWires := [10, 11, 12, 13],
    links := [(7, 10), (8, 12)],
    nextFresh := 20,
    loops := 0,
    cupEventNodes := [7],
    capEventNodes := [8] }

/-- The observable fixture's per-port internal cup counts BEFORE the crossing: the turnback sits on port `0`. -/
theorem crossing_observable_internalCupCounts_before :
    (extractArc 0 crossingObservableState).internalCupCounts = [1, 0, 0, 0] := rfl

/-- The observable fixture's per-port internal cup counts AFTER the crossing: the turnback has moved to port
`1`. -/
theorem crossing_observable_internalCupCounts_after :
    (extractArc 0 (stepCrossArc crossingObservableState 0)).internalCupCounts = [0, 1, 0, 0] := rfl

/-- ★ **The faithful crossing is OBSERVABLE on different-component strands** — the extract's per-port internal
cup counts differ after the crossing (`[0,1,0,0]` vs `[1,0,0,0]`): a genuine geometric change, not a no-op.  A
no-op crossing arm would falsely identify the crossing with the identity; the position swap does not.  Via the
head cup-count `0 ≠ 1`, propext-free. -/
theorem crossing_observable_extract_ne :
    extractArc 0 (stepCrossArc crossingObservableState 0) ≠ extractArc 0 crossingObservableState := by
  intro extractsEqual
  have countsEqual : (extractArc 0 (stepCrossArc crossingObservableState 0)).internalCupCounts
      = (extractArc 0 crossingObservableState).internalCupCounts :=
    congrArg FullArcStructure.internalCupCounts extractsEqual
  rw [crossing_observable_internalCupCounts_after, crossing_observable_internalCupCounts_before]
    at countsEqual
  have headEq : (0 : Nat) = 1 := congrArg (fun counts => natListGetAt counts 0) countsEqual
  exact Nat.noConfusion headEq

/-- ★ **The faithful crossing is INVISIBLE on same-component ports** — on the r6 probe state (wires `10, 11`
share the component `{7, 10, 11}` via the `11 → 10` edge), crossing them leaves the extract IDENTICAL.  Two
ports of one strand are interchangeable, exactly as geometry demands.  `rfl`. -/
theorem crossing_sameComponent_extract_unchanged :
    extractArc 0 (stepCrossArc crossingBoxProbeState 0) = extractArc 0 crossingBoxProbeState := rfl

/-! ## The conservative-refinement agreement: faithful = shipped on every cup / cap -/

/-- ★ **On a cup or a cap the corrected engine EQUALS the shipped one.**  Both dispatch on the same arity match;
a `0⇒2` cup routes both to `stepCupArc`, a `2⇒0` cap routes both to `stepCapArc`.  The new `2⇒2` arm and the box
fallback are unreachable under the cup/cap arity hypothesis, so the two definitions coincide.  Mirrors
`stepArcAtom_openWires_tracksBoundary`'s arity dispatch (`cases arity`; rewrite the two length scrutinees to their
concrete values so both matches reduce). -/
theorem stepArcAtomFaithful_eq_stepArcAtom_of_cupOrCap {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom) :
    stepArcAtomFaithful state atom = stepArcAtom state atom := by
  cases arity with
  | inl cupArity =>
      obtain ⟨domZero, codTwo⟩ := cupArity
      dsimp only [stepArcAtomFaithful, stepArcAtom]
      rw [domZero, codTwo]
  | inr capArity =>
      obtain ⟨domTwo, codZero⟩ := capArity
      dsimp only [stepArcAtomFaithful, stepArcAtom]
      rw [domTwo, codZero]

/-- ★ **On a spine of only cup / cap atoms the two folds agree.**  Structural induction on the spine, threading
the per-atom agreement through each `foldl` step. -/
theorem processArcSpineFaithful_eq_processArcSpine_of_allCupOrCap {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (cupOrCap : ∀ (atom : SpineAtom signature sourceMode targetMode), AtomHasCupOrCapArity atom)
    (atoms : List (SpineAtom signature sourceMode targetMode)) :
    ∀ (state : ArcWireState), processArcSpineFaithful state atoms = processArcSpine state atoms := by
  induction atoms with
  | nil => intro state; rfl
  | cons atom rest inductionHypothesis =>
      intro state
      show rest.foldl stepArcAtomFaithful (stepArcAtomFaithful state atom)
         = rest.foldl stepArcAtom (stepArcAtom state atom)
      rw [stepArcAtomFaithful_eq_stepArcAtom_of_cupOrCap state atom (cupOrCap atom)]
      exact inductionHypothesis (stepArcAtom state atom)

/-- ★ **At the walking-adjunction seed the two extracts COINCIDE.**  Every adjunction spine atom is a cup or a
cap (`adjunctionSpineAtom_hasCupOrCapArity`), so the corrected engine's extract equals the shipped
`arcStructureOf` — a CONSERVATIVE refinement: the faithful crossing arm never fires at the seed, so all shipped
soundness (`snake_arcStructureOf`, `identityOnLeft_arcStructureOf`, the snake-gap crux) transports verbatim. -/
theorem arcStructureOfFaithful_eq_arcStructureOf_adjunction
    {sourceMode targetMode : adjunctionModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    arcStructureOfFaithful cell = arcStructureOf cell := by
  dsimp only [arcStructureOfFaithful, arcStructureOf, arcStructureOfSpineListFaithful,
    arcStructureOfSpineList]
  rw [processArcSpineFaithful_eq_processArcSpine_of_allCupOrCap
      adjunctionSpineAtom_hasCupOrCapArity cell.spine
      (ArcWireState.mk (List.range sourcePath.length) [] sourcePath.length 0 [] [])]

/-! ## Honesty markers -/

/-- **Honesty marker — the CORRECTED crossing arm is shipped as an additive sibling.**  `stepCrossArc` /
`stepArcAtomFaithful` model a `2⇒2` symmetric crossing FAITHFULLY: width is preserved
(`crossAtom_stepArcAtomFaithful_openWires_widthPreserved`, contrast the box arm's `4 ⇒ 2`), the ids are
transposed not replaced (`crossAtom_stepArcAtomFaithful_openWires_transposed`), the forest and `nextFresh` are
untouched (`_links_untouched` / `_nextFresh_untouched`), and the crossing is observable exactly up to
same-component reordering (`crossing_observable_extract_ne` / `crossing_sameComponent_extract_unchanged`).  The
engine is a CONSERVATIVE refinement of the shipped one — it agrees on every cup / cap
(`stepArcAtomFaithful_eq_stepArcAtom_of_cupOrCap`) and at the whole walking-adjunction seed
(`arcStructureOfFaithful_eq_arcStructureOf_adjunction`), diverging only where the shipped box arm is CORRUPT.
The shipped `stepArcAtom` is NEVER edited.  `= true`. -/
def fxMode_hasArcCrossingFaithfulStep : Bool := true

/-- **Honesty pin — the shipped box arm stays corrupt (the r6 witness is untouched).**  This additive sibling
does not edit `stepArcAtom`; `fxMode_hasArcCrossingBoxArmCorruption` stays `true`.  `rfl`. -/
theorem arcCrossingFaithful_boxArmCorruption_stays_true :
    fxMode_hasArcCrossingBoxArmCorruption = true := rfl

/-- **Honesty pin — the general-signature peel stays the open keystone.**  The faithful crossing arm supplies a
real `2⇒2` step, but wiring it into `arcSwapCorePackage_of_adjunctionSwap` (a general-signature dispatcher plus
re-proving the partition independence for crossings) is the next round; `fxMode_hasArcPeelGeneralSignature` stays
`false`.  `rfl`. -/
theorem arcCrossingFaithful_generalSignature_stays_false :
    fxMode_hasArcPeelGeneralSignature = false := rfl

/-- **Honesty pin — the #2043 / WP-AMALG fresh-partition keystone is untouched.**  The general-signature peel is
exactly `ArcGodementSamePartitionFresh signature`; the corrected engine does not advance it.
`fxMode_hasArcGodementSamePartitionFreshProof` stays `false`.  `rfl`. -/
theorem arcCrossingFaithful_samePartitionFreshProof_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
