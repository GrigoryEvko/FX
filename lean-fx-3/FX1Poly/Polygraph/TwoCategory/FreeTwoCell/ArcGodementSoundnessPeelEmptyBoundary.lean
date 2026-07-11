import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcGodementSoundnessPeel
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineArityDiscipline
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # mode-3 floor — the Godement arc soundness CLOSED at the EMPTY boundary (n = 0), via a counter-shift proxy

`FreeTwoCellArcGodementSoundnessPeel` closed the walking-adjunction arc soundness for NON-empty source boundaries
(`arcStructureOf_sound_of_convFull_adjunction`, gated on `0 < sourcePath.length`): the shipped peel
`extractArc_eq_of_atomicTraceEquiv` needs `0 < nextFresh`, which fails at the canonical empty-boundary fold seed
`ArcWireState.mk (List.range 0) [] 0 0 [] []` = `mk [] [] 0 0 [] []` (nextFresh `0`).  Its wall marker is
`fxMode_hasArcGodementSoundnessPeelEmptyBoundary = false`.

This file DISCHARGES the empty-boundary case through the counter-shift PROXY (the arc analog of the matching
route's `MatchingCounterShift` / `MatchingEmptyBoundary`, but READ OFF the shipped arc renaming-equivariance —
strictly less bookkeeping):

  ★ `renameStateShift` + `processArcSpine_renameStateShift_ofChain` — the arc fold is EQUIVARIANT under a GLOBAL
    `(· + delta)` counter-shift, along a boundary-CHAINED cup/cap-disciplined spine (the cap's in-range wire reads
    are exactly the chain discipline; the cup / box arms commute unconditionally).  The renaming atoms
    (`natListInsertAt_map`, `renameLinks_unionFindJoin`, `natListGetAt_map_inRange`, `unionFindRootOf_rename`,
    `countEventsInRoot_rename`) are all shipped in `ArcSwapRenameable`; only the counter-OFFSET plumbing is new.
  ★ `extractArcAfterProcessing_emptyBoundary_counterShift` — the payoff: a chained, cup/cap-disciplined spine
    extracts IDENTICALLY from the degenerate seed `mk [] [] 0 0 [] []` (where the peel's `0 < nextFresh` fails)
    and the proxy seed `mk [] [] 1 0 [] []` (where it holds).  The two folds are `(· + 1)`-shift-related
    (`processArcSpine_renameStateShift_ofChain`), and the shift feeds the shipped `ArcRenameRel` read-off
    (`sameArcPartition_of_renameRel` + `extractArc_eq_of_sameArcPartition`) — at the empty bottom boundary there
    are NO fixed ports, so the everywhere-moving shift needs no `σ 0 = 0`.
  ★ `arcStructureOf_sound_of_convFull_adjunction_emptyBoundary` — the empty-boundary soundness leg: the peel FIRES
    from the proxy seed (fresh, forest, `0 < 1`, `0 ≤ 1`, empty-boundary-tracked, chained), and the counter-shift
    bridge exchanges the degenerate seed for the proxy on BOTH trace-equivalent spines (chain and arity
    transported along the equivalence).  At the adjunction the cup/cap discipline is AUTOMATIC
    (`adjunctionSpineAtom_hasCupOrCapArity`), so — unlike the matching template — NO `CellHasCupCapGenerators`
    hypothesis is owed.
  ★ `arcStructureOf_sound_of_convFull_adjunction_allBoundaries` — the TOTAL capstone: `arcStructureOf` is invariant
    under the COMPLETE `TwoCellConvFull` at the walking adjunction at EVERY source boundary, dispatching on the
    boundary length (positive via the shipped peel, empty via the counter-shift proxy).

## What is honest-DEFERRED

The GENERAL-signature soundness stays walled (the peel is `adjunctionModeSignature`-hardcoded through its 2×2
cup/cap swap dispatcher — see `FreeTwoCellArcPeelSignatureCeiling`), and the freshness-conditioned partition
residual `ArcGodementSamePartitionFresh` (`fxMode_hasArcGodementSamePartitionFreshProof`) — the #2043 UPSTREAM
half — is untouched: this file advances SOUNDNESS at the adjunction to all boundaries, it does NOT close the
general upstream residual (`arcPeelClosesAdjunctionSoundnessButNotGeneralUpstream` records exactly that state).

Raw Lean 4 + Init; the counter-shift fold is structural recursion threading the chain / arity discipline through
the shipped renaming atoms (the leg reorderings are `Nat.add_right_comm`).  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The global counter-shift and its injectivity -/

/-- Rename every wire / link / event id of an arc state by `(· + delta)` AND bump `nextFresh` by `delta` — the
counter-OFFSET clone of `renameState` (which holds `nextFresh` fixed).  This relates a fold to the SAME fold
seeded at a higher counter: the empty-boundary proxy. -/
def renameStateShift (delta : Nat) (state : ArcWireState) : ArcWireState :=
  { openWires := state.openWires.map (· + delta),
    links := renameLinks (· + delta) state.links,
    nextFresh := state.nextFresh + delta,
    loops := state.loops,
    cupEventNodes := state.cupEventNodes.map (· + delta),
    capEventNodes := state.capEventNodes.map (· + delta) }

/-- `(· + delta)` cancels on the right — hand-rolled (core `Nat.add_right_cancel` leaks `propext`).  Structural
recursion on `delta`. -/
theorem addRightInjectiveShift : (delta a b : Nat) → a + delta = b + delta → a = b
  | 0, _, _, equalSums => equalSums
  | delta + 1, a, b, equalSums => addRightInjectiveShift delta a b (Nat.succ.inj equalSums)

/-- The global counter-shift `(· + delta)` is injective. -/
theorem shiftInjective (delta : Nat) : ∀ a b, (· + delta) a = (· + delta) b → a = b :=
  fun a b equalImages => addRightInjectiveShift delta a b equalImages

/-! ## The arc step reduces to `stepCupArc` / `stepCapArc` under an arity read-off -/

/-- A `0 ⇒ 2` (cup) atom's arc step IS `stepCupArc` at its window position. -/
theorem stepArcAtom_eq_stepCupArc {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (domZero : atom.generatorDom.length = 0) (codTwo : atom.generatorCod.length = 2) :
    stepArcAtom state atom = stepCupArc state atom.leftContext.length := by
  unfold stepArcAtom
  rw [domZero, codTwo]

/-- A `2 ⇒ 0` (cap) atom's arc step IS `stepCapArc` at its window position. -/
theorem stepArcAtom_eq_stepCapArc {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (domTwo : atom.generatorDom.length = 2) (codZero : atom.generatorCod.length = 0) :
    stepArcAtom state atom = stepCapArc state atom.leftContext.length := by
  unfold stepArcAtom
  rw [domTwo, codZero]

/-! ## The cup / cap steps commute with the counter-shift -/

/-- A CUP step commutes with the global counter-shift.  The shifted state's fresh legs are the base legs `+ delta`
(so `(· + delta)` sends each on the nose), the splice via `natListInsertAt_map`, the two unions via
`renameLinks_unionFindJoin`; the leg reorderings are `Nat.add_right_comm`. -/
theorem stepCupArc_renameStateShift (delta : Nat) (state : ArcWireState) (position : Nat) :
    stepCupArc (renameStateShift delta state) position
      = renameStateShift delta (stepCupArc state position) := by
  dsimp only [stepCupArc, renameStateShift, List.map]
  rw [natListInsertAt_map (· + delta) state.openWires position [state.nextFresh, state.nextFresh + 1],
      renameLinks_unionFindJoin (· + delta) (shiftInjective delta),
      renameLinks_unionFindJoin (· + delta) (shiftInjective delta),
      Nat.add_right_comm state.nextFresh delta 1,
      Nat.add_right_comm state.nextFresh delta 2,
      Nat.add_right_comm state.nextFresh delta 3]
  dsimp only [List.map]

/-- A CAP step commutes with the global counter-shift, PROVIDED its two wire reads are in range (`position + 1 <
openWires.length`).  The reads transport via `natListGetAt_map_inRange`, the loop test via `unionFindRootOf_rename`
+ `beq_congr_inj`, the unions via `renameLinks_unionFindJoin`; the event-node reorder is `Nat.add_right_comm`. -/
theorem stepCapArc_renameStateShift (delta : Nat) (state : ArcWireState) (position : Nat)
    (posSuccInRange : position + 1 < state.openWires.length) :
    stepCapArc (renameStateShift delta state) position
      = renameStateShift delta (stepCapArc state position) := by
  have posInRange : position < state.openWires.length :=
    Nat.lt_of_le_of_lt (Nat.le_succ position) posSuccInRange
  have loopTestsAgree : isSameComponent (renameLinks (· + delta) state.links)
        (natListGetAt (state.openWires.map (· + delta)) position)
        (natListGetAt (state.openWires.map (· + delta)) (position + 1))
      = isSameComponent state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)) := by
    dsimp only [isSameComponent]
    rw [natListGetAt_map_inRange (· + delta) state.openWires position posInRange,
        natListGetAt_map_inRange (· + delta) state.openWires (position + 1) posSuccInRange,
        unionFindRootOf_rename (· + delta) (shiftInjective delta),
        unionFindRootOf_rename (· + delta) (shiftInjective delta),
        beq_congr_inj (· + delta) (shiftInjective delta)]
  dsimp only [stepCapArc, renameStateShift, List.map]
  rw [natListRemoveTwoAt_map (· + delta) state.openWires position, loopTestsAgree,
      natListGetAt_map_inRange (· + delta) state.openWires position posInRange,
      natListGetAt_map_inRange (· + delta) state.openWires (position + 1) posSuccInRange,
      renameLinks_unionFindJoin (· + delta) (shiftInjective delta),
      renameLinks_unionFindJoin (· + delta) (shiftInjective delta),
      Nat.add_right_comm state.nextFresh delta 1]

/-- ★ **One arc step commutes with the counter-shift**, for a cup/cap-arity atom whose cap window is in range.
Cup via `stepCupArc_renameStateShift` (no read), cap via `stepCapArc_renameStateShift` (the in-range wire reads
supplied by `capReadable`).  The box arm never fires (the arity is cup or cap). -/
theorem stepArcAtom_renameStateShift {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (delta : Nat) (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (capReadable : atom.generatorDom.length = 2 → atom.leftContext.length + 1 < state.openWires.length) :
    stepArcAtom (renameStateShift delta state) atom = renameStateShift delta (stepArcAtom state atom) := by
  cases arity with
  | inl cupArity =>
      rw [stepArcAtom_eq_stepCupArc (renameStateShift delta state) atom cupArity.1 cupArity.2,
          stepArcAtom_eq_stepCupArc state atom cupArity.1 cupArity.2]
      exact stepCupArc_renameStateShift delta state atom.leftContext.length
  | inr capArity =>
      rw [stepArcAtom_eq_stepCapArc (renameStateShift delta state) atom capArity.1 capArity.2,
          stepArcAtom_eq_stepCapArc state atom capArity.1 capArity.2]
      exact stepCapArc_renameStateShift delta state atom.leftContext.length (capReadable capArity.1)

/-- ★ **The arc fold commutes with the counter-shift along a boundary-chained cup/cap-disciplined spine.**
Structural recursion on the spine: each head's cap window is in range because the chain discipline pins
`openWires.length = domBoundaryLength = leftContext.length + generatorDom.length + rightContext.length` and the
tail's boundary is tracked by `stepArcAtom_openWires_tracksBoundary`. -/
theorem processArcSpine_renameStateShift_ofChain {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (delta : Nat) :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : ArcWireState) →
    (boundaryLength : Nat) →
    SpineBoundaryChained boundaryLength atoms → SpineHasCupCapAtoms atoms →
    state.openWires.length = boundaryLength →
    processArcSpine (renameStateShift delta state) atoms
      = renameStateShift delta (processArcSpine state atoms)
  | [], _, _, _, _, _ => rfl
  | atom :: rest, state, _, chained, arity, tracks => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      obtain ⟨headArity, tailArity⟩ := spineHasCupCapAtoms_tail arity
      have entryShape : state.openWires.length
          = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length :=
        tracks.trans headFires.symm
      have capReadable : atom.generatorDom.length = 2 →
          atom.leftContext.length + 1 < state.openWires.length := by
        intro domTwo
        rw [entryShape, domTwo]
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (atom.leftContext.length + 1)) (Nat.le_add_right _ _)
      show processArcSpine (stepArcAtom (renameStateShift delta state) atom) rest
        = renameStateShift delta (processArcSpine (stepArcAtom state atom) rest)
      rw [stepArcAtom_renameStateShift delta state atom headArity capReadable]
      exact processArcSpine_renameStateShift_ofChain delta rest (stepArcAtom state atom)
        atom.codBoundaryLength tailChained tailArity
        (stepArcAtom_openWires_tracksBoundary state atom headArity entryShape)

/-! ## The extract is invariant under the counter-shift at the empty boundary -/

/-- A state and its counter-shift are `ArcRenameRel`-related at the EMPTY boundary (`bottomCount = 0`): the boundary
nodes are just the open wires (no fixed ports), so every field reads off the shipped renaming atoms without a
`σ 0 = 0` hypothesis. -/
theorem arcRenameRel_renameStateShift (delta : Nat) (state : ArcWireState) :
    ArcRenameRel 0 (· + delta) state (renameStateShift delta state) where
  lengthEq := mapLength (· + delta) state.openWires
  loopsEq := rfl
  inj := shiftInjective delta
  bnodeCorr := by
    intro index indexInRange
    have indexBelow : index < state.openWires.length := by
      have shifted := indexInRange
      rwa [Nat.zero_add] at shifted
    show natListGetAt (state.openWires.map (· + delta)) index
       = (· + delta) (natListGetAt state.openWires index)
    exact natListGetAt_map_inRange (· + delta) state.openWires index indexBelow
  rootComm := fun node => unionFindRootOf_rename (· + delta) (shiftInjective delta) state.links node
  cupCorr := fun rootNode =>
    countEventsInRoot_rename (· + delta) (shiftInjective delta) state.links rootNode state.cupEventNodes
  capCorr := fun rootNode =>
    countEventsInRoot_rename (· + delta) (shiftInjective delta) state.links rootNode state.capEventNodes

/-- The arc extract at the empty boundary is invariant under the global counter-shift: `extractArc 0 state =
extractArc 0 (renameStateShift delta state)`.  Composes `arcRenameRel_renameStateShift` with the shipped
`sameArcPartition_of_renameRel` + `extractArc_eq_of_sameArcPartition` (the event-node counts agree by
`mapLength`). -/
theorem extractArc_renameStateShift_emptyBoundary (delta : Nat) (state : ArcWireState) :
    extractArc 0 state = extractArc 0 (renameStateShift delta state) :=
  extractArc_eq_of_sameArcPartition 0 state (renameStateShift delta state)
    (sameArcPartition_of_renameRel 0 (· + delta) state (renameStateShift delta state)
      (arcRenameRel_renameStateShift delta state))
    (mapLength (· + delta) state.cupEventNodes).symm
    (mapLength (· + delta) state.capEventNodes).symm

/-! ## The empty-boundary counter-shift bridge -/

/-- ★ **The empty-boundary counter-shift bridge.**  A chained, cup/cap-disciplined spine extracts IDENTICALLY from
the degenerate seed `mk [] [] 0 0 [] []` (where the peel's `0 < nextFresh` fails) and the proxy seed
`mk [] [] 1 0 [] []` (where it holds): the two folds are `(· + 1)`-shift-related
(`processArcSpine_renameStateShift_ofChain`, since `renameStateShift 1 (mk [] [] 0 0 [] []) = mk [] [] 1 0 [] []`),
and the shift preserves the empty-boundary extract (`extractArc_renameStateShift_emptyBoundary`). -/
theorem extractArcAfterProcessing_emptyBoundary_counterShift {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atoms : List (SpineAtom signature sourceMode targetMode))
    (chained : SpineBoundaryChained 0 atoms) (arity : SpineHasCupCapAtoms atoms) :
    extractArc 0 (processArcSpine (ArcWireState.mk [] [] 0 0 [] []) atoms)
      = extractArc 0 (processArcSpine (ArcWireState.mk [] [] 1 0 [] []) atoms) := by
  have foldEq : processArcSpine (ArcWireState.mk [] [] 1 0 [] []) atoms
      = renameStateShift 1 (processArcSpine (ArcWireState.mk [] [] 0 0 [] []) atoms) :=
    processArcSpine_renameStateShift_ofChain 1 atoms (ArcWireState.mk [] [] 0 0 [] []) 0 chained arity rfl
  rw [foldEq]
  exact extractArc_renameStateShift_emptyBoundary 1
    (processArcSpine (ArcWireState.mk [] [] 0 0 [] []) atoms)

/-! ## The empty-boundary soundness leg and the total capstone -/

/-- ★ **The empty-boundary Godement arc soundness leg.**  At a degenerate source boundary
(`sourcePath.length = 0`) the canonical fold seed `mk [] [] 0 0 [] []` fails the peel's `0 < nextFresh`, so the
run is exchanged (via `extractArcAfterProcessing_emptyBoundary_counterShift`) for the same run from the PROXY seed
`mk [] [] 1 0 [] []`, where the shipped peel `extractArc_eq_of_atomicTraceEquiv` fires (fresh, forest, `0 < 1`,
`0 ≤ 1`, empty-boundary-tracked, chained); the bridge on the second spine (its chain and arity transported along
the trace equivalence) exchanges back.  The cup/cap discipline is automatic at the adjunction. -/
theorem arcStructureOf_sound_of_convFull_adjunction_emptyBoundary
    {sourceMode targetMode : adjunctionModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (sourceEmpty : sourcePath.length = 0)
    (convFull : TwoCellConvFull adjunctionModeSignature firstCell secondCell) :
    arcStructureOf firstCell = arcStructureOf secondCell := by
  have atomicEquiv : AtomicTraceEquiv adjunctionModeSignature firstCell.spine secondCell.spine :=
    (twoCellConvFull_spineTraceEquiv convFull).toAtomicTraceEquiv
  have chainedFirst : SpineBoundaryChained 0 firstCell.spine :=
    sourceEmpty ▸ firstCell.spineBoundaryChained_spine
  have chainedSecond : SpineBoundaryChained 0 secondCell.spine :=
    (spineBoundaryChained_iff_of_atomicTraceEquiv atomicEquiv 0).mp chainedFirst
  have arityFirst : SpineHasCupCapAtoms firstCell.spine :=
    fun atom _ => adjunctionSpineAtom_hasCupOrCapArity atom
  have aritySecond : SpineHasCupCapAtoms secondCell.spine :=
    fun atom _ => adjunctionSpineAtom_hasCupOrCapArity atom
  have freshProxy : ArcStateFresh (ArcWireState.mk [] [] 1 0 [] []) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro element memberOfNil; cases memberOfNil)
  have peel : extractArc 0 (processArcSpine (ArcWireState.mk [] [] 1 0 [] []) firstCell.spine)
      = extractArc 0 (processArcSpine (ArcWireState.mk [] [] 1 0 [] []) secondCell.spine) :=
    extractArc_eq_of_atomicTraceEquiv atomicEquiv (ArcWireState.mk [] [] 1 0 [] []) 0 0
      freshProxy isUnionFindForest_nil (Nat.lt_succ_self 0) (Nat.zero_le 1) rfl chainedFirst
  have firstShift := extractArcAfterProcessing_emptyBoundary_counterShift firstCell.spine chainedFirst arityFirst
  have secondShift := extractArcAfterProcessing_emptyBoundary_counterShift secondCell.spine chainedSecond aritySecond
  show arcStructureOfSpineList sourcePath.length firstCell.spine
    = arcStructureOfSpineList sourcePath.length secondCell.spine
  rw [sourceEmpty]
  exact (firstShift.trans peel).trans secondShift.symm

/-- ★ **The walking-adjunction Godement arc soundness at EVERY source boundary** — the total capstone,
dispatching on the boundary length: positive boundaries via the shipped peel
(`arcStructureOf_sound_of_convFull_adjunction`), the empty boundary via the counter-shift proxy
(`arcStructureOf_sound_of_convFull_adjunction_emptyBoundary`).  `arcStructureOf` is invariant under the COMPLETE
`TwoCellConvFull` at the walking adjunction, with no boundary caveat. -/
theorem arcStructureOf_sound_of_convFull_adjunction_allBoundaries
    {sourceMode targetMode : adjunctionModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (convFull : TwoCellConvFull adjunctionModeSignature firstCell secondCell) :
    arcStructureOf firstCell = arcStructureOf secondCell := by
  cases boundaryCases : sourcePath.length with
  | zero =>
      exact arcStructureOf_sound_of_convFull_adjunction_emptyBoundary boundaryCases convFull
  | succ boundaryPredecessor =>
      exact arcStructureOf_sound_of_convFull_adjunction
        (by rw [boundaryCases]; exact Nat.succ_pos boundaryPredecessor) convFull

/-! ## Honesty markers + the #2043 UPSTREAM re-derivation -/

/-- **Honesty marker — the Godement arc soundness is CLOSED at the walking adjunction at ALL boundaries.**
`arcStructureOf_sound_of_convFull_adjunction_allBoundaries` proves `arcStructureOf` invariant under the COMPLETE
`TwoCellConvFull` at `adjunctionModeSignature` at EVERY source boundary — positive via the shipped peel, empty via
the counter-shift proxy `extractArcAfterProcessing_emptyBoundary_counterShift` (the degenerate seed
`mk [] [] 0 0 [] []` exchanged for `mk [] [] 1 0 [] []` where the peel's `0 < nextFresh` holds).  The wall
`fxMode_hasArcGodementSoundnessPeelEmptyBoundary` (peel-only) is thereby superseded on its empty-boundary clause.
`= true`. -/
def fxMode_hasArcGodementSoundnessPeelAllBoundaries : Bool := true

/-- Mode-side re-derivation of the #2043 UPSTREAM state after the counter-shift proxy: the walking-adjunction arc
soundness is now closed at EVERY boundary (`fxMode_hasArcGodementSoundnessPeelAllBoundaries = true`), yet the
#2043 upstream residual — the GENERAL-signature `ArcGodementSamePartitionFresh`, refuted AS STATED without
freshness (`fxMode_hasArcPartitionCommuteProof = false`) and open under freshness
(`fxMode_hasArcGodementSamePartitionFreshProof = false`) — is NOT supplied by the adjunction-hardcoded peel and
stays open.  The mode-side lane advances SOUNDNESS at the adjunction; it does NOT close the general upstream
residual (which the amalgam master `fxAmalg_hasSaturatedDispatchTheorem` routes here via WP-MONAD9). -/
theorem arcPeelClosesAdjunctionSoundnessButNotGeneralUpstream :
    fxMode_hasArcGodementSoundnessPeelAllBoundaries = true
      ∧ fxMode_hasArcPartitionCommuteProof = false
      ∧ fxMode_hasArcGodementSamePartitionFreshProof = false :=
  ⟨rfl, rfl, rfl⟩

end FX1Poly.Polygraph
