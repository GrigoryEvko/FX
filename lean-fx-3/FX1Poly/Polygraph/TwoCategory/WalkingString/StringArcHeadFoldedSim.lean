import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadFoldedSim
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcArity

/-! # WalkingString/StringArcHeadFoldedSim — the positional correspondence + count legs, ported
(FC-3 r19, THE CAP-HEAD DISCHARGE PORT — CANCEL/STRUCTURE substrate)

Phantom-signature two-token clone of the walking-adjunction `ArcHeadFoldedSim`, re-plumbed onto the FOUR-generator
seed.  The cup-head and cap-head seed pairs threaded through the unconditional positional-shift fold, plus the COUNT
LEGS the extract correspondence consumes (composite cup total = fresh total + 1 under a cup head; mirror for the
cap; the other total and boundary widths agree).  The proof only uses the `{signature}`-generic positional-shift kit
(`arcPositionalShiftSim_processArcSpine`, `arcHeadReindex_*SeedShifts`, `arcPositionalShiftSim_*HeadSeed`) and the
generic event-length / open-wire legs (`arcPositionalShiftSim_cupEventsLength`/`capEventsLength`/`openWiresLength`),
all REUSED by import — the signature is a pure phantom, so ONLY the `SpineAtom`-quantified statements clone.

Raw Lean 4 + Init; no `omega` / `simp`-AC / `WellFounded.fix`.  `propext`/`Quot.sound`/`Classical`/`sorry`/
`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The positional-shift fold over a spine (phantom-signature port) -/

/-- The positional-shift simulation is preserved by folding any spine — a phantom-signature clone of
`arcPositionalShiftSim_processArcSpine` (its only non-generic dependency is the seed classification
`adjointTripleSpineAtom_hasCupOrCapArity`; the per-step dispatch is `{signature}`-generic). -/
theorem stringArcPositionalShiftSim_processArcSpine
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (sigma : Nat → Nat) (delta threshold : Nat)
    (headCupEvents headCapEvents : List Nat)
    (sigmaShiftsAboveThreshold : ∀ identifier, threshold ≤ identifier →
      sigma identifier = identifier + delta) :
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    (baseState shiftedState : ArcWireState) →
    ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
      baseState shiftedState →
    ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
      (processArcSpine baseState atoms) (processArcSpine shiftedState atoms)
  | [], _, _, sim => sim
  | headAtom :: restAtoms, baseState, shiftedState, sim => by
      show ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
        (processArcSpine (stepArcAtom baseState headAtom) restAtoms)
        (processArcSpine (stepArcAtom shiftedState headAtom) restAtoms)
      exact stringArcPositionalShiftSim_processArcSpine sigma delta threshold
        headCupEvents headCapEvents sigmaShiftsAboveThreshold restAtoms
        (stepArcAtom baseState headAtom) (stepArcAtom shiftedState headAtom)
        (arcPositionalShiftSim_stepArcAtom sigma delta threshold headCupEvents headCapEvents
          baseState shiftedState headAtom
          (adjointTripleSpineAtom_hasCupOrCapArity headAtom) sigmaShiftsAboveThreshold sim)

/-! ## The folded simulations at the two head shapes -/

/-- ★ **The cup-head positional simulation at the folded end states** (four-generator port). -/
theorem stringArcPositionalShiftSim_cupHeadFolded
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    ArcPositionalShiftSim
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1)
      1 (bottomCount + 2) [bottomCount + 2] []
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] []) atoms)
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms) :=
  stringArcPositionalShiftSim_processArcSpine
    (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1)
    1 (bottomCount + 2) [bottomCount + 2] []
    (arcHeadReindex_cupSeedShifts bottomCount windowPosition)
    atoms
    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
    (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition)
    (arcPositionalShiftSim_cupHeadSeed bottomCount windowPosition)

/-- ★ **The cap-head positional simulation at the folded end states** (four-generator port). -/
theorem stringArcPositionalShiftSim_capHeadFolded
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    ArcPositionalShiftSim
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
      3 tailBoundary [] [bottomCount]
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms)
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms) :=
  stringArcPositionalShiftSim_processArcSpine
    (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
    3 tailBoundary [] [bottomCount]
    (arcHeadReindex_capSeedShifts bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits)
    atoms
    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
    (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition)
    (arcPositionalShiftSim_capHeadSeed bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits)

/-! ## The count legs at the two head shapes -/

/-- Under a cup head the composite run counts exactly ONE more cup event than the fresh run. -/
theorem stringArcCupHeadFolded_cupEventsLength
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).cupEventNodes.length
      = (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).cupEventNodes.length + 1 :=
  arcPositionalShiftSim_cupEventsLength
    (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1)
    1 (bottomCount + 2) [bottomCount + 2] []
    (processArcSpine
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] []) atoms)
    (processArcSpine
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms)
    (stringArcPositionalShiftSim_cupHeadFolded bottomCount windowPosition atoms)

/-- Under a cup head the cap-event totals of the two runs agree. -/
theorem stringArcCupHeadFolded_capEventsLength
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).capEventNodes.length
      = (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).capEventNodes.length :=
  arcPositionalShiftSim_capEventsLength
    (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1)
    1 (bottomCount + 2) [bottomCount + 2] []
    (processArcSpine
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] []) atoms)
    (processArcSpine
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms)
    (stringArcPositionalShiftSim_cupHeadFolded bottomCount windowPosition atoms)

/-- Under a cup head the two runs keep equal boundary widths. -/
theorem stringArcCupHeadFolded_openWiresLength
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).openWires.length
      = (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length :=
  arcPositionalShiftSim_openWiresLength
    (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1)
    1 (bottomCount + 2) [bottomCount + 2] []
    (processArcSpine
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] []) atoms)
    (processArcSpine
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms)
    (stringArcPositionalShiftSim_cupHeadFolded bottomCount windowPosition atoms)

/-- Under a cap head the composite run counts exactly ONE more cap event than the fresh run. -/
theorem stringArcCapHeadFolded_capEventsLength
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).capEventNodes.length
      = (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).capEventNodes.length + 1 :=
  arcPositionalShiftSim_capEventsLength
    (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
    3 tailBoundary [] [bottomCount]
    (processArcSpine
      (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms)
    (processArcSpine
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms)
    (stringArcPositionalShiftSim_capHeadFolded bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms)

/-- Under a cap head the cup-event totals of the two runs agree. -/
theorem stringArcCapHeadFolded_cupEventsLength
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).cupEventNodes.length
      = (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).cupEventNodes.length :=
  arcPositionalShiftSim_cupEventsLength
    (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
    3 tailBoundary [] [bottomCount]
    (processArcSpine
      (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms)
    (processArcSpine
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms)
    (stringArcPositionalShiftSim_capHeadFolded bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms)

/-- Under a cap head the two runs keep equal boundary widths. -/
theorem stringArcCapHeadFolded_openWiresLength
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).openWires.length
      = (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length :=
  arcPositionalShiftSim_openWiresLength
    (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
    3 tailBoundary [] [bottomCount]
    (processArcSpine
      (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms)
    (processArcSpine
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms)
    (stringArcPositionalShiftSim_capHeadFolded bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the positional correspondence + count legs ported to the adjoint-triple seed (FC-3 r19).**
The cup-head and cap-head folded positional simulations and the six count legs (`stringArcCapHeadFolded_capEventsLength`/
`_cupEventsLength`/`_openWiresLength` and the cup mirrors) — phantom-signature two-token clones of `ArcHeadFoldedSim`,
riding the `{signature}`-generic positional-shift kit (reused, never cloned).  Supplies the cup/cap event-length
legs the extract-structure transport consumes.  `= true`. -/
def fxString_hasArcHeadFoldedSim : Bool := true

end FX1Poly.Polygraph
