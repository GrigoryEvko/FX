import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingTwoCupSwapSim
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentSimInRange
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwapBoundary
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupTransfer

/-! # WalkingAdjunction/MatchingSwapPeel — the matching-carrier fold-through peel (Track B, piece (a))

The width-0 matching analogue of the arc `extractArc_eq_of_atomicTraceEquiv` (`ArcSwapPeel`), riding
brick 2 (`matchingStepSim_twoCupSwap`) at the swap node instead of the positivity-gated arc core package.
Trace-equivalent PURE-CUP spines extract the SAME `matchingOfSpineList`-style `DiagramType` from any fresh,
forest-rooted, boundary-tracked start state — with NO positive-fresh-seed hypothesis (`0 < nextFresh`), which
is exactly the arc obstruction (`ArcSwapCorePackage.sigmaFixesZero`) the width-0 seed cannot supply.

Why positivity-free: the cup-cup swap core `matchingStepSim_twoCupSwap` holds even at `nextFresh = 0`
(`blockSwap 0 0 = 2`), and the FOLD-THROUGH past the spine tail rides the SENTINEL-FREE component chain
(`matchingComponentRenameRel_ofCoreSim_boundaryDiscipline`), whose in-range window reads never invoke
`sigma 0 = 0`.  The bridge from the `MatchingStepSim` core to the `MatchingComponentSim` carrier is the
`beq`-injectivity downgrade (`matchingComponentSim_ofStepSim`), and `blockSwap` is injective.

  * `blockSwap_fix_ge` — `blockSwap nf` fixes every id at or above `nf + 4` (the two-cup fresh block ends
    at `nf + 3`), the `fixesAbove` leg the fold-through needs.
  * `matchingComponentSim_ofStepSim` — a `MatchingStepSim` over an INJECTIVE rename downgrades to
    `MatchingComponentSim` (root-commutation ⟹ same-component correspondence via `beq_congr_inj`).
  * `extractDiagram_eq_of_atomicCupSwap` — the swap-node content: two cups in the two Godement run orders,
    threaded past a shared tail, extract equal `DiagramType`.
  * ★ `extractDiagram_eq_of_atomicPureCupTraceEquiv` — the PEEL: along any `AtomicTraceEquiv` between pure-cup
    spines, the width-0 matching extract is invariant.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## `blockSwap` fixes ids above the fresh block -/

/-- `blockSwap nf` fixes any id at or above `nf + 4`: all four guards (`nf … nf+3`) fail because
`nf + k < nf + 4 ≤ identifier` for `k = 0 … 3`. -/
theorem blockSwap_fix_ge (nf identifier : Nat) (above : nf + 4 ≤ identifier) :
    blockSwap nf identifier = identifier := by
  have lt0 : nf < identifier := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) above
  have lt1 : nf + 1 < identifier := Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) nf) above
  have lt2 : nf + 2 < identifier := Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) nf) above
  have lt3 : nf + 3 < identifier := Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) nf) above
  show (if identifier == nf then nf + 2 else if identifier == nf + 1 then nf + 3
        else if identifier == nf + 2 then nf else if identifier == nf + 3 then nf + 1 else identifier)
      = identifier
  rw [if_neg (natBeqNeTrue (Ne.symm (Nat.ne_of_lt lt0))),
    if_neg (natBeqNeTrue (Ne.symm (Nat.ne_of_lt lt1))),
    if_neg (natBeqNeTrue (Ne.symm (Nat.ne_of_lt lt2))),
    if_neg (natBeqNeTrue (Ne.symm (Nat.ne_of_lt lt3)))]

/-! ## `MatchingStepSim` downgrades to `MatchingComponentSim` under injectivity -/

/-- A `MatchingStepSim` over an INJECTIVE rename downgrades to the component-level `MatchingComponentSim`:
the root-commutation field `rootComm` transports the same-component boolean via `beq_congr_inj` (an injective
`sigma` reflects `==`), which is exactly the `componentComm` field. -/
theorem matchingComponentSim_ofStepSim (sigma : Nat → Nat)
    (inj : ∀ a b, sigma a = sigma b → a = b)
    (stateS stateT : WireState) (sim : MatchingStepSim sigma stateS stateT) :
    MatchingComponentSim sigma stateS stateT where
  openMap := sim.openMap
  nfEq := sim.nfEq
  componentComm := by
    intro a b
    rw [sim.rootComm a, sim.rootComm b]
    exact beq_congr_inj sigma inj _ _
  loopsEq := sim.loopsEq
  forestS := sim.forestS
  forestT := sim.forestT

/-! ## Two-window arithmetic -/

/-- `a + 2 + b = b + 2 + a` — the disjoint-window swap commutes the two cup positions. -/
private theorem windowCommute (a b : Nat) : a + 2 + b = b + 2 + a := by
  rw [Nat.add_right_comm a 2 b, Nat.add_right_comm b 2 a, Nat.add_comm a b]

/-! ## The swap-node content -/

/-- The swap-node content of the peel.  Two adjacent cups fired in the two Godement run orders
(`generatorLeft` first vs `generatorRight` first, separated by the inert gap) extract the SAME
`DiagramType` at bottom boundary `bottomCount` from a fresh, forest-rooted, boundary-tracked start state.
Rides brick 2 (`matchingStepSim_twoCupSwap`, the positivity-free cup-cup core), downgrades it to the
component carrier (`matchingComponentSim_ofStepSim`, `blockSwap` injective), and folds it through the shared
tail via the sentinel-free suffix peel (`matchingComponentRenameRel_ofCoreSim_boundaryDiscipline`). -/
theorem extractDiagram_eq_of_atomicCupSwap
    {overallSource overallTarget : adjunctionGraph.Mode}
    {swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode : adjunctionGraph.Mode}
    {oneCellFMid oneCellFHigh : ModalityPath adjunctionGraph swapSourceMode swapMiddleLeft}
    {oneCellGLow oneCellGMid : ModalityPath adjunctionGraph swapMiddleRight swapTargetMode}
    (generatorLeft : adjunctionModeSignature.twoCell oneCellFMid oneCellFHigh)
    (generatorRight : adjunctionModeSignature.twoCell oneCellGLow oneCellGMid)
    (leftAcc : ModalityPath adjunctionGraph overallSource swapSourceMode)
    (inertPath : ModalityPath adjunctionGraph swapMiddleLeft swapMiddleRight)
    (rightAcc : ModalityPath adjunctionGraph swapTargetMode overallTarget)
    (rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (state : WireState) (bottomCount boundaryLength : Nat)
    (fresh : WireStateFresh state) (forest : isUnionFindForest state.links)
    (belowFresh : bottomCount ≤ state.nextFresh)
    (wiresEq : state.openWires.length = boundaryLength)
    (chained : SpineBoundaryChained boundaryLength
        (⟨swapSourceMode, swapMiddleLeft, leftAcc, oneCellFMid, oneCellFHigh, generatorLeft,
            composePath (composePath inertPath oneCellGLow) rightAcc⟩ ::
          ⟨swapMiddleRight, swapTargetMode,
            composePath (composePath leftAcc oneCellFHigh) inertPath, oneCellGLow, oneCellGMid,
            generatorRight, rightAcc⟩ :: rest))
    (fMidZero : oneCellFMid.length = 0) (fHighTwo : oneCellFHigh.length = 2)
    (gLowZero : oneCellGLow.length = 0) (gMidTwo : oneCellGMid.length = 2)
    (restPure : AllCupArity rest) :
    extractDiagram bottomCount (processSpine state
        (⟨swapSourceMode, swapMiddleLeft, leftAcc, oneCellFMid, oneCellFHigh, generatorLeft,
            composePath (composePath inertPath oneCellGLow) rightAcc⟩ ::
          ⟨swapMiddleRight, swapTargetMode,
            composePath (composePath leftAcc oneCellFHigh) inertPath, oneCellGLow, oneCellGMid,
            generatorRight, rightAcc⟩ :: rest))
      = extractDiagram bottomCount (processSpine state
          (⟨swapMiddleRight, swapTargetMode,
              composePath (composePath leftAcc oneCellFMid) inertPath, oneCellGLow, oneCellGMid,
              generatorRight, rightAcc⟩ ::
            ⟨swapSourceMode, swapMiddleLeft, leftAcc, oneCellFMid, oneCellFHigh, generatorLeft,
              composePath (composePath inertPath oneCellGMid) rightAcc⟩ :: rest)) := by
  let atomA : SpineAtom adjunctionModeSignature overallSource overallTarget :=
    ⟨swapSourceMode, swapMiddleLeft, leftAcc, oneCellFMid, oneCellFHigh, generatorLeft,
      composePath (composePath inertPath oneCellGLow) rightAcc⟩
  let atomB : SpineAtom adjunctionModeSignature overallSource overallTarget :=
    ⟨swapMiddleRight, swapTargetMode, composePath (composePath leftAcc oneCellFHigh) inertPath,
      oneCellGLow, oneCellGMid, generatorRight, rightAcc⟩
  let atomBr : SpineAtom adjunctionModeSignature overallSource overallTarget :=
    ⟨swapMiddleRight, swapTargetMode, composePath (composePath leftAcc oneCellFMid) inertPath,
      oneCellGLow, oneCellGMid, generatorRight, rightAcc⟩
  let atomAr : SpineAtom adjunctionModeSignature overallSource overallTarget :=
    ⟨swapSourceMode, swapMiddleLeft, leftAcc, oneCellFMid, oneCellFHigh, generatorLeft,
      composePath (composePath inertPath oneCellGMid) rightAcc⟩
  show extractDiagram bottomCount (processSpine state (atomA :: atomB :: rest))
    = extractDiagram bottomCount (processSpine state (atomBr :: atomAr :: rest))
  -- cup arities on the four atoms (defeq to the clean length hypotheses)
  have aDom : atomA.generatorDom.length = 0 := fMidZero
  have aCod : atomA.generatorCod.length = 2 := fHighTwo
  have bDom : atomB.generatorDom.length = 0 := gLowZero
  have bCod : atomB.generatorCod.length = 2 := gMidTwo
  have brDom : atomBr.generatorDom.length = 0 := gLowZero
  have brCod : atomBr.generatorCod.length = 2 := gMidTwo
  have arDom : atomAr.generatorDom.length = 0 := fMidZero
  have arCod : atomAr.generatorCod.length = 2 := fHighTwo
  -- the two composite states reduce to brick 2's cup-bubble shapes
  have hRedex : stepAtom (stepAtom state atomA) atomB
      = stepCup (stepCup state leftAcc.length) (inertPath.length + 2 + leftAcc.length) := by
    rw [stepAtom_ofCupArity state atomA aDom aCod,
      stepAtom_ofCupArity (stepCup state atomA.leftContext.length) atomB bDom bCod]
    show stepCup (stepCup state leftAcc.length)
        (composePath (composePath leftAcc oneCellFHigh) inertPath).length
      = stepCup (stepCup state leftAcc.length) (inertPath.length + 2 + leftAcc.length)
    rw [composePath_length_double leftAcc oneCellFHigh inertPath, fHighTwo,
      windowCommute leftAcc.length inertPath.length]
  have hReduct : stepAtom (stepAtom state atomBr) atomAr
      = stepCup (stepCup state (inertPath.length + leftAcc.length)) leftAcc.length := by
    rw [stepAtom_ofCupArity state atomBr brDom brCod,
      stepAtom_ofCupArity (stepCup state atomBr.leftContext.length) atomAr arDom arCod]
    show stepCup (stepCup state (composePath (composePath leftAcc oneCellFMid) inertPath).length)
        leftAcc.length
      = stepCup (stepCup state (inertPath.length + leftAcc.length)) leftAcc.length
    rw [composePath_length_double leftAcc oneCellFMid inertPath, fMidZero, Nat.add_zero,
      Nat.add_comm leftAcc.length inertPath.length]
  -- boundary bookkeeping
  have headFires : atomA.domBoundaryLength = boundaryLength := (spineBoundaryChained_tail chained).1
  have tailChained1 : SpineBoundaryChained atomA.codBoundaryLength (atomB :: rest) :=
    (spineBoundaryChained_tail chained).2
  have headFiresB : atomB.domBoundaryLength = atomA.codBoundaryLength :=
    (spineBoundaryChained_tail tailChained1).1
  have restChained : SpineBoundaryChained atomB.codBoundaryLength rest :=
    (spineBoundaryChained_tail tailChained1).2
  have rcLen : atomA.rightContext.length = inertPath.length + rightAcc.length := by
    show (composePath (composePath inertPath oneCellGLow) rightAcc).length
      = inertPath.length + rightAcc.length
    rw [composePath_length_double inertPath oneCellGLow rightAcc, gLowZero, Nat.add_zero]
  have boundaryEq : boundaryLength = leftAcc.length + inertPath.length + rightAcc.length := by
    rw [← headFires]
    show leftAcc.length + oneCellFMid.length + atomA.rightContext.length
      = leftAcc.length + inertPath.length + rightAcc.length
    rw [fMidZero, Nat.add_zero, rcLen, ← Nat.add_assoc]
  have positionBound : inertPath.length + leftAcc.length ≤ state.openWires.length := by
    rw [wiresEq, boundaryEq, Nat.add_comm inertPath.length leftAcc.length]
    exact Nat.le_add_right (leftAcc.length + inertPath.length) rightAcc.length
  -- brick 2 : the two cup-bubble orders are `MatchingStepSim (blockSwap nf)`-related
  have brick2 := matchingStepSim_twoCupSwap state fresh forest inertPath.length leftAcc.length positionBound
  have coreSim : MatchingComponentSim (blockSwap state.nextFresh)
      (stepAtom (stepAtom state atomA) atomB) (stepAtom (stepAtom state atomBr) atomAr) := by
    rw [hRedex, hReduct]
    exact matchingComponentSim_ofStepSim (blockSwap state.nextFresh)
      (blockSwap_injective state.nextFresh) _ _ brick2
  -- state tracking and fresh-block fixing for the fold-through
  have tracksA : (stepAtom state atomA).openWires.length = atomA.codBoundaryLength :=
    stepAtom_openWires_tracksBoundary state atomA (Or.inl ⟨aDom, aCod⟩) (wiresEq.trans headFires.symm)
  have restTracks : (stepAtom (stepAtom state atomA) atomB).openWires.length = atomB.codBoundaryLength :=
    stepAtom_openWires_tracksBoundary (stepAtom state atomA) atomB (Or.inl ⟨bDom, bCod⟩)
      (tracksA.trans headFiresB.symm)
  have coreNext : (stepAtom (stepAtom state atomA) atomB).nextFresh = state.nextFresh + 4 := by
    rw [hRedex, stepCup_nextFresh, stepCup_nextFresh]
  have fixesBoundary : ∀ identifier, identifier < bottomCount → blockSwap state.nextFresh identifier = identifier :=
    fun identifier hlt => blockSwap_fix_lt state.nextFresh identifier (Nat.lt_of_lt_of_le hlt belowFresh)
  have fixesAbove : ∀ identifier, (stepAtom (stepAtom state atomA) atomB).nextFresh ≤ identifier
      → blockSwap state.nextFresh identifier = identifier :=
    fun identifier hle => blockSwap_fix_ge state.nextFresh identifier (coreNext ▸ hle)
  have restArity : SpineHasCupCapAtoms rest := spineHasCupCapAtoms_ofAllCupArity rest restPure
  -- fold the core through the shared tail and read off equal diagrams
  have rel := matchingComponentRenameRel_ofCoreSim_boundaryDiscipline
    (blockSwap state.nextFresh) bottomCount fixesBoundary rest
    (stepAtom (stepAtom state atomA) atomB) (stepAtom (stepAtom state atomBr) atomAr)
    atomB.codBoundaryLength restChained restArity restTracks fixesAbove coreSim
  show extractDiagram bottomCount (processSpine (stepAtom (stepAtom state atomA) atomB) rest)
    = extractDiagram bottomCount (processSpine (stepAtom (stepAtom state atomBr) atomAr) rest)
  exact extractDiagram_of_matchingComponentRenameRel bottomCount (blockSwap state.nextFresh) _ _ rel

/-! ## The peel -/

/-- ★ **The matching fold-through peel (piece (a)).**  Along ANY `AtomicTraceEquiv` between PURE-CUP spines,
the width-0 matching extract is invariant: from every fresh, forest-rooted, boundary-tracked start state with
`bottomCount ≤ nextFresh`, both processed spines extract the same `DiagramType`.  Positivity-free — the swap
node rides brick 2 (`matchingStepSim_twoCupSwap`) and the sentinel-free component fold, never
`0 < nextFresh`. -/
theorem extractDiagram_eq_of_atomicPureCupTraceEquiv
    {overallSource overallTarget : adjunctionGraph.Mode}
    {firstList secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (traceEquiv : AtomicTraceEquiv adjunctionModeSignature firstList secondList) :
    ∀ (state : WireState) (bottomCount boundaryLength : Nat),
      WireStateFresh state → isUnionFindForest state.links →
      bottomCount ≤ state.nextFresh →
      state.openWires.length = boundaryLength →
      SpineBoundaryChained boundaryLength firstList →
      AllCupArity firstList →
      extractDiagram bottomCount (processSpine state firstList)
        = extractDiagram bottomCount (processSpine state secondList) := by
  induction traceEquiv with
  | ofSwap swapStep =>
      cases swapStep with
      | @swap swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode
          oneCellFMid oneCellFHigh oneCellGLow oneCellGMid
          generatorLeft generatorRight leftAcc inertPath rightAcc rest =>
          intro state bottomCount boundaryLength fresh forest belowFresh wiresEq chained pureCup
          cases pureCup with
          | cons hdomL hcodL restPure1 =>
              cases restPure1 with
              | cons hdomR hcodR restPure =>
                  exact extractDiagram_eq_of_atomicCupSwap generatorLeft generatorRight leftAcc inertPath
                    rightAcc rest state bottomCount boundaryLength fresh forest belowFresh wiresEq chained
                    hdomL hcodL hdomR hcodR restPure
  | refl _ => exact fun _ _ _ _ _ _ _ _ _ => rfl
  | symm innerEquiv innerHypothesis =>
      intro state bottomCount boundaryLength fresh forest belowFresh wiresEq chained pureCup
      have firstPure : AllCupArity _ :=
        allCupArity_preservedOfAtomicTraceEquiv (AtomicTraceEquiv.symm innerEquiv) pureCup
      have firstChained :=
        (spineBoundaryChained_iff_of_atomicTraceEquiv innerEquiv boundaryLength).mpr chained
      exact (innerHypothesis state bottomCount boundaryLength fresh forest belowFresh wiresEq
        firstChained firstPure).symm
  | trans leftEquiv _ leftHypothesis rightHypothesis =>
      intro state bottomCount boundaryLength fresh forest belowFresh wiresEq chained pureCup
      have midPure : AllCupArity _ := allCupArity_preservedOfAtomicTraceEquiv leftEquiv pureCup
      have midChained :=
        (spineBoundaryChained_iff_of_atomicTraceEquiv leftEquiv boundaryLength).mp chained
      exact (leftHypothesis state bottomCount boundaryLength fresh forest belowFresh wiresEq chained
          pureCup).trans
        (rightHypothesis state bottomCount boundaryLength fresh forest belowFresh wiresEq midChained
          midPure)
  | consCongr atom _ tailHypothesis =>
      intro state bottomCount boundaryLength fresh forest belowFresh wiresEq chained pureCup
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      cases pureCup with
      | cons hdom hcod restPure =>
          have stepCupEq : stepAtom state atom = stepCup state atom.leftContext.length :=
            stepAtom_ofCupArity state atom hdom hcod
          have freshStep : WireStateFresh (stepAtom state atom) := by
            rw [stepCupEq]; exact stepCup_wireStateFresh state atom.leftContext.length fresh
          have forestStep : isUnionFindForest (stepAtom state atom).links := by
            rw [stepCupEq]; exact isUnionFindForest_stepCup state atom.leftContext.length forest
          have belowStep : bottomCount ≤ (stepAtom state atom).nextFresh :=
            Nat.le_trans belowFresh (stepAtom_nextFresh_le state atom)
          have tracksStep : (stepAtom state atom).openWires.length = atom.codBoundaryLength :=
            stepAtom_openWires_tracksBoundary state atom (Or.inl ⟨hdom, hcod⟩)
              (wiresEq.trans headFires.symm)
          exact tailHypothesis (stepAtom state atom) bottomCount atom.codBoundaryLength freshStep
            forestStep belowStep tracksStep tailChained restPure

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the matching fold-through peel is SHIPPED, POSITIVITY-FREE (Track B, piece (a)).**
`extractDiagram_eq_of_atomicPureCupTraceEquiv`: along any `AtomicTraceEquiv` between pure-cup spines the
width-0 matching extract is invariant — the swap node rides brick 2 (`matchingStepSim_twoCupSwap`, the
positivity-free cup-cup core), downgrades to the component carrier (`matchingComponentSim_ofStepSim`,
`blockSwap` injective), and folds through the shared tail via the SENTINEL-FREE suffix peel
(`matchingComponentRenameRel_ofCoreSim_boundaryDiscipline`), so NO `0 < nextFresh` / `sigma 0 = 0` is ever
needed.  The refl/symm/trans/consCongr cases thread the pure-cup regime (`allCupArity_preservedOf…`),
the chain discipline (`spineBoundaryChained_iff_of_atomicTraceEquiv`), and the fresh/forest/tracking
invariants.

  What this marker does NOT claim: the matching-carrier LOCATE port (piece (b) — `chordShift`,
  `forwardChordsNotAdjacent`, `emptyMatchingNoForwardChord`, `matchingLocateAux`) that consumes this peel,
  and the direct-Catalan assembly (piece (c)) closing `WidthZeroPureCupDeterminacy`.  `convOfMapEq` and the
  fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasMatchingSwapPeel : Bool := true

end FX1Poly.Polygraph
