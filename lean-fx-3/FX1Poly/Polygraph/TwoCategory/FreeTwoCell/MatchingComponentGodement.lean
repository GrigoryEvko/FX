import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentSim

/-! # mode-3 keystone — the freshness-conditioned COMPONENT-level Godement chain

`MatchingSwapObstruction` refuted the unconditional root-level chain; `MatchingComponentSim` shipped the
corrected component-level simulation substrate.  This file assembles the CORRECTED chain Props over that
substrate and RE-GATES the soundness consumption on freshness:

  ★ `MatchingSwapStateConditions` — the reachable-state package (`bottomCount ≤ nextFresh`, forest,
    `0 < nextFresh`, `WireStateFresh`), with the initial-state instance and `stepAtom` / `processSpine` /
    `runMatchingCell` preservation.  These are exactly the conditions the matching fold maintains from the
    canonical start state, so conditioning the residual on them loses NO consuming instance (except the
    empty-boundary degeneracy documented below).
  ★ `MatchingGodementComponentCoreSwap` → `MatchingGodementComponentSwapRenameable` →
    `MatchingGodementComponentCommute` — the corrected residual chain: freshness-conditioned, component-level
    (no injectivity, no root-level commutation), each reduction proved with nothing else owed.
  ★ `traceInvariant_of_conditionedGodementInvariant` + `matchingOf_sound_of_conditionedGodementInvariant` —
    the RE-GATE: the trace-equivalence induction threads `MatchingSwapStateConditions` through `stepAtom`
    (the `consCongr` case), so the CONDITIONED Godement invariance suffices for full `TwoCellConvFull`
    soundness of `matchingOf` — the freshness-conditioning is now consumable, not just honest.
  ★ `matchingOf_sound_of_componentCoreSwap` — the capstone composition: the SINGLE remaining obligation for
    `TwoCellConvFull`-soundness of `matchingOf` (at non-empty source boundaries) is the component core swap.

## The empty-boundary degeneracy (honest residual)

The re-gated soundness needs `0 < sourcePath.length`: at an EMPTY source boundary the canonical initial state
has `nextFresh = 0`, and the `0 < nextFresh` condition — load-bearing for the cap-read sentinel `sigma 0 = 0`
(a `blockRotate` window containing `0` cannot fix `0`) — fails.  Closing that case needs either a separate
degenerate argument (at `nextFresh = 0` freshness forces `openWires = []`, `links = []`) or an in-range
read discipline making the sentinel moot.  Deferred with the witness; see the honesty markers.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Tier0

/-! ## The reachable-state conditions package -/

/-- ★ **The reachable-state conditions of the matching fold** — everything the corrected block-swap residual
is conditioned on: the bottom boundary sits below the fresh counter, the links form a forest, the fresh
counter is positive (the cap-read sentinel's guard), and the state is fresh (`WireStateFresh`).  All four hold
at the canonical initial state (for a non-empty boundary) and are preserved by every fold step — so they
hold at every state the soundness chain ever consumes the residual at. -/
structure MatchingSwapStateConditions (bottomCount : Nat) (state : WireState) : Prop where
  /-- The bottom boundary ports sit below the fresh counter. -/
  bottomLe : bottomCount ≤ state.nextFresh
  /-- The links form a union-find forest. -/
  forest : isUnionFindForest state.links
  /-- The fresh counter is positive — the guard for the cap-read default sentinel `sigma 0 = 0`. -/
  nfPos : 0 < state.nextFresh
  /-- Every open wire and link endpoint is below the fresh counter. -/
  fresh : WireStateFresh state

/-- The canonical initial matching state `⟨range bottomCount, [], bottomCount, 0⟩` satisfies the conditions,
GIVEN a non-empty bottom boundary (`0 < bottomCount` — the initial fresh counter IS `bottomCount`). -/
theorem matchingSwapStateConditions_initial (bottomCount : Nat) (bottomPos : 0 < bottomCount) :
    MatchingSwapStateConditions bottomCount ⟨List.range bottomCount, [], bottomCount, 0⟩ where
  bottomLe := Nat.le_refl bottomCount
  forest := by exact True.intro
  nfPos := bottomPos
  fresh := wireStateFresh_initial bottomCount

/-- One matching step preserves the conditions package — `nextFresh` monotonicity carries `bottomLe` / `nfPos`,
the forest and freshness invariants their own preservation lemmas. -/
theorem matchingSwapStateConditions_stepAtom {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (state : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (conditions : MatchingSwapStateConditions bottomCount state) :
    MatchingSwapStateConditions bottomCount (stepAtom state atom) where
  bottomLe := Nat.le_trans conditions.bottomLe (stepAtom_nextFresh_le state atom)
  forest := isUnionFindForest_stepAtom state atom conditions.forest
  nfPos := Nat.lt_of_lt_of_le conditions.nfPos (stepAtom_nextFresh_le state atom)
  fresh := stepAtom_wireStateFresh state atom conditions.fresh conditions.nfPos

/-- The whole matching fold preserves the conditions package. -/
theorem matchingSwapStateConditions_processSpine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (atoms : List (SpineAtom signature sourceMode targetMode)) (state : WireState)
    (conditions : MatchingSwapStateConditions bottomCount state) :
    MatchingSwapStateConditions bottomCount (processSpine state atoms) where
  bottomLe := Nat.le_trans conditions.bottomLe (processSpine_nextFresh_le atoms state)
  forest := isUnionFindForest_processSpine atoms state conditions.forest
  nfPos := Nat.lt_of_lt_of_le conditions.nfPos (processSpine_nextFresh_le atoms state)
  fresh := processSpine_wireStateFresh atoms state conditions.fresh conditions.nfPos

/-- Running one cell preserves the conditions package. -/
theorem matchingSwapStateConditions_runMatchingCell {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (bottomCount : Nat) (state : WireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod)
    (conditions : MatchingSwapStateConditions bottomCount state) :
    MatchingSwapStateConditions bottomCount (runMatchingCell state leftAcc rightAcc cell) :=
  matchingSwapStateConditions_processSpine bottomCount (cell.spineDiff leftAcc rightAcc []) state conditions

/-! ## The corrected residual chain — freshness-conditioned, component-level -/

/-- ★ **The CORRECTED core block-swap obligation** — the component-level, freshness-conditioned replacement
for the REFUTED `MatchingGodementCoreSwapSim`.  Two fixes, both forced by the machine-checked obstructions
(`FreeTwoCell/MatchingSwapObstruction`): the state is conditioned on `MatchingSwapStateConditions` (the cup
collision `not_matchingGodementCoreSwapSim` kills the unconditional form), and the simulation is the
component-level `MatchingComponentSim` (the join-order root flip `not_matchingGodementCoreSwapSimFresh` kills
the root-level form even fresh).  The injectivity conjunct is GONE — the component view never transports root
equality through `sigma`.  The witness `sigma` (= `blockRotate` over the two blocks' fresh ranges) is the
standing residual. -/
def MatchingGodementComponentCoreSwap (signature : ModeSignature) : Prop :=
  ∀ {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (bottomCount : Nat) (state : WireState),
    MatchingSwapStateConditions bottomCount state →
    ∃ sigma : Nat → Nat,
      sigma 0 = 0
        ∧ (∀ identifier, identifier < bottomCount → sigma identifier = identifier)
        ∧ (∀ identifier,
            (runMatchingCell (runMatchingCell
                (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
                leftAcc (composePath gLow rightAcc) cellAlphaUpper)
              (composePath leftAcc fHigh) rightAcc cellBeta).nextFresh ≤ identifier
            → sigma identifier = identifier)
        ∧ MatchingComponentSim sigma
            (runMatchingCell (runMatchingCell
                (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
                leftAcc (composePath gLow rightAcc) cellAlphaUpper)
              (composePath leftAcc fHigh) rightAcc cellBeta)
            (runMatchingCell (runMatchingCell
                (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
                (composePath leftAcc fMid) rightAcc cellBeta)
              leftAcc (composePath gMid rightAcc) cellAlphaUpper)

/-- ★ **The corrected renaming-level residual** — the freshness-conditioned, component-level replacement for
the REFUTED `MatchingGodementSwapRenameable`: the two full Godement run orders are
`MatchingComponentRenameRel`-related at every CONDITIONED state. -/
def MatchingGodementComponentSwapRenameable (signature : ModeSignature) : Prop :=
  ∀ {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    (bottomCount : Nat) (state : WireState),
    MatchingSwapStateConditions bottomCount state →
    ∃ sigma : Nat → Nat, MatchingComponentRenameRel bottomCount sigma
      (processSpine
        (runMatchingCell (runMatchingCell (runMatchingCell
            (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBeta)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)
      (processSpine
        (runMatchingCell (runMatchingCell (runMatchingCell
            (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            (composePath leftAcc fMid) rightAcc cellBeta)
          leftAcc (composePath gMid rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)

/-- ★ **The corrected suffix-peel reduction.**  The component core swap implies the renaming-level residual —
the core `MatchingComponentSim` is peeled over the common `cellBetaUpper`-then-`rest` tail by
`matchingComponentRenameRel_full_of_coreSim`, with nothing else owed. -/
theorem matchingGodementComponentSwapRenameable_of_coreSwap {signature : ModeSignature}
    (coreSwap : MatchingGodementComponentCoreSwap signature) :
    MatchingGodementComponentSwapRenameable signature := by
  intro _ _ _ _ _ _ _ fHigh _ _ _ cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest
    bottomCount state conditions
  obtain ⟨sigma, sigmaFixesZero, fixesBoundary, fixesAbove, sim⟩ :=
    coreSwap cellAlpha cellAlphaUpper cellBeta leftAcc rightAcc bottomCount state conditions
  exact ⟨sigma, matchingComponentRenameRel_full_of_coreSim sigma sigmaFixesZero bottomCount fixesBoundary _ _
    (composePath leftAcc fHigh) rightAcc cellBetaUpper rest fixesAbove sim⟩

/-- ★ **The corrected two-block extract commutation** — the freshness-conditioned replacement for the
too-strong unconditional `MatchingGodementCommute`: the two run orders extract to the same `DiagramType` from
every CONDITIONED state. -/
def MatchingGodementComponentCommute (signature : ModeSignature) : Prop :=
  ∀ {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    (bottomCount : Nat) (state : WireState),
    MatchingSwapStateConditions bottomCount state →
    extractDiagram bottomCount (processSpine
        (runMatchingCell (runMatchingCell (runMatchingCell
            (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBeta)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)
      = extractDiagram bottomCount (processSpine
        (runMatchingCell (runMatchingCell (runMatchingCell
            (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            (composePath leftAcc fMid) rightAcc cellBeta)
          leftAcc (composePath gMid rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)

/-- ★ **The corrected read-off reduction.**  The renaming-level residual implies the extract commutation —
the component rename witness feeds the CLOSED `extractDiagram_of_matchingComponentRenameRel`. -/
theorem matchingGodementComponentCommute_of_swapRenameable {signature : ModeSignature}
    (swapRenameable : MatchingGodementComponentSwapRenameable signature) :
    MatchingGodementComponentCommute signature := by
  intro _ _ _ _ _ _ _ _ _ _ _ cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest
    bottomCount state conditions
  obtain ⟨sigma, rel⟩ :=
    swapRenameable cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest bottomCount state
      conditions
  exact extractDiagram_of_matchingComponentRenameRel bottomCount sigma _ _ rel

/-! ## The re-gated soundness consumption -/

/-- ★ **The CONDITIONED Godement-step invariance.**  From the conditioned two-block commutation: a
`SpineGodementStep` preserves the extract from every CONDITIONED state — `cases` on the single constructor,
four `processSpine_spineDiff` peels per side, exactly the unconditional reduction's proof with the conditions
threaded through. -/
theorem matchingGodementInvariant_of_componentCommute {signature : ModeSignature}
    (commute : MatchingGodementComponentCommute signature)
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat) (state : WireState)
    (conditions : MatchingSwapStateConditions bottomCount state)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (step : SpineGodementStep signature firstList secondList) :
    extractAfterProcessing bottomCount state firstList
      = extractAfterProcessing bottomCount state secondList := by
  cases step with
  | godement cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest =>
    simp only [extractAfterProcessing, processSpine_spineDiff]
    exact commute cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest bottomCount state
      conditions

/-- ★ **The RE-GATED trace invariance** — the freshness-threaded clone of
`traceInvariant_of_godementInvariant`: given the CONDITIONED Godement-step invariance, full `SpineTraceEquiv`
preserves the extract from every CONDITIONED state.  The `consCongr` case is the whole point: it steps the
state by the head atom AND carries the conditions across via `matchingSwapStateConditions_stepAtom` — so
conditioning the residual on reachable-state invariants costs the consumer NOTHING. -/
theorem traceInvariant_of_conditionedGodementInvariant {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat)
    (godementInvariant : ∀ (state : WireState),
        MatchingSwapStateConditions bottomCount state →
        ∀ {firstList secondList : List (SpineAtom signature overallSource overallTarget)},
        SpineGodementStep signature firstList secondList →
        extractAfterProcessing bottomCount state firstList
          = extractAfterProcessing bottomCount state secondList)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (equiv : SpineTraceEquiv signature firstList secondList) :
    ∀ (state : WireState), MatchingSwapStateConditions bottomCount state →
      extractAfterProcessing bottomCount state firstList
        = extractAfterProcessing bottomCount state secondList := by
  induction equiv with
  | ofStep step => intro state conditions; exact godementInvariant state conditions step
  | refl _ => intro _ _; rfl
  | symm _ inductionHypothesis =>
      intro state conditions; exact (inductionHypothesis state conditions).symm
  | trans _ _ firstHypothesis secondHypothesis =>
      intro state conditions
      exact (firstHypothesis state conditions).trans (secondHypothesis state conditions)
  | consCongr atom _ inductionHypothesis =>
      intro state conditions
      exact inductionHypothesis (stepAtom state atom)
        (matchingSwapStateConditions_stepAtom bottomCount state atom conditions)

/-- ★ **Full `TwoCellConvFull` soundness of `matchingOf` from the CONDITIONED invariance** — the re-gated
clone of `matchingOf_sound_of_godementInvariant`, at a NON-EMPTY source boundary (the canonical initial state
then satisfies the conditions; the empty-boundary case is the documented degeneracy). -/
theorem matchingOf_sound_of_conditionedGodementInvariant {signature : ModeSignature}
    (godementInvariant : ∀ {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat)
        (state : WireState),
        MatchingSwapStateConditions bottomCount state →
        ∀ {firstList secondList : List (SpineAtom signature overallSource overallTarget)},
        SpineGodementStep signature firstList secondList →
        extractAfterProcessing bottomCount state firstList
          = extractAfterProcessing bottomCount state secondList)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (sourceNonEmpty : 0 < sourcePath.length)
    (convFull : TwoCellConvFull signature firstCell secondCell) :
    matchingOf firstCell = matchingOf secondCell :=
  traceInvariant_of_conditionedGodementInvariant sourcePath.length
    (fun state conditions {_firstList _secondList} step =>
      godementInvariant sourcePath.length state conditions step)
    (twoCellConvFull_spineTraceEquiv convFull)
    { openWires := List.range sourcePath.length, links := [], nextFresh := sourcePath.length, loops := 0 }
    (matchingSwapStateConditions_initial sourcePath.length sourceNonEmpty)

/-- ★ **The capstone composition** — the ENTIRE `TwoCellConvFull`-soundness of `matchingOf` (at non-empty
source boundaries) from the SINGLE corrected obligation: component core swap → renaming residual → extract
commutation → conditioned invariance → re-gated trace induction. -/
theorem matchingOf_sound_of_componentCoreSwap {signature : ModeSignature}
    (coreSwap : MatchingGodementComponentCoreSwap signature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (sourceNonEmpty : 0 < sourcePath.length)
    (convFull : TwoCellConvFull signature firstCell secondCell) :
    matchingOf firstCell = matchingOf secondCell :=
  matchingOf_sound_of_conditionedGodementInvariant
    (fun {_overallSource _overallTarget} bottomCount state conditions {_firstList _secondList} step =>
      matchingGodementInvariant_of_componentCommute
        (matchingGodementComponentCommute_of_swapRenameable
          (matchingGodementComponentSwapRenameable_of_coreSwap coreSwap))
        bottomCount state conditions step)
    sourceNonEmpty convFull

/-! ## Honesty markers -/

/-- **Honesty marker — the corrected component-level Godement chain is ASSEMBLED and RE-GATED.**  The
freshness-conditioned chain Props (`MatchingGodementComponentCoreSwap` → `…SwapRenameable` → `…Commute`) are
each reduced with nothing else owed, the conditioned Godement-step invariance is proved from the commute, and
— the load-bearing part — the trace-equivalence induction is RE-PROVED threading
`MatchingSwapStateConditions` through `stepAtom` (`traceInvariant_of_conditionedGodementInvariant`), so the
conditioned residual is CONSUMABLE: `matchingOf_sound_of_componentCoreSwap` derives full `TwoCellConvFull`
soundness of `matchingOf` at non-empty source boundaries from the component core swap alone.  `= true`. -/
def fxMode_hasMatchingComponentGodementChain : Bool := true

/-- **Honesty marker — the component core-swap WITNESS is NOT proven; two residuals stand.**  (i) THE WITNESS:
the explicit `sigma = blockRotate lo w1 w2` realising `MatchingComponentSim` between the two run orders at
every conditioned state — its `openMap` (disjoint-window locality), `componentComm` (join-order independence
of the PARTITION — now a TRUE obligation, unlike the refuted root-level form), and `loopsEq` (the exchange
argument); `nfEq` and the forests are already generic (`matchingCoreSwap_nextFresh_eq`,
`isUnionFindForest_runMatchingCell`).  (ii) THE EMPTY-BOUNDARY DEGENERACY: at `sourcePath = nil` the initial
`nextFresh` is `0` and the `nfPos` condition fails (the `blockRotate` window would contain the cap-read
sentinel `0`); the walking adjunction's unit/counit have nil boundaries, so the saturated-keystone re-gate
additionally needs the degenerate case (freshness at `nextFresh = 0` forces `openWires = []`, `links = []`)
or an in-range read discipline.  `= false`. -/
def fxMode_hasMatchingComponentCoreSwapWitness : Bool := false

end FX1Poly.Tier0
