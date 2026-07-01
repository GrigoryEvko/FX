import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDecision

/-! # mode-3 floor — the FREE 2-cell decision via the FULL planar-arc structure (Joyal-Street, spine-modulo-trace)

The companion `FreeTwoCellMatchingDecision` computes the BOUNDARY matching of a free 2-cell read as a planar
string diagram — and proved that invariant is, at the walking-adjunction seed, DECISION-VACUOUS: three pairwise
non-convertible cells `left => left` (the identity, the snake, the double snake) share ONE boundary matching
`{1, 1, [1,0], 0}`, because their boundary connectivity is identical (a single through-strand) while their
INTERNAL turning structure differs.  The snake is a through-strand with one cup-turnback and one cap-turnback;
the identity is a straight strand with none.  The boundary matching forgets the turnbacks.

This file ships the STRICTLY FINER invariant the matching shadow lacked: the **full planar-arc structure** — the
boundary matching PLUS the internal cup/cap arc data (how many cup-turnbacks and cap-turnbacks lie on each
strand) PLUS the cup/cap totals PLUS the loop count.  This is the data Joyal-Street's graphical calculus
records, and it CLOSES the snake gap: `arcStructureOf snake /= arcStructureOf identity` by `rfl` (the crux that
validates the whole approach).

## How the internal arcs are read

`arcStructureOf` reads the spine bottom-to-top through the SAME union-find as `matchingOf`, but additionally
allocates one **event node** per cup and per cap and unions it into the wire's connected component.  At the end,
for every boundary port it counts the cup-events and cap-events sharing its component (the turnbacks on that
strand).  Two cells with the same boundary connectivity but different turnback counts now get DIFFERENT arc
structures — which is exactly the snake-vs-identity distinction.

## Trace-invariance and the residual

The arc structure reads ONLY the spine, so it is invariant under every interchange-free structural law and all
four whisker-functoriality laws ON THE NOSE (the spine is unchanged).  Under the Godement / interchange step the
spine is permuted (two horizontally-disjoint blocks transpose with a context shift), and the arc structure's
invariance reduces — exactly as `matchingOf`'s did — to the single state-parametric union-find independence
lemma (`arcStructureOf_sound_of_godementInvariant`).  Two parts of the new data are in fact UNCONDITIONALLY
Godement-invariant (the cup/cap totals: a Godement step preserves the multiset of cup/cap atoms); the
per-component attribution rides the same connectivity residual as the boundary matching.

## What is honest-DEFERRED

  * the Godement union-find independence (the single soundness residual, shared with the matching route, now
    over the richer extract) — `fxMode_hasArcGodementIndependenceProof = false`;
  * the RECONSTRUCTION `arcStructureOf a = arcStructureOf b -> SpineTraceEquiv a b` (the Joyal-Street
    completeness — same planar-arc type implies planar-isotopic implies trace-equivalent) —
    `fxMode_hasArcStructureReconstruction = false`;
  * the assembled `Decidable (TwoCellConvFull ...)` is provided GATED on exactly those two residuals plus the
    shipped `twoCellConvFull_spineTraceEquiv`, making the precise outstanding obligations explicit.

Raw Lean 4 + Init; structural / fuel recursion, no `omega` / `simp`-AC / `WellFounded.fix`.  Per-declaration
`#assert_no_axioms` gated in the (un-registered) audit twin. -/

namespace FX1Poly.Tier0

/-! ## The full planar-arc structure -/

/-- ★ The **full planar-arc structure** of a free 2-cell read as a planar string diagram: the boundary
`DiagramType` (boundary port counts, the canonical partner matching, the loop count) STRENGTHENED with the
internal cup/cap arc data.  `cupCount` / `capCount` are the totals of each turnback kind; `internalCupCounts` /
`internalCapCounts` record, per boundary port, how many cup-events / cap-events lie on that port's strand
(component).  A flat datum of `Nat` / `List Nat`, so its equality is decidable and COMPUTES.  This is strictly
finer than the boundary `DiagramType`: the snake and the identity share a `DiagramType` but differ here (the
snake's strand carries one cup-turnback and one cap-turnback; the identity's carries none). -/
structure FullArcStructure where
  /-- The boundary topological type: port counts, canonical partner matching, loop count. -/
  diagram : DiagramType
  /-- The total number of cup events (the `0 => 2` turnbacks). -/
  cupCount : Nat
  /-- The total number of cap events (the `2 => 0` turnbacks). -/
  capCount : Nat
  /-- Per boundary port, the number of cup events on that port's connected component (strand). -/
  internalCupCounts : List Nat
  /-- Per boundary port, the number of cap events on that port's connected component (strand). -/
  internalCapCounts : List Nat
deriving DecidableEq

/-! ## The wire-tracking state with cup/cap event nodes -/

/-- The wire-tracking state threaded bottom-to-top through a spine — the `WireState` of the matching route,
EXTENDED with the list of allocated cup-event and cap-event node ids.  Each event node is unioned into its
arc's connected component, so its final component is the strand it turns back on. -/
structure ArcWireState where
  /-- The open wires, left to right, by node id. -/
  openWires : List Nat
  /-- The connectivity union-find over wire AND event nodes (child -> parent edges). -/
  links : List (Nat × Nat)
  /-- The next fresh node id. -/
  nextFresh : Nat
  /-- The closed loops detected so far. -/
  loops : Nat
  /-- The allocated cup-event node ids (each unioned into its cup's component). -/
  cupEventNodes : List Nat
  /-- The allocated cap-event node ids (each unioned into its cap's component). -/
  capEventNodes : List Nat

/-- Process a single CUP (a `0 => 2` generator, the unit): allocate two fresh connected leg wires plus one fresh
event node unioned into the same component, and splice the legs into the open-wire list at `position`. -/
def stepCupArc (state : ArcWireState) (position : Nat) : ArcWireState :=
  let leftLeg := state.nextFresh
  let rightLeg := state.nextFresh + 1
  let eventNode := state.nextFresh + 2
  { openWires := natListInsertAt state.openWires position [leftLeg, rightLeg],
    links := unionFindJoin (unionFindJoin state.links leftLeg rightLeg) eventNode leftLeg,
    nextFresh := state.nextFresh + 3,
    loops := state.loops,
    cupEventNodes := eventNode :: state.cupEventNodes,
    capEventNodes := state.capEventNodes }

/-- Process a single CAP (a `2 => 0` generator, the counit): connect the two adjacent wires at `position`
(incrementing the loop count when they were already connected), allocate one fresh event node unioned into the
merged component, then drop the two wires. -/
def stepCapArc (state : ArcWireState) (position : Nat) : ArcWireState :=
  let leftWire := natListGetAt state.openWires position
  let rightWire := natListGetAt state.openWires (position + 1)
  let eventNode := state.nextFresh
  let wasSameComponent := isSameComponent state.links leftWire rightWire
  { openWires := natListRemoveTwoAt state.openWires position,
    links := unionFindJoin (unionFindJoin state.links leftWire rightWire) eventNode leftWire,
    nextFresh := state.nextFresh + 1,
    loops := if wasSameComponent then state.loops + 1 else state.loops,
    cupEventNodes := state.cupEventNodes,
    capEventNodes := eventNode :: state.capEventNodes }

/-- Process one spine atom: a `0 => 2` generator is a CUP, a `2 => 0` generator is a CAP, both fired at the live
position `leftContext.length`.  Any other arity is a generic opaque box (never occurs at the cup/cap
walking-adjunction seed): drop its inputs, add disconnected fresh outputs, record NO arc event (a box is not a
turnback).  The arity is read off the generator's boundary 1-cell lengths, so this works at any signature. -/
def stepArcAtom {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode) : ArcWireState :=
  let position := atom.leftContext.length
  match atom.generatorDom.length, atom.generatorCod.length with
  | 0, 2 => stepCupArc state position
  | 2, 0 => stepCapArc state position
  | numConsumed, numProduced =>
      let droppedWires :=
        Nat.rec state.openWires (fun _ shorter => natListRemoveTwoAt shorter position) numConsumed
      { openWires := natListInsertAt droppedWires position (List.range numProduced |>.map (· + state.nextFresh)),
        links := state.links,
        nextFresh := state.nextFresh + numProduced,
        loops := state.loops,
        cupEventNodes := state.cupEventNodes,
        capEventNodes := state.capEventNodes }

/-- Fold the per-atom arc step over a whole spine, bottom-to-top (head first). -/
def processArcSpine {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atoms : List (SpineAtom signature sourceMode targetMode)) : ArcWireState :=
  atoms.foldl stepArcAtom state

/-! ## Extracting the arc structure -/

/-- Count the event nodes whose component root equals `rootHere` (the turnbacks on one strand).  Structural on
the event-node list, propext-free. -/
def countEventsInRoot (links : List (Nat × Nat)) (rootHere : Nat) : List Nat → Nat
  | [] => 0
  | eventNode :: rest =>
      (if unionFindRootOf links eventNode == rootHere then 1 else 0) + countEventsInRoot links rootHere rest

/-- The number of `eventNodes` sharing boundary port `index`'s component — the turnback count on that strand. -/
def internalEventCountAt (links : List (Nat × Nat)) (boundaryNodes eventNodes : List Nat) (index : Nat) : Nat :=
  countEventsInRoot links (unionFindRootOf links (natListGetAt boundaryNodes index)) eventNodes

/-- Read the final arc state into a `FullArcStructure`: the boundary `DiagramType` via the matching route's
`extractDiagram`, the cup/cap totals from the event lists, and the per-port internal cup/cap counts by scanning
each port's component for its turnbacks. -/
def extractArc (bottomCount : Nat) (state : ArcWireState) : FullArcStructure :=
  let topWires := state.openWires
  let boundaryNodes := List.range bottomCount ++ topWires
  let total := bottomCount + topWires.length
  { diagram := extractDiagram bottomCount
      ({ openWires := state.openWires, links := state.links, nextFresh := state.nextFresh,
         loops := state.loops } : WireState),
    cupCount := state.cupEventNodes.length,
    capCount := state.capEventNodes.length,
    internalCupCounts := (List.range total).map (internalEventCountAt state.links boundaryNodes state.cupEventNodes),
    internalCapCounts := (List.range total).map (internalEventCountAt state.links boundaryNodes state.capEventNodes) }

/-- Read a flat spine list (with a given bottom-boundary wire count) into its `FullArcStructure` — the
spine-level core of `arcStructureOf`, factored out so the spine-congruence is a one-line `congrArg`. -/
def arcStructureOfSpineList {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (atoms : List (SpineAtom signature sourceMode targetMode)) : FullArcStructure :=
  extractArc bottomCount
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms)

/-- ★ The **full planar-arc structure** of a free 2-cell: read its spine bottom-to-top through the cup/cap
union-find with event-node tracking, then extract the boundary matching plus the internal cup/cap arc data.
Defined by structural / fuel recursion, so it COMPUTES.  Strictly finer than `matchingOf`: it sees the internal
turnbacks the boundary matching forgets (closing the snake gap). -/
def arcStructureOf {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) : FullArcStructure :=
  arcStructureOfSpineList sourcePath.length cell.spine

/-! ## Soundness under the interchange-free structural fragment -/

/-- `arcStructureOf` depends on the cell only through its spine (and the boundary length): equal spines give
equal arc structures. -/
theorem arcStructureOf_congr_of_spine_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (spineEqual : firstCell.spine = secondCell.spine) : arcStructureOf firstCell = arcStructureOf secondCell :=
  congrArg (arcStructureOfSpineList sourcePath.length) spineEqual

/-- ★ **Soundness of `arcStructureOf` under the interchange-free structural fragment**: every one of the eleven
structural strict-2-category laws preserves the arc structure, because each preserves the spine on the nose
(`TwoCellStepInterchangeFree.spine_eq`). -/
theorem arcStructureOf_eq_of_interchangeFreeStep {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStepInterchangeFree signature firstCell secondCell) :
    arcStructureOf firstCell = arcStructureOf secondCell :=
  arcStructureOf_congr_of_spine_eq step.spine_eq

/-! ## Soundness under whisker functoriality — the four `TwoCellConvFull` whisker laws -/

/-- Soundness under whisker-left-unit: same spine, definitional. -/
theorem arcStructureOf_whiskerLeftUnit {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellDom oneCellCod : ModalityPath signature.graph sourceMode targetMode}
    (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
    arcStructureOf (RawTwoCellExpr.whiskerLeft (identityPath sourceMode) body) = arcStructureOf body :=
  arcStructureOf_congr_of_spine_eq rfl

/-- Soundness under whisker-right-unit: through the spine-invisible boundary cast. -/
theorem arcStructureOf_whiskerRightUnit {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellDom oneCellCod : ModalityPath signature.graph sourceMode targetMode}
    (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
    arcStructureOf (RawTwoCellExpr.whiskerRight (identityPath targetMode) body)
      = arcStructureOf (RawTwoCellExpr.castBoundary (composePath_identityPath_right oneCellDom).symm
          (composePath_identityPath_right oneCellCod).symm body) := by
  rw [arcStructureOf, arcStructureOf, RawTwoCellExpr.castBoundary_spine]; rfl

/-- Soundness under whisker-left-comp: the `composePath`-associativity reassociation of the left whisker
context, definitionally absorbed on the left. -/
theorem arcStructureOf_whiskerLeftComp {signature : ModeSignature}
    {sourceMode middleModeOne middleModeTwo targetMode : signature.graph.Mode}
    (oneCellOuter : ModalityPath signature.graph sourceMode middleModeOne)
    (oneCellInner : ModalityPath signature.graph middleModeOne middleModeTwo)
    {oneCellDom oneCellCod : ModalityPath signature.graph middleModeTwo targetMode}
    (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
    arcStructureOf (RawTwoCellExpr.whiskerLeft (composePath oneCellOuter oneCellInner) body)
      = arcStructureOf (RawTwoCellExpr.castBoundary
          (composePath_assoc oneCellOuter oneCellInner oneCellDom).symm
          (composePath_assoc oneCellOuter oneCellInner oneCellCod).symm
          (RawTwoCellExpr.whiskerLeft oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body))) := by
  rw [arcStructureOf, arcStructureOf, RawTwoCellExpr.castBoundary_spine]
  dsimp only [RawTwoCellExpr.spine, RawTwoCellExpr.spineDiff]
  rw [composePath_assoc (identityPath sourceMode) oneCellOuter oneCellInner]

/-- Soundness under whisker-right-comp: the right dual. -/
theorem arcStructureOf_whiskerRightComp {signature : ModeSignature}
    {sourceMode middleModeOne middleModeTwo targetMode : signature.graph.Mode}
    {oneCellDom oneCellCod : ModalityPath signature.graph sourceMode middleModeOne}
    (oneCellInner : ModalityPath signature.graph middleModeOne middleModeTwo)
    (oneCellOuter : ModalityPath signature.graph middleModeTwo targetMode)
    (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
    arcStructureOf (RawTwoCellExpr.whiskerRight (composePath oneCellInner oneCellOuter) body)
      = arcStructureOf (RawTwoCellExpr.castBoundary
          (composePath_assoc oneCellDom oneCellInner oneCellOuter)
          (composePath_assoc oneCellCod oneCellInner oneCellOuter)
          (RawTwoCellExpr.whiskerRight oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body))) := by
  rw [arcStructureOf, arcStructureOf, RawTwoCellExpr.castBoundary_spine]
  dsimp only [RawTwoCellExpr.spine, RawTwoCellExpr.spineDiff]
  rw [composePath_assoc]

/-! ## FULL `TwoCellConvFull` soundness — assembled modulo exactly one residual

As in the matching route, the full soundness reduces — with nothing else owed — to the single state-parametric
Godement-step invariance over the richer arc extract.  `arcTraceInvariant_of_godementInvariant` discharges all
the other `SpineTraceEquiv` constructors (reflexivity / symmetry / transitivity, and the head-cons congruence
threads the atom through the arc step), and `arcStructureOf_sound_of_godementInvariant` packages it against
`TwoCellConvFull` through the shipped `twoCellConvFull_spineTraceEquiv`. -/

/-- Run a spine from an ARBITRARY arc state, then read off the arc structure — the state-parametric core. -/
def extractArcAfterProcessing {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (state : ArcWireState) (atoms : List (SpineAtom signature sourceMode targetMode)) :
    FullArcStructure := extractArc bottomCount (processArcSpine state atoms)

/-- Trace invariance of the state-parametric arc extract, REDUCED to the single Godement-step case: given that
the Godement spine step preserves the arc extract from every state, full `SpineTraceEquiv` does. -/
theorem arcTraceInvariant_of_godementInvariant {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat)
    (godementInvariant : ∀ (state : ArcWireState)
        {firstList secondList : List (SpineAtom signature overallSource overallTarget)},
        SpineGodementStep signature firstList secondList →
        extractArcAfterProcessing bottomCount state firstList
          = extractArcAfterProcessing bottomCount state secondList)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (equiv : SpineTraceEquiv signature firstList secondList) :
    ∀ (state : ArcWireState),
      extractArcAfterProcessing bottomCount state firstList
        = extractArcAfterProcessing bottomCount state secondList := by
  induction equiv with
  | ofStep step => intro state; exact godementInvariant state step
  | refl _ => intro _; rfl
  | symm _ inductionHypothesis => intro state; exact (inductionHypothesis state).symm
  | trans _ _ firstHypothesis secondHypothesis =>
      intro state; exact (firstHypothesis state).trans (secondHypothesis state)
  | consCongr atom _ inductionHypothesis => intro state; exact inductionHypothesis (stepArcAtom state atom)

/-- ★ **FULL `TwoCellConvFull` soundness of `arcStructureOf`, assembled modulo one residual.**  Given the
state-parametric Godement-step invariance, `arcStructureOf` is invariant under the COMPLETE
free-strict-2-category convertibility — every structural law, all whisker functoriality, every congruence, and
the interchange step.  All of it routes through the proven `twoCellConvFull_spineTraceEquiv`; the ONLY input
owed is the one Godement lemma. -/
theorem arcStructureOf_sound_of_godementInvariant {signature : ModeSignature}
    (godementInvariant : ∀ {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat)
        (state : ArcWireState)
        {firstList secondList : List (SpineAtom signature overallSource overallTarget)},
        SpineGodementStep signature firstList secondList →
        extractArcAfterProcessing bottomCount state firstList
          = extractArcAfterProcessing bottomCount state secondList)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (convFull : TwoCellConvFull signature firstCell secondCell) :
    arcStructureOf firstCell = arcStructureOf secondCell :=
  arcTraceInvariant_of_godementInvariant sourcePath.length
    (fun state {_firstList _secondList} step => godementInvariant sourcePath.length state step)
    (twoCellConvFull_spineTraceEquiv convFull)
    (ArcWireState.mk (List.range sourcePath.length) [] sourcePath.length 0 [] [])

/-! ## The cup / cap counts are UNCONDITIONAL `TwoCellConvFull` invariants

The new arc data has two parts.  The per-component attribution rides the connectivity residual above.  But the
cup/cap TOTALS are unconditionally `TwoCellConvFull`-invariant — a refinement of the generator count splitting
it by turnback kind — proved directly by induction on the convertibility, with no Godement residual.  These
already separate the snake (one cup, one cap) from the identity (none), giving the snake gap an UNCONDITIONAL
finer witness than the matching route's generator count. -/

/-- The number of CUP generators (`0 => 2` turnbacks) in a free 2-cell, by structural recursion on the
expression.  Whiskering recurses into the body without changing its generator leaves' intrinsic boundaries, so
reading the boundary lengths at a `gen` leaf reads the generator's intrinsic arity. -/
def RawTwoCellExpr.cupCount {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Nat
  | _, _, sourcePath, targetPath, .gen _ => if sourcePath.length == 0 && targetPath.length == 2 then 1 else 0
  | _, _, _, _, .id _ => 0
  | _, _, _, _, .vcomp cellAlpha cellBeta => cellAlpha.cupCount + cellBeta.cupCount
  | _, _, _, _, .whiskerLeft _ cellBeta => cellBeta.cupCount
  | _, _, _, _, .whiskerRight _ cellBeta => cellBeta.cupCount

/-- The number of CAP generators (`2 => 0` turnbacks) in a free 2-cell. -/
def RawTwoCellExpr.capCount {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Nat
  | _, _, sourcePath, targetPath, .gen _ => if sourcePath.length == 2 && targetPath.length == 0 then 1 else 0
  | _, _, _, _, .id _ => 0
  | _, _, _, _, .vcomp cellAlpha cellBeta => cellAlpha.capCount + cellBeta.capCount
  | _, _, _, _, .whiskerLeft _ cellBeta => cellBeta.capCount
  | _, _, _, _, .whiskerRight _ cellBeta => cellBeta.capCount

/-- Middle-four exchange for `Nat` addition: `(a + b) + (c + d) = (a + c) + (b + d)` — the arithmetic shape of
the interchange law on turnback counts.  Propext-free (explicit `Nat.add_assoc` / `Nat.add_left_comm`). -/
private theorem natMiddleFourExchange (first second third fourth : Nat) :
    (first + second) + (third + fourth) = (first + third) + (second + fourth) := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm second third fourth]

/-- A boundary cast preserves the cup count. -/
theorem RawTwoCellExpr.cupCount_castBoundary {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    (RawTwoCellExpr.castBoundary hsource htarget cell).cupCount = cell.cupCount := by
  cases hsource; cases htarget; rfl

/-- A boundary cast preserves the cap count. -/
theorem RawTwoCellExpr.capCount_castBoundary {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    (RawTwoCellExpr.castBoundary hsource htarget cell).capCount = cell.capCount := by
  cases hsource; cases htarget; rfl

/-- The cup count is preserved by every 3-cell rewrite (interchange included): the interchange case is the
middle-four exchange of the four blocks' counts. -/
theorem TwoCellStep.cupCount_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStep signature expr reduct) : expr.cupCount = reduct.cupCount := by
  induction step with
  | vcompIdLeft _ => dsimp only [RawTwoCellExpr.cupCount]; rw [Nat.zero_add]
  | vcompIdRight _ => dsimp only [RawTwoCellExpr.cupCount]; rw [Nat.add_zero]
  | vcompAssoc _ _ _ => dsimp only [RawTwoCellExpr.cupCount]; rw [Nat.add_assoc]
  | whiskerLeftId _ _ => rfl
  | whiskerRightId _ _ => rfl
  | whiskerLeftVcomp _ _ _ => rfl
  | whiskerRightVcomp _ _ _ => rfl
  | vcompCongrLeft _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.cupCount]; rw [inductionHypothesis]
  | vcompCongrRight _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.cupCount]; rw [inductionHypothesis]
  | whiskerLeftCongr _ _ inductionHypothesis => exact inductionHypothesis
  | whiskerRightCongr _ _ inductionHypothesis => exact inductionHypothesis
  | interchange cellAlpha cellAlphaUpper cellBeta cellBetaUpper =>
      dsimp only [RawTwoCellExpr.hcomp, RawTwoCellExpr.cupCount]
      exact natMiddleFourExchange cellAlpha.cupCount cellAlphaUpper.cupCount
        cellBeta.cupCount cellBetaUpper.cupCount

/-- The cap count is preserved by every 3-cell rewrite. -/
theorem TwoCellStep.capCount_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStep signature expr reduct) : expr.capCount = reduct.capCount := by
  induction step with
  | vcompIdLeft _ => dsimp only [RawTwoCellExpr.capCount]; rw [Nat.zero_add]
  | vcompIdRight _ => dsimp only [RawTwoCellExpr.capCount]; rw [Nat.add_zero]
  | vcompAssoc _ _ _ => dsimp only [RawTwoCellExpr.capCount]; rw [Nat.add_assoc]
  | whiskerLeftId _ _ => rfl
  | whiskerRightId _ _ => rfl
  | whiskerLeftVcomp _ _ _ => rfl
  | whiskerRightVcomp _ _ _ => rfl
  | vcompCongrLeft _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.capCount]; rw [inductionHypothesis]
  | vcompCongrRight _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.capCount]; rw [inductionHypothesis]
  | whiskerLeftCongr _ _ inductionHypothesis => exact inductionHypothesis
  | whiskerRightCongr _ _ inductionHypothesis => exact inductionHypothesis
  | interchange cellAlpha cellAlphaUpper cellBeta cellBetaUpper =>
      dsimp only [RawTwoCellExpr.hcomp, RawTwoCellExpr.capCount]
      exact natMiddleFourExchange cellAlpha.capCount cellAlphaUpper.capCount
        cellBeta.capCount cellBetaUpper.capCount

/-- The cup count is a `TwoCellConv` invariant. -/
theorem TwoCellConv.cupCount_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature firstCell secondCell) : firstCell.cupCount = secondCell.cupCount := by
  induction conv with
  | ofStep step => exact step.cupCount_eq
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis

/-- The cap count is a `TwoCellConv` invariant. -/
theorem TwoCellConv.capCount_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature firstCell secondCell) : firstCell.capCount = secondCell.capCount := by
  induction conv with
  | ofStep step => exact step.capCount_eq
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis

/-- ★ **The cup count is invariant under the completed convertibility `TwoCellConvFull`.**  By induction: each
whisker-functoriality law passes the count through a whiskering / boundary cast unchanged, the congruences thread
the inductive hypothesis, and the structural / interchange content comes from `TwoCellConv.cupCount_eq`. -/
theorem TwoCellConvFull.cupCount_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (convFull : TwoCellConvFull signature firstCell secondCell) :
    firstCell.cupCount = secondCell.cupCount := by
  induction convFull with
  | ofConv conv => exact conv.cupCount_eq
  | whiskerLeftUnit _ => rfl
  | whiskerRightUnit body => exact (RawTwoCellExpr.cupCount_castBoundary _ _ body).symm
  | whiskerLeftComp oneCellOuter oneCellInner body =>
      exact (RawTwoCellExpr.cupCount_castBoundary _ _
        (RawTwoCellExpr.whiskerLeft oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body))).symm
  | whiskerRightComp oneCellInner oneCellOuter body =>
      exact (RawTwoCellExpr.cupCount_castBoundary _ _
        (RawTwoCellExpr.whiskerRight oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body))).symm
  | vcompCongrLeft _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.cupCount]; rw [inductionHypothesis]
  | vcompCongrRight _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.cupCount]; rw [inductionHypothesis]
  | whiskerLeftCongr _ _ inductionHypothesis => exact inductionHypothesis
  | whiskerRightCongr _ _ inductionHypothesis => exact inductionHypothesis
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis

/-- ★ **The cap count is invariant under `TwoCellConvFull`.** -/
theorem TwoCellConvFull.capCount_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (convFull : TwoCellConvFull signature firstCell secondCell) :
    firstCell.capCount = secondCell.capCount := by
  induction convFull with
  | ofConv conv => exact conv.capCount_eq
  | whiskerLeftUnit _ => rfl
  | whiskerRightUnit body => exact (RawTwoCellExpr.capCount_castBoundary _ _ body).symm
  | whiskerLeftComp oneCellOuter oneCellInner body =>
      exact (RawTwoCellExpr.capCount_castBoundary _ _
        (RawTwoCellExpr.whiskerLeft oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body))).symm
  | whiskerRightComp oneCellInner oneCellOuter body =>
      exact (RawTwoCellExpr.capCount_castBoundary _ _
        (RawTwoCellExpr.whiskerRight oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body))).symm
  | vcompCongrLeft _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.capCount]; rw [inductionHypothesis]
  | vcompCongrRight _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.capCount]; rw [inductionHypothesis]
  | whiskerLeftCongr _ _ inductionHypothesis => exact inductionHypothesis
  | whiskerRightCongr _ _ inductionHypothesis => exact inductionHypothesis
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis

/-! ## The crux: the arc structure DISTINGUISHES the snake from the identity

The matching route's `decisionVacuity_at_seed` proved the boundary matching agrees on the identity, the snake,
and the double snake (all `{1, 1, [1,0], 0}`).  The arc structure SEPARATES them: the snake's single strand
carries one cup-turnback and one cap-turnback (`internalCupCounts = [1, 1]`, `internalCapCounts = [1, 1]`), the
identity's carries none (`[0, 0]`, `[0, 0]`).  This is the crux that validates the whole geometric route — it
fixes the decision-vacuity the boundary matching could not. -/

/-- The snake's full arc structure: a single through-strand (boundary `{1, 1, [1,0], 0}`) carrying ONE
cup-turnback and ONE cap-turnback. -/
theorem snake_arcStructureOf :
    arcStructureOf snakeOnLeft =
      { diagram := { bottomCount := 1, topCount := 1, partner := [1, 0], loops := 0 },
        cupCount := 1, capCount := 1, internalCupCounts := [1, 1], internalCapCounts := [1, 1] } := rfl

/-- The identity-on-`left` full arc structure: the SAME boundary, but a straight strand with NO turnbacks. -/
theorem identityOnLeft_arcStructureOf :
    arcStructureOf identityOnLeft =
      { diagram := { bottomCount := 1, topCount := 1, partner := [1, 0], loops := 0 },
        cupCount := 0, capCount := 0, internalCupCounts := [0, 0], internalCapCounts := [0, 0] } := rfl

/-- The snake's cup count, read off its arc structure, is `1`. -/
theorem snake_arcStructureOf_cupCount : (arcStructureOf snakeOnLeft).cupCount = 1 := rfl

/-- The identity's cup count, read off its arc structure, is `0`. -/
theorem identityOnLeft_arcStructureOf_cupCount : (arcStructureOf identityOnLeft).cupCount = 0 := rfl

/-- The snake's internal cup-turnback data, read per boundary port, is `[1, 1]`. -/
theorem snake_internalCupCounts : (arcStructureOf snakeOnLeft).internalCupCounts = [1, 1] := rfl

/-- The identity's internal cup-turnback data is `[0, 0]`. -/
theorem identityOnLeft_internalCupCounts : (arcStructureOf identityOnLeft).internalCupCounts = [0, 0] := rfl

/-- The snake's internal cup-turnback data differs from the identity's even at the boundary-port level
(`[1, 1]` vs `[0, 0]`): a GEOMETRIC, not merely numeric, separation. -/
theorem snake_internalCupCounts_ne_identity :
    (arcStructureOf snakeOnLeft).internalCupCounts ≠ (arcStructureOf identityOnLeft).internalCupCounts := by
  rw [snake_internalCupCounts, identityOnLeft_internalCupCounts]; decide

/-- ★ **CRUX — the arc structure distinguishes the snake from the identity** (where the boundary matching
could not).  Via the cup-turnback count `1 ≠ 0`; the full `rfl` structures (`snake_arcStructureOf`,
`identityOnLeft_arcStructureOf`) also exhibit the separation in `internalCupCounts` / `internalCapCounts`.  This
is the geometric content the matching shadow forgot — fixing the decision-vacuity at the seed. -/
theorem snake_arcStructureOf_ne_identity : arcStructureOf snakeOnLeft ≠ arcStructureOf identityOnLeft := by
  intro structures_equal
  have cupsEqual : (arcStructureOf snakeOnLeft).cupCount = (arcStructureOf identityOnLeft).cupCount :=
    congrArg FullArcStructure.cupCount structures_equal
  rw [snake_arcStructureOf_cupCount, identityOnLeft_arcStructureOf_cupCount] at cupsEqual
  exact Nat.noConfusion cupsEqual

/-- The double snake's arc structure: TWO cup-turnbacks and two cap-turnbacks on the strand — distinct again
from both the snake and the identity (where the matching collapses all three). -/
theorem doubleSnake_arcStructureOf :
    arcStructureOf doubleSnakeOnLeft =
      { diagram := { bottomCount := 1, topCount := 1, partner := [1, 0], loops := 0 },
        cupCount := 2, capCount := 2, internalCupCounts := [2, 2], internalCapCounts := [2, 2] } := rfl

/-- The double snake's cup count, read off its arc structure, is `2`. -/
theorem doubleSnake_arcStructureOf_cupCount : (arcStructureOf doubleSnakeOnLeft).cupCount = 2 := rfl

/-- ★ **The arc structure REFUTES the seed's decision-vacuity.**  The three cells the matching route collapsed
to one boundary type now get THREE pairwise-distinct arc structures (cup counts `0`, `1`, `2`).  Where
`matchingOf` could not refute any parallel pair at the seed, `arcStructureOf` refutes all three — the finer
invariant the seed needed. -/
theorem arcStructure_separates_at_seed :
    arcStructureOf identityOnLeft ≠ arcStructureOf snakeOnLeft
      ∧ arcStructureOf snakeOnLeft ≠ arcStructureOf doubleSnakeOnLeft
      ∧ arcStructureOf identityOnLeft ≠ arcStructureOf doubleSnakeOnLeft := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have counts := congrArg FullArcStructure.cupCount h
    rw [identityOnLeft_arcStructureOf_cupCount, snake_arcStructureOf_cupCount] at counts
    exact Nat.noConfusion counts
  · have counts := congrArg FullArcStructure.cupCount h
    rw [snake_arcStructureOf_cupCount, doubleSnake_arcStructureOf_cupCount] at counts
    exact absurd counts (by decide)
  · have counts := congrArg FullArcStructure.cupCount h
    rw [identityOnLeft_arcStructureOf_cupCount, doubleSnake_arcStructureOf_cupCount] at counts
    exact Nat.noConfusion counts

/-! ## The interchange-obstruction smokes: the arc data is BLIND to interchange (unconditionally)

The interchange / Godement endpoints — the parallel units and the contracting parallel counits that no oriented
rewrite could join — agree on the cup/cap-COUNT components of the arc structure, UNCONDITIONALLY (via the
cell-level count invariance, no Godement residual and no heavy kernel reduction).  This is the arc-level analog
of the matching route's obstruction smokes: the geometric route sees through the orientation asymmetry that
blocked rewriting.  The FULL arc-structure equality on these witnesses
(`arcStructureOf redex = arcStructureOf reduct`) is the named Godement residual — computationally confirmed but
kernel-defeq-heavy on the large parallel cells, so it is exhibited here through its unconditional count
components. -/

/-- ★ The two parallel-units interchange endpoints agree on the cup count (unconditionally — interchange
preserves the multiset of cup turnbacks). -/
theorem parallelUnits_cupCount_eq : parallelUnitsRedex.cupCount = parallelUnitsReduct.cupCount :=
  parallelUnitsConvFull.cupCount_eq

/-- ★ ... and on the cap count. -/
theorem parallelUnits_capCount_eq : parallelUnitsRedex.capCount = parallelUnitsReduct.capCount :=
  parallelUnitsConvFull.capCount_eq

/-- ★ The two parallel-COUNITS Godement endpoints — the contracting-transposition obstruction the oriented
reducer proved un-orientable — agree on the cap count (unconditionally). -/
theorem parallelCounits_capCount_eq : parallelCounitsRedex.capCount = parallelCounitsReduct.capCount :=
  parallelCounitsConvFull.capCount_eq

/-- ★ ... and on the cup count. -/
theorem parallelCounits_cupCount_eq : parallelCounitsRedex.cupCount = parallelCounitsReduct.cupCount :=
  parallelCounitsConvFull.cupCount_eq

/-! ## The decision, assembled GATED on the two precise residuals

`arcStructureOf` is a complete invariant of `SpineTraceEquiv` exactly when it is both SOUND (trace-equivalent
spines share an arc structure — the Godement residual) and COMPLETE (equal arc structures are trace-equivalent
— the Joyal-Street reconstruction residual).  Given both, the decision is a one-line dependent-if over the
decidable arc-structure equality.  We expose the decision GATED on exactly those inputs, so the outstanding
obligations are explicit. -/

/-- Trace-invariance of `arcStructureOf` on the spine, REDUCED to the Godement residual (the sound direction). -/
theorem arcStructureOfSpineList_traceInvariant {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat)
    (godementInvariant : ∀ (state : ArcWireState)
        {firstList secondList : List (SpineAtom signature overallSource overallTarget)},
        SpineGodementStep signature firstList secondList →
        extractArcAfterProcessing bottomCount state firstList
          = extractArcAfterProcessing bottomCount state secondList)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (equiv : SpineTraceEquiv signature firstList secondList) :
    arcStructureOfSpineList bottomCount firstList = arcStructureOfSpineList bottomCount secondList :=
  arcTraceInvariant_of_godementInvariant bottomCount godementInvariant equiv
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])

/-- ★ **`Decidable (SpineTraceEquiv ...)`, GATED on the two residuals.**  Given soundness (trace-equivalence
implies equal arc structure) and completeness (the reconstruction), trace equivalence is decided by comparing
the (decidable, computing) arc structures.  The `isFalse` branch uses soundness; the `isTrue` branch the
reconstruction. -/
def decidableSpineTraceEquiv_of {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat)
    (sound : ∀ {firstList secondList : List (SpineAtom signature overallSource overallTarget)},
        SpineTraceEquiv signature firstList secondList →
        arcStructureOfSpineList bottomCount firstList = arcStructureOfSpineList bottomCount secondList)
    (complete : ∀ {firstList secondList : List (SpineAtom signature overallSource overallTarget)},
        arcStructureOfSpineList bottomCount firstList = arcStructureOfSpineList bottomCount secondList →
        SpineTraceEquiv signature firstList secondList)
    (firstList secondList : List (SpineAtom signature overallSource overallTarget)) :
    Decidable (SpineTraceEquiv signature firstList secondList) :=
  if structuresEqual : arcStructureOfSpineList bottomCount firstList = arcStructureOfSpineList bottomCount secondList
  then isTrue (complete structuresEqual)
  else isFalse (fun equiv => structuresEqual (sound equiv))

/-- ★ **`Decidable (TwoCellConvFull ...)`, GATED on the precise residuals.**  Given (1) the Godement union-find
independence (`godementInvariant`, yielding `arcStructureOf` soundness through the shipped
`twoCellConvFull_spineTraceEquiv`), and (2) the cell-level reconstruction (equal arc structures are
convertible), the completed free-strict-2-category convertibility is decided by comparing the (computing) arc
structures.  This is the FREE-system word-problem decision, with its two outstanding obligations made
explicit. -/
def decidableTwoCellConvFull_of {signature : ModeSignature}
    (godementInvariant : ∀ {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat)
        (state : ArcWireState)
        {firstList secondList : List (SpineAtom signature overallSource overallTarget)},
        SpineGodementStep signature firstList secondList →
        extractArcAfterProcessing bottomCount state firstList
          = extractArcAfterProcessing bottomCount state secondList)
    (reconstruct : ∀ {sourceMode targetMode : signature.graph.Mode}
        {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
        {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath},
        arcStructureOf firstCell = arcStructureOf secondCell → TwoCellConvFull signature firstCell secondCell)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath) :
    Decidable (TwoCellConvFull signature firstCell secondCell) :=
  if structuresEqual : arcStructureOf firstCell = arcStructureOf secondCell
  then isTrue (reconstruct structuresEqual)
  else isFalse (fun convFull =>
    structuresEqual (arcStructureOf_sound_of_godementInvariant godementInvariant convFull))

/-! ## Honesty markers -/

/-- **Honesty marker — the arc structure CLOSES the snake gap (the matching route's incompleteness).**
`arcStructureOf` is strictly finer than `matchingOf`: it separates the snake from the identity
(`snake_arcStructureOf_ne_identity`) and refutes the seed's three-way decision-vacuity
(`arcStructure_separates_at_seed`), where the boundary matching collapsed all three to one type.  The cup/cap
TOTALS in it are UNCONDITIONALLY `TwoCellConvFull`-invariant (`TwoCellConvFull.cupCount_eq` /
`.capCount_eq`).  This is the validating contribution: the geometric route's invariant sees the internal arcs
the boundary matching forgot.  `= true`. -/
def fxMode_hasArcStructureClosesSnakeGap : Bool := true

/-- **Honesty marker — full `arcStructureOf` soundness is ASSEMBLED modulo one named lemma (shared with the
matching route).**  `arcStructureOf_sound_of_godementInvariant` proves invariance under the COMPLETE
`TwoCellConvFull` GIVEN the state-parametric Godement-step invariance of the arc extract — the union-find
INDEPENDENCE of two horizontally-disjoint blocks, now over the richer (event-tracking) extract.  TRUE (a
state-renaming simulation; the fresh-id allocation differs, the extracted `FullArcStructure` does not) and
computationally confirmed on every obstruction witness (whose unconditional count components are
`parallelUnits_cupCount_eq` / `parallelCounits_capCount_eq`); its general zero-axiom proof is the single
outstanding soundness
obligation.  `= false`. -/
def fxMode_hasArcGodementIndependenceProof : Bool := false

/-- **Honesty marker — the RECONSTRUCTION (Joyal-Street completeness) is the named residual.**  The YES-direction
`arcStructureOf a = arcStructureOf b -> SpineTraceEquiv a b` (same planar-arc type implies planar-isotopic implies
trace-equivalent — Joyal-Street) is the list-level Mazurkiewicz reconstruction over the realizable cup/cap arc
structures, and it composes with the spine->cell reconstruction (`fxMode_hasSpineTraceReconstruction`) to a
cell-level reconstruction.  `decidableSpineTraceEquiv_of` / `decidableTwoCellConvFull_of` land
`Decidable (...)` GATED on exactly this plus the Godement independence above.  `= false`. -/
def fxMode_hasArcStructureReconstruction : Bool := false

/-- **Honesty marker — the assembled FREE-system decision.**  `decidableTwoCellConvFull_of` is the complete
free-2-cell word-problem decision via the full planar-arc invariant, GATED on the two residuals
(`fxMode_hasArcGodementIndependenceProof`, `fxMode_hasArcStructureReconstruction`).  Until both discharge it
stays a conditional decision; the unconditional content shipped here is the invariant itself, its
structural-and-whisker soundness, the unconditional cup/cap-count invariance, and the snake-gap-closing crux.
`= false`. -/
def fxMode_hasCompleteArcDecision : Bool := false

end FX1Poly.Tier0
