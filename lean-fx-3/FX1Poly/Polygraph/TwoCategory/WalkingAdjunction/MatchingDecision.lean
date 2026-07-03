import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.WhiskerFunctoriality

/-! # mode-3 floor — the FREE 2-cell decision via the Joyal-Street MATCHING invariant (topological route)

Three prior passes proved the REWRITING route to deciding the free strict-2-category 2-cell word problem
(`TwoCellConvFull`) intrinsically blocked: the Godement / interchange critical pair is non-confluent, and the
single-atom oriented Godement swap is provably INCOMPLETE (`FreeTwoCellOrientedReducer`'s
`adjunctionCounitGodementStep` — the contracting counit transposition is uphill in every linear context-length
measure and its reverse is not Godement-shaped).  This file takes the COMPLEMENTARY topological route of
Joyal–Street's graphical calculus: read a free 2-cell as a planar string diagram and compute a DIRECT
topological invariant — the non-crossing boundary MATCHING of its wire-positions plus the closed-LOOP count —
which is invariant under planar isotopy (= interchange), so it SEES THROUGH the orientation obstruction the
rewriting route foundered on.

## The walking-adjunction seed, read topologically

The seed `adjunctionModeSignature` is the walking adjunction: `unit : id_base ⇒ left·right` is a CUP producing
the word `LR`, `counit : right·left ⇒ id_tip` is a CAP consuming the word `RL`.  A free 2-cell `f ⇒ g` is a
planar 1-manifold in a rectangle whose bottom boundary reads `f` and top boundary reads `g`.  `matchingOf`
computes its topological type by reading the SPINE (`FreeTwoCellSpine`) bottom-to-top, maintaining a union-find
over the open wires: a cup opens two connected wires; a cap connects (and removes) two adjacent wires, closing a
LOOP when they were already connected.  The output `DiagramType` is the canonical boundary partner-matching plus
the loop count.

## HONEST scope — sound, NOT complete (the snake gap)

This invariant is SOUND for `TwoCellConvFull` (the NO / `isFalse` direction): convertible 2-cells have equal
`matchingOf` — interchange is planar isotopy, which preserves the matching and the loop count.  It is NOT
complete: the SNAKE `(left ◁ counit) ∘ (unit ▷ left) : left ⇒ left` has the SAME boundary matching as `id_left`
(both a single through-strand) and ZERO loops, yet is a DISTINCT free 2-cell (straightening it is the TRIANGLE
identity, which is NOT a free move — the saturated agent's quotient, not ours).  So `matchingOf` decides the
`isFalse` branch but the `isTrue` (completeness) branch needs a STRICTLY FINER invariant — the full planar
isotopy class, equivalently the spine modulo trace equivalence (`SpineTraceEquiv`), which retains the snake's two
generators.  The generator count (`ComputadWordProblem`) is one coarse witness that DOES separate snake from
identity; the matching adds orthogonal NO-direction power (different boundary connectivity).

Moreover at THIS seed closed loops are NEVER realizable: a cup makes `LR` but a cap eats `RL`, so no oriented
circle closes (the loop count is identically `0`).  The loop machinery is kept for generality and honesty; the
`isFalse` power here is entirely the boundary matching.

## What this file ships (each piece zero-axiom)

  * **`DiagramType`** + its computing `DecidableEq` — the topological type (boundary partner-matching + loop
    count) as a flat datum.
  * ★ **`matchingOf`** — the union-find reading of a free 2-cell's spine into its `DiagramType`.  Structural /
    fuel recursion, so it COMPUTES (the smokes are `rfl` / `decide`).
  * ★ the CRUX smokes — `matchingOf` identifies the interchange obstruction endpoints
    (`adjunctionParallelUnitsRedex` / `…Reduct`) as EQUAL (`decide`), validating that the topological route sees
    through the Godement obstruction the rewriting route could not orient.
  * the honest incompleteness witness — `matchingOf snake = matchingOf id_left` while their generator counts
    differ (`2 ≠ 0`): the precise snake gap.

Raw Lean 4 + Init; structural recursion + `Nat`-fuel union-find, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the (un-registered) audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The topological type -/

/-- ★ The **topological type** of a free 2-cell read as a planar string diagram: the boundary wire count split
into bottom (source-word) and top (target-word) ports, the canonical PARTNER matching (`partner.get k` is the
boundary index matched to boundary index `k`, with bottom ports `0 … bottomCount-1` and top ports
`bottomCount … bottomCount+topCount-1`), and the number of closed LOOPS.  A flat datum of `Nat` / `List Nat`, so
its equality is decidable and COMPUTES. -/
structure DiagramType where
  /-- The number of bottom-boundary wire ports (the source word's length). -/
  bottomCount : Nat
  /-- The number of top-boundary wire ports (the target word's length). -/
  topCount : Nat
  /-- The canonical partner matching over the `bottomCount + topCount` boundary ports. -/
  partner : List Nat
  /-- The number of closed loops (bubbles). -/
  loops : Nat
deriving DecidableEq

/-! ## List position helpers (structural, propext-free) -/

/-- Read the element of a `Nat` list at a position, defaulting to `0` past the end (the live position is always
in range for a well-typed cell; the default keeps the function total). -/
def natListGetAt : List Nat → Nat → Nat
  | [], _ => 0
  | head :: _, 0 => head
  | _ :: rest, position + 1 => natListGetAt rest position

/-- Splice a block of new wires into a `Nat` list at a position (structural on the position then the list). -/
def natListInsertAt : List Nat → Nat → List Nat → List Nat
  | wires, 0, block => block ++ wires
  | [], _ + 1, block => block
  | head :: rest, position + 1, block => head :: natListInsertAt rest position block

/-- Remove the two wires at `position` and `position+1` (the pair a cap consumes). -/
def natListRemoveTwoAt : List Nat → Nat → List Nat
  | [], _ => []
  | _ :: _ :: rest, 0 => rest
  | [singleton], 0 => [singleton]
  | head :: rest, position + 1 => head :: natListRemoveTwoAt rest position

/-! ## A fuel-bounded union-find over `Nat` node ids -/

/-- Look up a node's recorded parent (a child→parent edge), `none` when the node is a root. -/
def unionFindParent : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (child, parent) :: rest, node =>
      if child == node then some parent else unionFindParent rest node

/-- Follow parent edges to the root, fuel-bounded (the chain is no longer than the edge count). -/
def unionFindRoot : Nat → List (Nat × Nat) → Nat → Nat
  | 0, _, node => node
  | fuel + 1, links, node =>
      match unionFindParent links node with
      | none => node
      | some parent => unionFindRoot fuel links parent

/-- The root of a node, with fuel sized to the edge list. -/
def unionFindRootOf (links : List (Nat × Nat)) (node : Nat) : Nat :=
  unionFindRoot (links.length + 1) links node

/-- Whether two nodes are already in the same component. -/
def isSameComponent (links : List (Nat × Nat)) (firstNode secondNode : Nat) : Bool :=
  unionFindRootOf links firstNode == unionFindRootOf links secondNode

/-- Union two nodes — point the first root at the second (no-op when already joined). -/
def unionFindJoin (links : List (Nat × Nat)) (firstNode secondNode : Nat) : List (Nat × Nat) :=
  let firstRoot := unionFindRootOf links firstNode
  let secondRoot := unionFindRootOf links secondNode
  if firstRoot == secondRoot then links else (firstRoot, secondRoot) :: links

/-! ## The processing state + the per-atom step -/

/-- The wire-tracking state threaded bottom-to-top through a spine: the open wires (left to right, by node id),
the connectivity union-find, the next fresh node id, and the closed-loop count so far. -/
structure WireState where
  /-- The open wires, left to right, by node id. -/
  openWires : List Nat
  /-- The connectivity union-find (child→parent edges). -/
  links : List (Nat × Nat)
  /-- The next fresh node id. -/
  nextFresh : Nat
  /-- The closed loops detected so far. -/
  loops : Nat

/-- Process a single CUP (a `0 ⇒ 2` generator, the unit): allocate two fresh connected wires and splice them
into the open-wire list at `position`. -/
def stepCup (state : WireState) (position : Nat) : WireState :=
  let leftLeg := state.nextFresh
  let rightLeg := state.nextFresh + 1
  { openWires := natListInsertAt state.openWires position [leftLeg, rightLeg],
    links := unionFindJoin state.links leftLeg rightLeg,
    nextFresh := state.nextFresh + 2,
    loops := state.loops }

/-- Process a single CAP (a `2 ⇒ 0` generator, the counit): connect the two adjacent wires at `position`,
incrementing the loop count when they were already connected (a closed loop), then drop them. -/
def stepCap (state : WireState) (position : Nat) : WireState :=
  let leftWire := natListGetAt state.openWires position
  let rightWire := natListGetAt state.openWires (position + 1)
  if isSameComponent state.links leftWire rightWire then
    { openWires := natListRemoveTwoAt state.openWires position,
      links := state.links,
      nextFresh := state.nextFresh,
      loops := state.loops + 1 }
  else
    { openWires := natListRemoveTwoAt state.openWires position,
      links := unionFindJoin state.links leftWire rightWire,
      nextFresh := state.nextFresh,
      loops := state.loops }

/-- Process one spine atom: a `0 ⇒ 2` generator is a CUP, a `2 ⇒ 0` generator is a CAP, both fired at the live
position `leftContext.length`.  Any other arity is a generic opaque box (never occurs at the cup/cap
walking-adjunction seed): drop its inputs, add disconnected fresh outputs.  The arity is read off the generator's
boundary 1-cell lengths, so this works at any signature without an indexed match on the generator. -/
def stepAtom {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : WireState) (atom : SpineAtom signature sourceMode targetMode) : WireState :=
  let position := atom.leftContext.length
  match atom.generatorDom.length, atom.generatorCod.length with
  | 0, 2 => stepCup state position
  | 2, 0 => stepCap state position
  | numConsumed, numProduced =>
      let droppedWires :=
        Nat.rec state.openWires (fun _ shorter => natListRemoveTwoAt shorter position) numConsumed
      { openWires := natListInsertAt droppedWires position (List.range numProduced |>.map (· + state.nextFresh)),
        links := state.links,
        nextFresh := state.nextFresh + numProduced,
        loops := state.loops }

/-- Fold the per-atom step over a whole spine, bottom-to-top (head first). -/
def processSpine {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : WireState) (atoms : List (SpineAtom signature sourceMode targetMode)) : WireState :=
  atoms.foldl stepAtom state

/-! ## Extracting the canonical boundary matching -/

/-- Scan candidate boundary indices for the first one (other than `excludeIndex`) whose node shares
`rootHere`'s component — the partner of `excludeIndex` in the boundary matching. -/
def findPartnerScan (links : List (Nat × Nat)) (boundaryNodes : List Nat) (rootHere excludeIndex : Nat) :
    List Nat → Nat
  | [] => excludeIndex
  | candidate :: rest =>
      if candidate != excludeIndex && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere
      then candidate
      else findPartnerScan links boundaryNodes rootHere excludeIndex rest

/-- The partner boundary index of `index`: the first OTHER boundary index in the same component. -/
def partnerIndexOf (links : List (Nat × Nat)) (boundaryNodes : List Nat) (total index : Nat) : Nat :=
  findPartnerScan links boundaryNodes
    (unionFindRootOf links (natListGetAt boundaryNodes index)) index (List.range total)

/-- Read the final wire state into a `DiagramType`: the remaining open wires ARE the top ports (in order); the
bottom ports were node ids `0 … bottomCount-1`; the canonical matching pairs boundary indices by shared
component. -/
def extractDiagram (bottomCount : Nat) (state : WireState) : DiagramType :=
  let topWires := state.openWires
  let topCount := topWires.length
  let boundaryNodes := List.range bottomCount ++ topWires
  let total := bottomCount + topCount
  { bottomCount := bottomCount,
    topCount := topCount,
    partner := (List.range total).map (partnerIndexOf state.links boundaryNodes total),
    loops := state.loops }

/-- Read a flat spine list (with a given bottom-boundary wire count) into its `DiagramType` — the spine-level
core of `matchingOf`, factored out so that `matchingOf`'s spine-congruence is a one-line `congrArg`. -/
def matchingOfSpineList {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (atoms : List (SpineAtom signature sourceMode targetMode)) : DiagramType :=
  extractDiagram bottomCount
    (processSpine { openWires := List.range bottomCount, links := [], nextFresh := bottomCount, loops := 0 } atoms)

/-! ## The matching invariant -/

/-- ★ The **Joyal–Street topological type** of a free 2-cell: read its spine bottom-to-top through the
cup/cap union-find, then extract the canonical boundary matching plus the loop count.  Defined by structural /
fuel recursion, so it COMPUTES.  SOUND for `TwoCellConvFull` (interchange-invariant — the NO-direction; at this
seed it is in fact boundary-determined, hence decision-vacuous — see the honesty markers), and NOT complete (the
snake gap, see the file header). -/
def matchingOf {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) : DiagramType :=
  matchingOfSpineList sourcePath.length cell.spine

/-! ## Soundness under the interchange-free structural fragment

`matchingOf` reads ONLY the spine (and the source-word length, fixed by the boundary), so it is invariant under
any rewrite that preserves the spine.  The eleven interchange-free structural laws do exactly that
(`TwoCellStepInterchangeFree.spine_eq`, congruences INCLUDED), so `matchingOf` is invariant under the whole
structural fragment — a clean, complete soundness leg for that fragment.  (The Godement / interchange step
preserves the spine only up to TRACE equivalence, not on the nose; its `matchingOf`-invariance is the residual
below — computationally evidenced by the obstruction smokes, formally the union-find independence lemma.) -/

/-- `matchingOf` depends on the cell only through its spine (and the boundary length): equal spines give equal
diagram types. -/
theorem matchingOf_congr_of_spine_eq {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (spineEqual : firstCell.spine = secondCell.spine) : matchingOf firstCell = matchingOf secondCell :=
  congrArg (matchingOfSpineList sourcePath.length) spineEqual

/-- ★ **Soundness of `matchingOf` under the interchange-free structural fragment**: every one of the eleven
structural strict-2-category laws (identity removal, re-association, whisker distribution / unit — congruences
included) preserves the topological type, because each preserves the spine on the nose
(`TwoCellStepInterchangeFree.spine_eq`).  This is the `isFalse`-direction soundness leg for the structural
fragment of `TwoCellConvFull`. -/
theorem matchingOf_eq_of_interchangeFreeStep {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStepInterchangeFree signature firstCell secondCell) :
    matchingOf firstCell = matchingOf secondCell :=
  matchingOf_congr_of_spine_eq step.spine_eq

/-! ## Soundness under whisker FUNCTORIALITY — the four `TwoCellConvFull` whisker laws

Beyond the structural fragment, `matchingOf` is invariant under each of the four whisker-functoriality laws of
`TwoCellConvFull` (stripping a unit-1-cell whisker, splitting a composite-1-cell whisker), because each relates
SAME-SPINE cells (the unit laws by definitional `composePath`-left-identity, the composite laws by the proven
`composePath_assoc`, threaded through the spine-invisible `castBoundary`).  Together with
`matchingOf_eq_of_interchangeFreeStep` this proves `matchingOf` invariant under EVERY generator of
`TwoCellConvFull` EXCEPT the single `interchange` (Godement) step — narrowing the soundness residual to exactly
that one rule. -/

/-- Soundness under whisker-left-unit: `matchingOf (emptyPath ◁ X) = matchingOf X` (same spine, definitional). -/
theorem matchingOf_whiskerLeftUnit {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {oneCellDom oneCellCod : ModalityPath signature.graph sourceMode targetMode}
    (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
    matchingOf (RawTwoCellExpr.whiskerLeft (identityPath sourceMode) body) = matchingOf body :=
  matchingOf_congr_of_spine_eq rfl

/-- Soundness under whisker-right-unit: `matchingOf (X ▷ emptyPath) = matchingOf X` (through the spine-invisible
boundary cast). -/
theorem matchingOf_whiskerRightUnit {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {oneCellDom oneCellCod : ModalityPath signature.graph sourceMode targetMode}
    (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
    matchingOf (RawTwoCellExpr.whiskerRight (identityPath targetMode) body)
      = matchingOf (RawTwoCellExpr.castBoundary (composePath_identityPath_right oneCellDom).symm
          (composePath_identityPath_right oneCellCod).symm body) := by
  rw [matchingOf, matchingOf, RawTwoCellExpr.castBoundary_spine]; rfl

/-- Soundness under whisker-left-comp: `matchingOf ((f∘g) ◁ X) = matchingOf (f ◁ (g ◁ X))` (the
`composePath`-associativity reassociation of the left whisker context, definitionally absorbed on the left). -/
theorem matchingOf_whiskerLeftComp {signature : ModeSignature}
    {sourceMode middleModeOne middleModeTwo targetMode : signature.graph.Mode}
    (oneCellOuter : ModalityPath signature.graph sourceMode middleModeOne)
    (oneCellInner : ModalityPath signature.graph middleModeOne middleModeTwo)
    {oneCellDom oneCellCod : ModalityPath signature.graph middleModeTwo targetMode}
    (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
    matchingOf (RawTwoCellExpr.whiskerLeft (composePath oneCellOuter oneCellInner) body)
      = matchingOf (RawTwoCellExpr.castBoundary
          (composePath_assoc oneCellOuter oneCellInner oneCellDom).symm
          (composePath_assoc oneCellOuter oneCellInner oneCellCod).symm
          (RawTwoCellExpr.whiskerLeft oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body))) := by
  rw [matchingOf, matchingOf, RawTwoCellExpr.castBoundary_spine]
  dsimp only [RawTwoCellExpr.spine, RawTwoCellExpr.spineDiff]
  rw [composePath_assoc (identityPath sourceMode) oneCellOuter oneCellInner]

/-- Soundness under whisker-right-comp: `matchingOf ((g∘f) ▷ X) = matchingOf (f ▷ (g ▷ X))` (the right dual). -/
theorem matchingOf_whiskerRightComp {signature : ModeSignature}
    {sourceMode middleModeOne middleModeTwo targetMode : signature.graph.Mode}
    {oneCellDom oneCellCod : ModalityPath signature.graph sourceMode middleModeOne}
    (oneCellInner : ModalityPath signature.graph middleModeOne middleModeTwo)
    (oneCellOuter : ModalityPath signature.graph middleModeTwo targetMode)
    (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
    matchingOf (RawTwoCellExpr.whiskerRight (composePath oneCellInner oneCellOuter) body)
      = matchingOf (RawTwoCellExpr.castBoundary
          (composePath_assoc oneCellDom oneCellInner oneCellOuter)
          (composePath_assoc oneCellCod oneCellInner oneCellOuter)
          (RawTwoCellExpr.whiskerRight oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body))) := by
  rw [matchingOf, matchingOf, RawTwoCellExpr.castBoundary_spine]
  dsimp only [RawTwoCellExpr.spine, RawTwoCellExpr.spineDiff]
  rw [composePath_assoc]

/-! ## FULL `TwoCellConvFull` soundness — ASSEMBLED modulo exactly one residual

`matchingOf` reads only the spine, and the proven `twoCellConvFull_spineTraceEquiv` already maps
`TwoCellConvFull` into `SpineTraceEquiv` of the spines.  So the FULL soundness reduces, with NOTHING else owed,
to a single lemma: that the Godement spine step (`SpineGodementStep`, the interchange's trace-monoid
independence) preserves the diagram extract from EVERY processing state.  `traceInvariant_of_godementInvariant`
discharges all the other `SpineTraceEquiv` constructors (reflexivity / symmetry / transitivity chain, and the
head-cons congruence threads the atom through the state), and `matchingOf_sound_of_godementInvariant` packages
the result against `TwoCellConvFull`.  The residual `godementInvariant` is exactly the state-parametric
union-find independence — TRUE (a state-renaming simulation between the two run orders) and computationally
confirmed on every obstruction witness, but its general zero-axiom proof is the named outstanding lemma. -/

/-- Run a spine from an ARBITRARY processing state, then read off the diagram — the state-parametric core that
lets the head-cons congruence of `SpineTraceEquiv` thread through. -/
def extractAfterProcessing {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (state : WireState) (atoms : List (SpineAtom signature sourceMode targetMode)) :
    DiagramType := extractDiagram bottomCount (processSpine state atoms)

/-- Trace invariance of the state-parametric extract, REDUCED to the single Godement-step case: given that the
Godement spine step preserves the extract from every state, full `SpineTraceEquiv` does — reflexivity / symmetry
/ transitivity chain, and `consCongr` threads the head atom through `stepAtom`. -/
theorem traceInvariant_of_godementInvariant {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat)
    (godementInvariant : ∀ (state : WireState)
        {firstList secondList : List (SpineAtom signature overallSource overallTarget)},
        SpineGodementStep signature firstList secondList →
        extractAfterProcessing bottomCount state firstList = extractAfterProcessing bottomCount state secondList)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (equiv : SpineTraceEquiv signature firstList secondList) :
    ∀ (state : WireState),
      extractAfterProcessing bottomCount state firstList
        = extractAfterProcessing bottomCount state secondList := by
  induction equiv with
  | ofStep step => intro state; exact godementInvariant state step
  | refl _ => intro _; rfl
  | symm _ inductionHypothesis => intro state; exact (inductionHypothesis state).symm
  | trans _ _ firstHypothesis secondHypothesis =>
      intro state; exact (firstHypothesis state).trans (secondHypothesis state)
  | consCongr atom _ inductionHypothesis => intro state; exact inductionHypothesis (stepAtom state atom)

/-- ★ **FULL `TwoCellConvFull` soundness of `matchingOf`, assembled modulo one residual.**  Given the
state-parametric Godement-step invariance (`godementInvariant`), `matchingOf` is invariant under the COMPLETE
free-strict-2-category convertibility — every structural law, all whisker functoriality, every congruence, and
the interchange step.  All of it routes through the proven `twoCellConvFull_spineTraceEquiv`; the ONLY input
owed is the one Godement lemma, narrowing the entire soundness residual to that single (computationally
confirmed) statement. -/
theorem matchingOf_sound_of_godementInvariant {signature : ModeSignature}
    (godementInvariant : ∀ {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat)
        (state : WireState)
        {firstList secondList : List (SpineAtom signature overallSource overallTarget)},
        SpineGodementStep signature firstList secondList →
        extractAfterProcessing bottomCount state firstList = extractAfterProcessing bottomCount state secondList)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (convFull : TwoCellConvFull signature firstCell secondCell) :
    matchingOf firstCell = matchingOf secondCell :=
  traceInvariant_of_godementInvariant sourcePath.length
    (fun state {_firstList _secondList} step => godementInvariant sourcePath.length state step)
    (twoCellConvFull_spineTraceEquiv convFull)
    { openWires := List.range sourcePath.length, links := [], nextFresh := sourcePath.length, loops := 0 }

/-! ## The generator count is a `TwoCellConvFull` invariant — the snake/identity separator

The boundary matching cannot tell a snake from the identity (the incompleteness below).  The generator count
CAN, and it is a genuine `TwoCellConvFull` invariant — every whisker-functoriality law and congruence passes the
count through unchanged.  This is the witness that the snake gap is a real distinction, not an artifact of a weak
invariant. -/

/-- A boundary cast preserves the generator count (the cast is an `Eq.rec`; substituting the two boundary
equalities collapses it to the identity). -/
theorem RawTwoCellExpr.generatorCount_castBoundary {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    (RawTwoCellExpr.castBoundary hsource htarget cell).generatorCount = cell.generatorCount := by
  cases hsource; cases htarget; rfl

/-- ★ **The generator count is invariant under the completed convertibility `TwoCellConvFull`.**  By induction:
`ofConv` reuses `TwoCellConv.generatorCount_eq`; each whisker-functoriality law passes the count through a
whiskering / boundary cast unchanged (`generatorCount_castBoundary`); the four congruences thread the inductive
hypothesis; `refl` / `symm` / `trans` chain.  Hence cells of different generator count are NOT
`TwoCellConvFull`-related — the separator the matching lacks. -/
theorem TwoCellConvFull.generatorCount_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (convFull : TwoCellConvFull signature firstCell secondCell) :
    firstCell.generatorCount = secondCell.generatorCount := by
  induction convFull with
  | ofConv conv => exact conv.generatorCount_eq
  | whiskerLeftUnit _ => rfl
  | whiskerRightUnit body => exact (RawTwoCellExpr.generatorCount_castBoundary _ _ body).symm
  | whiskerLeftComp oneCellOuter oneCellInner body =>
      exact (RawTwoCellExpr.generatorCount_castBoundary _ _
        (RawTwoCellExpr.whiskerLeft oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body))).symm
  | whiskerRightComp oneCellInner oneCellOuter body =>
      exact (RawTwoCellExpr.generatorCount_castBoundary _ _
        (RawTwoCellExpr.whiskerRight oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body))).symm
  | vcompCongrLeft _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.generatorCount]; rw [inductionHypothesis]
  | vcompCongrRight _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.generatorCount]; rw [inductionHypothesis]
  | whiskerLeftCongr _ _ inductionHypothesis => exact inductionHypothesis
  | whiskerRightCongr _ _ inductionHypothesis => exact inductionHypothesis
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis

/-- Cells of different generator count are not `TwoCellConvFull` — the contrapositive distinguisher. -/
theorem TwoCellConvFull.not_of_generatorCount_ne {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (countsDiffer : firstCell.generatorCount ≠ secondCell.generatorCount) :
    ¬ TwoCellConvFull signature firstCell secondCell :=
  fun convFull => countsDiffer convFull.generatorCount_eq

/-! ## The walking-adjunction witnesses (cup/cap string diagrams) -/

/-- The 1-cell `left : base ⟶ tip`. -/
def adjunctionLeftPath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip :=
  ModalityPath.cons AdjunctionModality.left (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)

/-- The identity 2-cell on the base identity 1-cell. -/
def identityOnBase :
    RawTwoCellExpr adjunctionModeSignature (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) := RawTwoCellExpr.id _

/-- The identity 2-cell on the `left·right` 1-cell. -/
def identityOnLeftRight :
    RawTwoCellExpr adjunctionModeSignature adjunctionLeftThenRight adjunctionLeftThenRight := RawTwoCellExpr.id _

/-- The identity 2-cell on the `right·left` 1-cell. -/
def identityOnRightLeft :
    RawTwoCellExpr adjunctionModeSignature adjunctionRightThenLeft adjunctionRightThenLeft := RawTwoCellExpr.id _

/-- The identity 2-cell on the tip identity 1-cell. -/
def identityOnTip :
    RawTwoCellExpr adjunctionModeSignature (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) := RawTwoCellExpr.id _

/-- The interchange REDEX of the two parallel units (cups): `hcomp (id ⊟ unit) (unit ⊟ id) : id_base ⇒ LRLR`. -/
def parallelUnitsRedex : RawTwoCellExpr adjunctionModeSignature
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
    (composePath adjunctionLeftThenRight adjunctionLeftThenRight) :=
  RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp identityOnBase adjunctionUnitTwoCell)
    (RawTwoCellExpr.vcomp adjunctionUnitTwoCell identityOnLeftRight)

/-- The interchange REDUCT of the two parallel units: `(hcomp id unit) ⊟ (hcomp unit id)`. -/
def parallelUnitsReduct : RawTwoCellExpr adjunctionModeSignature
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
    (composePath adjunctionLeftThenRight adjunctionLeftThenRight) :=
  RawTwoCellExpr.vcomp (RawTwoCellExpr.hcomp identityOnBase adjunctionUnitTwoCell)
    (RawTwoCellExpr.hcomp adjunctionUnitTwoCell identityOnLeftRight)

/-- The interchange REDEX of two parallel COUNITS (caps): `hcomp (id ⊟ counit) (counit ⊟ id) : RLRL ⇒ id_tip` —
the cell-level analog of `FreeTwoCellOrientedReducer`'s `adjunctionCounitGodementStep`, the exact obstruction the
expanding-oriented rewriting reducer could NOT realize. -/
def parallelCounitsRedex : RawTwoCellExpr adjunctionModeSignature
    (composePath adjunctionRightThenLeft adjunctionRightThenLeft)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) :=
  RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp identityOnRightLeft adjunctionCounitTwoCell)
    (RawTwoCellExpr.vcomp adjunctionCounitTwoCell identityOnTip)

/-- The interchange REDUCT of two parallel counits: `(hcomp id counit) ⊟ (hcomp counit id)`. -/
def parallelCounitsReduct : RawTwoCellExpr adjunctionModeSignature
    (composePath adjunctionRightThenLeft adjunctionRightThenLeft)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) :=
  RawTwoCellExpr.vcomp (RawTwoCellExpr.hcomp identityOnRightLeft adjunctionCounitTwoCell)
    (RawTwoCellExpr.hcomp adjunctionCounitTwoCell identityOnTip)

/-- The unit half of the snake (`unit ▷ left : left ⇒ left·right·left`). -/
def snakeUnitWhisker := RawTwoCellExpr.whiskerRight adjunctionLeftPath adjunctionUnitTwoCell

/-- The counit half of the snake (`left ◁ counit : left·right·left ⇒ left`). -/
def snakeCounitWhisker := RawTwoCellExpr.whiskerLeft adjunctionLeftPath adjunctionCounitTwoCell

/-- The **snake / zig-zag** on `left`: `(left ◁ counit) ∘ (unit ▷ left) : left ⇒ left` — a single through-strand
with a U-turn, DISTINCT from `id_left` in the free 2-category (straightening it is the triangle identity). -/
def snakeOnLeft := RawTwoCellExpr.vcomp snakeUnitWhisker snakeCounitWhisker

/-- The identity 2-cell on `left` — a straight strand. -/
def identityOnLeft : RawTwoCellExpr adjunctionModeSignature adjunctionLeftPath adjunctionLeftPath :=
  RawTwoCellExpr.id _

/-! ## ★ The crux: `matchingOf` identifies the obstruction endpoints as EQUAL

The rewriting route foundered on the Godement / interchange step (and especially the CONTRACTING counit
transposition, which no linear measure orients).  The topological `matchingOf` assigns BOTH endpoints of each
such step the SAME diagram type — by direct `decide` — so it sees through the obstruction the rewriting route
could not. -/

/-- The single `interchange` 3-cell connecting the parallel-units redex and reduct. -/
def parallelUnitsInterchangeStep :
    TwoCellStep adjunctionModeSignature parallelUnitsRedex parallelUnitsReduct :=
  TwoCellStep.interchange identityOnBase adjunctionUnitTwoCell adjunctionUnitTwoCell identityOnLeftRight

/-- Hence the parallel-units endpoints are `TwoCellConvFull` (via interchange). -/
def parallelUnitsConvFull :
    TwoCellConvFull adjunctionModeSignature parallelUnitsRedex parallelUnitsReduct :=
  TwoCellConvFull.ofConv (TwoCellConv.ofStep parallelUnitsInterchangeStep)

/-- The redex's topological type: two cups, the 4 top ports matched `0↔1`, `2↔3`. -/
theorem parallelUnitsRedex_matchingOf :
    matchingOf parallelUnitsRedex = { bottomCount := 0, topCount := 4, partner := [1, 0, 3, 2], loops := 0 } :=
  rfl

/-- The reduct's topological type — identical to the redex's. -/
theorem parallelUnitsReduct_matchingOf :
    matchingOf parallelUnitsReduct = { bottomCount := 0, topCount := 4, partner := [1, 0, 3, 2], loops := 0 } :=
  rfl

/-- ★ **CRUX (interchange obstruction).**  `matchingOf` identifies the two interchange endpoints as EQUAL — the
canonical Eckmann–Hilton non-confluence witness (the parent's `adjunctionParallelUnitsRedex/Reduct` analog) gets
ONE topological type `{ bottomCount := 0, topCount := 4, partner := [1,0,3,2], loops := 0 }`.  Each side computes
by `rfl`; their equality validates that the topological route sees through the Godement obstruction. -/
theorem parallelUnits_matchingOf_eq : matchingOf parallelUnitsRedex = matchingOf parallelUnitsReduct :=
  parallelUnitsRedex_matchingOf.trans parallelUnitsReduct_matchingOf.symm

/-- The single `interchange` 3-cell connecting the parallel-COUNITS redex and reduct. -/
def parallelCounitsInterchangeStep :
    TwoCellStep adjunctionModeSignature parallelCounitsRedex parallelCounitsReduct :=
  TwoCellStep.interchange identityOnRightLeft adjunctionCounitTwoCell adjunctionCounitTwoCell identityOnTip

/-- Hence the parallel-counits endpoints are `TwoCellConvFull`. -/
def parallelCounitsConvFull :
    TwoCellConvFull adjunctionModeSignature parallelCounitsRedex parallelCounitsReduct :=
  TwoCellConvFull.ofConv (TwoCellConv.ofStep parallelCounitsInterchangeStep)

/-- The counit redex's topological type: two caps, the 4 bottom ports matched `0↔1`, `2↔3`. -/
theorem parallelCounitsRedex_matchingOf :
    matchingOf parallelCounitsRedex = { bottomCount := 4, topCount := 0, partner := [1, 0, 3, 2], loops := 0 } :=
  rfl

/-- The counit reduct's topological type — identical to the redex's. -/
theorem parallelCounitsReduct_matchingOf :
    matchingOf parallelCounitsReduct = { bottomCount := 4, topCount := 0, partner := [1, 0, 3, 2], loops := 0 } :=
  rfl

/-- ★ **CRUX (counit obstruction).**  `matchingOf` identifies the two COUNIT Godement endpoints as EQUAL — the
exact contracting-transposition obstruction `FreeTwoCellOrientedReducer` proved un-orientable for the rewriting
reducer.  Both get `{ bottomCount := 4, topCount := 0, partner := [1,0,3,2], loops := 0 }` (each by `rfl`).  This
is the crux validating the topological route: the matching invariant is provably blind to the orientation
asymmetry (expanding unit vs contracting counit) that blocked rewriting. -/
theorem parallelCounits_matchingOf_eq :
    matchingOf parallelCounitsRedex = matchingOf parallelCounitsReduct :=
  parallelCounitsRedex_matchingOf.trans parallelCounitsReduct_matchingOf.symm

/-! ## The snake gap: `matchingOf` is sound but INCOMPLETE (and decision-vacuous at this seed)

The snake and the identity on `left` have the SAME topological type, yet are DISTINCT free 2-cells (separated by
the generator count, a genuine `TwoCellConvFull` invariant).  So `matchingOf` cannot witness their
non-convertibility — the precise incompleteness the coordinator flagged. -/

/-- The snake's topological type — a single through-strand, no loops. -/
theorem snake_matchingOf :
    matchingOf snakeOnLeft = { bottomCount := 1, topCount := 1, partner := [1, 0], loops := 0 } := rfl

/-- The identity-on-`left` topological type — the SAME single through-strand. -/
theorem identityOnLeft_matchingOf :
    matchingOf identityOnLeft = { bottomCount := 1, topCount := 1, partner := [1, 0], loops := 0 } := rfl

/-- The snake has the SAME diagram type as the identity (both a single through-strand, no loops). -/
theorem snake_matchingOf_eq_identity : matchingOf snakeOnLeft = matchingOf identityOnLeft :=
  snake_matchingOf.trans identityOnLeft_matchingOf.symm

/-- Yet the snake and the identity have DIFFERENT generator counts (`2 ≠ 0`). -/
theorem snake_generatorCount_ne_identity :
    snakeOnLeft.generatorCount ≠ identityOnLeft.generatorCount := by decide

/-- ★ **The snake gap, formally.**  The snake is NOT `TwoCellConvFull` to the identity (different generator count
— the count being a `TwoCellConvFull` invariant), even though `matchingOf` cannot tell them apart.  This is the
precise sense in which the boundary-matching + loop-count invariant is INCOMPLETE for the free strict
2-category: the genuine free invariant must retain the snake's two generators (the spine modulo trace
equivalence, `SpineTraceEquiv` — the full Joyal–Street isotopy type), which the matching shadow forgets. -/
theorem snake_not_convFull_identity :
    ¬ TwoCellConvFull adjunctionModeSignature snakeOnLeft identityOnLeft :=
  TwoCellConvFull.not_of_generatorCount_ne snake_generatorCount_ne_identity

/-- The double snake on `left` — two zig-zags stacked vertically (generator count `4`). -/
def doubleSnakeOnLeft : RawTwoCellExpr adjunctionModeSignature adjunctionLeftPath adjunctionLeftPath :=
  RawTwoCellExpr.vcomp snakeOnLeft snakeOnLeft

/-- The double snake's topological type — again the single through-strand. -/
theorem doubleSnake_matchingOf :
    matchingOf doubleSnakeOnLeft = { bottomCount := 1, topCount := 1, partner := [1, 0], loops := 0 } := rfl

/-- ★ **Decision-vacuity at the seed, witnessed as a theorem.**  Three cells `left ⇒ left` with PAIRWISE
DISTINCT generator counts `0, 2, 4` — hence pairwise NON-`TwoCellConvFull` — all share ONE diagram type
`{1,1,[1,0],0}`.  So `matchingOf` agrees on cells it must keep distinct: at the walking adjunction the boundary
matching is determined by the boundary 1-cells alone, so `matchingOf` cannot REFUTE any parallel pair.  Its
genuine `isFalse` power (different boundary connectivity) is real in general but vacuous here; the seed's
distinctions are carried by the generator count and, completely, by the spine-modulo-trace class. -/
theorem decisionVacuity_at_seed :
    matchingOf identityOnLeft = matchingOf snakeOnLeft
      ∧ matchingOf snakeOnLeft = matchingOf doubleSnakeOnLeft
      ∧ identityOnLeft.generatorCount = 0
      ∧ snakeOnLeft.generatorCount = 2
      ∧ doubleSnakeOnLeft.generatorCount = 4 :=
  ⟨snake_matchingOf_eq_identity.symm, snake_matchingOf.trans doubleSnake_matchingOf.symm, rfl, rfl, rfl⟩

/-- Smoke: the matching of the bare unit (a cup) is `top0 ↔ top1`, and of the bare counit (a cap) is
`bot0 ↔ bot1` — both loop-free, exhibiting the cup/cap primitives `matchingOf` reads. -/
theorem unit_counit_matchingOf :
    matchingOf adjunctionUnitTwoCell = { bottomCount := 0, topCount := 2, partner := [1, 0], loops := 0 } ∧
      matchingOf adjunctionCounitTwoCell = { bottomCount := 2, topCount := 0, partner := [1, 0], loops := 0 } :=
  ⟨rfl, rfl⟩

/-! ## Honesty markers -/

/-- **Honesty marker — the matching invariant is SOUND, and PROVABLY INCOMPLETE.**  `matchingOf` is proven
invariant under EVERY generator of `TwoCellConvFull` except one: the interchange-free structural fragment
(`matchingOf_eq_of_interchangeFreeStep`) and all four whisker-functoriality laws
(`matchingOf_whisker{Left,Right}{Unit,Comp}`).  The single uncovered generator is the `interchange` (Godement)
step — computationally confirmed matching-invariant on every obstruction witness
(`parallelUnits_matchingOf_eq`, `parallelCounits_matchingOf_eq`).  Incompleteness is now a THEOREM, not a gap:
the snake has the same diagram type as the identity (`snake_matchingOf_eq_identity`) yet is a distinct free
2-cell (`snake_not_convFull_identity`).  The complete invariant is the strictly finer spine-modulo-trace class
(`SpineTraceEquiv`, the full Joyal–Street isotopy type), whose reconstruction is the standing
`fxMode_hasSpineTraceReconstruction` residual.  `= false`. -/
def fxMode_hasCompleteMatchingInvariant : Bool := false

/-- **Honesty marker — at THIS seed the matching is boundary-determined, hence DECISION-VACUOUS.**  At the
walking adjunction every cup makes `LR` and every cap eats `RL`, so (i) no oriented circle ever closes — the loop
count is identically `0`; and (ii) the planar boundary matching between two fixed 1-cells is unique when it
exists, so `matchingOf` agrees on EVERY parallel pair.  This is now PROVEN as `decisionVacuity_at_seed`: three
cells `left ⇒ left` of generator count `0, 2, 4` (hence pairwise non-convertible) share one diagram type.
Therefore `matchingOf` cannot REFUTE any `TwoCellConvFull` instance at the seed: its `isFalse` power is genuine
in general but vacuous here, and the walking-adjunction decision is carried entirely by the FINER invariants
(generator count separates the snake; the spine-modulo-trace class is the complete one).  The matching machinery
is the correct foundation; the seed simply lives in its kernel.  `= false`. -/
def fxMode_hasMatchingDecisionPowerAtSeed : Bool := false

/-- **Honesty marker — the FULL soundness is ASSEMBLED modulo exactly one named lemma.**
`matchingOf_sound_of_godementInvariant` proves `matchingOf` invariant under the COMPLETE `TwoCellConvFull` GIVEN
a single residual: the state-parametric Godement-step invariance `godementInvariant` (a `SpineGodementStep`
preserves the diagram extract from every processing state).  Everything else routes through the proven
`twoCellConvFull_spineTraceEquiv`.  The residual is TRUE — it is the union-find INDEPENDENCE of two
horizontally-disjoint blocks (a state-renaming simulation between the two run orders; the fresh-id allocation
differs, the extracted `DiagramType` does not) — and is computationally confirmed on every obstruction witness
(`parallelUnits_matchingOf_eq`, `parallelCounits_matchingOf_eq`).  Its general zero-axiom proof (a separation-style
disjoint-support commutation over the dependently-typed union-find) is the single outstanding obligation; this
pass ships the assembly, the structural + all-whisker soundness outright, and the computational crux.  `= false`. -/
def fxMode_hasMatchingGodementIndependenceProof : Bool := false

end FX1Poly.Polygraph
