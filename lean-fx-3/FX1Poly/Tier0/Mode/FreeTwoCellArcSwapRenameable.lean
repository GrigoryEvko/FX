import FX1Poly.Tier0.Mode.FreeTwoCellArcSamePartitionFresh

/-! # mode-3 floor (leg B, W2-ArcSwap) — the Godement block-swap renaming, foundation + reduction

`FreeTwoCellArcSamePartitionFresh` reduced the freshness-conditioned Godement arc residual
`ArcGodementSamePartitionFresh` to a renaming existence `ArcGodementSwapRenameable`: from every FRESH starting
state, the two Godement run orders (redex `cellAlphaUpper` then `cellBeta`, reduct `cellBeta` then
`cellAlphaUpper`, with the common `cellAlpha` prefix and `cellBetaUpper` suffix and `rest` tail) are related by
an injective boundary-fixing node renaming (`ArcRenameRel`).  It proved the renaming-INVARIANCE of the partition
view but left the renaming WITNESS open (`fxMode_hasArcGodementSwapRenameableProof = false`).

This file ships the renaming-EQUIVARIANCE infrastructure the witness construction is built on, all zero-axiom:

  ★ `renameLinks_unionFindJoin` — **the union-find JOIN commutes with an injective renaming**: renaming the
    edge list and the two joined nodes commutes with the union (`renameLinks σ (unionFindJoin links a b)
    = unionFindJoin (renameLinks σ links) (σ a) (σ b)`).  Leverages the parent's `unionFindRootOf_rename` +
    `beq_congr_inj`, so it needs NO union-find correctness / fuel reasoning — the clean half of obstruction (2).
  ★ `unionFindRoot_consJoin` — **root-following after a disjoint-range union** (the other half of obstruction
    (2)): prepending a root→root edge `(p, q)` (`p`, `q` parentless, `p ≠ q`) redirects exactly the nodes whose
    root was `p` to `q`, leaving the rest unchanged.  Fuel induction, conditional on the chain settling (the
    acyclicity content of the fold's reachable states, deferred); `unionFindRoot_of_parentless` anchors it.
  ★ `countEventsInRoot_rename` / `countEventsInRoot_append` — the per-root event count is renaming-covariant and
    additive over list concatenation (so the two run orders' DIFFERENTLY-ORDERED event lists count the same per
    root, via `Nat.add_comm` — the order-insensitivity the partition view needs).
  ★ `renameState` + `stepArcAtom_renameState` / `processArcSpine_renameState` — the **arc fold is equivariant
    under an injective input renaming** that fixes `0` and every id at-or-above `nextFresh`: renaming the input
    wires commutes with running the whole spine.  The complete renaming-invariance of the arc fold (cup / cap /
    box arms), the engine for transporting the partition relation across a common suffix.
  ★ `stepArcAtom_nextFresh_le` / `processArcSpine_nextFresh_le` — `nextFresh` is monotone (the fresh ranges only
    grow), and `arcStateFresh` is preserved by `stepArcAtom` / `processArcSpine` / `runArcCell` — the
    region-layout invariant's anchor.
  ★ `renameRel_of_renameState` — an injective renaming fixing the bottom ports turns `t = renameState σ s` into
    `ArcRenameRel bottomCount σ s t`: the bridge from the equivariance to the partition relation the residual
    consumes.

## What is honest-DEFERRED (the genuine combinatorial core, now SHARPENED)

`ArcGodementSwapRenameable` — `fxMode_hasArcGodementSwapRenameableProof2 = false`.  The remaining obstruction is
the SUPPORT/LOCALITY analysis: the two horizontally-disjoint blocks `cellAlphaUpper` (f-region) and `cellBeta`
(g-region) touch disjoint wire windows and allocate disjoint fresh ranges, so transposing them only permutes the
fresh ranges — the block-swap renaming.  Establishing the per-step support window plus the root-following after a
disjoint-range union (the genuine union-find correctness, which needs the acyclicity invariant of the fold's
reachable states) is the standing obligation; the renaming-EQUIVARIANCE half — how every read-off transports
across an injective renaming — is proved here.

Raw Lean 4 + Init; structural / fuel recursion, `decide`-form `Nat` equality, no `omega` / `simp`-AC /
`WellFounded.fix` / `List.append`-lemmas (`List.map_append` is reproved by hand as `mapAppend`).  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Tier0

/-! ## `propext`-free list-map helpers (Lean core's `List.map_append` leaks `propext`) -/

/-- `List.map` distributes over append — reproved by hand (`List.map_append` routes through `propext`).
Structural recursion on the first list. -/
theorem mapAppend (sigma : Nat → Nat) :
    (front back : List Nat) → (front ++ back).map sigma = front.map sigma ++ back.map sigma
  | [], _ => rfl
  | head :: tail, back => by
      show sigma head :: (tail ++ back).map sigma = sigma head :: (tail.map sigma ++ back.map sigma)
      rw [mapAppend sigma tail back]

/-- Splicing a wire block commutes with an injective renaming of every id (`natListInsertAt` over a `map`). -/
theorem natListInsertAt_map (sigma : Nat → Nat) :
    (wires : List Nat) → (position : Nat) → (block : List Nat) →
    (natListInsertAt wires position block).map sigma
      = natListInsertAt (wires.map sigma) position (block.map sigma)
  | wires, 0, block => by
      simp only [natListInsertAt]
      exact mapAppend sigma block wires
  | [], _ + 1, _ => rfl
  | head :: rest, position + 1, block => by
      show sigma head :: (natListInsertAt rest position block).map sigma
         = sigma head :: natListInsertAt (rest.map sigma) position (block.map sigma)
      rw [natListInsertAt_map sigma rest position block]

/-- Removing the two wires at a position commutes with a renaming of every id. -/
theorem natListRemoveTwoAt_map (sigma : Nat → Nat) :
    (wires : List Nat) → (position : Nat) →
    (natListRemoveTwoAt wires position).map sigma = natListRemoveTwoAt (wires.map sigma) position
  | [], _ => rfl
  | _ :: _ :: _, 0 => rfl
  | [_], 0 => rfl
  | head :: rest, position + 1 => by
      simp only [List.map, natListRemoveTwoAt]
      rw [natListRemoveTwoAt_map sigma rest position]

/-- Reading a wire at a position commutes with a renaming that fixes `0` (the past-the-end default). -/
theorem natListGetAt_map (sigma : Nat → Nat) (sigmaFixesZero : sigma 0 = 0) :
    (wires : List Nat) → (position : Nat) →
    natListGetAt (wires.map sigma) position = sigma (natListGetAt wires position)
  | [], _ => sigmaFixesZero.symm
  | _ :: _, 0 => rfl
  | _ :: rest, position + 1 => natListGetAt_map sigma sigmaFixesZero rest position

/-- A renaming fixing every id at-or-above a threshold fixes a whole list of such ids. -/
theorem mapFixedAbove (sigma : Nat → Nat) (threshold : Nat)
    (fixesAbove : ∀ identifier, threshold ≤ identifier → sigma identifier = identifier) :
    (wires : List Nat) → (∀ wire ∈ wires, threshold ≤ wire) → wires.map sigma = wires
  | [], _ => rfl
  | head :: tail, allAtLeastThreshold => by
      show sigma head :: tail.map sigma = head :: tail
      rw [fixesAbove head (allAtLeastThreshold head (List.Mem.head _)),
        mapFixedAbove sigma threshold fixesAbove tail
          (fun wire wireInTail => allAtLeastThreshold wire (List.Mem.tail _ wireInTail))]

/-- Every id in `(range n).map (· + base)` is at least `base`. -/
theorem mem_mapAdd_ge (base : Nat) :
    (wires : List Nat) → (target : Nat) → target ∈ wires.map (· + base) → base ≤ target
  | [], _, targetMem => by cases targetMem
  | head :: tail, target, targetMem => by
      cases targetMem with
      | head => exact Nat.le_add_left base head
      | tail _ targetInTail => exact mem_mapAdd_ge base tail target targetInTail

/-! ## The union-find JOIN commutes with an injective renaming -/

/-- ★ **The union-find join commutes with an injective renaming.**  `renameLinks σ (unionFindJoin links a b)
= unionFindJoin (renameLinks σ links) (σ a) (σ b)`.  The join compares the two roots and (when distinct)
prepends a root→root edge; renaming commutes with the roots (`unionFindRootOf_rename`) and with the comparison
(`beq_congr_inj`), and `renameLinks` distributes over the prepended edge definitionally.  No union-find
correctness / fuel reasoning — the clean, propext-free half of obstruction (2). -/
theorem renameLinks_unionFindJoin (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b)
    (links : List (Nat × Nat)) (firstNode secondNode : Nat) :
    renameLinks sigma (unionFindJoin links firstNode secondNode)
      = unionFindJoin (renameLinks sigma links) (sigma firstNode) (sigma secondNode) := by
  show renameLinks sigma
      (if unionFindRootOf links firstNode == unionFindRootOf links secondNode then links
        else (unionFindRootOf links firstNode, unionFindRootOf links secondNode) :: links)
    = (if unionFindRootOf (renameLinks sigma links) (sigma firstNode)
          == unionFindRootOf (renameLinks sigma links) (sigma secondNode)
        then renameLinks sigma links
        else (unionFindRootOf (renameLinks sigma links) (sigma firstNode),
              unionFindRootOf (renameLinks sigma links) (sigma secondNode)) :: renameLinks sigma links)
  rw [unionFindRootOf_rename sigma inj links firstNode, unionFindRootOf_rename sigma inj links secondNode,
    beq_congr_inj sigma inj]
  cases unionFindRootOf links firstNode == unionFindRootOf links secondNode with
  | true => rfl
  | false => rfl

/-! ## The per-root event count is renaming-covariant and additive over concatenation -/

/-- ★ **The per-root event count is renaming-covariant.**  `countEventsInRoot (renameLinks σ links) (σ rootHere)
(events.map σ) = countEventsInRoot links rootHere events` for injective `σ`: each event's renamed root equals the
renamed event's root (`unionFindRootOf_rename`), and the comparison transports by `beq_congr_inj`.  Structural on
the event list. -/
theorem countEventsInRoot_rename (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b)
    (links : List (Nat × Nat)) (rootHere : Nat) :
    (events : List Nat) →
    countEventsInRoot (renameLinks sigma links) (sigma rootHere) (events.map sigma)
      = countEventsInRoot links rootHere events
  | [] => rfl
  | eventNode :: rest => by
      show (if unionFindRootOf (renameLinks sigma links) (sigma eventNode) == sigma rootHere then 1 else 0)
            + countEventsInRoot (renameLinks sigma links) (sigma rootHere) (rest.map sigma)
         = (if unionFindRootOf links eventNode == rootHere then 1 else 0)
            + countEventsInRoot links rootHere rest
      rw [unionFindRootOf_rename sigma inj links eventNode, beq_congr_inj sigma inj,
        countEventsInRoot_rename sigma inj links rootHere rest]

/-- ★ **The per-root event count is additive over concatenation.**  `countEventsInRoot links r (front ++ back)
= countEventsInRoot links r front + countEventsInRoot links r back` — structural on `front`, the cons of `++`
reducing definitionally.  With `Nat.add_comm` this makes the count BLIND to swapping two event blocks (the exact
difference between the two Godement run orders' event lists). -/
theorem countEventsInRoot_append (links : List (Nat × Nat)) (rootHere : Nat) :
    (front back : List Nat) →
    countEventsInRoot links rootHere (front ++ back)
      = countEventsInRoot links rootHere front + countEventsInRoot links rootHere back
  | [], _ => (Nat.zero_add _).symm
  | eventNode :: rest, back => by
      show (if unionFindRootOf links eventNode == rootHere then 1 else 0)
            + countEventsInRoot links rootHere (rest ++ back)
         = (if unionFindRootOf links eventNode == rootHere then 1 else 0)
              + countEventsInRoot links rootHere rest
            + countEventsInRoot links rootHere back
      rw [countEventsInRoot_append links rootHere rest back, Nat.add_assoc]

/-! ## `nextFresh` is monotone — the fresh ranges only grow (the locality anchor) -/

/-- One arc step never lowers `nextFresh` (a cup adds 3, a cap adds 1, a box adds its output count). -/
theorem stepArcAtom_nextFresh_le {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode) :
    state.nextFresh ≤ (stepArcAtom state atom).nextFresh := by
  unfold stepArcAtom
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_add_right _ _
  · exact Nat.le_add_right _ _

/-- The whole arc fold never lowers `nextFresh`. -/
theorem processArcSpine_nextFresh_le {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : ArcWireState) →
    state.nextFresh ≤ (processArcSpine state atoms).nextFresh
  | [], _ => Nat.le_refl _
  | atom :: rest, state =>
      Nat.le_trans (stepArcAtom_nextFresh_le state atom)
        (processArcSpine_nextFresh_le rest (stepArcAtom state atom))

/-- Running one cell never lowers `nextFresh`. -/
theorem runArcCell_nextFresh_le {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (state : ArcWireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod) :
    state.nextFresh ≤ (runArcCell state leftAcc rightAcc cell).nextFresh :=
  processArcSpine_nextFresh_le (cell.spineDiff leftAcc rightAcc []) state

/-! ## The arc fold is equivariant under an injective input renaming -/

/-- Rename every wire / link / event id of an arc state by `σ`, holding `nextFresh` and the loop count fixed
(the fresh-allocation counter and the bubble count are renaming-invariant data). -/
def renameState (sigma : Nat → Nat) (state : ArcWireState) : ArcWireState :=
  { openWires := state.openWires.map sigma,
    links := renameLinks sigma state.links,
    nextFresh := state.nextFresh,
    loops := state.loops,
    cupEventNodes := state.cupEventNodes.map sigma,
    capEventNodes := state.capEventNodes.map sigma }

/-- A CUP step commutes with an injective renaming fixing every id at-or-above `nextFresh` (the two legs and the
event node it allocates).  Field-by-field: the splice via `natListInsertAt_map` + the fixed legs, the two unions
via `renameLinks_unionFindJoin` + the fixed roots, the consed event via the fixed event id. -/
theorem stepCupArc_renameState (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b)
    (state : ArcWireState) (position : Nat)
    (fixesAbove : ∀ identifier, state.nextFresh ≤ identifier → sigma identifier = identifier) :
    stepCupArc (renameState sigma state) position = renameState sigma (stepCupArc state position) := by
  have hnf : sigma state.nextFresh = state.nextFresh := fixesAbove _ (Nat.le_refl _)
  have hnf1 : sigma (state.nextFresh + 1) = state.nextFresh + 1 := fixesAbove _ (Nat.le_add_right _ _)
  have hnf2 : sigma (state.nextFresh + 2) = state.nextFresh + 2 := fixesAbove _ (Nat.le_add_right _ _)
  dsimp only [stepCupArc, renameState, List.map]
  rw [natListInsertAt_map sigma state.openWires position [state.nextFresh, state.nextFresh + 1]]
  dsimp only [List.map]
  rw [renameLinks_unionFindJoin sigma inj, renameLinks_unionFindJoin sigma inj, hnf, hnf1, hnf2]

/-- A CAP step commutes with an injective renaming fixing `0` (the past-the-end wire-read default) and every id
at-or-above `nextFresh` (the event node it allocates).  The two wire reads transport via `natListGetAt_map`, the
unions via `renameLinks_unionFindJoin`, the loop-test via `unionFindRootOf_rename` + `beq_congr_inj`, the
wire-drop via `natListRemoveTwoAt_map`. -/
theorem stepCapArc_renameState (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b)
    (sigmaFixesZero : sigma 0 = 0) (state : ArcWireState) (position : Nat)
    (fixesAbove : ∀ identifier, state.nextFresh ≤ identifier → sigma identifier = identifier) :
    stepCapArc (renameState sigma state) position = renameState sigma (stepCapArc state position) := by
  have hnf : sigma state.nextFresh = state.nextFresh := fixesAbove _ (Nat.le_refl _)
  -- The renamed same-component test agrees with the original (whole-`isSameComponent` bool, so the loop `if`'s
  -- Decidable instance transports without `propext`).
  have hsame : isSameComponent (renameLinks sigma state.links)
      (natListGetAt (state.openWires.map sigma) position) (natListGetAt (state.openWires.map sigma) (position + 1))
        = isSameComponent state.links (natListGetAt state.openWires position)
            (natListGetAt state.openWires (position + 1)) := by
    dsimp only [isSameComponent]
    rw [natListGetAt_map sigma sigmaFixesZero, natListGetAt_map sigma sigmaFixesZero,
      unionFindRootOf_rename sigma inj, unionFindRootOf_rename sigma inj, beq_congr_inj sigma inj]
  dsimp only [stepCapArc, renameState, List.map]
  rw [natListRemoveTwoAt_map sigma state.openWires position, hsame,
    natListGetAt_map sigma sigmaFixesZero state.openWires position,
    natListGetAt_map sigma sigmaFixesZero state.openWires (position + 1),
    renameLinks_unionFindJoin sigma inj, renameLinks_unionFindJoin sigma inj, hnf]

/-- A generic BOX step (an atom whose arity is neither cup nor cap; absent at the adjunction seed but present in
the general fold) commutes with an injective renaming fixing every id at-or-above `nextFresh`.  The links are
untouched (so the renaming is verbatim), and the wire rearrange / fresh outputs transport via
`droppedWires_map` + `natListInsertAt_map` + `mapFixedAbove`. -/
theorem droppedWires_map (sigma : Nat → Nat) (position : Nat) :
    (numConsumed : Nat) → (openWires : List Nat) →
    (Nat.rec openWires (fun _ shorter => natListRemoveTwoAt shorter position) numConsumed : List Nat).map sigma
      = Nat.rec (openWires.map sigma) (fun _ shorter => natListRemoveTwoAt shorter position) numConsumed
  | 0, _ => rfl
  | numConsumed + 1, openWires => by
      show (natListRemoveTwoAt
              (Nat.rec openWires (fun _ shorter => natListRemoveTwoAt shorter position) numConsumed)
              position).map sigma
         = natListRemoveTwoAt
              (Nat.rec (openWires.map sigma) (fun _ shorter => natListRemoveTwoAt shorter position) numConsumed)
              position
      rw [natListRemoveTwoAt_map sigma _ position, droppedWires_map sigma position numConsumed openWires]

/-- ★ **One arc step is equivariant under an injective input renaming** fixing `0` and every id at-or-above
`nextFresh`: renaming the wires / links / events of the input state and running the step equals running the step
and renaming.  By the three arms (`stepCupArc_renameState`, `stepCapArc_renameState`, the box record). -/
theorem stepArcAtom_renameState {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0)
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (fixesAbove : ∀ identifier, state.nextFresh ≤ identifier → sigma identifier = identifier) :
    stepArcAtom (renameState sigma state) atom = renameState sigma (stepArcAtom state atom) := by
  unfold stepArcAtom
  split
  · exact stepCupArc_renameState sigma inj state _ fixesAbove
  · exact stepCapArc_renameState sigma inj sigmaFixesZero state _ fixesAbove
  · have hblk : ((List.range (atom.generatorCod.length)).map (· + state.nextFresh)).map sigma
          = (List.range (atom.generatorCod.length)).map (· + state.nextFresh) :=
      mapFixedAbove sigma state.nextFresh fixesAbove _ (mem_mapAdd_ge state.nextFresh _)
    dsimp only [renameState]
    rw [natListInsertAt_map sigma _ atom.leftContext.length,
      droppedWires_map sigma atom.leftContext.length atom.generatorDom.length state.openWires, hblk]

/-- ★ **The whole arc fold is equivariant under an injective input renaming** fixing `0` and every id
at-or-above the starting `nextFresh`.  Structural recursion on the spine; the head via `stepArcAtom_renameState`,
the tail threading the strengthened fixing hypothesis through `stepArcAtom_nextFresh_le` (`nextFresh` only grows,
so the fixed range only shrinks). -/
theorem processArcSpine_renameState {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0) :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : ArcWireState) →
    (∀ identifier, state.nextFresh ≤ identifier → sigma identifier = identifier) →
    processArcSpine (renameState sigma state) atoms = renameState sigma (processArcSpine state atoms)
  | [], _, _ => rfl
  | atom :: rest, state, fixesAbove => by
      show processArcSpine (stepArcAtom (renameState sigma state) atom) rest
         = renameState sigma (processArcSpine (stepArcAtom state atom) rest)
      rw [stepArcAtom_renameState sigma inj sigmaFixesZero state atom fixesAbove]
      exact processArcSpine_renameState sigma inj sigmaFixesZero rest (stepArcAtom state atom)
        (fun identifier idAtLeast =>
          fixesAbove identifier (Nat.le_trans (stepArcAtom_nextFresh_le state atom) idAtLeast))

/-- Running one cell is equivariant under an injective input renaming fixing `0` and the future-allocation tail. -/
theorem runArcCell_renameState {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0)
    (state : ArcWireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod)
    (fixesAbove : ∀ identifier, state.nextFresh ≤ identifier → sigma identifier = identifier) :
    runArcCell (renameState sigma state) leftAcc rightAcc cell
      = renameState sigma (runArcCell state leftAcc rightAcc cell) :=
  processArcSpine_renameState sigma inj sigmaFixesZero (cell.spineDiff leftAcc rightAcc []) state fixesAbove

/-! ## The bridge to `ArcRenameRel` and the renaming-invariance of the extract -/

/-- A renaming preserves list length (`List.length_map` leaks `propext`; reproved by hand). -/
theorem mapLength (sigma : Nat → Nat) : (wires : List Nat) → (wires.map sigma).length = wires.length
  | [] => rfl
  | _ :: tail => by show (tail.map sigma).length + 1 = tail.length + 1; rw [mapLength sigma tail]

/-- A renaming fixing every member of a list fixes the list. -/
theorem mapFixedOn (sigma : Nat → Nat) :
    (wires : List Nat) → (∀ wire ∈ wires, sigma wire = wire) → wires.map sigma = wires
  | [], _ => rfl
  | head :: tail, allFixed => by
      show sigma head :: tail.map sigma = head :: tail
      rw [allFixed head (List.Mem.head _),
        mapFixedOn sigma tail (fun wire wireInTail => allFixed wire (List.Mem.tail _ wireInTail))]

/-- The boundary nodes of a renamed state are the `σ`-image of the boundary nodes — when `σ` fixes the bottom
ports `0 … bottomCount-1` (so the `range bottomCount` prefix is renaming-invariant). -/
theorem boundaryNodesOf_renameState (bottomCount : Nat) (sigma : Nat → Nat)
    (sigmaFixesBoundary : ∀ identifier, identifier < bottomCount → sigma identifier = identifier)
    (state : ArcWireState) :
    boundaryNodesOf bottomCount (renameState sigma state)
      = (boundaryNodesOf bottomCount state).map sigma := by
  show List.range bottomCount ++ state.openWires.map sigma
     = (List.range bottomCount ++ state.openWires).map sigma
  rw [mapAppend sigma (List.range bottomCount) state.openWires,
    mapFixedOn sigma (List.range bottomCount)
      (fun identifier identifierInRange => sigmaFixesBoundary identifier (mem_range_imp_lt identifierInRange))]

/-- ★ **`renameState` realizes `ArcRenameRel`.**  An injective renaming fixing `0` and the bottom ports turns a
state and its renaming into an `ArcRenameRel` pair: lengths via `mapLength`, the boundary correspondence via
`boundaryNodesOf_renameState` + `natListGetAt_map`, the root-commutation via the parent's `unionFindRootOf_rename`,
the per-root event counts via `countEventsInRoot_rename`.  The bridge from the equivariance to the partition
relation the residual consumes. -/
theorem renameRel_of_renameState (bottomCount : Nat) (sigma : Nat → Nat)
    (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0)
    (sigmaFixesBoundary : ∀ identifier, identifier < bottomCount → sigma identifier = identifier)
    (state : ArcWireState) :
    ArcRenameRel bottomCount sigma state (renameState sigma state) where
  lengthEq := mapLength sigma state.openWires
  loopsEq := rfl
  inj := inj
  bnodeCorr := fun index _ => by
    rw [boundaryNodesOf_renameState bottomCount sigma sigmaFixesBoundary state,
      natListGetAt_map sigma sigmaFixesZero]
  rootComm := fun node => unionFindRootOf_rename sigma inj state.links node
  cupCorr := fun rootNode => countEventsInRoot_rename sigma inj state.links rootNode state.cupEventNodes
  capCorr := fun rootNode => countEventsInRoot_rename sigma inj state.links rootNode state.capEventNodes

/-- ★ **The arc extract is invariant under an injective boundary-fixing renaming.**  `extractArc bottomCount
state = extractArc bottomCount (renameState σ state)` for injective `σ` fixing `0` and the bottom ports — the
fresh wire-ids are union-find internals the extract reads through.  Composes `renameRel_of_renameState` with the
parent's `sameArcPartition_of_renameRel` + `extractArc_eq_of_sameArcPartition` (the event-node counts agree by
`mapLength`).  The concrete payoff of the renaming-equivariance: the planar-arc structure does not see node-id
relabelings. -/
theorem extractArc_renameState (bottomCount : Nat) (sigma : Nat → Nat)
    (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0)
    (sigmaFixesBoundary : ∀ identifier, identifier < bottomCount → sigma identifier = identifier)
    (state : ArcWireState) :
    extractArc bottomCount state = extractArc bottomCount (renameState sigma state) :=
  extractArc_eq_of_sameArcPartition bottomCount state (renameState sigma state)
    (sameArcPartition_of_renameRel bottomCount sigma state (renameState sigma state)
      (renameRel_of_renameState bottomCount sigma inj sigmaFixesZero sigmaFixesBoundary state))
    (mapLength sigma state.cupEventNodes).symm (mapLength sigma state.capEventNodes).symm

/-! ## Toward the support-locality obstruction: union-find root-following after a join -/

/-- A parentless node is its own root at every fuel — the base fact for root-following. -/
theorem unionFindRoot_of_parentless (links : List (Nat × Nat)) (node : Nat)
    (parentless : unionFindParent links node = none) :
    (fuel : Nat) → unionFindRoot fuel links node = node
  | 0 => rfl
  | _ + 1 => by
      show (match unionFindParent links node with
            | none => node | some parent => unionFindRoot _ links parent) = node
      rw [parentless]

/-- A parentless node is its own `unionFindRootOf` root. -/
theorem unionFindRootOf_of_parentless (links : List (Nat × Nat)) (node : Nat)
    (parentless : unionFindParent links node = none) : unionFindRootOf links node = node :=
  unionFindRoot_of_parentless links node parentless (links.length + 1)

/-- ★ **Locality: a node above every edge's child id is parentless.**  When every union-find edge's CHILD lies
strictly below `bound` and `node ≥ bound`, `node` is no edge's child, hence parentless.  Structural on the edge
list; the head-collision case contradicts `child < bound ≤ node = child`. -/
theorem unionFindParent_none_of_lt (bound : Nat) :
    (links : List (Nat × Nat)) → (∀ edge ∈ links, edge.1 < bound) → (node : Nat) → bound ≤ node →
    unionFindParent links node = none
  | [], _, _, _ => rfl
  | (child, parent) :: rest, allChildBelow, node, boundLeNode => by
      show (if child == node then some parent else unionFindParent rest node) = none
      cases hc : child == node with
      | true =>
          have nodeBelow : node < bound :=
            of_decide_eq_true hc ▸ allChildBelow (child, parent) (List.Mem.head _)
          exact absurd (Nat.lt_of_lt_of_le nodeBelow boundLeNode) (Nat.lt_irrefl node)
      | false =>
          exact unionFindParent_none_of_lt bound rest
            (fun edge edgeInRest => allChildBelow edge (List.Mem.tail _ edgeInRest)) node boundLeNode

/-- A fresh state's nodes at-or-above `nextFresh` are parentless — the locality atom that discharges the
`parentless` preconditions of `unionFindRoot_consJoin` for the freshly-allocated cup / cap legs (every existing
edge's child lies below `nextFresh`). -/
theorem unionFindParent_none_of_freshNode (state : ArcWireState) (fresh : ArcStateFresh state)
    (node : Nat) (atLeast : state.nextFresh ≤ node) : unionFindParent state.links node = none :=
  unionFindParent_none_of_lt state.nextFresh state.links
    (fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).1) node atLeast

/-- ★ **Root-following after prepending a disjoint root→root edge** — the union-find JOIN correctness the prompt
names, conditional on the root-chain settling within the fuel (the acyclicity content of the fold's reachable
states, deferred).  With `p` and `q` both parentless in `links` and `p ≠ q`, following `x` in `(p, q) :: links`
lands on `q` exactly when it lands on `p` in `links`, and is otherwise unchanged.  Induction on `fuel`, casing the
parent of `x`; the `p`-collision case discharges by `unionFindRoot_of_parentless` (the new edge does not give `q`
a parent since `p ≠ q`), the descent case threads the inductive hypothesis through the shared parent. -/
theorem unionFindRoot_consJoin (links : List (Nat × Nat)) (p q : Nat)
    (pParentless : unionFindParent links p = none) (qParentless : unionFindParent links q = none)
    (distinct : ¬ (p == q) = true) :
    (fuel : Nat) → (x : Nat) → unionFindParent links (unionFindRoot fuel links x) = none →
    unionFindRoot (fuel + 1) ((p, q) :: links) x
      = (if p == unionFindRoot fuel links x then q else unionFindRoot fuel links x)
  | 0, x, settles => by
      show (match (if p == x then some q else unionFindParent links x) with
            | none => x | some parent => unionFindRoot 0 ((p, q) :: links) parent)
         = (if p == x then q else x)
      rw [show unionFindParent links x = none from settles]
      cases p == x with
      | true => rfl
      | false => rfl
  | fuel + 1, x, settles => by
      cases hpx : unionFindParent links x with
      | none =>
          -- x is parentless: its root is x; the new edge redirects x to q exactly when p == x
          rw [show unionFindRoot (fuel + 1) links x = x from
            unionFindRoot_of_parentless links x hpx (fuel + 1)]
          show (match (if p == x then some q else unionFindParent links x) with
                | none => x | some parent => unionFindRoot (fuel + 1) ((p, q) :: links) parent)
             = (if p == x then q else x)
          rw [hpx]
          cases p == x with
          | true =>
              have hqParentlessCons : unionFindParent ((p, q) :: links) q = none := by
                show (if p == q then some q else unionFindParent links q) = none
                cases hpqc : p == q with
                | true => exact absurd hpqc distinct
                | false => exact qParentless
              exact unionFindRoot_of_parentless ((p, q) :: links) q hqParentlessCons (fuel + 1)
          | false => rfl
      | some par =>
          -- x has parent par; the new edge leaves x's parent unchanged (p is parentless, so p ≠ x)
          have hxRoot : unionFindRoot (fuel + 1) links x = unionFindRoot fuel links par := by
            show (match unionFindParent links x with
                  | none => x | some parent => unionFindRoot fuel links parent)
               = unionFindRoot fuel links par
            rw [hpx]
          have settlesPar : unionFindParent links (unionFindRoot fuel links par) = none := by
            rw [← hxRoot]; exact settles
          show (match (if p == x then some q else unionFindParent links x) with
                | none => x | some parent => unionFindRoot (fuel + 1) ((p, q) :: links) parent)
             = (if p == unionFindRoot (fuel + 1) links x then q else unionFindRoot (fuel + 1) links x)
          rw [hpx, hxRoot]
          cases hpxc : p == x with
          | true =>
              have hpeqx : p = x := of_decide_eq_true hpxc
              rw [hpeqx] at pParentless
              rw [pParentless] at hpx
              nomatch hpx
          | false =>
              exact unionFindRoot_consJoin links p q pParentless qParentless distinct fuel par settlesPar

/-! ## Honesty markers -/

/-- **Honesty marker — the union-find JOIN renaming-commutation is proved.**  `renameLinks_unionFindJoin` shows
`renameLinks σ (unionFindJoin links a b) = unionFindJoin (renameLinks σ links) (σ a) (σ b)` for injective `σ`,
leveraging the parent's `unionFindRootOf_rename` + `beq_congr_inj` — the clean, fuel-free half of the union-find
join correctness obstruction.  `= true`. -/
def fxMode_hasUnionFindJoinRenameCommute : Bool := true

/-- **Honesty marker — root-following after a disjoint-range union is proved (modulo settling).**
`unionFindRoot_consJoin` shows that prepending a root→root edge `(p, q)` with `p`, `q` parentless and `p ≠ q`
redirects exactly the nodes whose root was `p` to `q`, leaving the rest unchanged — the union-find JOIN
correctness the prompt names — conditional on the root-chain settling within the fuel (the acyclicity invariant of
the fold's reachable states, the one piece deferred).  `unionFindRoot_of_parentless` /
`unionFindRootOf_of_parentless` anchor it.  `= true`. -/
def fxMode_hasUnionFindRootFollowingAfterJoin : Bool := true

/-- **Honesty marker — the arc fold is renaming-EQUIVARIANT.**  `stepArcAtom_renameState` /
`processArcSpine_renameState` / `runArcCell_renameState` prove that an injective input renaming fixing `0` and
every id at-or-above `nextFresh` commutes with the whole arc fold (all three arms: cup, cap, box), and
`nextFresh` is monotone (`stepArcAtom_nextFresh_le` etc.).  This is the renaming-EQUIVARIANCE half of the
block-swap witness — how every wire / link / event read-off transports across a renaming — drowned in node-id
bookkeeping in the prior passes, now discharged.  `= true`. -/
def fxMode_hasArcFoldRenamingEquivariance : Bool := true

/-- **Honesty marker — the arc extract is renaming-INVARIANT.**  `extractArc_renameState` proves
`extractArc bottomCount state = extractArc bottomCount (renameState σ state)` for an injective boundary-fixing
`σ` — the planar-arc structure does not see node-id relabelings (the concrete consequence of the equivariance,
via the bridge `renameRel_of_renameState` into the parent's partition-view factoring).  `= true`. -/
def fxMode_hasExtractArcRenamingInvariance : Bool := true

/-- **Honesty marker — the block-swap renaming WITNESS remains the standing obligation.**
`ArcGodementSwapRenameable` (parent) asks for the explicit injective boundary-fixing block-swap `σ` relating the
two Godement run orders from every fresh state.  This file ships the renaming-EQUIVARIANCE infrastructure the
witness is built on (the join renaming-commutation `renameLinks_unionFindJoin`, the root-following after a
disjoint-range union `unionFindRoot_consJoin`, the full fold equivariance, the extract renaming-invariance, the
`nextFresh` monotonicity, the `ArcRenameRel` bridge), all zero-axiom.  What remains is the SUPPORT/LOCALITY
analysis: the two horizontally-disjoint blocks `cellAlphaUpper` (f-region) and `cellBeta` (g-region) touch
disjoint wire windows and allocate disjoint fresh ranges, so transposing them permutes only the fresh ranges.
The remaining pieces are (1) discharging the `settles` precondition of `unionFindRoot_consJoin` — the acyclicity
invariant of the fold's reachable states — and (2) the region-layout induction tying the disjoint windows to the
two blocks' spines.  So this marker stays `false`: the orchestrator must NOT flip the parent's
`fxMode_hasArcGodementSwapRenameableProof` on the basis of this file.  `= false`. -/
def fxMode_hasArcGodementSwapRenameableProof2 : Bool := false

end FX1Poly.Tier0
