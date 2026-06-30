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

## What is honest-DEFERRED (the genuine combinatorial core) — and the `renameState` route REFUTED

`ArcGodementSwapRenameable` — `fxMode_hasArcGodementSwapRenameableProof2 = false`.  The remaining obstruction is
the SUPPORT/LOCALITY analysis: the two horizontally-disjoint blocks `cellAlphaUpper` (f-region) and `cellBeta`
(g-region) touch disjoint wire windows and allocate disjoint fresh ranges, so transposing them only permutes the
fresh ranges — the block-swap renaming.  The renaming-EQUIVARIANCE half (how every read-off transports across an
injective renaming) and the acyclicity/forest invariant (the root-following after a disjoint-range union) are
proved here.

★ **A prior pass tried to close the residual by suffix-peeling to a `renameState`-EQUALITY core swap
(`ArcGodementCoreSwapRenameable`); that formulation is now PROVED FALSE** —
`not_arcGodementCoreSwapRenameable_adjunction` (zero-axiom) refutes it at the empty fresh state.  Demanding a
single `σ` to realise both the redex↔reduct open-wire range swap (`[0,1,3,4]` vs `[3,4,0,1]`) and the IDENTICAL
union-find link lists is unsatisfiable.  So `arcGodementSwapRenameable_of_coreSwap` is a SOUND but
vacuously-usable implication; the live route is to construct the `ArcRenameRel` between the two full run orders
DIRECTLY (its boundary / root / event-count fields ARE invisible to the fresh-id allocation ORDER, unlike raw
`renameState` equality).  That direct `ArcRenameRel` witness — the genuine Mazurkiewicz-independence construction —
is the standing obligation.

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

/-! ## The forest / acyclicity invariant — discharging the `settles` precondition unconditionally

`unionFindRoot_consJoin` was conditional on the root chain settling within the fuel.  That obligation is exactly
the acyclicity of the fold's reachable states, and it is preserved by the only operation that ever touches the
links — `unionFindJoin`, which prepends a `root → root` edge between two DISTINCT roots.  Capturing that shape as a
structural FOREST predicate makes settling a finite induction over the already-shipped lemmas, and the predicate
is preserved by every fold step (cup / cap / box) from the empty initial `links`. -/

/-- ★ **The union-find edge list forms a forest.**  Read head-to-tail, every edge's child AND parent are roots in
the edges strictly below it (parentless in the tail), and the two endpoints differ.  This is precisely the shape
`unionFindJoin` maintains — it only ever prepends a `root → root` edge between two distinct roots — and it is
strong enough to make every root chain settle (`unionFindRootOf_parentless_of_forest`).  Structural recursion on
the edge list; `propext`-free, and reduces definitionally on `cons` (`isUnionFindForest_cons`). -/
def isUnionFindForest : List (Nat × Nat) → Prop
  | [] => True
  | edge :: rest =>
      unionFindParent rest edge.1 = none ∧ unionFindParent rest edge.2 = none
        ∧ ¬ (edge.1 == edge.2) = true ∧ isUnionFindForest rest

/-- The forest predicate unfolds definitionally on `cons` (proved by `rfl`, so `propext`-free) — the explicit
shape `isUnionFindForest (edge :: rest)` exposes for downstream destructuring. -/
theorem isUnionFindForest_cons (edge : Nat × Nat) (rest : List (Nat × Nat)) :
    isUnionFindForest (edge :: rest)
      = (unionFindParent rest edge.1 = none ∧ unionFindParent rest edge.2 = none
          ∧ ¬ (edge.1 == edge.2) = true ∧ isUnionFindForest rest) := rfl

/-- The empty edge list is a forest — the fold's initial `links`. -/
theorem isUnionFindForest_nil : isUnionFindForest ([] : List (Nat × Nat)) := trivial

/-- ★ **A forest settles: every node's root is parentless** — the acyclicity content that DISCHARGES the `settles`
precondition of `unionFindRoot_consJoin` unconditionally.  Structural induction on the edge list: the empty list
is immediate; for `edge :: rest`, the inductive hypothesis (the root of `x` in `rest` is parentless in `rest`)
discharges the exact `settles` obligation of `unionFindRoot_consJoin rest edge.1 edge.2`, which computes the root
of `x` in the bigger list as `if edge.1 == rootInRest then edge.2 else rootInRest` — and in either case the head
edge `(edge.1, edge.2)` leaves that node parentless (`edge.1 ≠ edge.2` keeps `edge.2` parentless, the inductive
hypothesis keeps `rootInRest` parentless).  No fuel / well-founded recursion; the only self-call is on the shorter
`rest`, and the `settles` hypothesis of `unionFindRoot_consJoin` is supplied by the inductive hypothesis. -/
theorem unionFindRootOf_parentless_of_forest :
    (links : List (Nat × Nat)) → isUnionFindForest links → (x : Nat) →
    unionFindParent links (unionFindRootOf links x) = none
  | [], _, _ => rfl
  | edge :: rest, hforest, x => by
      have hchild : unionFindParent rest edge.1 = none := hforest.1
      have hparent : unionFindParent rest edge.2 = none := hforest.2.1
      have hdistinct : ¬ (edge.1 == edge.2) = true := hforest.2.2.1
      have hrest : isUnionFindForest rest := hforest.2.2.2
      have ih : unionFindParent rest (unionFindRootOf rest x) = none :=
        unionFindRootOf_parentless_of_forest rest hrest x
      have key : unionFindRootOf (edge :: rest) x
          = (if edge.1 == unionFindRootOf rest x then edge.2 else unionFindRootOf rest x) :=
        unionFindRoot_consJoin rest edge.1 edge.2 hchild hparent hdistinct (rest.length + 1) x ih
      rw [key]
      cases hcond : edge.1 == unionFindRootOf rest x with
      | true =>
          show (if edge.1 == edge.2 then some edge.2 else unionFindParent rest edge.2) = none
          cases hpair : edge.1 == edge.2 with
          | true => exact absurd hpair hdistinct
          | false => exact hparent
      | false =>
          show (if edge.1 == unionFindRootOf rest x then some edge.2
                  else unionFindParent rest (unionFindRootOf rest x)) = none
          cases hcond2 : edge.1 == unionFindRootOf rest x with
          | true => rw [hcond] at hcond2; exact Bool.noConfusion hcond2
          | false => exact ih

/-- ★ **Root-following after a disjoint-range union, UNCONDITIONAL on a forest.**  When `links` is a forest with
`p`, `q` parentless and `p ≠ q`, prepending the root→root edge `(p, q)` redirects exactly the nodes whose root was
`p` to `q`, leaving every other root unchanged — `unionFindRoot_consJoin` with its `settles` precondition
discharged by `unionFindRootOf_parentless_of_forest`.  The fuel matches `unionFindRootOf` on both sides
(`((p, q) :: links).length + 1 = links.length + 2`), so this is the strengthened, hypothesis-free form the
block-swap witness will consume. -/
theorem unionFindRootOf_consJoin (links : List (Nat × Nat)) (p q : Nat)
    (hforest : isUnionFindForest links)
    (pParentless : unionFindParent links p = none) (qParentless : unionFindParent links q = none)
    (distinct : ¬ (p == q) = true) (x : Nat) :
    unionFindRootOf ((p, q) :: links) x
      = (if p == unionFindRootOf links x then q else unionFindRootOf links x) :=
  unionFindRoot_consJoin links p q pParentless qParentless distinct (links.length + 1) x
    (unionFindRootOf_parentless_of_forest links hforest x)

/-! ## The forest invariant is preserved by every fold step -/

/-- ★ **The union-find JOIN preserves the forest invariant.**  When already joined the links are returned
verbatim; otherwise the prepended edge `(rootFirst, rootSecond)` has both endpoints parentless
(`unionFindRootOf_parentless_of_forest`) and distinct (the else-branch test), so the consed list is again a
forest.  The single combinatorial step that makes the whole fold acyclic. -/
theorem isUnionFindForest_unionFindJoin (links : List (Nat × Nat)) (firstNode secondNode : Nat)
    (hforest : isUnionFindForest links) :
    isUnionFindForest (unionFindJoin links firstNode secondNode) := by
  show isUnionFindForest
      (if unionFindRootOf links firstNode == unionFindRootOf links secondNode then links
        else (unionFindRootOf links firstNode, unionFindRootOf links secondNode) :: links)
  cases hcond : unionFindRootOf links firstNode == unionFindRootOf links secondNode with
  | true => exact hforest
  | false =>
      show unionFindParent links (unionFindRootOf links firstNode) = none
        ∧ unionFindParent links (unionFindRootOf links secondNode) = none
        ∧ ¬ (unionFindRootOf links firstNode == unionFindRootOf links secondNode) = true
        ∧ isUnionFindForest links
      refine ⟨unionFindRootOf_parentless_of_forest links hforest firstNode,
        unionFindRootOf_parentless_of_forest links hforest secondNode, ?_, hforest⟩
      intro htrue
      rw [hcond] at htrue
      exact Bool.noConfusion htrue

/-- A CUP step preserves the forest invariant — its `links` is two nested `unionFindJoin`s over `state.links`. -/
theorem isUnionFindForest_stepCupArc (state : ArcWireState) (position : Nat)
    (hforest : isUnionFindForest state.links) :
    isUnionFindForest (stepCupArc state position).links := by
  show isUnionFindForest
      (unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh)
  exact isUnionFindForest_unionFindJoin _ _ _ (isUnionFindForest_unionFindJoin _ _ _ hforest)

/-- A CAP step preserves the forest invariant — its `links` is two nested `unionFindJoin`s over `state.links`. -/
theorem isUnionFindForest_stepCapArc (state : ArcWireState) (position : Nat)
    (hforest : isUnionFindForest state.links) :
    isUnionFindForest (stepCapArc state position).links := by
  show isUnionFindForest
      (unionFindJoin (unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1))) state.nextFresh
        (natListGetAt state.openWires position))
  exact isUnionFindForest_unionFindJoin _ _ _ (isUnionFindForest_unionFindJoin _ _ _ hforest)

/-- ★ **One arc step preserves the forest invariant** — cup / cap via the nested-join lemmas, box leaves `links`
untouched.  By the three arms of `stepArcAtom`. -/
theorem isUnionFindForest_stepArcAtom {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (hforest : isUnionFindForest state.links) :
    isUnionFindForest (stepArcAtom state atom).links := by
  unfold stepArcAtom
  split
  · exact isUnionFindForest_stepCupArc state _ hforest
  · exact isUnionFindForest_stepCapArc state _ hforest
  · exact hforest

/-- ★ **The whole arc fold preserves the forest invariant.**  Structural recursion on the spine, threading
`isUnionFindForest_stepArcAtom` through each atom — so every reachable fold state has acyclic `links`. -/
theorem isUnionFindForest_processArcSpine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : ArcWireState) →
    isUnionFindForest state.links → isUnionFindForest (processArcSpine state atoms).links
  | [], _, hforest => hforest
  | atom :: rest, state, hforest =>
      isUnionFindForest_processArcSpine rest (stepArcAtom state atom)
        (isUnionFindForest_stepArcAtom state atom hforest)

/-- Running one cell preserves the forest invariant. -/
theorem isUnionFindForest_runArcCell {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (state : ArcWireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod)
    (hforest : isUnionFindForest state.links) :
    isUnionFindForest (runArcCell state leftAcc rightAcc cell).links :=
  isUnionFindForest_processArcSpine (cell.spineDiff leftAcc rightAcc []) state hforest

/-- The canonical INITIAL arc state has forest `links` (empty), so every state reachable by the fold from it has
acyclic `links` — the standing acyclicity invariant of the reachable states, now established. -/
theorem isUnionFindForest_initialLinks (bottomCount : Nat) :
    isUnionFindForest (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []).links :=
  isUnionFindForest_nil

/-! ## The suffix-peel: reducing the full block-swap to the core swap

The two Godement run orders share a common `cellAlpha` prefix and a common `cellBetaUpper`-then-`rest` suffix —
they differ only in the ORDER of the two middle blocks `cellAlphaUpper` (f-region) and `cellBeta` (g-region).  The
renaming-equivariance of the fold lets us PEEL the common suffix: if the two CORE post-prefix states are a
`renameState` of each other, the full final states are too, so the residual collapses to the explicit block-swap
`σ` between the two core states alone (residual (2), the support/locality analysis — still open). -/

/-- ★ **Suffix-transport: applying a common cell then a common tail spine commutes with an injective renaming.**
Composes `runArcCell_renameState` (for the suffix cell) with `processArcSpine_renameState` (for the tail), the
`nextFresh`-monotonicity (`runArcCell_nextFresh_le`) shrinking the fixed range across the cell.  The engine of the
suffix-peel: a `renameState` between two states is preserved by running the same `cellBetaUpper`-then-`rest`
suffix. -/
theorem processArcSpine_runArcCell_renameState {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0)
    (source : ArcWireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod)
    (rest : List (SpineAtom signature overallSource overallTarget))
    (fixesAbove : ∀ identifier, source.nextFresh ≤ identifier → sigma identifier = identifier) :
    processArcSpine (runArcCell (renameState sigma source) leftAcc rightAcc cell) rest
      = renameState sigma (processArcSpine (runArcCell source leftAcc rightAcc cell) rest) := by
  rw [runArcCell_renameState sigma inj sigmaFixesZero source leftAcc rightAcc cell fixesAbove]
  exact processArcSpine_renameState sigma inj sigmaFixesZero rest (runArcCell source leftAcc rightAcc cell)
    (fun identifier idAtLeast =>
      fixesAbove identifier (Nat.le_trans (runArcCell_nextFresh_le source leftAcc rightAcc cell) idAtLeast))

/-- ★ **The core block-swap** — the residual stripped of its common suffix.  From the post-`cellAlpha` state, the
two core run orders (redex: `cellAlphaUpper` then `cellBeta`; reduct: `cellBeta` then `cellAlphaUpper`, with the
correctly-accumulated whisker contexts) are asked to be a single injective boundary-fixing `renameState` of each
other, with `σ` also fixing every id at-or-above the redex core's `nextFresh` (so the common suffix transports).

★ **WARNING — this `renameState`-equality formulation is FALSE** (refuted, machine-checked and zero-axiom, by
`not_arcGodementCoreSwapRenameable_adjunction` below).  It is STRICTLY stronger than the `ArcRenameRel` the parent
`ArcGodementSwapRenameable` consumes, and the strengthening is unsound: the two horizontally-disjoint blocks
allocate the second-run block's legs to the SAME high id range but on OPPOSITE sides (redex's `cellBeta` to the
right, reduct's `cellAlphaUpper` to the left), so the open-wire lists differ by a low↔high range swap while the
union-find link lists come out IDENTICAL — and the unique `σ` matching the open wires then breaks the (identical)
links.  Concretely at the empty fresh state (`bottomCount = 0`, `cellAlpha = id`, `cellAlphaUpper = cellBeta =`
the unit cup) the redex core's open wires are `[0, 1, 3, 4]` and the reduct core's are `[3, 4, 0, 1]`, forcing
`σ 0 = 3` against the mandated `σ 0 = 0`.  So `arcGodementSwapRenameable_of_coreSwap` is a SOUND but
vacuously-usable implication; the live route to the parent residual is the WEAKER `ArcRenameRel` directly (which
the fresh-id allocation difference is invisible to), NOT this raw-state equality. -/
def ArcGodementCoreSwapRenameable (signature : ModeSignature) : Prop :=
  ∀ {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (bottomCount : Nat) (state : ArcWireState),
    ArcStateFresh state → bottomCount ≤ state.nextFresh →
    ∃ sigma : Nat → Nat,
      (∀ a b, sigma a = sigma b → a = b) ∧ sigma 0 = 0
        ∧ (∀ identifier, identifier < bottomCount → sigma identifier = identifier)
        ∧ (∀ identifier,
            (runArcCell (runArcCell
                (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
                leftAcc (composePath gLow rightAcc) cellAlphaUpper)
              (composePath leftAcc fHigh) rightAcc cellBeta).nextFresh ≤ identifier
            → sigma identifier = identifier)
        ∧ (runArcCell (runArcCell
              (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
              (composePath leftAcc fMid) rightAcc cellBeta)
            leftAcc (composePath gMid rightAcc) cellAlphaUpper)
          = renameState sigma
              (runArcCell (runArcCell
                (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
                leftAcc (composePath gLow rightAcc) cellAlphaUpper)
              (composePath leftAcc fHigh) rightAcc cellBeta)

/-- ★ **The suffix-peel reduction: the core block-swap IMPLIES the full block-swap.**  Given the core
`renameState` `σ` between the two post-`cellAlpha` core states, the common `cellBetaUpper`-then-`rest` suffix
transports it (`processArcSpine_runArcCell_renameState`, with the core-`nextFresh` fixing hypothesis), so the two
full final states are `renameState`-related, and `renameRel_of_renameState` packages that as the `ArcRenameRel`
the parent's `ArcGodementSwapRenameable` demands.

★ **NOTE — sound but VACUOUSLY usable.**  This implication is valid, but its hypothesis
`ArcGodementCoreSwapRenameable signature` is UNSATISFIABLE at the adjunction seed (refuted by
`not_arcGodementCoreSwapRenameable_adjunction`): the `renameState`-equality core swap is over-strengthened and
false.  So this theorem does NOT yield `ArcGodementSwapRenameable` for `adjunctionModeSignature`; the parent must
be proved by a route that targets the WEAKER `ArcRenameRel` directly (where the redex/reduct open-wire range swap
and the identical-link mismatch are invisible), bypassing the raw-state `renameState` equality. -/
theorem arcGodementSwapRenameable_of_coreSwap {signature : ModeSignature}
    (coreSwap : ArcGodementCoreSwapRenameable signature) :
    ArcGodementSwapRenameable signature := by
  intro _ _ _ _ _ _ fMid fHigh gLow gMid _ cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc
    rightAcc rest bottomCount state stateFresh bottomLeFresh
  obtain ⟨sigma, inj, sigmaFixesZero, sigmaFixesBoundary, fixesAboveCore, coreEq⟩ :=
    coreSwap cellAlpha cellAlphaUpper cellBeta leftAcc rightAcc bottomCount state stateFresh bottomLeFresh
  refine ⟨sigma, ?_⟩
  rw [coreEq, processArcSpine_runArcCell_renameState sigma inj sigmaFixesZero
    (runArcCell (runArcCell
        (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
        leftAcc (composePath gLow rightAcc) cellAlphaUpper)
      (composePath leftAcc fHigh) rightAcc cellBeta)
    (composePath leftAcc fHigh) rightAcc cellBetaUpper rest fixesAboveCore]
  exact renameRel_of_renameState bottomCount sigma inj sigmaFixesZero sigmaFixesBoundary _

/-! ## The `renameState` core block-swap is OVER-STRENGTHENED — a machine-checked refutation

`ArcGodementCoreSwapRenameable` demands the reduct core state be a single `renameState sigma` of the redex core
state — an EXACT raw-state equality (the open-wire list, the union-find link list, and the event lists, all as
ordered lists) modulo one injective `sigma` fixing `0`, the boundary, and the suffix.  That is STRICTLY stronger
than the `ArcRenameRel` the parent `ArcGodementSwapRenameable` actually consumes, and it is FALSE.

The reason: both run orders allocate the SECOND block's fresh legs to the same high id range, but place that block
on OPPOSITE horizontal sides — the redex runs `cellBeta` (the g-region, to the RIGHT) second, the reduct runs
`cellAlphaUpper` (the f-region, to the LEFT) second.  So the two open-wire lists differ by a low↔high range swap
(`lowLegs ++ highLegs` versus `highLegs ++ lowLegs`), while the union-find link lists come out IDENTICAL (the
second-allocated block's edges are prepended the same way regardless of which block it is).  The unique `sigma`
matching the open wires must therefore swap the low and high leg ids — which then relabels the (identical) link
lists and breaks them.  No single `renameState sigma` reconciles both.

`not_arcGodementCoreSwapRenameable_adjunction` makes this rigorous: at the empty fresh state with `bottomCount = 0`,
`cellAlpha = id`, `cellAlphaUpper = cellBeta =` the unit cup, the redex core's open wires COMPUTE to `[0, 1, 3, 4]`
and the reduct core's to `[3, 4, 0, 1]`, so `reductCore = renameState sigma redexCore` forces `sigma 0 = 3`,
contradicting the mandatory `sigma 0 = 0`.  Hence `arcGodementSwapRenameable_of_coreSwap` is a SOUND but
vacuously-usable implication (its hypothesis is unsatisfiable already at the adjunction seed): the keystone's
parent `ArcGodementSwapRenameable` must be reached by the WEAKER `ArcRenameRel` route directly — NOT through this
`renameState` equality. -/

/-- ★ **The `renameState`-equality core block-swap is FALSE at the adjunction seed.**  Instantiated at the empty
fresh state (`bottomCount = 0`), `cellAlpha = id`, `cellAlphaUpper = cellBeta =` the unit cup: the redex core's
open wires reduce to `[0, 1, 3, 4]` and the reduct core's to `[3, 4, 0, 1]`, so any `sigma` with
`reductCore = renameState sigma redexCore` forces `sigma 0 = 3` (the head of the open-wire list), contradicting
the required `sigma 0 = 0`.  Zero-axiom: both core states reduce definitionally and the open-wire heads are read
off by `List.cons` injection.  This refutes the target of `fxMode_hasArcGodementSwapRenameableProof2` — the
`renameState`-equality formulation is over-strengthened; the live route is the `ArcRenameRel`-level parent. -/
theorem not_arcGodementCoreSwapRenameable_adjunction :
    ¬ ArcGodementCoreSwapRenameable adjunctionModeSignature := by
  intro coreSwap
  obtain ⟨sigma, _inj, sigmaFixesZero, _fixesBoundary, _fixesAbove, coreEq⟩ :=
    coreSwap
      (RawTwoCellExpr.id (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))
      adjunctionUnitTwoCell adjunctionUnitTwoCell
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
      0 (ArcWireState.mk [] [] 0 0 [] [])
      (by refine ⟨?_, ?_, ?_, ?_⟩ <;> intro _ mem <;> cases mem)
      (Nat.le_refl 0)
  -- `coreEq` projects on `openWires` to `[3, 4, 0, 1] = [0, 1, 3, 4].map sigma`; its head forces `3 = sigma 0`.
  have hopen : ([3, 4, 0, 1] : List Nat)
      = sigma 0 :: sigma 1 :: sigma 3 :: sigma 4 :: [] :=
    congrArg ArcWireState.openWires coreEq
  injection hopen with headEq _restEq
  rw [sigmaFixesZero] at headEq
  exact absurd headEq (by decide)

/-! ## The DIRECT `ArcRenameRel` route — toward the parent at the renaming level (W5-ARC)

The `renameState`-equality core swap is refuted above.  The live route the prompt names is to build the
`ArcRenameRel` between the two FULL run orders DIRECTLY: its fields (boundary-correspondence / root-commutation /
per-root event-count) ARE invisible to the fresh-id allocation ORDER, whereas raw `renameState` equality reads the
link/event LISTS positionally (and they come out permuted).  The engine is a single-step SIMULATION: a common arc
step preserves `ArcRenameRel` via the SAME `σ`, so the common `cellBetaUpper`-then-`rest` suffix peels at the
renaming level (replacing the dead `renameState` peel).  This section ships the reusable union-find / count / list
helpers the simulation consumes; the next sections build the simulation and the suffix-peel. -/

/-- The recorded parent of any node is a `.2` of some edge, so it is below any bound that bounds every edge's
parent.  Structural on the edge list; the head-collision case reads the bound off `allBelow`. -/
theorem unionFindParent_below (bound : Nat) :
    (links : List (Nat × Nat)) → (∀ edge ∈ links, edge.2 < bound) → (node parent : Nat) →
    unionFindParent links node = some parent → parent < bound
  | [], _, node, parent, h => by
      rw [show unionFindParent ([] : List (Nat × Nat)) node = none from rfl] at h
      nomatch h
  | (child, par) :: rest, allBelow, node, parent, h => by
      have hh : (if child == node then some par else unionFindParent rest node) = some parent := h
      cases hcn : child == node with
      | true => rw [hcn] at hh; rw [← Option.some.inj hh]; exact allBelow (child, par) (List.Mem.head _)
      | false =>
          rw [hcn] at hh
          exact unionFindParent_below bound rest
            (fun edge edgeInRest => allBelow edge (List.Mem.tail _ edgeInRest)) node parent hh

/-- Root-following stays below any parent bound: if every edge's parent is `< bound` and `node < bound`, then
`unionFindRoot fuel links node < bound` — each descent step lands on a recorded parent, itself `< bound`.  Fuel
induction; the parent step via `unionFindParent_below`. -/
theorem unionFindRoot_lt_of_below (links : List (Nat × Nat)) (bound : Nat)
    (allBelow : ∀ edge ∈ links, edge.2 < bound) :
    (fuel : Nat) → (node : Nat) → node < bound → unionFindRoot fuel links node < bound
  | 0, _, h => h
  | fuel + 1, node, h => by
      show (match unionFindParent links node with
            | none => node | some parent => unionFindRoot fuel links parent) < bound
      cases hp : unionFindParent links node with
      | none => exact h
      | some parent =>
          exact unionFindRoot_lt_of_below links bound allBelow fuel parent
            (unionFindParent_below bound links allBelow node parent hp)

/-- ★ **A fresh node's root stays below `nextFresh`.**  In a state whose every link parent is `< bound`, every
`node < bound` has `unionFindRootOf links node < bound`.  The locality fact: an old node's component root is an
old node — so a freshly-allocated id (`≥ nextFresh`) is never the root of an old node. -/
theorem unionFindRootOf_lt_of_fresh (links : List (Nat × Nat)) (bound : Nat)
    (allBelow : ∀ edge ∈ links, edge.2 < bound) (node : Nat) (h : node < bound) :
    unionFindRootOf links node < bound :=
  unionFindRoot_lt_of_below links bound allBelow (links.length + 1) node h

/-- ★ **The union-find JOIN in terms of the pre-join roots** (forest hypothesis).  `unionFindRootOf
(unionFindJoin links a b) x = if rootOf a == rootOf x then rootOf b else rootOf x`: in a forest, prepending the
`root a → root b` edge redirects exactly the nodes whose root was `rootOf a` to `rootOf b`, and the already-joined
no-op branch is the same conditional (when `rootOf a == rootOf b` the redirect is vacuous).  The workhorse that
turns `rootComm` preservation under a step into pure algebra (`unionFindRootOf_consJoin` + the forest invariant). -/
theorem unionFindRootOf_unionFindJoin (links : List (Nat × Nat)) (firstNode secondNode x : Nat)
    (hforest : isUnionFindForest links) :
    unionFindRootOf (unionFindJoin links firstNode secondNode) x
      = (if unionFindRootOf links firstNode == unionFindRootOf links x
          then unionFindRootOf links secondNode else unionFindRootOf links x) := by
  show unionFindRootOf
      (if unionFindRootOf links firstNode == unionFindRootOf links secondNode then links
        else (unionFindRootOf links firstNode, unionFindRootOf links secondNode) :: links) x
    = (if unionFindRootOf links firstNode == unionFindRootOf links x
        then unionFindRootOf links secondNode else unionFindRootOf links x)
  cases hcond : unionFindRootOf links firstNode == unionFindRootOf links secondNode with
  | true =>
      cases hfx : unionFindRootOf links firstNode == unionFindRootOf links x with
      | true =>
          have efx : unionFindRootOf links firstNode = unionFindRootOf links x := of_decide_eq_true hfx
          have efs : unionFindRootOf links firstNode = unionFindRootOf links secondNode :=
            of_decide_eq_true hcond
          show unionFindRootOf links x = unionFindRootOf links secondNode
          rw [← efx]; exact efs
      | false => rfl
  | false =>
      have hdistinct : ¬ (unionFindRootOf links firstNode == unionFindRootOf links secondNode) = true := by
        intro htrue; rw [hcond] at htrue; exact Bool.noConfusion htrue
      exact unionFindRootOf_consJoin links (unionFindRootOf links firstNode)
        (unionFindRootOf links secondNode) hforest
        (unionFindRootOf_parentless_of_forest links hforest firstNode)
        (unionFindRootOf_parentless_of_forest links hforest secondNode) hdistinct x

/-- The per-root event count agrees between two link lists that root every listed event the same way — the
count reads each event only through its root.  Structural on the event list. -/
theorem countEventsInRoot_congr_links (linksFirst linksSecond : List (Nat × Nat)) (rootHere : Nat) :
    (events : List Nat) →
    (∀ eventNode ∈ events, unionFindRootOf linksFirst eventNode = unionFindRootOf linksSecond eventNode) →
    countEventsInRoot linksFirst rootHere events = countEventsInRoot linksSecond rootHere events
  | [], _ => rfl
  | eventNode :: rest, agree => by
      show (if unionFindRootOf linksFirst eventNode == rootHere then 1 else 0)
            + countEventsInRoot linksFirst rootHere rest
         = (if unionFindRootOf linksSecond eventNode == rootHere then 1 else 0)
            + countEventsInRoot linksSecond rootHere rest
      rw [agree eventNode (List.Mem.head _),
        countEventsInRoot_congr_links linksFirst linksSecond rootHere rest
          (fun candidate candidateInRest => agree candidate (List.Mem.tail _ candidateInRest))]

/-- `List` append preserves length additively — reproved by hand (`List.length_append` is avoided to stay clear of
the `propext`-leaking `List.append` simp set).  Structural on the front. -/
theorem lengthAppend : (front back : List Nat) → (front ++ back).length = front.length + back.length
  | [], back => (Nat.zero_add back.length).symm
  | head :: tail, back => by
      show (tail ++ back).length + 1 = (tail.length + 1) + back.length
      rw [lengthAppend tail back, Nat.succ_add]

/-- Splicing a block into a wire list adds the block's length to the total — unconditionally (the splice keeps every
original wire and inserts the block, regardless of whether the position is in range).  Structural on position then
list; the base case via `lengthAppend`. -/
theorem natListInsertAt_length :
    (wires : List Nat) → (position : Nat) → (block : List Nat) →
    (natListInsertAt wires position block).length = wires.length + block.length
  | [], 0, block => by
      show (block ++ ([] : List Nat)).length = (0 : Nat) + block.length
      rw [Nat.zero_add]
      exact lengthAppend block []
  | head :: rest, 0, block => by
      show (block ++ (head :: rest)).length = (head :: rest).length + block.length
      rw [lengthAppend block (head :: rest), Nat.add_comm]
  | [], _ + 1, block => by
      show block.length = (0 : Nat) + block.length
      rw [Nat.zero_add]
  | head :: rest, position + 1, block => by
      show (natListInsertAt rest position block).length + 1 = (rest.length + 1) + block.length
      rw [natListInsertAt_length rest position block, Nat.succ_add]

/-- The cons-successor equation of `natListRemoveTwoAt` as a `rfl`-lemma (the equation compiler will not reduce it
for a free tail — `cases` on the tail forces both shapes to compute). -/
theorem natListRemoveTwoAt_succ (head : Nat) (rest : List Nat) (position : Nat) :
    natListRemoveTwoAt (head :: rest) (position + 1) = head :: natListRemoveTwoAt rest position := by
  cases rest <;> rfl

/-- Removing the two wires at a position is a length CONGRUENCE: two wire lists of equal length stay equal length
after the removal — the removal's length depends only on the input length and the position, not the ids.  Joint
structural recursion on the position and the two lists; the length hypothesis rules out the mismatched-shape arms. -/
theorem natListRemoveTwoAt_length_congr :
    (position : Nat) → (wiresFirst wiresSecond : List Nat) → wiresFirst.length = wiresSecond.length →
    (natListRemoveTwoAt wiresFirst position).length = (natListRemoveTwoAt wiresSecond position).length
  | _, [], [], _ => rfl
  | _, [], _ :: _, hlen => Nat.noConfusion hlen
  | _, _ :: _, [], hlen => Nat.noConfusion hlen
  | 0, [_], [_], _ => rfl
  | 0, [_], _ :: _ :: _, hlen => Nat.noConfusion (Nat.succ.inj hlen)
  | 0, _ :: _ :: _, [_], hlen => Nat.noConfusion (Nat.succ.inj hlen)
  | 0, _ :: _ :: firstRest, _ :: _ :: secondRest, hlen => by
      show firstRest.length = secondRest.length
      exact Nat.succ.inj (Nat.succ.inj hlen)
  | position + 1, headFirst :: restFirst, headSecond :: restSecond, hlen => by
      rw [natListRemoveTwoAt_succ headFirst restFirst position,
        natListRemoveTwoAt_succ headSecond restSecond position]
      show (natListRemoveTwoAt restFirst position).length + 1
         = (natListRemoveTwoAt restSecond position).length + 1
      rw [natListRemoveTwoAt_length_congr position restFirst restSecond (Nat.succ.inj hlen)]

/-! ## Honesty markers -/

/-- **Honesty marker — the `renameState`-equality core block-swap is REFUTED (over-strengthened).**
`not_arcGodementCoreSwapRenameable_adjunction` proves `¬ ArcGodementCoreSwapRenameable adjunctionModeSignature`,
machine-checked and zero-axiom: at the empty fresh state the two core run orders' open-wire lists are `[0, 1, 3, 4]`
(redex) and `[3, 4, 0, 1]` (reduct), so no boundary-and-`0`-fixing injective `σ` makes `reductCore` a
`renameState σ` of `redexCore` (the head forces `σ 0 = 3 ≠ 0`).  Hence the `renameState`-equality formulation that
`arcGodementSwapRenameable_of_coreSwap` reduces to is a DEAD route — sound but with an unsatisfiable hypothesis;
the parent `ArcGodementSwapRenameable` must be reached via the weaker `ArcRenameRel` directly.  `= true`. -/
def fxMode_hasArcCoreSwapRenameStateRefuted : Bool := true

/-- **Honesty marker — the union-find JOIN renaming-commutation is proved.**  `renameLinks_unionFindJoin` shows
`renameLinks σ (unionFindJoin links a b) = unionFindJoin (renameLinks σ links) (σ a) (σ b)` for injective `σ`,
leveraging the parent's `unionFindRootOf_rename` + `beq_congr_inj` — the clean, fuel-free half of the union-find
join correctness obstruction.  `= true`. -/
def fxMode_hasUnionFindJoinRenameCommute : Bool := true

/-- **Honesty marker — root-following after a disjoint-range union is proved UNCONDITIONALLY.**
`unionFindRoot_consJoin` shows that prepending a root→root edge `(p, q)` with `p`, `q` parentless and `p ≠ q`
redirects exactly the nodes whose root was `p` to `q`, leaving the rest unchanged — the union-find JOIN
correctness the prompt names — and `unionFindRootOf_consJoin` discharges its `settles` precondition from the
forest invariant (`unionFindRootOf_parentless_of_forest`), so the strengthened form carries no settling
hypothesis.  `unionFindRoot_of_parentless` / `unionFindRootOf_of_parentless` anchor it.  `= true`. -/
def fxMode_hasUnionFindRootFollowingAfterJoin : Bool := true

/-- **Honesty marker — the arc fold's acyclicity/FOREST invariant is established.**  `isUnionFindForest` captures
the shape `unionFindJoin` maintains (every edge's child and parent are roots in its tail, endpoints distinct);
`unionFindRootOf_parentless_of_forest` proves a forest settles (every root is parentless), discharging the
`settles` precondition of `unionFindRoot_consJoin`; and the predicate is preserved by `unionFindJoin`
(`isUnionFindForest_unionFindJoin`) and hence by every fold step — cup / cap / box / spine / cell
(`isUnionFindForest_stepArcAtom` / `_processArcSpine` / `_runArcCell`) — from the empty initial `links`
(`isUnionFindForest_initialLinks`).  So every reachable fold state has acyclic `links`: residual (1) of the
block-swap obstruction is closed.  `= true`. -/
def fxMode_hasArcFoldForestInvariant : Bool := true

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

/-- **Honesty marker — the block-swap residual is SUFFIX-PEELED to the core swap.**
`arcGodementSwapRenameable_of_coreSwap` proves `ArcGodementCoreSwapRenameable signature → ArcGodementSwapRenameable
signature`: the two Godement run orders share a `cellAlpha` prefix and a `cellBetaUpper`-then-`rest` suffix, and
the suffix-transport `processArcSpine_runArcCell_renameState` carries the core `renameState` through it, with
`renameRel_of_renameState` packaging the result as the `ArcRenameRel` the parent demands.  So everything ABOVE the
explicit core block-swap `σ` (the suffix, the partition read-off, the `ArcRenameRel` bridge) is discharged; the
standing obligation collapses to `ArcGodementCoreSwapRenameable` (residual (2)).  The implication is SOUND, but
residual (2) is now REFUTED as stated (`not_arcGodementCoreSwapRenameable_adjunction`,
`fxMode_hasArcCoreSwapRenameStateRefuted`): the `renameState`-equality core swap is over-strengthened and false,
so this peel is a dead route — the parent must instead be reached at the `ArcRenameRel` level directly.
`= true`. -/
def fxMode_hasArcSwapSuffixPeel : Bool := true

/-- **Honesty marker — the block-swap renaming WITNESS is NOT proved; its `renameState` formulation is REFUTED.**
`ArcGodementSwapRenameable` (parent) asks for an injective boundary-fixing `σ` relating the two Godement run
orders from every fresh state, at the `ArcRenameRel` level.  This file ships the renaming-EQUIVARIANCE
infrastructure (the join renaming-commutation `renameLinks_unionFindJoin`, the root-following after a
disjoint-range union — UNCONDITIONAL via `unionFindRootOf_consJoin` + the forest invariant —, the full fold
equivariance, the extract renaming-invariance, the `nextFresh` monotonicity, the `ArcRenameRel` bridge) and the
forest/acyclicity invariant (residual (1), CLOSED — `fxMode_hasArcFoldForestInvariant`), all zero-axiom.

It ALSO attempted residual (2) by suffix-peeling to a `renameState`-equality core swap
(`ArcGodementCoreSwapRenameable`, `arcGodementSwapRenameable_of_coreSwap`).  **That core swap is now PROVED FALSE**
(`not_arcGodementCoreSwapRenameable_adjunction`, `fxMode_hasArcCoreSwapRenameStateRefuted`): demanding ONE `σ`
that simultaneously realises the redex↔reduct open-wire range swap AND fixes the (identical) link lists is
unsatisfiable — at the empty fresh state the cores' open wires are `[0, 1, 3, 4]` vs `[3, 4, 0, 1]`, forcing
`σ 0 = 3 ≠ 0`.  So the suffix-peel is a DEAD route: `arcGodementSwapRenameable_of_coreSwap` is sound but its
hypothesis can never be met.

The live route to the parent is to build the `ArcRenameRel` between the two FULL run orders DIRECTLY (its
boundary-correspondence / root-commutation / per-root event-count fields ARE invisible to the fresh-id allocation
order, unlike raw `renameState` equality), via the locality/support analysis of the two disjoint blocks — still
open.  This marker therefore STAYS `false`, and the orchestrator must NOT flip the parent's
`fxMode_hasArcGodementSwapRenameableProof` on the basis of this file.  `= false`. -/
def fxMode_hasArcGodementSwapRenameableProof2 : Bool := false

end FX1Poly.Tier0
