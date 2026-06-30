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

/-! ## Freshness (`ArcStateFresh`) is preserved by the whole fold — the simulation's locality anchor

The single-step `ArcRenameRel` simulation needs both run states FRESH at every step (so freshly-allocated legs are
parentless and old nodes' roots stay below `nextFresh`).  The docstring claimed this preservation; it is supplied
here.  First the membership/bound helpers, then the per-step preservation, then the fold. -/

/-- A bound holding on both halves of an append holds on the whole — by hand (`List.mem_append` leaks `propext`).
Structural on the front. -/
theorem mem_append_lt (bound : Nat) :
    (front back : List Nat) → (∀ x ∈ front, x < bound) → (∀ x ∈ back, x < bound) →
    ∀ x ∈ front ++ back, x < bound
  | [], _, _, hback => hback
  | head :: tail, back, hfront, hback => by
      intro x hx
      cases hx with
      | head => exact hfront head (List.Mem.head _)
      | tail _ hxtail =>
          exact mem_append_lt bound tail back (fun y hy => hfront y (List.Mem.tail _ hy)) hback x hxtail

/-- Splicing two bounded blocks keeps every wire bounded. -/
theorem natListInsertAt_all_lt (bound : Nat) :
    (wires : List Nat) → (position : Nat) → (block : List Nat) →
    (∀ w ∈ wires, w < bound) → (∀ b ∈ block, b < bound) →
    ∀ t ∈ natListInsertAt wires position block, t < bound
  | [], 0, block, _, hblock => by
      intro t ht; exact mem_append_lt bound block [] hblock (fun _ hmem => nomatch hmem) t ht
  | head :: rest, 0, block, hwires, hblock => by
      intro t ht; exact mem_append_lt bound block (head :: rest) hblock hwires t ht
  | [], _ + 1, _, _, hblock => by intro t ht; exact hblock t ht
  | head :: rest, position + 1, block, hwires, hblock => by
      intro t ht
      cases ht with
      | head => exact hwires head (List.Mem.head _)
      | tail _ httail =>
          exact natListInsertAt_all_lt bound rest position block
            (fun w hw => hwires w (List.Mem.tail _ hw)) hblock t httail

/-- Removal keeps every surviving wire a member of the original list. -/
theorem mem_natListRemoveTwoAt :
    (wires : List Nat) → (position : Nat) → (x : Nat) → x ∈ natListRemoveTwoAt wires position → x ∈ wires
  | [], _, _, hx => by cases hx
  | [_], 0, _, hx => hx
  | _ :: _ :: _, 0, _, hx => List.Mem.tail _ (List.Mem.tail _ hx)
  | head :: rest, position + 1, x, hx => by
      rw [natListRemoveTwoAt_succ head rest position] at hx
      cases hx with
      | head => exact List.Mem.head _
      | tail _ hxtail => exact List.Mem.tail _ (mem_natListRemoveTwoAt rest position x hxtail)

/-- Removal keeps every surviving wire bounded. -/
theorem natListRemoveTwoAt_all_lt (bound : Nat) (wires : List Nat) (position : Nat)
    (hwires : ∀ w ∈ wires, w < bound) : ∀ t ∈ natListRemoveTwoAt wires position, t < bound :=
  fun t ht => hwires t (mem_natListRemoveTwoAt wires position t ht)

/-- A read wire is bounded — a member (bounded) or the past-the-end default `0` (`< bound` when `bound > 0`). -/
theorem natListGetAt_lt (bound : Nat) (hbound : 0 < bound) :
    (wires : List Nat) → (position : Nat) → (∀ w ∈ wires, w < bound) → natListGetAt wires position < bound
  | [], _, _ => hbound
  | head :: _, 0, hwires => hwires head (List.Mem.head _)
  | _ :: rest, position + 1, hwires =>
      natListGetAt_lt bound hbound rest position (fun w hw => hwires w (List.Mem.tail _ hw))

/-- The freshly-allocated box outputs `(range n).map (· + base)` are all `< base + n`. -/
theorem map_add_lt (base bound : Nat) :
    (wires : List Nat) → (∀ w ∈ wires, w < bound) → ∀ t ∈ wires.map (· + base), t < base + bound
  | [], _ => fun _ hmem => nomatch hmem
  | head :: tail, hwires => by
      intro t ht
      cases ht with
      | head =>
          show head + base < base + bound
          rw [Nat.add_comm head base]
          exact Nat.add_lt_add_left (hwires head (List.Mem.head _)) base
      | tail _ httail =>
          exact map_add_lt base bound tail (fun w hw => hwires w (List.Mem.tail _ hw)) t httail

/-- The union-find JOIN keeps every edge bounded when the pre-join roots of the joined nodes are bounded. -/
theorem unionFindJoin_all_lt (bound : Nat) (links : List (Nat × Nat)) (firstNode secondNode : Nat)
    (hlinks : ∀ edge ∈ links, edge.1 < bound ∧ edge.2 < bound)
    (hfirst : unionFindRootOf links firstNode < bound)
    (hsecond : unionFindRootOf links secondNode < bound) :
    ∀ edge ∈ unionFindJoin links firstNode secondNode, edge.1 < bound ∧ edge.2 < bound := by
  show ∀ edge ∈ (if unionFindRootOf links firstNode == unionFindRootOf links secondNode then links
      else (unionFindRootOf links firstNode, unionFindRootOf links secondNode) :: links),
      edge.1 < bound ∧ edge.2 < bound
  cases unionFindRootOf links firstNode == unionFindRootOf links secondNode with
  | true => exact hlinks
  | false =>
      intro edge hedge
      cases hedge with
      | head => exact ⟨hfirst, hsecond⟩
      | tail _ hedgeTail => exact hlinks edge hedgeTail

/-- ★ **A CUP step preserves freshness.**  Its legs `nf, nf+1, nf+2` are `< nf+3`, the spliced open wires stay
bounded (`natListInsertAt_all_lt`), and the two nested joins stay bounded (`unionFindJoin_all_lt`, the joined
nodes' roots bounded by `unionFindRootOf_lt_of_fresh`).  The event node `nf+2` and the unchanged cap list stay
bounded. -/
theorem stepCupArc_arcStateFresh (state : ArcWireState) (position : Nat) (fresh : ArcStateFresh state) :
    ArcStateFresh (stepCupArc state position) := by
  obtain ⟨hopen, hlinks, hcup, hcap⟩ := fresh
  have hb0 : state.nextFresh < state.nextFresh + 3 := Nat.lt_add_of_pos_right (by decide)
  have hb1 : state.nextFresh + 1 < state.nextFresh + 3 := Nat.add_lt_add_left (by decide) state.nextFresh
  have hb2 : state.nextFresh + 2 < state.nextFresh + 3 := Nat.add_lt_add_left (by decide) state.nextFresh
  have hlinks3 : ∀ edge ∈ state.links, edge.1 < state.nextFresh + 3 ∧ edge.2 < state.nextFresh + 3 :=
    fun edge he => ⟨Nat.lt_trans (hlinks edge he).1 hb0, Nat.lt_trans (hlinks edge he).2 hb0⟩
  have hpar3 : ∀ edge ∈ state.links, edge.2 < state.nextFresh + 3 := fun edge he => (hlinks3 edge he).2
  have hr0 : unionFindRootOf state.links state.nextFresh < state.nextFresh + 3 :=
    unionFindRootOf_lt_of_fresh state.links (state.nextFresh + 3) hpar3 state.nextFresh hb0
  have hr1 : unionFindRootOf state.links (state.nextFresh + 1) < state.nextFresh + 3 :=
    unionFindRootOf_lt_of_fresh state.links (state.nextFresh + 3) hpar3 (state.nextFresh + 1) hb1
  have hlinks1 := unionFindJoin_all_lt (state.nextFresh + 3) state.links state.nextFresh (state.nextFresh + 1)
    hlinks3 hr0 hr1
  have hpar1 : ∀ edge ∈ unionFindJoin state.links state.nextFresh (state.nextFresh + 1),
      edge.2 < state.nextFresh + 3 := fun edge he => (hlinks1 edge he).2
  have hr2 : unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (state.nextFresh + 2) < state.nextFresh + 3 :=
    unionFindRootOf_lt_of_fresh _ (state.nextFresh + 3) hpar1 (state.nextFresh + 2) hb2
  have hr0' : unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      state.nextFresh < state.nextFresh + 3 :=
    unionFindRootOf_lt_of_fresh _ (state.nextFresh + 3) hpar1 state.nextFresh hb0
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact natListInsertAt_all_lt (state.nextFresh + 3) state.openWires position
      [state.nextFresh, state.nextFresh + 1] (fun w hw => Nat.lt_trans (hopen w hw) hb0)
      (fun b hb => by cases hb with
        | head => exact hb0
        | tail _ hbt => cases hbt with
          | head => exact hb1
          | tail _ hbtt => nomatch hbtt)
  · exact unionFindJoin_all_lt (state.nextFresh + 3) _ (state.nextFresh + 2) state.nextFresh hlinks1 hr2 hr0'
  · exact fun node hn => by cases hn with
      | head => exact hb2
      | tail _ hnt => exact Nat.lt_trans (hcup node hnt) hb0
  · exact fun node hn => Nat.lt_trans (hcap node hn) hb0

/-- ★ **A CAP step preserves freshness.**  Its event node `nf` is `< nf+1`, the read wires are bounded
(`natListGetAt_lt`, default `0 < nf+1`), the surviving open wires stay bounded (`natListRemoveTwoAt_all_lt`), and
the two nested joins stay bounded.  The unchanged cup list and the consed event stay bounded. -/
theorem stepCapArc_arcStateFresh (state : ArcWireState) (position : Nat) (fresh : ArcStateFresh state) :
    ArcStateFresh (stepCapArc state position) := by
  obtain ⟨hopen, hlinks, hcup, hcap⟩ := fresh
  have hb0 : state.nextFresh < state.nextFresh + 1 := Nat.lt_succ_self _
  have hpos : (0 : Nat) < state.nextFresh + 1 := Nat.succ_pos _
  have hlinks1bound : ∀ edge ∈ state.links, edge.1 < state.nextFresh + 1 ∧ edge.2 < state.nextFresh + 1 :=
    fun edge he => ⟨Nat.lt_trans (hlinks edge he).1 hb0, Nat.lt_trans (hlinks edge he).2 hb0⟩
  have hpar1 : ∀ edge ∈ state.links, edge.2 < state.nextFresh + 1 := fun edge he => (hlinks1bound edge he).2
  have hleft : natListGetAt state.openWires position < state.nextFresh + 1 :=
    natListGetAt_lt (state.nextFresh + 1) hpos state.openWires position (fun w hw => Nat.lt_trans (hopen w hw) hb0)
  have hright : natListGetAt state.openWires (position + 1) < state.nextFresh + 1 :=
    natListGetAt_lt (state.nextFresh + 1) hpos state.openWires (position + 1)
      (fun w hw => Nat.lt_trans (hopen w hw) hb0)
  have hrl : unionFindRootOf state.links (natListGetAt state.openWires position) < state.nextFresh + 1 :=
    unionFindRootOf_lt_of_fresh state.links (state.nextFresh + 1) hpar1 _ hleft
  have hrr : unionFindRootOf state.links (natListGetAt state.openWires (position + 1)) < state.nextFresh + 1 :=
    unionFindRootOf_lt_of_fresh state.links (state.nextFresh + 1) hpar1 _ hright
  have hlinks1 := unionFindJoin_all_lt (state.nextFresh + 1) state.links
    (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1)) hlinks1bound hrl hrr
  have hpar1' : ∀ edge ∈ unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)), edge.2 < state.nextFresh + 1 :=
    fun edge he => (hlinks1 edge he).2
  have hrev : unionFindRootOf (unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1))) state.nextFresh < state.nextFresh + 1 :=
    unionFindRootOf_lt_of_fresh _ (state.nextFresh + 1) hpar1' state.nextFresh hb0
  have hrl' : unionFindRootOf (unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1))) (natListGetAt state.openWires position)
        < state.nextFresh + 1 :=
    unionFindRootOf_lt_of_fresh _ (state.nextFresh + 1) hpar1' _ hleft
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact natListRemoveTwoAt_all_lt (state.nextFresh + 1) state.openWires position
      (fun w hw => Nat.lt_trans (hopen w hw) hb0)
  · exact unionFindJoin_all_lt (state.nextFresh + 1) _ state.nextFresh (natListGetAt state.openWires position)
      hlinks1 hrev hrl'
  · exact fun node hn => Nat.lt_trans (hcup node hn) hb0
  · exact fun node hn => by cases hn with
      | head => exact hb0
      | tail _ hnt => exact Nat.lt_trans (hcap node hnt) hb0

/-- Every wire surviving the box's input-dropping fold is a member of the original open wires. -/
theorem mem_droppedWires (position : Nat) :
    (numConsumed : Nat) → (openWires : List Nat) → (x : Nat) →
    x ∈ (Nat.rec openWires (fun _ shorter => natListRemoveTwoAt shorter position) numConsumed : List Nat) →
    x ∈ openWires
  | 0, _, _, hx => hx
  | numConsumed + 1, openWires, x, hx =>
      mem_droppedWires position numConsumed openWires x
        (mem_natListRemoveTwoAt
          (Nat.rec openWires (fun _ shorter => natListRemoveTwoAt shorter position) numConsumed) position x hx)

/-- ★ **One arc step preserves freshness** — cup / cap via the dedicated lemmas, box via the bound on its fresh
outputs (`map_add_lt`) and the untouched links / event lists (`< nextFresh ≤ nextFresh + numProduced`). -/
theorem stepArcAtom_arcStateFresh {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode) (fresh : ArcStateFresh state) :
    ArcStateFresh (stepArcAtom state atom) := by
  unfold stepArcAtom
  split
  · exact stepCupArc_arcStateFresh state _ fresh
  · exact stepCapArc_arcStateFresh state _ fresh
  · obtain ⟨hopen, hlinks, hcup, hcap⟩ := fresh
    have hle : state.nextFresh ≤ state.nextFresh + atom.generatorCod.length := Nat.le_add_right _ _
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine natListInsertAt_all_lt (state.nextFresh + atom.generatorCod.length) _ atom.leftContext.length
        ((List.range atom.generatorCod.length).map (· + state.nextFresh)) ?_ ?_
      · exact fun w hw => Nat.lt_of_lt_of_le
          (hopen w (mem_droppedWires atom.leftContext.length atom.generatorDom.length state.openWires w hw)) hle
      · exact fun b hb => map_add_lt state.nextFresh atom.generatorCod.length
          (List.range atom.generatorCod.length) (fun k hk => mem_range_imp_lt hk) b hb
    · exact fun edge he => ⟨Nat.lt_of_lt_of_le (hlinks edge he).1 hle, Nat.lt_of_lt_of_le (hlinks edge he).2 hle⟩
    · exact fun node hn => Nat.lt_of_lt_of_le (hcup node hn) hle
    · exact fun node hn => Nat.lt_of_lt_of_le (hcap node hn) hle

/-- The whole arc fold preserves freshness — structural recursion on the spine. -/
theorem processArcSpine_arcStateFresh {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : ArcWireState) →
    ArcStateFresh state → ArcStateFresh (processArcSpine state atoms)
  | [], _, fresh => fresh
  | atom :: rest, state, fresh =>
      processArcSpine_arcStateFresh rest (stepArcAtom state atom) (stepArcAtom_arcStateFresh state atom fresh)

/-- Running one cell preserves freshness. -/
theorem runArcCell_arcStateFresh {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (state : ArcWireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod) (fresh : ArcStateFresh state) :
    ArcStateFresh (runArcCell state leftAcc rightAcc cell) :=
  processArcSpine_arcStateFresh (cell.spineDiff leftAcc rightAcc []) state fresh

/-! ## The union-find AUTOMORPHISM transport — `rootComm` is preserved by a corresponding join

This is the mathematical heart of the direct route, and exactly what the dead `renameState`-equality route could
NOT express.  `ArcRenameRel.rootComm` says `σ` is a union-find AUTOMORPHISM (`rootOf t (σ x) = σ (rootOf s x)`),
which is order-INSENSITIVE — unlike raw link-list equality.  We show this automorphism property is PRESERVED when
both states perform a `σ`-corresponding `unionFindJoin`.  With `unionFindRootOf_unionFindJoin` reducing each join
to a conditional on pre-join roots, the proof is pure algebra: push `σ` through the conditional via the old
`rootComm` + `beq_congr_inj`. -/

/-- Pushing an injective renaming through a boolean `if` (the conditional has the SAME guard on both sides). -/
theorem ite_push_sigma (sigma : Nat → Nat) (guard : Bool) (whenTrue whenFalse : Nat) :
    (if guard then sigma whenTrue else sigma whenFalse) = sigma (if guard then whenTrue else whenFalse) := by
  cases guard with
  | true => rfl
  | false => rfl

/-- ★ **The union-find automorphism property is preserved by a corresponding join.**  If `σ` root-commutes
between forests `linksS` and `linksT`, and the two joined node-pairs correspond under `σ` (`firstT = σ firstS`,
`secondT = σ secondS`), then `σ` still root-commutes after the join.  Pure algebra over
`unionFindRootOf_unionFindJoin` (each join's root reduced to a guard on pre-join roots) + the old `rootComm` +
`beq_congr_inj` (the guard transports) + `ite_push_sigma` (the branch values transport).  The order-INSENSITIVE
content the `renameState`-equality core swap could not capture. -/
theorem rootComm_unionFindJoin (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b)
    (linksS linksT : List (Nat × Nat))
    (hforestS : isUnionFindForest linksS) (hforestT : isUnionFindForest linksT)
    (firstS secondS firstT secondT : Nat)
    (hfirst : firstT = sigma firstS) (hsecond : secondT = sigma secondS)
    (hRoot : ∀ x, unionFindRootOf linksT (sigma x) = sigma (unionFindRootOf linksS x)) :
    ∀ x, unionFindRootOf (unionFindJoin linksT firstT secondT) (sigma x)
      = sigma (unionFindRootOf (unionFindJoin linksS firstS secondS) x) := by
  intro x
  rw [unionFindRootOf_unionFindJoin linksT firstT secondT (sigma x) hforestT,
    unionFindRootOf_unionFindJoin linksS firstS secondS x hforestS,
    hfirst, hsecond, hRoot firstS, hRoot x, hRoot secondS, beq_congr_inj sigma inj]
  exact ite_push_sigma sigma _ _ _

/-- The two leg ids a step allocates at `nextFresh (+1/+2)` correspond to themselves under a `σ` fixing the
future-allocation tail — the equal-`nextFresh` companion fact the cup/cap rootComm transports consume. -/
theorem freshLeg_corr (sigma : Nat → Nat) (nextFreshS nextFreshT : Nat) (hnf : nextFreshS = nextFreshT)
    (fixesAbove : ∀ identifier, nextFreshS ≤ identifier → sigma identifier = identifier) (offset : Nat) :
    nextFreshT + offset = sigma (nextFreshS + offset) := by
  rw [fixesAbove (nextFreshS + offset) (Nat.le_add_right _ _), hnf]

/-- ★ **A CUP step preserves the union-find automorphism property.**  The cup's links are two nested joins of the
FRESH legs `nf, nf+1, nf+2` (id-identical on both states by equal `nextFresh`, fixed by `σ`), so two applications
of `rootComm_unionFindJoin` (with `freshLeg_corr` discharging every leg correspondence and
`isUnionFindForest_unionFindJoin` the intermediate forest) carry `rootComm` across the whole cup. -/
theorem stepCupArc_rootComm (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b)
    (stateS stateT : ArcWireState)
    (hforestS : isUnionFindForest stateS.links) (hforestT : isUnionFindForest stateT.links)
    (hnf : stateS.nextFresh = stateT.nextFresh)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (hRoot : ∀ x, unionFindRootOf stateT.links (sigma x) = sigma (unionFindRootOf stateS.links x))
    (positionS positionT : Nat) :
    ∀ x, unionFindRootOf (stepCupArc stateT positionT).links (sigma x)
      = sigma (unionFindRootOf (stepCupArc stateS positionS).links x) := by
  intro x
  have hleg0 : stateT.nextFresh = sigma stateS.nextFresh := freshLeg_corr sigma _ _ hnf fixesAbove 0
  have hleg1 : stateT.nextFresh + 1 = sigma (stateS.nextFresh + 1) := freshLeg_corr sigma _ _ hnf fixesAbove 1
  have hleg2 : stateT.nextFresh + 2 = sigma (stateS.nextFresh + 2) := freshLeg_corr sigma _ _ hnf fixesAbove 2
  have hRoot1 := rootComm_unionFindJoin sigma inj stateS.links stateT.links hforestS hforestT
    stateS.nextFresh (stateS.nextFresh + 1) stateT.nextFresh (stateT.nextFresh + 1) hleg0 hleg1 hRoot
  exact rootComm_unionFindJoin sigma inj
    (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
    (unionFindJoin stateT.links stateT.nextFresh (stateT.nextFresh + 1))
    (isUnionFindForest_unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1) hforestS)
    (isUnionFindForest_unionFindJoin stateT.links stateT.nextFresh (stateT.nextFresh + 1) hforestT)
    (stateS.nextFresh + 2) stateS.nextFresh (stateT.nextFresh + 2) stateT.nextFresh hleg2 hleg0 hRoot1 x

/-- ★ **A CAP step preserves the union-find automorphism property** — GIVEN that the two read wires correspond
under `σ` (`hleftCorr` / `hrightCorr`, the boundary-correspondence content at the fire position).  The cap's links
are the join of the two read wires then the join of the fresh event node `nf` with the left wire, so two
applications of `rootComm_unionFindJoin` carry `rootComm` across — exactly as for the cup, with the read-wire
correspondences in place of the fresh-leg ones for the first join. -/
theorem stepCapArc_rootComm (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b)
    (stateS stateT : ArcWireState)
    (hforestS : isUnionFindForest stateS.links) (hforestT : isUnionFindForest stateT.links)
    (hnf : stateS.nextFresh = stateT.nextFresh)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (hRoot : ∀ x, unionFindRootOf stateT.links (sigma x) = sigma (unionFindRootOf stateS.links x))
    (position : Nat)
    (hleftCorr : natListGetAt stateT.openWires position = sigma (natListGetAt stateS.openWires position))
    (hrightCorr :
      natListGetAt stateT.openWires (position + 1) = sigma (natListGetAt stateS.openWires (position + 1))) :
    ∀ x, unionFindRootOf (stepCapArc stateT position).links (sigma x)
      = sigma (unionFindRootOf (stepCapArc stateS position).links x) := by
  intro x
  have hleg0 : stateT.nextFresh = sigma stateS.nextFresh := freshLeg_corr sigma _ _ hnf fixesAbove 0
  have hRoot1 := rootComm_unionFindJoin sigma inj stateS.links stateT.links hforestS hforestT
    (natListGetAt stateS.openWires position) (natListGetAt stateS.openWires (position + 1))
    (natListGetAt stateT.openWires position) (natListGetAt stateT.openWires (position + 1))
    hleftCorr hrightCorr hRoot
  exact rootComm_unionFindJoin sigma inj
    (unionFindJoin stateS.links (natListGetAt stateS.openWires position)
      (natListGetAt stateS.openWires (position + 1)))
    (unionFindJoin stateT.links (natListGetAt stateT.openWires position)
      (natListGetAt stateT.openWires (position + 1)))
    (isUnionFindForest_unionFindJoin stateS.links _ _ hforestS)
    (isUnionFindForest_unionFindJoin stateT.links _ _ hforestT)
    stateS.nextFresh (natListGetAt stateS.openWires position)
    stateT.nextFresh (natListGetAt stateT.openWires position) hleg0 hleftCorr hRoot1 x

/-! ## The structural `ArcRenameRel` fields are preserved by a step (`lengthEq`, `loopsEq`)

The open-wire count and loop count are renaming-INVARIANT data (no ids), so their step-preservation is structural —
`lengthEq` from the insert/remove length lemmas (id-free), `loopsEq` from the cup/box no-op and the cap
same-component test agreeing under `σ` (`rootComm` + `beq_congr_inj`). -/

/-- The box input-dropping fold is a length congruence (iterated `natListRemoveTwoAt_length_congr`). -/
theorem droppedWires_length_congr (position : Nat) :
    (numConsumed : Nat) → (wiresFirst wiresSecond : List Nat) → wiresFirst.length = wiresSecond.length →
    (Nat.rec wiresFirst (fun _ shorter => natListRemoveTwoAt shorter position) numConsumed : List Nat).length
      = (Nat.rec wiresSecond (fun _ shorter => natListRemoveTwoAt shorter position) numConsumed : List Nat).length
  | 0, _, _, hlen => hlen
  | numConsumed + 1, wiresFirst, wiresSecond, hlen =>
      natListRemoveTwoAt_length_congr position _ _
        (droppedWires_length_congr position numConsumed wiresFirst wiresSecond hlen)

/-- ★ **A step preserves the open-wire count equality** — id-free: cup adds 2, cap removes 2, box swaps
`numConsumed` for `numProduced`, all length-functions of the input length alone. -/
theorem stepArcAtom_lengthEq {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (stateS stateT : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (hlen : stateT.openWires.length = stateS.openWires.length) :
    (stepArcAtom stateT atom).openWires.length = (stepArcAtom stateS atom).openWires.length := by
  unfold stepArcAtom
  split
  · show (natListInsertAt stateT.openWires (atom.leftContext.length)
            [stateT.nextFresh, stateT.nextFresh + 1]).length
       = (natListInsertAt stateS.openWires (atom.leftContext.length)
            [stateS.nextFresh, stateS.nextFresh + 1]).length
    rw [natListInsertAt_length, natListInsertAt_length]
    show stateT.openWires.length + 2 = stateS.openWires.length + 2
    rw [hlen]
  · exact natListRemoveTwoAt_length_congr (atom.leftContext.length) stateT.openWires stateS.openWires hlen
  · show (natListInsertAt
            (Nat.rec stateT.openWires (fun _ shorter => natListRemoveTwoAt shorter atom.leftContext.length)
              atom.generatorDom.length)
            atom.leftContext.length ((List.range atom.generatorCod.length).map (· + stateT.nextFresh))).length
       = (natListInsertAt
            (Nat.rec stateS.openWires (fun _ shorter => natListRemoveTwoAt shorter atom.leftContext.length)
              atom.generatorDom.length)
            atom.leftContext.length ((List.range atom.generatorCod.length).map (· + stateS.nextFresh))).length
    rw [natListInsertAt_length, natListInsertAt_length, mapLength, mapLength,
      droppedWires_length_congr atom.leftContext.length atom.generatorDom.length
        stateT.openWires stateS.openWires hlen]

/-- ★ **A step preserves the loop-count equality** — GIVEN the read wires correspond under `σ`.  Cup / box leave
loops untouched; the cap increments iff the two read wires are already in one component, and that boolean agrees on
both states (the read wires correspond under `σ` and `σ` root-commutes, so the same-component `==` transports by
`beq_congr_inj`). -/
theorem stepArcAtom_loopsEq {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b)
    (stateS stateT : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (hRoot : ∀ x, unionFindRootOf stateT.links (sigma x) = sigma (unionFindRootOf stateS.links x))
    (hwireCorr : ∀ index, natListGetAt stateT.openWires index = sigma (natListGetAt stateS.openWires index))
    (hloops : stateT.loops = stateS.loops) :
    (stepArcAtom stateT atom).loops = (stepArcAtom stateS atom).loops := by
  unfold stepArcAtom
  split
  · exact hloops
  · have hsc : isSameComponent stateT.links (natListGetAt stateT.openWires (atom.leftContext.length))
          (natListGetAt stateT.openWires (atom.leftContext.length + 1))
        = isSameComponent stateS.links (natListGetAt stateS.openWires (atom.leftContext.length))
          (natListGetAt stateS.openWires (atom.leftContext.length + 1)) := by
      show (unionFindRootOf stateT.links (natListGetAt stateT.openWires (atom.leftContext.length))
              == unionFindRootOf stateT.links (natListGetAt stateT.openWires (atom.leftContext.length + 1)))
         = (unionFindRootOf stateS.links (natListGetAt stateS.openWires (atom.leftContext.length))
              == unionFindRootOf stateS.links (natListGetAt stateS.openWires (atom.leftContext.length + 1)))
      rw [hwireCorr (atom.leftContext.length), hwireCorr (atom.leftContext.length + 1),
        hRoot (natListGetAt stateS.openWires (atom.leftContext.length)),
        hRoot (natListGetAt stateS.openWires (atom.leftContext.length + 1)), beq_congr_inj sigma inj]
    show (if isSameComponent stateT.links (natListGetAt stateT.openWires (atom.leftContext.length))
              (natListGetAt stateT.openWires (atom.leftContext.length + 1))
            then stateT.loops + 1 else stateT.loops)
       = (if isSameComponent stateS.links (natListGetAt stateS.openWires (atom.leftContext.length))
              (natListGetAt stateS.openWires (atom.leftContext.length + 1))
            then stateS.loops + 1 else stateS.loops)
    rw [hsc, hloops]
  · exact hloops

/-! ## The CUP / BOX count fields reduce to OLD roots (`cupCorr` / `capCorr`, the isolated-component case)

A cup allocates a fresh, ISOLATED 3-node component (`nf, nf+1, nf+2`), so it leaves every OLD node's root unchanged
(the fresh edges' children are `≥ nf`, never on an old chain); a box leaves `links` untouched outright.  The
locality fact below — `unionFindRootOf_stepCupArc_old` — is exactly what reduces the per-root count fields for the
cup / box steps to the INPUT per-root counts: with old roots unchanged, `countEventsInRoot_congr_links` rewrites the
new-link counts to old-link counts, and the input `cupCorr` / `capCorr` transport them (the new cup event handled by
the proven `rootComm`).  So the per-root count residual is isolated to the CAP step alone, whose component MERGE
genuinely redistributes counts (`f(rRw) ↦ f(rLw)+f(rRw)`) — the one remaining hard core. -/

/-- `(b == a) = false` from `a < b` (`==` is `decide (· = ·)` for `Nat`). -/
theorem beq_false_of_lt {a b : Nat} (h : a < b) : (b == a) = false := by
  apply decide_eq_false
  intro heq
  exact absurd heq.symm (Nat.ne_of_lt h)

/-- ★ **A CUP leaves OLD nodes' roots unchanged.**  For `y` with `unionFindRootOf links y < nextFresh` (every old
node, since roots stay below `nextFresh` in a fresh forest), the cup's two fresh joins do not move `y`'s root —
the fresh legs `nf, nf+1, nf+2` form an isolated component whose edge children are all `≥ nextFresh`, so the
guards `nf == rootOf y` / `nf+2 == rootOf y` are false (`rootOf y < nf`).  The locality fact `cupCorr` needs. -/
theorem unionFindRootOf_stepCupArc_old (state : ArcWireState) (position : Nat) (fresh : ArcStateFresh state)
    (hforest : isUnionFindForest state.links) (y : Nat)
    (hrooty : unionFindRootOf state.links y < state.nextFresh) :
    unionFindRootOf (stepCupArc state position).links y = unionFindRootOf state.links y := by
  obtain ⟨_, hlinks, _, _⟩ := fresh
  have hchild : ∀ edge ∈ state.links, edge.1 < state.nextFresh := fun e he => (hlinks e he).1
  have hpnf : unionFindParent state.links state.nextFresh = none :=
    unionFindParent_none_of_lt state.nextFresh state.links hchild state.nextFresh (Nat.le_refl _)
  have hrootnf : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_of_parentless state.links state.nextFresh hpnf
  have hpnf1 : unionFindParent state.links (state.nextFresh + 1) = none :=
    unionFindParent_none_of_lt state.nextFresh state.links hchild (state.nextFresh + 1) (Nat.le_add_right _ _)
  have hrootnf1 : unionFindRootOf state.links (state.nextFresh + 1) = state.nextFresh + 1 :=
    unionFindRootOf_of_parentless state.links (state.nextFresh + 1) hpnf1
  have hnflt2 : state.nextFresh < state.nextFresh + 2 := Nat.lt_add_of_pos_right (by decide)
  have hnf1lt2 : state.nextFresh + 1 < state.nextFresh + 2 := Nat.add_lt_add_left (by decide) state.nextFresh
  have hforest1 : isUnionFindForest (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) :=
    isUnionFindForest_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) hforest
  -- Step 1: the inner join leaves `y`'s root unchanged.
  have hstep1 : unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) y
      = unionFindRootOf state.links y := by
    rw [unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) y hforest, hrootnf]
    cases hc : state.nextFresh == unionFindRootOf state.links y with
    | true => exact absurd (of_decide_eq_true hc).symm (Nat.ne_of_lt hrooty)
    | false => rfl
  -- the fresh event leg `nf+2` is its own root in the inner join (parentless: all inner-join children `< nf+2`).
  have hchild1 : ∀ edge ∈ unionFindJoin state.links state.nextFresh (state.nextFresh + 1),
      edge.1 < state.nextFresh + 2 := fun e he =>
    (unionFindJoin_all_lt (state.nextFresh + 2) state.links state.nextFresh (state.nextFresh + 1)
      (fun edge he => ⟨Nat.lt_trans (hchild edge he) hnflt2,
        Nat.lt_trans (hlinks edge he).2 hnflt2⟩)
      (by rw [hrootnf]; exact hnflt2) (by rw [hrootnf1]; exact hnf1lt2) e he).1
  have hroot2 : unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (state.nextFresh + 2) = state.nextFresh + 2 :=
    unionFindRootOf_of_parentless _ (state.nextFresh + 2)
      (unionFindParent_none_of_lt (state.nextFresh + 2) _ hchild1 (state.nextFresh + 2) (Nat.le_refl _))
  -- Step 3: the outer join (event leg `nf+2 → nf`) leaves `y`'s root unchanged.
  show unionFindRootOf (unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (state.nextFresh + 2) state.nextFresh) y = unionFindRootOf state.links y
  rw [unionFindRootOf_unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (state.nextFresh + 2) state.nextFresh y hforest1, hroot2, hstep1]
  cases hc : state.nextFresh + 2 == unionFindRootOf state.links y with
  | true => exact absurd (of_decide_eq_true hc).symm (Nat.ne_of_lt (Nat.lt_trans hrooty hnflt2))
  | false => rfl

/-! ## The LIVE core obligation — the `ArcRenameRel`-level block swap

The refuted `ArcGodementCoreSwapRenameable` demanded a `renameState`-EQUALITY between the two post-`cellAlpha` core
states; the link/event LISTS come out permuted, so it is false.  The LIVE core states the genuine independence at
the `ArcRenameRel` level (root-commutation / boundary-correspondence / per-root counts — all order-INSENSITIVE), and
ADDITIONALLY asks `σ` to fix the redex core's future-allocation tail so the common `cellBetaUpper`-then-`rest`
suffix transports (the single-step `ArcRenameRel` simulation, of which the `rootComm` / `lengthEq` / `loopsEq`
fields above are the proven part).  This is the reduction target the parent `ArcGodementSwapRenameable` collapses
to once the (partly-proven) simulation peels the suffix — and the witness is the explicit block-swap `σ` permuting
the two disjoint fresh ranges. -/
def ArcGodementCoreSwapRenameRel (signature : ModeSignature) : Prop :=
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
      (∀ identifier,
          (runArcCell (runArcCell
              (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
              leftAcc (composePath gLow rightAcc) cellAlphaUpper)
            (composePath leftAcc fHigh) rightAcc cellBeta).nextFresh ≤ identifier
          → sigma identifier = identifier)
        ∧ ArcRenameRel bottomCount sigma
            (runArcCell (runArcCell
                (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
                leftAcc (composePath gLow rightAcc) cellAlphaUpper)
              (composePath leftAcc fHigh) rightAcc cellBeta)
            (runArcCell (runArcCell
                (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
                (composePath leftAcc fMid) rightAcc cellBeta)
              leftAcc (composePath gMid rightAcc) cellAlphaUpper)

/-! ## W6-ARC — the single-step `ArcRenameRel` SIMULATION: all seven fields are step-stable

The refuted `renameState`-equality route read the link/event LISTS positionally.  The live route maintains the
ORDER-INSENSITIVE invariant: the open wires / cup-event / cap-event lists are pointwise `σ`-images, `nextFresh` is
shared, and `σ` is a union-find AUTOMORPHISM (`rootComm`).  This section proves that invariant — bundled as
`ArcStepSim` — is preserved by a common arc step (cup / cap / box), and that it yields the full `ArcRenameRel`.
Crucially the per-root cup/cap COUNT fields are NOT a separate hard core: they reduce to the proven `rootComm`
through the clean count-transport `countEventsInRoot_rootComm` (the cap MERGE redistributes counts, but it does so
σ-isomorphically, so the relation is preserved). -/

/-- ★ **The per-root event count transports across a `rootComm` automorphism.**  When `σ` root-commutes between
`linksS` and `linksT` (`unionFindRootOf linksT (σ x) = σ (unionFindRootOf linksS x)`), counting the `σ`-imaged
events in the `σ`-imaged root over `linksT` equals counting the originals over `linksS`: each event's `linksT`
root is the `σ`-image of its `linksS` root (`hRoot`), so the `==` guard transports by `beq_congr_inj`.  Structural
on the event list.  This is what makes the cup/cap COUNT fields fall out of the proven `rootComm` — the cap's
component MERGE redistributes counts, but the redistribution is the SAME (up to `σ`) on both states, so the
per-root relation is invariant.  (Companion to `countEventsInRoot_rename`, but with `linksT` GENERAL — related to
`linksS` only by the automorphism, not by `renameLinks`, which is exactly the order-insensitive content.) -/
theorem countEventsInRoot_rootComm (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b)
    (linksS linksT : List (Nat × Nat)) (rootHere : Nat)
    (hRoot : ∀ x, unionFindRootOf linksT (sigma x) = sigma (unionFindRootOf linksS x)) :
    (events : List Nat) →
    countEventsInRoot linksT (sigma rootHere) (events.map sigma) = countEventsInRoot linksS rootHere events
  | [] => rfl
  | eventNode :: rest => by
      show (if unionFindRootOf linksT (sigma eventNode) == sigma rootHere then 1 else 0)
            + countEventsInRoot linksT (sigma rootHere) (rest.map sigma)
         = (if unionFindRootOf linksS eventNode == rootHere then 1 else 0)
            + countEventsInRoot linksS rootHere rest
      rw [hRoot eventNode, beq_congr_inj sigma inj,
        countEventsInRoot_rootComm sigma inj linksS linksT rootHere hRoot rest]

/-- One arc step changes `nextFresh` by an amount depending only on the atom (cup `+3`, cap `+1`, box `+codLen`),
so equal `nextFresh` is preserved by a common step.  By the three arms. -/
theorem stepArcAtom_nextFresh_eq {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (stateS stateT : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (nfEq : stateS.nextFresh = stateT.nextFresh) :
    (stepArcAtom stateS atom).nextFresh = (stepArcAtom stateT atom).nextFresh := by
  unfold stepArcAtom
  split
  · show stateS.nextFresh + 3 = stateT.nextFresh + 3; rw [nfEq]
  · show stateS.nextFresh + 1 = stateT.nextFresh + 1; rw [nfEq]
  · show stateS.nextFresh + atom.generatorCod.length = stateT.nextFresh + atom.generatorCod.length; rw [nfEq]

/-- ★ **`bnodeCorr` step-preservation (residual a), at the list level.**  The open-wire list of a step is a function
of the input open wires, `nextFresh`, and the atom ALONE (not the links), so if the two states' open wires are
pointwise `σ`-images (`stateT.openWires = stateS.openWires.map σ`) and `nextFresh` agrees with `σ` fixing the
future tail, the post-step open wires are again `σ`-images.  Cup: the splice `natListInsertAt` commutes
(`natListInsertAt_map`), the two fresh legs fixed (`nf, nf+1`).  Cap: the drop `natListRemoveTwoAt` commutes.  Box:
the input-dropping fold commutes (`droppedWires_map`) and the fresh output block is fixed (`mapFixedAbove`). -/
theorem stepArcAtom_openWires_map {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (stateS stateT : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (openMap : stateT.openWires = stateS.openWires.map sigma)
    (nfEq : stateS.nextFresh = stateT.nextFresh)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier) :
    (stepArcAtom stateT atom).openWires = (stepArcAtom stateS atom).openWires.map sigma := by
  have hleg0 : sigma stateS.nextFresh = stateT.nextFresh := by rw [fixesAbove _ (Nat.le_refl _), nfEq]
  have hleg1 : sigma (stateS.nextFresh + 1) = stateT.nextFresh + 1 := by
    rw [fixesAbove _ (Nat.le_add_right _ _), nfEq]
  unfold stepArcAtom
  split
  · show natListInsertAt stateT.openWires (atom.leftContext.length) [stateT.nextFresh, stateT.nextFresh + 1]
       = (natListInsertAt stateS.openWires (atom.leftContext.length) [stateS.nextFresh, stateS.nextFresh + 1]).map
          sigma
    rw [natListInsertAt_map]
    show natListInsertAt stateT.openWires (atom.leftContext.length) [stateT.nextFresh, stateT.nextFresh + 1]
       = natListInsertAt (stateS.openWires.map sigma) (atom.leftContext.length)
          [sigma stateS.nextFresh, sigma (stateS.nextFresh + 1)]
    rw [← openMap, hleg0, hleg1]
  · show natListRemoveTwoAt stateT.openWires (atom.leftContext.length)
       = (natListRemoveTwoAt stateS.openWires (atom.leftContext.length)).map sigma
    rw [natListRemoveTwoAt_map, ← openMap]
  · have hblk : ((List.range atom.generatorCod.length).map (· + stateS.nextFresh)).map sigma
          = (List.range atom.generatorCod.length).map (· + stateT.nextFresh) := by
      rw [mapFixedAbove sigma stateS.nextFresh fixesAbove _ (mem_mapAdd_ge stateS.nextFresh _)]
      exact congrArg (fun base => (List.range atom.generatorCod.length).map (· + base)) nfEq
    show natListInsertAt
          (Nat.rec stateT.openWires (fun _ shorter => natListRemoveTwoAt shorter atom.leftContext.length)
            atom.generatorDom.length)
          atom.leftContext.length ((List.range atom.generatorCod.length).map (· + stateT.nextFresh))
       = (natListInsertAt
            (Nat.rec stateS.openWires (fun _ shorter => natListRemoveTwoAt shorter atom.leftContext.length)
              atom.generatorDom.length)
            atom.leftContext.length ((List.range atom.generatorCod.length).map (· + stateS.nextFresh))).map sigma
    rw [natListInsertAt_map, droppedWires_map, hblk, openMap]

/-- ★ **The cup-event list is step-preserved as a `σ`-image.**  A cup conses `nf+2` (fixed by `σ`), a cap / box
leave the cup list untouched.  By the three arms. -/
theorem stepArcAtom_cupEventNodes_map {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (stateS stateT : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (cupMap : stateT.cupEventNodes = stateS.cupEventNodes.map sigma)
    (nfEq : stateS.nextFresh = stateT.nextFresh)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier) :
    (stepArcAtom stateT atom).cupEventNodes = (stepArcAtom stateS atom).cupEventNodes.map sigma := by
  have hleg2 : sigma (stateS.nextFresh + 2) = stateT.nextFresh + 2 := by
    rw [fixesAbove _ (Nat.le_add_right _ _), nfEq]
  unfold stepArcAtom
  split
  · show (stateT.nextFresh + 2) :: stateT.cupEventNodes
       = sigma (stateS.nextFresh + 2) :: stateS.cupEventNodes.map sigma
    rw [hleg2, cupMap]
  · exact cupMap
  · exact cupMap

/-- ★ **The cap-event list is step-preserved as a `σ`-image.**  A cap conses `nf` (fixed by `σ`), a cup / box leave
the cap list untouched.  By the three arms. -/
theorem stepArcAtom_capEventNodes_map {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (stateS stateT : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (capMap : stateT.capEventNodes = stateS.capEventNodes.map sigma)
    (nfEq : stateS.nextFresh = stateT.nextFresh)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier) :
    (stepArcAtom stateT atom).capEventNodes = (stepArcAtom stateS atom).capEventNodes.map sigma := by
  have hleg0 : sigma stateS.nextFresh = stateT.nextFresh := by rw [fixesAbove _ (Nat.le_refl _), nfEq]
  unfold stepArcAtom
  split
  · exact capMap
  · show stateT.nextFresh :: stateT.capEventNodes = sigma stateS.nextFresh :: stateS.capEventNodes.map sigma
    rw [hleg0, capMap]
  · exact capMap

/-- ★ **`rootComm` step-preservation (the proven hard core, dispatched).**  The union-find automorphism property is
carried across a common step: cup via `stepCupArc_rootComm`, cap via `stepCapArc_rootComm` (its read-wire
correspondences supplied by the open-wire `σ`-image via `natListGetAt_map`), box leaves `links` untouched. -/
theorem stepArcAtom_rootComm {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0)
    (stateS stateT : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (forestS : isUnionFindForest stateS.links) (forestT : isUnionFindForest stateT.links)
    (nfEq : stateS.nextFresh = stateT.nextFresh)
    (openMap : stateT.openWires = stateS.openWires.map sigma)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (hRoot : ∀ x, unionFindRootOf stateT.links (sigma x) = sigma (unionFindRootOf stateS.links x)) :
    ∀ x, unionFindRootOf (stepArcAtom stateT atom).links (sigma x)
      = sigma (unionFindRootOf (stepArcAtom stateS atom).links x) := by
  intro x
  unfold stepArcAtom
  split
  · exact stepCupArc_rootComm sigma inj stateS stateT forestS forestT nfEq fixesAbove hRoot
      (atom.leftContext.length) (atom.leftContext.length) x
  · have hleftCorr : natListGetAt stateT.openWires (atom.leftContext.length)
        = sigma (natListGetAt stateS.openWires (atom.leftContext.length)) := by
      rw [openMap, natListGetAt_map sigma sigmaFixesZero]
    have hrightCorr : natListGetAt stateT.openWires (atom.leftContext.length + 1)
        = sigma (natListGetAt stateS.openWires (atom.leftContext.length + 1)) := by
      rw [openMap, natListGetAt_map sigma sigmaFixesZero]
    exact stepCapArc_rootComm sigma inj stateS stateT forestS forestT nfEq fixesAbove hRoot
      (atom.leftContext.length) hleftCorr hrightCorr x
  · exact hRoot x

/-! ## The bundled single-step simulation invariant -/

/-- ★ **The single-step `ArcRenameRel` simulation invariant.**  The order-INSENSITIVE data preserved by a common
arc step on a `σ`-renaming-related pair of states: the open wires / cup-event / cap-event lists are pointwise
`σ`-images, `nextFresh` is shared, `loops` agree, `σ` is a union-find AUTOMORPHISM (`rootComm`), and both link lists
are forests (the acyclicity the automorphism reasoning rests on).  Strictly stronger than `ArcRenameRel` (the LIST
images give the pointwise `bnodeCorr`/count fields), and — unlike raw `renameState` equality — preserved by the
fold, because it never reads the link/event lists POSITIONALLY. -/
structure ArcStepSim (sigma : Nat → Nat) (stateS stateT : ArcWireState) : Prop where
  /-- The open wires are pointwise `σ`-images. -/
  openMap : stateT.openWires = stateS.openWires.map sigma
  /-- The fresh-allocation counters agree (the two run orders allocate the same TOTAL count). -/
  nfEq : stateS.nextFresh = stateT.nextFresh
  /-- `σ` is a union-find automorphism. -/
  rootComm : ∀ x, unionFindRootOf stateT.links (sigma x) = sigma (unionFindRootOf stateS.links x)
  /-- The loop counts agree. -/
  loopsEq : stateT.loops = stateS.loops
  /-- The cup-event lists are pointwise `σ`-images. -/
  cupMap : stateT.cupEventNodes = stateS.cupEventNodes.map sigma
  /-- The cap-event lists are pointwise `σ`-images. -/
  capMap : stateT.capEventNodes = stateS.capEventNodes.map sigma
  /-- The source links form a forest. -/
  forestS : isUnionFindForest stateS.links
  /-- The target links form a forest. -/
  forestT : isUnionFindForest stateT.links

/-- ★ **The simulation invariant is preserved by a common arc step** — the seven-field bundle.  `openMap` via
`stepArcAtom_openWires_map` (residual a), `nfEq` via `stepArcAtom_nextFresh_eq`, `rootComm` via
`stepArcAtom_rootComm` (the proven automorphism transport), `loopsEq` via `stepArcAtom_loopsEq`, `cupMap`/`capMap`
via the event-list lemmas, the two forests via `isUnionFindForest_stepArcAtom`.  `fixesAbove` is passed for the
fresh-leg correspondences; the open-wire `σ`-image supplies the cap read-wire / loop-test correspondences. -/
theorem arcStepSim_step {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0)
    (stateS stateT : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (sim : ArcStepSim sigma stateS stateT) :
    ArcStepSim sigma (stepArcAtom stateS atom) (stepArcAtom stateT atom) where
  openMap := stepArcAtom_openWires_map sigma stateS stateT atom sim.openMap sim.nfEq fixesAbove
  nfEq := stepArcAtom_nextFresh_eq stateS stateT atom sim.nfEq
  rootComm := stepArcAtom_rootComm sigma inj sigmaFixesZero stateS stateT atom sim.forestS sim.forestT sim.nfEq
    sim.openMap fixesAbove sim.rootComm
  loopsEq := stepArcAtom_loopsEq sigma inj stateS stateT atom sim.rootComm
    (fun index => by rw [sim.openMap, natListGetAt_map sigma sigmaFixesZero stateS.openWires index]) sim.loopsEq
  cupMap := stepArcAtom_cupEventNodes_map sigma stateS stateT atom sim.cupMap sim.nfEq fixesAbove
  capMap := stepArcAtom_capEventNodes_map sigma stateS stateT atom sim.capMap sim.nfEq fixesAbove
  forestS := isUnionFindForest_stepArcAtom stateS atom sim.forestS
  forestT := isUnionFindForest_stepArcAtom stateT atom sim.forestT

/-- ★ **The simulation invariant folds over a whole spine** — structural recursion on the atoms, threading the
strengthened `fixesAbove` (the fixed range only shrinks as `nextFresh` grows, `stepArcAtom_nextFresh_le`). -/
theorem arcStepSim_processArcSpine {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0) :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (stateS stateT : ArcWireState) →
    (∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier) →
    ArcStepSim sigma stateS stateT →
    ArcStepSim sigma (processArcSpine stateS atoms) (processArcSpine stateT atoms)
  | [], _, _, _, sim => sim
  | atom :: rest, stateS, stateT, fixesAbove, sim => by
      show ArcStepSim sigma (processArcSpine (stepArcAtom stateS atom) rest)
        (processArcSpine (stepArcAtom stateT atom) rest)
      exact arcStepSim_processArcSpine sigma inj sigmaFixesZero rest (stepArcAtom stateS atom)
        (stepArcAtom stateT atom)
        (fun identifier idAtLeast =>
          fixesAbove identifier (Nat.le_trans (stepArcAtom_nextFresh_le stateS atom) idAtLeast))
        (arcStepSim_step sigma inj sigmaFixesZero stateS stateT atom fixesAbove sim)

/-- ★ **The simulation invariant survives running one cell** — the spine fold over `cell.spineDiff`. -/
theorem arcStepSim_runArcCell {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0)
    (stateS stateT : ArcWireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (sim : ArcStepSim sigma stateS stateT) :
    ArcStepSim sigma (runArcCell stateS leftAcc rightAcc cell) (runArcCell stateT leftAcc rightAcc cell) :=
  arcStepSim_processArcSpine sigma inj sigmaFixesZero (cell.spineDiff leftAcc rightAcc []) stateS stateT
    fixesAbove sim

/-- ★ **The simulation invariant yields the full `ArcRenameRel` — all SEVEN fields discharged.**  `lengthEq` from
the open-wire `σ`-image (`mapLength`), `loopsEq`/`inj`/`rootComm` straight from the invariant, `bnodeCorr` from the
open-wire image plus the boundary-fixing (`boundaryNodesOf` is `range ++ openWires`, the prefix fixed,
`natListGetAt_map`), and the two per-root COUNT fields from `countEventsInRoot_rootComm` + the event-list images.
This is the seven-field bundle: with `arcStepSim_step`/`_runArcCell` showing the invariant is step-stable, the whole
`ArcRenameRel` transports across any common suffix. -/
theorem arcRenameRel_of_arcStepSim (bottomCount : Nat) (sigma : Nat → Nat)
    (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0)
    (fixesBoundary : ∀ identifier, identifier < bottomCount → sigma identifier = identifier)
    (stateS stateT : ArcWireState) (sim : ArcStepSim sigma stateS stateT) :
    ArcRenameRel bottomCount sigma stateS stateT where
  lengthEq := by rw [sim.openMap, mapLength]
  loopsEq := sim.loopsEq
  inj := inj
  bnodeCorr := by
    intro i _
    have hbnd : boundaryNodesOf bottomCount stateT = (boundaryNodesOf bottomCount stateS).map sigma := by
      show List.range bottomCount ++ stateT.openWires = (List.range bottomCount ++ stateS.openWires).map sigma
      rw [sim.openMap, mapAppend, mapFixedOn sigma (List.range bottomCount)
        (fun identifier identifierInRange => fixesBoundary identifier (mem_range_imp_lt identifierInRange))]
    rw [hbnd, natListGetAt_map sigma sigmaFixesZero]
  rootComm := sim.rootComm
  cupCorr := by
    intro rootNode
    rw [sim.cupMap]
    exact countEventsInRoot_rootComm sigma inj stateS.links stateT.links rootNode sim.rootComm
      stateS.cupEventNodes
  capCorr := by
    intro rootNode
    rw [sim.capMap]
    exact countEventsInRoot_rootComm sigma inj stateS.links stateT.links rootNode sim.rootComm
      stateS.capEventNodes

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

/-- **Honesty marker — the union-find AUTOMORPHISM transport is proved (the heart of the direct route).**
`rootComm_unionFindJoin` shows the `ArcRenameRel.rootComm` field — `σ` is a union-find automorphism — is PRESERVED
when both states perform a `σ`-corresponding join, and `stepCupArc_rootComm` / `stepCapArc_rootComm` carry it
across a whole cup / cap step (two corresponding joins, the cap conditioned on the read wires corresponding).  This
is exactly the order-INSENSITIVE content the refuted `renameState`-equality core swap could not express: the link
lists come out permuted, but the ROOT structure is `σ`-isomorphic.  Built on `unionFindRootOf_unionFindJoin` (root
after a join as a guard on pre-join roots), `beq_congr_inj`, and `ite_push_sigma`, all zero-axiom.  `= true`. -/
def fxMode_hasArcRootCommAutomorphismTransport : Bool := true

/-- **Honesty marker — the structural `ArcRenameRel` fields are preserved by a step.**  `stepArcAtom_lengthEq`
(open-wire count, id-free via the insert/remove length lemmas) and `stepArcAtom_loopsEq` (loop count: cup / box
no-op, cap same-component test agreeing under `σ`) preserve the renaming-invariant counts across a cup / cap / box
step.  Together with `rootComm` (above) and `inj` (the renaming is fixed), four of `ArcRenameRel`'s seven fields
are step-stable.  `= true`. -/
def fxMode_hasArcStepStructuralFieldsPreserved : Bool := true

/-- **Honesty marker — freshness is a fold invariant.**  `stepArcAtom_arcStateFresh` /
`processArcSpine_arcStateFresh` / `runArcCell_arcStateFresh` prove `ArcStateFresh` (every mentioned id `<
nextFresh`) is preserved by every cup / cap / box step and the whole fold — the locality anchor that makes
freshly-allocated legs parentless and old nodes' roots stay below `nextFresh`, the side conditions the `rootComm`
transport consumes.  `= true`. -/
def fxMode_hasArcFoldFreshnessInvariant : Bool := true

/-- **Honesty marker — the LIVE `ArcRenameRel`-level core obligation is stated.**  `ArcGodementCoreSwapRenameRel`
replaces the refuted `renameState`-equality core swap with the genuine independence at the `ArcRenameRel` level
(boundary-correspondence / root-commutation / per-root counts — all order-INSENSITIVE), plus the future-tail
`σ`-fixing that lets the common suffix transport.  This is the reduction target the parent collapses to once the
single-step simulation peels the suffix; its `rootComm` / `lengthEq` / `loopsEq` fields are proven, leaving the
boundary-correspondence and per-root-count fields plus the explicit block-swap `σ`.  `= true`. -/
def fxMode_hasArcCoreSwapRenameRelStated : Bool := true

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

The live route — building `ArcRenameRel` between the two run orders DIRECTLY — is now under construction here, as a
single-step SIMULATION (a common arc step preserves `ArcRenameRel` via the SAME `σ`, so the common suffix peels at
the renaming level).  Of `ArcRenameRel`'s seven fields, FOUR are step-preserved zero-axiom:
  · `inj` — the renaming is fixed;
  · `lengthEq` — `stepArcAtom_lengthEq` (id-free);
  · `loopsEq` — `stepArcAtom_loopsEq` (cap same-component test transports);
  · `rootComm` — `stepCupArc_rootComm` / `stepCapArc_rootComm`, via the union-find AUTOMORPHISM transport
    `rootComm_unionFindJoin` — the mathematical heart (and exactly what `renameState` equality could not express).
The supporting fold invariants (FRESHNESS `*_arcStateFresh`, the FOREST/acyclicity `isUnionFindForest_*`, the
unifying root lemma `unionFindRootOf_unionFindJoin`) are all proven.

The PRECISE RESIDUAL (the standing obligation, keeping this marker `false`):
  (a) `bnodeCorr` step-preservation — the open wires correspond pointwise after the `natListInsertAt` /
      `natListRemoveTwoAt` of a step (index bookkeeping; supplies the cap read-wire correspondence the `rootComm` /
      `loopsEq` transports consume);
  (b) `cupCorr` step-preservation — the per-root cup-event count transports (the cup creates an ISOLATED fresh
      component, so old roots are unchanged: a count-congruence over `countEventsInRoot_congr_links`);
  (c) `capCorr` step-preservation — the per-root cap-event count transports across the cap's component MERGE (the
      genuine hard core: the merge redistributes counts, `f(rRw) ↦ f(rLw)+f(rRw)`, transported under `σ`);
  (d) assembling (a)–(c) with the proven four into the full single-step simulation, folding it over the
      `cellBetaUpper`-then-`rest` suffix, and exhibiting the explicit block-swap `σ` (permuting the two disjoint
      fresh ranges) to discharge `ArcGodementCoreSwapRenameRel` — whence `ArcGodementSwapRenameable`.
The orchestrator must NOT flip the parent's `fxMode_hasArcGodementSwapRenameableProof` on the basis of this file.
`= false`. -/
def fxMode_hasArcGodementSwapRenameableProof2 : Bool := false

end FX1Poly.Tier0
