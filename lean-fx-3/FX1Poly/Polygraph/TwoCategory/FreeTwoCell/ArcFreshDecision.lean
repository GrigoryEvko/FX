import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute

/-! # mode-3 floor — the FRESHNESS-gated arc-soundness plumbing (closing the consumer's `godementInvariant`)

`FreeTwoCellArcPartitionCommute` proved (zero-axiom) that the UN-conditioned Godement arc residual
`ArcGodementSamePartition` is FALSE (`not_arcGodementSamePartition`): it quantifies over EVERY `ArcWireState`,
including adversarial ones whose `links` / `openWires` name node ids `≥ nextFresh`, where the two Godement run
orders allocate their fresh cup/cap legs into SWAPPED id ranges and the boundary partition diverges.  The
corrected, TRUE residual is `ArcGodementSamePartitionFresh`, conditioned on `ArcStateFresh state` and
`bottomCount ≤ state.nextFresh` — the reachable-state invariant the actual fold maintains.

The CONSUMER chain (`decidableTwoCellConvFull_of`, `arcStructureOf_sound_of_godementInvariant`,
`arcTraceInvariant_of_godementInvariant` in `FreeTwoCellSpineTraceDecision`) demands the un-conditioned
`∀ state` `godementInvariant` — which is false.  This file supplies the FRESHNESS-GATED soundness path so the
consumer is satisfiable from the actual reachable (always-fresh) states:

  ★ `arcStateFresh_stepArcAtom` — **one fold step preserves freshness**.  A cup allocates its two legs and event
    node at `nextFresh … nextFresh+2` and bumps `nextFresh` to `+3`; a cap allocates one event node at `nextFresh`
    and bumps to `+1`; a generic box allocates its outputs at `nextFresh … nextFresh+numProduced-1` and bumps to
    `+numProduced`.  Every branch keeps every mentioned id strictly below the new `nextFresh` — the union-find
    roots the join introduces are reached through parent edges (themselves `< nextFresh`), so they too stay below.

  ★ `arcStateFresh_processArcSpine` — the fold of the above over a whole spine.

  ★ `godementInvariantFresh_of_samePartitionFresh` — the **freshness-gated `godementInvariant`**: from
    `ArcGodementSamePartitionFresh` (taken as a HYPOTHESIS — its proof is leg B), the state-parametric Godement-step
    arc-extract invariance holds for every FRESH state with `bottomCount ≤ nextFresh`.  The connectivity residual
    supplies the three partition fields via `extractArc_eq_of_sameArcPartition`; the cup/cap COUNT fields are the
    order-independent atom counts discharged exactly as the parent did (`Nat.add_right_comm`).

  ★ `arcTraceInvariantFresh` — `arcTraceInvariant_of_godementInvariant` re-proved THREADING freshness through the
    `consCongr` step (each `stepArcAtom` preserves freshness and never lowers `nextFresh`), so the freshness
    precondition is discharged automatically from the fresh-initial fold.

  ★ `arcStructureOf_sound_of_arcGodementSamePartitionFresh` — the assembled soundness: `arcStructureOf` is invariant
    under the COMPLETE `TwoCellConvFull`, gated on `ArcGodementSamePartitionFresh` alone, because the real decision
    always folds from `arcStateFresh_initial` (whose `nextFresh = bottomCount`).

  ★ `decidableTwoCellConvFull_of_fresh` — the FRESHNESS-gated decision corollary: it takes
    `ArcGodementSamePartitionFresh signature` (+ the reconstruction the existing `decidableTwoCellConvFull_of`
    already takes) and yields `Decidable (TwoCellConvFull …)`.  Discharging the ONE true lemma
    `ArcGodementSamePartitionFresh` (leg B) closes the soundness side.

This is the freshness-PLUMBING (preservation lemmas + the reduction to the hypothesis): fully provable now.  We do
NOT prove `ArcGodementSamePartitionFresh` itself (that is leg B).

Raw Lean 4 + Init; the list / union-find membership-and-bound helpers are structural recursion (the messy
multi-argument matches reduced via their equation lemmas `simp only [fn]`, the Bool-`if` of `unionFindParent` /
`unionFindJoin` cased via `cases h : _ == _` then `rw [h]`); the dispatch is `split` over `stepArcAtom`'s arity
match; the reductions reuse the parent's count machinery + `Nat.add_right_comm`.  No `omega`, no `simp`-AC, no
`List.append` lemmas, no `WellFounded.fix`, no `decide` on open terms.  Per-declaration `#assert_no_axioms` gated
in the audit twin. -/

namespace FX1Poly.Tier0

/-! ## `propext`-free list / union-find membership and bound helpers

Lean core's `List.mem_append` / `List.mem_map` / `List.mem_range` are iff lemmas that depend on `propext`; the
messy `natListRemoveTwoAt` / `natListInsertAt` / `unionFindParent` matches do not reduce per-arm by `rfl` (curried
multi-argument matches compile to non-reducing recursors), so each is reduced through its generated equation lemma
via `simp only [fn] at _`, then the membership decomposed by `List.Mem` constructor casing. -/

/-- A member of `block ++ rest` is a member of `block` or of `rest`.  Structural recursion on `block`, casing the
cons-membership by its `List.Mem` constructors — `propext`-free (no `List.mem_append`). -/
theorem mem_append_imp {target : Nat} :
    (block rest : List Nat) → target ∈ block ++ rest → target ∈ block ∨ target ∈ rest
  | [], _, membership => Or.inr membership
  | _ :: tail, rest, membership => by
      cases membership with
      | head => exact Or.inl (List.Mem.head _)
      | tail _ tailMem =>
          cases mem_append_imp tail rest tailMem with
          | inl inBlock => exact Or.inl (List.Mem.tail _ inBlock)
          | inr inRest => exact Or.inr inRest

/-- A member of `natListInsertAt wires position block` is a member of `wires` or of the spliced `block`.  Reduces
each arm via the equation lemma `simp only [natListInsertAt]`, then decomposes (`mem_append_imp` at position 0,
`List.Mem` casing under the cons recursion). -/
theorem mem_natListInsertAt_imp {target : Nat} :
    (wires : List Nat) → (position : Nat) → (block : List Nat) →
    target ∈ natListInsertAt wires position block → target ∈ wires ∨ target ∈ block
  | _, 0, block, membership => by
      simp only [natListInsertAt] at membership
      cases mem_append_imp block _ membership with
      | inl inBlock => exact Or.inr inBlock
      | inr inWires => exact Or.inl inWires
  | [], _ + 1, block, membership => Or.inr membership
  | _ :: rest, position + 1, block, membership => by
      simp only [natListInsertAt] at membership
      cases membership with
      | head => exact Or.inl (List.Mem.head _)
      | tail _ tailMem =>
          cases mem_natListInsertAt_imp rest position block tailMem with
          | inl inRest => exact Or.inl (List.Mem.tail _ inRest)
          | inr inBlock => exact Or.inr inBlock

/-- A member of `natListRemoveTwoAt wires position` is a member of `wires` (removal only drops elements).  The
arms reduce via `simp only [natListRemoveTwoAt]`; the `position+1` case recurses, the others re-inject by
`List.Mem.tail`. -/
theorem mem_natListRemoveTwoAt_imp {target : Nat} :
    (wires : List Nat) → (position : Nat) →
    target ∈ natListRemoveTwoAt wires position → target ∈ wires
  | [], _, membership => membership
  | _ :: _ :: _, 0, membership => by
      simp only [natListRemoveTwoAt] at membership
      exact List.Mem.tail _ (List.Mem.tail _ membership)
  | [_], 0, membership => membership
  | _ :: rest, position + 1, membership => by
      simp only [natListRemoveTwoAt] at membership
      cases membership with
      | head => exact List.Mem.head _
      | tail _ tailMem => exact List.Mem.tail _ (mem_natListRemoveTwoAt_imp rest position tailMem)

/-- `natListGetAt wires position` is either a member of `wires` or the `0` default (past the end).  Structural
recursion on the position / list — `propext`-free. -/
theorem natListGetAt_mem_or_zero :
    (wires : List Nat) → (position : Nat) →
    natListGetAt wires position ∈ wires ∨ natListGetAt wires position = 0
  | [], _ => Or.inr rfl
  | _ :: _, 0 => Or.inl (List.Mem.head _)
  | _ :: rest, position + 1 => by
      cases natListGetAt_mem_or_zero rest position with
      | inl inRest => exact Or.inl (List.Mem.tail _ inRest)
      | inr isZero => exact Or.inr isZero

/-- A member of `elems.map mapFn` is `mapFn source` for some `source ∈ elems`.  Structural recursion on `elems`
(equation lemma `simp only [List.map]`), `propext`-free (no `List.mem_map`). -/
theorem mem_map_imp {target : Nat} (mapFn : Nat → Nat) :
    (elems : List Nat) → target ∈ elems.map mapFn → ∃ source, source ∈ elems ∧ target = mapFn source
  | [], membership => by simp only [List.map] at membership; nomatch membership
  | head :: tail, membership => by
      simp only [List.map] at membership
      cases membership with
      | head => exact ⟨head, List.Mem.head _, rfl⟩
      | tail _ tailMem =>
          obtain ⟨source, sourceMem, sourceEq⟩ := mem_map_imp mapFn tail tailMem
          exact ⟨source, List.Mem.tail _ sourceMem, sourceEq⟩

/-- A member of the `numConsumed`-fold of `natListRemoveTwoAt _ position` over `baseWires` is a member of
`baseWires`.  Structural recursion on the fold count, each step via `mem_natListRemoveTwoAt_imp`. -/
theorem mem_iterRemoveTwoAt {target : Nat} (position : Nat) (baseWires : List Nat) (numConsumed : Nat) :
    target ∈ Nat.rec (motive := fun _ => List Nat) baseWires
        (fun _ shorter => natListRemoveTwoAt shorter position) numConsumed →
    target ∈ baseWires := by
  induction numConsumed with
  | zero => intro membership; exact membership
  | succ _ inductionHypothesis =>
      intro membership; exact inductionHypothesis (mem_natListRemoveTwoAt_imp _ position membership)

/-- `unionFindParent links node = some parent` forces `parent` to be the parent endpoint (`.2`) of some edge in
`links`.  Structural recursion on `links`, the head `if child == node` cased via `cases h : child == node` then
`rw [h]` (the Bool-`if` reduces definitionally once the condition is `true`/`false`) — `propext`-free. -/
theorem unionFindParent_mem :
    (links : List (Nat × Nat)) → (node parent : Nat) →
    unionFindParent links node = some parent → ∃ edge, edge ∈ links ∧ edge.2 = parent
  | [], _, _, membership => by
      simp only [unionFindParent] at membership
      nomatch membership
  | (child, par) :: rest, node, parent, membership => by
      unfold unionFindParent at membership
      cases hbeq : child == node with
      | true =>
          rw [hbeq] at membership
          exact ⟨(child, par), List.Mem.head _, Option.some.inj membership⟩
      | false =>
          rw [hbeq] at membership
          obtain ⟨edge, edgeMem, edgeSnd⟩ := unionFindParent_mem rest node parent membership
          exact ⟨edge, List.Mem.tail _ edgeMem, edgeSnd⟩

/-- The union-find root of an in-bound node stays in bound: following parent edges (each parent `< bound` by edge
boundedness) never leaves `[0, bound)`.  Structural recursion on the fuel, the parent step via
`unionFindParent_mem`. -/
theorem unionFindRoot_lt (bound : Nat) (links : List (Nat × Nat))
    (edgesBounded : ∀ edge ∈ links, edge.2 < bound) :
    (fuel node : Nat) → node < bound → unionFindRoot fuel links node < bound
  | 0, _, nodeBelow => nodeBelow
  | fuel + 1, node, nodeBelow => by
      unfold unionFindRoot
      cases hparent : unionFindParent links node with
      | none => exact nodeBelow
      | some parent =>
          obtain ⟨edge, edgeMem, edgeSnd⟩ := unionFindParent_mem links node parent hparent
          have parentBelow : parent < bound := by rw [← edgeSnd]; exact edgesBounded edge edgeMem
          exact unionFindRoot_lt bound links edgesBounded fuel parent parentBelow

/-- The fuel-sized root of an in-bound node stays in bound. -/
theorem unionFindRootOf_lt (bound : Nat) (links : List (Nat × Nat))
    (edgesBounded : ∀ edge ∈ links, edge.2 < bound) (node : Nat) (nodeBelow : node < bound) :
    unionFindRootOf links node < bound :=
  unionFindRoot_lt bound links edgesBounded (links.length + 1) node nodeBelow

/-- Joining two in-bound nodes keeps every edge endpoint in bound: the no-op branch returns `links`; the joining
branch prepends `(root firstNode, root secondNode)`, both roots in bound by `unionFindRootOf_lt`.  The Bool-`if`
of `unionFindJoin` is cased via `cases h : root == root` then `rw [h]`. -/
theorem unionFindJoin_edges_lt (bound : Nat) (links : List (Nat × Nat))
    (edgesBounded : ∀ edge ∈ links, edge.1 < bound ∧ edge.2 < bound)
    (firstNode secondNode : Nat) (firstBelow : firstNode < bound) (secondBelow : secondNode < bound) :
    ∀ edge ∈ unionFindJoin links firstNode secondNode, edge.1 < bound ∧ edge.2 < bound := by
  intro edge edgeMem
  simp only [unionFindJoin] at edgeMem
  cases hcmp : unionFindRootOf links firstNode == unionFindRootOf links secondNode with
  | true => rw [hcmp] at edgeMem; exact edgesBounded edge edgeMem
  | false =>
      rw [hcmp] at edgeMem
      cases edgeMem with
      | head =>
          exact ⟨unionFindRootOf_lt bound links (fun e he => (edgesBounded e he).2) firstNode firstBelow,
                 unionFindRootOf_lt bound links (fun e he => (edgesBounded e he).2) secondNode secondBelow⟩
      | tail _ tailMem => exact edgesBounded edge tailMem

/-- `x < bound → x < bound + slack` — the workhorse for re-basing a freshness bound past an allocation bump. -/
theorem lt_add_right_of_lt {target bound : Nat} (targetBelow : target < bound) (slack : Nat) :
    target < bound + slack :=
  Nat.lt_of_lt_of_le targetBelow (Nat.le_add_right bound slack)

/-! ## Freshness preservation per fold-step branch -/

/-- A CUP step preserves freshness.  New `nextFresh = old + 3`: the two legs `old, old+1` and the event node
`old+2` are all `< old+3`; the union-find joins introduce edges whose endpoints are the in-bound roots
(`unionFindJoin_edges_lt`, twice); the old open wires / links / events were `< old ≤ old+3`. -/
theorem arcStateFresh_stepCupArc (state : ArcWireState) (position : Nat)
    (hFresh : ArcStateFresh state) : ArcStateFresh (stepCupArc state position) := by
  obtain ⟨hWires, hLinks, hCup, hCap⟩ := hFresh
  unfold stepCupArc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro wire wireMem
    cases mem_natListInsertAt_imp _ position [state.nextFresh, state.nextFresh + 1] wireMem with
    | inl inOld => exact lt_add_right_of_lt (hWires wire inOld) 3
    | inr inNew =>
        cases inNew with
        | head => exact Nat.lt_add_of_pos_right (by decide)
        | tail _ tailMem =>
            cases tailMem with
            | head => exact Nat.add_lt_add_left (by decide) state.nextFresh
            | tail _ emptyMem => nomatch emptyMem
  · intro edge edgeMem
    refine unionFindJoin_edges_lt (state.nextFresh + 3) _ ?_ (state.nextFresh + 2) state.nextFresh
      (Nat.add_lt_add_left (by decide) state.nextFresh) (Nat.lt_add_of_pos_right (by decide)) edge edgeMem
    refine unionFindJoin_edges_lt (state.nextFresh + 3) _ ?_ state.nextFresh (state.nextFresh + 1)
      (Nat.lt_add_of_pos_right (by decide)) (Nat.add_lt_add_left (by decide) state.nextFresh)
    intro e he
    exact ⟨lt_add_right_of_lt (hLinks e he).1 3, lt_add_right_of_lt (hLinks e he).2 3⟩
  · intro node nodeMem
    cases nodeMem with
    | head => exact Nat.add_lt_add_left (by decide) state.nextFresh
    | tail _ tailMem => exact lt_add_right_of_lt (hCup node tailMem) 3
  · intro node nodeMem
    exact lt_add_right_of_lt (hCap node nodeMem) 3

/-- A CAP step preserves freshness.  New `nextFresh = old + 1`: the event node is `old < old+1`; the two consumed
wires `leftWire`/`rightWire` are read by `natListGetAt`, hence either an old wire (`< old`) or the `0` default,
both `< old+1`; the union-find joins introduce in-bound-root edges; the surviving open wires are a removal-subset
of the old (`< old`). -/
theorem arcStateFresh_stepCapArc (state : ArcWireState) (position : Nat)
    (hFresh : ArcStateFresh state) : ArcStateFresh (stepCapArc state position) := by
  obtain ⟨hWires, hLinks, hCup, hCap⟩ := hFresh
  have leftBelow : natListGetAt state.openWires position < state.nextFresh + 1 := by
    cases natListGetAt_mem_or_zero state.openWires position with
    | inl inList => exact lt_add_right_of_lt (hWires _ inList) 1
    | inr isZero => rw [isZero]; exact Nat.zero_lt_succ _
  have rightBelow : natListGetAt state.openWires (position + 1) < state.nextFresh + 1 := by
    cases natListGetAt_mem_or_zero state.openWires (position + 1) with
    | inl inList => exact lt_add_right_of_lt (hWires _ inList) 1
    | inr isZero => rw [isZero]; exact Nat.zero_lt_succ _
  unfold stepCapArc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro wire wireMem
    exact lt_add_right_of_lt (hWires wire (mem_natListRemoveTwoAt_imp _ position wireMem)) 1
  · intro edge edgeMem
    refine unionFindJoin_edges_lt (state.nextFresh + 1) _ ?_ state.nextFresh
      (natListGetAt state.openWires position) (Nat.lt_succ_self _) leftBelow edge edgeMem
    refine unionFindJoin_edges_lt (state.nextFresh + 1) _ ?_
      (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1)) leftBelow rightBelow
    intro e he
    exact ⟨lt_add_right_of_lt (hLinks e he).1 1, lt_add_right_of_lt (hLinks e he).2 1⟩
  · intro node nodeMem
    exact lt_add_right_of_lt (hCup node nodeMem) 1
  · intro node nodeMem
    cases nodeMem with
    | head => exact Nat.lt_succ_self _
    | tail _ tailMem => exact lt_add_right_of_lt (hCap node tailMem) 1

/-- The generic-box step body (an opaque generator of arity `numConsumed ⇒ numProduced`), factored out of
`stepArcAtom`'s catch-all arm so its freshness preservation is a single lemma.  Drops `numConsumed` input wires,
adds `numProduced` disconnected fresh outputs at `nextFresh … nextFresh+numProduced-1`, records no arc event. -/
def arcBoxStep (state : ArcWireState) (position numConsumed numProduced : Nat) : ArcWireState :=
  { openWires := natListInsertAt
      (Nat.rec state.openWires (fun _ shorter => natListRemoveTwoAt shorter position) numConsumed)
      position ((List.range numProduced).map (· + state.nextFresh)),
    links := state.links,
    nextFresh := state.nextFresh + numProduced,
    loops := state.loops,
    cupEventNodes := state.cupEventNodes,
    capEventNodes := state.capEventNodes }

/-- The generic-box step preserves freshness.  New `nextFresh = old + numProduced`: the surviving open wires are a
removal-subset of the old (`< old`); the fresh outputs are `source + old` for `source < numProduced`
(`< old + numProduced`); links and event lists are untouched (`< old ≤ old + numProduced`). -/
theorem arcStateFresh_arcBoxStep (state : ArcWireState) (position numConsumed numProduced : Nat)
    (hFresh : ArcStateFresh state) : ArcStateFresh (arcBoxStep state position numConsumed numProduced) := by
  obtain ⟨hWires, hLinks, hCup, hCap⟩ := hFresh
  unfold arcBoxStep
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro wire wireMem
    cases mem_natListInsertAt_imp _ position ((List.range numProduced).map (· + state.nextFresh)) wireMem with
    | inl inDropped =>
        exact lt_add_right_of_lt
          (hWires wire (mem_iterRemoveTwoAt position state.openWires numConsumed inDropped)) numProduced
    | inr inRange =>
        obtain ⟨source, sourceMem, sourceEq⟩ :=
          mem_map_imp (· + state.nextFresh) (List.range numProduced) inRange
        rw [sourceEq, Nat.add_comm source state.nextFresh]
        exact Nat.add_lt_add_left (mem_range_imp_lt sourceMem) state.nextFresh
  · intro edge edgeMem
    exact ⟨lt_add_right_of_lt (hLinks edge edgeMem).1 numProduced,
           lt_add_right_of_lt (hLinks edge edgeMem).2 numProduced⟩
  · intro node nodeMem
    exact lt_add_right_of_lt (hCup node nodeMem) numProduced
  · intro node nodeMem
    exact lt_add_right_of_lt (hCap node nodeMem) numProduced

/-! ## The fold-step dispatch and its monotonicity -/

/-- One fold step never lowers `nextFresh` (cup `+3`, cap `+1`, box `+numProduced`).  By `split` on
`stepArcAtom`'s arity match. -/
theorem stepArcAtom_nextFresh_le {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode) :
    state.nextFresh ≤ (stepArcAtom state atom).nextFresh := by
  unfold stepArcAtom
  split
  · exact Nat.le_add_right state.nextFresh 3
  · exact Nat.le_add_right state.nextFresh 1
  · exact Nat.le_add_right state.nextFresh _

/-- ★ **One fold step preserves `ArcStateFresh`.**  Folding one atom from a fresh state yields a fresh state: the
cup / cap / generic-box branches each allocate their own legs at/after `nextFresh` and bump it past them.  By
`split` on `stepArcAtom`'s arity match into the three branch lemmas. -/
theorem arcStateFresh_stepArcAtom {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (hFresh : ArcStateFresh state) : ArcStateFresh (stepArcAtom state atom) := by
  unfold stepArcAtom
  split
  · exact arcStateFresh_stepCupArc state _ hFresh
  · exact arcStateFresh_stepCapArc state _ hFresh
  · exact arcStateFresh_arcBoxStep state _ _ _ hFresh

/-- ★ **The whole-spine fold preserves `ArcStateFresh`.**  Structural recursion on the spine, the head via
`arcStateFresh_stepArcAtom`. -/
theorem arcStateFresh_processArcSpine {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : ArcWireState) →
    ArcStateFresh state → ArcStateFresh (processArcSpine state atoms)
  | [], _, hFresh => hFresh
  | atom :: rest, state, hFresh => by
      show ArcStateFresh (processArcSpine (stepArcAtom state atom) rest)
      exact arcStateFresh_processArcSpine rest (stepArcAtom state atom)
        (arcStateFresh_stepArcAtom state atom hFresh)

/-! ## The freshness-gated Godement-step invariant, reduced to the hypothesis `ArcGodementSamePartitionFresh` -/

/-- ★ **The freshness-gated `godementInvariant`.**  From the hypothesis `ArcGodementSamePartitionFresh` (leg B),
the state-parametric Godement-step arc-extract invariance holds for every FRESH state with
`bottomCount ≤ nextFresh`.  By `cases` on the single `SpineGodementStep.godement` constructor + four
`processArcSpine_spineDiff` peels (`simp only`), both sides land on the two run-order states; the connectivity
residual supplies the three partition fields through `extractArc_eq_of_sameArcPartition`, and the cup/cap COUNT
fields are the order-independent atom counts (`processArcSpine_*EventNodes_length` + `runArcCell_*EventNodes_length`
transposed by `Nat.add_right_comm`).  This is exactly the `godementInvariant` shape `arcTraceInvariant…` consumes,
now gated on freshness + the one true residual. -/
theorem godementInvariantFresh_of_samePartitionFresh {signature : ModeSignature}
    (samePartitionFresh : ArcGodementSamePartitionFresh signature)
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat) (state : ArcWireState)
    (hFresh : ArcStateFresh state) (hBottomLe : bottomCount ≤ state.nextFresh)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (step : SpineGodementStep signature firstList secondList) :
    extractArcAfterProcessing bottomCount state firstList
      = extractArcAfterProcessing bottomCount state secondList := by
  cases step with
  | godement cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest =>
    simp only [extractArcAfterProcessing, processArcSpine_spineDiff]
    exact extractArc_eq_of_sameArcPartition bottomCount _ _
      (samePartitionFresh cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest bottomCount state
        hFresh hBottomLe)
      (by simp only [processArcSpine_cupEventNodes_length, runArcCell_cupEventNodes_length]
          rw [Nat.add_right_comm (state.cupEventNodes.length + cellAlpha.cupCount)
            cellAlphaUpper.cupCount cellBeta.cupCount])
      (by simp only [processArcSpine_capEventNodes_length, runArcCell_capEventNodes_length]
          rw [Nat.add_right_comm (state.capEventNodes.length + cellAlpha.capCount)
            cellAlphaUpper.capCount cellBeta.capCount])

/-! ## The freshness-threaded trace invariance and the assembled soundness -/

/-- ★ **`arcTraceInvariant_of_godementInvariant`, re-proved THREADING freshness.**  Given the freshness-gated
Godement-step invariance, the full `SpineTraceEquiv` arc-extract invariance holds from every fresh state with
`bottomCount ≤ nextFresh`.  The `consCongr` step advances the state through one `stepArcAtom`, which preserves
freshness (`arcStateFresh_stepArcAtom`) and never lowers `nextFresh` (`stepArcAtom_nextFresh_le`), so both
preconditions thread automatically. -/
theorem arcTraceInvariantFresh {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat)
    (godementInvariantFresh : ∀ (state : ArcWireState), ArcStateFresh state → bottomCount ≤ state.nextFresh →
        ∀ {firstList secondList : List (SpineAtom signature overallSource overallTarget)},
        SpineGodementStep signature firstList secondList →
        extractArcAfterProcessing bottomCount state firstList
          = extractArcAfterProcessing bottomCount state secondList)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (equiv : SpineTraceEquiv signature firstList secondList) :
    ∀ (state : ArcWireState), ArcStateFresh state → bottomCount ≤ state.nextFresh →
      extractArcAfterProcessing bottomCount state firstList
        = extractArcAfterProcessing bottomCount state secondList := by
  induction equiv with
  | ofStep step => intro state hFresh hLe; exact godementInvariantFresh state hFresh hLe step
  | refl _ => intro _ _ _; rfl
  | symm _ inductionHypothesis => intro state hFresh hLe; exact (inductionHypothesis state hFresh hLe).symm
  | trans _ _ firstHypothesis secondHypothesis =>
      intro state hFresh hLe; exact (firstHypothesis state hFresh hLe).trans (secondHypothesis state hFresh hLe)
  | consCongr atom _ inductionHypothesis =>
      intro state hFresh hLe
      exact inductionHypothesis (stepArcAtom state atom) (arcStateFresh_stepArcAtom state atom hFresh)
        (Nat.le_trans hLe (stepArcAtom_nextFresh_le state atom))

/-- ★ **`arcStructureOf` soundness under the COMPLETE `TwoCellConvFull`, gated on `ArcGodementSamePartitionFresh`
alone.**  The real arc structure always folds from the fresh-initial state `mk (range n) [] n 0 [] []`
(`arcStateFresh_initial`, whose `nextFresh = n = bottomCount`), so the freshness precondition discharges
automatically and the soundness reduces to the one true residual taken as a hypothesis. -/
theorem arcStructureOf_sound_of_arcGodementSamePartitionFresh {signature : ModeSignature}
    (samePartitionFresh : ArcGodementSamePartitionFresh signature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (convFull : TwoCellConvFull signature firstCell secondCell) :
    arcStructureOf firstCell = arcStructureOf secondCell :=
  arcTraceInvariantFresh sourcePath.length
    (fun state hFresh hLe {_firstList _secondList} step =>
      godementInvariantFresh_of_samePartitionFresh samePartitionFresh sourcePath.length state hFresh hLe step)
    (twoCellConvFull_spineTraceEquiv convFull)
    (ArcWireState.mk (List.range sourcePath.length) [] sourcePath.length 0 [] [])
    (arcStateFresh_initial sourcePath.length)
    (Nat.le_refl sourcePath.length)

/-- ★ **The FRESHNESS-gated free-2-cell convertibility decision.**  Given (1) the freshness-conditioned Godement
residual `ArcGodementSamePartitionFresh` (leg B — taken as a hypothesis here, NOT proved) and (2) the same
cell-level reconstruction the un-gated `decidableTwoCellConvFull_of` already takes, the completed
free-strict-2-category convertibility is decided by comparing the (computing) arc structures.  Discharging the ONE
true lemma `ArcGodementSamePartitionFresh` closes the soundness side.  The `isFalse` branch uses
`arcStructureOf_sound_of_arcGodementSamePartitionFresh`; the `isTrue` branch the reconstruction. -/
def decidableTwoCellConvFull_of_fresh {signature : ModeSignature}
    (samePartitionFresh : ArcGodementSamePartitionFresh signature)
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
    structuresEqual (arcStructureOf_sound_of_arcGodementSamePartitionFresh samePartitionFresh convFull))

/-! ## Honesty marker -/

/-- **Honesty marker — the FRESHNESS-gated arc-soundness reduction is PROVED (zero-axiom).**  `stepArcAtom` and
`processArcSpine` preserve `ArcStateFresh` (`arcStateFresh_stepArcAtom` / `arcStateFresh_processArcSpine`); the
freshness-gated `godementInvariant` reduces to the hypothesis `ArcGodementSamePartitionFresh`
(`godementInvariantFresh_of_samePartitionFresh`); freshness threads through the trace closure
(`arcTraceInvariantFresh`), discharging the precondition from the fresh-initial fold; and the freshness-gated
decision `decidableTwoCellConvFull_of_fresh` takes `ArcGodementSamePartitionFresh` + the reconstruction and yields
the decision.  The ONE remaining soundness obligation is `ArcGodementSamePartitionFresh` itself (leg B —
`fxMode_hasArcGodementSamePartitionFreshProof`), NOT proved here.  `= true`. -/
def fxMode_hasArcFreshSoundnessReduction : Bool := true

end FX1Poly.Tier0
