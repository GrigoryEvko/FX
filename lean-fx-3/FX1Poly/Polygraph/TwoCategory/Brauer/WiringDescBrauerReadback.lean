import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerCompleteness

/-! # BREACH r4 P1 — the crossing-only READBACK (T2), IN-RANGE, PROVEN + crossing-block completeness

The r3 reduction `crossingCompleteness_of_readback` named the crossing-only readback T2 as the SOLE input separating
the shipped `S_n` straightening from crossing-only completeness.  This file DISCHARGES T2 in its honest IN-RANGE form
and derives crossing-block completeness UNCONDITIONALLY (no readback hypothesis).

## Why in-range (the general `∀` form is FALSE)

`BrauerCrossingOnlyReadback` (the ledger's `∀ bottomCount positions` form) is FALSE: an OUT-OF-RANGE crossing
(`position + 2 > bottomCount`) slices `< 2` open wires, `natListGetAt` defaults the missing input to node `0`, so
the wiring engine spuriously merges strand `0` while `applyAdjacentSwap` no-ops — e.g. over ONE bottom wire
`brauerDiagramOf 1 (crossingWord [0])` has `topCount = 2` but `permutationDiagram 1 (permuteOfCrossingWord 1 [0])`
has `topCount = 1`.  The clean, true statement gates every position in range (`position + 2 ≤ bottomCount`), which is
exactly what the completeness consumer supplies for free (`mentionsOnlyBelow generatorCount` words on
`generatorCount + 1` strands).

## The proof — a union-find STATE INVARIANT (the residual no shipped lemma supplied)

`StateIsPermGraph` says: after processing a crossing-only prefix, the union-find boundary view IS the permutation
graph of `permuteOfCrossingWord`.  Seed holds trivially; one in-range crossing preserves it — the fresh-forest step,
discharged by the shipped flat-disjunction join algebra (`isSameComponent_unionFindJoin`) plus the freshness of the
two new wires, reduced to an ADJACENT SWAP of the boundary indices.  The read-off `extractDiagram = permutationDiagram`
then falls out (`findPartnerScan` and `natIndexOfValue` are both "first same-strand index").

Raw Lean 4 + Init; structural recursion + fuel-bounded union-find (no `omega` / `simp`-AC / `native_decide` /
`WellFounded.fix`).  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local `Nat` / `Bool` helpers (propext-free) -/

/-- `(leftNode == rightNode) = false` from disequality — propext-free (`cases` on the decider). -/
private theorem natBeqFalse_ofNe (leftNode rightNode : Nat) (notEqual : leftNode ≠ rightNode) :
    (leftNode == rightNode) = false := by
  cases beqCase : leftNode == rightNode with
  | true => exact absurd (of_decide_eq_true beqCase) notEqual
  | false => rfl

/-! ## Local propext-free arithmetic + list helpers (Init's carry `propext` / `Quot.sound`) -/

/-- `n + a - n = a` — structural, propext-free. -/
private theorem addSubCancelLeftLocal : (n a : Nat) → n + a - n = a
  | 0, a => by rw [Nat.zero_add, Nat.sub_zero]
  | n + 1, a => by
      rw [Nat.add_right_comm n 1 a]
      show (n + a).succ - (n).succ = a
      rw [Nat.succ_sub_succ]
      exact addSubCancelLeftLocal n a

/-- `n ≤ i → n + (i - n) = i` — structural, propext-free. -/
private theorem addSubCancelLocal : (n i : Nat) → n ≤ i → n + (i - n) = i
  | 0, i, _ => by rw [Nat.zero_add, Nat.sub_zero]
  | n + 1, 0, h => absurd h (Nat.not_succ_le_zero n)
  | n + 1, i + 1, h => by
      rw [show (i + 1) - (n + 1) = i - n from Nat.succ_sub_succ i n, Nat.add_right_comm n 1 (i - n)]
      exact congrArg (· + 1) (addSubCancelLocal n i (Nat.le_of_succ_le_succ h))

/-- `list ++ [] = list` for `Nat` lists — structural, propext-free. -/
private theorem appendNilNat : (list : List Nat) → list ++ [] = list
  | [] => rfl
  | head :: rest => congrArg (head :: ·) (appendNilNat rest)

/-- `List.append` associativity for `Nat` lists — structural, propext-free. -/
private theorem appendAssocNat : (listA listB listC : List Nat) →
    (listA ++ listB) ++ listC = listA ++ (listB ++ listC)
  | [], _, _ => rfl
  | head :: rest, listB, listC => congrArg (head :: ·) (appendAssocNat rest listB listC)

/-- `foldl` over an append for the Brauer step — structural, propext-free (Init's `List.foldl_append`
carries `Quot.sound`). -/
private theorem foldlStepAppendLocal : (atomsA : List BrauerAtom) → (atomsB : List BrauerAtom) →
    (init : WireState) →
    (atomsA ++ atomsB).foldl stepBrauerAtom init
      = atomsB.foldl stepBrauerAtom (atomsA.foldl stepBrauerAtom init)
  | [], _, _ => rfl
  | atom :: rest, atomsB, init => foldlStepAppendLocal rest atomsB (stepBrauerAtom init atom)

/-! ## Fresh-node root facts (a node nobody's child roots to itself; a fresh node shares no old component) -/

/-- If `node` is nobody's child, its parent lookup is `none`.  Structural on the edge list. -/
private theorem unionFindParent_none_ofNotChild (node : Nat) :
    (links : List (Nat × Nat)) → (∀ edge ∈ links, edge.1 ≠ node) → unionFindParent links node = none
  | [], _ => rfl
  | (child, parent) :: rest, notChild => by
      have childNe : child ≠ node := notChild (child, parent) (List.Mem.head _)
      show (if child == node then some parent else unionFindParent rest node) = none
      rw [natBeqFalse_ofNe child node childNe]
      exact unionFindParent_none_ofNotChild node rest
        (fun edge memberOfRest => notChild edge (List.Mem.tail _ memberOfRest))

/-- With a `none` parent lookup, the fuel-bounded root is the node itself, at any fuel. -/
private theorem unionFindRoot_ofParentNone (links : List (Nat × Nat)) (node : Nat)
    (parentNone : unionFindParent links node = none) :
    (fuel : Nat) → unionFindRoot fuel links node = node
  | 0 => rfl
  | fuel + 1 => by
      show (match unionFindParent links node with
              | none => node
              | some parent => unionFindRoot fuel links parent) = node
      rw [parentNone]

/-- A node that is nobody's child roots to itself. -/
private theorem unionFindRootOf_ofNotChild (links : List (Nat × Nat)) (node : Nat)
    (notChild : ∀ edge ∈ links, edge.1 ≠ node) :
    unionFindRootOf links node = node :=
  unionFindRoot_ofParentNone links node (unionFindParent_none_ofNotChild node links notChild)
    (links.length + 1)

/-- A `some` parent lookup exhibits the parent among the recorded parents. -/
private theorem unionFindParent_some_memSnd (node : Nat) :
    (links : List (Nat × Nat)) → (parent : Nat) →
    unionFindParent links node = some parent → parent ∈ links.map Prod.snd
  | [], parent, lookupSome => by nomatch lookupSome
  | (child, recordedParent) :: rest, parent, lookupSome => by
      have lookupForm : (if child == node then some recordedParent else unionFindParent rest node)
          = some parent := lookupSome
      cases childBeq : child == node with
      | true =>
          rw [childBeq] at lookupForm
          rw [← Option.some.inj lookupForm]
          exact List.Mem.head _
      | false =>
          rw [childBeq] at lookupForm
          exact List.Mem.tail _ (unionFindParent_some_memSnd node rest parent lookupForm)

/-- The fuel-bounded root of a below-bound node stays below the bound, when every recorded parent is below it. -/
private theorem boundedRoot_ofParentsBelow (bound : Nat) (links : List (Nat × Nat))
    (parentsBelow : ∀ parent ∈ links.map Prod.snd, parent < bound) :
    (fuel node : Nat) → node < bound → unionFindRoot fuel links node < bound
  | 0, node, nodeBelow => nodeBelow
  | fuel + 1, node, nodeBelow => by
      show (match unionFindParent links node with
              | none => node
              | some parent => unionFindRoot fuel links parent) < bound
      cases lookupCase : unionFindParent links node with
      | none => exact nodeBelow
      | some parent =>
          have parentBelow : parent < bound :=
            parentsBelow parent (unionFindParent_some_memSnd node links parent lookupCase)
          exact boundedRoot_ofParentsBelow bound links parentsBelow fuel parent parentBelow

/-- A member of `links.map Prod.snd` comes from an edge in `links`. -/
private theorem memMapSnd_exEdge : (links : List (Nat × Nat)) → (parent : Nat) →
    parent ∈ links.map Prod.snd → ∃ child, (child, parent) ∈ links
  | [], _, memberOfNil => by cases memberOfNil
  | (child, recordedParent) :: rest, parent, memberOfMap => by
      cases memberOfMap with
      | head => exact ⟨child, List.Mem.head _⟩
      | tail _ memberOfRest =>
          obtain ⟨childRest, edgeInRest⟩ := memMapSnd_exEdge rest parent memberOfRest
          exact ⟨childRest, List.Mem.tail _ edgeInRest⟩

/-- The recorded parents of a fresh state's links are all below `nextFresh`. -/
private theorem freshParentsBelow {state : WireState} (fresh : WiringDescStateFresh state) :
    ∀ parent ∈ state.links.map Prod.snd, parent < state.nextFresh :=
  fun parent memberOfParents =>
    match memMapSnd_exEdge state.links parent memberOfParents with
    | ⟨child, edgeInLinks⟩ => (fresh.2 (child, parent) edgeInLinks).2

/-- A node at/above `nextFresh` is nobody's child in a fresh state's links. -/
private theorem freshNode_notChild {state : WireState} (fresh : WiringDescStateFresh state)
    (node : Nat) (nodeFresh : state.nextFresh ≤ node) :
    ∀ edge ∈ state.links, edge.1 ≠ node :=
  fun edge edgeInLinks childEqNode =>
    Nat.lt_irrefl node
      (Nat.lt_of_lt_of_le (childEqNode ▸ (fresh.2 edge edgeInLinks).1) nodeFresh)

/-- ★ A node at/above `nextFresh` roots to itself in a fresh state. -/
private theorem freshNode_rootSelf {state : WireState} (fresh : WiringDescStateFresh state)
    (node : Nat) (nodeFresh : state.nextFresh ≤ node) :
    unionFindRootOf state.links node = node :=
  unionFindRootOf_ofNotChild state.links node (freshNode_notChild fresh node nodeFresh)

/-- ★ A below-`nextFresh` node and an at/above-`nextFresh` node are in DIFFERENT components (freshness). -/
private theorem isSameComponent_below_fresh_false {state : WireState} (fresh : WiringDescStateFresh state)
    (oldNode freshNode : Nat) (oldBelow : oldNode < state.nextFresh)
    (freshAbove : state.nextFresh ≤ freshNode) :
    isSameComponent state.links oldNode freshNode = false := by
  have rootOldBelow : unionFindRootOf state.links oldNode < state.nextFresh :=
    boundedRoot_ofParentsBelow state.nextFresh state.links (freshParentsBelow fresh)
      (state.links.length + 1) oldNode oldBelow
  have rootFresh : unionFindRootOf state.links freshNode = freshNode :=
    freshNode_rootSelf fresh freshNode freshAbove
  show (unionFindRootOf state.links oldNode == unionFindRootOf state.links freshNode) = false
  rw [rootFresh]
  exact natBeqFalse_ofNe _ freshNode
    (fun rootEq => Nat.lt_irrefl freshNode (Nat.lt_of_lt_of_le (rootEq ▸ rootOldBelow) freshAbove))

/-! ## `natListGetAt` over append / range / slice / the crossing open-wire replacement -/

/-- `natListGetAt` on the left of an append, below the left length.  Structural on the list then index. -/
private theorem natListGetAt_append_left :
    (leftList rightList : List Nat) → (index : Nat) → index < leftList.length →
    natListGetAt (leftList ++ rightList) index = natListGetAt leftList index
  | [], _, index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | _ :: _, _, 0, _ => rfl
  | _ :: restLeft, rightList, index + 1, indexBelow =>
      natListGetAt_append_left restLeft rightList index (Nat.lt_of_succ_lt_succ indexBelow)

/-- `natListGetAt` on the right of an append, at a shifted index.  Structural on the left list. -/
private theorem natListGetAt_append_right :
    (leftList rightList : List Nat) → (index : Nat) →
    natListGetAt (leftList ++ rightList) (leftList.length + index) = natListGetAt rightList index
  | [], rightList, index => by
      show natListGetAt rightList (0 + index) = natListGetAt rightList index
      rw [Nat.zero_add]
  | headLeft :: restLeft, rightList, index => by
      show natListGetAt (headLeft :: (restLeft ++ rightList)) (restLeft.length + 1 + index)
        = natListGetAt rightList index
      rw [Nat.add_right_comm restLeft.length 1 index]
      show natListGetAt (restLeft ++ rightList) (restLeft.length + index) = natListGetAt rightList index
      exact natListGetAt_append_right restLeft rightList index

/-- Reading `List.range.loop` past its front drops into the accumulator (local copy). -/
private theorem rangeLoopGetPast : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetPast count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

/-- Reading `List.range.loop` below its front returns the index (local copy). -/
private theorem rangeLoopGetBelow : (count : Nat) → (accumulated : List Nat) → (index : Nat) →
    index < count → natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_lt_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetBelow count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have past := rangeLoopGetPast count (count :: accumulated) 0
          rw [Nat.zero_add count] at past
          rw [indexEq]; exact past

/-- `natListGetAt (List.range count) index = index` below the count. -/
private theorem natListGetAt_range (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetBelow count [] index indexBelow

/-- The two-wide slice at an in-range position reads off the two consecutive open wires. -/
private theorem natListSliceAt_two (wires : List Nat) (position : Nat)
    (hle : position + 2 ≤ wires.length) :
    natListSliceAt wires position 2 = [natListGetAt wires position, natListGetAt wires (position + 1)] := by
  induction position generalizing wires with
  | zero =>
      cases wires with
      | nil => exact absurd hle (Nat.not_succ_le_zero _)
      | cons headWire restWires =>
          cases restWires with
          | nil => exact absurd hle (Nat.not_succ_le_self 1)
          | cons nextWire rest =>
              rw [sliceAt_cons_zero_succ, sliceAt_cons_zero_succ, sliceAt_count_zero]
              rfl
  | succ position inductionHypothesis =>
      cases wires with
      | nil => exact absurd hle (Nat.not_succ_le_zero _)
      | cons headWire restWires =>
          show natListSliceAt restWires position 2
            = [natListGetAt restWires position, natListGetAt restWires (position + 1)]
          exact inductionHypothesis restWires (Nat.le_of_succ_le_succ hle)

/-! ## The crossing open-wire replacement — the swap of two positions -/

/-- The open-wire list a crossing produces: remove the two consumed wires at `position`, splice the two fresh output
wires there.  `natListGetAt` of it, at any index, replaces positions `position` / `position + 1` by the two fresh
nodes and leaves every other position unchanged.  Structural on `position` then the list. -/
private theorem natListGetAt_crossingReplace (freshLeft freshRight : Nat) (wires : List Nat)
    (position index : Nat) (hle : position + 2 ≤ wires.length) :
    natListGetAt (natListInsertAt (natListRemoveManyAt wires position 2) position [freshLeft, freshRight]) index
      = (if index = position then freshLeft
         else if index = position + 1 then freshRight
         else natListGetAt wires index) := by
  induction position generalizing wires index with
  | zero =>
      cases wires with
      | nil => exact absurd hle (Nat.not_succ_le_zero _)
      | cons headWire restWires =>
          cases restWires with
          | nil => exact absurd hle (Nat.not_succ_le_self 1)
          | cons nextWire rest =>
              rw [removeManyAt_zero_cons, removeManyAt_zero_cons, removeManyAt_zero, insertAt_zero]
              match index with
              | 0 => rfl
              | 1 => rfl
              | idx + 2 => rfl
  | succ positionPred inductionHypothesis =>
      cases wires with
      | nil => exact absurd hle (Nat.not_succ_le_zero _)
      | cons headWire restWires =>
          match index with
          | 0 =>
              rw [removeManyAt_succ_cons, insertAt_succ_cons]
              rw [if_neg (fun eqZero => Nat.noConfusion eqZero),
                if_neg (fun eqZero => Nat.noConfusion eqZero)]
              rfl
          | idx + 1 =>
              rw [removeManyAt_succ_cons, insertAt_succ_cons, natListGetAt]
              rw [inductionHypothesis restWires idx (Nat.le_of_succ_le_succ hle)]
              cases hidx : Nat.decEq idx positionPred with
              | isTrue heq =>
                  rw [if_pos heq, if_pos (congrArg (· + 1) heq)]
              | isFalse hne =>
                  rw [if_neg hne, if_neg (fun succEq => hne (Nat.succ.inj succEq))]
                  cases hidx2 : Nat.decEq idx (positionPred + 1) with
                  | isTrue heq2 => rw [if_pos heq2, if_pos (congrArg (· + 1) heq2)]
                  | isFalse hne2 =>
                      rw [if_neg hne2, if_neg (fun succEq => hne2 (Nat.succ.inj succEq))]
                      rfl

/-! ## The boundary view + the permutation graph -/

/-- The node id at boundary index `index`: a bottom index (`< bottomCount`) is node `index`; a top index reads the
open wire at `index - bottomCount`. -/
def boundaryNodeAt (bottomCount : Nat) (state : WireState) (index : Nat) : Nat :=
  if index < bottomCount then index else natListGetAt state.openWires (index - bottomCount)

/-- The strand a boundary index carries in the permutation graph of `perm`: bottom `i` carries `i`; top `n + j`
carries `perm[j]`. -/
def boundaryStrand (bottomCount : Nat) (perm : List Nat) (index : Nat) : Nat :=
  if index < bottomCount then index else natListGetAt perm (index - bottomCount)

/-! ## A `natListGetAt` bound + a fresh-distinct disconnection + the join-irrelevance lemma -/

/-- Reading a below-bound list at any index stays below the bound (past-the-end default `0 < bound`). -/
private theorem natListGetAt_lt_ofAll (bound : Nat) (nfPos : 0 < bound) :
    (wires : List Nat) → (∀ wire ∈ wires, wire < bound) → (index : Nat) → natListGetAt wires index < bound
  | [], _, _ => nfPos
  | headWire :: _, allBelow, 0 => allBelow headWire (List.Mem.head _)
  | _ :: restWires, allBelow, index + 1 =>
      natListGetAt_lt_ofAll bound nfPos restWires
        (fun wire wireMem => allBelow wire (List.Mem.tail _ wireMem)) index

/-- Two distinct at/above-`nextFresh` nodes are in different components (both roots are themselves). -/
private theorem isSameComponent_freshDistinct {state : WireState} (fresh : WiringDescStateFresh state)
    (nodeOne nodeTwo : Nat) (oneFresh : state.nextFresh ≤ nodeOne) (twoFresh : state.nextFresh ≤ nodeTwo)
    (distinct : nodeOne ≠ nodeTwo) :
    isSameComponent state.links nodeOne nodeTwo = false := by
  show (unionFindRootOf state.links nodeOne == unionFindRootOf state.links nodeTwo) = false
  rw [freshNode_rootSelf fresh nodeOne oneFresh, freshNode_rootSelf fresh nodeTwo twoFresh]
  exact natBeqFalse_ofNe nodeOne nodeTwo distinct

/-- ★ **Join-irrelevance.**  If a node `probe` is disconnected from BOTH endpoints of a join, then joining them does
not change whether any node shares `probe`'s component: `isSameComponent (join L fn sn) x probe = isSameComponent L x
probe`.  The flat-disjunction characterization with the two off-connections killing the mixed disjuncts. -/
private theorem join_irrelevant (links : List (Nat × Nat)) (forest : isUnionFindForest links)
    (joinLeft joinRight probe : Nat)
    (leftOff : isSameComponent links joinLeft probe = false)
    (rightOff : isSameComponent links joinRight probe = false) (probeOther : Nat) :
    isSameComponent (unionFindJoin links joinLeft joinRight) probeOther probe
      = isSameComponent links probeOther probe := by
  rw [isSameComponent_unionFindJoin links forest joinLeft joinRight probeOther probe, rightOff, leftOff]
  rw [Bool.and_false, Bool.false_and, Bool.or_false, Bool.or_false]

/-! ## The crossing step reduction -/

/-- The two output wires a crossing allocates: the two fresh ids `nextFresh`, `nextFresh + 1`. -/
private theorem crossingOutputNodes_eq (nextFresh : Nat) :
    (List.range 2).map (· + nextFresh) = [nextFresh, nextFresh + 1] := by
  show [0 + nextFresh, 1 + nextFresh] = [nextFresh, nextFresh + 1]
  rw [Nat.zero_add, Nat.add_comm 1 nextFresh]

/-- The generic arc fold on the crossing arc list, given both endpoint pairs start disconnected. -/
private theorem stepWiringArcs_crossing_eq (a b c d : Nat) (links : List (Nat × Nat))
    (adFalse : isSameComponent links a d = false)
    (bcFalse : isSameComponent (unionFindJoin links a d) b c = false) :
    stepWiringArcs [a, b] [c, d] 2 [(0, 3), (1, 2)] 0 links
      = (unionFindJoin (unionFindJoin links a d) b c, 0) := by
  have e0 : wiringEndpointNode [a, b] [c, d] 2 0 = a := rfl
  have e1 : wiringEndpointNode [a, b] [c, d] 2 1 = b := rfl
  have e2 : wiringEndpointNode [a, b] [c, d] 2 2 = c := rfl
  have e3 : wiringEndpointNode [a, b] [c, d] 2 3 = d := rfl
  show (if isSameComponent links (wiringEndpointNode [a, b] [c, d] 2 0) (wiringEndpointNode [a, b] [c, d] 2 3)
          then stepWiringArcs [a, b] [c, d] 2 [(1, 2)] (0 + 1) links
          else stepWiringArcs [a, b] [c, d] 2 [(1, 2)] 0
            (unionFindJoin links (wiringEndpointNode [a, b] [c, d] 2 0)
              (wiringEndpointNode [a, b] [c, d] 2 3))) = _
  rw [e0, e3, adFalse, if_neg (fun eq => Bool.noConfusion eq)]
  show (if isSameComponent (unionFindJoin links a d) (wiringEndpointNode [a, b] [c, d] 2 1)
          (wiringEndpointNode [a, b] [c, d] 2 2) then _
        else stepWiringArcs [a, b] [c, d] 2 [] 0
          (unionFindJoin (unionFindJoin links a d) (wiringEndpointNode [a, b] [c, d] 2 1)
            (wiringEndpointNode [a, b] [c, d] 2 2))) = _
  rw [e1, e2, bcFalse, if_neg (fun eq => Bool.noConfusion eq)]
  rfl

/-- ★ The crossing-step link update: the two-join `join (join L a d) b c` on the two consumed wires `a`, `b`
(`a = openWires[position]`, `b = openWires[position+1]`) and the two fresh legs `c = nextFresh`, `d = nextFresh + 1`. -/
private theorem stepWiring_crossing_links (state : WireState) (position : Nat)
    (fresh : WiringDescStateFresh state) (nfPos : 0 < state.nextFresh)
    (forest : isUnionFindForest state.links) (hrange : position + 2 ≤ state.openWires.length) :
    (stepWiring state position crossingWiring).links
      = unionFindJoin (unionFindJoin state.links
          (natListGetAt state.openWires position) (state.nextFresh + 1))
          (natListGetAt state.openWires (position + 1)) state.nextFresh := by
  have aLt : natListGetAt state.openWires position < state.nextFresh :=
    natListGetAt_lt_ofAll state.nextFresh nfPos state.openWires fresh.1 position
  have bLt : natListGetAt state.openWires (position + 1) < state.nextFresh :=
    natListGetAt_lt_ofAll state.nextFresh nfPos state.openWires fresh.1 (position + 1)
  have adFalse : isSameComponent state.links (natListGetAt state.openWires position)
      (state.nextFresh + 1) = false :=
    isSameComponent_below_fresh_false fresh _ _ aLt (Nat.le_succ state.nextFresh)
  have acFalse : isSameComponent state.links (natListGetAt state.openWires position)
      state.nextFresh = false :=
    isSameComponent_below_fresh_false fresh _ _ aLt (Nat.le_refl state.nextFresh)
  have dcFalse : isSameComponent state.links (state.nextFresh + 1) state.nextFresh = false :=
    isSameComponent_freshDistinct fresh _ _ (Nat.le_succ state.nextFresh) (Nat.le_refl state.nextFresh)
      (Nat.succ_ne_self state.nextFresh)
  have bcFalse : isSameComponent (unionFindJoin state.links (natListGetAt state.openWires position)
      (state.nextFresh + 1)) (natListGetAt state.openWires (position + 1)) state.nextFresh = false := by
    rw [join_irrelevant state.links forest _ _ _ acFalse dcFalse]
    exact isSameComponent_below_fresh_false fresh _ _ bLt (Nat.le_refl state.nextFresh)
  show (stepWiringArcs (natListSliceAt state.openWires position 2)
      ((List.range 2).map (· + state.nextFresh)) 2 [(0, 3), (1, 2)] 0 state.links).fst = _
  rw [natListSliceAt_two state.openWires position hrange, crossingOutputNodes_eq,
    stepWiringArcs_crossing_eq _ _ _ _ state.links adFalse bcFalse]

/-- The crossing step preserves the loop count (no arc closes a loop — both legs start disconnected). -/
private theorem stepWiring_crossing_loops (state : WireState) (position : Nat)
    (fresh : WiringDescStateFresh state) (nfPos : 0 < state.nextFresh)
    (forest : isUnionFindForest state.links) (hrange : position + 2 ≤ state.openWires.length) :
    (stepWiring state position crossingWiring).loops = state.loops := by
  have aLt : natListGetAt state.openWires position < state.nextFresh :=
    natListGetAt_lt_ofAll state.nextFresh nfPos state.openWires fresh.1 position
  have bLt : natListGetAt state.openWires (position + 1) < state.nextFresh :=
    natListGetAt_lt_ofAll state.nextFresh nfPos state.openWires fresh.1 (position + 1)
  have adFalse : isSameComponent state.links (natListGetAt state.openWires position)
      (state.nextFresh + 1) = false :=
    isSameComponent_below_fresh_false fresh _ _ aLt (Nat.le_succ state.nextFresh)
  have acFalse : isSameComponent state.links (natListGetAt state.openWires position)
      state.nextFresh = false :=
    isSameComponent_below_fresh_false fresh _ _ aLt (Nat.le_refl state.nextFresh)
  have dcFalse : isSameComponent state.links (state.nextFresh + 1) state.nextFresh = false :=
    isSameComponent_freshDistinct fresh _ _ (Nat.le_succ state.nextFresh) (Nat.le_refl state.nextFresh)
      (Nat.succ_ne_self state.nextFresh)
  have bcFalse : isSameComponent (unionFindJoin state.links (natListGetAt state.openWires position)
      (state.nextFresh + 1)) (natListGetAt state.openWires (position + 1)) state.nextFresh = false := by
    rw [join_irrelevant state.links forest _ _ _ acFalse dcFalse]
    exact isSameComponent_below_fresh_false fresh _ _ bLt (Nat.le_refl state.nextFresh)
  have hsnd : (stepWiringArcs (natListSliceAt state.openWires position 2)
      ((List.range 2).map (· + state.nextFresh)) 2 [(0, 3), (1, 2)] 0 state.links).snd = 0 := by
    rw [natListSliceAt_two state.openWires position hrange, crossingOutputNodes_eq,
      stepWiringArcs_crossing_eq _ _ _ _ state.links adFalse bcFalse]
  show state.loops + (stepWiringArcs (natListSliceAt state.openWires position 2)
      ((List.range 2).map (· + state.nextFresh)) 2 [(0, 3), (1, 2)] 0 state.links).snd + 0 = state.loops
  rw [hsnd, Nat.add_zero]

/-- The crossing step's open-wire list: the two consumed wires at `position` replaced by the two fresh legs. -/
private theorem stepWiring_crossing_open (state : WireState) (position : Nat) :
    (stepWiring state position crossingWiring).openWires
      = natListInsertAt (natListRemoveManyAt state.openWires position 2) position
          [state.nextFresh, state.nextFresh + 1] :=
  congrArg (natListInsertAt (natListRemoveManyAt state.openWires position 2) position)
    (crossingOutputNodes_eq state.nextFresh)

/-- The crossing replacement preserves the open-wire count (removes two, inserts two). -/
private theorem crossingReplace_length (freshLeft freshRight : Nat) (wires : List Nat) (position : Nat)
    (hle : position + 2 ≤ wires.length) :
    (natListInsertAt (natListRemoveManyAt wires position 2) position [freshLeft, freshRight]).length
      = wires.length := by
  induction position generalizing wires with
  | zero =>
      cases wires with
      | nil => exact absurd hle (Nat.not_succ_le_zero _)
      | cons headWire restWires =>
          cases restWires with
          | nil => exact absurd hle (Nat.not_succ_le_self 1)
          | cons nextWire rest =>
              rw [removeManyAt_zero_cons, removeManyAt_zero_cons, removeManyAt_zero, insertAt_zero]
              show (freshLeft :: freshRight :: rest).length = (headWire :: nextWire :: rest).length
              rfl
  | succ positionPred inductionHypothesis =>
      cases wires with
      | nil => exact absurd hle (Nat.not_succ_le_zero _)
      | cons headWire restWires =>
          rw [removeManyAt_succ_cons, insertAt_succ_cons]
          show (natListInsertAt (natListRemoveManyAt restWires positionPred 2) positionPred
                [freshLeft, freshRight]).length + 1 = restWires.length + 1
          rw [inductionHypothesis restWires (Nat.le_of_succ_le_succ hle)]

/-! ## The fresh-forest connectivity of the crossing two-join `K = join (join L a d) b c`

Over `L = state.links` with `a, b < nextFresh` and the two fresh legs `c = nextFresh`, `d = nextFresh + 1`, the two
joins glue `d` to `a` and `c` to `b`, touching no other old-node connectivity.  These facts characterize the new
same-component relation entirely in terms of the OLD one (with `c` acting as `b`, `d` as `a`). -/

/-- Old node against fresh leg `c = nextFresh`: `c` acts as `b`. -/
private theorem crossing_old_c (state : WireState) (fresh : WiringDescStateFresh state)
    (forest : isUnionFindForest state.links) (a b : Nat) (aLt : a < state.nextFresh)
    (bLt : b < state.nextFresh) (x : Nat) (xLt : x < state.nextFresh) :
    isSameComponent (unionFindJoin (unionFindJoin state.links a (state.nextFresh + 1)) b state.nextFresh)
        x state.nextFresh = isSameComponent state.links x b := by
  have forest1 : isUnionFindForest (unionFindJoin state.links a (state.nextFresh + 1)) :=
    isUnionFindForest_unionFindJoin state.links a (state.nextFresh + 1) forest
  have acFalse : isSameComponent state.links a state.nextFresh = false :=
    isSameComponent_below_fresh_false fresh a state.nextFresh aLt (Nat.le_refl _)
  have dcFalse : isSameComponent state.links (state.nextFresh + 1) state.nextFresh = false :=
    isSameComponent_freshDistinct fresh _ _ (Nat.le_succ _) (Nat.le_refl _) (Nat.succ_ne_self _)
  have bcFalse : isSameComponent state.links b state.nextFresh = false :=
    isSameComponent_below_fresh_false fresh b state.nextFresh bLt (Nat.le_refl _)
  have xcFalse : isSameComponent state.links x state.nextFresh = false :=
    isSameComponent_below_fresh_false fresh x state.nextFresh xLt (Nat.le_refl _)
  have bdFalse : isSameComponent state.links b (state.nextFresh + 1) = false :=
    isSameComponent_below_fresh_false fresh b (state.nextFresh + 1) bLt (Nat.le_succ _)
  have xdFalse : isSameComponent state.links (state.nextFresh + 1) x = false := by
    rw [isSameComponent_symm]
    exact isSameComponent_below_fresh_false fresh x (state.nextFresh + 1) xLt (Nat.le_succ _)
  rw [isSameComponent_unionFindJoin (unionFindJoin state.links a (state.nextFresh + 1)) forest1 b
        state.nextFresh x state.nextFresh,
    isSameComponent_self (unionFindJoin state.links a (state.nextFresh + 1)) state.nextFresh,
    join_irrelevant state.links forest a (state.nextFresh + 1) state.nextFresh acFalse dcFalse x,
    join_irrelevant state.links forest a (state.nextFresh + 1) state.nextFresh acFalse dcFalse b,
    isSameComponent_unionFindJoin state.links forest a (state.nextFresh + 1) b x,
    xcFalse, bcFalse, bdFalse, xdFalse]
  rw [isSameComponent_symm state.links x b]
  cases isSameComponent state.links b x <;> cases isSameComponent state.links a b <;>
    cases isSameComponent state.links a x <;> rfl

/-- Old node against fresh leg `d = nextFresh + 1`: `d` acts as `a`. -/
private theorem crossing_old_d (state : WireState) (fresh : WiringDescStateFresh state)
    (forest : isUnionFindForest state.links) (a b : Nat) (aLt : a < state.nextFresh)
    (bLt : b < state.nextFresh) (x : Nat) (xLt : x < state.nextFresh) :
    isSameComponent (unionFindJoin (unionFindJoin state.links a (state.nextFresh + 1)) b state.nextFresh)
        x (state.nextFresh + 1) = isSameComponent state.links x a := by
  have forest1 : isUnionFindForest (unionFindJoin state.links a (state.nextFresh + 1)) :=
    isUnionFindForest_unionFindJoin state.links a (state.nextFresh + 1) forest
  have adFalse : isSameComponent state.links a (state.nextFresh + 1) = false :=
    isSameComponent_below_fresh_false fresh a (state.nextFresh + 1) aLt (Nat.le_succ _)
  have bdFalse : isSameComponent state.links b (state.nextFresh + 1) = false :=
    isSameComponent_below_fresh_false fresh b (state.nextFresh + 1) bLt (Nat.le_succ _)
  have xdFalse : isSameComponent state.links x (state.nextFresh + 1) = false :=
    isSameComponent_below_fresh_false fresh x (state.nextFresh + 1) xLt (Nat.le_succ _)
  have acFalse : isSameComponent state.links a state.nextFresh = false :=
    isSameComponent_below_fresh_false fresh a state.nextFresh aLt (Nat.le_refl _)
  have xcFalse : isSameComponent state.links x state.nextFresh = false :=
    isSameComponent_below_fresh_false fresh x state.nextFresh xLt (Nat.le_refl _)
  have dcFalse : isSameComponent state.links (state.nextFresh + 1) state.nextFresh = false :=
    isSameComponent_freshDistinct fresh _ _ (Nat.le_succ _) (Nat.le_refl _) (Nat.succ_ne_self _)
  have cdFalse : isSameComponent state.links state.nextFresh (state.nextFresh + 1) = false :=
    isSameComponent_freshDistinct fresh _ _ (Nat.le_refl _) (Nat.le_succ _)
      (fun eq => Nat.succ_ne_self state.nextFresh eq.symm)
  have ddSelf : isSameComponent state.links (state.nextFresh + 1) (state.nextFresh + 1) = true :=
    isSameComponent_self state.links (state.nextFresh + 1)
  rw [isSameComponent_unionFindJoin (unionFindJoin state.links a (state.nextFresh + 1)) forest1 b
        state.nextFresh x (state.nextFresh + 1),
    isSameComponent_unionFindJoin state.links forest a (state.nextFresh + 1) x (state.nextFresh + 1),
    isSameComponent_unionFindJoin state.links forest a (state.nextFresh + 1) b (state.nextFresh + 1),
    isSameComponent_unionFindJoin state.links forest a (state.nextFresh + 1) state.nextFresh
      (state.nextFresh + 1),
    join_irrelevant state.links forest a (state.nextFresh + 1) state.nextFresh acFalse dcFalse x,
    xdFalse, adFalse, bdFalse, cdFalse, ddSelf, xcFalse, acFalse]
  rw [isSameComponent_symm state.links x a]
  cases isSameComponent state.links a x <;> cases isSameComponent state.links a b <;>
    cases isSameComponent (unionFindJoin state.links a (state.nextFresh + 1)) b x <;> rfl

/-- Old node against old node: the crossing (glue to fresh legs) changes no old-old connectivity. -/
private theorem crossing_old_old (state : WireState) (fresh : WiringDescStateFresh state)
    (forest : isUnionFindForest state.links) (a b : Nat) (aLt : a < state.nextFresh)
    (bLt : b < state.nextFresh) (x y : Nat) (xLt : x < state.nextFresh) (yLt : y < state.nextFresh) :
    isSameComponent (unionFindJoin (unionFindJoin state.links a (state.nextFresh + 1)) b state.nextFresh)
        x y = isSameComponent state.links x y := by
  have forest1 : isUnionFindForest (unionFindJoin state.links a (state.nextFresh + 1)) :=
    isUnionFindForest_unionFindJoin state.links a (state.nextFresh + 1) forest
  have acFalse : isSameComponent state.links a state.nextFresh = false :=
    isSameComponent_below_fresh_false fresh a state.nextFresh aLt (Nat.le_refl _)
  have dcFalse : isSameComponent state.links (state.nextFresh + 1) state.nextFresh = false :=
    isSameComponent_freshDistinct fresh _ _ (Nat.le_succ _) (Nat.le_refl _) (Nat.succ_ne_self _)
  have xcFalse : isSameComponent state.links x state.nextFresh = false :=
    isSameComponent_below_fresh_false fresh x state.nextFresh xLt (Nat.le_refl _)
  have ycFalse : isSameComponent state.links y state.nextFresh = false :=
    isSameComponent_below_fresh_false fresh y state.nextFresh yLt (Nat.le_refl _)
  have xdFalse : isSameComponent state.links x (state.nextFresh + 1) = false :=
    isSameComponent_below_fresh_false fresh x (state.nextFresh + 1) xLt (Nat.le_succ _)
  have dyFalse : isSameComponent state.links (state.nextFresh + 1) y = false := by
    rw [isSameComponent_symm]
    exact isSameComponent_below_fresh_false fresh y (state.nextFresh + 1) yLt (Nat.le_succ _)
  rw [isSameComponent_unionFindJoin (unionFindJoin state.links a (state.nextFresh + 1)) forest1 b
        state.nextFresh x y,
    isSameComponent_symm (unionFindJoin state.links a (state.nextFresh + 1)) state.nextFresh y,
    join_irrelevant state.links forest a (state.nextFresh + 1) state.nextFresh acFalse dcFalse y,
    join_irrelevant state.links forest a (state.nextFresh + 1) state.nextFresh acFalse dcFalse x,
    isSameComponent_unionFindJoin state.links forest a (state.nextFresh + 1) x y,
    ycFalse, xcFalse, dyFalse, xdFalse]
  cases isSameComponent state.links x y <;> cases isSameComponent state.links a x <;>
    cases isSameComponent state.links a y <;>
    cases isSameComponent (unionFindJoin state.links a (state.nextFresh + 1)) b x <;>
    cases isSameComponent (unionFindJoin state.links a (state.nextFresh + 1)) b y <;> rfl

/-- Fresh leg `c = nextFresh` against fresh leg `d = nextFresh + 1`: `c` acts as `b`, `d` acts as `a`. -/
private theorem crossing_c_d (state : WireState) (fresh : WiringDescStateFresh state)
    (forest : isUnionFindForest state.links) (a b : Nat) (aLt : a < state.nextFresh)
    (bLt : b < state.nextFresh) :
    isSameComponent (unionFindJoin (unionFindJoin state.links a (state.nextFresh + 1)) b state.nextFresh)
        state.nextFresh (state.nextFresh + 1) = isSameComponent state.links a b := by
  have forest1 : isUnionFindForest (unionFindJoin state.links a (state.nextFresh + 1)) :=
    isUnionFindForest_unionFindJoin state.links a (state.nextFresh + 1) forest
  have acFalse : isSameComponent state.links a state.nextFresh = false :=
    isSameComponent_below_fresh_false fresh a state.nextFresh aLt (Nat.le_refl _)
  have adFalse : isSameComponent state.links a (state.nextFresh + 1) = false :=
    isSameComponent_below_fresh_false fresh a (state.nextFresh + 1) aLt (Nat.le_succ _)
  have bcFalse : isSameComponent state.links b state.nextFresh = false :=
    isSameComponent_below_fresh_false fresh b state.nextFresh bLt (Nat.le_refl _)
  have bdFalse : isSameComponent state.links b (state.nextFresh + 1) = false :=
    isSameComponent_below_fresh_false fresh b (state.nextFresh + 1) bLt (Nat.le_succ _)
  have dcFalse : isSameComponent state.links (state.nextFresh + 1) state.nextFresh = false :=
    isSameComponent_freshDistinct fresh _ _ (Nat.le_succ _) (Nat.le_refl _) (Nat.succ_ne_self _)
  have cdFalse : isSameComponent state.links state.nextFresh (state.nextFresh + 1) = false :=
    isSameComponent_freshDistinct fresh _ _ (Nat.le_refl _) (Nat.le_succ _)
      (fun eq => Nat.succ_ne_self state.nextFresh eq.symm)
  have ddSelf : isSameComponent state.links (state.nextFresh + 1) (state.nextFresh + 1) = true :=
    isSameComponent_self state.links (state.nextFresh + 1)
  rw [isSameComponent_unionFindJoin (unionFindJoin state.links a (state.nextFresh + 1)) forest1 b
        state.nextFresh state.nextFresh (state.nextFresh + 1),
    isSameComponent_self (unionFindJoin state.links a (state.nextFresh + 1)) state.nextFresh,
    join_irrelevant state.links forest a (state.nextFresh + 1) state.nextFresh acFalse dcFalse b,
    isSameComponent_unionFindJoin state.links forest a (state.nextFresh + 1) state.nextFresh
      (state.nextFresh + 1),
    isSameComponent_unionFindJoin state.links forest a (state.nextFresh + 1) b (state.nextFresh + 1),
    cdFalse, acFalse, adFalse, ddSelf, bcFalse, bdFalse]
  cases isSameComponent state.links a b <;>
    cases isSameComponent (unionFindJoin state.links a (state.nextFresh + 1)) b state.nextFresh <;> rfl

/-! ## The lift: the crossing two-join same-component IS the old one, with `c ↦ b`, `d ↦ a` -/

/-- The old node a crossing boundary node maps to: the fresh left leg `c = nextFresh` acts as `b`, the fresh right
leg `d = nextFresh + 1` acts as `a`, every other node is itself. -/
def liftCrossNode (secondWire firstWire nextFresh node : Nat) : Nat :=
  if node = nextFresh then secondWire else if node = nextFresh + 1 then firstWire else node

/-- `liftCrossNode` at the left fresh leg is `secondWire`. -/
private theorem liftCrossNode_c (secondWire firstWire nextFresh : Nat) :
    liftCrossNode secondWire firstWire nextFresh nextFresh = secondWire := by
  show (if nextFresh = nextFresh then secondWire else _) = secondWire
  rw [if_pos rfl]

/-- `liftCrossNode` at the right fresh leg is `firstWire`. -/
private theorem liftCrossNode_d (secondWire firstWire nextFresh : Nat) :
    liftCrossNode secondWire firstWire nextFresh (nextFresh + 1) = firstWire := by
  show (if nextFresh + 1 = nextFresh then secondWire
        else if nextFresh + 1 = nextFresh + 1 then firstWire else _) = firstWire
  rw [if_neg (Nat.succ_ne_self nextFresh), if_pos rfl]

/-- `liftCrossNode` below the fresh counter is the identity. -/
private theorem liftCrossNode_old (secondWire firstWire nextFresh node : Nat) (nodeLt : node < nextFresh) :
    liftCrossNode secondWire firstWire nextFresh node = node := by
  show (if node = nextFresh then secondWire else if node = nextFresh + 1 then firstWire else node) = node
  rw [if_neg (Nat.ne_of_lt nodeLt),
    if_neg (Nat.ne_of_lt (Nat.lt_trans nodeLt (Nat.lt_succ_self nextFresh)))]

/-- A node below `nextFresh + 2` is the left fresh leg, the right fresh leg, or below `nextFresh`. -/
private theorem nodeCase (nextFresh w : Nat) (wBound : w < nextFresh + 2) :
    w = nextFresh ∨ w = nextFresh + 1 ∨ w < nextFresh := by
  rcases Nat.lt_or_ge w nextFresh with wLt | wGe
  · exact Or.inr (Or.inr wLt)
  · rcases Nat.lt_or_ge w (nextFresh + 1) with wLt1 | wGe1
    · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ wLt1) wGe)
    · exact Or.inr (Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ wBound) wGe1))

/-- ★ **The crossing lift lemma.**  For nodes below `nextFresh + 2`, the crossing two-join same-component relation
equals the OLD relation after mapping the two fresh legs back to their glued partners
(`c = nextFresh ↦ b`, `d = nextFresh + 1 ↦ a`).  The nine-case dispatch to the six connectivity facts + reflexivity
+ symmetry. -/
private theorem crossing_lift (state : WireState) (fresh : WiringDescStateFresh state)
    (forest : isUnionFindForest state.links) (a b : Nat) (aLt : a < state.nextFresh)
    (bLt : b < state.nextFresh) (u v : Nat) (uBound : u < state.nextFresh + 2)
    (vBound : v < state.nextFresh + 2) :
    isSameComponent (unionFindJoin (unionFindJoin state.links a (state.nextFresh + 1)) b state.nextFresh) u v
      = isSameComponent state.links (liftCrossNode b a state.nextFresh u)
          (liftCrossNode b a state.nextFresh v) := by
  rcases nodeCase state.nextFresh u uBound with hu | hu | hu
  · rcases nodeCase state.nextFresh v vBound with hv | hv | hv
    · subst hu; subst hv
      rw [liftCrossNode_c]
      exact (isSameComponent_self _ state.nextFresh).trans (isSameComponent_self state.links b).symm
    · subst hu; subst hv
      rw [liftCrossNode_c, liftCrossNode_d]
      exact (crossing_c_d state fresh forest a b aLt bLt).trans (isSameComponent_symm state.links a b)
    · subst hu
      rw [liftCrossNode_c, liftCrossNode_old b a state.nextFresh v hv]
      exact (isSameComponent_symm _ state.nextFresh v).trans
        ((crossing_old_c state fresh forest a b aLt bLt v hv).trans (isSameComponent_symm state.links v b))
  · rcases nodeCase state.nextFresh v vBound with hv | hv | hv
    · subst hu; subst hv
      rw [liftCrossNode_d, liftCrossNode_c]
      exact (isSameComponent_symm _ (state.nextFresh + 1) state.nextFresh).trans
        (crossing_c_d state fresh forest a b aLt bLt)
    · subst hu; subst hv
      rw [liftCrossNode_d]
      exact (isSameComponent_self _ (state.nextFresh + 1)).trans (isSameComponent_self state.links a).symm
    · subst hu
      rw [liftCrossNode_d, liftCrossNode_old b a state.nextFresh v hv]
      exact (isSameComponent_symm _ (state.nextFresh + 1) v).trans
        ((crossing_old_d state fresh forest a b aLt bLt v hv).trans (isSameComponent_symm state.links v a))
  · rcases nodeCase state.nextFresh v vBound with hv | hv | hv
    · subst hv
      rw [liftCrossNode_old b a state.nextFresh u hu, liftCrossNode_c]
      exact crossing_old_c state fresh forest a b aLt bLt u hu
    · subst hv
      rw [liftCrossNode_old b a state.nextFresh u hu, liftCrossNode_d]
      exact crossing_old_d state fresh forest a b aLt bLt u hu
    · rw [liftCrossNode_old b a state.nextFresh u hu, liftCrossNode_old b a state.nextFresh v hv]
      exact crossing_old_old state fresh forest a b aLt bLt u v hu hv

/-! ## The T2 state invariant + the adjacent-swap read-off -/

/-- ★ **The T2 state invariant** — after processing a crossing-only prefix `positions`, the union-find boundary view
IS the permutation graph of `permuteOfCrossingWord bottomCount positions`: the open-wire count is `bottomCount`, no
loops closed, and every boundary index pair shares a component exactly when it carries the same through-strand. -/
structure StateIsPermGraph (bottomCount : Nat) (positions : List Nat) (state : WireState) : Prop where
  /-- The open-wire count is the bottom count (all strands are through-strands). -/
  openLen : state.openWires.length = bottomCount
  /-- No closed loops. -/
  noLoops : state.loops = 0
  /-- The boundary same-component view IS the permutation-graph strand-equality. -/
  boundView : ∀ indexA indexB : Nat, indexA < bottomCount + bottomCount → indexB < bottomCount + bottomCount →
      isSameComponent state.links (boundaryNodeAt bottomCount state indexA)
          (boundaryNodeAt bottomCount state indexB)
        = decide (boundaryStrand bottomCount (permuteOfCrossingWord bottomCount positions) indexA
                  = boundaryStrand bottomCount (permuteOfCrossingWord bottomCount positions) indexB)

/-- ★ **The seed satisfies the invariant.**  At `brauerSeed`, `openWires = links = []`-free `List.range`, and
`permuteOfCrossingWord _ [] = List.range`, so the boundary node and boundary strand coincide definitionally and
`isSameComponent [] x y = decide (x = y)`. -/
theorem stateIsPermGraph_seed (bottomCount : Nat) :
    StateIsPermGraph bottomCount [] (brauerSeed bottomCount) where
  openLen := rangeLength_local bottomCount
  noLoops := rfl
  boundView := fun _ _ _ _ => rfl

/-- Reading an adjacent swap: `position` and `position + 1` exchange, every other index unchanged.  Structural on
`position` then the list, matching the swap's own matcher. -/
private theorem applyAdjacentSwap_get :
    (perm : List Nat) → (position : Nat) → (index : Nat) → position + 1 < perm.length →
    natListGetAt (applyAdjacentSwap perm position) index
      = (if index = position then natListGetAt perm (position + 1)
         else if index = position + 1 then natListGetAt perm position
         else natListGetAt perm index)
  | [], _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | [_single], position, _, hlt => absurd (Nat.lt_of_succ_lt_succ hlt) (Nat.not_lt_zero position)
  | first :: second :: rest, 0, index, _ => by
      match index with
      | 0 => rfl
      | 1 => rfl
      | idx + 2 => rfl
  | first :: second :: rest, positionPred + 1, index, hlt => by
      have restLt : positionPred + 1 < (second :: rest).length :=
        Nat.lt_of_succ_lt_succ hlt
      match index with
      | 0 => rfl
      | idx + 1 =>
          show natListGetAt (applyAdjacentSwap (second :: rest) positionPred) idx
            = (if idx + 1 = positionPred + 1 then natListGetAt (second :: rest) (positionPred + 1)
               else if idx + 1 = positionPred + 1 + 1 then natListGetAt (second :: rest) positionPred
               else natListGetAt (second :: rest) idx)
          rw [applyAdjacentSwap_get (second :: rest) positionPred idx restLt]
          cases hidx : Nat.decEq idx positionPred with
          | isTrue heq => rw [if_pos heq, if_pos (congrArg (· + 1) heq)]
          | isFalse hne =>
              rw [if_neg hne, if_neg (fun succEq => hne (Nat.succ.inj succEq))]
              cases hidx2 : Nat.decEq idx (positionPred + 1) with
              | isTrue heq2 => rw [if_pos heq2, if_pos (congrArg (· + 1) heq2)]
              | isFalse hne2 => rw [if_neg hne2, if_neg (fun succEq => hne2 (Nat.succ.inj succEq))]

/-- The boundary-index shuffle a crossing at boundary position `pos` induces: the two top boundary indices
`bottomCount + pos` and `bottomCount + pos + 1` exchange, all others fixed. -/
def shuffleIndex (bottomCount pos index : Nat) : Nat :=
  if index = bottomCount + pos then bottomCount + pos + 1
  else if index = bottomCount + pos + 1 then bottomCount + pos else index

/-- The shuffle stays inside the boundary range. -/
private theorem shuffleIndex_lt (bottomCount pos index : Nat) (prange : pos + 2 ≤ bottomCount)
    (indexLt : index < bottomCount + bottomCount) :
    shuffleIndex bottomCount pos index < bottomCount + bottomCount := by
  have posSuccLt : pos + 1 < bottomCount := Nat.lt_of_lt_of_le (Nat.lt_succ_self (pos + 1)) prange
  have posLt : pos < bottomCount := Nat.lt_of_succ_lt posSuccLt
  show (if index = bottomCount + pos then bottomCount + pos + 1
        else if index = bottomCount + pos + 1 then bottomCount + pos else index) < bottomCount + bottomCount
  split
  · exact Nat.add_lt_add_left posSuccLt bottomCount
  · split
    · exact Nat.add_lt_add_left posLt bottomCount
    · exact indexLt

/-- A boundary node stays below the fresh counter (a bottom port `< bottomCount ≤ nextFresh`, a top wire fresh). -/
private theorem boundaryNodeAt_lt (bottomCount : Nat) (state : WireState) (fresh : WiringDescStateFresh state)
    (nfPos : 0 < state.nextFresh) (nLe : bottomCount ≤ state.nextFresh) (index : Nat) :
    boundaryNodeAt bottomCount state index < state.nextFresh := by
  show (if index < bottomCount then index else natListGetAt state.openWires (index - bottomCount))
      < state.nextFresh
  split
  · rename_i indexLt; exact Nat.lt_of_lt_of_le indexLt nLe
  · exact natListGetAt_lt_ofAll state.nextFresh nfPos state.openWires fresh.1 (index - bottomCount)

/-- ★ **Strand coherence** — the swapped permutation's boundary strand at `index` is the old permutation's strand at
the shuffled index.  The adjacent swap of the through-strand permutation IS the boundary-index shuffle. -/
private theorem coherence_strand (bottomCount : Nat) (perm : List Nat) (pos : Nat)
    (permLen : perm.length = bottomCount) (prange : pos + 1 < bottomCount) (index : Nat) :
    boundaryStrand bottomCount (applyAdjacentSwap perm pos) index
      = boundaryStrand bottomCount perm (shuffleIndex bottomCount pos index) := by
  have permPosLt : pos + 1 < perm.length := permLen ▸ prange
  rcases Nat.lt_or_ge index bottomCount with hi | hi
  · have iNeP : index ≠ bottomCount + pos :=
      Nat.ne_of_lt (Nat.lt_of_lt_of_le hi (Nat.le_add_right bottomCount pos))
    have iNeP1 : index ≠ bottomCount + pos + 1 :=
      Nat.ne_of_lt (Nat.lt_of_lt_of_le hi
        (Nat.le_trans (Nat.le_add_right bottomCount pos) (Nat.le_succ _)))
    have hs : shuffleIndex bottomCount pos index = index := by
      show (if index = bottomCount + pos then _ else if index = bottomCount + pos + 1 then _ else index) = index
      rw [if_neg iNeP, if_neg iNeP1]
    show (if index < bottomCount then index else _)
      = (if shuffleIndex bottomCount pos index < bottomCount then shuffleIndex bottomCount pos index else _)
    rw [hs, if_pos hi, if_pos hi]
  · have iEq : bottomCount + (index - bottomCount) = index := addSubCancelLocal bottomCount index hi
    show (if index < bottomCount then index else natListGetAt (applyAdjacentSwap perm pos) (index - bottomCount))
      = boundaryStrand bottomCount perm (shuffleIndex bottomCount pos index)
    rw [if_neg (Nat.not_lt.mpr hi), applyAdjacentSwap_get perm pos (index - bottomCount) permPosLt]
    cases hj : Nat.decEq (index - bottomCount) pos with
    | isTrue hjEq =>
        rw [if_pos hjEq]
        have hIndex : index = bottomCount + pos := by rw [← hjEq]; exact iEq.symm
        show natListGetAt perm (pos + 1) = boundaryStrand bottomCount perm (shuffleIndex bottomCount pos index)
        rw [show shuffleIndex bottomCount pos index = bottomCount + pos + 1 by
          show (if index = bottomCount + pos then _ else _) = bottomCount + pos + 1; rw [if_pos hIndex]]
        show natListGetAt perm (pos + 1)
          = (if bottomCount + pos + 1 < bottomCount then _
             else natListGetAt perm (bottomCount + pos + 1 - bottomCount))
        rw [if_neg (Nat.not_lt.mpr (Nat.le_trans (Nat.le_add_right bottomCount pos) (Nat.le_succ _)))]
        rw [show bottomCount + pos + 1 - bottomCount = pos + 1 by
          rw [Nat.add_assoc, addSubCancelLeftLocal]]
    | isFalse hjNe =>
        rw [if_neg hjNe]
        cases hj1 : Nat.decEq (index - bottomCount) (pos + 1) with
        | isTrue hj1Eq =>
            rw [if_pos hj1Eq]
            have hIndex : index = bottomCount + pos + 1 := by
              rw [← iEq, hj1Eq]; exact (Nat.add_assoc bottomCount pos 1).symm
            show natListGetAt perm pos = boundaryStrand bottomCount perm (shuffleIndex bottomCount pos index)
            rw [show shuffleIndex bottomCount pos index = bottomCount + pos by
              show (if index = bottomCount + pos then _ else if index = bottomCount + pos + 1 then _ else _)
                = bottomCount + pos
              rw [if_neg (fun eq => hjNe (by rw [eq, addSubCancelLeftLocal])), if_pos hIndex]]
            show natListGetAt perm pos
              = (if bottomCount + pos < bottomCount then _ else natListGetAt perm (bottomCount + pos - bottomCount))
            rw [if_neg (Nat.not_lt.mpr (Nat.le_add_right bottomCount pos)), addSubCancelLeftLocal]
        | isFalse hj1Ne =>
            rw [if_neg hj1Ne]
            have iNeP : index ≠ bottomCount + pos :=
              fun eq => hjNe (by rw [eq, addSubCancelLeftLocal])
            have iNeP1 : index ≠ bottomCount + pos + 1 :=
              fun eq => hj1Ne (by rw [eq, Nat.add_assoc, addSubCancelLeftLocal])
            rw [show shuffleIndex bottomCount pos index = index by
              show (if index = bottomCount + pos then _ else if index = bottomCount + pos + 1 then _ else index)
                = index
              rw [if_neg iNeP, if_neg iNeP1]]
            show natListGetAt perm (index - bottomCount)
              = (if index < bottomCount then index else natListGetAt perm (index - bottomCount))
            rw [if_neg (Nat.not_lt.mpr hi)]

/-- ★ **Node coherence** — the lift of the new boundary node at `index` is the old boundary node at the shuffled
index.  The crossing's fresh legs (`c = nextFresh ↦ b`, `d = nextFresh + 1 ↦ a`) coincide with the old top wires the
shuffle exchanges. -/
private theorem coherence_node (bottomCount : Nat) (oldState : WireState)
    (fresh : WiringDescStateFresh oldState) (nfPos : 0 < oldState.nextFresh)
    (nLe : bottomCount ≤ oldState.nextFresh) (pos : Nat)
    (prangeOpen : pos + 2 ≤ oldState.openWires.length) (index : Nat) :
    liftCrossNode (natListGetAt oldState.openWires (pos + 1)) (natListGetAt oldState.openWires pos)
        oldState.nextFresh (boundaryNodeAt bottomCount (stepWiring oldState pos crossingWiring) index)
      = boundaryNodeAt bottomCount oldState (shuffleIndex bottomCount pos index) := by
  have newOpenGet : ∀ j, natListGetAt (stepWiring oldState pos crossingWiring).openWires j
      = (if j = pos then oldState.nextFresh else if j = pos + 1 then oldState.nextFresh + 1
         else natListGetAt oldState.openWires j) := fun j => by
    rw [stepWiring_crossing_open]
    exact natListGetAt_crossingReplace oldState.nextFresh (oldState.nextFresh + 1) oldState.openWires pos j
      prangeOpen
  rcases Nat.lt_or_ge index bottomCount with hi | hi
  · have iNeP : index ≠ bottomCount + pos :=
      Nat.ne_of_lt (Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _))
    have iNeP1 : index ≠ bottomCount + pos + 1 :=
      Nat.ne_of_lt (Nat.lt_of_lt_of_le hi (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _)))
    rw [show boundaryNodeAt bottomCount (stepWiring oldState pos crossingWiring) index = index by
        show (if index < bottomCount then index else _) = index; rw [if_pos hi],
      liftCrossNode_old _ _ _ index (Nat.lt_of_lt_of_le hi nLe),
      show shuffleIndex bottomCount pos index = index by
        show (if index = bottomCount + pos then _ else if index = bottomCount + pos + 1 then _ else index) = index
        rw [if_neg iNeP, if_neg iNeP1],
      show boundaryNodeAt bottomCount oldState index = index by
        show (if index < bottomCount then index else _) = index; rw [if_pos hi]]
  · have iEq : bottomCount + (index - bottomCount) = index := addSubCancelLocal bottomCount index hi
    rw [show boundaryNodeAt bottomCount (stepWiring oldState pos crossingWiring) index
          = natListGetAt (stepWiring oldState pos crossingWiring).openWires (index - bottomCount) by
        show (if index < bottomCount then index else _) = _; rw [if_neg (Nat.not_lt.mpr hi)],
      newOpenGet (index - bottomCount)]
    cases hj : Nat.decEq (index - bottomCount) pos with
    | isTrue hjEq =>
        have hIndex : index = bottomCount + pos := by rw [← hjEq]; exact iEq.symm
        rw [if_pos hjEq, liftCrossNode_c,
          show shuffleIndex bottomCount pos index = bottomCount + pos + 1 by
            show (if index = bottomCount + pos then _ else _) = _; rw [if_pos hIndex],
          show boundaryNodeAt bottomCount oldState (bottomCount + pos + 1)
              = natListGetAt oldState.openWires (pos + 1) by
            show (if bottomCount + pos + 1 < bottomCount then _
                  else natListGetAt oldState.openWires (bottomCount + pos + 1 - bottomCount)) = _
            rw [if_neg (Nat.not_lt.mpr (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _))),
              show bottomCount + pos + 1 - bottomCount = pos + 1 by
                rw [Nat.add_assoc, addSubCancelLeftLocal]]]
    | isFalse hjNe =>
        rw [if_neg hjNe]
        cases hj1 : Nat.decEq (index - bottomCount) (pos + 1) with
        | isTrue hj1Eq =>
            have hIndex : index = bottomCount + pos + 1 := by
              rw [← iEq, hj1Eq]; exact (Nat.add_assoc bottomCount pos 1).symm
            rw [if_pos hj1Eq, liftCrossNode_d,
              show shuffleIndex bottomCount pos index = bottomCount + pos by
                show (if index = bottomCount + pos then _ else if index = bottomCount + pos + 1 then _ else _) = _
                rw [if_neg (fun eq => hjNe (by rw [eq, addSubCancelLeftLocal])), if_pos hIndex],
              show boundaryNodeAt bottomCount oldState (bottomCount + pos)
                  = natListGetAt oldState.openWires pos by
                show (if bottomCount + pos < bottomCount then _
                      else natListGetAt oldState.openWires (bottomCount + pos - bottomCount)) = _
                rw [if_neg (Nat.not_lt.mpr (Nat.le_add_right _ _)), addSubCancelLeftLocal]]
        | isFalse hj1Ne =>
            have iNeP : index ≠ bottomCount + pos :=
              fun eq => hjNe (by rw [eq, addSubCancelLeftLocal])
            have iNeP1 : index ≠ bottomCount + pos + 1 :=
              fun eq => hj1Ne (by rw [eq, Nat.add_assoc, addSubCancelLeftLocal])
            rw [if_neg hj1Ne,
              liftCrossNode_old _ _ _ (natListGetAt oldState.openWires (index - bottomCount))
                (natListGetAt_lt_ofAll oldState.nextFresh nfPos oldState.openWires fresh.1 (index - bottomCount)),
              show shuffleIndex bottomCount pos index = index by
                show (if index = bottomCount + pos then _ else if index = bottomCount + pos + 1 then _ else index)
                  = index
                rw [if_neg iNeP, if_neg iNeP1],
              show boundaryNodeAt bottomCount oldState index
                  = natListGetAt oldState.openWires (index - bottomCount) by
                show (if index < bottomCount then index else _) = _; rw [if_neg (Nat.not_lt.mpr hi)]]

/-! ## Snoc decompositions of the two folds -/

/-- `crossingWord` distributes over concatenation (it is a `map`). -/
private theorem crossingWordAppendLocal : (wordLeft wordRight : List Nat) →
    crossingWord (wordLeft ++ wordRight) = crossingWord wordLeft ++ crossingWord wordRight
  | [], _ => rfl
  | _ :: rest, wordRight => congrArg (crossingAt _ :: ·) (crossingWordAppendLocal rest wordRight)

/-- The realized permutation after appending one position is one more adjacent swap. -/
private theorem permuteSnocLocal (bottomCount : Nat) (positions : List Nat) (pos : Nat) :
    permuteOfCrossingWord bottomCount (positions ++ [pos])
      = applyAdjacentSwap (permuteOfCrossingWord bottomCount positions) pos := by
  show (positions ++ [pos]).foldl applyAdjacentSwap (List.range bottomCount)
    = applyAdjacentSwap (positions.foldl applyAdjacentSwap (List.range bottomCount)) pos
  rw [foldl_append_swap positions [pos] (List.range bottomCount)]
  rfl

/-- Processing after appending one crossing position is one more `stepWiring`. -/
private theorem processBrauer_crossingWord_snoc (bottomCount : Nat) (positions : List Nat) (pos : Nat) :
    processBrauer (brauerSeed bottomCount) (crossingWord (positions ++ [pos]))
      = stepWiring (processBrauer (brauerSeed bottomCount) (crossingWord positions)) pos crossingWiring := by
  rw [crossingWordAppendLocal]
  show ((crossingWord positions) ++ [crossingAt pos]).foldl stepBrauerAtom (brauerSeed bottomCount)
    = stepWiring (processBrauer (brauerSeed bottomCount) (crossingWord positions)) pos crossingWiring
  rw [foldlStepAppendLocal]
  rfl

/-! ## The step + the fold — the in-range readback invariant -/

/-- ★★ **THE T2 STEP** — one in-range crossing preserves the permutation-graph invariant, advancing the permutation
by an adjacent swap.  The load-bearing residual, discharged: the crossing lift (fresh-forest connectivity) reduces the
new boundary same-component view to the OLD one at the shuffled indices (`coherence_node`), the old invariant reads it
off as the OLD permutation's strand equality, and the strand coherence (`coherence_strand`) turns that into the
SWAPPED permutation's — exactly the adjacent-swap advance. -/
theorem stateIsPermGraph_step (bottomCount : Nat) (positions : List Nat) (pos : Nat) (prange : pos + 2 ≤ bottomCount)
    (oldState : WireState) (cond : BrauerStateConditions bottomCount oldState)
    (inv : StateIsPermGraph bottomCount positions oldState) :
    StateIsPermGraph bottomCount (positions ++ [pos]) (stepWiring oldState pos crossingWiring) := by
  have prangeOpen : pos + 2 ≤ oldState.openWires.length := inv.openLen ▸ prange
  have prange1 : pos + 1 < bottomCount := Nat.lt_of_lt_of_le (Nat.lt_succ_self (pos + 1)) prange
  have aLt : natListGetAt oldState.openWires pos < oldState.nextFresh :=
    natListGetAt_lt_ofAll oldState.nextFresh cond.nfPos oldState.openWires cond.fresh.1 pos
  have bLt : natListGetAt oldState.openWires (pos + 1) < oldState.nextFresh :=
    natListGetAt_lt_ofAll oldState.nextFresh cond.nfPos oldState.openWires cond.fresh.1 (pos + 1)
  have newFresh : WiringDescStateFresh (stepWiring oldState pos crossingWiring) :=
    wiringDescStateFresh_stepWiring oldState pos crossingWiring cond.fresh cond.nfPos
  have permLen : (permuteOfCrossingWord bottomCount positions).length = bottomCount :=
    permuteOfCrossingWord_length bottomCount positions
  refine ⟨?_, ?_, ?_⟩
  · rw [stepWiring_crossing_open]
    exact (crossingReplace_length oldState.nextFresh (oldState.nextFresh + 1) oldState.openWires pos
      prangeOpen).trans inv.openLen
  · rw [stepWiring_crossing_loops oldState pos cond.fresh cond.nfPos cond.forest prangeOpen]
    exact inv.noLoops
  · intro i1 i2 h1 h2
    have bound1 : boundaryNodeAt bottomCount (stepWiring oldState pos crossingWiring) i1
        < oldState.nextFresh + 2 :=
      boundaryNodeAt_lt bottomCount (stepWiring oldState pos crossingWiring) newFresh
        (Nat.lt_of_lt_of_le cond.nfPos (Nat.le_add_right _ _))
        (Nat.le_trans cond.bottomLe (Nat.le_add_right _ _)) i1
    have bound2 : boundaryNodeAt bottomCount (stepWiring oldState pos crossingWiring) i2
        < oldState.nextFresh + 2 :=
      boundaryNodeAt_lt bottomCount (stepWiring oldState pos crossingWiring) newFresh
        (Nat.lt_of_lt_of_le cond.nfPos (Nat.le_add_right _ _))
        (Nat.le_trans cond.bottomLe (Nat.le_add_right _ _)) i2
    rw [permuteSnocLocal,
      stepWiring_crossing_links oldState pos cond.fresh cond.nfPos cond.forest prangeOpen,
      crossing_lift oldState cond.fresh cond.forest (natListGetAt oldState.openWires pos)
        (natListGetAt oldState.openWires (pos + 1)) aLt bLt _ _ bound1 bound2,
      coherence_node bottomCount oldState cond.fresh cond.nfPos cond.bottomLe pos prangeOpen i1,
      coherence_node bottomCount oldState cond.fresh cond.nfPos cond.bottomLe pos prangeOpen i2,
      inv.boundView (shuffleIndex bottomCount pos i1) (shuffleIndex bottomCount pos i2)
        (shuffleIndex_lt bottomCount pos i1 prange h1) (shuffleIndex_lt bottomCount pos i2 prange h2),
      coherence_strand bottomCount (permuteOfCrossingWord bottomCount positions) pos permLen prange1 i1,
      coherence_strand bottomCount (permuteOfCrossingWord bottomCount positions) pos permLen prange1 i2]

/-- The invariant is preserved across a whole in-range crossing-word suffix. -/
private theorem stateIsPermGraph_fold (bottomCount : Nat) (npos : 0 < bottomCount) :
    (processed remaining : List Nat) → (∀ q ∈ remaining, q + 2 ≤ bottomCount) →
    StateIsPermGraph bottomCount processed
        (processBrauer (brauerSeed bottomCount) (crossingWord processed)) →
    StateIsPermGraph bottomCount (processed ++ remaining)
        (processBrauer (brauerSeed bottomCount) (crossingWord (processed ++ remaining)))
  | processed, [], _, inv => by rw [appendNilNat]; exact inv
  | processed, q :: rest, ranges, inv => by
      have qrange : q + 2 ≤ bottomCount := ranges q (List.Mem.head _)
      have restRanges : ∀ r ∈ rest, r + 2 ≤ bottomCount := fun r rm => ranges r (List.Mem.tail _ rm)
      have reassoc : processed ++ q :: rest = (processed ++ [q]) ++ rest :=
        (appendAssocNat processed [q] rest).symm
      rw [reassoc]
      refine stateIsPermGraph_fold bottomCount npos (processed ++ [q]) rest restRanges ?_
      rw [processBrauer_crossingWord_snoc]
      exact stateIsPermGraph_step bottomCount processed q qrange
        (processBrauer (brauerSeed bottomCount) (crossingWord processed))
        (brauerReachable_conditions bottomCount npos (crossingWord processed)) inv

/-- ★★ **The T2 state invariant, for every in-range crossing word.**  Processing a crossing-only word whose every
position fires in range (`q + 2 ≤ bottomCount`) reaches a state whose union-find boundary view IS the permutation
graph of the through-strand permutation.  The seed + the fold. -/
theorem stateIsPermGraph_ofInRange (bottomCount : Nat) (npos : 0 < bottomCount) (positions : List Nat)
    (inRange : ∀ q ∈ positions, q + 2 ≤ bottomCount) :
    StateIsPermGraph bottomCount positions
      (processBrauer (brauerSeed bottomCount) (crossingWord positions)) :=
  stateIsPermGraph_fold bottomCount npos [] positions inRange (stateIsPermGraph_seed bottomCount)

/-- **Honesty marker — the T2 crossing-only readback STATE INVARIANT is PROVEN (the fresh-forest keystone).**
`stateIsPermGraph_ofInRange` establishes, for every in-range crossing word, that the union-find boundary
same-component view coincides with the through-strand permutation graph — the load-bearing residual the recon
identified ("a `stepWiring crossingWiring` connectivity induction no shipped lemma supplies").  The keystone is the
fresh-forest connectivity `crossing_lift` (the two fresh legs `c ↦ b`, `d ↦ a` reduce the new same-component to the
old one, via the shipped flat-disjunction join algebra), assembled with the boundary-index coherence
(`coherence_node` / `coherence_strand`) into the one-step advance `stateIsPermGraph_step`, folded from the seed.
Zero-axiom, structural.  `= true`. -/
def fxBrauer_hasCrossingReadbackStateInvariant : Bool := true




end FX1Poly.Polygraph
