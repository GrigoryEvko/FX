import FX1Poly.Polygraph.TwoCategory.Table.FrobeniusFoldLegs
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescConnectivityMono

/-! # Polygraph/TwoCategory/Table/FrobeniusConnectivityInduction — the connectivity induction over the
canonical-spider union-find fold (FROB-SEED-MERGE r1, #2250, closing #2017's realization node)

The FROB-RESUME r2 reduction (`Table/FrobeniusFoldLegs.lean`) sharpened the surviving node of the general-arity
spider realization to a pure CONNECTIVITY statement: `spiderPartition_of_allConnected` reduces
`extraSpiderDiagramOf m (canonicalSpiderOf m n) = ⟨m, n, replicate (m+n) 0⟩` to "the `mergeToOne`/`fanToN`
union-find fold connects every boundary port and leaves `n` open wires".  The r2 recon framed the crux as a
NON-INJECTIVE seed-merge simulation; the FROB-SEED-MERGE recon corrected that: a DIRECT connectivity fold over the
single run `processBrauer (brauerSeed m) (canonicalSpiderOf m n)` sidesteps the collapse entirely.  This file
builds that direct fold, zero-axiom, and feeds `spiderPartition_of_allConnected`.

## What ships here

  * **The generic arc-connection lemma** (`stepWiringArcs_connects_arc`) — for ANY generator wiring, every arc's
    two decoded endpoints share a component of the post-step links, regardless of the fresh/loop branch (the loop
    branch keeps them joined, the union branch joins them).  Structural on the arc list; the crossing-inclusive
    analog of the connectivity-monotone `stepWiringArcs_isSameComponent_ofBase`.
  * **The two comb step lemmas** (`stepWiring_mult_head`, `stepWiring_comult_head`) — one `μ` / `δ` at position 0
    on a `head :: … :: tail` open-wire list computes its openWires shape and connects the consumed head(s) to the
    fresh output(s).
  * **The two phase inductions** — `mergeFold_connects_all` (the μ-comb merges every bottom wire into one hub) and
    `fanFold_connects` (the δ-comb fans one wire to `n` open wires, all in the anchor's component, preserving base
    connectivity), plus `mergeToOne_result` assembling the merge with the `m = 0` unit birth.
  * **The assembly** — `canonicalSpiderFold_connected`: every boundary port of the canonical `(m, n)` spider fold
    shares ONE component, and the fold leaves exactly `n` open wires.  This discharges
    `spiderPartition_of_allConnected`'s hypothesis at EVERY arity, giving the general-arity connected realization
    `extraSpiderDiagramOf_canonicalSpider`.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.  The Nat
arithmetic uses only `add_comm` / `add_assoc` / `add_right_comm` / `zero_add` / `add_zero` (propext-free), the
constructor-clash refutation `Nat.noConfusion`.  Additive: nothing outside `Table/` is edited (the union-find and
join-algebra homes are read-only imports).  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Propext-free list / Nat helper kit (re-derived; `FrobeniusFoldLegs`' copies are `private`) -/

/-- `(List.range.loop count acc).length = count + acc.length` — propext-free, via the loop accumulator. -/
theorem connRangeLoopLength : (count : Nat) → (acc : List Nat) →
    (List.range.loop count acc).length = count + acc.length
  | 0, acc => (Nat.zero_add acc.length).symm
  | count + 1, acc => by
      have ih := connRangeLoopLength count (count :: acc)
      show (List.range.loop count (count :: acc)).length = count + 1 + acc.length
      rw [ih]
      show count + (acc.length + 1) = count + 1 + acc.length
      rw [← Nat.add_assoc count acc.length 1, Nat.add_right_comm count acc.length 1]

/-- `(List.range count).length = count` — propext-free. -/
theorem connRangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [connRangeLoopLength count []]
  exact Nat.add_zero count

/-- `(first ++ second).length = first.length + second.length` — propext-free structural recursion. -/
theorem connListLengthAppend : (first second : List Nat) →
    (first ++ second).length = first.length + second.length
  | [], second => (Nat.zero_add second.length).symm
  | head :: rest, second => by
      show (rest ++ second).length + 1 = (rest.length + 1) + second.length
      rw [connListLengthAppend rest second]
      exact Nat.add_right_comm rest.length second.length 1

/-- A read at an in-range index is a member of the list — propext-free structural recursion via the
`List.Mem` constructors. -/
theorem connGetAtMem : (nodes : List Nat) → (index : Nat) → index < nodes.length →
    natListGetAt nodes index ∈ nodes
  | [], index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | _head :: rest, 0, _ => List.Mem.head rest
  | head :: rest, index + 1, indexBelow =>
      List.Mem.tail head (connGetAtMem rest index (Nat.lt_of_succ_lt_succ indexBelow))

/-- Every element of `first ++ second` satisfies a predicate that holds on all of `first` and all of `second`
— propext-free structural recursion. -/
theorem connAllMemAppend {holds : Nat → Prop} :
    (first second : List Nat) →
    (∀ node, node ∈ first → holds node) → (∀ node, node ∈ second → holds node) →
    ∀ node, node ∈ first ++ second → holds node
  | [], _, _, holdsSecond, node, hmem => holdsSecond node hmem
  | head :: rest, second, holdsFirst, holdsSecond, node, hmem => by
      cases hmem with
      | head => exact holdsFirst head (List.Mem.head rest)
      | tail _ hrest =>
          exact connAllMemAppend rest second
            (fun other hother => holdsFirst other (List.Mem.tail head hother)) holdsSecond node hrest

/-- `(k + 1) + (t + 1) = (k + 2) + t` — the fan-length step arithmetic, propext-free. -/
theorem connFanLenArith (leftCount tailCount : Nat) :
    (leftCount + 1) + (tailCount + 1) = (leftCount + 2) + tailCount := by
  rw [Nat.add_comm tailCount 1, ← Nat.add_assoc]

/-! ## The generic arc-connection lemma -/

/-- ★ **Every arc of a generator wiring connects its two endpoints.**  After the whole `stepWiringArcs` fold, the
two decoded endpoints of ANY arc in the arc list share a component of the resulting links — regardless of which
branch each fold step took (the loop branch keeps an already-joined pair joined and survives via
`stepWiringArcs_isSameComponent_ofBase`; the union branch joins the pair via `isSameComponent_unionFindJoin_joined`
and it survives the rest).  Structural on the arc list. -/
theorem stepWiringArcs_connects_arc (inputNodes outputNodes : List Nat) (inputCount : Nat) :
    (arcs : List (Nat × Nat)) → (loopsAcc : Nat) → (links : List (Nat × Nat)) →
    isUnionFindForest links → (arc : Nat × Nat) → arc ∈ arcs →
    isSameComponent (stepWiringArcs inputNodes outputNodes inputCount arcs loopsAcc links).fst
        (wiringEndpointNode inputNodes outputNodes inputCount arc.1)
        (wiringEndpointNode inputNodes outputNodes inputCount arc.2) = true
  | [], _, _, _, _, hmem => nomatch hmem
  | (headFirst, headSecond) :: rest, loopsAcc, links, forest, arc, hmem => by
      dsimp only [stepWiringArcs]
      split
      · cases hmem with
        | head =>
            rename_i hcond
            exact stepWiringArcs_isSameComponent_ofBase inputNodes outputNodes inputCount
              (wiringEndpointNode inputNodes outputNodes inputCount headFirst)
              (wiringEndpointNode inputNodes outputNodes inputCount headSecond)
              rest (loopsAcc + 1) links forest hcond
        | tail _ hrest =>
            exact stepWiringArcs_connects_arc inputNodes outputNodes inputCount rest (loopsAcc + 1) links
              forest arc hrest
      · cases hmem with
        | head =>
            exact stepWiringArcs_isSameComponent_ofBase inputNodes outputNodes inputCount
              (wiringEndpointNode inputNodes outputNodes inputCount headFirst)
              (wiringEndpointNode inputNodes outputNodes inputCount headSecond)
              rest loopsAcc
              (unionFindJoin links
                (wiringEndpointNode inputNodes outputNodes inputCount headFirst)
                (wiringEndpointNode inputNodes outputNodes inputCount headSecond))
              (isUnionFindForest_unionFindJoin links _ _ forest)
              (isSameComponent_unionFindJoin_joined links forest
                (wiringEndpointNode inputNodes outputNodes inputCount headFirst)
                (wiringEndpointNode inputNodes outputNodes inputCount headSecond))
        | tail _ hrest =>
            exact stepWiringArcs_connects_arc inputNodes outputNodes inputCount rest loopsAcc
              (unionFindJoin links
                (wiringEndpointNode inputNodes outputNodes inputCount headFirst)
                (wiringEndpointNode inputNodes outputNodes inputCount headSecond))
              (isUnionFindForest_unionFindJoin links _ _ forest) arc hrest

/-- One `stepWiring` step connects the endpoints of every arc of its `WiringDesc` — the arc fold's payoff read
onto the step's links (the step's `links` is that fold's output over the incoming links). -/
theorem stepWiring_connects_arc (state : WireState) (position : Nat) (desc : WiringDesc)
    (forest : isUnionFindForest state.links) (arc : Nat × Nat) (hmem : arc ∈ desc.arcs) :
    isSameComponent (stepWiring state position desc).links
        (wiringEndpointNode (natListSliceAt state.openWires position desc.inputCount)
          ((List.range desc.outputCount).map (· + state.nextFresh)) desc.inputCount arc.1)
        (wiringEndpointNode (natListSliceAt state.openWires position desc.inputCount)
          ((List.range desc.outputCount).map (· + state.nextFresh)) desc.inputCount arc.2) = true :=
  stepWiringArcs_connects_arc
    (natListSliceAt state.openWires position desc.inputCount)
    ((List.range desc.outputCount).map (· + state.nextFresh))
    desc.inputCount desc.arcs 0 state.links forest arc hmem

/-! ## The two comb step lemmas -/

/-- ★ **One multiplication at the head merges the two head wires into the fresh output.**  On an open-wire list
`hub :: w :: rest`, `stepWiring … multWiring` leaves `(0 + nextFresh) :: rest`, and both `hub` and `w` share a
component with the fresh output `0 + nextFresh`. -/
theorem stepWiring_mult_head (state : WireState) (hub secondWire : Nat) (rest : List Nat)
    (hopen : state.openWires = hub :: secondWire :: rest) (forest : isUnionFindForest state.links) :
    (stepWiring state 0 multWiring).openWires = (0 + state.nextFresh) :: rest
      ∧ isSameComponent (stepWiring state 0 multWiring).links hub (0 + state.nextFresh) = true
      ∧ isSameComponent (stepWiring state 0 multWiring).links secondWire (0 + state.nextFresh) = true := by
  refine ⟨?_, ?_, ?_⟩
  · show natListInsertAt (natListRemoveManyAt state.openWires 0 2) 0
        ((List.range 1).map (· + state.nextFresh)) = (0 + state.nextFresh) :: rest
    rw [hopen]
    simp only [natListRemoveManyAt, natListInsertAt, List.range, List.range.loop, List.map]; rfl
  · have hconn := stepWiring_connects_arc state 0 multWiring forest (0, 2) (List.Mem.head [(1, 2)])
    rw [hopen] at hconn
    exact hconn
  · have hconn := stepWiring_connects_arc state 0 multWiring forest (1, 2)
      (List.Mem.tail (0, 2) (List.Mem.head []))
    rw [hopen] at hconn
    exact hconn

/-- ★ **One comultiplication at the head fans the head wire into two fresh outputs.**  On an open-wire list
`headWire :: tail`, `stepWiring … comultWiring` leaves `(0 + nextFresh) :: (1 + nextFresh) :: tail`, and `headWire`
shares a component with BOTH fresh outputs. -/
theorem stepWiring_comult_head (state : WireState) (headWire : Nat) (tailWires : List Nat)
    (hopen : state.openWires = headWire :: tailWires) (forest : isUnionFindForest state.links) :
    (stepWiring state 0 comultWiring).openWires
        = (0 + state.nextFresh) :: (1 + state.nextFresh) :: tailWires
      ∧ isSameComponent (stepWiring state 0 comultWiring).links headWire (0 + state.nextFresh) = true
      ∧ isSameComponent (stepWiring state 0 comultWiring).links headWire (1 + state.nextFresh) = true := by
  refine ⟨?_, ?_, ?_⟩
  · show natListInsertAt (natListRemoveManyAt state.openWires 0 1) 0
        ((List.range 2).map (· + state.nextFresh))
          = (0 + state.nextFresh) :: (1 + state.nextFresh) :: tailWires
    rw [hopen]
    simp only [natListRemoveManyAt, natListInsertAt, List.range, List.range.loop, List.map]; rfl
  · have hconn := stepWiring_connects_arc state 0 comultWiring forest (0, 1) (List.Mem.head [(0, 2)])
    rw [hopen] at hconn
    exact hconn
  · have hconn := stepWiring_connects_arc state 0 comultWiring forest (0, 2)
      (List.Mem.tail (0, 1) (List.Mem.head []))
    rw [hopen] at hconn
    exact hconn

/-! ## The merge phase — every bottom wire merges into one hub -/

/-- `mergeToOne (inputs + 1)` is `inputs` copies of `multAt 0` (the μ-comb over `inputs + 1` inputs). -/
theorem mergeToOne_succ_eq_replicate : (inputs : Nat) →
    mergeToOne (inputs + 1) = List.replicate inputs (multAt 0)
  | 0 => rfl
  | inputs + 1 => by
      have ih := mergeToOne_succ_eq_replicate inputs
      show multAt 0 :: mergeToOne (inputs + 1) = multAt 0 :: List.replicate inputs (multAt 0)
      rw [ih]

/-- ★ **The μ-comb merges every open wire into one hub.**  Firing `mergeToOne`-many multiplications on a state whose
open wires are `hub :: tailWires` collapses to a single open wire `finalHub`, connects `hub` and every tail wire to
it, and preserves every incoming same-component membership.  Structural on `tailWires`. -/
theorem mergeFold_connects_all :
    (tailWires : List Nat) → (state : WireState) → (hub : Nat) →
    state.openWires = hub :: tailWires → isUnionFindForest state.links →
    ∃ finalHub : Nat,
      (processBrauer state (List.replicate tailWires.length (multAt 0))).openWires = [finalHub]
      ∧ isUnionFindForest (processBrauer state (List.replicate tailWires.length (multAt 0))).links
      ∧ isSameComponent (processBrauer state (List.replicate tailWires.length (multAt 0))).links
          hub finalHub = true
      ∧ (∀ wire, wire ∈ tailWires →
           isSameComponent (processBrauer state (List.replicate tailWires.length (multAt 0))).links
             wire finalHub = true)
      ∧ (∀ probeOne probeTwo, isSameComponent state.links probeOne probeTwo = true →
           isSameComponent (processBrauer state (List.replicate tailWires.length (multAt 0))).links
             probeOne probeTwo = true)
  | [], state, hub, hopen, forest => by
      refine ⟨hub, ?_, forest, isSameComponent_self state.links hub, ?_, fun _ _ base => base⟩
      · show state.openWires = [hub]
        rw [hopen]
      · intro wire hwire
        nomatch hwire
  | secondWire :: rest, state, hub, hopen, forest => by
      obtain ⟨hOpen1, hHub1, hSecond1⟩ := stepWiring_mult_head state hub secondWire rest hopen forest
      have forest1 : isUnionFindForest (stepWiring state 0 multWiring).links :=
        stepWiring_links_isUnionFindForest state 0 multWiring forest
      obtain ⟨finalHub, hFinOpen, hFinForest, hFinHub, hFinTail, hFinBase⟩ :=
        mergeFold_connects_all rest (stepWiring state 0 multWiring) (0 + state.nextFresh) hOpen1 forest1
      refine ⟨finalHub, hFinOpen, hFinForest, ?_, ?_, ?_⟩
      · exact isSameComponent_trans _ hub (0 + state.nextFresh) finalHub
          (hFinBase hub (0 + state.nextFresh) hHub1) hFinHub
      · intro wire hwire
        cases hwire with
        | head =>
            exact isSameComponent_trans _ secondWire (0 + state.nextFresh) finalHub
              (hFinBase secondWire (0 + state.nextFresh) hSecond1) hFinHub
        | tail _ hrest => exact hFinTail wire hrest
      · intro probeOne probeTwo hbase
        exact hFinBase probeOne probeTwo
          (stepWiring_isSameComponent_ofBase state 0 multWiring forest probeOne probeTwo hbase)

/-- ★ **The merge phase result.**  `processBrauer (brauerSeed m) (mergeToOne m)` has ONE open wire `hub`, its links
are a forest, and every bottom node in `List.range m` shares `hub`'s component.  Splits on `m = 0` (the unit births
the hub, no bottom ports) and `m = inputs + 1` (the μ-comb merges the seed's `List.range` open wires). -/
theorem mergeToOne_result (m : Nat) :
    ∃ hub : Nat,
      (processBrauer (brauerSeed m) (mergeToOne m)).openWires = [hub]
      ∧ isUnionFindForest (processBrauer (brauerSeed m) (mergeToOne m)).links
      ∧ (∀ node, node ∈ List.range m →
           isSameComponent (processBrauer (brauerSeed m) (mergeToOne m)).links node hub = true) := by
  match m with
  | 0 =>
      refine ⟨0, rfl, isUnionFindForest_nil, ?_⟩
      intro node hnode
      nomatch hnode
  | inputs + 1 =>
      cases hrange : List.range (inputs + 1) with
      | nil =>
          have hlen : (0 : Nat) = inputs + 1 := by
            have hcount := connRangeLength (inputs + 1)
            rw [hrange] at hcount
            exact hcount
          exact Nat.noConfusion hlen
      | cons head tail =>
          have htailLen : tail.length = inputs := by
            have hlen : tail.length + 1 = inputs + 1 := by
              have hcount := connRangeLength (inputs + 1)
              rw [hrange] at hcount
              exact hcount
            exact Nat.succ.inj hlen
          have hopen : (brauerSeed (inputs + 1)).openWires = head :: tail := hrange
          obtain ⟨finalHub, hFinOpen, hFinForest, hFinHub, hFinTail, _⟩ :=
            mergeFold_connects_all tail (brauerSeed (inputs + 1)) head hopen isUnionFindForest_nil
          have hword : mergeToOne (inputs + 1) = List.replicate tail.length (multAt 0) := by
            rw [htailLen]; exact mergeToOne_succ_eq_replicate inputs
          refine ⟨finalHub, ?_, ?_, ?_⟩
          · rw [hword]; exact hFinOpen
          · rw [hword]; exact hFinForest
          · intro node hnode
            rw [hword]
            cases hnode with
            | head => exact hFinHub
            | tail _ hrest => exact hFinTail node hrest

/-! ## The fan phase — one wire fans to `n` open wires, all in the anchor's component -/

/-- ★ **The δ-comb fans the head wire to `n` open wires, all anchored.**  Firing `fanToN n` on a state whose open
wires are `headWire :: tailWires`, with `headWire` and every tail wire already in the `anchor` component, leaves
`n + tailWires.length` open wires, all in the `anchor` component; the links stay a forest.  Structural on `n`
(matching `fanToN`'s `0 | 1 | outputs + 2` shape). -/
theorem fanFold_connects :
    (outputCount : Nat) → (state : WireState) → (anchor headWire : Nat) → (tailWires : List Nat) →
    state.openWires = headWire :: tailWires → isUnionFindForest state.links →
    isSameComponent state.links headWire anchor = true →
    (∀ wire, wire ∈ tailWires → isSameComponent state.links wire anchor = true) →
    (processBrauer state (fanToN outputCount)).openWires.length = outputCount + tailWires.length
      ∧ isUnionFindForest (processBrauer state (fanToN outputCount)).links
      ∧ (∀ wire, wire ∈ (processBrauer state (fanToN outputCount)).openWires →
           isSameComponent (processBrauer state (fanToN outputCount)).links wire anchor = true)
  | 0, state, anchor, headWire, tailWires, hopen, forest, _, hTail => by
      have hOpenNil : (processBrauer state (fanToN 0)).openWires = tailWires := by
        show natListInsertAt (natListRemoveManyAt state.openWires 0 1) 0
            ((List.range 0).map (· + state.nextFresh)) = tailWires
        rw [hopen]
        simp only [natListRemoveManyAt, natListInsertAt, List.range, List.range.loop, List.map]; rfl
      refine ⟨?_, forest, ?_⟩
      · rw [hOpenNil]
        exact (Nat.zero_add tailWires.length).symm
      · intro wire hwire
        rw [hOpenNil] at hwire
        exact hTail wire hwire
  | 1, state, anchor, headWire, tailWires, hopen, forest, hHead, hTail => by
      have hOpen1 : (processBrauer state (fanToN 1)).openWires = headWire :: tailWires := hopen
      refine ⟨?_, forest, ?_⟩
      · rw [hOpen1]
        exact Nat.add_comm tailWires.length 1
      · intro wire hwire
        rw [hOpen1] at hwire
        cases hwire with
        | head => exact hHead
        | tail _ hrest => exact hTail wire hrest
  | outputs + 2, state, anchor, headWire, tailWires, hopen, forest, hHead, hTail => by
      obtain ⟨hStepOpen, hStepFirst, hStepSecond⟩ :=
        stepWiring_comult_head state headWire tailWires hopen forest
      have forest1 : isUnionFindForest (stepWiring state 0 comultWiring).links :=
        stepWiring_links_isUnionFindForest state 0 comultWiring forest
      have hHeadAnchor1 : isSameComponent (stepWiring state 0 comultWiring).links headWire anchor = true :=
        stepWiring_isSameComponent_ofBase state 0 comultWiring forest headWire anchor hHead
      have hNewHead : isSameComponent (stepWiring state 0 comultWiring).links (0 + state.nextFresh) anchor = true :=
        isSameComponent_trans _ (0 + state.nextFresh) headWire anchor
          (isSameComponent_flip _ headWire (0 + state.nextFresh) hStepFirst) hHeadAnchor1
      have hTail1 : ∀ wire, wire ∈ (1 + state.nextFresh) :: tailWires →
          isSameComponent (stepWiring state 0 comultWiring).links wire anchor = true := by
        intro wire hwire
        cases hwire with
        | head =>
            exact isSameComponent_trans _ (1 + state.nextFresh) headWire anchor
              (isSameComponent_flip _ headWire (1 + state.nextFresh) hStepSecond) hHeadAnchor1
        | tail _ hrest =>
            exact stepWiring_isSameComponent_ofBase state 0 comultWiring forest wire anchor
              (hTail wire hrest)
      obtain ⟨hLen, hForest, hAll⟩ :=
        fanFold_connects (outputs + 1) (stepWiring state 0 comultWiring) anchor (0 + state.nextFresh)
          ((1 + state.nextFresh) :: tailWires) hStepOpen forest1 hNewHead hTail1
      refine ⟨?_, hForest, hAll⟩
      exact hLen.trans (connFanLenArith outputs tailWires.length)

/-! ## The assembly — every boundary port of the canonical spider fold is one component -/

/-- ★ **The canonical `(m, n)` spider fold connects every boundary port and leaves `n` open wires.**  Splits the
canonical word `mergeToOne m ++ fanToN n` at the phase boundary (`processBrauer_append`): the merge collapses every
bottom wire to one hub (`mergeToOne_result`), and the fan (`fanFold_connects`, anchor = hub) fans that hub to `n`
open wires — all in the hub's component — while preserving the bottom-wire connectivity (connectivity monotonicity).
So every node of `List.range m ++ finalOpenWires` shares the hub's component. -/
theorem canonicalSpiderFold_connected (m n : Nat) :
    ∃ hub : Nat,
      (processBrauer (brauerSeed m) (canonicalSpiderOf m n)).openWires.length = n
      ∧ (∀ node,
           node ∈ List.range m ++ (processBrauer (brauerSeed m) (canonicalSpiderOf m n)).openWires →
           isSameComponent (processBrauer (brauerSeed m) (canonicalSpiderOf m n)).links node hub = true) := by
  obtain ⟨hub, hMergeOpen, hMergeForest, hMergeRange⟩ := mergeToOne_result m
  have hsplit : processBrauer (brauerSeed m) (canonicalSpiderOf m n)
      = processBrauer (processBrauer (brauerSeed m) (mergeToOne m)) (fanToN n) := by
    show processBrauer (brauerSeed m) (mergeToOne m ++ fanToN n) = _
    exact processBrauer_append (mergeToOne m) (brauerSeed m) (fanToN n)
  obtain ⟨hFanLen, _, hFanAll⟩ :=
    fanFold_connects n (processBrauer (brauerSeed m) (mergeToOne m)) hub hub []
      hMergeOpen hMergeForest (isSameComponent_self _ hub) (fun _ hwire => nomatch hwire)
  refine ⟨hub, ?_, ?_⟩
  · rw [hsplit, hFanLen]
    exact Nat.add_zero n
  · intro node hnode
    rw [hsplit] at hnode ⊢
    refine connAllMemAppend (List.range m)
      (processBrauer (processBrauer (brauerSeed m) (mergeToOne m)) (fanToN n)).openWires ?_ hFanAll node hnode
    intro other hother
    exact processBrauer_isSameComponent_ofBase (fanToN n) (processBrauer (brauerSeed m) (mergeToOne m))
      hMergeForest other hub (hMergeRange other hother)

/-! ## The public deliverables — the connectivity hypothesis + the general-arity connected realization -/

/-- ★ **The canonical `(m, n)` spider fold leaves exactly `n` open wires.** -/
theorem canonicalSpider_finalOpenLength (m n : Nat) :
    (processBrauer (brauerSeed m) (canonicalSpiderOf m n)).openWires.length = n := by
  obtain ⟨_, hlen, _⟩ := canonicalSpiderFold_connected m n
  exact hlen

/-- ★ **The full connectivity of the canonical `(m, n)` spider fold** — every pair of in-range boundary indices is
same-component, `spiderPartition_of_allConnected`'s hypothesis at EVERY arity.  Each boundary node is a member of
`List.range m ++ openWires` (`connGetAtMem`), hence shares the hub's component (`canonicalSpiderFold_connected`), so
any two share it by transitivity. -/
theorem canonicalSpiderConnectivity (m n : Nat) :
    ∀ firstIndex secondIndex,
      firstIndex < m + (processBrauer (brauerSeed m) (canonicalSpiderOf m n)).openWires.length →
      secondIndex < m + (processBrauer (brauerSeed m) (canonicalSpiderOf m n)).openWires.length →
      matchingSameComponent m (processBrauer (brauerSeed m) (canonicalSpiderOf m n))
        firstIndex secondIndex = true := by
  obtain ⟨hub, _, hAll⟩ := canonicalSpiderFold_connected m n
  intro firstIndex secondIndex hFirst hSecond
  have hlenEq :
      (List.range m ++ (processBrauer (brauerSeed m) (canonicalSpiderOf m n)).openWires).length
        = m + (processBrauer (brauerSeed m) (canonicalSpiderOf m n)).openWires.length := by
    rw [connListLengthAppend, connRangeLength]
  have hmemFirst := connGetAtMem
    (List.range m ++ (processBrauer (brauerSeed m) (canonicalSpiderOf m n)).openWires)
    firstIndex (by rw [hlenEq]; exact hFirst)
  have hmemSecond := connGetAtMem
    (List.range m ++ (processBrauer (brauerSeed m) (canonicalSpiderOf m n)).openWires)
    secondIndex (by rw [hlenEq]; exact hSecond)
  show isSameComponent (processBrauer (brauerSeed m) (canonicalSpiderOf m n)).links
      (natListGetAt (List.range m ++ (processBrauer (brauerSeed m) (canonicalSpiderOf m n)).openWires) firstIndex)
      (natListGetAt (List.range m ++ (processBrauer (brauerSeed m) (canonicalSpiderOf m n)).openWires) secondIndex)
        = true
  exact isSameComponent_trans _ _ hub _ (hAll _ hmemFirst)
    (isSameComponent_flip _ _ hub (hAll _ hmemSecond))

/-- ★ **The general-arity CONNECTED spider realization** — `extraSpiderDiagramOf m (canonicalSpiderOf m n)` is the
fully-connected single-block partition `⟨m, n, replicate (m + n) 0⟩` for ALL `m`, `n`.  Feeds the full connectivity
(`canonicalSpiderConnectivity`) and the open-wire count (`canonicalSpider_finalOpenLength`) into the shipped
connectivity->partition reduction `spiderPartition_of_allConnected`.  This is the surviving node of #2017's
spider-fusion normal form, now landed. -/
theorem extraSpiderDiagramOf_canonicalSpider (m n : Nat) :
    extraSpiderDiagramOf m (canonicalSpiderOf m n)
      = { bottomCount := m, topCount := n, blockLabels := List.replicate (m + n) 0 } := by
  have hbase := spiderPartition_of_allConnected m
    (processBrauer (brauerSeed m) (canonicalSpiderOf m n)) (canonicalSpiderConnectivity m n)
  show forgetSpiderClosed
      (extractSpiderDiagram m (processBrauer (brauerSeed m) (canonicalSpiderOf m n)))
        = { bottomCount := m, topCount := n, blockLabels := List.replicate (m + n) 0 }
  rw [hbase, canonicalSpider_finalOpenLength]

/-! ### Non-vacuity — the general realization lands the exact block at concrete arities

Each instance cross-checks the general theorem `extraSpiderDiagramOf_canonicalSpider` against the direct
block (`decide` on the concrete `SpiderPartitionType`), demonstrating the induction FIRES at the connected
`(2, 2)`, `(3, 2)`, and the wider `(4, 3)` arity — not just at the previously machine-checked `decide` sizes. -/

/-- The general realization lands the connected `2 ⇒ 2` block `{2, 2, [0,0,0,0]}`. -/
theorem canonicalSpiderRealization_2_2 :
    extraSpiderDiagramOf 2 (canonicalSpiderOf 2 2)
      = { bottomCount := 2, topCount := 2, blockLabels := [0, 0, 0, 0] } :=
  (extraSpiderDiagramOf_canonicalSpider 2 2).trans (by decide)

/-- The general realization lands the connected `3 ⇒ 2` block `{3, 2, [0,0,0,0,0]}`. -/
theorem canonicalSpiderRealization_3_2 :
    extraSpiderDiagramOf 3 (canonicalSpiderOf 3 2)
      = { bottomCount := 3, topCount := 2, blockLabels := [0, 0, 0, 0, 0] } :=
  (extraSpiderDiagramOf_canonicalSpider 3 2).trans (by decide)

/-- ★ The general realization lands the WIDE connected `4 ⇒ 3` block `{4, 3, [0,0,0,0,0,0,0]}` — the induction
fires at an arity beyond the previously demonstrated `(m, n)` family. -/
theorem canonicalSpiderRealization_4_3 :
    extraSpiderDiagramOf 4 (canonicalSpiderOf 4 3)
      = { bottomCount := 4, topCount := 3, blockLabels := [0, 0, 0, 0, 0, 0, 0] } :=
  (extraSpiderDiagramOf_canonicalSpider 4 3).trans (by decide)

end FX1Poly.Polygraph
