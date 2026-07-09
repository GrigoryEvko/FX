import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanInsertion

/-! # WalkingString — the union-find FRESHNESS core: adding a fresh edge preserves old roots (FC-3, piece A-i)

`fxString_hasOrientPreservationResidual` (in `StringFussCatalanInsertion`) named the CUP half of the `preserves`
residual precisely: after `stepCup` splices a FRESH connected pair `(nextFresh, nextFresh+1)`, proving the strand
discipline is preserved needs "that every id in `openWires`/`links` is `< nextFresh` and that adding the edge
`(nextFresh, nextFresh+1)` changes no OLD-old `isSameComponent` — a union-find `unionFindRootOf`-cons/freshness arc
over the shipped fuel-bounded root finder", and the FC-1 OPEN marker stressed "none of which exist over the bare
`WireState`".  This file BUILDS the mathematical heart of that arc:

  * the FRESHNESS invariant `StringWireStateFresh` (every open wire and every link endpoint is `< nextFresh`), with its
    fresh-seed base `stringInitialWireState_fresh`;
  * ★ `unionFindRoot_cons_freshAbove` — the substantive lemma: **prepending an edge whose child sits at or above a
    bound changes no root below that bound**, at MATCHED fuel.  This is the "adding a fresh edge preserves old roots"
    fact, proved by structural fuel recursion with a bounded-parent invariant (a fresh child never appears on the
    chain from a below-bound node);
  * the fresh-node root facts (`unionFindParent_none_of_notChild` / `unionFindRootOf_of_notChild`): a node that is
    nobody's child is its own root at any fuel — so a fresh leg roots to itself.

## What this LOCALIZES (the honest advance)

The SAME-FUEL cons-invariance and the fresh-is-own-root facts are the union-find plumbing FC-1 named as missing.
What they do NOT by themselves close is the FUEL NORMALIZATION: `isSameComponent` reads `unionFindRootOf`, which
fixes fuel to `links.length + 1`, so comparing a root under the extended `((fc,fp)::links)` (fuel `links.length+2`)
to the root under `links` (fuel `links.length+1`) needs one extra fuel step to be harmless — TRUE only because the
union-find is a FOREST (acyclic), which is the un-ported `ArcNonCrossingFold` / forest invariant.  So this file ships
the cons-invariance CORE and honestly walls the fuel-normalization (see the honesty markers);
`fxString_hasOrientPreservationResidual` and `fxString_hasNoLoopsTheorem` stay `false`.

Raw Lean 4 + Init; the union-find lemmas are structural list / fuel recursion, the `Bool`-equality reductions go
through private clean `Nat`/`List` helpers (public duplicates leak `propext`).  `propext`/`Quot.sound`/`Classical`/
`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private clean `Nat`/`List` helpers (public duplicates leak `propext`) -/

/-- `a ≠ b → (a == b) = false`, propext-clean (`cases` on the boolean equality decider). -/
private theorem natBeqFalseOfNe (leftNode rightNode : Nat) (notEqual : leftNode ≠ rightNode) :
    (leftNode == rightNode) = false := by
  cases beqCase : leftNode == rightNode with
  | true => exact absurd (of_decide_eq_true beqCase) notEqual
  | false => rfl

/-- Membership in `List.range.loop count accumulated` is below-`count` or in the accumulator (structural). -/
private theorem memRangeLoop : (count : Nat) → (accumulated : List Nat) → (value : Nat) →
    value ∈ List.range.loop count accumulated → value < count ∨ value ∈ accumulated
  | 0, _, _, memberOfAcc => Or.inr memberOfAcc
  | count + 1, accumulated, value, memberOfLoop => by
      have folded : value ∈ List.range.loop count (count :: accumulated) := memberOfLoop
      cases memRangeLoop count (count :: accumulated) value folded with
      | inl below => exact Or.inl (Nat.lt_succ_of_lt below)
      | inr memberOfConsAcc =>
          cases memberOfConsAcc with
          | head => exact Or.inl (Nat.lt_succ_self count)
          | tail _ memberOfAcc => exact Or.inr memberOfAcc

/-- Every element of `List.range count` is below `count` (structural, propext-clean; avoids `List.mem_range`). -/
private theorem memRangeLt (count value : Nat) (memberOfRange : value ∈ List.range count) : value < count := by
  have loopMember : value ∈ List.range.loop count [] := memberOfRange
  cases memRangeLoop count [] value loopMember with
  | inl below => exact below
  | inr memberOfNil => exact absurd memberOfNil (by intro h; cases h)

/-! ## Union-find parent facts -/

/-- Prepending an edge whose child differs from `node` leaves the parent lookup unchanged. -/
theorem unionFindParent_cons_ofChildNe (freshChild freshParent node : Nat) (links : List (Nat × Nat))
    (childBeq : (freshChild == node) = false) :
    unionFindParent ((freshChild, freshParent) :: links) node = unionFindParent links node := by
  show (if freshChild == node then some freshParent else unionFindParent links node)
    = unionFindParent links node
  cases hc : freshChild == node with
  | true => rw [hc] at childBeq; exact Bool.noConfusion childBeq
  | false => rfl

/-- If `node` is nobody's child, its parent lookup is `none`.  Structural on the edge list. -/
theorem unionFindParent_none_of_notChild (node : Nat) :
    (links : List (Nat × Nat)) → (∀ edge ∈ links, edge.1 ≠ node) → unionFindParent links node = none
  | [], _ => rfl
  | (child, parent) :: rest, notChild => by
      have childNe : child ≠ node := notChild (child, parent) (List.Mem.head _)
      have childBeq : (child == node) = false := natBeqFalseOfNe child node childNe
      rw [unionFindParent_cons_ofChildNe child parent node rest childBeq]
      exact unionFindParent_none_of_notChild node rest
        (fun edge memberOfRest => notChild edge (List.Mem.tail _ memberOfRest))

/-- A `some` parent lookup exhibits the parent among the recorded parents.  Structural on the edge list. -/
theorem unionFindParent_some_mem_snd (node : Nat) :
    (links : List (Nat × Nat)) → (parent : Nat) →
    unionFindParent links node = some parent → parent ∈ links.map Prod.snd
  | [], parent, lookupSome => by
      have lookupNone : (none : Option Nat) = some parent := lookupSome
      nomatch lookupNone
  | (child, recordedParent) :: rest, parent, lookupSome => by
      have lookupForm : (if child == node then some recordedParent else unionFindParent rest node)
          = some parent := lookupSome
      cases childBeq : child == node with
      | true =>
          rw [childBeq] at lookupForm
          have parentEq : recordedParent = parent := Option.some.inj lookupForm
          rw [← parentEq]
          exact List.Mem.head _
      | false =>
          rw [childBeq] at lookupForm
          exact List.Mem.tail _ (unionFindParent_some_mem_snd node rest parent lookupForm)

/-! ## Fresh-node root facts (a node that is nobody's child is its own root) -/

/-- With a `none` parent lookup, the fuel-bounded root of a node is the node itself, at ANY fuel. -/
theorem unionFindRoot_of_parentNone (links : List (Nat × Nat)) (node : Nat)
    (parentNone : unionFindParent links node = none) :
    (fuel : Nat) → unionFindRoot fuel links node = node
  | 0 => rfl
  | fuel + 1 => by
      show (match unionFindParent links node with
              | none => node
              | some parent => unionFindRoot fuel links parent) = node
      rw [parentNone]

/-- ★ A node that is nobody's child roots to itself (the fresh-leg fact): `unionFindRootOf links node = node`. -/
theorem unionFindRootOf_of_notChild (links : List (Nat × Nat)) (node : Nat)
    (notChild : ∀ edge ∈ links, edge.1 ≠ node) :
    unionFindRootOf links node = node :=
  unionFindRoot_of_parentNone links node (unionFindParent_none_of_notChild node links notChild)
    (links.length + 1)

/-! ## ★ The substantive lemma — a fresh edge preserves every below-bound root (matched fuel) -/

/-- ★★ **Adding an edge whose child sits at/above a bound changes no root below that bound** (matched fuel).  If
every recorded PARENT in `links` is `< bound` and `bound ≤ freshChild`, then for every `node < bound` and every
`fuel`, prepending `(freshChild, freshParent)` leaves `unionFindRoot fuel` unchanged: the chain from a below-bound
node visits only below-bound nodes (`node`, then recorded parents, all `< bound ≤ freshChild`), so it never matches
the fresh child and the extra edge is invisible.  Structural fuel recursion; the recursion's parent stays below the
bound by `unionFindParent_some_mem_snd`.  This is the "a fresh cup pair changes no old `isSameComponent`" heart FC-1
named — at fixed fuel. -/
theorem unionFindRoot_cons_freshAbove (freshChild freshParent bound : Nat) (links : List (Nat × Nat))
    (parentsBounded : ∀ parent ∈ links.map Prod.snd, parent < bound) (boundLeFresh : bound ≤ freshChild) :
    (fuel node : Nat) → node < bound →
    unionFindRoot fuel ((freshChild, freshParent) :: links) node = unionFindRoot fuel links node
  | 0, _, _ => rfl
  | fuel + 1, node, nodeBelow => by
      have nodeLtFresh : node < freshChild := Nat.lt_of_lt_of_le nodeBelow boundLeFresh
      have childBeq : (freshChild == node) = false :=
        natBeqFalseOfNe freshChild node (fun freshEqNode => Nat.lt_irrefl node (freshEqNode ▸ nodeLtFresh))
      show (match unionFindParent ((freshChild, freshParent) :: links) node with
              | none => node
              | some parent => unionFindRoot fuel ((freshChild, freshParent) :: links) parent)
            = (match unionFindParent links node with
              | none => node
              | some parent => unionFindRoot fuel links parent)
      rw [unionFindParent_cons_ofChildNe freshChild freshParent node links childBeq]
      cases lookupCase : unionFindParent links node with
      | none => rfl
      | some parent =>
          have parentBounded : parent < bound :=
            parentsBounded parent (unionFindParent_some_mem_snd node links parent lookupCase)
          show unionFindRoot fuel ((freshChild, freshParent) :: links) parent
            = unionFindRoot fuel links parent
          exact unionFindRoot_cons_freshAbove freshChild freshParent bound links parentsBounded boundLeFresh
            fuel parent parentBounded

/-! ## The freshness invariant + its fresh-seed base -/

/-- ★ **The freshness invariant.**  Every open wire and every link endpoint is a node id `< nextFresh` — so
`nextFresh` (and every id `≥ nextFresh`) is genuinely FRESH: it appears nowhere in the state.  This is the datum the
CUP-preservation subcase consumes (a fresh cup pair reads a cup word and shares no component with any old wire). -/
structure StringWireStateFresh (state : WireState) : Prop where
  /-- Every open wire is below the fresh counter. -/
  openBelow : ∀ wire ∈ state.openWires, wire < state.nextFresh
  /-- Every link endpoint (child and parent) is below the fresh counter. -/
  linksBelow : ∀ edge ∈ state.links, edge.1 < state.nextFresh ∧ edge.2 < state.nextFresh

/-- The recorded parents are all below `nextFresh` (the `unionFindRoot_cons_freshAbove` precondition, extracted). -/
theorem StringWireStateFresh_parentsBelow {state : WireState} (fresh : StringWireStateFresh state) :
    ∀ parent ∈ state.links.map Prod.snd, parent < state.nextFresh := by
  intro parent memberOfParents
  have edgeMem := mapSndMem state.links parent memberOfParents
  obtain ⟨child, edgeMemberOfLinks⟩ := edgeMem
  exact (fresh.linksBelow (child, parent) edgeMemberOfLinks).2
where
  /-- A member of `links.map Prod.snd` comes from an edge in `links`. -/
  mapSndMem : (links : List (Nat × Nat)) → (parent : Nat) → parent ∈ links.map Prod.snd →
      ∃ child, (child, parent) ∈ links
    | [], _, memberOfNil => absurd memberOfNil (by intro h; cases h)
    | (child, recordedParent) :: rest, parent, memberOfMap => by
        cases memberOfMap with
        | head => exact ⟨child, List.Mem.head _⟩
        | tail _ memberOfRest =>
            obtain ⟨childRest, edgeMemberOfRest⟩ := mapSndMem rest parent memberOfRest
            exact ⟨childRest, List.Mem.tail _ edgeMemberOfRest⟩

/-- ★ **The fresh seed satisfies the freshness invariant.**  At `stringInitialWireState bottomCount` the open wires
are `List.range bottomCount` (all `< bottomCount = nextFresh`) and there are no links (vacuous).  The base of the
CUP-preservation induction. -/
theorem stringInitialWireState_fresh (bottomCount : Nat) :
    StringWireStateFresh (stringInitialWireState bottomCount) where
  openBelow := fun wire memberOfRange => memRangeLt bottomCount wire memberOfRange
  linksBelow := fun edge memberOfNil => absurd memberOfNil (by intro h; cases h)

/-! ## The freshness invariant is preserved by a CUP step (the inductive step at a cup) -/

/-- Membership in an append is membership in one side (structural, propext-clean). -/
private theorem memAppendOr : (prefixList suffixList : List Nat) → (value : Nat) →
    value ∈ prefixList ++ suffixList → value ∈ prefixList ∨ value ∈ suffixList
  | [], _, _, memberOfSuffix => Or.inr memberOfSuffix
  | head :: rest, suffixList, value, memberOfCons => by
      have memberForm : value ∈ head :: (rest ++ suffixList) := memberOfCons
      cases memberForm with
      | head => exact Or.inl (List.Mem.head _)
      | tail _ memberOfRest =>
          cases memAppendOr rest suffixList value memberOfRest with
          | inl memberOfRestPrefix => exact Or.inl (List.Mem.tail _ memberOfRestPrefix)
          | inr memberOfSuffix => exact Or.inr memberOfSuffix

/-- Splicing a block: every member of the result is in the block or in the original list (structural). -/
theorem natListInsertAt_mem : (wires : List Nat) → (position : Nat) → (block : List Nat) → (value : Nat) →
    value ∈ natListInsertAt wires position block → value ∈ block ∨ value ∈ wires
  | wires, 0, block, value, memberOfInsert => by
      rw [natListInsertAt_eq_listInsertAt, listInsertAt_zero] at memberOfInsert
      exact memAppendOr block wires value memberOfInsert
  | [], _ + 1, block, value, memberOfInsert => Or.inl (by exact memberOfInsert)
  | head :: rest, position + 1, block, value, memberOfInsert => by
      have memberForm : value ∈ head :: natListInsertAt rest position block := memberOfInsert
      cases memberForm with
      | head => exact Or.inr (List.Mem.head _)
      | tail _ memberOfRest =>
          cases natListInsertAt_mem rest position block value memberOfRest with
          | inl memberOfBlock => exact Or.inl memberOfBlock
          | inr memberOfRestWires => exact Or.inr (List.Mem.tail _ memberOfRestWires)

/-- Joining two nodes that are ALREADY roots (each nobody's child) and are distinct prepends exactly their edge. -/
theorem unionFindJoin_freshPair (links : List (Nat × Nat)) (firstNode secondNode : Nat)
    (firstRootEq : unionFindRootOf links firstNode = firstNode)
    (secondRootEq : unionFindRootOf links secondNode = secondNode)
    (distinct : (firstNode == secondNode) = false) :
    unionFindJoin links firstNode secondNode = (firstNode, secondNode) :: links := by
  show (if unionFindRootOf links firstNode == unionFindRootOf links secondNode then links
        else (unionFindRootOf links firstNode, unionFindRootOf links secondNode) :: links)
      = (firstNode, secondNode) :: links
  rw [firstRootEq, secondRootEq]
  cases rootBeq : firstNode == secondNode with
  | true => rw [rootBeq] at distinct; exact Bool.noConfusion distinct
  | false => rfl

/-- ★★ **Freshness is preserved by a CUP step.**  `stepCup` splices the two fresh legs `nextFresh`, `nextFresh+1`
into the open wires and joins them — and since each fresh leg is nobody's child (freshness), the join prepends
exactly `(nextFresh, nextFresh+1)`.  Every new open wire is either a fresh leg (`< nextFresh+2`) or an old wire
(`< nextFresh < nextFresh+2`), and every new link endpoint is either a fresh leg or an old endpoint — so the new
state is again `StringWireStateFresh` with `nextFresh` advanced to `nextFresh+2`.  This is the inductive step at a
cup: the CUP-preservation induction's freshness leg, DISCHARGED. -/
theorem StringWireStateFresh_stepCup (state : WireState) (position : Nat)
    (fresh : StringWireStateFresh state) :
    StringWireStateFresh (stepCup state position) := by
  have freshLtTwo : state.nextFresh < state.nextFresh + 2 :=
    Nat.lt_succ_of_lt (Nat.lt_succ_self state.nextFresh)
  have freshSuccLtTwo : state.nextFresh + 1 < state.nextFresh + 2 := Nat.lt_succ_self (state.nextFresh + 1)
  have leftNotChild : ∀ edge ∈ state.links, edge.1 ≠ state.nextFresh :=
    fun edge memberOfLinks => Nat.ne_of_lt (fresh.linksBelow edge memberOfLinks).1
  have rightNotChild : ∀ edge ∈ state.links, edge.1 ≠ state.nextFresh + 1 :=
    fun edge memberOfLinks =>
      Nat.ne_of_lt (Nat.lt_trans (fresh.linksBelow edge memberOfLinks).1 (Nat.lt_succ_self state.nextFresh))
  have leftRoot : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_of_notChild state.links state.nextFresh leftNotChild
  have rightRoot : unionFindRootOf state.links (state.nextFresh + 1) = state.nextFresh + 1 :=
    unionFindRootOf_of_notChild state.links (state.nextFresh + 1) rightNotChild
  have distinct : (state.nextFresh == state.nextFresh + 1) = false :=
    natBeqFalseOfNe state.nextFresh (state.nextFresh + 1) (Nat.ne_of_lt (Nat.lt_succ_self state.nextFresh))
  have joinEq : unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
      = (state.nextFresh, state.nextFresh + 1) :: state.links :=
    unionFindJoin_freshPair state.links state.nextFresh (state.nextFresh + 1) leftRoot rightRoot distinct
  refine ⟨?_, ?_⟩
  · intro wire memberOfNew
    have memberOfInsert :
        wire ∈ natListInsertAt state.openWires position [state.nextFresh, state.nextFresh + 1] := memberOfNew
    show wire < state.nextFresh + 2
    cases natListInsertAt_mem state.openWires position [state.nextFresh, state.nextFresh + 1] wire
        memberOfInsert with
    | inl memberOfBlock =>
        cases memberOfBlock with
        | head => exact freshLtTwo
        | tail _ memberOfRestBlock =>
            cases memberOfRestBlock with
            | head => exact freshSuccLtTwo
            | tail _ memberOfNil => exact absurd memberOfNil (by intro contra; cases contra)
    | inr memberOfOld => exact Nat.lt_trans (fresh.openBelow wire memberOfOld) freshLtTwo
  · intro edge memberOfNew
    have memberOfJoin : edge ∈ unionFindJoin state.links state.nextFresh (state.nextFresh + 1) := memberOfNew
    rw [joinEq] at memberOfJoin
    show edge.1 < state.nextFresh + 2 ∧ edge.2 < state.nextFresh + 2
    cases memberOfJoin with
    | head => exact ⟨freshLtTwo, freshSuccLtTwo⟩
    | tail _ memberOfOld =>
        exact ⟨Nat.lt_trans (fresh.linksBelow edge memberOfOld).1 freshLtTwo,
          Nat.lt_trans (fresh.linksBelow edge memberOfOld).2 freshLtTwo⟩

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the union-find FRESHNESS core is shipped (the plumbing FC-1 named as missing).**  The freshness
invariant `StringWireStateFresh` (every open wire and link endpoint `< nextFresh`) is shipped with its fresh-seed base
(`stringInitialWireState_fresh`) and its parent-bound extraction (`StringWireStateFresh_parentsBelow`); the substantive
lemma `unionFindRoot_cons_freshAbove` proves that **prepending an edge whose child sits at/above a bound preserves
every root below the bound** (at matched fuel), by structural fuel recursion with the chain staying below the bound
(`unionFindParent_some_mem_snd` + `unionFindParent_cons_ofChildNe`); and the fresh-leg root facts
(`unionFindParent_none_of_notChild` / `unionFindRoot_of_parentNone` / `unionFindRootOf_of_notChild`) prove a node
that is nobody's child roots to itself at any fuel.  Finally the INDUCTIVE STEP at a cup is DISCHARGED:
`StringWireStateFresh_stepCup` proves freshness is preserved by `stepCup` (the fresh legs join to exactly
`(nextFresh, nextFresh+1)` by `unionFindJoin_freshPair`, every new open wire / link endpoint stays below the advanced
`nextFresh+2`, via `natListInsertAt_mem`).  This is exactly "the `unionFindRootOf`-cons/freshness arc over the shipped
fuel-bounded root finder" the FC-1 OPEN marker named as not existing over the bare `WireState`.  All UNCONDITIONAL,
zero-axiom.  `= true`. -/
def fxString_hasCupFreshnessKit : Bool := true

/-- **OPEN (honest, LOCALIZED) — the CUP-preservation flip owes the FUEL-NORMALIZATION (forest/acyclicity) + the
full discipline preservation.**  `unionFindRoot_cons_freshAbove` is a MATCHED-fuel fact; but `isSameComponent` reads
`unionFindRootOf`, which fixes fuel to `links.length + 1`, so lifting the cons-invariance to the actual
`isSameComponent ((freshChild,freshParent) :: links) = isSameComponent links` (on below-bound wires) needs one extra
fuel step to be harmless — TRUE only because the union-find is a FOREST (acyclic: every `unionFindJoin` points a
current ROOT at a distinct node, so no cycle forms), and the fuel bound `links.length + 1` then always reaches a
root.  That acyclicity is the un-ported `ArcNonCrossingFold` / forest invariant.  With it, CUP-preservation of the
strand discipline closes (fresh pair reads the cup's cod word, shares no old component); without it the fuel gap
stands.  And the CAP half of `preserves` still owes the planar survivor P4 (genuinely-new).  So
`fxString_hasOrientPreservationResidual` and `fxString_hasNoLoopsTheorem` STAY `false`, honestly, with the frontier
moved: the fresh-edge root-preservation heart is SHIPPED, the residual is fuel-normalization (forest) + CAP planar
survivor P4.  `= false`. -/
def fxString_hasCupPreservationFromFreshness : Bool := false

end FX1Poly.Polygraph
