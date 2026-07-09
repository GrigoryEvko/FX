import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanForest

/-! # WalkingString — the CUP orientation-preservation heart (FC-3b, CUP case)

FC-3b's `StringFussCatalanForest` CLOSED residual (i): on a forest, a fresh cup edge changes no below-bound
`isSameComponent`.  This file uses that to build the CONNECTIVITY HEART of the CUP case of `preserves` — the
"a fresh cup pair is same-component with each other but with NO old wire" isolation — and assembles the CUP case of
the orientation discipline:

  * ★ `stringUnionFindRoot_lt_of_linksBelow` / `…RootOf…` — a root stays below any bound the link endpoints respect
    (the chain visits only recorded parents);
  * ★ `stringUnionFindRootOf_freshLeftLeg` — the fresh LEFT leg roots to the fresh right leg (the head edge redirects
    it), `…freshRightLeg` — the fresh RIGHT leg is its own root;
  * ★★ `stringFreshLeg_not_sameComponent_old` — a fresh leg is NOT same-component with any old (below-bound) wire
    (its root is `≥ nextFresh`, the old root is `< nextFresh`);
  * the read helpers (`stringStepCup_openWires_read_*`, `stringAdvanceLabels_read_*`) via the shipped L1–L3 kit;
  * ★★ `stringOrientationDiscipline_stepCup` — the CUP case of `preserves`, UNCONDITIONAL given the state's freshness
    + forest + the cup's cod word being an ordered cup word.

Raw Lean 4 + Init; the connectivity is structural fuel recursion (private `Nat`/beq helpers where the public name
leaks `propext`), the reads are the generic index-shift kit, the orient assembly is a region case split.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private clean `Nat`/beq helpers -/

/-- `(value == value) = true` (`Nat.beq` does not reduce on `succ` for the elaborator, so this routes through the
`decide`-form, which IS `propext`-clean here — the codebase idiom). -/
private theorem natBeqSelfCup (value : Nat) : (value == value) = true := decide_eq_true rfl

/-- `a ≠ b → (a == b) = false`, propext-clean. -/
private theorem natBeqFalseOfNeCup (leftNode rightNode : Nat) (notEqual : leftNode ≠ rightNode) :
    (leftNode == rightNode) = false := by
  cases beqCase : leftNode == rightNode with
  | true => exact absurd (of_decide_eq_true beqCase) notEqual
  | false => rfl

/-! ## Root-below-bound: a root visits only recorded parents -/

/-- ★ **A root stays below any bound the recorded parents respect.**  Following parent edges from a below-bound node
visits only recorded parents (each `< bound` by hypothesis) or stops at the node itself, so the root is `< bound`.
Structural fuel recursion; the parent-membership goes through the shipped `unionFindParent_some_mem_snd`. -/
theorem stringUnionFindRoot_lt_of_linksBelow (bound : Nat) (links : List (Nat × Nat))
    (parentsBounded : ∀ parent ∈ links.map Prod.snd, parent < bound) :
    (fuel node : Nat) → node < bound → unionFindRoot fuel links node < bound
  | 0, node, nodeBelow => nodeBelow
  | fuel + 1, node, nodeBelow => by
      show (match unionFindParent links node with
            | none => node | some parent => unionFindRoot fuel links parent) < bound
      cases hp : unionFindParent links node with
      | none => exact nodeBelow
      | some parent =>
          have parentBelow : parent < bound :=
            parentsBounded parent (unionFindParent_some_mem_snd node links parent hp)
          exact stringUnionFindRoot_lt_of_linksBelow bound links parentsBounded fuel parent parentBelow

/-- A below-bound node's `unionFindRootOf` is below the bound. -/
theorem stringUnionFindRootOf_lt_of_linksBelow (bound : Nat) (links : List (Nat × Nat))
    (parentsBounded : ∀ parent ∈ links.map Prod.snd, parent < bound) (node : Nat) (nodeBelow : node < bound) :
    unionFindRootOf links node < bound :=
  stringUnionFindRoot_lt_of_linksBelow bound links parentsBounded (links.length + 1) node nodeBelow

/-! ## The fresh-leg roots after the cup join -/

/-- The consed fresh edge leaves the RIGHT leg parentless (`freshRight` is nobody's child in `links`, and the head
child `freshLeft ≠ freshRight`). -/
theorem stringFreshRightLeg_parentless_cons (freshLeft freshRight : Nat) (links : List (Nat × Nat))
    (distinctLR : (freshLeft == freshRight) = false) (rightNotChild : unionFindParent links freshRight = none) :
    unionFindParent ((freshLeft, freshRight) :: links) freshRight = none := by
  rw [unionFindParent_cons_ofChildNe freshLeft freshRight freshRight links distinctLR]
  exact rightNotChild

/-- ★ **The fresh RIGHT leg is its own root after the join.** -/
theorem stringUnionFindRootOf_freshRightLeg (freshLeft freshRight : Nat) (links : List (Nat × Nat))
    (distinctLR : (freshLeft == freshRight) = false) (rightNotChild : unionFindParent links freshRight = none) :
    unionFindRootOf ((freshLeft, freshRight) :: links) freshRight = freshRight :=
  unionFindRoot_of_parentNone ((freshLeft, freshRight) :: links) freshRight
    (stringFreshRightLeg_parentless_cons freshLeft freshRight links distinctLR rightNotChild)
    (((freshLeft, freshRight) :: links).length + 1)

/-- ★ **The fresh LEFT leg roots to the fresh RIGHT leg after the join.**  The head edge `(freshLeft, freshRight)`
gives `freshLeft` the parent `freshRight`, which is itself a root — so the left leg's root is the right leg. -/
theorem stringUnionFindRootOf_freshLeftLeg (freshLeft freshRight : Nat) (links : List (Nat × Nat))
    (distinctLR : (freshLeft == freshRight) = false) (rightNotChild : unionFindParent links freshRight = none) :
    unionFindRootOf ((freshLeft, freshRight) :: links) freshLeft = freshRight := by
  show unionFindRoot (links.length + 2) ((freshLeft, freshRight) :: links) freshLeft = freshRight
  have parentLeft : unionFindParent ((freshLeft, freshRight) :: links) freshLeft = some freshRight := by
    show (if freshLeft == freshLeft then some freshRight else unionFindParent links freshLeft) = some freshRight
    exact if_pos (natBeqSelfCup freshLeft)
  show (match unionFindParent ((freshLeft, freshRight) :: links) freshLeft with
        | none => freshLeft | some parent => unionFindRoot (links.length + 1) ((freshLeft, freshRight) :: links) parent)
      = freshRight
  rw [parentLeft]
  exact unionFindRoot_of_parentNone ((freshLeft, freshRight) :: links) freshRight
    (stringFreshRightLeg_parentless_cons freshLeft freshRight links distinctLR rightNotChild)
    (links.length + 1)

/-! ## The fresh legs are same-component with each other, isolated from old wires -/

/-- ★★ **The fresh cup pair is SAME-component.**  Both legs root to the fresh right leg (`freshLeft ↦ freshRight`,
`freshRight ↦ freshRight`), so `isSameComponent` reads `true`. -/
theorem stringFreshPair_sameComponent (freshLeft freshRight : Nat) (links : List (Nat × Nat))
    (distinctLR : (freshLeft == freshRight) = false) (rightNotChild : unionFindParent links freshRight = none) :
    isSameComponent ((freshLeft, freshRight) :: links) freshLeft freshRight = true := by
  show (unionFindRootOf ((freshLeft, freshRight) :: links) freshLeft
        == unionFindRootOf ((freshLeft, freshRight) :: links) freshRight) = true
  rw [stringUnionFindRootOf_freshLeftLeg freshLeft freshRight links distinctLR rightNotChild,
    stringUnionFindRootOf_freshRightLeg freshLeft freshRight links distinctLR rightNotChild]
  exact natBeqSelfCup freshRight

/-- ★★ **A fresh leg (LEFT argument) is NOT same-component with an old (below-bound) wire.**  The fresh leg's root is
`freshRight ≥ bound`, while the old wire's root is `< bound` (`stringUnionFindRootOf_lt_of_linksBelow`, and residual
(i) leaves it unchanged under the fresh edge) — so the two roots differ. -/
theorem stringFreshLeg_not_sameComponent_old (freshLeft freshRight bound freshLeg oldWire : Nat)
    (links : List (Nat × Nat))
    (parentsBounded : ∀ parent ∈ links.map Prod.snd, parent < bound) (boundLeFresh : bound ≤ freshLeft)
    (hforest : stringIsUnionFindForest links)
    (freshLegRootEq : unionFindRootOf ((freshLeft, freshRight) :: links) freshLeg = freshRight)
    (boundLeRight : bound ≤ freshRight) (oldBelow : oldWire < bound) :
    isSameComponent ((freshLeft, freshRight) :: links) freshLeg oldWire = false := by
  show (unionFindRootOf ((freshLeft, freshRight) :: links) freshLeg
        == unionFindRootOf ((freshLeft, freshRight) :: links) oldWire) = false
  rw [freshLegRootEq,
    stringUnionFindRootOf_cons_freshAbove_forest freshLeft freshRight bound links parentsBounded boundLeFresh
      hforest oldWire oldBelow]
  have oldRootBelow : unionFindRootOf links oldWire < bound :=
    stringUnionFindRootOf_lt_of_linksBelow bound links parentsBounded oldWire oldBelow
  exact natBeqFalseOfNeCup freshRight (unionFindRootOf links oldWire)
    (Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le oldRootBelow boundLeRight)))

/-- ★★ **A fresh leg (RIGHT argument) is NOT same-component with an old (below-bound) wire** — the swapped-argument
form, computing the root beq in the old-on-left order (avoids a beq-commutativity detour). -/
theorem stringOld_not_sameComponent_freshLeg (freshLeft freshRight bound freshLeg oldWire : Nat)
    (links : List (Nat × Nat))
    (parentsBounded : ∀ parent ∈ links.map Prod.snd, parent < bound) (boundLeFresh : bound ≤ freshLeft)
    (hforest : stringIsUnionFindForest links)
    (freshLegRootEq : unionFindRootOf ((freshLeft, freshRight) :: links) freshLeg = freshRight)
    (boundLeRight : bound ≤ freshRight) (oldBelow : oldWire < bound) :
    isSameComponent ((freshLeft, freshRight) :: links) oldWire freshLeg = false := by
  show (unionFindRootOf ((freshLeft, freshRight) :: links) oldWire
        == unionFindRootOf ((freshLeft, freshRight) :: links) freshLeg) = false
  rw [freshLegRootEq,
    stringUnionFindRootOf_cons_freshAbove_forest freshLeft freshRight bound links parentsBounded boundLeFresh
      hforest oldWire oldBelow]
  have oldRootBelow : unionFindRootOf links oldWire < bound :=
    stringUnionFindRootOf_lt_of_linksBelow bound links parentsBounded oldWire oldBelow
  exact natBeqFalseOfNeCup (unionFindRootOf links oldWire) freshRight
    (Nat.ne_of_lt (Nat.lt_of_lt_of_le oldRootBelow boundLeRight))

/-! ## Private helpers: membership + a `succ - self` -/

/-- An in-range `natListGetAt` read is a genuine list member (so freshness bounds it). -/
private theorem natListGetAtMemCup : (wires : List Nat) → (index : Nat) → index < wires.length →
    natListGetAt wires index ∈ wires
  | [], index, hindex => absurd hindex (Nat.not_lt_zero index)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, hindex => List.Mem.tail _ (natListGetAtMemCup rest index (Nat.lt_of_succ_lt_succ hindex))

/-- `(value + 1) - value = 1`, propext-clean. -/
private theorem natSuccSubSelfCup : (value : Nat) → (value + 1) - value = 1
  | 0 => rfl
  | value + 1 => by
      show (value + 1 + 1) - (value + 1) = 1
      rw [Nat.succ_sub_succ]; exact natSuccSubSelfCup value

/-! ## The wire / label reads across the cup splice (via the shipped L1–L3 kit) -/

/-- **Wire read, BELOW the splice.**  An open-wire index below the insertion point reads the OLD wire. -/
theorem stringStepCup_openWires_read_below (state : WireState) (position index : Nat)
    (positionInRange : position ≤ state.openWires.length) (below : index < position) :
    natListGetAt (stepCup state position).openWires index = natListGetAt state.openWires index := by
  show natListGetAt (natListInsertAt state.openWires position [state.nextFresh, state.nextFresh + 1]) index
    = natListGetAt state.openWires index
  rw [natListGetAt_eq_listGetAtD, natListInsertAt_eq_listInsertAt, natListGetAt_eq_listGetAtD]
  exact listGetAtD_insertAt_below 0 state.openWires position [state.nextFresh, state.nextFresh + 1] index
    positionInRange below

/-- **Wire read, LEFT block leg.**  The index at the splice point reads the fresh left leg `nextFresh`. -/
theorem stringStepCup_openWires_read_blockLow (state : WireState) (position : Nat)
    (positionInRange : position ≤ state.openWires.length) :
    natListGetAt (stepCup state position).openWires position = state.nextFresh := by
  show natListGetAt (natListInsertAt state.openWires position [state.nextFresh, state.nextFresh + 1]) position
    = state.nextFresh
  rw [natListGetAt_eq_listGetAtD, natListInsertAt_eq_listInsertAt,
    listGetAtD_insertAt_block 0 state.openWires position [state.nextFresh, state.nextFresh + 1] position
      positionInRange (Nat.le_refl position) (Nat.lt_succ_of_lt (Nat.lt_succ_self position)),
    Nat.sub_self]
  rfl

/-- **Wire read, RIGHT block leg.**  The index at `position + 1` reads the fresh right leg `nextFresh + 1`. -/
theorem stringStepCup_openWires_read_blockHigh (state : WireState) (position : Nat)
    (positionInRange : position ≤ state.openWires.length) :
    natListGetAt (stepCup state position).openWires (position + 1) = state.nextFresh + 1 := by
  show natListGetAt (natListInsertAt state.openWires position [state.nextFresh, state.nextFresh + 1]) (position + 1)
    = state.nextFresh + 1
  rw [natListGetAt_eq_listGetAtD, natListInsertAt_eq_listInsertAt,
    listGetAtD_insertAt_block 0 state.openWires position [state.nextFresh, state.nextFresh + 1] (position + 1)
      positionInRange (Nat.le_succ position) (Nat.succ_lt_succ (Nat.lt_succ_self position)),
    natSuccSubSelfCup position]
  rfl

/-- **Wire read, ABOVE the splice.**  An index at/above `position + 2` reads the OLD wire shifted down by 2. -/
theorem stringStepCup_openWires_read_above (state : WireState) (position index : Nat)
    (positionInRange : position ≤ state.openWires.length) (above : position + 2 ≤ index) :
    natListGetAt (stepCup state position).openWires index = natListGetAt state.openWires (index - 2) := by
  show natListGetAt (natListInsertAt state.openWires position [state.nextFresh, state.nextFresh + 1]) index
    = natListGetAt state.openWires (index - 2)
  rw [natListGetAt_eq_listGetAtD, natListInsertAt_eq_listInsertAt, natListGetAt_eq_listGetAtD]
  exact listGetAtD_insertAt_above 0 state.openWires position [state.nextFresh, state.nextFresh + 1] index
    positionInRange above

/-- **Label read, BELOW the splice.** -/
theorem stringAdvanceLabels_read_below (labels : List WireLabel) (position index : Nat) (labelL labelR : WireLabel)
    (positionInRange : position ≤ labels.length) (below : index < position) :
    wireLabelListGetAt (wireLabelListInsertAt labels position [labelL, labelR]) index = wireLabelListGetAt labels index := by
  rw [wireLabelListGetAt_eq_listGetAtD, wireLabelListGetAt_eq_listGetAtD]
  exact listGetAtD_insertAt_below WireLabel.gWire labels position [labelL, labelR] index positionInRange below

/-- **Label read, LEFT block leg.** -/
theorem stringAdvanceLabels_read_blockLow (labels : List WireLabel) (position : Nat) (labelL labelR : WireLabel)
    (positionInRange : position ≤ labels.length) :
    wireLabelListGetAt (wireLabelListInsertAt labels position [labelL, labelR]) position = labelL := by
  rw [wireLabelListGetAt_eq_listGetAtD]
  show listGetAtD WireLabel.gWire (listInsertAt labels position [labelL, labelR]) position = labelL
  rw [listGetAtD_insertAt_block WireLabel.gWire labels position [labelL, labelR] position
      positionInRange (Nat.le_refl position) (Nat.lt_succ_of_lt (Nat.lt_succ_self position)),
    Nat.sub_self]
  rfl

/-- **Label read, RIGHT block leg.** -/
theorem stringAdvanceLabels_read_blockHigh (labels : List WireLabel) (position : Nat) (labelL labelR : WireLabel)
    (positionInRange : position ≤ labels.length) :
    wireLabelListGetAt (wireLabelListInsertAt labels position [labelL, labelR]) (position + 1) = labelR := by
  rw [wireLabelListGetAt_eq_listGetAtD]
  show listGetAtD WireLabel.gWire (listInsertAt labels position [labelL, labelR]) (position + 1) = labelR
  rw [listGetAtD_insertAt_block WireLabel.gWire labels position [labelL, labelR] (position + 1)
      positionInRange (Nat.le_succ position) (Nat.succ_lt_succ (Nat.lt_succ_self position)),
    natSuccSubSelfCup position]
  rfl

/-- **Label read, ABOVE the splice.** -/
theorem stringAdvanceLabels_read_above (labels : List WireLabel) (position index : Nat) (labelL labelR : WireLabel)
    (positionInRange : position ≤ labels.length) (above : position + 2 ≤ index) :
    wireLabelListGetAt (wireLabelListInsertAt labels position [labelL, labelR]) index = wireLabelListGetAt labels (index - 2) := by
  rw [wireLabelListGetAt_eq_listGetAtD, wireLabelListGetAt_eq_listGetAtD]
  exact listGetAtD_insertAt_above WireLabel.gWire labels position [labelL, labelR] index positionInRange above

/-! ## The cup links equality — after a fresh join, `links` is exactly the fresh edge consed on -/

/-- ★ **After a CUP, the links are the fresh edge consed on the old links.**  The two fresh legs are already roots
(nobody's child, by freshness) and distinct, so `unionFindJoin` prepends exactly `(nextFresh, nextFresh+1)`.  This
brings `(stepCup state position).links` into the `((freshChild, freshParent) :: links)` shape all the connectivity
lemmas (and residual (i)) are stated over. -/
theorem stringStepCup_links_eq (state : WireState) (position : Nat) (fresh : StringWireStateFresh state) :
    (stepCup state position).links = (state.nextFresh, state.nextFresh + 1) :: state.links := by
  show unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
    = (state.nextFresh, state.nextFresh + 1) :: state.links
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
    natBeqFalseOfNeCup state.nextFresh (state.nextFresh + 1) (Nat.ne_of_lt (Nat.lt_succ_self state.nextFresh))
  exact unionFindJoin_freshPair state.links state.nextFresh (state.nextFresh + 1) leftRoot rightRoot distinct

/-! ## Region classification + `Nat` subtraction helpers -/

/-- A position relative to the cup's insertion point falls in exactly one of four regions: strictly below, the left
fresh leg (`= position`), the right fresh leg (`= position + 1`), or strictly above the 2-block. -/
private theorem cupRegion (position index : Nat) :
    index < position ∨ index = position ∨ index = position + 1 ∨ position + 2 ≤ index := by
  rcases Nat.lt_trichotomy index position with below | atLow | above
  · exact Or.inl below
  · exact Or.inr (Or.inl atLow)
  · rcases Nat.lt_or_ge index (position + 2) with inBlock | aboveBlock
    · exact Or.inr (Or.inr (Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ inBlock) above)))
    · exact Or.inr (Or.inr (Or.inr aboveBlock))

/-- `2 ≤ value → value - 2 + 2 = value`, propext-clean (`value - 2` reduces definitionally on `value + 2`). -/
private theorem natSubAddTwoCup : (value : Nat) → 2 ≤ value → value - 2 + 2 = value
  | 0, twoLe => absurd twoLe (Nat.not_succ_le_zero 1)
  | 1, twoLe => absurd (Nat.le_of_succ_le_succ twoLe) (Nat.not_succ_le_zero 0)
  | _ + 2, _ => rfl

/-- `value < bound + 2 → 2 ≤ value → value - 2 < bound`, propext-clean. -/
private theorem natSubTwoLtBoundCup (value bound : Nat) (valueGe : 2 ≤ value) (valueLt : value < bound + 2) :
    value - 2 < bound := by
  have addBack : value - 2 + 2 = value := natSubAddTwoCup value valueGe
  have step : value - 2 + 2 < bound + 2 := by rw [addBack]; exact valueLt
  exact Nat.lt_of_add_lt_add_right step

/-- `smaller < larger → 2 ≤ smaller → 2 ≤ larger → smaller - 2 < larger - 2`, propext-clean. -/
private theorem natSubTwoLtCup (smaller larger : Nat) (smallGe : 2 ≤ smaller) (largeGe : 2 ≤ larger)
    (smallLtLarge : smaller < larger) : smaller - 2 < larger - 2 := by
  have addSmall : smaller - 2 + 2 = smaller := natSubAddTwoCup smaller smallGe
  have addLarge : larger - 2 + 2 = larger := natSubAddTwoCup larger largeGe
  have step : smaller - 2 + 2 < larger - 2 + 2 := by rw [addSmall, addLarge]; exact smallLtLarge
  exact Nat.lt_of_add_lt_add_right step

/-- `position + 2 ≤ index → 2 ≤ index` (the fresh-block floor). -/
private theorem twoLeOfBlockAbove (position index : Nat) (above : position + 2 ≤ index) : 2 ≤ index :=
  Nat.le_trans (Nat.le_add_left 2 position) above

/-- `leftV + addend ≤ rightV + addend → leftV ≤ rightV`, propext-clean (structural on `addend`; the shipped
`Nat.le_of_add_le_add_right` leaks `propext`). -/
private theorem natLeOfAddLeAddRightCup : (addend leftV rightV : Nat) →
    leftV + addend ≤ rightV + addend → leftV ≤ rightV
  | 0, _, _, cancelled => cancelled
  | addend + 1, leftV, rightV, shifted =>
      natLeOfAddLeAddRightCup addend leftV rightV (Nat.le_of_succ_le_succ shifted)

/-! ## The both-old reduction — an old-old same-component pair reads a cup word by the old discipline -/

/-- ★★ **A same-component pair of OLD wires (below `nextFresh`) reads a cup word.**  Residual (i)
(`stringIsSameComponent_cons_freshAbove_forest`) strips the fresh cup edge, so the pair is same-component in the OLD
links; the old discipline's `orient` then delivers the cup word.  This is the shared engine of the three both-old
region combinations (below/below, below/above, above/above) in the CUP orient case. -/
theorem stringCupOrient_oldPair (state : WireState) (labels : List WireLabel)
    (fresh : StringWireStateFresh state) (hforest : stringIsUnionFindForest state.links)
    (discipline : StringOrientationDiscipline state labels)
    (oldLow oldHigh : Nat) (oldLowLtHigh : oldLow < oldHigh) (oldHighLt : oldHigh < state.openWires.length)
    (sameNew : isSameComponent ((state.nextFresh, state.nextFresh + 1) :: state.links)
        (natListGetAt state.openWires oldLow) (natListGetAt state.openWires oldHigh) = true) :
    isCupWordOrdered (wireLabelListGetAt labels oldLow) (wireLabelListGetAt labels oldHigh) = true := by
  have oldLowLt : oldLow < state.openWires.length := Nat.lt_trans oldLowLtHigh oldHighLt
  have lowMem : natListGetAt state.openWires oldLow ∈ state.openWires :=
    natListGetAtMemCup state.openWires oldLow oldLowLt
  have highMem : natListGetAt state.openWires oldHigh ∈ state.openWires :=
    natListGetAtMemCup state.openWires oldHigh oldHighLt
  have lowBelow : natListGetAt state.openWires oldLow < state.nextFresh := fresh.openBelow _ lowMem
  have highBelow : natListGetAt state.openWires oldHigh < state.nextFresh := fresh.openBelow _ highMem
  have parentsBounded := StringWireStateFresh_parentsBelow fresh
  have consEq := stringIsSameComponent_cons_freshAbove_forest state.nextFresh (state.nextFresh + 1)
    state.nextFresh state.links parentsBounded (Nat.le_refl _) hforest
    (natListGetAt state.openWires oldLow) (natListGetAt state.openWires oldHigh) lowBelow highBelow
  rw [consEq] at sameNew
  exact discipline.orient oldLow oldHigh oldLowLtHigh oldHighLt sameNew

/-! ## ★★ The CUP case of `preserves` -/

/-- ★★ **The CUP case of the orientation-discipline fold invariance.**  After `stepCup` at `position` splicing the
fresh cup pair with cod labels `[labelL, labelR]` (an ordered cup word), the strand-orientation discipline is
preserved — GIVEN the state's freshness (`StringWireStateFresh`) and forest (`stringIsUnionFindForest`).  The
`sameLengths` half is `stringAdvanceLabels_sameLengths_cup`; the `orient` half classifies both open positions into
four cup regions (below the block, the two fresh legs, above the block) and discharges the sixteen combinations:
both-old pairs reduce to the old discipline via residual (i) (`stringCupOrient_oldPair`), the two fresh legs read the
cup's cod word (an ordered cup word by `codIsCupWord`), and every mixed (old + fresh) pair is refuted as
non-same-component (a fresh leg roots to `nextFresh+1 ≥ nextFresh`, an old wire below `nextFresh`).  This is the CUP
half of the `preserves` residual FC-1 named, CLOSED unconditionally (given freshness + forest, which the fold carries). -/
theorem stringOrientationDiscipline_stepCup (state : WireState) (labels : List WireLabel) (position : Nat)
    (labelL labelR : WireLabel) (positionInRange : position ≤ state.openWires.length)
    (fresh : StringWireStateFresh state) (hforest : stringIsUnionFindForest state.links)
    (discipline : StringOrientationDiscipline state labels)
    (codIsCupWord : isCupWordOrdered labelL labelR = true) :
    StringOrientationDiscipline (stepCup state position)
      (wireLabelListInsertAt labels position [labelL, labelR]) := by
  have positionLabelInRange : position ≤ labels.length := discipline.sameLengths.symm ▸ positionInRange
  have linksEq : (stepCup state position).links = (state.nextFresh, state.nextFresh + 1) :: state.links :=
    stringStepCup_links_eq state position fresh
  have parentsBounded := StringWireStateFresh_parentsBelow fresh
  have rightNotChildParent : unionFindParent state.links (state.nextFresh + 1) = none :=
    unionFindParent_none_of_notChild (state.nextFresh + 1) state.links
      (fun edge memberOfLinks =>
        Nat.ne_of_lt (Nat.lt_trans (fresh.linksBelow edge memberOfLinks).1 (Nat.lt_succ_self state.nextFresh)))
  have distinctLR : (state.nextFresh == state.nextFresh + 1) = false :=
    natBeqFalseOfNeCup state.nextFresh (state.nextFresh + 1) (Nat.ne_of_lt (Nat.lt_succ_self state.nextFresh))
  have leftRootEq : unionFindRootOf ((state.nextFresh, state.nextFresh + 1) :: state.links) state.nextFresh
      = state.nextFresh + 1 :=
    stringUnionFindRootOf_freshLeftLeg state.nextFresh (state.nextFresh + 1) state.links distinctLR
      rightNotChildParent
  have rightRootEq : unionFindRootOf ((state.nextFresh, state.nextFresh + 1) :: state.links) (state.nextFresh + 1)
      = state.nextFresh + 1 :=
    stringUnionFindRootOf_freshRightLeg state.nextFresh (state.nextFresh + 1) state.links distinctLR
      rightNotChildParent
  have newLenEq : (stepCup state position).openWires.length = state.openWires.length + 2 :=
    stringStepCup_openWires_length state position positionInRange
  refine ⟨?_, ?_⟩
  · exact stringAdvanceLabels_sameLengths_cup state labels [labelL, labelR] position positionInRange rfl
      discipline.sameLengths
  · intro lowPos highPos lowPosLtHigh highLtNew sameTrue
    have highLt2 : highPos < state.openWires.length + 2 := newLenEq ▸ highLtNew
    rcases cupRegion position lowPos with hLow | hLow | hLow | hLow <;>
      rcases cupRegion position highPos with hHigh | hHigh | hHigh | hHigh
    -- (below, below)
    · have readLow := stringStepCup_openWires_read_below state position lowPos positionInRange hLow
      have readHigh := stringStepCup_openWires_read_below state position highPos positionInRange hHigh
      rw [linksEq, readLow, readHigh] at sameTrue
      have highLtOld : highPos < state.openWires.length := Nat.lt_of_lt_of_le hHigh positionInRange
      have labelLow := stringAdvanceLabels_read_below labels position lowPos labelL labelR
        positionLabelInRange hLow
      have labelHigh := stringAdvanceLabels_read_below labels position highPos labelL labelR
        positionLabelInRange hHigh
      rw [labelLow, labelHigh]
      exact stringCupOrient_oldPair state labels fresh hforest discipline lowPos highPos lowPosLtHigh
        highLtOld sameTrue
    -- (below, eqLow): mixed
    · have readLow := stringStepCup_openWires_read_below state position lowPos positionInRange hLow
      have readHigh := stringStepCup_openWires_read_blockLow state position positionInRange
      have lowLtOld : lowPos < state.openWires.length := Nat.lt_of_lt_of_le hLow positionInRange
      have lowBelow : natListGetAt state.openWires lowPos < state.nextFresh :=
        fresh.openBelow _ (natListGetAtMemCup state.openWires lowPos lowLtOld)
      rw [linksEq, readLow, hHigh, readHigh] at sameTrue
      have notSame := stringOld_not_sameComponent_freshLeg state.nextFresh (state.nextFresh + 1) state.nextFresh
        state.nextFresh (natListGetAt state.openWires lowPos) state.links parentsBounded (Nat.le_refl _)
        hforest leftRootEq (Nat.le_succ _) lowBelow
      rw [notSame] at sameTrue
      exact Bool.noConfusion sameTrue
    -- (below, eqHigh): mixed
    · have readLow := stringStepCup_openWires_read_below state position lowPos positionInRange hLow
      have readHigh := stringStepCup_openWires_read_blockHigh state position positionInRange
      have lowLtOld : lowPos < state.openWires.length := Nat.lt_of_lt_of_le hLow positionInRange
      have lowBelow : natListGetAt state.openWires lowPos < state.nextFresh :=
        fresh.openBelow _ (natListGetAtMemCup state.openWires lowPos lowLtOld)
      rw [linksEq, readLow, hHigh, readHigh] at sameTrue
      have notSame := stringOld_not_sameComponent_freshLeg state.nextFresh (state.nextFresh + 1) state.nextFresh
        (state.nextFresh + 1) (natListGetAt state.openWires lowPos) state.links parentsBounded (Nat.le_refl _)
        hforest rightRootEq (Nat.le_succ _) lowBelow
      rw [notSame] at sameTrue
      exact Bool.noConfusion sameTrue
    -- (below, above)
    · have readLow := stringStepCup_openWires_read_below state position lowPos positionInRange hLow
      have readHigh := stringStepCup_openWires_read_above state position highPos positionInRange hHigh
      rw [linksEq, readLow, readHigh] at sameTrue
      have twoLeHigh : 2 ≤ highPos := twoLeOfBlockAbove position highPos hHigh
      have highSubLt : highPos - 2 < state.openWires.length := natSubTwoLtBoundCup highPos _ twoLeHigh highLt2
      have addBack : highPos - 2 + 2 = highPos := natSubAddTwoCup highPos twoLeHigh
      have posLeHighSub : position ≤ highPos - 2 :=
        natLeOfAddLeAddRightCup 2 position (highPos - 2) (by rw [addBack]; exact hHigh)
      have lowLtHighSub : lowPos < highPos - 2 := Nat.lt_of_lt_of_le hLow posLeHighSub
      have labelLow := stringAdvanceLabels_read_below labels position lowPos labelL labelR
        positionLabelInRange hLow
      have labelHigh := stringAdvanceLabels_read_above labels position highPos labelL labelR
        positionLabelInRange hHigh
      rw [labelLow, labelHigh]
      exact stringCupOrient_oldPair state labels fresh hforest discipline lowPos (highPos - 2) lowLtHighSub
        highSubLt sameTrue
    -- (eqLow, below): impossible
    · exact absurd (Nat.lt_trans (Nat.lt_of_lt_of_le hHigh (Nat.le_of_eq hLow.symm)) lowPosLtHigh)
        (Nat.lt_irrefl highPos)
    -- (eqLow, eqLow): impossible
    · rw [hLow, hHigh] at lowPosLtHigh
      exact absurd lowPosLtHigh (Nat.lt_irrefl position)
    -- (eqLow, eqHigh): the FRESH PAIR
    · have labelLow := stringAdvanceLabels_read_blockLow labels position labelL labelR positionLabelInRange
      have labelHigh := stringAdvanceLabels_read_blockHigh labels position labelL labelR positionLabelInRange
      rw [hLow, hHigh, labelLow, labelHigh]
      exact codIsCupWord
    -- (eqLow, above): mixed
    · have readLow := stringStepCup_openWires_read_blockLow state position positionInRange
      have readHigh := stringStepCup_openWires_read_above state position highPos positionInRange hHigh
      have twoLeHigh : 2 ≤ highPos := twoLeOfBlockAbove position highPos hHigh
      have highSubLt : highPos - 2 < state.openWires.length := natSubTwoLtBoundCup highPos _ twoLeHigh highLt2
      have highBelow : natListGetAt state.openWires (highPos - 2) < state.nextFresh :=
        fresh.openBelow _ (natListGetAtMemCup state.openWires (highPos - 2) highSubLt)
      rw [linksEq, hLow, readLow, readHigh] at sameTrue
      have notSame := stringFreshLeg_not_sameComponent_old state.nextFresh (state.nextFresh + 1) state.nextFresh
        state.nextFresh (natListGetAt state.openWires (highPos - 2)) state.links parentsBounded (Nat.le_refl _)
        hforest leftRootEq (Nat.le_succ _) highBelow
      rw [notSame] at sameTrue
      exact Bool.noConfusion sameTrue
    -- (eqHigh, below): impossible
    · rw [hLow] at lowPosLtHigh
      exact absurd (Nat.lt_trans (Nat.lt_succ_self position) (Nat.lt_trans lowPosLtHigh hHigh))
        (Nat.lt_irrefl position)
    -- (eqHigh, eqLow): impossible
    · rw [hLow, hHigh] at lowPosLtHigh
      exact absurd (Nat.lt_trans (Nat.lt_succ_self position) lowPosLtHigh) (Nat.lt_irrefl position)
    -- (eqHigh, eqHigh): impossible
    · rw [hLow, hHigh] at lowPosLtHigh
      exact absurd lowPosLtHigh (Nat.lt_irrefl (position + 1))
    -- (eqHigh, above): mixed
    · have readLow := stringStepCup_openWires_read_blockHigh state position positionInRange
      have readHigh := stringStepCup_openWires_read_above state position highPos positionInRange hHigh
      have twoLeHigh : 2 ≤ highPos := twoLeOfBlockAbove position highPos hHigh
      have highSubLt : highPos - 2 < state.openWires.length := natSubTwoLtBoundCup highPos _ twoLeHigh highLt2
      have highBelow : natListGetAt state.openWires (highPos - 2) < state.nextFresh :=
        fresh.openBelow _ (natListGetAtMemCup state.openWires (highPos - 2) highSubLt)
      rw [linksEq, hLow, readLow, readHigh] at sameTrue
      have notSame := stringFreshLeg_not_sameComponent_old state.nextFresh (state.nextFresh + 1) state.nextFresh
        (state.nextFresh + 1) (natListGetAt state.openWires (highPos - 2)) state.links parentsBounded (Nat.le_refl _)
        hforest rightRootEq (Nat.le_succ _) highBelow
      rw [notSame] at sameTrue
      exact Bool.noConfusion sameTrue
    -- (above, below): impossible
    · have lowGe : position + 2 ≤ lowPos := hLow
      have highLtBlock : highPos < position := hHigh
      exact absurd (Nat.lt_trans lowPosLtHigh (Nat.lt_of_lt_of_le highLtBlock
        (Nat.le_trans (Nat.le_add_right position 2) lowGe))) (Nat.lt_irrefl lowPos)
    -- (above, eqLow): impossible
    · have lowGe : position + 2 ≤ lowPos := hLow
      have highEq : highPos = position := hHigh
      exact absurd (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le lowPosLtHigh (Nat.le_of_eq highEq))
        (Nat.le_trans (Nat.le_add_right position 2) lowGe)) (Nat.lt_irrefl lowPos)
    -- (above, eqHigh): impossible
    · have lowGe : position + 2 ≤ lowPos := hLow
      have highEq : highPos = position + 1 := hHigh
      exact absurd (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le lowPosLtHigh (Nat.le_of_eq highEq))
        (Nat.le_trans (Nat.le_succ (position + 1)) lowGe)) (Nat.lt_irrefl lowPos)
    -- (above, above)
    · have readLow := stringStepCup_openWires_read_above state position lowPos positionInRange hLow
      have readHigh := stringStepCup_openWires_read_above state position highPos positionInRange hHigh
      rw [linksEq, readLow, readHigh] at sameTrue
      have twoLeLow : 2 ≤ lowPos := twoLeOfBlockAbove position lowPos hLow
      have twoLeHigh : 2 ≤ highPos := twoLeOfBlockAbove position highPos hHigh
      have highSubLt : highPos - 2 < state.openWires.length := natSubTwoLtBoundCup highPos _ twoLeHigh highLt2
      have lowSubLtHighSub : lowPos - 2 < highPos - 2 := natSubTwoLtCup lowPos highPos twoLeLow twoLeHigh lowPosLtHigh
      have labelLow := stringAdvanceLabels_read_above labels position lowPos labelL labelR
        positionLabelInRange hLow
      have labelHigh := stringAdvanceLabels_read_above labels position highPos labelL labelR
        positionLabelInRange hHigh
      rw [labelLow, labelHigh]
      exact stringCupOrient_oldPair state labels fresh hforest discipline (lowPos - 2) (highPos - 2)
        lowSubLtHighSub highSubLt sameTrue

end FX1Poly.Polygraph
