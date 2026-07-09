import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanCupPreserves

/-! # WalkingString — the CUP non-crossing (planarity) preservation (FC-3b, CUP leg of the joint invariant)

The CUP orientation case (`stringOrientationDiscipline_stepCup`) does NOT need non-crossing, but the JOINT fold
invariant the no-loops flip threads DOES: non-crossing must survive every step so the CAP survivor argument (P4) can
consume it.  This file ports the non-crossing planarity invariant `StringNonCrossing` (from `StringFussCatalanInsertion`)
across a CUP step:

  * ★ the key geometric observation — in an INTERLEAVING `lowA < lowB < highA < highB`, BOTH arcs are NON-adjacent
    (`+2` apart), and after a cup the ONLY fresh-involving same-component arc is the ADJACENT fresh pair
    `(position, position+1)`; so both interleaving arcs are OLD-old, and the interleaving reduces to the OLD
    non-crossing via residual (i);
  * `cupUnmap` (below ↦ self, above ↦ minus-two) with its strict monotonicity on old indices and the old-read /
    old-bound lemmas;
  * ★★ `stringStepCup_arc_bothOld` — a NON-adjacent same-component arc has both endpoints OLD (neither a fresh leg),
    via the fresh-leg isolation (`stringFreshLeg_not_sameComponent_old` / `stringOld_not_sameComponent_freshLeg`);
  * ★★ `stringNonCrossing_stepCup` — the CUP case of the non-crossing fold invariance, UNCONDITIONAL given freshness
    + forest.

Raw Lean 4 + Init; the classification is `cupRegion` case splits, the reduction is residual (i), the monotonicity is
`Nat` arithmetic on the `cupUnmap` shift.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The de-splice map — old index below the block is unmoved, above the block shifts down by 2 -/

/-- Send a NEW open-wire index (after a cup splice at `position`) back to its OLD index: below the fresh 2-block
unmoved, at/above the block shifted down by 2.  Only meaningful on OLD indices (`< position` or `≥ position + 2`). -/
def cupUnmap (position index : Nat) : Nat := if index < position then index else index - 2

/-! ## Private `Nat` helpers (propext-clean) -/

/-- `2 ≤ value → value - 2 + 2 = value` (re-declared privately; the `CupPreserves` copy is private to that file). -/
private theorem natSubAddTwoNC : (value : Nat) → 2 ≤ value → value - 2 + 2 = value
  | 0, twoLe => absurd twoLe (Nat.not_succ_le_zero 1)
  | 1, twoLe => absurd (Nat.le_of_succ_le_succ twoLe) (Nat.not_succ_le_zero 0)
  | _ + 2, _ => rfl

/-- `leftV + addend ≤ rightV + addend → leftV ≤ rightV`, propext-clean (structural on `addend`). -/
private theorem natLeOfAddLeAddRightNC : (addend leftV rightV : Nat) →
    leftV + addend ≤ rightV + addend → leftV ≤ rightV
  | 0, _, _, cancelled => cancelled
  | addend + 1, leftV, rightV, shifted =>
      natLeOfAddLeAddRightNC addend leftV rightV (Nat.le_of_succ_le_succ shifted)

/-- `smaller < larger → 2 ≤ smaller → 2 ≤ larger → smaller - 2 < larger - 2`, propext-clean. -/
private theorem natSubTwoLtNC (smaller larger : Nat) (smallGe : 2 ≤ smaller) (largeGe : 2 ≤ larger)
    (smallLtLarge : smaller < larger) : smaller - 2 < larger - 2 := by
  have addSmall : smaller - 2 + 2 = smaller := natSubAddTwoNC smaller smallGe
  have addLarge : larger - 2 + 2 = larger := natSubAddTwoNC larger largeGe
  have step : smaller - 2 + 2 < larger - 2 + 2 := by rw [addSmall, addLarge]; exact smallLtLarge
  exact Nat.lt_of_add_lt_add_right step

/-- `value < bound + 2 → 2 ≤ value → value - 2 < bound`, propext-clean. -/
private theorem natSubTwoLtBoundNC (value bound : Nat) (valueGe : 2 ≤ value) (valueLt : value < bound + 2) :
    value - 2 < bound := by
  have addBack : value - 2 + 2 = value := natSubAddTwoNC value valueGe
  have step : value - 2 + 2 < bound + 2 := by rw [addBack]; exact valueLt
  exact Nat.lt_of_add_lt_add_right step

/-- `position + 2 ≤ index → 2 ≤ index`. -/
private theorem twoLeOfAboveNC (position index : Nat) (above : position + 2 ≤ index) : 2 ≤ index :=
  Nat.le_trans (Nat.le_add_left 2 position) above

/-- `a ≠ b → (a == b) = false`, propext-clean (re-declared privately). -/
private theorem natBeqFalseOfNeNC (leftNode rightNode : Nat) (notEqual : leftNode ≠ rightNode) :
    (leftNode == rightNode) = false := by
  cases beqCase : leftNode == rightNode with
  | true => exact absurd (of_decide_eq_true beqCase) notEqual
  | false => rfl

/-- An in-range `natListGetAt` read is a genuine list member (re-declared privately). -/
private theorem natListGetAtMemNC : (wires : List Nat) → (index : Nat) → index < wires.length →
    natListGetAt wires index ∈ wires
  | [], index, hindex => absurd hindex (Nat.not_lt_zero index)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, hindex => List.Mem.tail _ (natListGetAtMemNC rest index (Nat.lt_of_succ_lt_succ hindex))

/-- The four cup regions relative to the insertion point (re-declared privately). -/
private theorem cupRegionNC (position index : Nat) :
    index < position ∨ index = position ∨ index = position + 1 ∨ position + 2 ≤ index := by
  rcases Nat.lt_trichotomy index position with below | atLow | above
  · exact Or.inl below
  · exact Or.inr (Or.inl atLow)
  · rcases Nat.lt_or_ge index (position + 2) with inBlock | aboveBlock
    · exact Or.inr (Or.inr (Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ inBlock) above)))
    · exact Or.inr (Or.inr (Or.inr aboveBlock))

/-! ## Old-index reads and the unmap ordering -/

/-- ★ **An OLD index reads its old wire under `cupUnmap`, and stays in range.**  Below the block the index is unmoved,
at/above the block it shifts down by 2 — either way it reads `state.openWires` at `cupUnmap position index`, and the
unmapped index is below the old length. -/
theorem stringStepCup_read_oldIndex (state : WireState) (position index : Nat)
    (positionInRange : position ≤ state.openWires.length) (indexLt : index < state.openWires.length + 2)
    (oldIndex : index < position ∨ position + 2 ≤ index) :
    natListGetAt (stepCup state position).openWires index
        = natListGetAt state.openWires (cupUnmap position index)
      ∧ cupUnmap position index < state.openWires.length := by
  rcases oldIndex with below | above
  · refine ⟨?_, ?_⟩
    · rw [stringStepCup_openWires_read_below state position index positionInRange below]
      show natListGetAt state.openWires index = natListGetAt state.openWires (if index < position then index else index - 2)
      rw [if_pos below]
    · show (if index < position then index else index - 2) < state.openWires.length
      rw [if_pos below]; exact Nat.lt_of_lt_of_le below positionInRange
  · have notBelow : ¬ index < position := Nat.not_lt.mpr (Nat.le_trans (Nat.le_add_right position 2) above)
    refine ⟨?_, ?_⟩
    · rw [stringStepCup_openWires_read_above state position index positionInRange above]
      show natListGetAt state.openWires (index - 2) = natListGetAt state.openWires (if index < position then index else index - 2)
      rw [if_neg notBelow]
    · show (if index < position then index else index - 2) < state.openWires.length
      rw [if_neg notBelow]
      exact natSubTwoLtBoundNC index state.openWires.length (twoLeOfAboveNC position index above) indexLt

/-- ★ **`cupUnmap` is strictly monotone on OLD indices.**  Below-block indices map to themselves, above-block indices
shift down by 2 while staying above the below-block image — so the strict order is preserved across the 2-gap. -/
theorem cupUnmap_strictMono (position lower higher : Nat)
    (lowerOld : lower < position ∨ position + 2 ≤ lower) (higherOld : higher < position ∨ position + 2 ≤ higher)
    (lowerLtHigher : lower < higher) : cupUnmap position lower < cupUnmap position higher := by
  show (if lower < position then lower else lower - 2) < (if higher < position then higher else higher - 2)
  rcases lowerOld with lowerBelow | lowerAbove
  · rw [if_pos lowerBelow]
    rcases higherOld with higherBelow | higherAbove
    · rw [if_pos higherBelow]; exact lowerLtHigher
    · have notBelow : ¬ higher < position := Nat.not_lt.mpr (Nat.le_trans (Nat.le_add_right position 2) higherAbove)
      rw [if_neg notBelow]
      have posLeSub : position ≤ higher - 2 :=
        natLeOfAddLeAddRightNC 2 position (higher - 2)
          (by rw [natSubAddTwoNC higher (twoLeOfAboveNC position higher higherAbove)]; exact higherAbove)
      exact Nat.lt_of_lt_of_le lowerBelow posLeSub
  · have lowerNotBelow : ¬ lower < position := Nat.not_lt.mpr (Nat.le_trans (Nat.le_add_right position 2) lowerAbove)
    have higherAbove : position + 2 ≤ higher := by
      rcases higherOld with higherBelow | ha
      · exact absurd (Nat.lt_trans lowerLtHigher higherBelow) (Nat.not_lt.mpr (Nat.le_trans (Nat.le_add_right position 2) lowerAbove))
      · exact ha
    have higherNotBelow : ¬ higher < position := Nat.not_lt.mpr (Nat.le_trans (Nat.le_add_right position 2) higherAbove)
    rw [if_neg lowerNotBelow, if_neg higherNotBelow]
    exact natSubTwoLtNC lower higher (twoLeOfAboveNC position lower lowerAbove)
      (twoLeOfAboveNC position higher higherAbove) lowerLtHigher

/-! ## A non-adjacent same-component arc has both endpoints old -/

/-- ★★ **A NON-adjacent same-component arc (after a cup) has BOTH endpoints OLD.**  If `low + 2 ≤ high` and the two
new wires at `low`, `high` are same-component, then neither is a fresh leg: a fresh leg is same-component ONLY with
the other fresh leg (`stringFreshLeg_not_sameComponent_old` / `stringOld_not_sameComponent_freshLeg`), i.e. only with
its immediate neighbour — impossible across a `+2` gap.  The geometric core: the only fresh arc is the adjacent
`(position, position+1)` pair, which cannot span a non-adjacent window. -/
theorem stringStepCup_arc_bothOld (state : WireState) (position : Nat)
    (fresh : StringWireStateFresh state) (hforest : stringIsUnionFindForest state.links)
    (low high : Nat) (nonAdj : low + 2 ≤ high) (highLt : high < state.openWires.length + 2)
    (sameArc : isSameComponent ((state.nextFresh, state.nextFresh + 1) :: state.links)
        (natListGetAt (stepCup state position).openWires low)
        (natListGetAt (stepCup state position).openWires high) = true)
    (positionInRange : position ≤ state.openWires.length) :
    (low < position ∨ position + 2 ≤ low) ∧ (high < position ∨ position + 2 ≤ high) := by
  have parentsBounded := StringWireStateFresh_parentsBelow fresh
  have rightNotChildParent : unionFindParent state.links (state.nextFresh + 1) = none :=
    unionFindParent_none_of_notChild (state.nextFresh + 1) state.links
      (fun edge memberOfLinks =>
        Nat.ne_of_lt (Nat.lt_trans (fresh.linksBelow edge memberOfLinks).1 (Nat.lt_succ_self state.nextFresh)))
  have distinctLR : (state.nextFresh == state.nextFresh + 1) = false :=
    natBeqFalseOfNeNC state.nextFresh (state.nextFresh + 1) (Nat.ne_of_lt (Nat.lt_succ_self state.nextFresh))
  have leftRootEq : unionFindRootOf ((state.nextFresh, state.nextFresh + 1) :: state.links) state.nextFresh
      = state.nextFresh + 1 :=
    stringUnionFindRootOf_freshLeftLeg state.nextFresh (state.nextFresh + 1) state.links distinctLR rightNotChildParent
  have rightRootEq : unionFindRootOf ((state.nextFresh, state.nextFresh + 1) :: state.links) (state.nextFresh + 1)
      = state.nextFresh + 1 :=
    stringUnionFindRootOf_freshRightLeg state.nextFresh (state.nextFresh + 1) state.links distinctLR rightNotChildParent
  have lowLtHigh : low < high := Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt (Nat.lt_succ_self low)) nonAdj
  -- read an old wire's below-`nextFresh` bound
  have oldBelow : ∀ index : Nat, (index < position ∨ position + 2 ≤ index) → index < state.openWires.length + 2 →
      natListGetAt (stepCup state position).openWires index < state.nextFresh := by
    intro index oldIndex indexLt
    obtain ⟨readEq, unmapLt⟩ := stringStepCup_read_oldIndex state position index positionInRange indexLt oldIndex
    rw [readEq]
    exact fresh.openBelow _ (natListGetAtMemNC state.openWires (cupUnmap position index) unmapLt)
  refine ⟨?_, ?_⟩
  · -- low is old
    rcases cupRegionNC position low with lowBelow | lowEq | lowEqSucc | lowAbove
    · exact Or.inl lowBelow
    · exfalso
      -- low = position ⟹ newWires[low] = nextFresh; high must be old (≥ position+2), fresh leg not same-comp old
      have readLow := stringStepCup_openWires_read_blockLow state position positionInRange
      have highAbove : position + 2 ≤ high := lowEq ▸ nonAdj
      have highBelow : natListGetAt (stepCup state position).openWires high < state.nextFresh :=
        oldBelow high (Or.inr highAbove) highLt
      rw [lowEq, readLow] at sameArc
      have notSame := stringFreshLeg_not_sameComponent_old state.nextFresh (state.nextFresh + 1) state.nextFresh
        state.nextFresh (natListGetAt (stepCup state position).openWires high) state.links parentsBounded
        (Nat.le_refl _) hforest leftRootEq (Nat.le_succ _) highBelow
      rw [notSame] at sameArc
      exact Bool.noConfusion sameArc
    · exfalso
      -- low = position + 1 ⟹ newWires[low] = nextFresh+1; high ≥ position+3
      have readLow := stringStepCup_openWires_read_blockHigh state position positionInRange
      have highGe : low + 2 ≤ high := nonAdj
      rw [lowEqSucc] at highGe
      have highAbove : position + 2 ≤ high := Nat.le_trans (Nat.le_succ (position + 2)) highGe
      have highBelow : natListGetAt (stepCup state position).openWires high < state.nextFresh :=
        oldBelow high (Or.inr highAbove) highLt
      rw [lowEqSucc, readLow] at sameArc
      have notSame := stringFreshLeg_not_sameComponent_old state.nextFresh (state.nextFresh + 1) state.nextFresh
        (state.nextFresh + 1) (natListGetAt (stepCup state position).openWires high) state.links parentsBounded
        (Nat.le_refl _) hforest rightRootEq (Nat.le_succ _) highBelow
      rw [notSame] at sameArc
      exact Bool.noConfusion sameArc
    · exact Or.inr lowAbove
  · -- high is old
    rcases cupRegionNC position high with highBelow | highEq | highEqSucc | highAbove
    · exact Or.inl highBelow
    · exfalso
      -- high = position ⟹ newWires[high] = nextFresh; low < position
      have readHigh := stringStepCup_openWires_read_blockLow state position positionInRange
      have lowBelowPos : low < position := Nat.lt_of_lt_of_le lowLtHigh (Nat.le_of_eq highEq)
      have lowBelowFresh : natListGetAt (stepCup state position).openWires low < state.nextFresh :=
        oldBelow low (Or.inl lowBelowPos) (Nat.lt_trans lowLtHigh highLt)
      rw [highEq, readHigh] at sameArc
      have notSame := stringOld_not_sameComponent_freshLeg state.nextFresh (state.nextFresh + 1) state.nextFresh
        state.nextFresh (natListGetAt (stepCup state position).openWires low) state.links parentsBounded
        (Nat.le_refl _) hforest leftRootEq (Nat.le_succ _) lowBelowFresh
      rw [notSame] at sameArc
      exact Bool.noConfusion sameArc
    · exfalso
      -- high = position + 1 ⟹ newWires[high] = nextFresh+1; low < position
      have readHigh := stringStepCup_openWires_read_blockHigh state position positionInRange
      have step : low + 2 ≤ position + 1 := highEqSucc ▸ nonAdj
      have lowBelowPos : low < position := Nat.le_of_succ_le_succ step
      have lowBelowFresh : natListGetAt (stepCup state position).openWires low < state.nextFresh :=
        oldBelow low (Or.inl lowBelowPos) (Nat.lt_trans lowLtHigh highLt)
      rw [highEqSucc, readHigh] at sameArc
      have notSame := stringOld_not_sameComponent_freshLeg state.nextFresh (state.nextFresh + 1) state.nextFresh
        (state.nextFresh + 1) (natListGetAt (stepCup state position).openWires low) state.links parentsBounded
        (Nat.le_refl _) hforest rightRootEq (Nat.le_succ _) lowBelowFresh
      rw [notSame] at sameArc
      exact Bool.noConfusion sameArc
    · exact Or.inr highAbove

/-! ## ★★ The CUP case of the non-crossing fold invariance -/

/-- ★★ **The CUP case of the non-crossing (planarity) fold invariance.**  After `stepCup` at `position`, the
non-crossing invariant is preserved (given freshness + forest).  In any candidate interleaving
`lowA < lowB < highA < highB`, BOTH arcs are non-adjacent (`+2` apart, forced by the strict ordering), so BOTH are
OLD-old (`stringStepCup_arc_bothOld`); the four old indices `cupUnmap`-back to a strictly-ordered old quadruple
(`cupUnmap_strictMono`), each arc's same-component reduces to the OLD links via residual (i)
(`stringIsSameComponent_cons_freshAbove_forest`), and the OLD non-crossing then rules the interleaving out.  This is
the CUP leg of the joint invariant the no-loops flip threads. -/
theorem stringNonCrossing_stepCup (state : WireState) (position : Nat)
    (positionInRange : position ≤ state.openWires.length)
    (fresh : StringWireStateFresh state) (hforest : stringIsUnionFindForest state.links)
    (nonCrossing : StringNonCrossing state) :
    StringNonCrossing (stepCup state position) := by
  intro lowA lowB highA highB lowALtLowB lowBLtHighA highALtHighB highBLt sameA sameB
  have linksEq : (stepCup state position).links = (state.nextFresh, state.nextFresh + 1) :: state.links :=
    stringStepCup_links_eq state position fresh
  have newLenEq : (stepCup state position).openWires.length = state.openWires.length + 2 :=
    stringStepCup_openWires_length state position positionInRange
  have highBLt2 : highB < state.openWires.length + 2 := newLenEq ▸ highBLt
  have highALt2 : highA < state.openWires.length + 2 := Nat.lt_trans highALtHighB highBLt2
  rw [linksEq] at sameA sameB
  -- both arcs are non-adjacent
  have nonAdjA : lowA + 2 ≤ highA := Nat.le_trans (Nat.succ_le_succ lowALtLowB) lowBLtHighA
  have nonAdjB : lowB + 2 ≤ highB := Nat.le_trans (Nat.succ_le_succ lowBLtHighA) highALtHighB
  -- both arcs old-old
  obtain ⟨lowAOld, highAOld⟩ :=
    stringStepCup_arc_bothOld state position fresh hforest lowA highA nonAdjA highALt2 sameA positionInRange
  obtain ⟨lowBOld, highBOld⟩ :=
    stringStepCup_arc_bothOld state position fresh hforest lowB highB nonAdjB highBLt2 sameB positionInRange
  -- old reads + bounds
  obtain ⟨readLowA, unmapLowALt⟩ :=
    stringStepCup_read_oldIndex state position lowA positionInRange
      (Nat.lt_trans (Nat.lt_trans lowALtLowB (Nat.lt_of_le_of_lt (Nat.le_of_lt lowBLtHighA) highALtHighB)) highBLt2) lowAOld
  obtain ⟨readLowB, unmapLowBLt⟩ :=
    stringStepCup_read_oldIndex state position lowB positionInRange
      (Nat.lt_trans (Nat.lt_trans lowBLtHighA highALtHighB) highBLt2) lowBOld
  obtain ⟨readHighA, unmapHighALt⟩ :=
    stringStepCup_read_oldIndex state position highA positionInRange highALt2 highAOld
  obtain ⟨readHighB, unmapHighBLt⟩ :=
    stringStepCup_read_oldIndex state position highB positionInRange highBLt2 highBOld
  -- old wires are below nextFresh
  have lowABelow : natListGetAt state.openWires (cupUnmap position lowA) < state.nextFresh :=
    fresh.openBelow _ (natListGetAtMemNC state.openWires (cupUnmap position lowA) unmapLowALt)
  have highABelow : natListGetAt state.openWires (cupUnmap position highA) < state.nextFresh :=
    fresh.openBelow _ (natListGetAtMemNC state.openWires (cupUnmap position highA) unmapHighALt)
  have lowBBelow : natListGetAt state.openWires (cupUnmap position lowB) < state.nextFresh :=
    fresh.openBelow _ (natListGetAtMemNC state.openWires (cupUnmap position lowB) unmapLowBLt)
  have highBBelow : natListGetAt state.openWires (cupUnmap position highB) < state.nextFresh :=
    fresh.openBelow _ (natListGetAtMemNC state.openWires (cupUnmap position highB) unmapHighBLt)
  have parentsBounded := StringWireStateFresh_parentsBelow fresh
  -- strip the fresh edge from each arc's same-component
  rw [readLowA, readHighA,
    stringIsSameComponent_cons_freshAbove_forest state.nextFresh (state.nextFresh + 1) state.nextFresh state.links
      parentsBounded (Nat.le_refl _) hforest _ _ lowABelow highABelow] at sameA
  rw [readLowB, readHighB,
    stringIsSameComponent_cons_freshAbove_forest state.nextFresh (state.nextFresh + 1) state.nextFresh state.links
      parentsBounded (Nat.le_refl _) hforest _ _ lowBBelow highBBelow] at sameB
  -- the unmapped quadruple is strictly ordered
  have oLoALtLoB : cupUnmap position lowA < cupUnmap position lowB :=
    cupUnmap_strictMono position lowA lowB lowAOld lowBOld lowALtLowB
  have oLoBLtHiA : cupUnmap position lowB < cupUnmap position highA :=
    cupUnmap_strictMono position lowB highA lowBOld highAOld lowBLtHighA
  have oHiALtHiB : cupUnmap position highA < cupUnmap position highB :=
    cupUnmap_strictMono position highA highB highAOld highBOld highALtHighB
  exact nonCrossing (cupUnmap position lowA) (cupUnmap position lowB) (cupUnmap position highA)
    (cupUnmap position highB) oLoALtLoB oLoBLtHiA oHiALtHiB unmapHighBLt sameA sameB

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the CUP case of the non-crossing planarity fold invariance is CLOSED.**  `stringNonCrossing_stepCup`
proves `StringNonCrossing (stepCup state position)` from `StringNonCrossing state` (given freshness + forest), via the
geometric observation that an INTERLEAVING forces both arcs non-adjacent, a non-adjacent same-component arc after a cup
is OLD-old (`stringStepCup_arc_bothOld`, from the fresh-leg isolation), and the OLD non-crossing rules the interleaving
out after `cupUnmap`-ing (`cupUnmap_strictMono`) and stripping the fresh edge (residual (i)).  All UNCONDITIONAL (given
freshness + forest, which the fold carries), zero-axiom.  This is the CUP leg of the joint invariant the no-loops flip
threads.  `= true`. -/
def fxString_hasCupNonCrossingPreservation : Bool := true

end FX1Poly.Polygraph
