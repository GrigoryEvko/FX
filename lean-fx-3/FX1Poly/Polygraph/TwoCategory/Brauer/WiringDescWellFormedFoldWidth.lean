import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescWellFormedFoldAssembly
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcExtractorRec
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcReadOffCount
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingFoldAlignment

/-! # BRAUER r21 — the corrected-word GENERAL `WellFormedBrauerFold` (the connectivity-free assembly, flipped)

The r20 six-phase reduction `wellFormedBrauerFold_standardFormWordExt5_ofPhases`
(`Brauer/WiringDescWellFormedFoldAssembly.lean`) discharges the corrected word from six per-phase width obligations;
r20 left OPEN the FEEDING of those obligations from the corrected extractor's fields.  This file closes the feeding —
the connectivity-FREE half of the r19 wall's third residual — and flips
`fxBrauer_hasWellFormedFoldGeneralAssembly`.

## The bill of bridges fed into the reduction (each zero-axiom, structural)

  * **the staircase POSITION-BOUND** `permutationToCrossingWord_posBound` (r21 B1, `Brauer/WiringDescArcConjugator.lean`)
    on the two shipped range-permutation read-offs (`readOffBottomOrder_isPermutationOfRange` /
    `readOffTopOrderInverse_isPermutationOfRange`) for the bottom / top crossing phases;
  * ★ **`throughStrandPerm_isBounded`** — the middle staircase's `order` (the TOP-indexed through permutation) is
    `[0, #through)`-bounded (the genuinely-new counting piece: each emitted rank
    `arcMiddleCountBelow throughBottoms (partner …)` is strict because the port is a through bottom, via the
    involution);
  * **`crossingWordFold_openWires_length`** (r17) preserves the width through each crossing phase;
  * ★ **`capBlockOpenWiresShrinkWidth`** / **`cupBlockOpenWiresGrowWidth`** — the cap block SHRINKS the width by
    `2·#capFeet`, the cup block GROWS it by `2·#cupArcs` (fresh inductions over the single-step length lemmas);
  * **the two cruxes** `capArcFeetTwiceThroughSumsToBottom` / `cupArcTwiceThroughSumsToTop` and ★ the through-count
    symmetry `throughStrandBottoms_length_eq_throughStrandTops` (r21, `Brauer/WiringDescArcReadOffCount.lean`) fix the
    phase-boundary widths (`2·#capFeet + #through = bottomCount`, `#through + 2·#cupArcs = topCount`,
    `#throughBottoms = #throughTops`);
  * trivial `brauerSeedOpenWiresLengthWidth` (seed width) and `natReplicateMemEqWidth` (cup block entries).

## What flips and what stays OPEN

`wellFormedBrauerFold_correctedWord_general` is a straight-line assembly of the six phase discharges chained by
width-accounting — NOT an induction over the diagram, NO connectivity, NO arc classification.  It flips
`fxBrauer_hasWellFormedFoldGeneralAssembly` (`Brauer/WiringDescWellFormedFoldAssembly.lean`).  The masters
(`fxBrauer_hasTagCorrDisjoint` / `_hasTagCorrExtraction` / `_hasFoldAlignmentE3`) and the r19 wall
`fxBrauer_hasFoldTargetHonestAssembly` stay honestly `false`: they owe the through-strand cross-phase T-CONNECT (at
boundary-index granularity over arbitrary interior states) and T-ENUM / E3, both unbuilt.  #2013 does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin; independent `#print axioms` clean. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Section 0 — the re-derived propext-free `Nat` / `Bool` / list kit -/

/-- Right-cancellation of `Nat` addition, structural on the cancelled summand (`Nat.add_right_cancel` leaks `propext`). -/
private theorem natAddRightCancelWidth : (right leftFirst leftSecond : Nat) →
    leftFirst + right = leftSecond + right → leftFirst = leftSecond
  | 0, leftFirst, leftSecond, equal => by rw [Nat.add_zero, Nat.add_zero] at equal; exact equal
  | right + 1, leftFirst, leftSecond, equal => by
      rw [Nat.add_succ leftFirst right, Nat.add_succ leftSecond right] at equal
      exact natAddRightCancelWidth right leftFirst leftSecond (Nat.succ.inj equal)

/-- `Nat.ble a b = true → a ≤ b`, structural (core's `Nat.le_of_ble_eq_true` route reused propext-free). -/
private theorem natLeOfBleWidth : (a b : Nat) → Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => Bool.noConfusion h
  | a + 1, b + 1, h => Nat.succ_le_succ (natLeOfBleWidth a b h)

/-- `a ≤ b → Nat.ble a b = true`, structural. -/
private theorem natBleOfLeWidth : (a b : Nat) → a ≤ b → Nat.ble a b = true
  | 0, _, _ => rfl
  | a + 1, 0, h => absurd h (Nat.not_succ_le_zero a)
  | a + 1, b + 1, h => natBleOfLeWidth a b (Nat.le_of_succ_le_succ h)

/-- `Nat.blt a b = true → a < b`, via `natLeOfBleWidth (a+1) b` (`Nat.blt a b` is `Nat.ble (a+1) b`). -/
private theorem natLtOfBltWidth (a b : Nat) (h : Nat.blt a b = true) : a < b := natLeOfBleWidth (a + 1) b h

/-- `Nat.ble (n+1) n = false`, structural. -/
private theorem natBleSuccSelfFalseWidth : (n : Nat) → Nat.ble (n + 1) n = false
  | 0 => rfl
  | k + 1 => natBleSuccSelfFalseWidth k

/-- `Nat.blt n n = false` (a value is never strictly below itself). -/
private theorem natBltSelfFalseWidth (n : Nat) : Nat.blt n n = false := natBleSuccSelfFalseWidth n

/-- `Nat.beq a b = true → a = b`, structural. -/
private theorem eqOfNatBeqWidth : (a b : Nat) → Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => Bool.noConfusion h
  | _ + 1, 0, h => Bool.noConfusion h
  | a + 1, b + 1, h => congrArg (· + 1) (eqOfNatBeqWidth a b h)

/-- `Nat.beq a b = false → a ≠ b`, structural. -/
private theorem neOfNatBeqFalseWidth : (a b : Nat) → Nat.beq a b = false → a ≠ b
  | 0, 0, h => Bool.noConfusion h
  | 0, _ + 1, _ => fun equal => Nat.noConfusion equal
  | _ + 1, 0, _ => fun equal => Nat.noConfusion equal
  | a + 1, b + 1, h => fun equal => neOfNatBeqFalseWidth a b h (Nat.succ.inj equal)

/-- A member of a cons distinct from the head is a member of the tail. -/
private theorem memConsOfNeWidth (value head : Nat) (rest : List Nat) (mem : value ∈ head :: rest)
    (ne : value ≠ head) : value ∈ rest := by
  cases mem with
  | head => exact absurd rfl ne
  | tail _ memRest => exact memRest

/-- `List.range.loop` membership INTRODUCTION — below the fuel or already accumulated. -/
private theorem memRangeLoopWidth : (count : Nat) → (acc : List Nat) → (target : Nat) →
    (target < count ∨ target ∈ acc) → target ∈ List.range.loop count acc
  | 0, _, target, disj => by
      cases disj with
      | inl below => exact absurd below (Nat.not_lt_zero target)
      | inr mem => exact mem
  | count + 1, acc, target, disj => by
      show target ∈ List.range.loop count (count :: acc)
      refine memRangeLoopWidth count (count :: acc) target ?_
      cases disj with
      | inl below =>
          cases Nat.lt_or_ge target count with
          | inl belowCount => exact Or.inl belowCount
          | inr atLeast =>
              have targetEq : target = count := Nat.le_antisymm (Nat.le_of_lt_succ below) atLeast
              exact Or.inr (targetEq ▸ List.Mem.head acc)
      | inr mem => exact Or.inr (List.Mem.tail count mem)

/-- `target < count → target ∈ List.range count`. -/
private theorem memRangeOfLtWidth (target count : Nat) (lt : target < count) : target ∈ List.range count :=
  memRangeLoopWidth count [] target (Or.inl lt)

/-- `List.range.loop` membership ELIMINATION — below the fuel or accumulated. -/
private theorem memRangeLoopLtWidth : (count : Nat) → (acc : List Nat) → (target : Nat) →
    target ∈ List.range.loop count acc → target < count ∨ target ∈ acc
  | 0, _, _, mem => Or.inr mem
  | count + 1, acc, target, mem => by
      have inner := memRangeLoopLtWidth count (count :: acc) target mem
      cases inner with
      | inl below => exact Or.inl (Nat.lt_succ_of_lt below)
      | inr memCons =>
          cases memCons with
          | head => exact Or.inl (Nat.lt_succ_self count)
          | tail _ memAcc => exact Or.inr memAcc

/-- `target ∈ List.range count → target < count`. -/
private theorem memRangeLtWidth (target count : Nat) (mem : target ∈ List.range count) : target < count := by
  cases memRangeLoopLtWidth count [] target mem with
  | inl below => exact below
  | inr memNil => exact nomatch memNil

/-- An in-range positional read is a member. -/
private theorem natListGetAtMemWidth : (entries : List Nat) → (index : Nat) → index < entries.length →
    natListGetAt entries index ∈ entries
  | [], index, lt => absurd lt (Nat.not_lt_zero index)
  | _ :: _, 0, _ => List.Mem.head _
  | head :: rest, index + 1, lt =>
      List.Mem.tail head (natListGetAtMemWidth rest index (Nat.lt_of_succ_lt_succ lt))

/-- An out-of-range positional read is the `0` default. -/
private theorem natListGetAtDefaultWidth : (entries : List Nat) → (index : Nat) → entries.length ≤ index →
    natListGetAt entries index = 0
  | [], _, _ => rfl
  | head :: rest, 0, le => absurd le (Nat.not_succ_le_zero rest.length)
  | _ :: rest, index + 1, le => natListGetAtDefaultWidth rest index (Nat.le_of_succ_le_succ le)

/-- Membership in a `filterMap` inverts to a source member with a `some` image — `propext`-free (the general forward
direction, replicated locally per the `dsimp only [List.filterMap]` technique). -/
private theorem memFilterMapExistsWidth {sourceType targetType : Type}
    (transform : sourceType → Option targetType) :
    (entries : List sourceType) → (target : targetType) → target ∈ entries.filterMap transform →
    ∃ source, source ∈ entries ∧ transform source = some target
  | [], _, memNil => nomatch memNil
  | head :: rest, target, mem => by
      cases headImage : transform head with
      | none =>
          have memReduced : target ∈ List.filterMap transform rest := by
            dsimp only [List.filterMap] at mem
            rw [headImage] at mem
            exact mem
          obtain ⟨source, sourceMem, sourceEq⟩ := memFilterMapExistsWidth transform rest target memReduced
          exact ⟨source, List.Mem.tail head sourceMem, sourceEq⟩
      | some mappedHead =>
          have memReduced : target ∈ mappedHead :: List.filterMap transform rest := by
            dsimp only [List.filterMap] at mem
            rw [headImage] at mem
            exact mem
          cases memReduced with
          | head => exact ⟨head, List.Mem.head rest, headImage⟩
          | tail _ innerMem =>
              obtain ⟨source, sourceMem, sourceEq⟩ := memFilterMapExistsWidth transform rest target innerMem
              exact ⟨source, List.Mem.tail head sourceMem, sourceEq⟩

/-- `List.range` length, structural (core's route leaks `propext`). -/
private theorem rangeLoopLengthWidth : (count : Nat) → (acc : List Nat) →
    (List.range.loop count acc).length = count + acc.length
  | 0, acc => (Nat.zero_add acc.length).symm
  | count + 1, acc => by
      show (List.range.loop count (count :: acc)).length = (count + 1) + acc.length
      rw [rangeLoopLengthWidth count (count :: acc)]
      show count + (acc.length + 1) = (count + 1) + acc.length
      rw [Nat.add_succ, Nat.succ_add]

private theorem rangeLengthWidth (count : Nat) : (List.range count).length = count :=
  (rangeLoopLengthWidth count []).trans (Nat.add_zero count)

/-- Every entry of `natReplicate count value` equals `value`. -/
private theorem natReplicateMemEqWidth : (count value target : Nat) →
    target ∈ natReplicate count value → target = value
  | 0, _, _, memNil => nomatch memNil
  | count + 1, value, target, mem => by
      have memCons : target ∈ value :: natReplicate count value := mem
      cases memCons with
      | head => rfl
      | tail _ memRest => exact natReplicateMemEqWidth count value target memRest

/-! ## Section 1 — the rank lemmas (`arcMiddleCountBelow`) -/

/-- `arcMiddleCountBelow` never exceeds the list length (each entry contributes at most one). -/
private theorem arcMiddleCountBelowLeWidth : (entries : List Nat) → (bound : Nat) →
    arcMiddleCountBelow entries bound ≤ entries.length
  | [], _ => Nat.le_refl 0
  | head :: rest, bound => by
      show cond (Nat.blt head bound) 1 0 + arcMiddleCountBelow rest bound ≤ rest.length + 1
      have condLe : cond (Nat.blt head bound) 1 0 ≤ 1 := by
        cases Nat.blt head bound with
        | true => exact Nat.le_refl 1
        | false => exact Nat.zero_le 1
      exact Nat.le_trans (Nat.add_le_add condLe (arcMiddleCountBelowLeWidth rest bound))
        (Nat.le_of_eq (Nat.add_comm 1 rest.length))

/-- ★ **The rank is STRICT when the bound is a list member.**  If `bound ∈ entries` then
`arcMiddleCountBelow entries bound < entries.length` — the member equal to `bound` is not counted (`bound < bound` is
false), so at least one entry is uncounted.  Structural on `entries`. -/
private theorem arcMiddleCountBelowLtOfMemWidth : (entries : List Nat) → (bound : Nat) →
    bound ∈ entries → arcMiddleCountBelow entries bound < entries.length
  | [], _, memNil => nomatch memNil
  | head :: rest, bound, member => by
      show cond (Nat.blt head bound) 1 0 + arcMiddleCountBelow rest bound < rest.length + 1
      cases hb : Nat.beq head bound with
      | true =>
          have headEq : head = bound := eqOfNatBeqWidth head bound hb
          have bltFalse : Nat.blt head bound = false := by rw [headEq]; exact natBltSelfFalseWidth bound
          rw [bltFalse]
          show (0 : Nat) + arcMiddleCountBelow rest bound < rest.length + 1
          rw [Nat.zero_add]
          exact Nat.lt_succ_of_le (arcMiddleCountBelowLeWidth rest bound)
      | false =>
          have boundMemRest : bound ∈ rest :=
            memConsOfNeWidth bound head rest member (neOfNatBeqFalseWidth head bound hb).symm
          have ih := arcMiddleCountBelowLtOfMemWidth rest bound boundMemRest
          have condLe : cond (Nat.blt head bound) 1 0 ≤ 1 := by
            cases Nat.blt head bound with
            | true => exact Nat.le_refl 1
            | false => exact Nat.zero_le 1
          have step1 : cond (Nat.blt head bound) 1 0 + arcMiddleCountBelow rest bound
              ≤ 1 + arcMiddleCountBelow rest bound := Nat.add_le_add_right condLe _
          have step2 : 1 + arcMiddleCountBelow rest bound ≤ rest.length := by
            rw [Nat.add_comm 1 (arcMiddleCountBelow rest bound)]; exact ih
          exact Nat.lt_of_le_of_lt (Nat.le_trans step1 step2) (Nat.lt_succ_self rest.length)

/-! ## Section 2 — A′: the through-strand permutation is `[0, #through)`-bounded -/

/-- ★ **Every emitted value of `throughStrandPerm` is a valid rank.**  Each entry is
`arcMiddleCountBelow throughBottoms (partner (bottomCount + topIndex))` for a THROUGH top, whose bottom partner is a
through bottom (via the involution), so the rank is strictly below `#throughBottoms`. -/
private theorem throughStrandPermMemLtWidth (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner)
    (value : Nat) (member : value ∈ throughStrandPerm bottomCount topCount partner) :
    value < (throughStrandBottoms bottomCount partner).length := by
  obtain ⟨topIndex, topIndexMem, transformEq⟩ :=
    memFilterMapExistsWidth
      (fun topIndex => match Nat.blt (natListGetAt partner (bottomCount + topIndex)) bottomCount with
        | true => some (arcMiddleCountBelow (throughStrandBottoms bottomCount partner)
            (natListGetAt partner (bottomCount + topIndex)))
        | false => none)
      (List.range topCount) value member
  cases hblt : Nat.blt (natListGetAt partner (bottomCount + topIndex)) bottomCount with
  | false =>
      rw [hblt] at transformEq
      dsimp only at transformEq
      exact nomatch transformEq
  | true =>
      rw [hblt] at transformEq
      dsimp only at transformEq
      have valueEq : value = arcMiddleCountBelow (throughStrandBottoms bottomCount partner)
          (natListGetAt partner (bottomCount + topIndex)) := (Option.some.inj transformEq).symm
      have topIndexLt : topIndex < topCount := memRangeLtWidth topIndex topCount topIndexMem
      have portIdxLtTotal : bottomCount + topIndex < bottomCount + topCount :=
        Nat.add_lt_add_left topIndexLt bottomCount
      have portLtBc : natListGetAt partner (bottomCount + topIndex) < bottomCount := natLtOfBltWidth _ _ hblt
      have selfInv : natListGetAt partner (natListGetAt partner (bottomCount + topIndex)) = bottomCount + topIndex :=
        wf.isSelfInverse (bottomCount + topIndex) portIdxLtTotal
      have portRange : natListGetAt partner (bottomCount + topIndex) ∈ List.range bottomCount :=
        memRangeOfLtWidth (natListGetAt partner (bottomCount + topIndex)) bottomCount portLtBc
      have portGuard : throughBottomGuard bottomCount partner (natListGetAt partner (bottomCount + topIndex)) = true := by
        show Nat.ble bottomCount (natListGetAt partner (natListGetAt partner (bottomCount + topIndex))) = true
        rw [selfInv]
        exact natBleOfLeWidth bottomCount (bottomCount + topIndex) (Nat.le_add_right bottomCount topIndex)
      have portMemBottoms : natListGetAt partner (bottomCount + topIndex)
          ∈ throughStrandBottoms bottomCount partner :=
        memFilterMapGuardComplete (throughBottomGuard bottomCount partner) (List.range bottomCount)
          (natListGetAt partner (bottomCount + topIndex)) portRange portGuard
      rw [valueEq]
      exact arcMiddleCountBelowLtOfMemWidth (throughStrandBottoms bottomCount partner)
        (natListGetAt partner (bottomCount + topIndex)) portMemBottoms

/-- ★★ **A′ — the through permutation is `[0, #through)`-bounded.**  For every well-formed boundary involution, every
positional read of `throughStrandPerm` below `#throughBottoms` is `< #throughBottoms`: an in-range read is a genuine
emitted rank (bounded by `throughStrandPermMemLtWidth`), an out-of-range read is the `0` default (below the positive
width).  This is the `orderBounded` hypothesis the middle crossing phase's position-bound consumes. -/
theorem throughStrandPerm_isBounded (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner) :
    ∀ index, index < (throughStrandBottoms bottomCount partner).length →
      natListGetAt (throughStrandPerm bottomCount topCount partner) index
        < (throughStrandBottoms bottomCount partner).length := by
  intro index indexLt
  cases Nat.lt_or_ge index (throughStrandPerm bottomCount topCount partner).length with
  | inl inRange =>
      exact throughStrandPermMemLtWidth bottomCount topCount partner wf
        (natListGetAt (throughStrandPerm bottomCount topCount partner) index)
        (natListGetAtMemWidth (throughStrandPerm bottomCount topCount partner) index inRange)
  | inr outOfRange =>
      rw [natListGetAtDefaultWidth (throughStrandPerm bottomCount topCount partner) index outOfRange]
      exact Nat.lt_of_le_of_lt (Nat.zero_le index) indexLt

/-! ## Section 3 — C / D: the cap-block SHRINK and cup-block GROW width laws -/

/-- Firing a cup (`0 ⇒ 2`) at an in-range position GROWS the open-wire count by exactly two. -/
private theorem stepCupAtLengthWidth (state : WireState) (pos : Nat)
    (hle : pos ≤ state.openWires.length) :
    (stepBrauerAtom state (cupAt pos)).openWires.length = state.openWires.length + 2 := by
  obtain ⟨rightLen, hRight⟩ := Nat.le.dest hle
  show (stepWiring state pos cupWiring).openWires.length = state.openWires.length + 2
  have fits : state.openWires.length = pos + cupWiring.inputCount + rightLen := by
    show state.openWires.length = pos + 0 + rightLen
    rw [Nat.add_zero]; exact hRight.symm
  rw [stepWiring_openWires_length_fits state pos rightLen cupWiring fits]
  show pos + 2 + rightLen = state.openWires.length + 2
  rw [Nat.add_right_comm pos 2 rightLen, hRight]

/-- Firing a cap (`2 ⇒ 0`) at an in-range position SHRINKS the open-wire count by exactly two. -/
private theorem stepCapAtLengthWidth (state : WireState) (pos : Nat)
    (hfits : pos + 2 ≤ state.openWires.length) :
    (stepBrauerAtom state (capAt pos)).openWires.length + 2 = state.openWires.length := by
  obtain ⟨rightLen, fitsRaw⟩ := Nat.le.dest hfits
  show (stepWiring state pos capWiring).openWires.length + 2 = state.openWires.length
  have fits : state.openWires.length = pos + capWiring.inputCount + rightLen := by
    show state.openWires.length = pos + 2 + rightLen
    exact fitsRaw.symm
  rw [stepWiring_openWires_length_fits state pos rightLen capWiring fits]
  show pos + rightLen + 2 = state.openWires.length
  rw [Nat.add_right_comm pos rightLen 2]
  exact fitsRaw

/-- ★ **The cap block SHRINKS the width by `2·count`.**  Folding `capWord (natReplicate count 0)` (count caps at
position `0`) over a state with `count + count ≤ width` leaves `width - 2·count` open wires — in additive form,
`result + (count + count) = width`.  Fresh structural induction over the single-step cap length lemma. -/
theorem capBlockOpenWiresShrinkWidth :
    (count : Nat) → (state : WireState) → count + count ≤ state.openWires.length →
    (processBrauer state (capWord (natReplicate count 0))).openWires.length + (count + count)
      = state.openWires.length
  | 0, state, _ => by
      show state.openWires.length + 0 = state.openWires.length
      rw [Nat.add_zero]
  | count + 1, state, fits => by
      show (processBrauer (stepBrauerAtom state (capAt 0)) (capWord (natReplicate count 0))).openWires.length
        + ((count + 1) + (count + 1)) = state.openWires.length
      have twoLower : 2 ≤ (count + 1) + (count + 1) :=
        Nat.add_le_add (Nat.succ_le_succ (Nat.zero_le count)) (Nat.succ_le_succ (Nat.zero_le count))
      have twoLe : 0 + 2 ≤ state.openWires.length := by rw [Nat.zero_add]; exact Nat.le_trans twoLower fits
      have shrink : (stepBrauerAtom state (capAt 0)).openWires.length + 2 = state.openWires.length :=
        stepCapAtLengthWidth state 0 twoLe
      have hEq : (count + 1) + (count + 1) = count + count + 2 := by
        rw [Nat.add_assoc, Nat.add_comm 1 (count + 1), Nat.add_assoc, Nat.add_assoc]
      have newFits : count + count ≤ (stepBrauerAtom state (capAt 0)).openWires.length := by
        have h1 : count + count + 2 ≤ (stepBrauerAtom state (capAt 0)).openWires.length + 2 := by
          rw [shrink, ← hEq]; exact fits
        obtain ⟨leftover, hLeft⟩ := Nat.le.dest h1
        refine Nat.le.intro (k := leftover) ?_
        have aligned : count + count + leftover + 2 = (stepBrauerAtom state (capAt 0)).openWires.length + 2 := by
          rw [Nat.add_right_comm (count + count) leftover 2]; exact hLeft
        exact natAddRightCancelWidth 2 (count + count + leftover)
          (stepBrauerAtom state (capAt 0)).openWires.length aligned
      have ih := capBlockOpenWiresShrinkWidth count (stepBrauerAtom state (capAt 0)) newFits
      rw [hEq, ← Nat.add_assoc, ih, shrink]

/-- ★ **The cup block GROWS the width by `2·count`.**  Folding `cupWord (natReplicate count value)` (count cups at
position `value ≤ width`) over a state adds `2·count` open wires — `result = width + (count + count)`.  Fresh
structural induction over the single-step cup length lemma (the position stays in range since the width only grows). -/
theorem cupBlockOpenWiresGrowWidth :
    (count value : Nat) → (state : WireState) → value ≤ state.openWires.length →
    (processBrauer state (cupWord (natReplicate count value))).openWires.length
      = state.openWires.length + (count + count)
  | 0, _, state, _ => by
      show state.openWires.length = state.openWires.length + 0
      rw [Nat.add_zero]
  | count + 1, value, state, hle => by
      show (processBrauer (stepBrauerAtom state (cupAt value)) (cupWord (natReplicate count value))).openWires.length
        = state.openWires.length + ((count + 1) + (count + 1))
      have grow : (stepBrauerAtom state (cupAt value)).openWires.length = state.openWires.length + 2 :=
        stepCupAtLengthWidth state value hle
      have hleNew : value ≤ (stepBrauerAtom state (cupAt value)).openWires.length := by
        rw [grow]; exact Nat.le_trans hle (Nat.le_add_right state.openWires.length 2)
      have ih := cupBlockOpenWiresGrowWidth count value (stepBrauerAtom state (cupAt value)) hleNew
      rw [ih, grow]
      have hEq : (count + 1) + (count + 1) = count + count + 2 := by
        rw [Nat.add_assoc, Nat.add_comm 1 (count + 1), Nat.add_assoc, Nat.add_assoc]
      rw [hEq, Nat.add_right_comm state.openWires.length 2 (count + count),
        Nat.add_assoc state.openWires.length (count + count) 2]

/-! ## Section 4 — E: the seed width -/

/-- ★ **The seed has `bottomCount` open wires.**  `(brauerSeed bottomCount).openWires = List.range bottomCount`. -/
theorem brauerSeedOpenWiresLengthWidth (bottomCount : Nat) :
    (brauerSeed bottomCount).openWires.length = bottomCount := by
  show (List.range bottomCount).length = bottomCount
  exact rangeLengthWidth bottomCount

/-! ## Section 5 — the concrete-output truth-probe (the boundary case FIRST) -/

/-- ★ **Truth-probe (concrete outputs FIRST).**  The cap block over the width-4 all-caps boundary shrinks the width to
zero (`0 + 4 = 4`); a two-cup block over two wires grows it to six; and the through permutation of the adversarial-B
partner is `[0, #through)`-bounded — read straight off the kernel, before the general lemmas. -/
theorem widthBridges_probe :
    (processBrauer (brauerSeed 4) (capWord (natReplicate 2 0))).openWires.length + (2 + 2) = 4
      ∧ (processBrauer (brauerSeed 2) (cupWord (natReplicate 2 2))).openWires.length = 2 + (2 + 2)
      ∧ (throughStrandPerm 3 3 [2, 4, 0, 5, 1, 3]).all
          (fun value => decide (value < (throughStrandBottoms 3 [2, 4, 0, 5, 1, 3]).length)) = true :=
  ⟨capBlockOpenWiresShrinkWidth 2 (brauerSeed 4) (by decide),
   cupBlockOpenWiresGrowWidth 2 2 (brauerSeed 2) (by decide),
   by decide⟩

/-! ## Section 6 — the GENERAL corrected-word `WellFormedBrauerFold` (the six phase discharges assembled) -/

/-- ★★★ **THE GENERAL corrected-word `WellFormedBrauerFold` (BRAUER r21).**  For EVERY well-formed boundary
involution `d`, the corrected extractor's realized word `standardFormWordExt5 (reconstructStandardFormExt5Corrected d)`
is well-formed at the seed.  A straight-line assembly of the six per-phase discharges chained by width-accounting —
NO induction over the diagram, NO connectivity, NO arc classification: the three crossing phases' window bounds come
from the staircase position-bound on the two range-permutation read-offs plus A′ (the middle order's boundedness);
the phase-boundary widths from the crossing width-preservation, the cap SHRINK / cup GROW block laws, the two cruxes,
and the through-count symmetry.  This is the connectivity-free half of the r19 wall's third residual, DISCHARGED. -/
theorem wellFormedBrauerFold_correctedWord_general (d : DiagramType)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner) :
    WellFormedBrauerFold (brauerSeed d.bottomCount)
      (standardFormWordExt5 (reconstructStandardFormExt5Corrected d)) := by
  -- the two width cruxes + the through-count symmetry
  have bottomCrux : (capArcFeetIndices d.bottomCount d.partner).length
      + (capArcFeetIndices d.bottomCount d.partner).length
      + (throughStrandBottoms d.bottomCount d.partner).length = d.bottomCount :=
    capArcFeetTwiceThroughSumsToBottom d.bottomCount (d.bottomCount + d.topCount) d.partner
      (Nat.le_add_right d.bottomCount d.topCount) wf
  have topCrux : (cupArcTopIndices d.bottomCount d.topCount d.partner).length
      + (cupArcTopIndices d.bottomCount d.topCount d.partner).length
      + (throughStrandTops d.bottomCount d.topCount d.partner).length = d.topCount :=
    cupArcTwiceThroughSumsToTop d.bottomCount d.topCount d.partner wf
  have throughSym : (throughStrandBottoms d.bottomCount d.partner).length
      = (throughStrandTops d.bottomCount d.topCount d.partner).length :=
    throughStrandBottoms_length_eq_throughStrandTops d.bottomCount d.topCount d.partner wf
  -- the three crossing-phase window bounds (staircase position-bound on the read-off orders)
  have bottomPosBound : ∀ pos, pos ∈ permutationToCrossingWord d.bottomCount
        (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner) →
      pos + 2 ≤ d.bottomCount :=
    permutationToCrossingWord_posBound d.bottomCount _
      (readOffBottomOrder_isPermutationOfRange d.bottomCount d.topCount d.partner wf).isBounded
  have middlePosBound : ∀ pos, pos ∈ permutationToCrossingWord
        (throughStrandBottoms d.bottomCount d.partner).length
        (throughStrandPerm d.bottomCount d.topCount d.partner) →
      pos + 2 ≤ (throughStrandBottoms d.bottomCount d.partner).length :=
    permutationToCrossingWord_posBound (throughStrandBottoms d.bottomCount d.partner).length _
      (throughStrandPerm_isBounded d.bottomCount d.topCount d.partner wf)
  have topPosBound : ∀ pos, pos ∈ permutationToCrossingWord d.topCount
        (permInverse (throughStrandTops d.bottomCount d.topCount d.partner
          ++ cupArcTops d.bottomCount d.topCount d.partner)) →
      pos + 2 ≤ d.topCount :=
    permutationToCrossingWord_posBound d.topCount _
      (readOffTopOrderInverse_isPermutationOfRange d.bottomCount d.topCount d.partner wf).isBounded
  -- the phase-boundary widths
  have wBottom : (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (permutationToCrossingWord d.bottomCount
          (capArcFeet d.bottomCount d.partner
            ++ throughStrandBottoms d.bottomCount d.partner)))).openWires.length = d.bottomCount :=
    crossingWordFold_openWires_length d.bottomCount _ (brauerSeed d.bottomCount)
      (brauerSeedOpenWiresLengthWidth d.bottomCount) bottomPosBound
  have wCap : (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (permutationToCrossingWord d.bottomCount
          (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner))))
        (capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0))).openWires.length
      = (throughStrandBottoms d.bottomCount d.partner).length := by
    have hShrink := capBlockOpenWiresShrinkWidth (capArcFeetIndices d.bottomCount d.partner).length
      (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (permutationToCrossingWord d.bottomCount
          (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner))))
      (by rw [wBottom]; exact Nat.le.intro bottomCrux)
    rw [wBottom] at hShrink
    have hCeq : (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (permutationToCrossingWord d.bottomCount
            (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner))))
          (capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0))).openWires.length
        + ((capArcFeetIndices d.bottomCount d.partner).length
          + (capArcFeetIndices d.bottomCount d.partner).length)
        = (throughStrandBottoms d.bottomCount d.partner).length
          + ((capArcFeetIndices d.bottomCount d.partner).length
            + (capArcFeetIndices d.bottomCount d.partner).length) := by
      rw [Nat.add_comm (throughStrandBottoms d.bottomCount d.partner).length _]
      exact hShrink.trans bottomCrux.symm
    exact natAddRightCancelWidth _ _ (throughStrandBottoms d.bottomCount d.partner).length hCeq
  have lengthAfterCap : (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (permutationToCrossingWord d.bottomCount
          (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner))
          ++ capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0))).openWires.length
      = (throughStrandBottoms d.bottomCount d.partner).length := by
    rw [processBrauer_append (crossingWord (permutationToCrossingWord d.bottomCount
      (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner)))
      (brauerSeed d.bottomCount)
      (capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0))]
    exact wCap
  have lengthAfterMiddle : (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (permutationToCrossingWord d.bottomCount
          (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner))
          ++ capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0)
          ++ crossingWord (permutationToCrossingWord (throughStrandBottoms d.bottomCount d.partner).length
            (throughStrandPerm d.bottomCount d.topCount d.partner)))).openWires.length
      = (throughStrandBottoms d.bottomCount d.partner).length := by
    rw [processBrauer_append (crossingWord (permutationToCrossingWord d.bottomCount
        (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner))
        ++ capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0))
      (brauerSeed d.bottomCount)
      (crossingWord (permutationToCrossingWord (throughStrandBottoms d.bottomCount d.partner).length
        (throughStrandPerm d.bottomCount d.topCount d.partner)))]
    exact crossingWordFold_openWires_length (throughStrandBottoms d.bottomCount d.partner).length _
      (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (permutationToCrossingWord d.bottomCount
          (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner))
          ++ capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0)))
      lengthAfterCap middlePosBound
  have lengthAfterCup : (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (permutationToCrossingWord d.bottomCount
          (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner))
          ++ capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0)
          ++ crossingWord (permutationToCrossingWord (throughStrandBottoms d.bottomCount d.partner).length
            (throughStrandPerm d.bottomCount d.topCount d.partner))
          ++ cupWord (natReplicate (cupArcTopIndices d.bottomCount d.topCount d.partner).length
            (throughStrandBottoms d.bottomCount d.partner).length))).openWires.length
      = d.topCount := by
    rw [processBrauer_append (crossingWord (permutationToCrossingWord d.bottomCount
          (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner))
          ++ capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0)
          ++ crossingWord (permutationToCrossingWord (throughStrandBottoms d.bottomCount d.partner).length
            (throughStrandPerm d.bottomCount d.topCount d.partner)))
      (brauerSeed d.bottomCount)
      (cupWord (natReplicate (cupArcTopIndices d.bottomCount d.topCount d.partner).length
        (throughStrandBottoms d.bottomCount d.partner).length))]
    rw [cupBlockOpenWiresGrowWidth (cupArcTopIndices d.bottomCount d.topCount d.partner).length
      (throughStrandBottoms d.bottomCount d.partner).length
      (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (permutationToCrossingWord d.bottomCount
          (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner))
          ++ capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0)
          ++ crossingWord (permutationToCrossingWord (throughStrandBottoms d.bottomCount d.partner).length
            (throughStrandPerm d.bottomCount d.topCount d.partner))))
      (Nat.le_of_eq lengthAfterMiddle.symm), lengthAfterMiddle, throughSym,
      Nat.add_comm (throughStrandTops d.bottomCount d.topCount d.partner).length _]
    exact topCrux
  -- feed the six phase discharges into the r20 reduction
  exact wellFormedBrauerFold_standardFormWordExt5_ofPhases (reconstructStandardFormExt5Corrected d)
    (wellFormedBrauerFold_crossingWord d.bottomCount _ (brauerSeed d.bottomCount)
      (brauerSeedOpenWiresLengthWidth d.bottomCount) bottomPosBound)
    (wellFormedBrauerFold_capZeros (capArcFeetIndices d.bottomCount d.partner).length
      (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (permutationToCrossingWord d.bottomCount
          (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner))))
      (by rw [wBottom]; exact Nat.le.intro bottomCrux))
    (wellFormedBrauerFold_crossingWord (throughStrandBottoms d.bottomCount d.partner).length _
      (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (permutationToCrossingWord d.bottomCount
          (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner))
          ++ capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0)))
      lengthAfterCap middlePosBound)
    (wellFormedBrauerFold_cupWord (throughStrandBottoms d.bottomCount d.partner).length _
      (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (permutationToCrossingWord d.bottomCount
          (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner))
          ++ capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0)
          ++ crossingWord (permutationToCrossingWord (throughStrandBottoms d.bottomCount d.partner).length
            (throughStrandPerm d.bottomCount d.topCount d.partner))))
      (Nat.le_of_eq lengthAfterMiddle.symm)
      (fun pos posMem => Nat.le_of_eq
        (natReplicateMemEqWidth (cupArcTopIndices d.bottomCount d.topCount d.partner).length
          (throughStrandBottoms d.bottomCount d.partner).length pos posMem)))
    (wellFormedBrauerFold_crossingWord d.topCount _
      (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (permutationToCrossingWord d.bottomCount
          (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner))
          ++ capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0)
          ++ crossingWord (permutationToCrossingWord (throughStrandBottoms d.bottomCount d.partner).length
            (throughStrandPerm d.bottomCount d.topCount d.partner))
          ++ cupWord (natReplicate (cupArcTopIndices d.bottomCount d.topCount d.partner).length
            (throughStrandBottoms d.bottomCount d.partner).length)))
      lengthAfterCup topPosBound)
    (wellFormedBrauerFold_circleWord d.loops
      (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (permutationToCrossingWord d.bottomCount
          (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner))
          ++ capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0)
          ++ crossingWord (permutationToCrossingWord (throughStrandBottoms d.bottomCount d.partner).length
            (throughStrandPerm d.bottomCount d.topCount d.partner))
          ++ cupWord (natReplicate (cupArcTopIndices d.bottomCount d.topCount d.partner).length
            (throughStrandBottoms d.bottomCount d.partner).length)
          ++ crossingWord (permutationToCrossingWord d.topCount
            (permInverse (throughStrandTops d.bottomCount d.topCount d.partner
              ++ cupArcTops d.bottomCount d.topCount d.partner))))))

/-! ## Section 7 — non-vacuity: the general theorem on real involutions -/

/-- ★ **The width-4 all-caps boundary is a boundary involution** — the self-attack case where `2·#caps = bottomCount`
exactly (`#through = 0`), the sole nontrivial cap width obligation at equality. -/
theorem isBoundaryInvolution_allCapsBoundary :
    IsBoundaryInvolution 4 [3, 2, 1, 0] where
  hasBoundaryLength := rfl
  mapsInRange := by decide
  isSelfInverse := by decide
  isFixedPointFree := by decide

/-- ★★ **The general corrected-word is well-formed on the all-caps boundary** (nested caps, `#through = 0`, the tight
`2·#caps = bottomCount` width case). -/
theorem wellFormedBrauerFold_correctedWord_general_allCapsBoundary :
    WellFormedBrauerFold (brauerSeed 4)
      (standardFormWordExt5 (reconstructStandardFormExt5Corrected
        { bottomCount := 4, topCount := 0, partner := [3, 2, 1, 0], loops := 0 })) :=
  wellFormedBrauerFold_correctedWord_general
    { bottomCount := 4, topCount := 0, partner := [3, 2, 1, 0], loops := 0 } isBoundaryInvolution_allCapsBoundary

/-- ★★ **The general corrected-word is well-formed on the width-8 all-through wild diagram** (four through strands,
the middle staircase width `4`, A′ non-vacuous). -/
theorem wellFormedBrauerFold_correctedWord_general_wildThrough :
    WellFormedBrauerFold (brauerSeed wildThroughDiagram.bottomCount)
      (standardFormWordExt5 (reconstructStandardFormExt5Corrected wildThroughDiagram)) :=
  wellFormedBrauerFold_correctedWord_general wildThroughDiagram isBoundaryInvolution_wildThrough

/-- ★★ **The general corrected-word is well-formed on the mixed through/cup/loop wild diagram** (both cruxes and the
through-count symmetry all non-trivial). -/
theorem wellFormedBrauerFold_correctedWord_general_wildCupLoop :
    WellFormedBrauerFold (brauerSeed wildCupLoopDiagram.bottomCount)
      (standardFormWordExt5 (reconstructStandardFormExt5Corrected wildCupLoopDiagram)) :=
  wellFormedBrauerFold_correctedWord_general wildCupLoopDiagram isBoundaryInvolution_wildCupLoop

/-! ## Section 8 — the r21 general-assembly marker -/

/-- ★★ **Honesty marker — the GENERAL corrected-word `WellFormedBrauerFold` is SHIPPED (BRAUER r21).**
`wellFormedBrauerFold_correctedWord_general` proves, for EVERY well-formed boundary involution, that the corrected
extractor's word is well-formed at the seed — the connectivity-free half of the r19 wall's third residual, DISCHARGED
by feeding the r20 six-phase reduction from the staircase position-bound, A′ (`throughStrandPerm_isBounded`), the cap
SHRINK / cup GROW block laws, the two cruxes, and the through-count symmetry
(`throughStrandBottoms_length_eq_throughStrandTops`).  Exercised on the all-caps boundary and two wild involutions
(`_allCapsBoundary` / `_wildThrough` / `_wildCupLoop`).  Feeds the flip of
`fxBrauer_hasWellFormedFoldGeneralAssembly` (`Brauer/WiringDescWellFormedFoldAssembly.lean`).  `= true`. -/
def fxBrauer_hasCorrectedWordGeneralWellFormed : Bool := true

end FX1Poly.Polygraph
