import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingInvariant
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.NonCrossingMatching
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScan
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute

/-! # ArcNonCrossingExtract — the state invariant transfers to the extracted matching (cap rung D2a-iv, extract)

The final rung of D2a-iv: the state-level planarity invariant `ArcNonCrossing bottomCount state`
implies the extracted `DiagramType`'s `partner` list is `IsNonCrossing`.  This is the translation
from the fold-preserved connectivity invariant to the topological non-crossing predicate the
leg-aligned cup selector consumes (D1/D2).

## The bridge — the two position renderings coincide

`extractArc bottomCount state` reads the arc state's `(openWires, links)` through the matching
route's `extractDiagram`, whose `partner k` is `partnerIndexOf links (List.range bottomCount ++
openWires) total k` over `total = bottomCount + openWires.length`.  The planarity predicate places
boundary index `k` at `boundaryPosition bottomCount total k`; the state invariant places a token at
`arcEndTokenPosition bottomCount state`.  These COINCIDE under `tokenOfIndex k := bottomPort k` for
`k < bottomCount` else `openSlot (k - bottomCount)` — a bottom port keeps its value, a top index
reverses past the seed block identically in both renderings.  With the node reading and validity
also transported (`arcEndTokenNode (tokenOfIndex k) = natListGetAt boundaryNodes k`), a crossing of
two `partner` arcs becomes an interleaved same-component quadruple of valid tokens, contradicting
`ArcNonCrossing`.  Each `partner` arc's two endpoints ARE same-component (`partnerIndexOf`'s scan
returns a shared-root candidate or the fixed point) — the forward soundness, census-free.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (per-file copy, following the codebase pattern) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

private theorem rangeLoopGetAt_past : (count : Nat) → (accumulated : List Nat) →
    (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count)
      = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAt_past count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAt_below : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAt_below count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAt_past count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAt_below (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAt_below count [] index indexBelow

/-! ## Private clean Nat-subtraction plumbing (Init's cancel/comm subtraction lemmas leak propext) -/

/-- `(start + amount) - start = amount`, hand-rolled clean. -/
private theorem addSubCancelLeft : (start amount : Nat) → (start + amount) - start = amount
  | 0, amount => by rw [Nat.zero_add, Nat.sub_zero]
  | start + 1, amount => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact addSubCancelLeft start amount

/-- `x - a - b = x - (a + b)`, hand-rolled clean (`Nat.sub_sub` leaks propext). -/
private theorem subSub : (x a b : Nat) → x - a - b = x - (a + b)
  | _, _, 0 => by rw [Nat.add_zero, Nat.sub_zero]
  | x, a, Nat.succ b => by
      show x - a - Nat.succ b = x - (a + Nat.succ b)
      rw [Nat.sub_succ, subSub x a b, Nat.add_succ, Nat.sub_succ]

/-- `(a + x) - (a + y) = x - y`, hand-rolled clean (`Nat.add_sub_add_left` route via `Nat.min_comm`
would leak). -/
private theorem addSubAddCancelLeft : (a x y : Nat) → (a + x) - (a + y) = x - y
  | 0, _, _ => by rw [Nat.zero_add, Nat.zero_add]
  | Nat.succ a, x, y => by
      show (Nat.succ a + x) - (Nat.succ a + y) = x - y
      rw [Nat.succ_add, Nat.succ_add, Nat.succ_sub_succ]
      exact addSubAddCancelLeft a x y

/-- `Nat.min a b = b` when `b ≤ a`, hand-rolled clean (`Nat.min_eq_right` leaks propext through
`Nat.min_comm`); `Nat.min a b` is defeq `if a ≤ b then a else b`. -/
private theorem natMinRight (firstNat secondNat : Nat) (order : secondNat ≤ firstNat) :
    Nat.min firstNat secondNat = secondNat := by
  show (if firstNat ≤ secondNat then firstNat else secondNat) = secondNat
  cases Nat.decLe firstNat secondNat with
  | isTrue firstLeSecond => rw [if_pos firstLeSecond]; exact Nat.le_antisymm firstLeSecond order
  | isFalse firstNotLeSecond => rw [if_neg firstNotLeSecond]

/-- `Nat.max a b = a` when `b ≤ a`, hand-rolled clean (`Nat.max_eq_left` leaks propext through
`Nat.max_comm`); `Nat.max a b` is defeq `if a ≤ b then b else a`. -/
private theorem natMaxLeft (firstNat secondNat : Nat) (order : secondNat ≤ firstNat) :
    Nat.max firstNat secondNat = firstNat := by
  show (if firstNat ≤ secondNat then secondNat else firstNat) = firstNat
  cases Nat.decLe firstNat secondNat with
  | isTrue firstLeSecond => rw [if_pos firstLeSecond]; exact Nat.le_antisymm order firstLeSecond
  | isFalse firstNotLeSecond => rw [if_neg firstNotLeSecond]

/-- The cyclic-position inner regroup: `(bottomCount + openLen) - 1 - (bottomCount + offset) =
openLen - 1 - offset` — the arithmetic identifying `boundaryPosition`'s top-index reversal with
`arcEndTokenPosition`'s open-slot reversal. -/
private theorem boundaryInnerRegroup (bottomCount openLen offset : Nat) :
    (bottomCount + openLen) - 1 - (bottomCount + offset) = openLen - 1 - offset := by
  rw [subSub (bottomCount + openLen) 1 (bottomCount + offset), subSub openLen 1 offset,
    Nat.add_left_comm 1 bottomCount offset,
    addSubAddCancelLeft bottomCount openLen (1 + offset)]

/-! ## Private list plumbing (`List.length_map` leaks propext; the map reads are structural) -/

/-- `(l.map f).length = l.length`, hand-rolled clean. -/
private theorem natListMapLength (mapFunction : Nat → Nat) :
    (list : List Nat) → (list.map mapFunction).length = list.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (natListMapLength mapFunction rest)

/-- Reading a mapped list in range applies the function to the read. -/
private theorem natListGetAt_map_below (mapFunction : Nat → Nat) :
    (list : List Nat) → (index : Nat) → index < list.length →
    natListGetAt (list.map mapFunction) index = mapFunction (natListGetAt list index)
  | [], index, below => absurd below (Nat.not_lt_zero index)
  | _ :: _, 0, _ => rfl
  | _ :: rest, index + 1, below =>
      natListGetAt_map_below mapFunction rest index (Nat.lt_of_succ_lt_succ below)

/-- Reading `(List.range total).map f` at an in-range index returns `f index`. -/
private theorem natListGetAt_map_range (mapFunction : Nat → Nat) (total index : Nat)
    (indexBelow : index < total) :
    natListGetAt ((List.range total).map mapFunction) index = mapFunction index := by
  have inRange : index < (List.range total).length := by rw [rangeLength total]; exact indexBelow
  rw [natListGetAt_map_below mapFunction (List.range total) index inRange,
    rangeGetAt_below total index indexBelow]

/-- Reading a prefixed boundary below the prefix block reads the block. -/
private theorem natListGetAt_append_below :
    (block wires : List Nat) → (index : Nat) → index < block.length →
    natListGetAt (block ++ wires) index = natListGetAt block index
  | [], _, index, below => absurd below (Nat.not_lt_zero index)
  | _ :: _, _, 0, _ => rfl
  | _ :: rest, wires, index + 1, below =>
      natListGetAt_append_below rest wires index (Nat.lt_of_succ_lt_succ below)

/-- Reading a prefixed boundary past the prefix block reads the tail. -/
private theorem natListGetAt_appendPast :
    (block wires : List Nat) → (offset : Nat) →
    natListGetAt (block ++ wires) (offset + block.length) = natListGetAt wires offset
  | [], _, _ => rfl
  | _ :: blockRest, wires, offset => natListGetAt_appendPast blockRest wires offset

/-- A range-prefixed boundary read below the range returns the index. -/
private theorem natListGetAt_rangeAppendBelow (count : Nat) (wires : List Nat) (index : Nat)
    (indexBelow : index < count) :
    natListGetAt (List.range count ++ wires) index = index := by
  have inRange : index < (List.range count).length := by rw [rangeLength count]; exact indexBelow
  rw [natListGetAt_append_below (List.range count) wires index inRange,
    rangeGetAt_below count index indexBelow]

/-! ## Private partner-scan membership + reflexivity (per-file copies) -/

/-- The partner scan returns either the exclude fallback or a member of the scanned list. -/
private theorem findPartnerScan_memOrExclude (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (rootHere excludeIndex : Nat) : (scanned : List Nat) →
    findPartnerScan links boundaryNodes rootHere excludeIndex scanned = excludeIndex
      ∨ findPartnerScan links boundaryNodes rootHere excludeIndex scanned ∈ scanned
  | [] => Or.inl rfl
  | candidate :: rest => by
      rw [findPartnerScan_cons]
      cases headTest : (candidate != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere) with
      | true => exact Or.inr (List.Mem.head rest)
      | false =>
          cases findPartnerScan_memOrExclude links boundaryNodes rootHere excludeIndex rest with
          | inl isExclude => exact Or.inl isExclude
          | inr isMember => exact Or.inr (List.Mem.tail candidate isMember)

/-- Every node shares its own component. -/
private theorem isSameComponentRefl (links : List (Nat × Nat)) (probeNode : Nat) :
    isSameComponent links probeNode probeNode = true :=
  decide_eq_true (rfl : unionFindRootOf links probeNode = unionFindRootOf links probeNode)

/-! ## The boundary index → end token translation -/

/-- The boundary end token of a `partner` index: a bottom port for a bottom index, an open slot
(shifted past the seed block) for a top index.  Its rectangle position and its union-find node read
both coincide with the matching route's `boundaryPosition` / `boundaryNodes` reads. -/
def tokenOfIndex (bottomCount index : Nat) : ArcEndToken :=
  if index < bottomCount then ArcEndToken.bottomPort index
  else ArcEndToken.openSlot (index - bottomCount)

/-- ★ **The two position renderings coincide.**  `boundaryPosition bottomCount total index`
(the matching route's cyclic linearization, `total = bottomCount + openWires.length`) equals
`arcEndTokenPosition bottomCount state (tokenOfIndex bottomCount index)` (the state invariant's
token position): bottom indices keep their value, top indices reverse past the seed block the same
way in both. -/
theorem boundaryPosition_eq_arcEndTokenPosition (bottomCount : Nat) (state : ArcWireState)
    (index : Nat) :
    boundaryPosition bottomCount (bottomCount + state.openWires.length) index
      = arcEndTokenPosition bottomCount state (tokenOfIndex bottomCount index) := by
  unfold boundaryPosition tokenOfIndex
  cases Nat.lt_or_ge index bottomCount with
  | inl below => rw [if_pos below, if_pos below]; rfl
  | inr atLeast =>
      rw [if_neg (fun indexLtBottom => Nat.lt_irrefl index (Nat.lt_of_lt_of_le indexLtBottom atLeast)),
        if_neg (fun indexLtBottom => Nat.lt_irrefl index (Nat.lt_of_lt_of_le indexLtBottom atLeast))]
      show bottomCount + ((bottomCount + state.openWires.length) - 1 - index)
        = bottomCount + (state.openWires.length - 1 - (index - bottomCount))
      obtain ⟨slot, slotEq⟩ := Nat.le.dest atLeast
      rw [← slotEq, addSubCancelLeft bottomCount slot,
        boundaryInnerRegroup bottomCount state.openWires.length slot]

/-- ★ **The node reading coincides.**  The union-find node the token reads equals the matching
route's boundary-node read `natListGetAt (List.range bottomCount ++ openWires) index`: a bottom port
IS the index, an open slot reads the same open wire the past-block append does. -/
theorem arcEndTokenNode_tokenOfIndex (bottomCount : Nat) (state : ArcWireState) (index : Nat) :
    arcEndTokenNode state (tokenOfIndex bottomCount index)
      = natListGetAt (List.range bottomCount ++ state.openWires) index := by
  unfold tokenOfIndex
  cases Nat.lt_or_ge index bottomCount with
  | inl below =>
      rw [if_pos below]
      exact (natListGetAt_rangeAppendBelow bottomCount state.openWires index below).symm
  | inr atLeast =>
      rw [if_neg (fun indexLtBottom => Nat.lt_irrefl index (Nat.lt_of_lt_of_le indexLtBottom atLeast))]
      show natListGetAt state.openWires (index - bottomCount)
        = natListGetAt (List.range bottomCount ++ state.openWires) index
      obtain ⟨slot, slotEq⟩ := Nat.le.dest atLeast
      rw [← slotEq, addSubCancelLeft bottomCount slot]
      have indexForm : bottomCount + slot = slot + (List.range bottomCount).length := by
        rw [rangeLength bottomCount, Nat.add_comm bottomCount slot]
      rw [indexForm]
      exact (natListGetAt_appendPast (List.range bottomCount) state.openWires slot).symm

/-- ★ **The token of an in-range index is valid.**  A bottom index gives a bottom port below the
seed width; a top index gives an open slot into the current frontier. -/
theorem isValidArcEndToken_tokenOfIndex (bottomCount : Nat) (state : ArcWireState) (index : Nat)
    (indexBelow : index < bottomCount + state.openWires.length) :
    isValidArcEndToken bottomCount state (tokenOfIndex bottomCount index) := by
  unfold tokenOfIndex
  cases Nat.lt_or_ge index bottomCount with
  | inl below => rw [if_pos below]; exact below
  | inr atLeast =>
      rw [if_neg (fun indexLtBottom => Nat.lt_irrefl index (Nat.lt_of_lt_of_le indexLtBottom atLeast))]
      show index - bottomCount < state.openWires.length
      obtain ⟨slot, slotEq⟩ := Nat.le.dest atLeast
      rw [← slotEq, addSubCancelLeft bottomCount slot]
      have slotBumpBelow : bottomCount + slot < bottomCount + state.openWires.length := by
        rw [slotEq]; exact indexBelow
      exact Nat.lt_of_add_lt_add_left slotBumpBelow

/-! ## The forward partner soundness (census-free) -/

/-- ★ **Each `partnerIndexOf` arc is a same-component pair (or a fixed point).**  The scan returns
either `index` itself (no partner in its component) or a boundary index whose read shares `index`'s
component (`findPartnerScan_root_ofFound`).  This is the forward direction — no census needed. -/
theorem partnerIndexOf_sameComponent_or_fixed (state : ArcWireState) (bottomCount index : Nat) :
    partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length) index = index
      ∨ isSameComponent state.links
          (natListGetAt (List.range bottomCount ++ state.openWires) index)
          (natListGetAt (List.range bottomCount ++ state.openWires)
            (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
              (bottomCount + state.openWires.length) index)) = true := by
  cases Nat.decEq (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
      (bottomCount + state.openWires.length) index) index with
  | isTrue isFixed => exact Or.inl isFixed
  | isFalse notFixed =>
      refine Or.inr ?_
      have rootEq := findPartnerScan_root_ofFound state.links
        (List.range bottomCount ++ state.openWires)
        (unionFindRootOf state.links
          (natListGetAt (List.range bottomCount ++ state.openWires) index))
        index (List.range (bottomCount + state.openWires.length)) notFixed
      exact decide_eq_true rootEq.symm

/-- ★ **The partner index stays in range.**  The scan returns `index` (in range) or a member of the
scanned `List.range total` (in range). -/
theorem partnerIndexOf_below (state : ArcWireState) (bottomCount index : Nat)
    (indexBelow : index < bottomCount + state.openWires.length) :
    partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length) index < bottomCount + state.openWires.length := by
  cases findPartnerScan_memOrExclude state.links (List.range bottomCount ++ state.openWires)
      (unionFindRootOf state.links (natListGetAt (List.range bottomCount ++ state.openWires) index))
      index (List.range (bottomCount + state.openWires.length)) with
  | inl isExclude =>
      have partnerEq : partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
          (bottomCount + state.openWires.length) index = index := isExclude
      rw [partnerEq]; exact indexBelow
  | inr isMember => exact mem_range_imp_lt isMember

/-! ## The near/far arc endpoints of a partner index -/

/-- ★ **An arc's two rectangle endpoints as valid same-component tokens.**  For an in-range index
and its `partnerIdx = natListGetAt partner index` (in range, arc-sound), the two boundary tokens
`tokenOfIndex index` and `tokenOfIndex partnerIdx` are valid, sit at `arcMinPosition` and
`arcMaxPosition` (dispatched by which end is nearer), and share a union-find component. -/
theorem arcNearFarTokens (bottomCount : Nat) (state : ArcWireState)
    (total : Nat) (totalEq : total = bottomCount + state.openWires.length)
    (partner : List Nat) (index partnerIdx : Nat)
    (indexBelow : index < total) (partnerBelow : partnerIdx < total)
    (partnerAt : natListGetAt partner index = partnerIdx)
    (arcSound : partnerIdx = index ∨ isSameComponent state.links
        (natListGetAt (List.range bottomCount ++ state.openWires) index)
        (natListGetAt (List.range bottomCount ++ state.openWires) partnerIdx) = true) :
    ∃ tokenNear tokenFar : ArcEndToken,
      isValidArcEndToken bottomCount state tokenNear ∧
      isValidArcEndToken bottomCount state tokenFar ∧
      arcEndTokenPosition bottomCount state tokenNear
        = arcMinPosition bottomCount total partner index ∧
      arcEndTokenPosition bottomCount state tokenFar
        = arcMaxPosition bottomCount total partner index ∧
      isSameComponent state.links (arcEndTokenNode state tokenNear)
        (arcEndTokenNode state tokenFar) = true := by
  subst totalEq
  have validSelf := isValidArcEndToken_tokenOfIndex bottomCount state index indexBelow
  have validPartner := isValidArcEndToken_tokenOfIndex bottomCount state partnerIdx partnerBelow
  have posSelfEq := (boundaryPosition_eq_arcEndTokenPosition bottomCount state index).symm
  have posPartnerEq := (boundaryPosition_eq_arcEndTokenPosition bottomCount state partnerIdx).symm
  have minEq : arcMinPosition bottomCount (bottomCount + state.openWires.length) partner index
      = Nat.min (boundaryPosition bottomCount (bottomCount + state.openWires.length) index)
          (boundaryPosition bottomCount (bottomCount + state.openWires.length) partnerIdx) := by
    show Nat.min (boundaryPosition bottomCount (bottomCount + state.openWires.length) index)
        (boundaryPosition bottomCount (bottomCount + state.openWires.length)
          (natListGetAt partner index))
      = Nat.min (boundaryPosition bottomCount (bottomCount + state.openWires.length) index)
          (boundaryPosition bottomCount (bottomCount + state.openWires.length) partnerIdx)
    rw [partnerAt]
  have maxEq : arcMaxPosition bottomCount (bottomCount + state.openWires.length) partner index
      = Nat.max (boundaryPosition bottomCount (bottomCount + state.openWires.length) index)
          (boundaryPosition bottomCount (bottomCount + state.openWires.length) partnerIdx) := by
    show Nat.max (boundaryPosition bottomCount (bottomCount + state.openWires.length) index)
        (boundaryPosition bottomCount (bottomCount + state.openWires.length)
          (natListGetAt partner index))
      = Nat.max (boundaryPosition bottomCount (bottomCount + state.openWires.length) index)
          (boundaryPosition bottomCount (bottomCount + state.openWires.length) partnerIdx)
    rw [partnerAt]
  rw [minEq, maxEq]
  have sameNearFar : isSameComponent state.links
      (arcEndTokenNode state (tokenOfIndex bottomCount index))
      (arcEndTokenNode state (tokenOfIndex bottomCount partnerIdx)) = true := by
    rw [arcEndTokenNode_tokenOfIndex bottomCount state index,
      arcEndTokenNode_tokenOfIndex bottomCount state partnerIdx]
    cases arcSound with
    | inl fixed => rw [fixed]; exact isSameComponentRefl state.links _
    | inr sound => exact sound
  cases Nat.le_total
      (boundaryPosition bottomCount (bottomCount + state.openWires.length) index)
      (boundaryPosition bottomCount (bottomCount + state.openWires.length) partnerIdx) with
  | inl selfLePartner =>
      exact ⟨tokenOfIndex bottomCount index, tokenOfIndex bottomCount partnerIdx,
        validSelf, validPartner,
        posSelfEq.trans (Nat.min_eq_left selfLePartner).symm,
        posPartnerEq.trans (Nat.max_eq_right selfLePartner).symm,
        sameNearFar⟩
  | inr partnerLeSelf =>
      exact ⟨tokenOfIndex bottomCount partnerIdx, tokenOfIndex bottomCount index,
        validPartner, validSelf,
        posPartnerEq.trans (natMinRight _ _ partnerLeSelf).symm,
        posSelfEq.trans (natMaxLeft _ _ partnerLeSelf).symm,
        isSameComponent_flip state.links _ _ sameNearFar⟩

/-! ## The extract translation -/

/-- ★ **The state invariant extracts to a non-crossing matching.**  If the arc-fold state is
`ArcNonCrossing`, the `DiagramType` its `extractArc` reads has an `IsNonCrossing` `partner` list:
were two partner arcs to cross, their four rectangle endpoints — valid tokens at strictly increasing
positions, each arc's two ends sharing a component — would interleave, contradicting the state-level
`ArcNonCrossing`.  Census-free: only the forward partner soundness (`partnerIndexOf` returns a
shared-component candidate) is used, not the two-endpoint census. -/
theorem isNonCrossing_extractArc_diagram_partner (bottomCount : Nat) (state : ArcWireState)
    (nonCrossing : ArcNonCrossing bottomCount state) :
    IsNonCrossing bottomCount (extractArc bottomCount state).diagram.partner := by
  show IsNonCrossing bottomCount
    ((List.range (bottomCount + state.openWires.length)).map
      (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length)))
  intro leftIndex leftBelow rightIndex rightBelow crossing
  have partnerLength : ((List.range (bottomCount + state.openWires.length)).map
      (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length))).length
      = bottomCount + state.openWires.length := by
    rw [natListMapLength, rangeLength]
  have leftBelowTotal : leftIndex < bottomCount + state.openWires.length :=
    partnerLength ▸ leftBelow
  have rightBelowTotal : rightIndex < bottomCount + state.openWires.length :=
    partnerLength ▸ rightBelow
  rw [partnerLength] at crossing
  obtain ⟨minLeftLtMinRight, minRightLtMaxLeft, maxLeftLtMaxRight⟩ := crossing
  have partnerLeftEq : natListGetAt ((List.range (bottomCount + state.openWires.length)).map
        (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
          (bottomCount + state.openWires.length))) leftIndex
      = partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
          (bottomCount + state.openWires.length) leftIndex :=
    natListGetAt_map_range _ (bottomCount + state.openWires.length) leftIndex leftBelowTotal
  have partnerRightEq : natListGetAt ((List.range (bottomCount + state.openWires.length)).map
        (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
          (bottomCount + state.openWires.length))) rightIndex
      = partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
          (bottomCount + state.openWires.length) rightIndex :=
    natListGetAt_map_range _ (bottomCount + state.openWires.length) rightIndex rightBelowTotal
  obtain ⟨leftNear, leftFar, leftNearValid, leftFarValid, leftNearPos, leftFarPos, leftSame⟩ :=
    arcNearFarTokens bottomCount state (bottomCount + state.openWires.length) rfl
      ((List.range (bottomCount + state.openWires.length)).map
        (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
          (bottomCount + state.openWires.length)))
      leftIndex
      (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length) leftIndex)
      leftBelowTotal
      (partnerIndexOf_below state bottomCount leftIndex leftBelowTotal)
      partnerLeftEq
      (partnerIndexOf_sameComponent_or_fixed state bottomCount leftIndex)
  obtain ⟨rightNear, rightFar, rightNearValid, rightFarValid, rightNearPos, rightFarPos, rightSame⟩ :=
    arcNearFarTokens bottomCount state (bottomCount + state.openWires.length) rfl
      ((List.range (bottomCount + state.openWires.length)).map
        (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
          (bottomCount + state.openWires.length)))
      rightIndex
      (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length) rightIndex)
      rightBelowTotal
      (partnerIndexOf_below state bottomCount rightIndex rightBelowTotal)
      partnerRightEq
      (partnerIndexOf_sameComponent_or_fixed state bottomCount rightIndex)
  have posAB : arcEndTokenPosition bottomCount state leftNear
      < arcEndTokenPosition bottomCount state rightNear := by
    rw [leftNearPos, rightNearPos]; exact minLeftLtMinRight
  have posBC : arcEndTokenPosition bottomCount state rightNear
      < arcEndTokenPosition bottomCount state leftFar := by
    rw [rightNearPos, leftFarPos]; exact minRightLtMaxLeft
  have posCD : arcEndTokenPosition bottomCount state leftFar
      < arcEndTokenPosition bottomCount state rightFar := by
    rw [leftFarPos, rightFarPos]; exact maxLeftLtMaxRight
  exact nonCrossing leftNear rightNear leftFar rightFar
    leftNearValid rightNearValid leftFarValid rightFarValid
    posAB posBC posCD leftSame rightSame

/-! ## Honesty marker -/

/-- **Honesty marker — the extract translation to `IsNonCrossing` is SHIPPED (cap rung D2a-iv,
extract, COMPLETE).**  `tokenOfIndex` (the boundary-index → end-token map),
`boundaryPosition_eq_arcEndTokenPosition` (the two position renderings coincide),
`arcEndTokenNode_tokenOfIndex` (the node readings coincide), `isValidArcEndToken_tokenOfIndex`,
`partnerIndexOf_sameComponent_or_fixed` (forward partner soundness, census-free),
`partnerIndexOf_below`, `arcNearFarTokens` (an arc's endpoints as valid same-component tokens at
`arcMinPosition`/`arcMaxPosition`), and `isNonCrossing_extractArc_diagram_partner` (the full
translation: `ArcNonCrossing bottomCount state → IsNonCrossing bottomCount (extractArc bottomCount
state).diagram.partner`).  This closes D2a-iv (cup preservation + cap preservation + fold + extract).
What this marker does NOT claim: the leg-aligned cup selector that consumes the planar partition
(D1/D2/D3) or the cup-cancellation FLIP.  `= true`. -/
def fxMode_hasArcNonCrossingExtract : Bool := true

end FX1Poly.Polygraph
