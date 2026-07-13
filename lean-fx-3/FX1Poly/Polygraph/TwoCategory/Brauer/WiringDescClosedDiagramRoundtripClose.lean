import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescExt5CorrectedRoundtripBridge
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescPadCongruence
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcReadOffCount

/-! # BRAUER r55 — THE CLOSED-DIAGRAM (`bottomCount = 0`) ROUNDTRIP CLOSE: the COMPLETE R3-A roundtrip

The r54 bridge (`Brauer/WiringDescExt5CorrectedRoundtripBridge.lean`) delivered the R3-A roundtrip
`standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d) = d` for every well-formed boundary involution
with `0 < d.bottomCount`, and named the sole residual: the `bottomCount = 0` (closed / cup-only / loop-only) class,
unreachable by the frozen `0 < bc` stack (`brauerSeed 0` has `nextFresh = 0`, the r31
`boundedBoundaryComponents_reachable` gate).  This file closes that corner by **route D-pad** and assembles the
COMPLETE all-`bottomCount` roundtrip.

## The route (D-pad, executed as a one-sided LEFT-pad transport)

  * **`padThrough`** embeds a `bc = 0` diagram into `bc = 1` by one through-strand: both boundary ports are added
    and every partner index shifts by `2` with reciprocal edges (`partner := 1 :: 0 :: map (+2)`).  It is injective
    (`unpadThrough` is a computable left inverse) and preserves well-formedness
    (`padThrough_isBoundaryInvolution`), so the FROZEN r54 bridge applies verbatim to the padded diagram
    (`ext5CorrectedRoundtrip_padThrough`).
  * ★★★ **The one-sided left-pad extract transport** (`extractDiagram_padThrough_ofLeftPadSim`): over a
    `MatchingLeftPadSim 1` pair of runs at base boundary `0`, the padded extract IS `padThrough` of the base
    extract — read off the four-zone boundary reads and the pad-inert union-find zones of the shipped left-pad
    simulation (`Brauer/WiringDescPadCongruence.lean`, `FreeTwoCell/MatchingLeftPad*`).  Fed by
    `processBrauer_leftPadSim` over the base word, this gives
    `extractDiagram 1 (fold (shift 1 word)) = padThrough (extractDiagram 0 (fold word))` for ANY in-range word.
  * **The word algebra**: at `bc = 0` the corrected reconstruction collapses (bottom staircase, cap block and
    middle all empty — `pTCW 0 / pTCW 1` are `[]`), and the PADDED reconstruction's word is exactly the
    position-shift of the base word on the cup/crossing prefix (`padMainWord_eq_shift`): the read-offs shift
    (`throughStrandTops` of the pad is `[0]`, `cupArcTops` shifts by one), `permInverse` commutes with the
    fixed-point-`0` shift (`permInverse_zeroConsShift`), and the selection-sort staircase realizer commutes with it
    too (`permutationToCrossingWord_zeroConsShift` — the genuine fold-commutes-with-pad induction the recon
    predicted).  The trailing `circleWord` block does NOT shift (it fires at position `0` regardless); the runs
    agree anyway because a cup-cap circle pair produces the SAME state fired at position `1` or `0` over a
    non-empty wire list (`processBrauer_circlePairPositionIrrelevant`) — the loops>0 trap the recon flagged,
    closed at the fold level.
  * **In-rangeness for free**: the firing discipline `BrauerWordInRange 0 (base word)` is assembled from the
    shipped counting stack — `topReadOffOrderLength` (so the cup block opens EXACTLY `topCount` wires at `bc = 0`),
    `readOffTopOrderInverse_isPermutationOfRange` + `permutationToCrossingWord_posBound` (every staircase crossing
    fits), and the circle pairs are in range at any width.

## What this file ships

  * ★★★ **the STRIP identity** `ext5CorrectedRoundtrip_stripPad`:
    `standardFormDiagramExt5 (reconstructStandardFormExt5Corrected (padThrough d)) = padThrough
    (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d))` for every well-formed `bottomCount = 0`
    diagram — the honest generality this proof route supports (the `#eval` census pins the identity on wider
    inputs, including malformed ones; the validity-independent universal stays an honest residual, named for r56).
  * ★★★ **the `bottomCount = 0` corner** `ext5CorrectedRoundtrip_bottomZero` (strip + padded roundtrip +
    injectivity) and ★★★ **the COMPLETE roundtrip** `ext5CorrectedRoundtrip_complete` — by cases on
    `d.bottomCount`, hypothesis-free except well-formedness — plus the r53 valid-involution-vocabulary form
    `ext5CorrectedRoundtrip_completeOfValidCensus`.
  * ★★ **Brick E — the census-bridge CONVERSE** `isInvolutionPartner_ofIsBoundaryInvolution` (Prop → Bool, the
    exact mirror of the r54 decoders) and the packaged iff `isBoundaryInvolution_iff_validCensus`.
  * ★ the committed `#eval` census re-pins (the recon's 20-valid / 4-malformed table as named defs), the complete
    theorem FIRED on concrete closed diagrams through the GENERAL path, malformed negative controls, and the
    honest terminal state.

## The FLIP (the honest supersession)

`fxBrauer_hasExt5CorrectedRoundtripProof` (`Brauer/WiringDescArcExtractorRec.lean:217`) is pinned `= false` by
`rfl`-conjunctions in eight-plus FROZEN ledgers (`WiringDescStandardFoldR5Ledger`, `WiringDescArcEnumeration`,
`WiringDescReadOffWiring`, `WiringDescCorrectedFold`, `WiringDescArcReadOffPermutation`,
`WiringDescArcReadOffCount`, the r54 terminal state).  Editing it is mechanically FORBIDDEN (it would break every
one of those frozen `rfl`s), so — per the r31/r54 precedent — the flip vehicle is the NEW superseding content
marker `fxBrauer_hasExt5CorrectedRoundtripComplete := true` below, and `:217` stays byte-intact as a
ledger-preservation artifact whose `false` no longer states a truth gap (see the marker's docstring).

Raw Lean 4 + Init.  Zero-axiom: structural recursion only, no `omega` / `simp`-AC / `native_decide` /
`WellFounded.fix`; per-declaration `#assert_no_axioms` in the audit twin plus an independent `#print axioms`
witness file. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## §0 Local propext-free micro-helpers (structural; the shipped twins are `private` to their files) -/

/-- Both-true introduction for `&&` — full-enum `Bool` match, propext-free. -/
private theorem boolAndIntroRt : (leftFlag rightFlag : Bool) → leftFlag = true → rightFlag = true →
    (leftFlag && rightFlag) = true
  | true, _, _, rightTrue => rightTrue
  | false, _, leftTrue, _ => Bool.noConfusion leftTrue

/-- `a ≤ b → Nat.ble a b = true` — structural on both operands. -/
private theorem bleTrueOfLeRt : (a b : Nat) → a ≤ b → Nat.ble a b = true
  | 0, _, _ => rfl
  | a + 1, 0, le => absurd le (Nat.not_succ_le_zero a)
  | a + 1, b + 1, le => bleTrueOfLeRt a b (Nat.le_of_succ_le_succ le)

/-- `a < b → Nat.blt a b = true`. -/
private theorem bltTrueOfLtRt (a b : Nat) (lt : a < b) : Nat.blt a b = true :=
  bleTrueOfLeRt (a + 1) b lt

/-- `Nat.beq n n = true` — structural. -/
private theorem natBeqSelfRt : (n : Nat) → Nat.beq n n = true
  | 0 => rfl
  | n + 1 => natBeqSelfRt n

/-- `a = b → Nat.beq a b = true`. -/
private theorem beqTrueOfEqRt (a b : Nat) (eq : a = b) : Nat.beq a b = true := by
  subst eq; exact natBeqSelfRt a

/-- `a ≠ b → Nat.beq a b = false` — structural. -/
private theorem natBeqFalseOfNeRt : (a b : Nat) → a ≠ b → Nat.beq a b = false
  | 0, 0, ne => absurd rfl ne
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, _ => rfl
  | a + 1, b + 1, ne => natBeqFalseOfNeRt a b (fun eq => ne (congrArg (· + 1) eq))

/-- `a ≠ b → not (Nat.beq a b) = true`. -/
private theorem notBeqTrueOfNeRt (a b : Nat) (ne : a ≠ b) : not (Nat.beq a b) = true := by
  rw [natBeqFalseOfNeRt a b ne]; rfl

/-- An all-true predicate folds to a true `List.all` — the builder mirror of the r54 decoder. -/
private theorem allTrueOfForallMemRt {elementType : Type} (predicate : elementType → Bool) :
    (elements : List elementType) →
    ((element : elementType) → element ∈ elements → predicate element = true) →
    elements.all predicate = true
  | [], _ => rfl
  | head :: rest, hyp =>
      boolAndIntroRt (predicate head) (rest.all predicate)
        (hyp head (List.Mem.head rest))
        (allTrueOfForallMemRt predicate rest (fun element member => hyp element (List.Mem.tail head member)))

/-- Membership in `List.range.loop` splits: below the counter or already in the accumulator. -/
private theorem memRangeLoopSplitRt : (count : Nat) → (acc : List Nat) → (value : Nat) →
    value ∈ List.range.loop count acc → value < count ∨ value ∈ acc
  | 0, _, _, member => Or.inr member
  | count + 1, acc, value, member => by
      have split := memRangeLoopSplitRt count (count :: acc) value member
      cases split with
      | inl belowCount => exact Or.inl (Nat.lt_succ_of_lt belowCount)
      | inr memberCons =>
          cases memberCons with
          | head => exact Or.inl (Nat.lt_succ_self count)
          | tail _ memberAcc => exact Or.inr memberAcc

/-- `value ∈ List.range count → value < count` — the propext-free `List.mem_range.mp`. -/
private theorem ltOfMemRangeRt (value count : Nat) (member : value ∈ List.range count) : value < count := by
  cases memRangeLoopSplitRt count [] value member with
  | inl belowCount => exact belowCount
  | inr memberNil => nomatch memberNil

/-- Membership in the accumulator survives the range loop. -/
private theorem memRangeLoopOfMemAccRt : (count : Nat) → (acc : List Nat) → (value : Nat) →
    value ∈ acc → value ∈ List.range.loop count acc
  | 0, _, _, memAcc => memAcc
  | count + 1, acc, value, memAcc =>
      memRangeLoopOfMemAccRt count (count :: acc) value (List.Mem.tail count memAcc)

/-- Every index below the counter occurs in the range loop. -/
private theorem memRangeLoopOfLtRt : (count : Nat) → (acc : List Nat) → (index : Nat) → index < count →
    index ∈ List.range.loop count acc
  | 0, _, index, below => absurd below (Nat.not_lt_zero index)
  | count + 1, acc, index, below => by
      cases Nat.lt_or_ge index count with
      | inl belowCount => exact memRangeLoopOfLtRt count (count :: acc) index belowCount
      | inr atLeastCount =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_lt_succ below) atLeastCount
          exact indexEq ▸ memRangeLoopOfMemAccRt count (count :: acc) count (List.Mem.head acc)

/-- `index < count → index ∈ List.range count` — the propext-free `List.mem_range.mpr`. -/
private theorem memRangeOfLtRt (index count : Nat) (below : index < count) : index ∈ List.range count :=
  memRangeLoopOfLtRt count [] index below

/-- Map preserves length — local structural copy. -/
private theorem mapLengthRt {alpha beta : Type} (mapFn : alpha → beta) : (elements : List alpha) →
    (elements.map mapFn).length = elements.length
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (mapLengthRt mapFn rest)

/-- Map fuses with map — local structural copy. -/
private theorem mapMapRt {alpha beta gamma : Type} (innerFn : alpha → beta) (outerFn : beta → gamma) :
    (elements : List alpha) → (elements.map innerFn).map outerFn = elements.map (fun value => outerFn (innerFn value))
  | [] => rfl
  | head :: rest => congrArg (outerFn (innerFn head) :: ·) (mapMapRt innerFn outerFn rest)

/-- Pointwise-equal functions map equal lists (the funext-free map congruence). -/
private theorem mapCongrOfMemRt {alpha beta : Type} (leftFn rightFn : alpha → beta) :
    (elements : List alpha) → ((element : alpha) → element ∈ elements → leftFn element = rightFn element) →
    elements.map leftFn = elements.map rightFn
  | [], _ => rfl
  | head :: rest, hyp => by
      rw [List.map, List.map, hyp head (List.Mem.head rest),
        mapCongrOfMemRt leftFn rightFn rest (fun element member => hyp element (List.Mem.tail head member))]

/-- Map distributes over append — local structural copy. -/
private theorem mapAppendRt {alpha beta : Type} (mapFn : alpha → beta) :
    (front rear : List alpha) → (front ++ rear).map mapFn = front.map mapFn ++ rear.map mapFn
  | [], _ => rfl
  | head :: rest, rear => congrArg (mapFn head :: ·) (mapAppendRt mapFn rest rear)

/-- FilterMap fuses with map — local structural copy. -/
private theorem filterMapMapRt {alpha beta gamma : Type} (innerFn : alpha → beta) (chooseFn : beta → Option gamma) :
    (elements : List alpha) →
    (elements.map innerFn).filterMap chooseFn = elements.filterMap (fun value => chooseFn (innerFn value))
  | [] => rfl
  | head :: rest => by
      rw [List.map, List.filterMap, List.filterMap]
      cases chooseFn (innerFn head) with
      | none => exact filterMapMapRt innerFn chooseFn rest
      | some chosen => exact congrArg (chosen :: ·) (filterMapMapRt innerFn chooseFn rest)

/-- Pointwise-equal choosers filterMap equal lists. -/
private theorem filterMapCongrOfMemRt {alpha beta : Type} (leftFn rightFn : alpha → Option beta) :
    (elements : List alpha) → ((element : alpha) → element ∈ elements → leftFn element = rightFn element) →
    elements.filterMap leftFn = elements.filterMap rightFn
  | [], _ => rfl
  | head :: rest, hyp => by
      rw [List.filterMap, List.filterMap, hyp head (List.Mem.head rest),
        filterMapCongrOfMemRt leftFn rightFn rest (fun element member => hyp element (List.Mem.tail head member))]

/-- A constant-`none` chooser filterMaps to the empty list. -/
private theorem filterMapConstNoneRt {alpha beta : Type} :
    (elements : List alpha) → elements.filterMap (fun _ => (none : Option beta)) = []
  | [] => rfl
  | _ :: rest => filterMapConstNoneRt rest

/-- `List.range (count + 1)` is `0` consed onto the shift of `List.range count` — the range shift split. -/
private theorem rangeLoopShiftRt : (count : Nat) → (acc : List Nat) →
    List.range.loop (count + 1) (acc.map (· + 1)) = 0 :: (List.range.loop count acc).map (· + 1)
  | 0, acc => rfl
  | count + 1, acc => by
      show List.range.loop (count + 1) ((count + 1) :: acc.map (· + 1))
        = 0 :: (List.range.loop count (count :: acc)).map (· + 1)
      have consAsMap : (count + 1) :: acc.map (· + 1) = (count :: acc).map (· + 1) := rfl
      rw [consAsMap]
      exact rangeLoopShiftRt count (count :: acc)

/-- `List.range (count + 1) = 0 :: (List.range count).map (· + 1)`. -/
private theorem rangeSuccShiftRt (count : Nat) : List.range (count + 1) = 0 :: (List.range count).map (· + 1) := by
  show List.range.loop (count + 1) [] = 0 :: (List.range.loop count []).map (· + 1)
  have emptyAsMap : ([] : List Nat) = ([] : List Nat).map (· + 1) := rfl
  rw [emptyAsMap]
  exact rangeLoopShiftRt count []

/-- Shifted-list length cancellation: `map (+2)` keeps length. -/
private theorem lengthMapAddTwoRt : (elements : List Nat) →
    (elements.map (fun value => value + 2)).length = elements.length
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (lengthMapAddTwoRt rest)

/-- Reading a `map (+2)` image below its length adds two to the base read. -/
private theorem getAtMapAddTwoRt : (elements : List Nat) → (position : Nat) → position < elements.length →
    natListGetAt (elements.map (fun value => value + 2)) position = natListGetAt elements position + 2
  | [], position, below => absurd below (Nat.not_lt_zero position)
  | _ :: _, 0, _ => rfl
  | _ :: rest, position + 1, below => getAtMapAddTwoRt rest position (Nat.lt_of_succ_lt_succ below)

/-- Reading a `map (+1)` image below its length adds one to the base read. -/
private theorem getAtMapAddOneRt : (elements : List Nat) → (position : Nat) → position < elements.length →
    natListGetAt (elements.map (fun value => value + 1)) position = natListGetAt elements position + 1
  | [], position, below => absurd below (Nat.not_lt_zero position)
  | _ :: _, 0, _ => rfl
  | _ :: rest, position + 1, below => getAtMapAddOneRt rest position (Nat.lt_of_succ_lt_succ below)

/-- The padded total rewrites additively: `(bc + 1) + (tc + 1) = (bc + tc) + 2`. -/
private theorem padTotalEqRt (bottomCount topCount : Nat) :
    (bottomCount + 1) + (topCount + 1) = (bottomCount + topCount) + 2 := by
  rw [Nat.add_succ, Nat.succ_add]

/-- `1` sits below the padded total. -/
private theorem oneLtPadTotalRt (bottomCount topCount : Nat) : 1 < (bottomCount + 1) + (topCount + 1) := by
  rw [padTotalEqRt]; exact Nat.succ_lt_succ (Nat.succ_pos (bottomCount + topCount))

/-- `0` sits below the padded total. -/
private theorem zeroLtPadTotalRt (bottomCount topCount : Nat) : 0 < (bottomCount + 1) + (topCount + 1) := by
  rw [padTotalEqRt]; exact Nat.succ_pos _

/-- A shifted index below the padded total is below the base total. -/
private theorem innerBelowOfPadRt (bottomCount topCount k : Nat)
    (below : k + 2 < (bottomCount + 1) + (topCount + 1)) : k < bottomCount + topCount := by
  rw [padTotalEqRt] at below
  exact Nat.lt_of_add_lt_add_right below

/-! ## §1 Route D-pad: `padThrough` / `unpadThrough` and the padded well-formedness -/

/-- ★ **`padThrough` — one through-strand under a closed diagram.**  Adds one bottom and one top boundary port
wired to each other (`partner` entries `1` and `0` at the front) and shifts every base partner index by `2` —
reciprocal edges preserved, loops untouched.  On a `bottomCount = 0` diagram this reaches `bottomCount = 1`, where
the FROZEN r54 roundtrip stack applies. -/
def padThrough (d : DiagramType) : DiagramType :=
  { bottomCount := d.bottomCount + 1, topCount := d.topCount + 1,
    partner := 1 :: 0 :: d.partner.map (fun value => value + 2), loops := d.loops }

/-- **`unpadThrough` — the computable left inverse of `padThrough`** (drop the through-strand ports, unshift). -/
def unpadThrough (d : DiagramType) : DiagramType :=
  { bottomCount := d.bottomCount - 1, topCount := d.topCount - 1,
    partner := (d.partner.drop 2).map (fun value => value - 2), loops := d.loops }

/-- `map (+2)` then `map (-2)` cancels — the unpad shift cancellation. -/
private theorem mapAddTwoSubTwoCancelRt : (elements : List Nat) →
    (elements.map (fun value => value + 2)).map (fun value => value - 2) = elements
  | [] => rfl
  | head :: rest => congrArg (fun tail => head :: tail) (mapAddTwoSubTwoCancelRt rest)

/-- ★ **`unpadThrough` inverts `padThrough`** — the pad is a section of the unpad. -/
theorem unpadThrough_padThrough (d : DiagramType) : unpadThrough (padThrough d) = d :=
  congrArg (fun replacedPartner => { d with partner := replacedPartner }) (mapAddTwoSubTwoCancelRt d.partner)

/-- ★ **`padThrough` is injective** — via the computable left inverse. -/
theorem padThrough_injective (left right : DiagramType) (padEq : padThrough left = padThrough right) :
    left = right := by
  have lifted := congrArg unpadThrough padEq
  rw [unpadThrough_padThrough, unpadThrough_padThrough] at lifted
  exact lifted

/-- ★★ **The padded partner is a boundary involution** whenever the base partner is: the through-strand ports
partner each other reciprocally and fixed-point-freely, and the shifted base entries inherit every field through
the `+2` index shift. -/
theorem isBoundaryInvolution_padPartner (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner) :
    IsBoundaryInvolution ((bottomCount + 1) + (topCount + 1))
      (1 :: 0 :: partner.map (fun value => value + 2)) where
  hasBoundaryLength := by
    show (partner.map (fun value => value + 2)).length + 2 = (bottomCount + 1) + (topCount + 1)
    rw [lengthMapAddTwoRt, wf.hasBoundaryLength, padTotalEqRt]
  mapsInRange := by
    intro index indexBelow
    match index with
    | 0 => exact oneLtPadTotalRt bottomCount topCount
    | 1 => exact zeroLtPadTotalRt bottomCount topCount
    | k + 2 =>
        have kBelow : k < bottomCount + topCount := innerBelowOfPadRt bottomCount topCount k indexBelow
        have kBelowLen : k < partner.length := wf.hasBoundaryLength ▸ kBelow
        show natListGetAt (partner.map (fun value => value + 2)) k < (bottomCount + 1) + (topCount + 1)
        rw [getAtMapAddTwoRt partner k kBelowLen, padTotalEqRt]
        exact Nat.add_lt_add_right (wf.mapsInRange k kBelow) 2
  isSelfInverse := by
    intro index indexBelow
    match index with
    | 0 => rfl
    | 1 => rfl
    | k + 2 =>
        have kBelow : k < bottomCount + topCount := innerBelowOfPadRt bottomCount topCount k indexBelow
        have kBelowLen : k < partner.length := wf.hasBoundaryLength ▸ kBelow
        have imageBelow : natListGetAt partner k < bottomCount + topCount := wf.mapsInRange k kBelow
        have imageBelowLen : natListGetAt partner k < partner.length := wf.hasBoundaryLength ▸ imageBelow
        show natListGetAt (1 :: 0 :: partner.map (fun value => value + 2))
              (natListGetAt (partner.map (fun value => value + 2)) k) = k + 2
        rw [getAtMapAddTwoRt partner k kBelowLen]
        show natListGetAt (partner.map (fun value => value + 2)) (natListGetAt partner k) = k + 2
        rw [getAtMapAddTwoRt partner (natListGetAt partner k) imageBelowLen, wf.isSelfInverse k kBelow]
  isFixedPointFree := by
    intro index indexBelow
    match index with
    | 0 => exact fun absurdEq => Nat.noConfusion absurdEq
    | 1 => exact fun absurdEq => Nat.noConfusion absurdEq
    | k + 2 =>
        have kBelow : k < bottomCount + topCount := innerBelowOfPadRt bottomCount topCount k indexBelow
        have kBelowLen : k < partner.length := wf.hasBoundaryLength ▸ kBelow
        show natListGetAt (partner.map (fun value => value + 2)) k ≠ k + 2
        rw [getAtMapAddTwoRt partner k kBelowLen]
        exact fun absurdEq =>
          wf.isFixedPointFree k kBelow (Nat.succ.inj (Nat.succ.inj absurdEq))

/-- ★★ **`padThrough` preserves well-formedness**, stated on the diagram fields. -/
theorem padThrough_isBoundaryInvolution (d : DiagramType)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner) :
    IsBoundaryInvolution ((padThrough d).bottomCount + (padThrough d).topCount) (padThrough d).partner :=
  isBoundaryInvolution_padPartner d.bottomCount d.topCount d.partner wf

/-- ★★ **The padded diagram roundtrips** — the FROZEN r54 bridge applied to `padThrough d` (its bottom boundary is
non-empty by construction). -/
theorem ext5CorrectedRoundtrip_padThrough (d : DiagramType)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner) :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected (padThrough d)) = padThrough d :=
  ext5CorrectedRoundtrip_ofPos (padThrough d) (Nat.succ_pos d.bottomCount)
    (padThrough_isBoundaryInvolution d wf)

/-! ## §2 Brick E — the census-bridge CONVERSE (`IsBoundaryInvolution → isInvolutionPartner`) -/

/-- ★★ **Brick E — the r53 census CONVERSE.**  A boundary involution passes the r53 Bool census
`isInvolutionPartner`: every field of the Prop rebuilds its own conjunct through the builder mirrors of the r54
decoders (`Nat.blt` / `Nat.beq` / `List.all` introductions, all structural, propext-free). -/
theorem isInvolutionPartner_ofIsBoundaryInvolution (partner : List Nat) (total : Nat)
    (wf : IsBoundaryInvolution total partner) : isInvolutionPartner partner = true := by
  unfold isInvolutionPartner
  apply allTrueOfForallMemRt
  intro index member
  have indexBelowLen : index < partner.length := ltOfMemRangeRt index partner.length member
  have indexBelow : index < total := wf.hasBoundaryLength ▸ indexBelowLen
  have bltPart : Nat.blt (natListGetAt partner index) partner.length = true :=
    bltTrueOfLtRt _ _ (wf.hasBoundaryLength ▸ wf.mapsInRange index indexBelow)
  have beqPart : Nat.beq (natListGetAt partner (natListGetAt partner index)) index = true :=
    beqTrueOfEqRt _ _ (wf.isSelfInverse index indexBelow)
  have notBeqPart : not (Nat.beq (natListGetAt partner index) index) = true :=
    notBeqTrueOfNeRt _ _ (wf.isFixedPointFree index indexBelow)
  exact boolAndIntroRt _ _ (boolAndIntroRt _ _ bltPart beqPart) notBeqPart

/-- ★★ **The census iff** — the r53 Bool census (plus the boundary-length equation) is EXACTLY the Prop
`IsBoundaryInvolution`: forward by the r54 Brick B decoder `isBoundaryInvolution_ofValidCensus`, backward by
Brick E.  The r53 exact-cut census (`countRepresentativeRealizeXorValid = 0`) now has its Prop-level mirror. -/
theorem isBoundaryInvolution_iff_validCensus (partner : List Nat) (total : Nat) :
    IsBoundaryInvolution total partner
      ↔ (partner.length = total ∧ isInvolutionPartner partner = true) :=
  Iff.intro
    (fun wf => And.intro wf.hasBoundaryLength (isInvolutionPartner_ofIsBoundaryInvolution partner total wf))
    (fun census => isBoundaryInvolution_ofValidCensus partner total census.left census.right)

/-! ## §3 The word algebra — the padded reconstruction's word is the position-shift of the base word
(on the cup/crossing prefix; the trailing circles do not shift and are handled at the fold level in §5) -/

/-- `Nat.blt (a + 2) (b + 2)` peels to `Nat.blt a b` — definitional double-succ reduction. -/
private theorem bltAddTwoBothRt (a b : Nat) : Nat.blt (a + 2) (b + 2) = Nat.blt a b := rfl

/-- `Nat.blt (x + 2) 1 = false` — a shifted partner entry never reads as a bottom port of the pad. -/
private theorem bltAddTwoOneFalseRt (x : Nat) : Nat.blt (x + 2) 1 = false := rfl

/-- `Nat.ble 1 (x + 2) = true` — a shifted partner entry always clears the pad's bottom bound. -/
private theorem bleOneAddTwoTrueRt (x : Nat) : Nat.ble 1 (x + 2) = true := rfl

/-- The decide-based Nat `==` peels a shared successor — via `decide` introduction/elimination (propext-free). -/
private theorem beqSuccBothRt (a b : Nat) : ((a + 1 == b + 1) : Bool) = (a == b) := by
  show decide (a + 1 = b + 1) = decide (a = b)
  cases hDecide : decide (a = b) with
  | true => exact decide_eq_true (congrArg (· + 1) (of_decide_eq_true hDecide))
  | false =>
      exact decide_eq_false (fun succEq => absurd (Nat.succ.inj succEq) (of_decide_eq_false hDecide))

/-- The first-index scan ignores a `map (+1)` shift when the target shifts along — `natIndexOfValue` commutes
with the successor relabeling (unconditional: misses stay misses position-for-position). -/
private theorem indexOfValueMapAddOneRt : (elements : List Nat) → (target : Nat) →
    natIndexOfValue (elements.map (· + 1)) (target + 1) = natIndexOfValue elements target
  | [], _ => rfl
  | head :: rest, target => by
      show (match (head + 1 == target + 1 : Bool) with
            | true => 0
            | false => natIndexOfValue (rest.map (· + 1)) (target + 1) + 1)
          = (match (head == target : Bool) with
            | true => 0
            | false => natIndexOfValue rest target + 1)
      rw [beqSuccBothRt head target]
      cases head == target with
      | true => rfl
      | false => exact congrArg (· + 1) (indexOfValueMapAddOneRt rest target)

/-- ★ **`permInverse` commutes with the fixed-point-`0` shift**: inverting `0 :: map (+1) q` is `0` consed onto
the shift of `permInverse q` — the pad's through-strand stays at position `0` on both sides of the inversion. -/
theorem permInverse_zeroConsShift (basePerm : List Nat) :
    permInverse (0 :: basePerm.map (· + 1)) = 0 :: (permInverse basePerm).map (· + 1) := by
  show (List.range ((basePerm.map (· + 1)).length + 1)).map
        (fun value => natIndexOfValue (0 :: basePerm.map (· + 1)) value)
      = 0 :: (permInverse basePerm).map (· + 1)
  rw [mapLengthRt, rangeSuccShiftRt basePerm.length]
  show natIndexOfValue (0 :: basePerm.map (· + 1)) 0
        :: ((List.range basePerm.length).map (· + 1)).map
            (fun value => natIndexOfValue (0 :: basePerm.map (· + 1)) value)
      = 0 :: (permInverse basePerm).map (· + 1)
  rw [mapMapRt, show permInverse basePerm = (List.range basePerm.length).map
      (fun value => natIndexOfValue basePerm value) from rfl,
    mapMapRt]
  refine congrArg (0 :: ·) (mapCongrOfMemRt _ _ (List.range basePerm.length) ?_)
  intro value _
  show natIndexOfValue (basePerm.map (· + 1)) (value + 1) + 1 = natIndexOfValue basePerm value + 1
  rw [indexOfValueMapAddOneRt basePerm value]

/-- `n - m - k = n - (m + k)` — structural on `k` (the core `Nat.sub_sub` leaks propext). -/
private theorem subSubRt (n m : Nat) : (k : Nat) → n - m - k = n - (m + k)
  | 0 => rfl
  | k + 1 => congrArg Nat.pred (subSubRt n m k)

/-- `(n + m) - n = m` — structural on `n` (the core cancellation lemmas leak propext). -/
private theorem addSubCancelLeftRt : (n m : Nat) → (n + m) - n = m
  | 0, m => Nat.zero_add m
  | n + 1, m => by
      have stepShape : (n + 1) + m = ((n + m) + 1 : Nat) := Nat.succ_add n m
      rw [stepShape]
      exact Eq.trans (Nat.succ_sub_succ (n + m) n) (addSubCancelLeftRt n m)

/-- Append is associative — local structural copy (the core `List.append_assoc` leaks propext). -/
private theorem appendAssocRt {alpha : Type} : (front middle rear : List alpha) →
    (front ++ middle) ++ rear = front ++ (middle ++ rear)
  | [], _, _ => rfl
  | head :: rest, middle, rear => congrArg (head :: ·) (appendAssocRt rest middle rear)

/-- Appending nil is the identity — local structural copy (the core `List.append_nil` leaks propext). -/
private theorem appendNilRt {alpha : Type} : (elements : List alpha) → elements ++ [] = elements
  | [] => rfl
  | head :: rest => congrArg (head :: ·) (appendNilRt rest)

/-- The adjacent swap commutes with any element-wise relabeling (pure position surgery). -/
private theorem applyAdjacentSwapMapRt (relabel : Nat → Nat) :
    (elements : List Nat) → (position : Nat) →
    applyAdjacentSwap (elements.map relabel) position = (applyAdjacentSwap elements position).map relabel
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _, 0 => rfl
  | first :: second :: rest, position + 1 =>
      congrArg (relabel first :: ·) (applyAdjacentSwapMapRt relabel (second :: rest) position)

/-- A shifted-position swap over a `0`-headed shifted list keeps the head and swaps the shifted tail. -/
private theorem applyAdjacentSwapZeroConsRt : (tail : List Nat) → (position : Nat) →
    applyAdjacentSwap (0 :: tail) (position + 1) = 0 :: applyAdjacentSwap tail position
  | [], _ => rfl
  | _ :: _, _ => rfl

/-- The whole bubble fold (shifted positions, `0`-headed shifted working list) is the shift of the base fold. -/
private theorem foldlSwapZeroConsShiftRt : (positions : List Nat) → (currentPerm : List Nat) →
    (positions.map (· + 1)).foldl applyAdjacentSwap (0 :: currentPerm.map (· + 1))
      = 0 :: (positions.foldl applyAdjacentSwap currentPerm).map (· + 1)
  | [], _ => rfl
  | position :: rest, currentPerm => by
      show (rest.map (· + 1)).foldl applyAdjacentSwap
            (applyAdjacentSwap (0 :: currentPerm.map (· + 1)) (position + 1))
          = 0 :: ((rest.foldl applyAdjacentSwap (applyAdjacentSwap currentPerm position)).map (· + 1))
      rw [applyAdjacentSwapZeroConsRt (currentPerm.map (· + 1)) position,
        applyAdjacentSwapMapRt (· + 1) currentPerm position]
      exact foldlSwapZeroConsShiftRt rest (applyAdjacentSwap currentPerm position)

/-- The descending bubble shifts entry-wise when both ends shift. -/
private theorem descendingSwapPositionsShiftRt (endIndex startIndex : Nat) :
    descendingSwapPositions (endIndex + 1) (startIndex + 1)
      = (descendingSwapPositions endIndex startIndex).map (· + 1) := by
  show (List.range ((endIndex + 1) - (startIndex + 1))).map (fun step => (endIndex + 1) - 1 - step)
      = ((List.range (endIndex - startIndex)).map (fun step => endIndex - 1 - step)).map (· + 1)
  rw [Nat.succ_sub_succ endIndex startIndex, mapMapRt]
  refine mapCongrOfMemRt _ _ (List.range (endIndex - startIndex)) ?_
  intro step stepMember
  have stepBelowGap : step < endIndex - startIndex :=
    ltOfMemRangeRt step (endIndex - startIndex) stepMember
  have stepBelowEnd : step < endIndex :=
    Nat.lt_of_lt_of_le stepBelowGap (Nat.sub_le endIndex startIndex)
  show endIndex - step = (endIndex - 1 - step) + 1
  cases Nat.le.dest stepBelowEnd with
  | intro gap gapEq =>
      have endAsSum : endIndex = step + (1 + gap) := by
        rw [← Nat.add_assoc step 1 gap]
        exact gapEq.symm
      have endAsSumFront : endIndex = (1 + step) + gap := by
        rw [Nat.add_comm 1 step, Nat.add_assoc step 1 gap]
        exact endAsSum
      have leftRead : endIndex - step = 1 + gap := by
        rw [endAsSum]
        exact addSubCancelLeftRt step (1 + gap)
      have rightInner : endIndex - 1 - step = gap := by
        rw [subSubRt endIndex 1 step, endAsSumFront]
        exact addSubCancelLeftRt (1 + step) gap
      rw [leftRead, rightInner, Nat.add_comm 1 gap]

/-- The scan past a `0` head for a successor target — one miss, position bumps (definitional). -/
private theorem indexOfZeroConsSuccRt (tail : List Nat) (target : Nat) :
    natIndexOfValue (0 :: tail) (target + 1) = natIndexOfValue tail (target + 1) + 1 := rfl

/-- One-step unfolding of the selection-sort realizer fold (definitional; surfaces the `let`). -/
private theorem realizerFoldStepRt (perm : List Nat) (fuel position : Nat) (currentPerm : List Nat) :
    permutationRealizerFold perm (fuel + 1) position currentPerm
      = descendingSwapPositions (natIndexOfValue currentPerm (natListGetAt perm position)) position
        ++ permutationRealizerFold perm fuel (position + 1)
            ((descendingSwapPositions (natIndexOfValue currentPerm (natListGetAt perm position))
              position).foldl applyAdjacentSwap currentPerm) := rfl

/-- ★ **The realizer fold commutes with the fixed-point-`0` shift** — the genuine selection-sort induction: at
every step the padded run reads the shifted target one position later, finds it one slot later, bubbles it with
the shifted swap positions over the `0`-headed shifted working list, and recurses in lockstep.  The reads stay
in range by the fuel budget `posBase + fuel ≤ basePerm.length`. -/
private theorem realizerFoldZeroConsShiftRt (basePerm : List Nat) :
    (fuel posBase : Nat) → (currentBase : List Nat) →
    posBase + fuel ≤ basePerm.length →
    permutationRealizerFold (0 :: basePerm.map (· + 1)) fuel (posBase + 1) (0 :: currentBase.map (· + 1))
      = (permutationRealizerFold basePerm fuel posBase currentBase).map (· + 1)
  | 0, _, _, _ => rfl
  | fuel + 1, posBase, currentBase, fits => by
      have fitsFlat : (posBase + fuel) + 1 ≤ basePerm.length := by
        rw [Nat.add_assoc posBase fuel 1]
        exact fits
      have posBelow : posBase < basePerm.length :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_add_right posBase fuel)) fitsFlat
      have nextFits : (posBase + 1) + fuel ≤ basePerm.length := by
        rw [Nat.add_assoc posBase 1 fuel, Nat.add_comm 1 fuel]
        exact fits
      rw [realizerFoldStepRt, realizerFoldStepRt]
      have readEq : natListGetAt (0 :: basePerm.map (· + 1)) (posBase + 1)
          = natListGetAt basePerm posBase + 1 := by
        show natListGetAt (basePerm.map (· + 1)) posBase = natListGetAt basePerm posBase + 1
        exact getAtMapAddOneRt basePerm posBase posBelow
      rw [readEq, indexOfZeroConsSuccRt, indexOfValueMapAddOneRt,
        descendingSwapPositionsShiftRt, foldlSwapZeroConsShiftRt,
        realizerFoldZeroConsShiftRt basePerm fuel (posBase + 1)
          ((descendingSwapPositions
            (natIndexOfValue currentBase (natListGetAt basePerm posBase)) posBase).foldl
            applyAdjacentSwap currentBase) nextFits,
        ← mapAppendRt]

/-- ★★ **The staircase realizer commutes with the fixed-point-`0` shift** — prepending an untouched strand `0`
and shifting a one-line permutation shifts its `permutationToCrossingWord` staircase position-wise.  The
fold-commutes-with-pad induction the naive word-shift argument cannot supply. -/
theorem permutationToCrossingWord_zeroConsShift (width : Nat) (basePerm : List Nat)
    (widthFits : width ≤ basePerm.length + 1) :
    permutationToCrossingWord (width + 1) (0 :: basePerm.map (· + 1))
      = (permutationToCrossingWord width basePerm).map (· + 1) := by
  cases width with
  | zero => rfl
  | succ innerWidth =>
      show permutationRealizerFold (0 :: basePerm.map (· + 1)) (innerWidth + 1) 0
          (List.range (innerWidth + 2))
        = (permutationRealizerFold basePerm innerWidth 0 (List.range (innerWidth + 1))).map (· + 1)
      rw [realizerFoldStepRt, rangeSuccShiftRt (innerWidth + 1)]
      have getZero : natListGetAt (0 :: basePerm.map (· + 1)) 0 = 0 := rfl
      rw [getZero]
      have idxZero : natIndexOfValue (0 :: (List.range (innerWidth + 1)).map (· + 1)) 0 = 0 := rfl
      rw [idxZero]
      have bubbleEmpty : descendingSwapPositions 0 0 = [] := rfl
      rw [bubbleEmpty]
      have appendNil : ([] : List Nat)
          ++ permutationRealizerFold (0 :: basePerm.map (· + 1)) innerWidth (0 + 1)
              (([] : List Nat).foldl applyAdjacentSwap
                (0 :: (List.range (innerWidth + 1)).map (· + 1)))
        = permutationRealizerFold (0 :: basePerm.map (· + 1)) innerWidth (0 + 1)
            (0 :: (List.range (innerWidth + 1)).map (· + 1)) := rfl
      rw [appendNil]
      have innerFits : 0 + innerWidth ≤ basePerm.length := by
        rw [Nat.zero_add]
        exact Nat.le_of_succ_le_succ widthFits
      exact realizerFoldZeroConsShiftRt basePerm innerWidth 0 (List.range (innerWidth + 1)) innerFits

/-! ## §4 The padded read-offs — every extractor block of `padThrough` collapses or shifts -/

/-- One-step unfolding of `List.filterMap` on a cons (definitional). -/
private theorem filterMapConsRt {alpha beta : Type} (chooseFn : alpha → Option beta)
    (head : alpha) (rest : List alpha) :
    (head :: rest).filterMap chooseFn
      = match chooseFn head with
        | none => rest.filterMap chooseFn
        | some value => value :: rest.filterMap chooseFn := rfl

/-- A filterMap whose chooser shifts its `some`-images by one IS the shift of the base filterMap. -/
private theorem filterMapShiftImageRt (baseChoose padChoose : Nat → Option Nat) :
    (elements : List Nat) →
    ((element : Nat) → element ∈ elements → padChoose element = (baseChoose element).map (· + 1)) →
    elements.filterMap padChoose = (elements.filterMap baseChoose).map (· + 1)
  | [], _ => rfl
  | head :: rest, hyp => by
      rw [filterMapConsRt padChoose head rest, filterMapConsRt baseChoose head rest,
        hyp head (List.Mem.head rest)]
      cases baseChoose head with
      | none =>
          exact filterMapShiftImageRt baseChoose padChoose rest
            (fun element member => hyp element (List.Mem.tail head member))
      | some value =>
          exact congrArg ((value + 1) :: ·)
            (filterMapShiftImageRt baseChoose padChoose rest
              (fun element member => hyp element (List.Mem.tail head member)))

/-- FilterMap membership inverts to a source element (structural; never the iff). -/
private theorem memFilterMapInvRt {alpha beta : Type} (chooseFn : alpha → Option beta) :
    (elements : List alpha) → (target : beta) → target ∈ elements.filterMap chooseFn →
    ∃ source, source ∈ elements ∧ chooseFn source = some target
  | [], _, member => nomatch member
  | head :: rest, target, member => by
      rw [filterMapConsRt chooseFn head rest] at member
      cases hChoose : chooseFn head with
      | none =>
          rw [hChoose] at member
          have tailWitness := memFilterMapInvRt chooseFn rest target member
          cases tailWitness with
          | intro source sourceData =>
              exact ⟨source, List.Mem.tail head sourceData.left, sourceData.right⟩
      | some value =>
          rw [hChoose] at member
          cases member with
          | head => exact ⟨head, List.Mem.head rest, hChoose⟩
          | tail _ tailMember =>
              have tailWitness := memFilterMapInvRt chooseFn rest target tailMember
              cases tailWitness with
              | intro source sourceData =>
                  exact ⟨source, List.Mem.tail head sourceData.left, sourceData.right⟩

/-- Every smaller-foot cup index of a `bottomCount = 0` diagram sits below `topCount` (its filterMap only ever
emits its range source). -/
private theorem cupArcTopIndicesBoundedRt (topCount : Nat) (partner : List Nat) :
    (index : Nat) → index ∈ cupArcTopIndices 0 topCount partner → index < topCount := by
  intro index member
  have sourceWitness := memFilterMapInvRt _ (List.range topCount) index member
  cases sourceWitness with
  | intro source sourceData =>
      have sourceBelow : source < topCount := ltOfMemRangeRt source topCount sourceData.left
      have chooseEq := sourceData.right
      cases hCondition : (Nat.ble 0 (natListGetAt partner (0 + source))
          && Nat.blt (0 + source) (natListGetAt partner (0 + source))) with
      | true =>
          rw [hCondition] at chooseEq
          have indexEq : index = source := (Option.some.inj chooseEq).symm
          exact indexEq ▸ sourceBelow
      | false =>
          rw [hCondition] at chooseEq
          exact nomatch chooseEq

/-- ★ The padded through-strand bottoms: exactly the pad strand `[0]` (definitional). -/
private theorem throughStrandBottomsPadRt (partner : List Nat) :
    throughStrandBottoms 1 (1 :: 0 :: partner.map (fun value => value + 2)) = [0] := rfl

/-- ★ The padded cap feet: none (the pad bottom partners a top port; definitional). -/
private theorem capArcFeetIndicesPadRt (partner : List Nat) :
    capArcFeetIndices 1 (1 :: 0 :: partner.map (fun value => value + 2)) = [] := rfl

/-- The double-cons read at a twice-shifted index lands in the shifted partner block (definitional). -/
private theorem padPartnerReadPeelRt (partner : List Nat) (index : Nat) :
    natListGetAt (1 :: 0 :: partner.map (fun value => value + 2)) ((index + 1) + 1)
      = natListGetAt (partner.map (fun value => value + 2)) index := rfl

/-- ★ The padded through-strand tops: exactly the pad strand `[0]` — every shifted top reads a `+2` partner,
never a bottom port. -/
private theorem throughStrandTopsPadRt (topCount : Nat) (partner : List Nat)
    (lengthEq : partner.length = topCount) :
    throughStrandTops 1 (topCount + 1) (1 :: 0 :: partner.map (fun value => value + 2)) = [0] := by
  show (List.range (topCount + 1)).filterMap _ = [0]
  rw [rangeSuccShiftRt topCount, filterMapConsRt, filterMapMapRt]
  show (0 : Nat) :: (List.range topCount).filterMap _ = [0]
  refine congrArg (0 :: ·) ?_
  rw [filterMapCongrOfMemRt _ (fun _ => (none : Option Nat)) (List.range topCount) ?_,
    filterMapConstNoneRt]
  intro index member
  have indexBelowLen : index < partner.length := by
    rw [lengthEq]
    exact ltOfMemRangeRt index topCount member
  show (match Nat.blt (natListGetAt (1 :: 0 :: partner.map (fun value => value + 2)) (1 + (index + 1))) 1 with
        | true => some (index + 1)
        | false => none)
      = none
  rw [Nat.add_comm 1 (index + 1), padPartnerReadPeelRt partner index,
    getAtMapAddTwoRt partner index indexBelowLen]
  rfl

/-- ★ The padded smaller-foot cup indices are the shift of the base ones — the pad top is a through leg (head
`none`), every shifted top keeps its cup verdict verbatim. -/
private theorem cupArcTopIndicesPadRt (topCount : Nat) (partner : List Nat)
    (lengthEq : partner.length = topCount) :
    cupArcTopIndices 1 (topCount + 1) (1 :: 0 :: partner.map (fun value => value + 2))
      = (cupArcTopIndices 0 topCount partner).map (· + 1) := by
  show (List.range (topCount + 1)).filterMap _
      = ((List.range topCount).filterMap _).map (· + 1)
  rw [rangeSuccShiftRt topCount, filterMapConsRt, filterMapMapRt]
  show (List.range topCount).filterMap _
      = ((List.range topCount).filterMap _).map (· + 1)
  refine filterMapShiftImageRt _ _ (List.range topCount) ?_
  intro index member
  have indexBelowLen : index < partner.length := by
    rw [lengthEq]
    exact ltOfMemRangeRt index topCount member
  show (match (Nat.ble 1 (natListGetAt (1 :: 0 :: partner.map (fun value => value + 2)) (1 + (index + 1)))
          && Nat.blt (1 + (index + 1))
            (natListGetAt (1 :: 0 :: partner.map (fun value => value + 2)) (1 + (index + 1)))) with
        | true => some (index + 1)
        | false => none)
      = (match (Nat.ble 0 (natListGetAt partner (0 + index))
          && Nat.blt (0 + index) (natListGetAt partner (0 + index))) with
        | true => some index
        | false => none).map (· + 1)
  rw [Nat.add_comm 1 (index + 1), padPartnerReadPeelRt partner index,
    getAtMapAddTwoRt partner index indexBelowLen, Nat.zero_add index]
  show (match Nat.blt index (natListGetAt partner index) with
        | true => some (index + 1)
        | false => (none : Option Nat))
      = (match Nat.blt index (natListGetAt partner index) with
        | true => some index
        | false => (none : Option Nat)).map (· + 1)
  cases Nat.blt index (natListGetAt partner index) with
  | true => rfl
  | false => rfl

/-- ★ The padded cup arc top legs are the shift of the base ones (pair expansion shifts leg-wise). -/
private theorem expandCupTopPairsShiftRt (partner : List Nat) :
    (indices : List Nat) → ((index : Nat) → index ∈ indices → index < partner.length) →
    expandCupTopPairs 1 (1 :: 0 :: partner.map (fun value => value + 2)) (indices.map (· + 1))
      = (expandCupTopPairs 0 partner indices).map (· + 1)
  | [], _ => rfl
  | index :: rest, boundHyp => by
      show (index + 1)
            :: (natListGetAt (1 :: 0 :: partner.map (fun value => value + 2)) (1 + (index + 1)) - 1)
            :: expandCupTopPairs 1 (1 :: 0 :: partner.map (fun value => value + 2)) (rest.map (· + 1))
          = ((index :: (natListGetAt partner (0 + index) - 0) :: expandCupTopPairs 0 partner rest).map (· + 1))
      rw [Nat.add_comm 1 (index + 1), padPartnerReadPeelRt partner index,
        getAtMapAddTwoRt partner index (boundHyp index (List.Mem.head rest)), Nat.zero_add index]
      show (index + 1) :: (natListGetAt partner index + 1)
            :: expandCupTopPairs 1 (1 :: 0 :: partner.map (fun value => value + 2)) (rest.map (· + 1))
          = (index + 1) :: (natListGetAt partner index + 1) :: (expandCupTopPairs 0 partner rest).map (· + 1)
      exact congrArg ((index + 1) :: (natListGetAt partner index + 1) :: ·)
        (expandCupTopPairsShiftRt partner rest
          (fun element member => boundHyp element (List.Mem.tail index member)))

/-- ★ The padded cup arc tops shift by one. -/
private theorem cupArcTopsPadRt (topCount : Nat) (partner : List Nat)
    (lengthEq : partner.length = topCount) :
    cupArcTops 1 (topCount + 1) (1 :: 0 :: partner.map (fun value => value + 2))
      = (cupArcTops 0 topCount partner).map (· + 1) := by
  show expandCupTopPairs 1 (1 :: 0 :: partner.map (fun value => value + 2))
        (cupArcTopIndices 1 (topCount + 1) (1 :: 0 :: partner.map (fun value => value + 2)))
      = (expandCupTopPairs 0 partner (cupArcTopIndices 0 topCount partner)).map (· + 1)
  rw [cupArcTopIndicesPadRt topCount partner lengthEq]
  exact expandCupTopPairsShiftRt partner (cupArcTopIndices 0 topCount partner)
    (fun index member => by
      rw [lengthEq]
      exact cupArcTopIndicesBoundedRt topCount partner index member)

/-- The base through-strand tops at `bottomCount = 0` are empty (no partner reads below zero). -/
private theorem throughStrandTopsBaseEmptyRt (topCount : Nat) (partner : List Nat) :
    throughStrandTops 0 topCount partner = [] := by
  show (List.range topCount).filterMap _ = []
  refine Eq.trans (filterMapCongrOfMemRt _ (fun _ => (none : Option Nat)) (List.range topCount) ?_)
    (filterMapConstNoneRt (List.range topCount))
  intro index _
  rfl

/-- The base top read-off order at `bottomCount = 0` is the cup tops alone. -/
private theorem baseTopOrderRt (topCount : Nat) (partner : List Nat) :
    throughStrandTops 0 topCount partner ++ cupArcTops 0 topCount partner
      = cupArcTops 0 topCount partner := by
  rw [throughStrandTopsBaseEmptyRt topCount partner]
  rfl

/-- ★ **The counting fact at `bottomCount = 0`** — the cup tops enumerate the WHOLE top boundary:
`|cupArcTops| = topCount` (the shipped r16 width-length identity with the empty through block). -/
private theorem cupArcTopsLengthBaseRt (topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (0 + topCount) partner) :
    (cupArcTops 0 topCount partner).length = topCount := by
  have fullLength := topReadOffOrderLength 0 topCount partner wf
  rw [throughStrandTopsBaseEmptyRt topCount partner] at fullLength
  exact fullLength

/-! ## §5 The two words — the padded reconstruction's word vs the shifted base word -/

/-- The position shift distributes over word concatenation. -/
private theorem shiftBrauerWordAppendRt (delta : Nat) : (front rear : List BrauerAtom) →
    shiftBrauerWord delta (front ++ rear) = shiftBrauerWord delta front ++ shiftBrauerWord delta rear
  | [], _ => rfl
  | atom :: rest, rear => by
      show ({ position := delta + atom.position, wiring := atom.wiring } : BrauerAtom)
            :: shiftBrauerWord delta (rest ++ rear)
          = ({ position := delta + atom.position, wiring := atom.wiring } : BrauerAtom)
            :: (shiftBrauerWord delta rest ++ shiftBrauerWord delta rear)
      exact congrArg (_ :: ·) (shiftBrauerWordAppendRt delta rest rear)

/-- Shifting the position-`0` cup block by one is the position-`1` cup block. -/
private theorem cupWordReplicateShiftRt : (count : Nat) →
    shiftBrauerWord 1 (cupWord (natReplicate count 0)) = cupWord (natReplicate count 1)
  | 0 => rfl
  | count + 1 => congrArg (cupAt 1 :: ·) (cupWordReplicateShiftRt count)

/-- Shifting a crossing word by one shifts its positions element-wise. -/
private theorem crossingWordShiftRt : (positions : List Nat) →
    shiftBrauerWord 1 (crossingWord positions) = crossingWord (positions.map (· + 1))
  | [] => rfl
  | position :: rest => by
      show ({ position := 1 + position, wiring := crossingWiring } : BrauerAtom)
            :: shiftBrauerWord 1 (crossingWord rest)
          = ({ position := position + 1, wiring := crossingWiring } : BrauerAtom)
            :: crossingWord (rest.map (· + 1))
      rw [Nat.add_comm 1 position, crossingWordShiftRt rest]

/-- ★ **The base word collapse at `bottomCount = 0`** — the bottom staircase, cap block and middle are all empty
(definitional), leaving cups, the top staircase and the circles. -/
private theorem baseWordCollapseRt (topCount : Nat) (partner : List Nat) (loops : Nat) :
    standardFormWordExt5 (reconstructStandardFormExt5Corrected
        { bottomCount := 0, topCount := topCount, partner := partner, loops := loops })
      = cupWord (natReplicate (cupArcTopIndices 0 topCount partner).length 0)
        ++ crossingWord (permutationToCrossingWord topCount
            (permInverse (throughStrandTops 0 topCount partner ++ cupArcTops 0 topCount partner)))
        ++ circleWord loops := rfl

/-- ★★ **The padded reconstruction collapses** — bottom staircase / cap block / middle are empty (the pad strand
is the sole bottom, a through leg), the cup block sits one position right, and the top staircase is the
position-shift of the base staircase (the read-off shifts + the `permInverse` and realizer shift laws). -/
private theorem padFormCollapseRt (topCount : Nat) (partner : List Nat) (loops : Nat)
    (lengthEq : partner.length = topCount)
    (widthBound : topCount ≤ (cupArcTops 0 topCount partner).length + 1) :
    reconstructStandardFormExt5Corrected (padThrough
        { bottomCount := 0, topCount := topCount, partner := partner, loops := loops })
      = { bottomCount := 1, bottomPerm := [], capBlock := [], middle := [],
          cupBlock := natReplicate (cupArcTopIndices 0 topCount partner).length 1,
          topPerm := (permutationToCrossingWord topCount
            (permInverse (cupArcTops 0 topCount partner))).map (· + 1),
          loops := loops } := by
  show ({ bottomCount := 1, bottomPerm := [], capBlock := [], middle := [],
          cupBlock := natReplicate
            (cupArcTopIndices 1 (topCount + 1) (1 :: 0 :: partner.map (fun value => value + 2))).length 1,
          topPerm := permutationToCrossingWord (topCount + 1)
            (permInverse (throughStrandTops 1 (topCount + 1) (1 :: 0 :: partner.map (fun value => value + 2))
              ++ cupArcTops 1 (topCount + 1) (1 :: 0 :: partner.map (fun value => value + 2)))),
          loops := loops } : BrauerStandardFormExt5) = _
  rw [cupArcTopIndicesPadRt topCount partner lengthEq, mapLengthRt,
    throughStrandTopsPadRt topCount partner lengthEq, cupArcTopsPadRt topCount partner lengthEq]
  have appendShape : ([0] : List Nat) ++ (cupArcTops 0 topCount partner).map (· + 1)
      = 0 :: (cupArcTops 0 topCount partner).map (· + 1) := rfl
  rw [appendShape, permInverse_zeroConsShift (cupArcTops 0 topCount partner),
    permutationToCrossingWord_zeroConsShift topCount (permInverse (cupArcTops 0 topCount partner))
      (by rw [permInverse_length]; exact widthBound)]

/-- ★★ **The padded word collapse** — the realized word of the padded reconstruction. -/
private theorem padWordCollapseRt (topCount : Nat) (partner : List Nat) (loops : Nat)
    (lengthEq : partner.length = topCount)
    (widthBound : topCount ≤ (cupArcTops 0 topCount partner).length + 1) :
    standardFormWordExt5 (reconstructStandardFormExt5Corrected (padThrough
        { bottomCount := 0, topCount := topCount, partner := partner, loops := loops }))
      = cupWord (natReplicate (cupArcTopIndices 0 topCount partner).length 1)
        ++ crossingWord ((permutationToCrossingWord topCount
            (permInverse (cupArcTops 0 topCount partner))).map (· + 1))
        ++ circleWord loops := by
  rw [padFormCollapseRt topCount partner loops lengthEq widthBound]
  rfl

/-- ★★ **The shifted base word** — position-shifting the whole base word shifts cups and staircase into the
padded word's prefix; ONLY the trailing circle block differs (it shifts here, it does not in the padded word). -/
private theorem shiftedBaseWordRt (topCount : Nat) (partner : List Nat) (loops : Nat) :
    shiftBrauerWord 1 (standardFormWordExt5 (reconstructStandardFormExt5Corrected
        { bottomCount := 0, topCount := topCount, partner := partner, loops := loops }))
      = cupWord (natReplicate (cupArcTopIndices 0 topCount partner).length 1)
        ++ crossingWord ((permutationToCrossingWord topCount
            (permInverse (cupArcTops 0 topCount partner))).map (· + 1))
        ++ shiftBrauerWord 1 (circleWord loops) := by
  rw [baseWordCollapseRt topCount partner loops, shiftBrauerWordAppendRt, shiftBrauerWordAppendRt,
    cupWordReplicateShiftRt, crossingWordShiftRt, baseTopOrderRt topCount partner]

/-! ## §6 The firing discipline — the base word is in range at boundary `0` (the counting stack pays) -/

/-- The cup generator is tag-well-formed. -/
private theorem cupTagsInRangeRt : WiringDescTagsInRange cupWiring := by
  intro arc member
  cases member with
  | head => exact ⟨by decide, by decide⟩
  | tail _ tailMember => nomatch tailMember

/-- The cap generator is tag-well-formed. -/
private theorem capTagsInRangeRt : WiringDescTagsInRange capWiring := by
  intro arc member
  cases member with
  | head => exact ⟨by decide, by decide⟩
  | tail _ tailMember => nomatch tailMember

/-- The crossing generator is tag-well-formed. -/
private theorem crossingTagsInRangeRt : WiringDescTagsInRange crossingWiring := by
  intro arc member
  cases member with
  | head => exact ⟨by decide, by decide⟩
  | tail _ tailMember =>
      cases tailMember with
      | head => exact ⟨by decide, by decide⟩
      | tail _ deeperMember => nomatch deeperMember

/-- Doubling a successor: `(n + 1) + (n + 1) = (n + n) + 2`. -/
private theorem doubleSuccRt (n : Nat) : (n + 1) + (n + 1) = (n + n) + 2 := by
  rw [Nat.add_assoc n 1 (n + 1), Nat.add_comm 1 (n + 1), ← Nat.add_assoc n (n + 1) 1,
    ← Nat.add_assoc n n 1]

/-- A block of position-`0` cups is in range at any starting width; each cup widens the boundary by two. -/
private theorem cupsInRangeRt : (count width : Nat) → (tail : List BrauerAtom) →
    BrauerWordInRange (width + (count + count)) tail →
    BrauerWordInRange width (cupWord (natReplicate count 0) ++ tail)
  | 0, _, _, tailRange => tailRange
  | count + 1, width, tail, tailRange => by
      show BrauerWordInRange width (cupAt 0 :: (cupWord (natReplicate count 0) ++ tail))
      refine BrauerWordInRange.cons (cupAt 0) width ?_ cupTagsInRangeRt ?_
      · exact (Nat.zero_add width).symm
      · have arithShape : width + ((count + 1) + (count + 1)) = 2 + width + (count + count) := by
          rw [doubleSuccRt count, Nat.add_comm 2 width, Nat.add_assoc width 2 (count + count),
            Nat.add_comm 2 (count + count), ← Nat.add_assoc width (count + count) 2]
        exact cupsInRangeRt count (2 + width) tail (arithShape ▸ tailRange)

/-- A crossing word whose positions all fit the width is in range there (crossings preserve the width). -/
private theorem crossingsInRangeRt : (positions : List Nat) → (width : Nat) → (tail : List BrauerAtom) →
    ((position : Nat) → position ∈ positions → position + 2 ≤ width) →
    BrauerWordInRange width tail →
    BrauerWordInRange width (crossingWord positions ++ tail)
  | [], _, _, _, tailRange => tailRange
  | position :: rest, width, tail, positionsFit, tailRange => by
      show BrauerWordInRange width (crossingAt position :: (crossingWord rest ++ tail))
      cases Nat.le.dest (positionsFit position (List.Mem.head rest)) with
      | intro rightLen widthEq =>
          refine BrauerWordInRange.cons (crossingAt position) rightLen ?_ crossingTagsInRangeRt ?_
          · exact widthEq.symm
          · exact widthEq.symm ▸ crossingsInRangeRt rest width tail
              (fun innerPosition member => positionsFit innerPosition (List.Mem.tail position member))
              tailRange

/-- The circle word is in range at ANY width — each cup opens its own pair, the cap closes it. -/
private theorem circlesInRangeRt : (loopCount width : Nat) → BrauerWordInRange width (circleWord loopCount)
  | 0, width => BrauerWordInRange.nil width
  | loopCount + 1, width => by
      show BrauerWordInRange width (cupAt 0 :: capAt 0 :: circleWord loopCount)
      refine BrauerWordInRange.cons (cupAt 0) width ?_ cupTagsInRangeRt ?_
      · exact (Nat.zero_add width).symm
      · refine BrauerWordInRange.cons (capAt 0) width rfl capTagsInRangeRt ?_
        exact (Nat.zero_add width).symm ▸ circlesInRangeRt loopCount width

/-- The cup count doubles to the whole top boundary at `bottomCount = 0` (the r16 counting stack). -/
private theorem cupPairCountRt (topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (0 + topCount) partner) :
    (cupArcTopIndices 0 topCount partner).length + (cupArcTopIndices 0 topCount partner).length
      = topCount := by
  have expandLength : (cupArcTops 0 topCount partner).length
      = (cupArcTopIndices 0 topCount partner).length + (cupArcTopIndices 0 topCount partner).length :=
    expandCupTopPairs_length 0 partner (cupArcTopIndices 0 topCount partner)
  rw [cupArcTopsLengthBaseRt topCount partner wf] at expandLength
  exact expandLength.symm

/-- ★ **The base word is in range at boundary `0`** — the cups open exactly `topCount` wires (the counting
identity), the staircase positions fit by the shipped position bound over the shipped range-permutation witness,
and the circles fit anywhere. -/
private theorem baseWordInRangeRt (topCount : Nat) (partner : List Nat) (loops : Nat)
    (wf : IsBoundaryInvolution (0 + topCount) partner) :
    BrauerWordInRange 0 (standardFormWordExt5 (reconstructStandardFormExt5Corrected
      { bottomCount := 0, topCount := topCount, partner := partner, loops := loops })) := by
  rw [baseWordCollapseRt topCount partner loops,
    appendAssocRt (cupWord (natReplicate (cupArcTopIndices 0 topCount partner).length 0))
      (crossingWord (permutationToCrossingWord topCount
        (permInverse (throughStrandTops 0 topCount partner ++ cupArcTops 0 topCount partner))))
      (circleWord loops)]
  refine cupsInRangeRt (cupArcTopIndices 0 topCount partner).length 0 _ ?_
  have atTopBoundary : BrauerWordInRange topCount
      (crossingWord (permutationToCrossingWord topCount
          (permInverse (throughStrandTops 0 topCount partner ++ cupArcTops 0 topCount partner)))
        ++ circleWord loops) := by
    refine crossingsInRangeRt _ topCount (circleWord loops) ?_ (circlesInRangeRt loops topCount)
    intro position member
    exact permutationToCrossingWord_posBound topCount
      (permInverse (throughStrandTops 0 topCount partner ++ cupArcTops 0 topCount partner))
      (readOffTopOrderInverse_isPermutationOfRange 0 topCount partner wf).isBounded
      position member
  exact (Nat.zero_add _).symm ▸ ((cupPairCountRt topCount partner wf).symm ▸ atTopBoundary)

/-- The cup/crossing PREFIX of the base word is in range at boundary `0` (for the mid-state width fact). -/
private theorem basePrefixInRangeRt (topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (0 + topCount) partner) :
    BrauerWordInRange 0
      (cupWord (natReplicate (cupArcTopIndices 0 topCount partner).length 0)
        ++ crossingWord (permutationToCrossingWord topCount
            (permInverse (throughStrandTops 0 topCount partner ++ cupArcTops 0 topCount partner)))) := by
  refine cupsInRangeRt (cupArcTopIndices 0 topCount partner).length 0 _ ?_
  have crossingsAlone := crossingsInRangeRt (permutationToCrossingWord topCount
      (permInverse (throughStrandTops 0 topCount partner ++ cupArcTops 0 topCount partner)))
    topCount [] (fun position member =>
      permutationToCrossingWord_posBound topCount
        (permInverse (throughStrandTops 0 topCount partner ++ cupArcTops 0 topCount partner))
        (readOffTopOrderInverse_isPermutationOfRange 0 topCount partner wf).isBounded
        position member)
    (BrauerWordInRange.nil topCount)
  have appendNilShape : crossingWord (permutationToCrossingWord topCount
        (permInverse (throughStrandTops 0 topCount partner ++ cupArcTops 0 topCount partner))) ++ []
      = crossingWord (permutationToCrossingWord topCount
          (permInverse (throughStrandTops 0 topCount partner ++ cupArcTops 0 topCount partner))) :=
    appendNilRt _
  rw [appendNilShape] at crossingsAlone
  exact (Nat.zero_add _).symm ▸ ((cupPairCountRt topCount partner wf).symm ▸ crossingsAlone)

/-! ## §7 The ONE-SIDED left-pad extract transport — the padded extract IS `padThrough` of the base extract -/

/-- Reading `List.range (count + 2)` splits as `0`, `1`, then the double shift of `List.range count`. -/
private theorem rangeSplitTwoRt (count : Nat) :
    List.range (count + 2) = 0 :: 1 :: (List.range count).map (fun value => (value + 1) + 1) := by
  rw [rangeSuccShiftRt (count + 1), rangeSuccShiftRt count]
  show 0 :: ((0 :: (List.range count).map (· + 1)).map (· + 1))
      = 0 :: 1 :: (List.range count).map (fun value => (value + 1) + 1)
  rw [show ((0 :: (List.range count).map (· + 1)).map (· + 1))
      = 1 :: ((List.range count).map (· + 1)).map (· + 1) from rfl,
    mapMapRt]


/-- The shifted-candidate scan mirrors the base scan two positions later — per candidate, the exclusion test
peels two successors and the root test defers through the componentComm of the simulation. -/
private theorem scanShiftRt (baseLinks padLinks : List (Nat × Nat)) (baseWires padWires : List Nat)
    (readShiftHyp : (offset : Nat) → offset < baseWires.length →
      natListGetAt (List.range 1 ++ padWires) ((offset + 1) + 1) = natListGetAt baseWires offset + 1)
    (componentShift : (leftNode rightNode : Nat) →
      (unionFindRootOf padLinks (leftNode + 1) == unionFindRootOf padLinks (rightNode + 1))
        = (unionFindRootOf baseLinks leftNode == unionFindRootOf baseLinks rightNode))
    (excludeBase : Nat) :
    (candidates : List Nat) →
    ((candidate : Nat) → candidate ∈ candidates → candidate < baseWires.length) →
    findPartnerScan padLinks (List.range 1 ++ padWires)
        (unionFindRootOf padLinks (natListGetAt baseWires excludeBase + 1))
        ((excludeBase + 1) + 1) (candidates.map (fun value => (value + 1) + 1))
      = findPartnerScan baseLinks (List.range 0 ++ baseWires)
          (unionFindRootOf baseLinks (natListGetAt baseWires excludeBase))
          excludeBase candidates + 2
  | [], _ => rfl
  | candidate :: rest, candidatesBelow => by
      show findPartnerScan padLinks (List.range 1 ++ padWires)
          (unionFindRootOf padLinks (natListGetAt baseWires excludeBase + 1))
          ((excludeBase + 1) + 1)
          (((candidate + 1) + 1) :: rest.map (fun value => (value + 1) + 1))
        = findPartnerScan baseLinks (List.range 0 ++ baseWires)
            (unionFindRootOf baseLinks (natListGetAt baseWires excludeBase))
            excludeBase (candidate :: rest) + 2
      rw [findPartnerScan_cons, findPartnerScan_cons]
      have candidateBelow : candidate < baseWires.length :=
        candidatesBelow candidate (List.Mem.head rest)
      have beqPeeled : ((candidate + 1) + 1 == (excludeBase + 1) + 1) = (candidate == excludeBase) := by
        rw [beqSuccBothRt (candidate + 1) (excludeBase + 1), beqSuccBothRt candidate excludeBase]
      have bneShape : (((candidate + 1) + 1 : Nat) != (excludeBase + 1) + 1)
          = ((candidate : Nat) != excludeBase) :=
        congrArg (fun flag => !flag) beqPeeled
      have rootShape : (unionFindRootOf padLinks
            (natListGetAt (List.range 1 ++ padWires) ((candidate + 1) + 1))
            == unionFindRootOf padLinks (natListGetAt baseWires excludeBase + 1))
          = (unionFindRootOf baseLinks
              (natListGetAt (List.range 0 ++ baseWires) candidate)
            == unionFindRootOf baseLinks (natListGetAt baseWires excludeBase)) := by
        rw [readShiftHyp candidate candidateBelow]
        exact componentShift (natListGetAt baseWires candidate)
          (natListGetAt baseWires excludeBase)
      rw [bneShape, rootShape]
      cases hCondition : ((candidate : Nat) != excludeBase)
          && (unionFindRootOf baseLinks
              (natListGetAt (List.range 0 ++ baseWires) candidate)
            == unionFindRootOf baseLinks (natListGetAt baseWires excludeBase)) with
      | true => rfl
      | false =>
          exact scanShiftRt baseLinks padLinks baseWires padWires readShiftHyp componentShift
            excludeBase rest
            (fun innerCandidate member => candidatesBelow innerCandidate (List.Mem.tail candidate member))

/-- ★★★ **The one-sided left-pad extract transport (`delta = 1`, base boundary `0`).**  Over a left-pad-simulated
pair of runs, the padded extract IS `padThrough` of the base extract: the pad wire `0` reads at padded boundary
indices `0` and `1` (its own component, the through-strand), and every shifted index scans to the shift of the
base partner through the componentComm / pad-inert zones of the simulation. -/
theorem extractDiagram_padThrough_ofLeftPadSim (baseState padState : WireState)
    (sim : MatchingLeftPadSim 1 (padIdentifiers 0 1) baseState padState) :
    extractDiagram 1 padState = padThrough (extractDiagram 0 baseState) := by
  have padWiresShape : padState.openWires
      = 0 :: baseState.openWires.map (fun value => value + 1) := by
    rw [sim.openMap]
    show [0] ++ baseState.openWires.map (freshShiftAbove 0 1)
        = 0 :: baseState.openWires.map (fun value => value + 1)
    rw [mapCongrOfMemRt (freshShiftAbove 0 1) (fun value => value + 1) baseState.openWires
      (fun _ _ => rfl)]
    rfl
  have topCountShape : padState.openWires.length = baseState.openWires.length + 1 := by
    rw [padWiresShape]
    show (baseState.openWires.map (fun value => value + 1)).length + 1
        = baseState.openWires.length + 1
    rw [mapLengthRt]
  have readZero : natListGetAt (List.range 1 ++ padState.openWires) 0 = 0 := by
    rw [padWiresShape]
    rfl
  have readOne : natListGetAt (List.range 1 ++ padState.openWires) 1 = 0 := by
    rw [padWiresShape]
    rfl
  have readShift : (offset : Nat) → offset < baseState.openWires.length →
      natListGetAt (List.range 1 ++ padState.openWires) ((offset + 1) + 1)
        = natListGetAt baseState.openWires offset + 1 := by
    intro offset offsetBelow
    rw [padWiresShape]
    exact getAtMapAddOneRt baseState.openWires offset offsetBelow
  have padRootZero : unionFindRootOf padState.links 0 = 0 :=
    sim.padRootsFixed 0 (Nat.succ_pos 0)
  have shiftRootHigh : (node : Nat) → 1 ≤ unionFindRootOf padState.links (node + 1) := by
    intro node
    exact sim.rootAvoidsPad (node + 1) (Nat.succ_le_succ (Nat.zero_le node))
  have componentShift : (leftNode rightNode : Nat) →
      (unionFindRootOf padState.links (leftNode + 1) == unionFindRootOf padState.links (rightNode + 1))
        = (unionFindRootOf baseState.links leftNode == unionFindRootOf baseState.links rightNode) := by
    intro leftNode rightNode
    exact sim.componentComm leftNode rightNode
  have zeroBeqRootFalse : (node : Nat) →
      ((0 : Nat) == unionFindRootOf padState.links (node + 1)) = false := by
    intro node
    refine decide_eq_false ?_
    intro zeroEq
    have rootHigh := shiftRootHigh node
    rw [← zeroEq] at rootHigh
    exact Nat.not_succ_le_zero 0 rootHigh
  have totalShape : 1 + padState.openWires.length = baseState.openWires.length + 2 := by
    rw [topCountShape, Nat.add_comm 1 (baseState.openWires.length + 1)]
  have partnerZero : partnerIndexOf padState.links (List.range 1 ++ padState.openWires)
      (baseState.openWires.length + 2) 0 = 1 := by
    show findPartnerScan padState.links (List.range 1 ++ padState.openWires)
        (unionFindRootOf padState.links (natListGetAt (List.range 1 ++ padState.openWires) 0)) 0
        (List.range (baseState.openWires.length + 2)) = 1
    rw [rangeSplitTwoRt baseState.openWires.length, findPartnerScan_cons, findPartnerScan_cons,
      readZero, readOne, padRootZero]
    rfl
  have partnerOne : partnerIndexOf padState.links (List.range 1 ++ padState.openWires)
      (baseState.openWires.length + 2) 1 = 0 := by
    show findPartnerScan padState.links (List.range 1 ++ padState.openWires)
        (unionFindRootOf padState.links (natListGetAt (List.range 1 ++ padState.openWires) 1)) 1
        (List.range (baseState.openWires.length + 2)) = 0
    rw [rangeSplitTwoRt baseState.openWires.length, findPartnerScan_cons,
      readZero, readOne, padRootZero]
    rfl
  have partnerShift : (index : Nat) → index < baseState.openWires.length →
      partnerIndexOf padState.links (List.range 1 ++ padState.openWires)
          (baseState.openWires.length + 2) ((index + 1) + 1)
        = partnerIndexOf baseState.links (List.range 0 ++ baseState.openWires)
            baseState.openWires.length index + 2 := by
    intro index indexBelow
    show findPartnerScan padState.links (List.range 1 ++ padState.openWires)
        (unionFindRootOf padState.links
          (natListGetAt (List.range 1 ++ padState.openWires) ((index + 1) + 1)))
        ((index + 1) + 1) (List.range (baseState.openWires.length + 2))
      = findPartnerScan baseState.links (List.range 0 ++ baseState.openWires)
          (unionFindRootOf baseState.links
            (natListGetAt (List.range 0 ++ baseState.openWires) index))
          index (List.range baseState.openWires.length) + 2
    rw [readShift index indexBelow, rangeSplitTwoRt baseState.openWires.length,
      findPartnerScan_cons, findPartnerScan_cons, readZero, readOne, padRootZero,
      zeroBeqRootFalse (natListGetAt baseState.openWires index)]
    exact scanShiftRt baseState.links padState.links baseState.openWires padState.openWires
      readShift componentShift index (List.range baseState.openWires.length)
      (fun candidate member => ltOfMemRangeRt candidate baseState.openWires.length member)
  have partnerListShape : (List.range (baseState.openWires.length + 2)).map
        (partnerIndexOf padState.links (List.range 1 ++ padState.openWires)
          (baseState.openWires.length + 2))
      = 1 :: 0 :: ((List.range baseState.openWires.length).map
          (partnerIndexOf baseState.links (List.range 0 ++ baseState.openWires)
            baseState.openWires.length)).map (fun value => value + 2) := by
    rw [rangeSplitTwoRt baseState.openWires.length]
    show partnerIndexOf padState.links (List.range 1 ++ padState.openWires)
          (baseState.openWires.length + 2) 0
        :: partnerIndexOf padState.links (List.range 1 ++ padState.openWires)
          (baseState.openWires.length + 2) 1
        :: ((List.range baseState.openWires.length).map (fun value => (value + 1) + 1)).map
          (partnerIndexOf padState.links (List.range 1 ++ padState.openWires)
            (baseState.openWires.length + 2))
      = _
    rw [partnerZero, partnerOne, mapMapRt, mapMapRt]
    refine congrArg (1 :: ·) (congrArg (0 :: ·) ?_)
    refine mapCongrOfMemRt _ _ (List.range baseState.openWires.length) ?_
    intro index member
    exact partnerShift index (ltOfMemRangeRt index baseState.openWires.length member)
  show ({ bottomCount := 1, topCount := padState.openWires.length,
          partner := (List.range (1 + padState.openWires.length)).map
            (partnerIndexOf padState.links (List.range 1 ++ padState.openWires)
              (1 + padState.openWires.length)),
          loops := padState.loops } : DiagramType)
      = { bottomCount := 0 + 1, topCount := baseState.openWires.length + 1,
          partner := 1 :: 0 :: ((List.range (0 + baseState.openWires.length)).map
            (partnerIndexOf baseState.links (List.range 0 ++ baseState.openWires)
              (0 + baseState.openWires.length))).map (fun value => value + 2),
          loops := baseState.loops }
  rw [totalShape, Nat.zero_add baseState.openWires.length, partnerListShape, topCountShape,
    sim.loopsEq]

/-! ## §8 The circle-position glue — a cup-cap circle pair lands on the SAME state fired at `1` or `0` -/

/-- Fold splitting for the Brauer word processor. -/
private theorem processBrauerAppendRt : (front rear : List BrauerAtom) → (state : WireState) →
    processBrauer state (front ++ rear) = processBrauer (processBrauer state front) rear
  | [], _, _ => rfl
  | atom :: rest, rear, state => processBrauerAppendRt rest rear (stepBrauerAtom state atom)

/-- Removing zero wires is the identity (per-constructor: the compiled matcher splits the list first). -/
private theorem removeManyZeroRt : (wires : List Nat) → (position : Nat) →
    natListRemoveManyAt wires position 0 = wires
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: _, _ + 1 => rfl

/-- Slicing zero wires is empty (per-constructor). -/
private theorem sliceZeroCountRt : (wires : List Nat) → (position : Nat) →
    natListSliceAt wires position 0 = []
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: _, _ + 1 => rfl

/-- Inserting at the front is prepending (per-constructor). -/
private theorem insertAtZeroRt : (wires block : List Nat) → natListInsertAt wires 0 block = block ++ wires
  | [], _ => rfl
  | _ :: _, _ => rfl

/-- Inserting past the head keeps the head. -/
private theorem insertAtConsSuccRt (head : Nat) (rest : List Nat) (position : Nat) (block : List Nat) :
    natListInsertAt (head :: rest) (position + 1) block = head :: natListInsertAt rest position block := rfl

/-- Slicing past the head skips it (count-split: the zero-count arm short-circuits). -/
private theorem sliceConsSuccPosRt (head : Nat) (rest : List Nat) (position : Nat) : (count : Nat) →
    natListSliceAt (head :: rest) (position + 1) count = natListSliceAt rest position count
  | 0 => Eq.trans (sliceZeroCountRt (head :: rest) (position + 1)) (sliceZeroCountRt rest position).symm
  | _ + 1 => rfl

/-- Slicing a head takes it. -/
private theorem sliceConsZeroSuccRt (head : Nat) (rest : List Nat) (count : Nat) :
    natListSliceAt (head :: rest) 0 (count + 1) = head :: natListSliceAt rest 0 count := rfl

/-- Removing past the head keeps the head (count-split). -/
private theorem removeManyConsSuccPosRt (head : Nat) (rest : List Nat) (position : Nat) : (count : Nat) →
    natListRemoveManyAt (head :: rest) (position + 1) count
      = head :: natListRemoveManyAt rest position count
  | 0 => by rw [removeManyZeroRt (head :: rest) (position + 1), removeManyZeroRt rest position]
  | _ + 1 => rfl

/-- Removing a head drops it. -/
private theorem removeManyConsZeroSuccRt (head : Nat) (rest : List Nat) (count : Nat) :
    natListRemoveManyAt (head :: rest) 0 (count + 1) = natListRemoveManyAt rest 0 count := rfl

/-- ★ **A circle pair fired at position `1` equals the pair fired at position `0`** over a non-empty wire list:
the cup opens the same fresh pair (left of or right of the head wire), the cap immediately consumes it, and the
union-find/loop bookkeeping never sees the difference. -/
private theorem circlePairShiftEqRt (state : WireState) (headWire : Nat) (restWires : List Nat)
    (wiresShape : state.openWires = headWire :: restWires) :
    stepBrauerAtom (stepBrauerAtom state (cupAt 1)) (capAt 1)
      = stepBrauerAtom (stepBrauerAtom state (cupAt 0)) (capAt 0) := by
  cases state with
  | mk stateWires stateLinks stateFresh stateLoops =>
      have wiresEq : stateWires = headWire :: restWires := wiresShape
      subst wiresEq
      have cupOneEq : stepBrauerAtom
          { openWires := headWire :: restWires, links := stateLinks, nextFresh := stateFresh,
            loops := stateLoops } (cupAt 1)
          = { openWires := headWire :: (0 + stateFresh) :: (1 + stateFresh) :: restWires,
              links := (stepWiringArcs [] [0 + stateFresh, 1 + stateFresh] 0 [(0, 1)] 0 stateLinks).fst,
              nextFresh := stateFresh + 2,
              loops := stateLoops
                + (stepWiringArcs [] [0 + stateFresh, 1 + stateFresh] 0 [(0, 1)] 0 stateLinks).snd
                + 0 } := by
        show ({ openWires := natListInsertAt (natListRemoveManyAt (headWire :: restWires) 1 0) 1
                  ((List.range 2).map (· + stateFresh)),
                links := (stepWiringArcs (natListSliceAt (headWire :: restWires) 1 0)
                  ((List.range 2).map (· + stateFresh)) 0 [(0, 1)] 0 stateLinks).fst,
                nextFresh := stateFresh + 2,
                loops := stateLoops + (stepWiringArcs (natListSliceAt (headWire :: restWires) 1 0)
                  ((List.range 2).map (· + stateFresh)) 0 [(0, 1)] 0 stateLinks).snd + 0 } : WireState)
            = _
        rw [removeManyZeroRt (headWire :: restWires) 1, sliceZeroCountRt (headWire :: restWires) 1,
          insertAtConsSuccRt headWire restWires 0 ((List.range 2).map (· + stateFresh)),
          insertAtZeroRt restWires ((List.range 2).map (· + stateFresh))]
        rfl
      have cupZeroEq : stepBrauerAtom
          { openWires := headWire :: restWires, links := stateLinks, nextFresh := stateFresh,
            loops := stateLoops } (cupAt 0)
          = { openWires := (0 + stateFresh) :: (1 + stateFresh) :: headWire :: restWires,
              links := (stepWiringArcs [] [0 + stateFresh, 1 + stateFresh] 0 [(0, 1)] 0 stateLinks).fst,
              nextFresh := stateFresh + 2,
              loops := stateLoops
                + (stepWiringArcs [] [0 + stateFresh, 1 + stateFresh] 0 [(0, 1)] 0 stateLinks).snd
                + 0 } := by
        show ({ openWires := natListInsertAt (natListRemoveManyAt (headWire :: restWires) 0 0) 0
                  ((List.range 2).map (· + stateFresh)),
                links := (stepWiringArcs (natListSliceAt (headWire :: restWires) 0 0)
                  ((List.range 2).map (· + stateFresh)) 0 [(0, 1)] 0 stateLinks).fst,
                nextFresh := stateFresh + 2,
                loops := stateLoops + (stepWiringArcs (natListSliceAt (headWire :: restWires) 0 0)
                  ((List.range 2).map (· + stateFresh)) 0 [(0, 1)] 0 stateLinks).snd + 0 } : WireState)
            = _
        rw [removeManyZeroRt (headWire :: restWires) 0, sliceZeroCountRt (headWire :: restWires) 0,
          insertAtZeroRt (headWire :: restWires) ((List.range 2).map (· + stateFresh))]
        rfl
      rw [cupOneEq, cupZeroEq]
      show ({ openWires := natListInsertAt
                (natListRemoveManyAt
                  (headWire :: (0 + stateFresh) :: (1 + stateFresh) :: restWires) 1 2) 1 [],
              links := (stepWiringArcs
                (natListSliceAt (headWire :: (0 + stateFresh) :: (1 + stateFresh) :: restWires) 1 2)
                [] 2 [(0, 1)] 0
                (stepWiringArcs [] [0 + stateFresh, 1 + stateFresh] 0 [(0, 1)] 0 stateLinks).fst).fst,
              nextFresh := stateFresh + 2 + 0,
              loops := stateLoops
                + (stepWiringArcs [] [0 + stateFresh, 1 + stateFresh] 0 [(0, 1)] 0 stateLinks).snd + 0
                + (stepWiringArcs
                  (natListSliceAt (headWire :: (0 + stateFresh) :: (1 + stateFresh) :: restWires) 1 2)
                  [] 2 [(0, 1)] 0
                  (stepWiringArcs [] [0 + stateFresh, 1 + stateFresh] 0 [(0, 1)] 0 stateLinks).fst).snd
                + 0 } : WireState)
          = { openWires := natListInsertAt
                (natListRemoveManyAt
                  ((0 + stateFresh) :: (1 + stateFresh) :: headWire :: restWires) 0 2) 0 [],
              links := (stepWiringArcs
                (natListSliceAt ((0 + stateFresh) :: (1 + stateFresh) :: headWire :: restWires) 0 2)
                [] 2 [(0, 1)] 0
                (stepWiringArcs [] [0 + stateFresh, 1 + stateFresh] 0 [(0, 1)] 0 stateLinks).fst).fst,
              nextFresh := stateFresh + 2 + 0,
              loops := stateLoops
                + (stepWiringArcs [] [0 + stateFresh, 1 + stateFresh] 0 [(0, 1)] 0 stateLinks).snd + 0
                + (stepWiringArcs
                  (natListSliceAt ((0 + stateFresh) :: (1 + stateFresh) :: headWire :: restWires) 0 2)
                  [] 2 [(0, 1)] 0
                  (stepWiringArcs [] [0 + stateFresh, 1 + stateFresh] 0 [(0, 1)] 0 stateLinks).fst).snd
                + 0 }
      rw [sliceConsSuccPosRt headWire ((0 + stateFresh) :: (1 + stateFresh) :: restWires) 0 2,
        sliceConsZeroSuccRt (0 + stateFresh) ((1 + stateFresh) :: restWires) 1,
        sliceConsZeroSuccRt (1 + stateFresh) restWires 0,
        sliceZeroCountRt restWires 0,
        sliceConsZeroSuccRt (0 + stateFresh) ((1 + stateFresh) :: headWire :: restWires) 1,
        sliceConsZeroSuccRt (1 + stateFresh) (headWire :: restWires) 0,
        sliceZeroCountRt (headWire :: restWires) 0,
        removeManyConsSuccPosRt headWire ((0 + stateFresh) :: (1 + stateFresh) :: restWires) 0 2,
        removeManyConsZeroSuccRt (0 + stateFresh) ((1 + stateFresh) :: restWires) 1,
        removeManyConsZeroSuccRt (1 + stateFresh) restWires 0,
        removeManyZeroRt restWires 0,
        removeManyConsZeroSuccRt (0 + stateFresh) ((1 + stateFresh) :: headWire :: restWires) 1,
        removeManyConsZeroSuccRt (1 + stateFresh) (headWire :: restWires) 0,
        removeManyZeroRt (headWire :: restWires) 0,
        insertAtConsSuccRt headWire restWires 0 [],
        insertAtZeroRt restWires [],
        insertAtZeroRt (headWire :: restWires) []]
      rfl

/-- The position-`0` circle pair restores the open wires exactly. -/
private theorem circlePairWiresRt (state : WireState) :
    (stepBrauerAtom (stepBrauerAtom state (cupAt 0)) (capAt 0)).openWires = state.openWires := by
  show natListInsertAt
      (natListRemoveManyAt
        (natListInsertAt (natListRemoveManyAt state.openWires 0 0) 0
          ((List.range 2).map (· + state.nextFresh))) 0 2) 0 []
    = state.openWires
  rw [removeManyZeroRt state.openWires 0,
    insertAtZeroRt state.openWires ((List.range 2).map (· + state.nextFresh))]
  show natListInsertAt
      (natListRemoveManyAt
        ((0 + state.nextFresh) :: (1 + state.nextFresh) :: state.openWires) 0 2) 0 []
    = state.openWires
  rw [removeManyConsZeroSuccRt (0 + state.nextFresh) ((1 + state.nextFresh) :: state.openWires) 1,
    removeManyConsZeroSuccRt (1 + state.nextFresh) state.openWires 0,
    removeManyZeroRt state.openWires 0, insertAtZeroRt state.openWires []]
  rfl

/-- ★ **The shifted circle word folds to the plain circle word** over any state with a non-empty wire list. -/
private theorem processCirclesShiftedRt : (loopCount : Nat) → (state : WireState) →
    (headWire : Nat) → (restWires : List Nat) → state.openWires = headWire :: restWires →
    processBrauer state (shiftBrauerWord 1 (circleWord loopCount))
      = processBrauer state (circleWord loopCount)
  | 0, _, _, _, _ => rfl
  | loopCount + 1, state, headWire, restWires, wiresShape => by
      show processBrauer (stepBrauerAtom (stepBrauerAtom state (cupAt 1)) (capAt 1))
            (shiftBrauerWord 1 (circleWord loopCount))
          = processBrauer (stepBrauerAtom (stepBrauerAtom state (cupAt 0)) (capAt 0))
            (circleWord loopCount)
      rw [circlePairShiftEqRt state headWire restWires wiresShape]
      exact processCirclesShiftedRt loopCount
        (stepBrauerAtom (stepBrauerAtom state (cupAt 0)) (capAt 0)) headWire restWires
        (Eq.trans (circlePairWiresRt state) wiresShape)

/-! ## §9 The fold bridge — the padded word and the shifted base word fold to the SAME state -/

/-- ★★ **The padded reconstruction's fold equals the shifted base word's fold** (both from `brauerSeed 1`): the
cup/crossing prefixes agree verbatim (§5), and the trailing circle blocks agree at the fold level (§8) because
the mid-state's wire list starts with the pad strand (the left-pad wire simulation over the prefix). -/
private theorem padVsShiftFoldRt (topCount : Nat) (partner : List Nat) (loops : Nat)
    (wf : IsBoundaryInvolution (0 + topCount) partner)
    (lengthEq : partner.length = topCount)
    (widthBound : topCount ≤ (cupArcTops 0 topCount partner).length + 1) :
    processBrauer (brauerSeed 1) (standardFormWordExt5 (reconstructStandardFormExt5Corrected
        (padThrough { bottomCount := 0, topCount := topCount, partner := partner, loops := loops })))
      = processBrauer (brauerSeed 1) (shiftBrauerWord 1 (standardFormWordExt5
          (reconstructStandardFormExt5Corrected
            { bottomCount := 0, topCount := topCount, partner := partner, loops := loops }))) := by
  rw [padWordCollapseRt topCount partner loops lengthEq widthBound,
    shiftedBaseWordRt topCount partner loops,
    processBrauerAppendRt
      (cupWord (natReplicate (cupArcTopIndices 0 topCount partner).length 1)
        ++ crossingWord ((permutationToCrossingWord topCount
            (permInverse (cupArcTops 0 topCount partner))).map (· + 1)))
      (circleWord loops) (brauerSeed 1),
    processBrauerAppendRt
      (cupWord (natReplicate (cupArcTopIndices 0 topCount partner).length 1)
        ++ crossingWord ((permutationToCrossingWord topCount
            (permInverse (cupArcTops 0 topCount partner))).map (· + 1)))
      (shiftBrauerWord 1 (circleWord loops)) (brauerSeed 1)]
  have seedWireSim : LeftPadWireSim 1 (brauerSeed 0) (brauerSeed 1) :=
    { openMap := rfl, nfShift := rfl }
  have prefixShiftShape : cupWord (natReplicate (cupArcTopIndices 0 topCount partner).length 1)
        ++ crossingWord ((permutationToCrossingWord topCount
            (permInverse (cupArcTops 0 topCount partner))).map (· + 1))
      = shiftBrauerWord 1
          (cupWord (natReplicate (cupArcTopIndices 0 topCount partner).length 0)
            ++ crossingWord (permutationToCrossingWord topCount
                (permInverse (throughStrandTops 0 topCount partner
                  ++ cupArcTops 0 topCount partner)))) := by
    rw [shiftBrauerWordAppendRt, cupWordReplicateShiftRt, crossingWordShiftRt,
      baseTopOrderRt topCount partner]
  have midWireSim : LeftPadWireSim 1
      (processBrauer (brauerSeed 0)
        (cupWord (natReplicate (cupArcTopIndices 0 topCount partner).length 0)
          ++ crossingWord (permutationToCrossingWord topCount
              (permInverse (throughStrandTops 0 topCount partner ++ cupArcTops 0 topCount partner)))))
      (processBrauer (brauerSeed 1)
        (shiftBrauerWord 1
          (cupWord (natReplicate (cupArcTopIndices 0 topCount partner).length 0)
            ++ crossingWord (permutationToCrossingWord topCount
                (permInverse (throughStrandTops 0 topCount partner
                  ++ cupArcTops 0 topCount partner)))))) :=
    processBrauer_leftPadWireSim 1 _ (brauerSeed 0) (brauerSeed 1) 0
      (basePrefixInRangeRt topCount partner wf) rfl seedWireSim
  have midWiresShape : (processBrauer (brauerSeed 1)
        (shiftBrauerWord 1
          (cupWord (natReplicate (cupArcTopIndices 0 topCount partner).length 0)
            ++ crossingWord (permutationToCrossingWord topCount
                (permInverse (throughStrandTops 0 topCount partner
                  ++ cupArcTops 0 topCount partner)))))).openWires
      = 0 :: (processBrauer (brauerSeed 0)
          (cupWord (natReplicate (cupArcTopIndices 0 topCount partner).length 0)
            ++ crossingWord (permutationToCrossingWord topCount
                (permInverse (throughStrandTops 0 topCount partner
                  ++ cupArcTops 0 topCount partner))))).openWires.map (freshShiftAbove 0 1) :=
    midWireSim.openMap
  rw [prefixShiftShape]
  exact (processCirclesShiftedRt loops _ 0 _ midWiresShape).symm

/-! ## §10 THE STRIP + the `bottomCount = 0` corner + the COMPLETE roundtrip -/

/-- ★★★ **THE STRIP IDENTITY** — realizing the padded reconstruction IS `padThrough` of realizing the base
reconstruction, for every well-formed `bottomCount = 0` diagram.  The fold bridge rewrites the padded fold to
the shifted base fold, and the one-sided left-pad extract transport reads it back as the pad of the base extract.
(The `#eval` census below pins the identity on wider inputs too — malformed included; the validity-independent
universal is an honest r56 residual.) -/
theorem ext5CorrectedRoundtrip_stripPad (d : DiagramType) (bottomZero : d.bottomCount = 0)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner) :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected (padThrough d))
      = padThrough (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d)) := by
  cases d with
  | mk bottomCount topCount partner loops =>
      have bottomEq : bottomCount = 0 := bottomZero
      subst bottomEq
      have wfPlain : IsBoundaryInvolution (0 + topCount) partner := wf
      have lengthEq : partner.length = topCount := by
        have boundaryLength := wfPlain.hasBoundaryLength
        rw [Nat.zero_add topCount] at boundaryLength
        exact boundaryLength
      have widthBound : topCount ≤ (cupArcTops 0 topCount partner).length + 1 := by
        rw [cupArcTopsLengthBaseRt topCount partner wfPlain]
        exact Nat.le_succ topCount
      show extractDiagram 1 (processBrauer (brauerSeed 1)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected
            (padThrough { bottomCount := 0, topCount := topCount, partner := partner, loops := loops }))))
        = padThrough (extractDiagram 0 (processBrauer (brauerSeed 0)
            (standardFormWordExt5 (reconstructStandardFormExt5Corrected
              { bottomCount := 0, topCount := topCount, partner := partner, loops := loops }))))
      rw [padVsShiftFoldRt topCount partner loops wfPlain lengthEq widthBound]
      exact extractDiagram_padThrough_ofLeftPadSim
        (processBrauer (brauerSeed 0) (standardFormWordExt5 (reconstructStandardFormExt5Corrected
          { bottomCount := 0, topCount := topCount, partner := partner, loops := loops })))
        (processBrauer (brauerSeed 1) (shiftBrauerWord 1 (standardFormWordExt5
          (reconstructStandardFormExt5Corrected
            { bottomCount := 0, topCount := topCount, partner := partner, loops := loops }))))
        (processBrauer_leftPadSim 1 0
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected
            { bottomCount := 0, topCount := topCount, partner := partner, loops := loops }))
          (baseWordInRangeRt topCount partner loops wfPlain))

/-- ★★★ **The `bottomCount = 0` corner of the R3-A roundtrip** — strip the pad off the FROZEN r54 bridge:
`padThrough` is injective, the padded diagram roundtrips (its bottom boundary is non-empty), and the strip
identity transports the roundtrip down to the closed diagram. -/
theorem ext5CorrectedRoundtrip_bottomZero (d : DiagramType) (bottomZero : d.bottomCount = 0)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner) :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d) = d :=
  padThrough_injective (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d)) d
    ((ext5CorrectedRoundtrip_stripPad d bottomZero wf).symm.trans
      (ext5CorrectedRoundtrip_padThrough d wf))

/-- ★★★ **THE COMPLETE R3-A ROUNDTRIP** — `standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d) = d`
for EVERY well-formed boundary involution, every `bottomCount` included: the FROZEN r54 bridge on `0 < bc`, the
route-D-pad corner on `bc = 0`.  The wall marker's verbatim demand, hypothesis-free except well-formedness. -/
theorem ext5CorrectedRoundtrip_complete (d : DiagramType)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner) :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d) = d := by
  cases hBottom : d.bottomCount with
  | zero => exact ext5CorrectedRoundtrip_bottomZero d hBottom wf
  | succ innerCount =>
      refine ext5CorrectedRoundtrip_ofPos d ?_ wf
      rw [hBottom]
      exact Nat.succ_pos innerCount

/-- ★★ **The complete roundtrip in the r53 valid-involution vocabulary** — every diagram whose partner passes the
r53 Bool census (with the boundary-length equation) roundtrips, `bottomCount = 0` included. -/
theorem ext5CorrectedRoundtrip_completeOfValidCensus (d : DiagramType)
    (lengthEq : d.partner.length = d.bottomCount + d.topCount)
    (census : isInvolutionPartner d.partner = true) :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d) = d :=
  ext5CorrectedRoundtrip_complete d
    (isBoundaryInvolution_ofValidCensus d.partner (d.bottomCount + d.topCount) lengthEq census)

/-! ## §11 The theorems FIRED on concrete closed diagrams — through the GENERAL path, not `decide` -/

/-- The empty closed diagram: no boundary, no loops. -/
def closedEmptyDiagram : DiagramType := { bottomCount := 0, topCount := 0, partner := [], loops := 0 }

/-- Three free circles: no boundary, three loops. -/
def closedLoopTripleDiagram : DiagramType := { bottomCount := 0, topCount := 0, partner := [], loops := 3 }

/-- A single cup with two trailing circles. -/
def closedCupWithLoopsDiagram : DiagramType :=
  { bottomCount := 0, topCount := 2, partner := [1, 0], loops := 2 }

/-- Two parallel (crossing-routed) cups `0 <-> 2`, `1 <-> 3`. -/
def closedParallelCupsDiagram : DiagramType :=
  { bottomCount := 0, topCount := 4, partner := [2, 3, 0, 1], loops := 0 }

/-- An outer cup over two nested inner arcs: `0 <-> 5`, `1 <-> 2`, `3 <-> 4`, plus two circles. -/
def closedOuterOverNestedLoopsDiagram : DiagramType :=
  { bottomCount := 0, topCount := 6, partner := [5, 2, 1, 4, 3, 0], loops := 2 }

/-- The width-8 fully-nested cup tower `[7,6,5,4,3,2,1,0]`. -/
def closedWidthEightNestedDiagram : DiagramType :=
  { bottomCount := 0, topCount := 8, partner := [7, 6, 5, 4, 3, 2, 1, 0], loops := 0 }

/-- MALFORMED: two fixed points (`partner[i] = i`) — not fixed-point-free. -/
def malformedFixedPointDiagram : DiagramType :=
  { bottomCount := 0, topCount := 2, partner := [0, 1], loops := 0 }

/-- MALFORMED: a three-cycle — not self-inverse. -/
def malformedThreeCycleDiagram : DiagramType :=
  { bottomCount := 0, topCount := 3, partner := [1, 2, 0], loops := 0 }

/-- MALFORMED: an out-of-range partner entry. -/
def malformedOutOfRangeDiagram : DiagramType :=
  { bottomCount := 0, topCount := 2, partner := [5, 0], loops := 0 }

/-- MALFORMED: a valid involution word that is too SHORT for its declared boundary. -/
def malformedLengthMismatchDiagram : DiagramType :=
  { bottomCount := 0, topCount := 4, partner := [1, 0], loops := 0 }

/-- ★★ **The r54 residual witness CLOSED through the general path** — `nestedCupsDiagram` (the exact
`bottomCount = 0` diagram the r54 bridge could only reach by `decide`) roundtrips through
`ext5CorrectedRoundtrip_completeOfValidCensus`. -/
theorem ext5CorrectedRoundtrip_general_nestedCups :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected nestedCupsDiagram) = nestedCupsDiagram :=
  ext5CorrectedRoundtrip_completeOfValidCensus nestedCupsDiagram rfl (by decide)

/-- ★ The triple-nested cup tower through the general path. -/
theorem ext5CorrectedRoundtrip_general_tripleNested :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected tripleNestedCupsDiagram)
      = tripleNestedCupsDiagram :=
  ext5CorrectedRoundtrip_completeOfValidCensus tripleNestedCupsDiagram rfl (by decide)

/-- ★ The EMPTY diagram through the general path (the degenerate corner of the corner). -/
theorem ext5CorrectedRoundtrip_general_closedEmpty :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected closedEmptyDiagram)
      = closedEmptyDiagram :=
  ext5CorrectedRoundtrip_completeOfValidCensus closedEmptyDiagram rfl (by decide)

/-- ★ The pure-loop diagram through the general path (no boundary at all, three circles). -/
theorem ext5CorrectedRoundtrip_general_loopTriple :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected closedLoopTripleDiagram)
      = closedLoopTripleDiagram :=
  ext5CorrectedRoundtrip_completeOfValidCensus closedLoopTripleDiagram rfl (by decide)

/-- ★ A cup with trailing circles through the general path (the loops>0 strip trap, closed). -/
theorem ext5CorrectedRoundtrip_general_cupWithLoops :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected closedCupWithLoopsDiagram)
      = closedCupWithLoopsDiagram :=
  ext5CorrectedRoundtrip_completeOfValidCensus closedCupWithLoopsDiagram rfl (by decide)

/-- ★ The width-8 nested tower + the mixed loop diagram through the general path. -/
theorem ext5CorrectedRoundtrip_general_widthEight :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected closedWidthEightNestedDiagram)
      = closedWidthEightNestedDiagram :=
  ext5CorrectedRoundtrip_completeOfValidCensus closedWidthEightNestedDiagram rfl (by decide)

/-- ★ The outer-over-nested diagram with loops through the general path. -/
theorem ext5CorrectedRoundtrip_general_outerOverNestedLoops :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected closedOuterOverNestedLoopsDiagram)
      = closedOuterOverNestedLoopsDiagram :=
  ext5CorrectedRoundtrip_completeOfValidCensus closedOuterOverNestedLoopsDiagram rfl (by decide)

/-- ★★ **The `0 < bottomCount` class still fires through the SAME complete theorem** — the width-12 entangled
monster (two caps + two throughs + two cups + one loop) through `ext5CorrectedRoundtrip_complete`: the assembly is
genuinely all-`bottomCount`, not a `bc = 0` special case. -/
theorem ext5CorrectedRoundtrip_general_monster :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected monsterDiagram) = monsterDiagram :=
  ext5CorrectedRoundtrip_complete monsterDiagram monster_isBoundaryInvolution

/-- ★ **The strip identity FIRED** on the nested cups (via the general strip theorem, not `decide`). -/
theorem ext5CorrectedRoundtrip_stripPad_nestedCups :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected (padThrough nestedCupsDiagram))
      = padThrough (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected nestedCupsDiagram)) :=
  ext5CorrectedRoundtrip_stripPad nestedCupsDiagram rfl
    (isBoundaryInvolution_ofValidCensus nestedCupsDiagram.partner
      (nestedCupsDiagram.bottomCount + nestedCupsDiagram.topCount) rfl (by decide))

/-- ★ **Brick E FIRED** — the census converse on the monster's partner agrees with the decidable census. -/
theorem isInvolutionPartner_monster_viaConverse : isInvolutionPartner monsterDiagram.partner = true :=
  isInvolutionPartner_ofIsBoundaryInvolution monsterDiagram.partner
    (monsterDiagram.bottomCount + monsterDiagram.topCount) monster_isBoundaryInvolution

/-! ### Malformed NEGATIVE CONTROLS — the census rejects, and the roundtrip genuinely fails -/

/-- ★ **The census rejects all four malformed closed inputs** — fixed points, a three-cycle, an out-of-range
entry (Bool census), and the boundary-length mismatch (length equation). -/
theorem closedMalformedCensusRejects :
    isInvolutionPartner malformedFixedPointDiagram.partner = false
      ∧ isInvolutionPartner malformedThreeCycleDiagram.partner = false
      ∧ isInvolutionPartner malformedOutOfRangeDiagram.partner = false
      ∧ Nat.beq malformedLengthMismatchDiagram.partner.length
          (malformedLengthMismatchDiagram.bottomCount + malformedLengthMismatchDiagram.topCount) = false :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- ★ **The malformed inputs genuinely fail the roundtrip** — the complete theorem's well-formedness hypothesis
is LOAD-BEARING, not decorative: on each malformed diagram the realized reconstruction differs from the input. -/
theorem closedMalformedRoundtripFails :
    diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected malformedFixedPointDiagram))
        malformedFixedPointDiagram = false
      ∧ diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected malformedThreeCycleDiagram))
        malformedThreeCycleDiagram = false
      ∧ diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected malformedOutOfRangeDiagram))
        malformedOutOfRangeDiagram = false
      ∧ diagramBeq (standardFormDiagramExt5
          (reconstructStandardFormExt5Corrected malformedLengthMismatchDiagram))
        malformedLengthMismatchDiagram = false :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ### The committed `#eval` census — the recon's 20-valid / 4-malformed table re-pinned

Every `bottomCount = 0` class representative roundtrips (`true`); every malformed input is rejected (`false`).
Run BEFORE the universals above were stated; committed per the census law. -/

-- the valid closed classes (expect `true` on every line)
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected closedEmptyDiagram)) closedEmptyDiagram                              -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected closedLoopTripleDiagram)) closedLoopTripleDiagram                    -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected { bottomCount := 0, topCount := 0, partner := [], loops := 5 })) { bottomCount := 0, topCount := 0, partner := [], loops := 5 }  -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected { bottomCount := 0, topCount := 2, partner := [1, 0], loops := 0 })) { bottomCount := 0, topCount := 2, partner := [1, 0], loops := 0 }  -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected closedCupWithLoopsDiagram)) closedCupWithLoopsDiagram                -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected { bottomCount := 0, topCount := 4, partner := [1, 0, 3, 2], loops := 0 })) { bottomCount := 0, topCount := 4, partner := [1, 0, 3, 2], loops := 0 }  -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected nestedCupsDiagram)) nestedCupsDiagram                                -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected closedParallelCupsDiagram)) closedParallelCupsDiagram                -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected { bottomCount := 0, topCount := 6, partner := [1, 0, 3, 2, 5, 4], loops := 0 })) { bottomCount := 0, topCount := 6, partner := [1, 0, 3, 2, 5, 4], loops := 0 }  -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected tripleNestedCupsDiagram)) tripleNestedCupsDiagram                    -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected { bottomCount := 0, topCount := 6, partner := [3, 2, 1, 0, 5, 4], loops := 0 })) { bottomCount := 0, topCount := 6, partner := [3, 2, 1, 0, 5, 4], loops := 0 }  -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected { bottomCount := 0, topCount := 6, partner := [5, 2, 1, 4, 3, 0], loops := 0 })) { bottomCount := 0, topCount := 6, partner := [5, 2, 1, 4, 3, 0], loops := 0 }  -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected { bottomCount := 0, topCount := 6, partner := [2, 3, 0, 1, 5, 4], loops := 0 })) { bottomCount := 0, topCount := 6, partner := [2, 3, 0, 1, 5, 4], loops := 0 }  -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected { bottomCount := 0, topCount := 4, partner := [3, 2, 1, 0], loops := 3 })) { bottomCount := 0, topCount := 4, partner := [3, 2, 1, 0], loops := 3 }  -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected closedOuterOverNestedLoopsDiagram)) closedOuterOverNestedLoopsDiagram -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected closedWidthEightNestedDiagram)) closedWidthEightNestedDiagram        -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected { bottomCount := 0, topCount := 8, partner := [1, 0, 3, 2, 5, 4, 7, 6], loops := 1 })) { bottomCount := 0, topCount := 8, partner := [1, 0, 3, 2, 5, 4, 7, 6], loops := 1 }  -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected { bottomCount := 0, topCount := 8, partner := [5, 2, 1, 4, 3, 0, 7, 6], loops := 2 })) { bottomCount := 0, topCount := 8, partner := [5, 2, 1, 4, 3, 0, 7, 6], loops := 2 }  -- true
-- the strip identity on valid AND malformed inputs (expect `true` — validity-independent empirically)
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected (padThrough nestedCupsDiagram))) (padThrough (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected nestedCupsDiagram)))  -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected (padThrough malformedFixedPointDiagram))) (padThrough (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected malformedFixedPointDiagram)))  -- true (strip beyond the proven scope)
-- the malformed inputs (expect `false` on every line)
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected malformedFixedPointDiagram)) malformedFixedPointDiagram              -- false
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected malformedThreeCycleDiagram)) malformedThreeCycleDiagram              -- false
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected malformedOutOfRangeDiagram)) malformedOutOfRangeDiagram              -- false
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected malformedLengthMismatchDiagram)) malformedLengthMismatchDiagram      -- false

/-! ## §12 Content markers + the honest terminal state + the r56 bill -/

/-- ★★★ **Honesty marker — THE COMPLETE R3-A ROUNDTRIP IS PROVEN (r55; the wall marker's demand DELIVERED).**
`ext5CorrectedRoundtrip_complete` proves `standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d) = d`
for EVERY well-formed boundary involution `d` — every `bottomCount`, the closed `bottomCount = 0` class INCLUDED
— hypothesis-free except well-formedness, zero-axiom, by cases on `d.bottomCount`: the FROZEN r54 bridge
(`ext5CorrectedRoundtrip_ofPos`, the r21-r31 `stepWiring`-connectivity induction) on `0 < bc`, and the r55 route
D-pad corner (`ext5CorrectedRoundtrip_bottomZero`: the strip identity `ext5CorrectedRoundtrip_stripPad` + the
padded roundtrip + `padThrough` injectivity) on `bc = 0`.

**The honest supersession**: this marker SUPERSEDES the R3-A wall marker
`fxBrauer_hasExt5CorrectedRoundtripProof` (`Brauer/WiringDescArcExtractorRec.lean:217`).  That marker's `false` is
pinned by `rfl`-conjunctions in eight-plus FROZEN ledgers (`WiringDescStandardFoldR5Ledger:98`,
`WiringDescArcEnumeration:475/511`, `WiringDescReadOffWiring:119`, `WiringDescCorrectedFold:113`,
`WiringDescArcReadOffPermutation:718`, `WiringDescArcReadOffCount:2013/2059`, the r54 terminal state), so editing
it would break every one of those frozen kernel-checked theorems; per the r31/r54 additive precedent it stays
byte-intact as a LEDGER-PRESERVATION ARTIFACT, and its `false` no longer states a truth OR route gap — THIS
marker carries the truth: the roundtrip is a THEOREM (`ext5CorrectedRoundtrip_complete`), fired on the closed
classes through the general path and negatively controlled on four malformed inputs.  `= true`. -/
def fxBrauer_hasExt5CorrectedRoundtripComplete : Bool := true

/-- ★★ **The r55 closed-diagram roundtrip-close terminal state — MACHINE-CHECKED.**  The COMPLETE-roundtrip
marker is `true` (this round's delivery) on top of the r54 `0 < bc` tranche marker; the superseded wall marker
stays byte-intact `false` (the ledger-preservation artifact); and the CONV-side dispatch/completeness masters ALL
STAY `false` — the roundtrip is fold-read-back (T-CLOSE), orthogonal to the `BrauerConv` drive (the R3-B inner
descent and the whisker-free driver remain the open poles).  Same-commit `rfl`-conjunction; purely additive. -/
theorem fxBrauer_closedDiagramRoundtripCloseTerminalState :
    fxBrauer_hasExt5CorrectedRoundtripComplete = true
      ∧ fxBrauer_hasExt5CorrectedRoundtripPosBottom = true
      ∧ fxBrauer_hasExt5CorrectedRoundtripProof = false
      ∧ fxBrauer_hasValidInvolutionFoldDischarged = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The r56 bill (the post-R3-A completeness road, named honestly)

  * **R3-B — the staged inner descent** (`fxBrauer_hasStagedInnerDescentDischarged`): the complete roundtrip
    removes the `0 < bc` side-condition from the descent's BASE (reconstruction is now a total section on valid
    involutions, `ext5CorrectedRoundtrip_complete`), but the interleaved-arc `i < k < j < l` jam in the descent
    STEP is untouched — the standing R3-B pole.
  * **The whisker-free driver / the genuine-conv bridge**: both live on the CONV direction (deriving the
    `whisker` congruence from the seven Lehrer-Zhang relations); the roundtrip is fold-read-back and unlocks
    nothing there directly — it only lets the completeness masters cite a genuinely-total section.
  * **The strip beyond well-formedness**: `ext5CorrectedRoundtrip_stripPad` is proven for well-formed
    `bottomCount = 0` diagrams — the generality the complete theorem needs.  The `#eval` census pins the identity
    on malformed inputs too (validity-independent empirically); the unconditional universal (and its `padCap` /
    arbitrary-left-tensor generalization, the monoidal-functoriality lane) is named r56 work.
  * **Brick E's iff feeding the r53 exact-cut census** a Prop-level statement
    (`isBoundaryInvolution_iff_validCensus` composed with `countRepresentativeRealizeXorValid = 0`). -/

end FX1Poly.Polygraph
