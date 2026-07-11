import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescPartnerSharesDispatch
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute

/-! # BRAUER r29 — T-CLOSE(b): `extractDiagram d.bottomCount F = d`, three fields + the honest loops wall

T-CLOSE(b) is `foldRealizesTargetDiagramCorrected d` (`WiringDescFoldTargetHonest`) — for a well-formed boundary
involution, the corrected six-phase fold reads back to `d`.  `extractDiagram d.bottomCount F` is a four-field record:

  * `bottomCount = d.bottomCount` — the argument, `rfl`.
  * `topCount = F.openWires.length` — `foldOpenWiresWidth_correctedWord` gives `= d.topCount` (B2).
  * `partner = (range total).map (partnerIndexOf F.links boundaryNodes total)` — pointwise
    `partnerIndexOf_reads_arc_unconditional` (B2, the six-arm dispatch) + list-extensionality by `getAt` reads it back
    to `d.partner`.  SHIPPED here.
  * `loops = F.loops` — needs `F.loops = d.loops`.  **THE RISK named by the recon**: no shipped circle-loop
    accounting, and the boundary-word-adds-0-loops leg needs a fresh connectivity invariant (no cap in the corrected
    fold ever closes a loop).  WALLED.

This file ships the three certain fields as `extractDiagram_correctedWord_ofLoopsField` (the full close, GATED on the
sole residual `F.loops = d.loops`) and names the loops residual exactly via the wall marker
`fxBrauer_hasFoldLoopsCorrectness = false`.  It does NOT flip `foldRealizesTargetDiagramCorrected`'s general proof or
any completeness master — #2013 stays one honest field open.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `native_decide`.  `propext`-safe list plumbing (hand-rolled
`listExtByGetAt`, never `List.ext` / `List.map_getElem`).  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Section 0 — the propext-free list-extensionality kit (hand-rolled) -/

/-- `(xs.map f).length = xs.length`. -/
private theorem mapLengthFold (mapFn : Nat → Nat) : (entries : List Nat) →
    (entries.map mapFn).length = entries.length
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (mapLengthFold mapFn rest)

/-- Membership in `acc` survives the range-loop fold, at the length level. -/
private theorem rangeLoopLengthFold : (count : Nat) → (acc : List Nat) →
    (List.range.loop count acc).length = count + acc.length
  | 0, acc => (Nat.zero_add acc.length).symm
  | count + 1, acc => by
      show (List.range.loop count (count :: acc)).length = (count + 1) + acc.length
      rw [rangeLoopLengthFold count (count :: acc)]
      show count + (acc.length + 1) = (count + 1) + acc.length
      rw [Nat.add_succ, Nat.succ_add]

/-- `(List.range count).length = count`. -/
private theorem rangeLengthFold (count : Nat) : (List.range count).length = count :=
  (rangeLoopLengthFold count []).trans (Nat.add_zero count)

/-- `natListGetAt (List.range.loop count acc) (offset + count) = natListGetAt acc offset`. -/
private theorem getAtRangeLoopPastFold : (count : Nat) → (acc : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count acc) (offset + count) = natListGetAt acc offset
  | 0, _, _ => rfl
  | count + 1, acc, offset => by
      have inner := getAtRangeLoopPastFold count (count :: acc) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

/-- `natListGetAt (List.range.loop count acc) index = index` for `index < count`. -/
private theorem getAtRangeLoopFold : (count : Nat) → (acc : List Nat) → (index : Nat) → index < count →
    natListGetAt (List.range.loop count acc) index = index
  | 0, _, index, h => absurd h (Nat.not_lt_zero index)
  | count + 1, acc, index, h => by
      cases Nat.lt_or_ge index count with
      | inl below => exact getAtRangeLoopFold count (count :: acc) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_lt_succ h) atLeast
          have pastRead : natListGetAt (List.range.loop count (count :: acc)) (0 + count)
              = natListGetAt (count :: acc) 0 := getAtRangeLoopPastFold count (count :: acc) 0
          rw [Nat.zero_add] at pastRead
          rw [indexEq]; exact pastRead

/-- `natListGetAt (List.range count) index = index` for `index < count`. -/
private theorem getAtRangeFold (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  getAtRangeLoopFold count [] index indexBelow

/-- `natListGetAt (xs.map f) index = f (natListGetAt xs index)` for `index < xs.length`. -/
private theorem getAtMapFold (mapFn : Nat → Nat) : (entries : List Nat) → (index : Nat) →
    index < entries.length → natListGetAt (entries.map mapFn) index = mapFn (natListGetAt entries index)
  | [], index, h => absurd h (Nat.not_lt_zero index)
  | head :: _, 0, _ => rfl
  | _ :: rest, index + 1, h => getAtMapFold mapFn rest index (Nat.lt_of_succ_lt_succ h)

/-- Two `Nat` lists agreeing in length and pointwise (by `natListGetAt`) are equal — `propext`-free. -/
private theorem listExtByGetAtFold : (entriesLeft entriesRight : List Nat) →
    entriesLeft.length = entriesRight.length →
    (∀ index, index < entriesLeft.length → natListGetAt entriesLeft index = natListGetAt entriesRight index) →
    entriesLeft = entriesRight
  | [], [], _, _ => rfl
  | [], _ :: _, lengthsEq, _ => Nat.noConfusion lengthsEq
  | _ :: _, [], lengthsEq, _ => Nat.noConfusion lengthsEq
  | headLeft :: tailLeft, headRight :: tailRight, lengthsEq, getAtEq => by
      have headEq : headLeft = headRight := getAtEq 0 (Nat.succ_pos _)
      have tailEq : tailLeft = tailRight :=
        listExtByGetAtFold tailLeft tailRight (Nat.succ.inj lengthsEq)
          (fun index indexBelow => getAtEq (index + 1) (Nat.succ_lt_succ indexBelow))
      rw [headEq, tailEq]

/-! ## Section 1 — the partner field (the whole B2 dispatch, list-assembled) -/

/-- ★★★ **The T-CLOSE(b) `partner` field.**  For a well-formed boundary involution, the extractor's partner map
reads back to `d.partner` — the full B2 six-arm dispatch (`partnerIndexOf_reads_arc_unconditional`) pointwise, then
list-extensionality by `getAt`.  The width `foldOpenWiresWidth_correctedWord` aligns the range length with
`d.partner.length` (`wf.hasBoundaryLength`). -/
theorem extractDiagram_partner_correctedWord (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner) :
    (List.range (d.bottomCount + (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).openWires.length)).map
        (partnerIndexOf
          (processBrauer (brauerSeed d.bottomCount)
            (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).links
          (List.range d.bottomCount ++ (processBrauer (brauerSeed d.bottomCount)
            (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).openWires)
          (d.bottomCount + (processBrauer (brauerSeed d.bottomCount)
            (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).openWires.length))
      = d.partner := by
  have hwidth := foldOpenWiresWidth_correctedWord d wf
  have htotalEq : d.bottomCount
      + (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).openWires.length
      = d.partner.length := by rw [hwidth, wf.hasBoundaryLength]
  apply listExtByGetAtFold
  · rw [mapLengthFold, rangeLengthFold, htotalEq]
  · intro index indexBelow
    rw [mapLengthFold, rangeLengthFold] at indexBelow
    rw [getAtMapFold _ (List.range _) index (by rw [rangeLengthFold]; exact indexBelow),
      getAtRangeFold _ index indexBelow]
    exact partnerIndexOf_reads_arc_unconditional d bottomPos wf index indexBelow

/-! ## Section 2 — the four-field close, GATED on the loops field -/

/-- ★★★ **T-CLOSE(b), reduced to the SOLE residual `F.loops = d.loops`.**  Given the loops field, the corrected
six-phase fold reads back to `d` exactly: the `bottomCount` field is `rfl`, the `topCount` field is
`foldOpenWiresWidth_correctedWord` (B2), the `partner` field is `extractDiagram_partner_correctedWord` (the whole B2
dispatch), and the `loops` field is the hypothesis.  So `foldRealizesTargetDiagramCorrected` is now ONE field open —
`F.loops = d.loops` — the named risk. -/
theorem extractDiagram_correctedWord_ofLoopsField (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner)
    (loopsField : (processBrauer (brauerSeed d.bottomCount)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).loops = d.loops) :
    extractDiagram d.bottomCount
        (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d)))
      = d := by
  apply diagramType_eq_of_fields
  · rfl
  · exact foldOpenWiresWidth_correctedWord d wf
  · exact extractDiagram_partner_correctedWord d bottomPos wf
  · exact loopsField

/-- ★★ **T-CLOSE(b) closes for every diagram whose corrected fold has the RIGHT loop count.**  Restated as an
implication into `foldRealizesTargetDiagramCorrected`: the loops field is the only premise beyond well-formedness. -/
theorem foldRealizesTargetDiagramCorrected_ofLoopsField (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (loopsField : (processBrauer (brauerSeed d.bottomCount)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).loops = d.loops) :
    foldRealizesTargetDiagramCorrected d :=
  fun wf => extractDiagram_correctedWord_ofLoopsField d bottomPos wf loopsField

/-! ## Section 3 — the loops field on the recon self-attacks (eval FIRST, decidable) -/

/-- ★ **The loops field HOLDS on the all-loop diagram `{0, 0, [], 3}` (decidable).**  With partner empty and the
boundary word vacuous, the three circle blocks add exactly `3` loops — the sharpest isolated test of the loops field.
`extractDiagram 0 F = {0, 0, [], 3}` `by decide`. -/
theorem foldLoopsField_allLoop :
    (processBrauer (brauerSeed 0)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected
          { bottomCount := 0, topCount := 0, partner := [], loops := 3 }))).loops = 3 := by decide

/-- ★ **The loops field HOLDS on adversarial-B (`loops := 1`, a genuine cap+through+cup+loop diagram).** -/
theorem foldLoopsField_adversarialB :
    (processBrauer (brauerSeed 3)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))).loops
      = adversarialBDiagram.loops := by decide

/-- ★ **The loops field HOLDS on the loop-free monster (`loops := 0`).** -/
theorem foldLoopsField_monster :
    (processBrauer (brauerSeed 6)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram))).loops
      = monsterDiagram.loops := by decide

/-- ★★ **T-CLOSE(b) FULLY CLOSES on adversarial-B via the gated form** — the loops field decided, the three certain
fields general.  The corrected fold reads back to `adversarialBDiagram` exactly, through the B2 dispatch (no
per-slot `decide` on the partner). -/
theorem foldRealizesTargetDiagramCorrected_adversarialB_viaGated :
    foldRealizesTargetDiagramCorrected adversarialBDiagram :=
  foldRealizesTargetDiagramCorrected_ofLoopsField adversarialBDiagram (by decide) foldLoopsField_adversarialB

/-! ## Section 4 — the honesty wall marker (the loops field is the sole residual) -/

/-- **Honesty WALL marker — the loops field `F.loops = d.loops` stays UNBUILT in general (the r29 named risk).**
T-CLOSE(b) `extractDiagram d.bottomCount F = d` closes three of four fields UNCONDITIONALLY: `bottomCount` (`rfl`),
`topCount` (`foldOpenWiresWidth_correctedWord`), and `partner` (`extractDiagram_partner_correctedWord`, the whole B2
six-arm dispatch).  The FOURTH field, `F.loops = d.loops`, has no shipped scaffold: it decomposes into a circle-loop
accounting `(processBrauer state (circleWord n)).loops = state.loops + n` (a clean structural induction, unbuilt) and
the boundary-word-adds-0-loops leg (`(processBrauer (brauerSeed bc) boundaryWord).loops = 0`, which needs a FRESH
connectivity invariant — no cap in the corrected fold ever fires on a pre-connected pair, hence never closes a loop).
`extractDiagram_correctedWord_ofLoopsField` reduces the ENTIRE `foldRealizesTargetDiagramCorrected` to exactly this
field; it holds decidably on every shipped witness (`foldLoopsField_allLoop` / `…_adversarialB` / `…_monster`), but
NOT in general.  So this marker is `false`, `foldRealizesTargetDiagramCorrected`'s general proof stays one field open,
NO completeness master flips, and #2013 does NOT close.  `= false`. -/
def fxBrauer_hasFoldLoopsCorrectness : Bool := false

end FX1Poly.Polygraph
