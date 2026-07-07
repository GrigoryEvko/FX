import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupTopTopFloorShift
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupStepDrop

/-! # ValleyCupTopTopStepTransport — the two-floor per-step lemma of the top-top offset fold (Piece II tail)

The residual `cupTopTopPartner` (`ValleyCupReconstruct`, cup case 3) is closed by a peel-last induction that runs the
SAME cup block through the per-cup partner transport `diagramPartner_stepCupArc` (`ArcCupStepDrop`) at TWO floors —
`bottomCount` (the whole valley) and `midWidth` (the cup alone) — carrying a top-region OFFSET-SPACE agreement.  The
arithmetic core (the floor factoring OUT of a single fresh-shift) is `ValleyCupTopTopFloorShift`.  This file lands the
PER-STEP engine of that induction: the two-floor per-step lemma.

## The offset-space top-region agreement, and its per-step preservation

`topRegionOffsetAgrees floorHi floorLo partnerHi partnerLo topLen` says the two partner lists agree, over the
`topLen` top-region ports, in OFFSET space: at every top offset `off`,

  * the at-or-above-floor TAG agrees (`floorHi ≤ readHi off ↔ floorLo ≤ readLo off`), and
  * WHEN the port is top-top (tag true), the offsets agree (`readHi off − floorHi = readLo off − floorLo`).

A single top-of-stack cup step transports each partner list by `diagramPartner_stepCupArc`:

  `partner ↦ natListInsertAt (partner.map (freshShiftAbove (floor + w) 2)) (floor + w) [floor + w + 1, floor + w]`.

`topRegionOffsetAgrees_step` proves this transport PRESERVES the agreement (with `topLen ↦ topLen + 2`), at a SHARED
window `w`.  Four zones per stepped read:

  * old ports below the window (`off < w`) and past it (`off > w + 1`) — the base read shifted by
    `freshShiftAbove (floor + w) 2`; the floor factors out in offset space by
    `freshShiftAbove_floorEquivariant_offset`, and the at-or-above-floor tag is EXACTLY preserved by the shift, so the
    base agreement carries through (`shiftedOffsetAgrees`);
  * the two fresh legs (`off = w`, `off = w + 1`) — partners `floor + w + 1` and `floor + w`, offsets `w + 1` and
    `w`, FLOOR-FREE, so the new top-top arc satisfies the agreement automatically on both runs.

## What this file lands (zero-axiom) — and the residual it does NOT discharge

  * ★ `topRegionOffsetAgrees` — the two-floor top-region offset-space agreement relation.
  * ★ `shiftedOffsetAgrees` — one shifted old-port read preserves tag + offset agreement across the two floors.
  * ★ `topRegionOffsetAgrees_step` — the two-floor per-step lemma: one shared top-of-stack cup step preserves the
    agreement.

This is the per-step engine the peel-last induction folds.  What is NOT closed here — hence `cupTopTopPartner` stays
a hypothesis of `cupRestrict_reconstructs`, and `valleyAppend_split` / `valleysWithEqualMatching_spineTraceEquiv` stay
gated: the induction itself (peel-last over the cup block at both floors, threading this per-step lemma), the
base-case seed reconciliation (the two seeds `range midWidth` vs `capState` differ only OFF the top-top ports), and
the WireState ↔ arc-encoding bridge assembly (`matchingOfSpineList` ↔ `extractArc ∘ processArcSpine`, via the shipped
`arcDiagram_eq_matching`).  No gate flag is flipped; fib-3 also carries the independent Piece-I beam
(`MatchingReductsShareSpineTrace`, #1996).

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local `Nat` / `List` plumbing (propext-free copies) -/

/-- `base + value - base = value` (hand-rolled; `Nat.add_sub_cancel_left` risks a `propext` leak). -/
private theorem addSubCancelLeftLocal : (base value : Nat) → base + value - base = value
  | 0, value => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, value => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact addSubCancelLeftLocal base value

/-- `values.map fn` has the same length as `values` (structural; core lemma risks display quirks). -/
private theorem listMapLenLocal {carrier : Type} (mapFn : Nat → carrier) :
    (values : List Nat) → (values.map mapFn).length = values.length
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (listMapLenLocal mapFn rest)

/-- `leftSide + cancelled < rightSide + cancelled → leftSide < rightSide` (hand-rolled). -/
private theorem natLtOfAddLtAddRight : (cancelled : Nat) → {leftSide rightSide : Nat} →
    leftSide + cancelled < rightSide + cancelled → leftSide < rightSide
  | 0, _, _, sumsLt => sumsLt
  | cancelled + 1, _, _, sumsLt => natLtOfAddLtAddRight cancelled (Nat.lt_of_succ_lt_succ sumsLt)

/-! ## The at-or-above-floor tag is preserved by the fresh-shift -/

/-- A value never exceeds its fresh-shift (`freshShiftAbove` adds `delta` or nothing). -/
private theorem selfLeFreshShiftAbove (threshold delta value : Nat) :
    value ≤ freshShiftAbove threshold delta value := by
  rcases Nat.lt_or_ge value threshold with valueBelow | valueAtOrAbove
  · rw [freshShiftAbove_ofNotLe threshold delta value (Nat.not_le_of_gt valueBelow)]
    exact Nat.le_refl value
  · rw [freshShiftAbove_ofLe threshold delta value valueAtOrAbove]
    exact Nat.le_add_right value delta

/-- If a value is at-or-above the floor, so is its fresh-shift. -/
private theorem floorLe_freshShiftAbove_of (floor threshold delta value : Nat)
    (floorLeValue : floor ≤ value) : floor ≤ freshShiftAbove threshold delta value :=
  Nat.le_trans floorLeValue (selfLeFreshShiftAbove threshold delta value)

/-- If a fresh-shift (at a floor-at-or-above threshold) is at-or-above the floor, so was the value. -/
private theorem floorLe_of_freshShiftAbove (floor threshold delta value : Nat)
    (floorLeThreshold : floor ≤ threshold)
    (floorLeShift : floor ≤ freshShiftAbove threshold delta value) : floor ≤ value := by
  rcases Nat.lt_or_ge value threshold with valueBelow | valueAtOrAbove
  · rw [freshShiftAbove_ofNotLe threshold delta value (Nat.not_le_of_gt valueBelow)] at floorLeShift
    exact floorLeShift
  · exact Nat.le_trans floorLeThreshold valueAtOrAbove

/-! ## One shifted old-port read preserves the two-floor agreement -/

/-- ★ **A shifted old-port read preserves tag + offset agreement across the two floors.**  Given a base read pair
(`baseHi` at floor `floorHi`, `baseLo` at floor `floorLo`) whose at-or-above-floor tags agree and whose offsets agree
when top-top, the two fresh-shifted reads `freshShiftAbove (floor + windowPos) 2 base` still agree in tag and (when
top-top) in offset — the floor factors out of the shift by `freshShiftAbove_floorEquivariant_offset`, and the tag is
exactly preserved by the shift. -/
theorem shiftedOffsetAgrees (floorHi floorLo windowPos baseHi baseLo : Nat)
    (tagAgrees : floorHi ≤ baseHi ↔ floorLo ≤ baseLo)
    (offsetAgrees : floorHi ≤ baseHi → baseHi - floorHi = baseLo - floorLo) :
    (floorHi ≤ freshShiftAbove (floorHi + windowPos) 2 baseHi
       ↔ floorLo ≤ freshShiftAbove (floorLo + windowPos) 2 baseLo)
    ∧ (floorHi ≤ freshShiftAbove (floorHi + windowPos) 2 baseHi →
        freshShiftAbove (floorHi + windowPos) 2 baseHi - floorHi
          = freshShiftAbove (floorLo + windowPos) 2 baseLo - floorLo) := by
  have floorHiLeThreshold : floorHi ≤ floorHi + windowPos := Nat.le_add_right floorHi windowPos
  have floorLoLeThreshold : floorLo ≤ floorLo + windowPos := Nat.le_add_right floorLo windowPos
  refine ⟨⟨fun shiftHi => ?_, fun shiftLo => ?_⟩, fun shiftHi => ?_⟩
  · exact floorLe_freshShiftAbove_of floorLo (floorLo + windowPos) 2 baseLo
      (tagAgrees.mp (floorLe_of_freshShiftAbove floorHi (floorHi + windowPos) 2 baseHi floorHiLeThreshold shiftHi))
  · exact floorLe_freshShiftAbove_of floorHi (floorHi + windowPos) 2 baseHi
      (tagAgrees.mpr (floorLe_of_freshShiftAbove floorLo (floorLo + windowPos) 2 baseLo floorLoLeThreshold shiftLo))
  · have baseHiAtOrAbove : floorHi ≤ baseHi :=
      floorLe_of_freshShiftAbove floorHi (floorHi + windowPos) 2 baseHi floorHiLeThreshold shiftHi
    rw [freshShiftAbove_floorEquivariant_offset floorHi windowPos 2 baseHi baseHiAtOrAbove,
      freshShiftAbove_floorEquivariant_offset floorLo windowPos 2 baseLo (tagAgrees.mp baseHiAtOrAbove),
      offsetAgrees baseHiAtOrAbove]

/-! ## The two-floor top-region offset-space agreement, and its per-step preservation -/

/-- The two-floor top-region offset-space agreement: over the `topLen` top-region ports, the at-or-above-floor tags
agree and (when top-top) the offsets agree.  `partnerHi`/`partnerLo` are the two runs' partner lists, read at the
top-region ports `floorHi + off` / `floorLo + off`. -/
def topRegionOffsetAgrees (floorHi floorLo : Nat) (partnerHi partnerLo : List Nat) (topLen : Nat) : Prop :=
  ∀ off : Nat, off < topLen →
    (floorHi ≤ natListGetAt partnerHi (floorHi + off) ↔ floorLo ≤ natListGetAt partnerLo (floorLo + off))
    ∧ (floorHi ≤ natListGetAt partnerHi (floorHi + off) →
        natListGetAt partnerHi (floorHi + off) - floorHi
          = natListGetAt partnerLo (floorLo + off) - floorLo)

/-- ★ **The two-floor per-step lemma.**  A single top-of-stack cup step at a SHARED window `windowPos` transports each
partner list by `natListInsertAt (partner.map (freshShiftAbove (floor + windowPos) 2)) (floor + windowPos)
[floor + windowPos + 1, floor + windowPos]` (the `diagramPartner_stepCupArc` shape) and PRESERVES the top-region
offset-space agreement, with `topLen ↦ topLen + 2`.  The partner lengths pin the top region
(`partner.length = floor + topLen`), the window fits (`windowPos ≤ topLen`), and the base agreement is given.  Old
ports below/past the window ride `shiftedOffsetAgrees`; the two fresh legs are floor-free. -/
theorem topRegionOffsetAgrees_step (floorHi floorLo windowPos topLen : Nat)
    (partnerHi partnerLo : List Nat)
    (lenHi : partnerHi.length = floorHi + topLen) (lenLo : partnerLo.length = floorLo + topLen)
    (windowFits : windowPos ≤ topLen)
    (base : topRegionOffsetAgrees floorHi floorLo partnerHi partnerLo topLen) :
    topRegionOffsetAgrees floorHi floorLo
      (natListInsertAt (partnerHi.map (freshShiftAbove (floorHi + windowPos) 2))
        (floorHi + windowPos) [floorHi + windowPos + 1, floorHi + windowPos])
      (natListInsertAt (partnerLo.map (freshShiftAbove (floorLo + windowPos) 2))
        (floorLo + windowPos) [floorLo + windowPos + 1, floorLo + windowPos])
      (topLen + 2) := by
  intro off offLt
  have posHiLe : floorHi + windowPos ≤ (partnerHi.map (freshShiftAbove (floorHi + windowPos) 2)).length := by
    rw [listMapLenLocal, lenHi]; exact Nat.add_le_add_left windowFits floorHi
  have posLoLe : floorLo + windowPos ≤ (partnerLo.map (freshShiftAbove (floorLo + windowPos) 2)).length := by
    rw [listMapLenLocal, lenLo]; exact Nat.add_le_add_left windowFits floorLo
  rcases Nat.lt_or_ge off windowPos with belowWindow | atOrAboveWindow
  · -- old port below the window: base read at `off`, shifted
    have offLtTop : off < topLen := Nat.lt_of_lt_of_le belowWindow windowFits
    have hiEq : natListGetAt (natListInsertAt (partnerHi.map (freshShiftAbove (floorHi + windowPos) 2))
          (floorHi + windowPos) [floorHi + windowPos + 1, floorHi + windowPos]) (floorHi + off)
        = freshShiftAbove (floorHi + windowPos) 2 (natListGetAt partnerHi (floorHi + off)) := by
      rw [natListGetAt_natListInsertAt_below (partnerHi.map (freshShiftAbove (floorHi + windowPos) 2))
          (floorHi + windowPos) [floorHi + windowPos + 1, floorHi + windowPos] (floorHi + off)
          (Nat.add_lt_add_left belowWindow floorHi)
          (by rw [listMapLenLocal, lenHi]; exact Nat.add_lt_add_left offLtTop floorHi),
        natListGetAt_map_inRange (freshShiftAbove (floorHi + windowPos) 2) partnerHi (floorHi + off)
          (by rw [lenHi]; exact Nat.add_lt_add_left offLtTop floorHi)]
    have loEq : natListGetAt (natListInsertAt (partnerLo.map (freshShiftAbove (floorLo + windowPos) 2))
          (floorLo + windowPos) [floorLo + windowPos + 1, floorLo + windowPos]) (floorLo + off)
        = freshShiftAbove (floorLo + windowPos) 2 (natListGetAt partnerLo (floorLo + off)) := by
      rw [natListGetAt_natListInsertAt_below (partnerLo.map (freshShiftAbove (floorLo + windowPos) 2))
          (floorLo + windowPos) [floorLo + windowPos + 1, floorLo + windowPos] (floorLo + off)
          (Nat.add_lt_add_left belowWindow floorLo)
          (by rw [listMapLenLocal, lenLo]; exact Nat.add_lt_add_left offLtTop floorLo),
        natListGetAt_map_inRange (freshShiftAbove (floorLo + windowPos) 2) partnerLo (floorLo + off)
          (by rw [lenLo]; exact Nat.add_lt_add_left offLtTop floorLo)]
    rw [hiEq, loEq]
    exact shiftedOffsetAgrees floorHi floorLo windowPos
      (natListGetAt partnerHi (floorHi + off)) (natListGetAt partnerLo (floorLo + off))
      (base off offLtTop).1 (base off offLtTop).2
  · rcases Nat.lt_or_ge off (windowPos + 1) with belowSucc | atOrAboveSucc
    · -- the fresh LEFT leg: `off = windowPos`, partner `floor + windowPos + 1`, offset `windowPos + 1`
      have offEq : off = windowPos := Nat.le_antisymm (Nat.le_of_lt_succ belowSucc) atOrAboveWindow
      subst offEq
      have hiEq : natListGetAt (natListInsertAt (partnerHi.map (freshShiftAbove (floorHi + off) 2))
            (floorHi + off) [floorHi + off + 1, floorHi + off]) (floorHi + off)
          = floorHi + off + 1 := by
        have inside := natListGetAt_natListInsertAt_inside (partnerHi.map (freshShiftAbove (floorHi + off) 2))
          (floorHi + off) [floorHi + off + 1, floorHi + off] 0 (Nat.succ_pos 1) posHiLe
        rw [Nat.add_zero] at inside
        exact inside
      have loEq : natListGetAt (natListInsertAt (partnerLo.map (freshShiftAbove (floorLo + off) 2))
            (floorLo + off) [floorLo + off + 1, floorLo + off]) (floorLo + off)
          = floorLo + off + 1 := by
        have inside := natListGetAt_natListInsertAt_inside (partnerLo.map (freshShiftAbove (floorLo + off) 2))
          (floorLo + off) [floorLo + off + 1, floorLo + off] 0 (Nat.succ_pos 1) posLoLe
        rw [Nat.add_zero] at inside
        exact inside
      rw [hiEq, loEq]
      refine ⟨⟨fun _ => Nat.le_add_right floorLo (off + 1), fun _ => Nat.le_add_right floorHi (off + 1)⟩,
        fun _ => ?_⟩
      have lhsCancel : floorHi + off + 1 - floorHi = off + 1 := addSubCancelLeftLocal floorHi (off + 1)
      have rhsCancel : floorLo + off + 1 - floorLo = off + 1 := addSubCancelLeftLocal floorLo (off + 1)
      rw [lhsCancel, rhsCancel]
    · rcases Nat.lt_or_ge off (windowPos + 2) with belowSuccSucc | atOrAboveSuccSucc
      · -- the fresh RIGHT leg: `off = windowPos + 1`, partner `floor + windowPos`, offset `windowPos`
        have offEq : off = windowPos + 1 := Nat.le_antisymm (Nat.le_of_lt_succ belowSuccSucc) atOrAboveSucc
        subst offEq
        have hiEq : natListGetAt (natListInsertAt (partnerHi.map (freshShiftAbove (floorHi + windowPos) 2))
              (floorHi + windowPos) [floorHi + windowPos + 1, floorHi + windowPos]) (floorHi + (windowPos + 1))
            = floorHi + windowPos :=
          natListGetAt_natListInsertAt_inside
            (partnerHi.map (freshShiftAbove (floorHi + windowPos) 2)) (floorHi + windowPos)
            [floorHi + windowPos + 1, floorHi + windowPos] 1 (Nat.lt_succ_self 1) posHiLe
        have loEq : natListGetAt (natListInsertAt (partnerLo.map (freshShiftAbove (floorLo + windowPos) 2))
              (floorLo + windowPos) [floorLo + windowPos + 1, floorLo + windowPos]) (floorLo + (windowPos + 1))
            = floorLo + windowPos :=
          natListGetAt_natListInsertAt_inside
            (partnerLo.map (freshShiftAbove (floorLo + windowPos) 2)) (floorLo + windowPos)
            [floorLo + windowPos + 1, floorLo + windowPos] 1 (Nat.lt_succ_self 1) posLoLe
        rw [hiEq, loEq]
        refine ⟨⟨fun _ => Nat.le_add_right floorLo windowPos, fun _ => Nat.le_add_right floorHi windowPos⟩,
          fun _ => ?_⟩
        rw [addSubCancelLeftLocal floorHi windowPos, addSubCancelLeftLocal floorLo windowPos]
      · -- old port past the window: base read at `off - 2`, shifted
        obtain ⟨gap, gapSpec⟩ := Nat.le.dest atOrAboveSuccSucc
        -- gapSpec : windowPos + 2 + gap = off
        have baseOffLtTop : windowPos + gap < topLen := by
          have shifted : windowPos + gap + 2 < topLen + 2 := by
            rw [Nat.add_right_comm windowPos gap 2, gapSpec]; exact offLt
          exact natLtOfAddLtAddRight 2 shifted
        have hiEq : natListGetAt (natListInsertAt (partnerHi.map (freshShiftAbove (floorHi + windowPos) 2))
              (floorHi + windowPos) [floorHi + windowPos + 1, floorHi + windowPos]) (floorHi + off)
            = freshShiftAbove (floorHi + windowPos) 2 (natListGetAt partnerHi (floorHi + (windowPos + gap))) := by
          have past := natListGetAt_natListInsertAt_pastBlock (partnerHi.map (freshShiftAbove (floorHi + windowPos) 2))
            (floorHi + windowPos) [floorHi + windowPos + 1, floorHi + windowPos] gap posHiLe
          have idxForm : floorHi + windowPos + gap + [floorHi + windowPos + 1, floorHi + windowPos].length
              = floorHi + off := by
            show floorHi + windowPos + gap + 2 = floorHi + off
            rw [← gapSpec, Nat.add_assoc (floorHi + windowPos) gap 2, Nat.add_assoc floorHi windowPos (gap + 2),
              Nat.add_comm gap 2, ← Nat.add_assoc windowPos 2 gap]
          rw [idxForm] at past
          rw [past, Nat.add_assoc floorHi windowPos gap,
            natListGetAt_map_inRange (freshShiftAbove (floorHi + windowPos) 2) partnerHi (floorHi + (windowPos + gap))
              (by rw [lenHi]; exact Nat.add_lt_add_left baseOffLtTop floorHi)]
        have loEq : natListGetAt (natListInsertAt (partnerLo.map (freshShiftAbove (floorLo + windowPos) 2))
              (floorLo + windowPos) [floorLo + windowPos + 1, floorLo + windowPos]) (floorLo + off)
            = freshShiftAbove (floorLo + windowPos) 2 (natListGetAt partnerLo (floorLo + (windowPos + gap))) := by
          have past := natListGetAt_natListInsertAt_pastBlock (partnerLo.map (freshShiftAbove (floorLo + windowPos) 2))
            (floorLo + windowPos) [floorLo + windowPos + 1, floorLo + windowPos] gap posLoLe
          have idxForm : floorLo + windowPos + gap + [floorLo + windowPos + 1, floorLo + windowPos].length
              = floorLo + off := by
            show floorLo + windowPos + gap + 2 = floorLo + off
            rw [← gapSpec, Nat.add_assoc (floorLo + windowPos) gap 2, Nat.add_assoc floorLo windowPos (gap + 2),
              Nat.add_comm gap 2, ← Nat.add_assoc windowPos 2 gap]
          rw [idxForm] at past
          rw [past, Nat.add_assoc floorLo windowPos gap,
            natListGetAt_map_inRange (freshShiftAbove (floorLo + windowPos) 2) partnerLo (floorLo + (windowPos + gap))
              (by rw [lenLo]; exact Nat.add_lt_add_left baseOffLtTop floorLo)]
        rw [hiEq, loEq]
        exact shiftedOffsetAgrees floorHi floorLo windowPos
          (natListGetAt partnerHi (floorHi + (windowPos + gap))) (natListGetAt partnerLo (floorLo + (windowPos + gap)))
          (base (windowPos + gap) baseOffLtTop).1 (base (windowPos + gap) baseOffLtTop).2

/-! ## Honesty marker -/

/-- **Honesty marker — the two-floor per-step lemma of the top-top offset fold is LANDED; the peel-last induction,
base-case seed reconciliation, and WireState bridge assembly around it are the un-shipped residual.**

Landed here, all zero-axiom:

  * `topRegionOffsetAgrees` — the two-floor top-region offset-space agreement relation (tag + offset per top port).
  * `shiftedOffsetAgrees` — one shifted old-port read preserves tag + offset agreement across the two floors (the
    floor factors out of the fresh-shift; the tag is exactly shift-preserved).
  * `topRegionOffsetAgrees_step` — the two-floor per-step lemma: one shared top-of-stack cup step (the
    `diagramPartner_stepCupArc` transport shape) preserves the agreement, `topLen ↦ topLen + 2`.

This is the per-step engine the peel-last two-run fold folds across the cup block.  What this marker does NOT close —
`cupTopTopPartner` (`ValleyCupReconstruct`, cup case 3), hence `cupRestrict_reconstructs` (which keeps it as a
hypothesis) and downstream `valleyAppend_split` / `valleysWithEqualMatching_spineTraceEquiv`: (i) the peel-last
induction itself, threading this per-step lemma over the whole cup block at both floors (`bottomCount` and
`midWidth`); (ii) the base-case reconciliation of the two differing seeds (`range midWidth` vs `capState`, whose
partner lists differ only OFF the top-top ports — the top-top restriction is load-bearing there); (iii) the WireState
↔ arc-encoding bridge assembly (`matchingOfSpineList` ↔ `extractArc ∘ processArcSpine`, via the shipped
`arcDiagram_eq_matching`).  A genuine multi-session brick.  No gate flag is flipped; fib-3 also carries the
independent Piece-I beam (`MatchingReductsShareSpineTrace`, #1996).  `= true`. -/
def fxMode_hasCupTopTopStepTransport : Bool := true

end FX1Poly.Polygraph
