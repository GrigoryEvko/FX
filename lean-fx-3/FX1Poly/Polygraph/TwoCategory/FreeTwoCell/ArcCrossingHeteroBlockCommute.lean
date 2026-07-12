import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingConsCongrStep
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcWindowCommutation

/-! # MODE-COMMUTE r12 — the HETEROGENEOUS crossing×cup / crossing×cap disjoint commutes (R3)

`ArcCrossingDisjointBlockCommute` (r10) landed the crossing×crossing disjoint commute (two faithful `2⇒2`
crossings at horizontally-disjoint windows produce the SAME `ArcWireState`, hence the same extract,
UNCONDITIONALLY).  `ArcWindowCommutation` (the cup/cap kit) landed the FOUR cup/cap × cup/cap wire-list
commutation laws that the shipped `arcSwapCorePackage` peel consumes.  The general-signature swap DISPATCHER's
`ofSwap` arm needs the remaining SIXTEEN arity-pair commutes; four of them are the genuinely-new HETEROGENEOUS
crossing × cup/cap laws with a `±2` OFFSET, delivered here (r12 = R3):

  * **cup LEFT / cross RIGHT** — the crossing fires 2 HIGHER in the cup-first order (a cup adds two wires below
    the crossing window), the `+2` offset.
  * **cap LEFT / cross RIGHT** — the crossing fires 2 LOWER in the cap-first order (a cap removes two wires
    below), the `-2` offset.
  * **cross LEFT / cup RIGHT** and **cross LEFT / cap RIGHT** — no shift (a crossing preserves width, so the
    cup/cap above fires at the same position in both orders).

Every one is UNCONDITIONAL in the perfect-matching sense (like r10): both orders yield literally the same
`ArcWireState`, so the partner field's regime gating never arises.  A crossing (`stepCrossArc`) only permutes
`openWires`, allocates no fresh id, touches no links; a cup/cap allocates fresh legs / an event node that are
IDENTICAL in both orders (a crossing bumps neither `nextFresh` nor the read wires when it is horizontally
disjoint), so each whole-state equality reduces to ONE `openWires` offset-shift lemma (cup) plus a wire-read
agreement (cap, whose read is below/above the crossing window).

The `openWires` geometry is the four swap × cup/cap commutation laws, proved by structural induction on the LOW
position in the shipped `gap`-convention (`ArcWindowCommutation`'s pattern) — the high position spelled
`gap + lowPosition` / `gap + 2 + lowPosition` so the induction reduces definitionally, bounds trailing `+ 2` so
the out-of-range arms die by `Nat.not_succ_le_zero`.  Two new swap shift laws (`natListSwapTwoAt_succ`,
`natListSwapTwoAt_appendPrefix`) mirror the shipped `natListInsertAt` / `natListRemoveTwoAt` shift kit.

## What this file does NOT do (the permanent pins stay false)

It does NOT assemble the dispatcher (that is r13) and it does NOT flip the general-signature keystone.
`fxMode_hasArcPeelGeneralSignature` (the arity ceiling) and the #2043 / WP-AMALG residual
`fxMode_hasArcGodementSamePartitionFreshProof` stay `false`; the shipped `stepArcAtom` / `stepCupArc` /
`stepCapArc` / `stepCrossArc` / `extractArc` are never edited.  This certificate is strictly ADDITIVE.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.  `natListRemoveTwoAt_succ`
/ `natListInsertAt_zero` / the append-prefix shift laws are the shipped `ArcWindowCommutation` kit.
Per-declaration `#assert_no_axioms` AND independent `#print axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The swap (crossing) shift laws — the two new cons/prefix reductions the offset algebra needs -/

/-- The faithful crossing commutes with prepending a single wire, shifting the position by one — the swap
analogue of `natListRemoveTwoAt_succ`.  Not definitional (the `natListRemoveTwoAt` matcher cases the list before
the position), so proved by reducing `natListSwapTwoAt` and rewriting the shipped remove-shift. -/
theorem natListSwapTwoAt_succ (head : Nat) (tail : List Nat) (position : Nat) :
    natListSwapTwoAt (head :: tail) (position + 1) = head :: natListSwapTwoAt tail position := by
  show natListInsertAt (natListRemoveTwoAt (head :: tail) (position + 1)) (position + 1)
      [natListGetAt (head :: tail) (position + 1 + 1), natListGetAt (head :: tail) (position + 1)]
    = head :: natListSwapTwoAt tail position
  rw [natListRemoveTwoAt_succ head tail position]
  rfl

/-- The faithful crossing at position `0` on a two-plus wire list transposes the two front wires — as a REWRITE
(the `natListRemoveTwoAt` matcher cases the list, so `natListSwapTwoAt (w0 :: w1 :: rest) 0` is stuck). -/
theorem natListSwapTwoAt_zero_cons_cons (frontWire secondWire : Nat) (restWires : List Nat) :
    natListSwapTwoAt (frontWire :: secondWire :: restWires) 0 = secondWire :: frontWire :: restWires := by
  show natListInsertAt (natListRemoveTwoAt (frontWire :: secondWire :: restWires) 0) 0
      [natListGetAt (frontWire :: secondWire :: restWires) 1,
       natListGetAt (frontWire :: secondWire :: restWires) 0]
    = secondWire :: frontWire :: restWires
  exact natListInsertAt_zero restWires [secondWire, frontWire]

/-- The faithful crossing commutes with prepending a two-wire block, shifting the position by two — the swap
analogue of the append-prefix shift for a length-2 prefix, from two `natListSwapTwoAt_succ` steps. -/
theorem natListSwapTwoAt_prependTwo (firstWire secondWire : Nat) (tail : List Nat) (position : Nat) :
    natListSwapTwoAt (firstWire :: secondWire :: tail) (position + 2)
      = firstWire :: secondWire :: natListSwapTwoAt tail position := by
  show natListSwapTwoAt (firstWire :: secondWire :: tail) (position + 1 + 1)
    = firstWire :: secondWire :: natListSwapTwoAt tail position
  rw [natListSwapTwoAt_succ firstWire (secondWire :: tail) (position + 1),
    natListSwapTwoAt_succ secondWire tail position]

/-- Removing a pair after prepending a two-wire block, shifting the position by two — the length-2 prepend shift
for `natListRemoveTwoAt`, from two `natListRemoveTwoAt_succ` steps. -/
theorem natListRemoveTwoAt_prependTwo (firstWire secondWire : Nat) (tail : List Nat) (position : Nat) :
    natListRemoveTwoAt (firstWire :: secondWire :: tail) (position + 2)
      = firstWire :: secondWire :: natListRemoveTwoAt tail position := by
  show natListRemoveTwoAt (firstWire :: secondWire :: tail) (position + 1 + 1)
    = firstWire :: secondWire :: natListRemoveTwoAt tail position
  rw [natListRemoveTwoAt_succ firstWire (secondWire :: tail) (position + 1),
    natListRemoveTwoAt_succ secondWire tail position]

/-- The faithful crossing at a position shifted past a prefix acts inside the suffix: the prefix rides along
untouched — the swap analogue of `natListInsertAt_appendPrefix` / `natListRemoveTwoAt_appendPrefix`. -/
theorem natListSwapTwoAt_appendPrefix :
    (prefixWires wires : List Nat) → (position : Nat) →
    natListSwapTwoAt (prefixWires ++ wires) (prefixWires.length + position)
      = prefixWires ++ natListSwapTwoAt wires position
  | [], wires, position => by
      show natListSwapTwoAt wires (0 + position) = natListSwapTwoAt wires position
      rw [Nat.zero_add]
  | headWire :: restPrefix, wires, position => by
      show natListSwapTwoAt (headWire :: (restPrefix ++ wires)) (restPrefix.length + 1 + position)
          = headWire :: (restPrefix ++ natListSwapTwoAt wires position)
      rw [Nat.add_right_comm restPrefix.length 1 position,
        natListSwapTwoAt_succ headWire (restPrefix ++ wires) (restPrefix.length + position)]
      exact congrArg (headWire :: ·)
        (natListSwapTwoAt_appendPrefix restPrefix wires position)

/-! ## The four heterogeneous crossing × cup/cap commutation laws (the openWires offset algebra) -/

/-- ★ **Splice below commutes past a crossing above (the `+2` offset).**  Crossing at `gap + lowPosition` then
splicing `lowBlock` at `lowPosition` equals splicing first and crossing at the position shifted UP by
`lowBlock.length` — the cup-LEFT / cross-RIGHT geometry.  The in-range swap-window bound is required. -/
theorem natListInsertAt_swapAbove_commute :
    (wires : List Nat) → (lowPosition gap : Nat) → (lowBlock : List Nat) →
    gap + lowPosition + 2 ≤ wires.length →
    natListInsertAt (natListSwapTwoAt wires (gap + lowPosition)) lowPosition lowBlock
      = natListSwapTwoAt (natListInsertAt wires lowPosition lowBlock) (gap + lowBlock.length + lowPosition)
  | wires, 0, gap, lowBlock, _ => by
      show natListInsertAt (natListSwapTwoAt wires gap) 0 lowBlock
        = natListSwapTwoAt (natListInsertAt wires 0 lowBlock) (gap + lowBlock.length)
      rw [natListInsertAt_zero (natListSwapTwoAt wires gap) lowBlock,
        natListInsertAt_zero wires lowBlock, Nat.add_comm gap lowBlock.length,
        natListSwapTwoAt_appendPrefix lowBlock wires gap]
  | [], lowPosition + 1, gap, lowBlock, boundHigh =>
      absurd boundHigh (Nat.not_succ_le_zero _)
  | headWire :: restWires, lowPosition + 1, gap, lowBlock, boundHigh => by
      show natListInsertAt (natListSwapTwoAt (headWire :: restWires) (gap + lowPosition + 1))
            (lowPosition + 1) lowBlock
          = natListSwapTwoAt (headWire :: natListInsertAt restWires lowPosition lowBlock)
              (gap + lowBlock.length + lowPosition + 1)
      rw [natListSwapTwoAt_succ headWire restWires (gap + lowPosition),
        natListSwapTwoAt_succ headWire (natListInsertAt restWires lowPosition lowBlock)
          (gap + lowBlock.length + lowPosition)]
      exact congrArg (headWire :: ·)
        (natListInsertAt_swapAbove_commute restWires lowPosition gap lowBlock
          (Nat.le_of_succ_le_succ boundHigh))

/-- ★ **A crossing below commutes past a splice above (no shift).**  Splicing `highBlock` at `gap + 2 +
lowPosition` (above the crossing window) then crossing at `lowPosition` equals crossing first and splicing at the
same position — the cross-LEFT / cup-RIGHT geometry (a crossing preserves width, so no shift). -/
theorem natListSwapTwoAt_insertAbove_commute :
    (wires : List Nat) → (lowPosition gap : Nat) → (highBlock : List Nat) →
    lowPosition + 2 ≤ wires.length →
    natListSwapTwoAt (natListInsertAt wires (gap + 2 + lowPosition) highBlock) lowPosition
      = natListInsertAt (natListSwapTwoAt wires lowPosition) (gap + 2 + lowPosition) highBlock
  | [], 0, _, _, boundLow => absurd boundLow (Nat.not_succ_le_zero _)
  | [_], 0, _, _, boundLow => absurd (Nat.le_of_succ_le_succ boundLow) (Nat.not_succ_le_zero 0)
  | frontWire :: secondWire :: restWires, 0, gap, highBlock, _ => by
      show natListSwapTwoAt (natListInsertAt (frontWire :: secondWire :: restWires) (gap + 2) highBlock) 0
        = natListInsertAt (natListSwapTwoAt (frontWire :: secondWire :: restWires) 0) (gap + 2) highBlock
      rw [natListSwapTwoAt_zero_cons_cons frontWire secondWire restWires]
      show natListSwapTwoAt (frontWire :: secondWire :: natListInsertAt restWires gap highBlock) 0
        = secondWire :: frontWire :: natListInsertAt restWires gap highBlock
      exact natListSwapTwoAt_zero_cons_cons frontWire secondWire (natListInsertAt restWires gap highBlock)
  | [], lowPosition + 1, _, _, boundLow => absurd boundLow (Nat.not_succ_le_zero _)
  | headWire :: restWires, lowPosition + 1, gap, highBlock, boundLow => by
      show natListSwapTwoAt (headWire :: natListInsertAt restWires (gap + 2 + lowPosition) highBlock)
            (lowPosition + 1)
          = natListInsertAt (natListSwapTwoAt (headWire :: restWires) (lowPosition + 1))
              (gap + 2 + lowPosition + 1) highBlock
      rw [natListSwapTwoAt_succ headWire (natListInsertAt restWires (gap + 2 + lowPosition) highBlock) lowPosition,
        natListSwapTwoAt_succ headWire restWires lowPosition]
      exact congrArg (headWire :: ·)
        (natListSwapTwoAt_insertAbove_commute restWires lowPosition gap highBlock
          (Nat.le_of_succ_le_succ boundLow))

/-- ★ **Pair removal below commutes past a crossing above (the `-2` offset).**  Crossing at `gap + 2 +
lowPosition` then removing the pair at `lowPosition` equals removing first and crossing at the position shifted
DOWN by the removed pair's width — the cap-LEFT / cross-RIGHT geometry. -/
theorem natListRemoveTwoAt_swapAbove_commute :
    (wires : List Nat) → (lowPosition gap : Nat) →
    gap + lowPosition + 2 ≤ wires.length →
    natListRemoveTwoAt (natListSwapTwoAt wires (gap + 2 + lowPosition)) lowPosition
      = natListSwapTwoAt (natListRemoveTwoAt wires lowPosition) (gap + lowPosition)
  | [], _, _, boundHigh => absurd boundHigh (Nat.not_succ_le_zero _)
  | [_], 0, gap, boundHigh => absurd (Nat.le_of_succ_le_succ boundHigh) (Nat.not_succ_le_zero gap)
  | frontWire :: secondWire :: restWires, 0, gap, _ => by
      show natListRemoveTwoAt (natListSwapTwoAt (frontWire :: secondWire :: restWires) (gap + 2)) 0
        = natListSwapTwoAt (natListRemoveTwoAt (frontWire :: secondWire :: restWires) 0) gap
      rw [natListSwapTwoAt_prependTwo frontWire secondWire restWires gap]
      rfl
  | firstWire :: restWires, lowPosition + 1, gap, boundHigh => by
      show natListRemoveTwoAt (natListSwapTwoAt (firstWire :: restWires) (gap + 2 + lowPosition + 1))
            (lowPosition + 1)
          = natListSwapTwoAt (natListRemoveTwoAt (firstWire :: restWires) (lowPosition + 1)) (gap + lowPosition + 1)
      rw [natListSwapTwoAt_succ firstWire restWires (gap + 2 + lowPosition),
        natListRemoveTwoAt_succ firstWire (natListSwapTwoAt restWires (gap + 2 + lowPosition)) lowPosition,
        natListRemoveTwoAt_succ firstWire restWires lowPosition,
        natListSwapTwoAt_succ firstWire (natListRemoveTwoAt restWires lowPosition) (gap + lowPosition)]
      exact congrArg (firstWire :: ·)
        (natListRemoveTwoAt_swapAbove_commute restWires lowPosition gap (Nat.le_of_succ_le_succ boundHigh))

/-- ★ **A crossing below commutes past a pair removal above (no shift).**  Removing the pair at `gap + 2 +
lowPosition` (above the crossing window) then crossing at `lowPosition` equals crossing first and removing at the
same position — the cross-LEFT / cap-RIGHT geometry. -/
theorem natListSwapTwoAt_removeAbove_commute :
    (wires : List Nat) → (lowPosition gap : Nat) →
    lowPosition + 2 ≤ wires.length →
    natListSwapTwoAt (natListRemoveTwoAt wires (gap + 2 + lowPosition)) lowPosition
      = natListRemoveTwoAt (natListSwapTwoAt wires lowPosition) (gap + 2 + lowPosition)
  | [], 0, _, boundLow => absurd boundLow (Nat.not_succ_le_zero _)
  | [_], 0, _, boundLow => absurd (Nat.le_of_succ_le_succ boundLow) (Nat.not_succ_le_zero 0)
  | frontWire :: secondWire :: restWires, 0, gap, _ => by
      show natListSwapTwoAt (natListRemoveTwoAt (frontWire :: secondWire :: restWires) (gap + 2)) 0
        = natListRemoveTwoAt (natListSwapTwoAt (frontWire :: secondWire :: restWires) 0) (gap + 2)
      rw [natListRemoveTwoAt_prependTwo frontWire secondWire restWires gap,
        natListSwapTwoAt_zero_cons_cons frontWire secondWire (natListRemoveTwoAt restWires gap),
        natListSwapTwoAt_zero_cons_cons frontWire secondWire restWires,
        natListRemoveTwoAt_prependTwo secondWire frontWire restWires gap]
  | [], lowPosition + 1, _, boundLow => absurd boundLow (Nat.not_succ_le_zero _)
  | headWire :: restWires, lowPosition + 1, gap, boundLow => by
      show natListSwapTwoAt (natListRemoveTwoAt (headWire :: restWires) (gap + 2 + lowPosition + 1))
            (lowPosition + 1)
          = natListRemoveTwoAt (natListSwapTwoAt (headWire :: restWires) (lowPosition + 1))
              (gap + 2 + lowPosition + 1)
      rw [natListRemoveTwoAt_succ headWire restWires (gap + 2 + lowPosition),
        natListSwapTwoAt_succ headWire (natListRemoveTwoAt restWires (gap + 2 + lowPosition)) lowPosition,
        natListSwapTwoAt_succ headWire restWires lowPosition,
        natListRemoveTwoAt_succ headWire (natListSwapTwoAt restWires lowPosition) (gap + 2 + lowPosition)]
      exact congrArg (headWire :: ·)
        (natListSwapTwoAt_removeAbove_commute restWires lowPosition gap (Nat.le_of_succ_le_succ boundLow))

/-! ## The state-level heterogeneous commutes — CUP cases

A cup allocates its two legs and event node from `nextFresh`, which a horizontally-disjoint crossing never bumps,
so the cup's `links` / `nextFresh` / `loops` / `cupEventNodes` / `capEventNodes` are IDENTICAL in both orders; a
crossing only permutes `openWires`.  So each whole-state equality is exactly the `openWires` offset law above
(the other five fields agree definitionally, exposed by `dsimp only [stepCrossArc, stepCupArc]`). -/

/-- ★ **cup LEFT / cross RIGHT commute (the `+2` offset).**  Firing the cup at `lowPosition` (inserting two
wires) then the crossing at the shifted window `gap + 2 + lowPosition` equals firing the crossing first at the
unshifted `gap + lowPosition` then the cup — the SAME `ArcWireState`, hence the same extract.  Window: the
crossing's window in range. -/
theorem stepCrossArc_stepCupArc_heteroCommute (state : ArcWireState) (lowPosition gap : Nat)
    (window : gap + lowPosition + 2 ≤ state.openWires.length) :
    stepCrossArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)
      = stepCupArc (stepCrossArc state (gap + lowPosition)) lowPosition := by
  dsimp only [stepCrossArc, stepCupArc]
  congr 1
  exact (natListInsertAt_swapAbove_commute state.openWires lowPosition gap
    [state.nextFresh, state.nextFresh + 1] window).symm

/-- ★ **cross LEFT / cup RIGHT commute (no shift).**  A crossing preserves width, so the cup above fires at the
same window `gap + 2 + lowPosition` in both orders — the SAME `ArcWireState`.  Window: the crossing's window in
range. -/
theorem stepCupArc_stepCrossArc_heteroCommute (state : ArcWireState) (lowPosition gap : Nat)
    (window : lowPosition + 2 ≤ state.openWires.length) :
    stepCupArc (stepCrossArc state lowPosition) (gap + 2 + lowPosition)
      = stepCrossArc (stepCupArc state (gap + 2 + lowPosition)) lowPosition := by
  dsimp only [stepCrossArc, stepCupArc]
  congr 1
  exact (natListSwapTwoAt_insertAbove_commute state.openWires lowPosition gap
    [state.nextFresh, state.nextFresh + 1] window).symm

/-- ★ **The whole extract commutes — cup LEFT / cross RIGHT.**  Equal states have equal extracts, so the entire
`FullArcStructure` (diagram + partner + cup/cap totals + per-port internal counts) is order-independent. -/
theorem extractArc_stepCrossArc_stepCupArc_disjointCommute (bottomCount : Nat) (state : ArcWireState)
    (lowPosition gap : Nat) (window : gap + lowPosition + 2 ≤ state.openWires.length) :
    extractArc bottomCount (stepCrossArc (stepCupArc state lowPosition) (gap + 2 + lowPosition))
      = extractArc bottomCount (stepCupArc (stepCrossArc state (gap + lowPosition)) lowPosition) :=
  congrArg (extractArc bottomCount)
    (stepCrossArc_stepCupArc_heteroCommute state lowPosition gap window)

/-- ★ **The whole extract commutes — cross LEFT / cup RIGHT.** -/
theorem extractArc_stepCupArc_stepCrossArc_disjointCommute (bottomCount : Nat) (state : ArcWireState)
    (lowPosition gap : Nat) (window : lowPosition + 2 ≤ state.openWires.length) :
    extractArc bottomCount (stepCupArc (stepCrossArc state lowPosition) (gap + 2 + lowPosition))
      = extractArc bottomCount (stepCrossArc (stepCupArc state (gap + 2 + lowPosition)) lowPosition) :=
  congrArg (extractArc bottomCount)
    (stepCupArc_stepCrossArc_heteroCommute state lowPosition gap window)

/-! ## Wire-read agreement — a crossing outside the cap's window leaves its two read wires unchanged

A cap reads its two wires positionally through `natListGetAt`; a crossing at a horizontally-disjoint window fixes
every index outside `{swapPos, swapPos + 1}` (the shipped `natListGetAt_natListSwapTwoAt` composed with
`transposeAdjacent_other`), so the cap's `leftWire` / `rightWire`, its component test (`loops`), and its link
joins are IDENTICAL in both orders.  This is the cap analogue of the cup's constant fresh legs. -/

/-- Reading a swapped list at an index BELOW the swap window equals reading the original there. -/
theorem natListGetAt_natListSwapTwoAt_below (wires : List Nat) (swapPos index : Nat)
    (window : swapPos + 1 < wires.length) (below : index < swapPos) :
    natListGetAt (natListSwapTwoAt wires swapPos) index = natListGetAt wires index := by
  rw [natListGetAt_natListSwapTwoAt wires swapPos index window,
    transposeAdjacent_other swapPos index (Nat.ne_of_lt below)
      (Nat.ne_of_lt (Nat.lt_trans below (Nat.lt_succ_self swapPos)))]

/-- Reading a swapped list at an index ABOVE the swap window equals reading the original there. -/
theorem natListGetAt_natListSwapTwoAt_above (wires : List Nat) (swapPos index : Nat)
    (window : swapPos + 1 < wires.length) (above : swapPos + 1 < index) :
    natListGetAt (natListSwapTwoAt wires swapPos) index = natListGetAt wires index := by
  rw [natListGetAt_natListSwapTwoAt wires swapPos index window,
    transposeAdjacent_other swapPos index
      (Nat.ne_of_gt (Nat.lt_trans (Nat.lt_succ_self swapPos) above)) (Nat.ne_of_gt above)]

/-- `lowPosition + 1 < gap + 2 + lowPosition` — the low cap/cross window sits strictly below the shifted high
window (the disjointness gap is at least two). -/
private theorem lowPos_succ_lt_gapShift (lowPosition gap : Nat) :
    lowPosition + 1 < gap + 2 + lowPosition := by
  have base : lowPosition + 1 < lowPosition + (gap + 2) :=
    Nat.add_lt_add_left (Nat.succ_lt_succ (Nat.succ_pos gap)) lowPosition
  rw [Nat.add_comm lowPosition (gap + 2)] at base
  exact base

/-- From the reduct crossing's in-range window, the list-law bound for the openWires offset. -/
private theorem listBound_of_crossWindow (gap lowPosition scanLength : Nat)
    (crossWindow : gap + 2 + lowPosition + 1 < scanLength) : gap + lowPosition + 2 ≤ scanLength := by
  have shape : gap + 2 + lowPosition + 1 = gap + lowPosition + 3 := by
    rw [Nat.add_right_comm gap 2 lowPosition]
  rw [shape] at crossWindow
  exact Nat.le_trans (Nat.le_succ (gap + lowPosition + 2)) (Nat.le_of_lt crossWindow)

/-! ## The state-level heterogeneous commutes — CAP cases -/

/-- ★ **cap LEFT / cross RIGHT commute (the `-2` offset).**  Firing the cap at `lowPosition` (removing two
wires) then the crossing at the shifted window `gap + lowPosition` equals firing the crossing first at the
unshifted `gap + 2 + lowPosition` then the cap — the SAME `ArcWireState`.  The cap's read wires agree because the
crossing acts strictly above them; window: the reduct crossing in range. -/
theorem stepCrossArc_stepCapArc_heteroCommute (state : ArcWireState) (lowPosition gap : Nat)
    (crossWindow : gap + 2 + lowPosition + 1 < state.openWires.length) :
    stepCrossArc (stepCapArc state lowPosition) (gap + lowPosition)
      = stepCapArc (stepCrossArc state (gap + 2 + lowPosition)) lowPosition := by
  have readLeft : natListGetAt (natListSwapTwoAt state.openWires (gap + 2 + lowPosition)) lowPosition
      = natListGetAt state.openWires lowPosition :=
    natListGetAt_natListSwapTwoAt_below state.openWires (gap + 2 + lowPosition) lowPosition crossWindow
      (Nat.lt_of_succ_lt (lowPos_succ_lt_gapShift lowPosition gap))
  have readRight : natListGetAt (natListSwapTwoAt state.openWires (gap + 2 + lowPosition)) (lowPosition + 1)
      = natListGetAt state.openWires (lowPosition + 1) :=
    natListGetAt_natListSwapTwoAt_below state.openWires (gap + 2 + lowPosition) (lowPosition + 1) crossWindow
      (lowPos_succ_lt_gapShift lowPosition gap)
  dsimp only [stepCrossArc, stepCapArc]
  rw [readLeft, readRight]
  congr 1
  exact (natListRemoveTwoAt_swapAbove_commute state.openWires lowPosition gap
    (listBound_of_crossWindow gap lowPosition state.openWires.length crossWindow)).symm

/-- ★ **cross LEFT / cap RIGHT commute (no shift).**  A crossing preserves width, so the cap above fires at the
same window `gap + 2 + lowPosition` in both orders — the SAME `ArcWireState`.  The cap's read wires agree because
the crossing acts strictly below them; window: the crossing in range. -/
theorem stepCapArc_stepCrossArc_heteroCommute (state : ArcWireState) (lowPosition gap : Nat)
    (swapWindow : lowPosition + 1 < state.openWires.length) :
    stepCapArc (stepCrossArc state lowPosition) (gap + 2 + lowPosition)
      = stepCrossArc (stepCapArc state (gap + 2 + lowPosition)) lowPosition := by
  have readLeft : natListGetAt (natListSwapTwoAt state.openWires lowPosition) (gap + 2 + lowPosition)
      = natListGetAt state.openWires (gap + 2 + lowPosition) :=
    natListGetAt_natListSwapTwoAt_above state.openWires lowPosition (gap + 2 + lowPosition) swapWindow
      (lowPos_succ_lt_gapShift lowPosition gap)
  have readRight : natListGetAt (natListSwapTwoAt state.openWires lowPosition) (gap + 2 + lowPosition + 1)
      = natListGetAt state.openWires (gap + 2 + lowPosition + 1) :=
    natListGetAt_natListSwapTwoAt_above state.openWires lowPosition (gap + 2 + lowPosition + 1) swapWindow
      (Nat.lt_trans (lowPos_succ_lt_gapShift lowPosition gap) (Nat.lt_succ_self (gap + 2 + lowPosition)))
  dsimp only [stepCrossArc, stepCapArc]
  rw [readLeft, readRight]
  congr 1
  exact (natListSwapTwoAt_removeAbove_commute state.openWires lowPosition gap swapWindow).symm

/-- ★ **The whole extract commutes — cap LEFT / cross RIGHT.** -/
theorem extractArc_stepCrossArc_stepCapArc_disjointCommute (bottomCount : Nat) (state : ArcWireState)
    (lowPosition gap : Nat) (crossWindow : gap + 2 + lowPosition + 1 < state.openWires.length) :
    extractArc bottomCount (stepCrossArc (stepCapArc state lowPosition) (gap + lowPosition))
      = extractArc bottomCount (stepCapArc (stepCrossArc state (gap + 2 + lowPosition)) lowPosition) :=
  congrArg (extractArc bottomCount)
    (stepCrossArc_stepCapArc_heteroCommute state lowPosition gap crossWindow)

/-- ★ **The whole extract commutes — cross LEFT / cap RIGHT.** -/
theorem extractArc_stepCapArc_stepCrossArc_disjointCommute (bottomCount : Nat) (state : ArcWireState)
    (lowPosition gap : Nat) (swapWindow : lowPosition + 1 < state.openWires.length) :
    extractArc bottomCount (stepCapArc (stepCrossArc state lowPosition) (gap + 2 + lowPosition))
      = extractArc bottomCount (stepCrossArc (stepCapArc state (gap + 2 + lowPosition)) lowPosition) :=
  congrArg (extractArc bottomCount)
    (stepCapArc_stepCrossArc_heteroCommute state lowPosition gap swapWindow)

/-! ## Non-vacuity witnesses — the heterogeneous commutes fire at the fresh seed -/

/-- `List.range.loop count acc` has length `count + acc.length` (structural, propext-free per-file copy — the
core `List.length_range` leaks `propext`). -/
private theorem heteroRangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := heteroRangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

/-- `(List.range count).length = count`, propext-free. -/
private theorem heteroRangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [heteroRangeLoopLength count []]
  exact Nat.add_zero count

/-- The seed arc state with `bottomCount` open wires and no history. -/
private def heteroSeed (bottomCount : Nat) : ArcWireState :=
  ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []

/-- ★ **Non-vacuous: the cup LEFT / cross RIGHT extract commute fires at every fresh seed with an in-range
disjoint window.**  A parameterized application — not a hand fixture. -/
theorem arcCrossingHeteroBlockCommute_cupSeed_confirms (bottomCount lowPosition gap : Nat)
    (window : gap + lowPosition + 2 ≤ bottomCount) :
    extractArc bottomCount (stepCrossArc (stepCupArc (heteroSeed bottomCount) lowPosition) (gap + 2 + lowPosition))
      = extractArc bottomCount
          (stepCupArc (stepCrossArc (heteroSeed bottomCount) (gap + lowPosition)) lowPosition) :=
  extractArc_stepCrossArc_stepCupArc_disjointCommute bottomCount (heteroSeed bottomCount) lowPosition gap
    (by
      show gap + lowPosition + 2 ≤ (List.range bottomCount).length
      rw [heteroRangeLength]
      exact window)

/-- ★ **Non-vacuous: the cap LEFT / cross RIGHT extract commute fires at every fresh seed with an in-range
disjoint window.** -/
theorem arcCrossingHeteroBlockCommute_capSeed_confirms (bottomCount lowPosition gap : Nat)
    (crossWindow : gap + 2 + lowPosition + 1 < bottomCount) :
    extractArc bottomCount (stepCrossArc (stepCapArc (heteroSeed bottomCount) lowPosition) (gap + lowPosition))
      = extractArc bottomCount
          (stepCapArc (stepCrossArc (heteroSeed bottomCount) (gap + 2 + lowPosition)) lowPosition) :=
  extractArc_stepCrossArc_stepCapArc_disjointCommute bottomCount (heteroSeed bottomCount) lowPosition gap
    (by
      show gap + 2 + lowPosition + 1 < (List.range bottomCount).length
      rw [heteroRangeLength]
      exact crossWindow)

/-! ## Honesty marker + pins -/

/-- **Honesty marker — the FOUR heterogeneous crossing × cup/cap disjoint commutes are SHIPPED (R3).**  The
`openWires` offset algebra (`natListInsertAt_swapAbove_commute` / `natListSwapTwoAt_insertAbove_commute` /
`natListRemoveTwoAt_swapAbove_commute` / `natListSwapTwoAt_removeAbove_commute`, from the two new swap shift laws
`natListSwapTwoAt_succ` / `natListSwapTwoAt_appendPrefix`) lifts to the whole `ArcWireState`
(`stepCrossArc_stepCupArc_heteroCommute` and its three siblings) — the cup allocates constant fresh legs, the cap
reads wires the crossing leaves fixed (`natListGetAt_natListSwapTwoAt_below` / `_above`), so both firing orders
yield literally the SAME state, hence the SAME `FullArcStructure` (the four `extractArc_…_disjointCommute`).  The
`+2` / `-2` / no-shift offsets are the recon's CASE A / B / C-D, delivered UNCONDITIONALLY (no perfect-matching
regime), exactly the r10 crossing×crossing shape.  Non-vacuous at every fresh seed
(`arcCrossingHeteroBlockCommute_cupSeed_confirms` / `_capSeed_confirms`).  These four fill the heterogeneous
`ofSwap` arms the general-signature swap dispatcher (r13) needs; the shipped `stepArcAtom` / `stepCupArc` /
`stepCapArc` / `stepCrossArc` / `extractArc` are never edited.  `= true`. -/
def fxMode_hasArcCrossingHeteroBlockCommute : Bool := true

/-- **Honesty pin — the r10 crossing×crossing disjoint commute stays `true`.**  These heterogeneous commutes are
the four MIXED arity pairs; the r10 marker is the homogeneous `2⇒2 × 2⇒2` arm, untouched.  `rfl`. -/
theorem arcCrossingHeteroBlockCommute_disjointBlockCommute_stays_true :
    fxMode_hasArcCrossingDisjointBlockCommute = true := rfl

/-- **Honesty pin — the r11 crossing `consCongr` step stays `true`.**  A distinct fact (the head-cons
faithful-step invariants), untouched.  `rfl`. -/
theorem arcCrossingHeteroBlockCommute_consCongrStep_stays_true :
    fxMode_hasArcCrossingConsCongrStep = true := rfl

/-- **Honesty pin — the shipped cup/cap window-op commutation kit stays `true`.**  This file adds the SWAP
analogues; the cup/cap × cup/cap kit is untouched.  `rfl`. -/
theorem arcCrossingHeteroBlockCommute_windowOpCommutation_stays_true :
    fxMode_hasArcWindowOpCommutation = true := rfl

/-- **Honesty pin — the general-signature peel stays the open keystone.**  These four arms supply the crossing's
heterogeneous disjoint-block Godement independence a general-signature peel's `ofSwap` needs, but they do NOT
build the `arcSwapCorePackage` dispatcher (no builder arm assembled).  `fxMode_hasArcPeelGeneralSignature` stays
`false`.  `rfl`. -/
theorem arcCrossingHeteroBlockCommute_generalSignature_stays_false :
    fxMode_hasArcPeelGeneralSignature = false := rfl

/-- **Honesty pin — the #2043 / WP-AMALG fresh-partition keystone is untouched.**
`fxMode_hasArcGodementSamePartitionFreshProof` stays `false`.  `rfl`. -/
theorem arcCrossingHeteroBlockCommute_samePartitionFreshProof_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
