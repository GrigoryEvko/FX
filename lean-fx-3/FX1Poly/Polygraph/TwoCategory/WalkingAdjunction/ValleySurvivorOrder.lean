import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyAppendSplit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # ValleySurvivorOrder — the through-strand order-preservation leg of the valley-append split

Piece II tail of the fib-3 gate needs the THROUGH-STRAND (survivor) re-ranking: a bottom port that no cap in the
cap block consumes passes through the whole valley, and its partner top port is pinned by its RANK among the
through-bottoms.  The rank is preserved between the cap-block-alone matching and the whole-valley matching because
the cup block only inserts NEW top arcs above — it never reorders the survivors' top targets.

This file lands the FOUNDATION of that re-ranking: the **survivor-order-preservation** leg.  A pure-cup block, run
from any boundary-tracking mid-state, maps the mid-state's open wires into the final open wires by a STRICTLY
MONOTONE, VALUE-PRESERVING position embedding.  Cups splice fresh legs via `natListInsertAt`, which inserts a
block BETWEEN existing wires (`natListGetAt_natListInsertAt_below` / `…_pastBlock`) and never reorders them
(`shiftPastPosition` is strictly monotone).  Folded over the whole cup block (conditioned on the boundary-chain
discipline `SpineBoundaryChained`, which pins each cup's firing position in range), the composite embedding
witnesses that every survivor's relative order — hence its rank among the through-bottoms — is exactly what it was
at the mid-state.

  * ★ `WireOrderEmbedding` — a strictly-monotone, `natListGetAt`-preserving, in-range position map between two
    wire lists (the "inserts between, never reorders" invariant, packaged for the fold).
  * `shiftPastPosition` + its value/order/bound lemmas — the single-`natListInsertAt` embedding datum.
  * `stepCup_wireOrderEmbedding` — one cup embeds its pre-wires into its post-wires.
  * `wireOrderEmbedding_comp` / `wireOrderEmbedding_id` — the fold's monoid.
  * ★ `processSpine_wireOrderEmbedding_ofAllCupArity` — THE survivor-order-preservation leg: a pure-cup block
    order-embeds any boundary-tracking mid-state's open wires into the final open wires.

Raw Lean 4 + Init; structural / fold recursion, no `omega` / `simp`-AC / `WellFounded.fix`.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The single-splice position embedding -/

/-- The position map a splice of a length-`blockLength` block at `position` induces on the pre-existing wires:
positions strictly below the splice stay put; positions at or beyond it shift up by the block length.  This is the
"inserts between, never reorders" map — strictly monotone and `natListGetAt`-preserving (below). -/
def shiftPastPosition (position blockLength index : Nat) : Nat :=
  if index < position then index else index + blockLength

/-- A splice reads through its position map unchanged: the wire at `index` before the splice sits at
`shiftPastPosition position block.length index` after it (in range, with the splice position itself in range so
past-position reads are not lost off the end). -/
theorem natListGetAt_shiftPastPosition (wires block : List Nat) (position index : Nat)
    (posInRange : position ≤ wires.length) (indexInRange : index < wires.length) :
    natListGetAt (natListInsertAt wires position block)
        (shiftPastPosition position block.length index)
      = natListGetAt wires index := by
  unfold shiftPastPosition
  rcases Nat.lt_or_ge index position with belowPosition | atOrBeyond
  · rw [if_pos belowPosition]
    exact natListGetAt_natListInsertAt_below wires position block index belowPosition indexInRange
  · rw [if_neg (Nat.not_lt.mpr atOrBeyond)]
    obtain ⟨offset, offsetEq⟩ := Nat.le.dest atOrBeyond
    rw [← offsetEq]
    exact natListGetAt_natListInsertAt_pastBlock wires position block offset posInRange

/-- The splice position map is strictly monotone — it never reorders the pre-existing wires. -/
theorem shiftPastPosition_strictMono (position blockLength : Nat) {firstIndex secondIndex : Nat}
    (indexLt : firstIndex < secondIndex) :
    shiftPastPosition position blockLength firstIndex < shiftPastPosition position blockLength secondIndex := by
  unfold shiftPastPosition
  rcases Nat.lt_or_ge firstIndex position with firstBelow | firstAtOrBeyond
  · rcases Nat.lt_or_ge secondIndex position with secondBelow | secondAtOrBeyond
    · rw [if_pos firstBelow, if_pos secondBelow]; exact indexLt
    · rw [if_pos firstBelow, if_neg (Nat.not_lt.mpr secondAtOrBeyond)]
      exact Nat.lt_of_lt_of_le indexLt (Nat.le_add_right secondIndex blockLength)
  · rcases Nat.lt_or_ge secondIndex position with secondBelow | secondAtOrBeyond
    · exact absurd (Nat.lt_of_lt_of_le secondBelow firstAtOrBeyond) (Nat.lt_asymm indexLt)
    · rw [if_neg (Nat.not_lt.mpr firstAtOrBeyond), if_neg (Nat.not_lt.mpr secondAtOrBeyond)]
      exact Nat.add_lt_add_right indexLt blockLength

/-- The splice position map keeps an in-range read in range (the post-list is longer by the block length). -/
theorem shiftPastPosition_lt (position blockLength index bound : Nat) (indexInRange : index < bound) :
    shiftPastPosition position blockLength index < bound + blockLength := by
  unfold shiftPastPosition
  rcases Nat.lt_or_ge index position with belowPosition | atOrBeyond
  · rw [if_pos belowPosition]
    exact Nat.lt_of_lt_of_le indexInRange (Nat.le_add_right bound blockLength)
  · rw [if_neg (Nat.not_lt.mpr atOrBeyond)]
    exact Nat.add_lt_add_right indexInRange blockLength

/-! ## The order-embedding invariant and its monoid -/

/-- A **wire-order embedding** from `source` into `target`: a strictly-monotone position map that reads every
in-range `source` wire to the same value at an in-range `target` position.  Packages "inserts between, never
reorders, never drops" so a pure-cup block's cumulative effect on the open wires composes through the fold. -/
structure WireOrderEmbedding (phi : Nat → Nat) (source target : List Nat) : Prop where
  /-- The position map preserves strict order — survivors keep their relative order. -/
  strictMono : ∀ firstIndex secondIndex, firstIndex < secondIndex → phi firstIndex < phi secondIndex
  /-- The position map preserves the wire value read at every in-range source position. -/
  reads : ∀ index, index < source.length → natListGetAt target (phi index) = natListGetAt source index
  /-- The position map lands every in-range source position in range of the target. -/
  inRange : ∀ index, index < source.length → phi index < target.length

/-- The identity order embedding of a wire list into itself. -/
theorem wireOrderEmbedding_id (source : List Nat) :
    WireOrderEmbedding (fun index => index) source source :=
  { strictMono := fun _ _ indexLt => indexLt
    reads := fun _ _ => rfl
    inRange := fun _ indexInRange => indexInRange }

/-- Order embeddings compose: `source ↪ middle ↪ target` gives `source ↪ target`. -/
theorem wireOrderEmbedding_comp {phiFirst phiSecond : Nat → Nat} {source middle target : List Nat}
    (embFirst : WireOrderEmbedding phiFirst source middle)
    (embSecond : WireOrderEmbedding phiSecond middle target) :
    WireOrderEmbedding (fun index => phiSecond (phiFirst index)) source target :=
  { strictMono := fun firstIndex secondIndex indexLt =>
      embSecond.strictMono _ _ (embFirst.strictMono firstIndex secondIndex indexLt)
    reads := fun index indexInRange => by
      rw [embSecond.reads (phiFirst index) (embFirst.inRange index indexInRange),
        embFirst.reads index indexInRange]
    inRange := fun index indexInRange =>
      embSecond.inRange (phiFirst index) (embFirst.inRange index indexInRange) }

/-- ★ **One cup order-embeds its pre-wires into its post-wires.**  The cup splices its two fresh legs at
`position` (`stepCup_openWires`), so the pre-wires read through `shiftPastPosition position 2` unchanged
(`natListGetAt_shiftPastPosition`), in order (`shiftPastPosition_strictMono`) and in range
(`shiftPastPosition_lt`, the post-list is two longer via `natListInsertAt_length`).  The firing position must be
in range (`posInRange`) so no past-position survivor is lost off the end. -/
theorem stepCup_wireOrderEmbedding (state : WireState) (position : Nat)
    (posInRange : position ≤ state.openWires.length) :
    WireOrderEmbedding (shiftPastPosition position 2) state.openWires
      (stepCup state position).openWires :=
  { strictMono := fun _ _ indexLt => shiftPastPosition_strictMono position 2 indexLt
    reads := fun index indexInRange => by
      rw [stepCup_openWires]
      exact natListGetAt_shiftPastPosition state.openWires
        [state.nextFresh, state.nextFresh + 1] position index posInRange indexInRange
    inRange := fun index indexInRange => by
      rw [stepCup_openWires, natListInsertAt_length]
      exact shiftPastPosition_lt position 2 index state.openWires.length indexInRange }

/-! ## The survivor-order-preservation leg -/

/-- ★ **Survivor-order-preservation — a pure-cup block order-embeds any boundary-tracking mid-state's open wires
into its final open wires.**  Run from a state whose open wires have length exactly the running boundary
(`tracks`) and whose atoms are boundary-chained (`chained`, pinning each cup's firing position in range), a
pure-cup block cumulatively splices only NEW top legs — so the mid-state's wires survive in the same relative
order and with the same values.  By induction on the `AllCupArity` witness: each cup fires at
`leftContext.length ≤ boundaryLength` (its dom width vanishes), embedding its pre-wires by
`stepCup_wireOrderEmbedding`; the post-state tracks the head's cod boundary (two wider), so the tail's embedding
composes on (`wireOrderEmbedding_comp`).  This is the order half of the through-strand re-ranking: since the
survivors keep their relative order in the open wires, their RANK among the through-bottoms is identical at the
mid-state and at the whole-valley final state. -/
theorem processSpine_wireOrderEmbedding_ofAllCupArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (state : WireState) → (boundaryLength : Nat) →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    ∃ phi, WireOrderEmbedding phi state.openWires (processSpine state atoms).openWires := by
  induction pureCup with
  | nil =>
      intro state _ _ _
      exact ⟨fun index => index, wireOrderEmbedding_id state.openWires⟩
  | cons hasCupDomArity hasCupCodArity _restAllCup restEmbed =>
      rename_i headAtom rest
      intro state boundaryLength tracks chained
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have posLeBoundary : headAtom.leftContext.length ≤ boundaryLength := by
        rw [← headFires]
        show headAtom.leftContext.length
          ≤ headAtom.leftContext.length + headAtom.generatorDom.length + headAtom.rightContext.length
        rw [hasCupDomArity, Nat.add_zero]
        exact Nat.le_add_right headAtom.leftContext.length headAtom.rightContext.length
      have posInRange : headAtom.leftContext.length ≤ state.openWires.length := by
        rw [tracks]; exact posLeBoundary
      have newTracks : (stepCup state headAtom.leftContext.length).openWires.length
          = headAtom.codBoundaryLength := by
        rw [stepCup_openWires, natListInsertAt_length]
        show state.openWires.length + 2 = headAtom.codBoundaryLength
        rw [tracks, ← headFires]
        show headAtom.leftContext.length + headAtom.generatorDom.length + headAtom.rightContext.length + 2
          = headAtom.leftContext.length + headAtom.generatorCod.length + headAtom.rightContext.length
        rw [hasCupDomArity, hasCupCodArity, Nat.add_zero]
        exact Nat.add_right_comm headAtom.leftContext.length headAtom.rightContext.length 2
      obtain ⟨phiRest, embRest⟩ :=
        restEmbed (stepCup state headAtom.leftContext.length) headAtom.codBoundaryLength newTracks tailChained
      have headEmbed := stepCup_wireOrderEmbedding state headAtom.leftContext.length posInRange
      show ∃ phi, WireOrderEmbedding phi state.openWires
        (processSpine (stepAtom state headAtom) rest).openWires
      rw [stepAtom_ofCupArity state headAtom hasCupDomArity hasCupCodArity]
      exact ⟨fun index => phiRest (shiftPastPosition headAtom.leftContext.length 2 index),
        wireOrderEmbedding_comp headEmbed embRest⟩

/-! ## Honesty marker -/

/-- **Honesty marker — the survivor-order-preservation leg is SHIPPED; the rank read-off through the shifting top
boundary is the residual (#2185).**

Landed here, all zero-axiom:

  * `processSpine_wireOrderEmbedding_ofAllCupArity` — a pure-cup block order-embeds any boundary-tracking
    mid-state's open wires into the final open wires: a strictly-monotone, value-preserving, in-range position map
    (`WireOrderEmbedding`).  The survivors keep their relative ORDER in the open wires, so their rank among the
    through-bottoms is invariant between the cap-block-alone mid-state and the whole-valley final state.  Built
    from the single-splice embedding `stepCup_wireOrderEmbedding` (cups splice fresh legs BETWEEN wires via
    `natListInsertAt`, never reordering — `shiftPastPosition` strictly monotone) folded over the cup block through
    the embedding monoid (`wireOrderEmbedding_comp` / `wireOrderEmbedding_id`), with the boundary-chain discipline
    pinning each cup's firing position in range.

What this marker does NOT claim: the full re-ranking `survivorPartner_reranking` — that a survivor bottom port's
`partnerIndexOf` in the whole valley equals `bc + (rank among through-bottoms)`, matching the cap-block-alone
value.  That step must convert the OPEN-WIRE order embedding above into a BOUNDARY-INDEX statement about
`partnerIndexOf`, whose `findPartnerScan` walks `List.range total` over `boundaryNodes = List.range bc ++
topWires` — and the top-port block, hence `total` and the absolute boundary indices, SHIFTS when the cup block
adds fresh top arcs.  Recovering the rank through that shifting boundary scan (a scan-level bijection matching the
order embedding here) is the standing "mid-state rigidity / index-shift bijection" residual — the valley-descent
beam #2185.  No gate flag is flipped.  `= true`. -/
def fxMode_hasValleySurvivorOrderPreservation : Bool := true

end FX1Poly.Polygraph
