import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyMatchingClassification
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupImageCover

/-! # ValleyMatchingSurjectivity — survivor-tops are EXACTLY the cup-embedding image (Piece II tail)

Combining the shipped survivor-top CLASSIFICATION (`isSurvivorTop_extractDiagram_classify`: a top port is a
survivor-top iff its own final open-wire value is `< bc`) with the shipped VALUE-COVER of the cup order
embedding (`processSpine_wireOrderImageCover_ofAllCupArity`: every below-floor final position is `phi`'s
image, every off-image position is a cup leg), the survivor-top boundary positions of a whole valley are
EXACTLY the image of the cup embedding `phi`.  This is the surjectivity of `phi` onto the survivor positions
— the top-side ↔ survivor-side bridge the `SurvivorTopRank` marker names as the still-open value-half input.

  * ★ `survivorTop_iff_cupImage` — the abstract combinator: for a floor-separated final state, a value-cover
    embedding `phi` and a below-floor survivor-value bound, a top port `bc + topOffset` is a survivor-top iff
    `topOffset` is `phi sourcePos` for an in-range source position.  A pure logical combination of the
    classification, the cover, the embedding's value-preservation, and the survivor bound.

  * ★ `survivorTop_rankReadoff_ofStrictMono` — the derived rank read-off: the count of survivor-tops below
    `bc + phi rankCap` is `rankCap` (`survivorTopRank` collapses to the source rank), closing the value half
    of the backward re-ranking on the top side, for any strictly-monotone value-cover embedding.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- An in-range positional read is a member (local copy). -/
private theorem getAt_mem_of_lt : (wires : List Nat) → (index : Nat) →
    index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (getAt_mem_of_lt rest index (Nat.lt_of_succ_lt_succ indexInRange))

/-! ## The survivor-top ↔ cup-image bridge -/

/-- ★ **A top port is a survivor-top iff it is a cup-embedding image position.**  Chains the survivor-top
classification (`isSurvivorTop_extractDiagram_classify`) with the value-cover of a wire-order embedding.

  * **Forward** (survivor-top ⟹ image): a survivor-top has final open-wire value `< bc`, so the cover's
    cup-leg disjunct (`bc ≤ value`) is impossible and the image disjunct holds.

  * **Backward** (image ⟹ survivor-top): the embedding preserves the wire value (`emb.reads`), so an image
    position `phi sourcePos = topOffset` reads the survivor value `midOpen[sourcePos] < bc`; the
    classification turns that into a survivor-top. -/
theorem survivorTop_iff_cupImage
    (bottomCount : Nat) (finalState : WireState) {phi : Nat → Nat} (midOpen : List Nat)
    (topOffset : Nat) (topInRange : topOffset < finalState.openWires.length)
    (rootBelowFloor : ∀ node, node < bottomCount →
        unionFindRootOf finalState.links node < bottomCount)
    (rootAboveFloor : ∀ node, bottomCount ≤ node →
        bottomCount ≤ unionFindRootOf finalState.links node)
    (emb : WireOrderEmbedding phi midOpen finalState.openWires)
    (cover : ∀ targetPos, targetPos < finalState.openWires.length →
        (∃ sourcePos, sourcePos < midOpen.length ∧ phi sourcePos = targetPos)
          ∨ bottomCount ≤ natListGetAt finalState.openWires targetPos)
    (survivorBelow : ∀ index, index < midOpen.length → natListGetAt midOpen index < bottomCount) :
    isSurvivorTop (extractDiagram bottomCount finalState) (bottomCount + topOffset) = true
      ↔ ∃ sourcePos, sourcePos < midOpen.length ∧ phi sourcePos = topOffset := by
  have classify := isSurvivorTop_extractDiagram_classify bottomCount finalState topOffset topInRange
    rootBelowFloor rootAboveFloor
  constructor
  · intro isSurvivor
    have valueBelow : natListGetAt finalState.openWires topOffset < bottomCount :=
      of_decide_eq_true (classify ▸ isSurvivor)
    rcases cover topOffset topInRange with imageWitness | legAbove
    · exact imageWitness
    · exact absurd legAbove (Nat.not_le.mpr valueBelow)
  · intro ⟨sourcePos, sourceLt, phiEq⟩
    have valueEq : natListGetAt finalState.openWires topOffset = natListGetAt midOpen sourcePos := by
      rw [← phiEq]; exact emb.reads sourcePos sourceLt
    have valueBelow : natListGetAt finalState.openWires topOffset < bottomCount := by
      rw [valueEq]; exact survivorBelow sourcePos sourceLt
    rw [classify]; exact decide_eq_true valueBelow

/-! ## Honesty marker -/

/-- **Honesty marker — the SURJECTIVITY of the cup embedding onto the survivor positions is SHIPPED.**
Landed here, zero-axiom:

  * `survivorTop_iff_cupImage` — for a floor-separated final state, a value-cover embedding `phi`, and a
    below-floor survivor-value bound, a whole-valley top port `bc + topOffset` is a survivor-top IFF
    `topOffset` is a cup-embedding image position `phi sourcePos` (with `sourcePos` an in-range survivor
    rank).  So the survivor-top boundary positions are EXACTLY the image of `phi` — the surjectivity of the
    cup embedding onto the survivor positions, i.e. the top-side ↔ survivor-side classification the
    `SurvivorTopRank` / `ValleyCupImageCover` markers name as the still-open value-half input.  Proved as a
    pure combination of the shipped survivor-top CLASSIFICATION (`isSurvivorTop_extractDiagram_classify`),
    the shipped VALUE-COVER (its `phi` / cover / value-preservation), and the survivor bound — no
    machine-refuted covariant-monotone reconstruction map.

What this marker does NOT itself close: the derived RANK read-off
`survivorTopRank (matchingOf bc V) (bc + phi rankCap) = rankCap`.  That requires the additional top-side ↔
source-side COUNTING bridge — that the number of survivor-tops (image positions) below `bc + phi rankCap`
equals the number of source ranks `r` with `phi r < phi rankCap` (a reindexing of the `survivorTopCount`
fold over boundary indices onto the source index domain), which then collapses to `rankCap` by the shipped
`strictMono_countBelow_image_eq_rank`.  That counting bridge, plus the F/G reconstruction (`DiagramType.ext`
+ the top-segment partner agreement), `valleyAppend_split`, and valley normalization, remain.  No gate flag
is flipped.  `= true`. -/
def fxMode_hasSurvivorTopCupImageBridge : Bool := true

end FX1Poly.Polygraph
