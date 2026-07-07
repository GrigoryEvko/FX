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
    of the backward re-ranking on the top side, for any strictly-monotone value-cover embedding.  Landed here,
    via the image-count reindex `countBelow_atStrictMonoImage_eq_rank` (the counting bridge).

  * ★ `survivorTop_matchingValley_iff_cupImage` — the CONCRETE whole-valley instance: for the actual valley
    `capAtoms ++ cupAtoms` run from the canonical seed, every hypothesis of `survivorTop_iff_cupImage` is
    discharged from shipped seed facts (image cover, N1/N2 roots, survivor bound), yielding the surjectivity at
    the concrete `matchingOf` with no abstract hypotheses left.

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

/-! ## The rank read-off — the counting bridge closes -/

/-- ★ **The survivor-top rank read-off.**  Under the same floor-separation + value-cover hypotheses as
`survivorTop_iff_cupImage`, the count of survivor-tops strictly below a survivor's whole-valley partner top
port `bottomCount + phi rankCap` is exactly `rankCap`.  The chain: `survivorTopRank` unfolds to
`countBelow (isSurvivorTop diagram)`; the bottom segment `[0, bottomCount)` never passes `isSurvivorTop`
(`countBelow_add_eq` + the all-false bottom vanish), leaving a count over the top offsets `[0, phi rankCap)`;
over those offsets the survivor-top predicate marks EXACTLY the cup-embedding images (`survivorTop_iff_cupImage`,
both directions), so the image-count reindex `countBelow_atStrictMonoImage_eq_rank` collapses the top-side count
to the source rank `rankCap`.  This is the value half of the backward re-ranking on the TOP side — the counting
bridge the `SurvivorTopRank` marker named as residual #2185's still-open input, now closed. -/
theorem survivorTop_rankReadoff_ofStrictMono
    (bottomCount : Nat) (finalState : WireState) {phi : Nat → Nat} (midOpen : List Nat)
    (rootBelowFloor : ∀ node, node < bottomCount →
        unionFindRootOf finalState.links node < bottomCount)
    (rootAboveFloor : ∀ node, bottomCount ≤ node →
        bottomCount ≤ unionFindRootOf finalState.links node)
    (emb : WireOrderEmbedding phi midOpen finalState.openWires)
    (cover : ∀ targetPos, targetPos < finalState.openWires.length →
        (∃ sourcePos, sourcePos < midOpen.length ∧ phi sourcePos = targetPos)
          ∨ bottomCount ≤ natListGetAt finalState.openWires targetPos)
    (survivorBelow : ∀ index, index < midOpen.length → natListGetAt midOpen index < bottomCount)
    {rankCap : Nat} (rankLt : rankCap < midOpen.length) :
    survivorTopRank (extractDiagram bottomCount finalState) (bottomCount + phi rankCap) = rankCap := by
  show survivorTopCount (extractDiagram bottomCount finalState) (bottomCount + phi rankCap) = rankCap
  rw [survivorTopCount_eq_countBelow,
    countBelow_add_eq (isSurvivorTop (extractDiagram bottomCount finalState)) bottomCount (phi rankCap)]
  have bottomZero :
      countBelow (isSurvivorTop (extractDiagram bottomCount finalState)) bottomCount = 0 := by
    apply countBelow_eq_zero_of_allFalse
    intro index indexLt
    show (Nat.ble (extractDiagram bottomCount finalState).bottomCount index
        && Nat.blt (natListGetAt (extractDiagram bottomCount finalState).partner index)
            (extractDiagram bottomCount finalState).bottomCount) = false
    have bleFalse : Nat.ble (extractDiagram bottomCount finalState).bottomCount index = false := by
      cases hble : Nat.ble (extractDiagram bottomCount finalState).bottomCount index with
      | false => rfl
      | true => exact absurd (Nat.le_of_ble_eq_true hble) (Nat.not_le.mpr indexLt)
    rw [bleFalse, Bool.false_and]
  rw [bottomZero, Nat.zero_add]
  exact countBelow_atStrictMonoImage_eq_rank
    (sourceLength := midOpen.length) (finalLength := finalState.openWires.length)
    emb.strictMono
    (fun sourcePos sourceLt =>
      (survivorTop_iff_cupImage bottomCount finalState midOpen (phi sourcePos)
        (emb.inRange sourcePos sourceLt) rootBelowFloor rootAboveFloor emb cover survivorBelow).mpr
        ⟨sourcePos, sourceLt, rfl⟩)
    (fun sourcePos sourceLt => emb.inRange sourcePos sourceLt)
    (fun offset offsetLt noSrc => by
      cases hval : isSurvivorTop (extractDiagram bottomCount finalState) (bottomCount + offset) with
      | false => rfl
      | true =>
          obtain ⟨sourcePos, sourceLt, phiEq⟩ :=
            (survivorTop_iff_cupImage bottomCount finalState midOpen offset offsetLt
              rootBelowFloor rootAboveFloor emb cover survivorBelow).mp hval
          exact absurd phiEq (noSrc sourcePos sourceLt))
    rankCap rankLt

/-! ## The concrete whole-valley surjectivity — all hypotheses discharged from shipped seed facts -/

/-- ★ **The concrete whole-valley survivor-top ↔ cup-image bridge.**  Instantiates the abstract
`survivorTop_iff_cupImage` at the actual whole valley `capAtoms ++ cupAtoms` run from the canonical seed,
discharging every hypothesis from shipped facts: the cup block's order embedding + value cover
(`processSpine_wireOrderImageCover_ofAllCupArity` at `freshFloor := bottomCount`, its `freshLe` premise from
`processSpine_nextFresh_ofAllCapArity_seed`), the floor-separation roots N1/N2
(`valleyRootBelowFloor` / `valleyCupLegRootAboveFloor`), and the survivor bound
(`processSpine_openWires_below_ofAllCapArity_seed`).  So the whole valley's survivor-top boundary positions are
EXACTLY the image of the cup embedding `phi` — the surjectivity at the concrete `matchingOf`, no abstract
hypotheses left. -/
theorem survivorTop_matchingValley_iff_cupImage
    {overallSource overallMiddle overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capAtoms : List (SpineAtom adjunctionModeSignature overallSource overallMiddle))
    (cupAtoms : List (SpineAtom adjunctionModeSignature overallMiddle overallTarget))
    (pureCap : AllCapArity capAtoms) (pureCup : AllCupArity cupAtoms)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms).openWires.length cupAtoms) :
    ∃ phi,
      WireOrderEmbedding phi
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms).openWires
          (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms)
            cupAtoms).openWires ∧
      ∀ topOffset,
        topOffset < (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms)
            cupAtoms).openWires.length →
        (isSurvivorTop (extractDiagram bottomCount
            (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms) cupAtoms))
            (bottomCount + topOffset) = true
          ↔ ∃ sourcePos,
              sourcePos < (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms).openWires.length
                ∧ phi sourcePos = topOffset) := by
  obtain ⟨phi, emb, cover⟩ := processSpine_wireOrderImageCover_ofAllCupArity bottomCount cupAtoms pureCup
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms)
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms).openWires.length rfl
    (Nat.le_of_eq (processSpine_nextFresh_ofAllCapArity_seed bottomCount capAtoms pureCap).symm)
    cupChained
  refine ⟨phi, emb, ?_⟩
  intro topOffset topInRange
  exact survivorTop_iff_cupImage bottomCount
    (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms) cupAtoms)
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms).openWires
    topOffset topInRange
    (fun node nodeBelow =>
      valleyRootBelowFloor bottomCount bottomPositive capAtoms cupAtoms pureCap pureCup node nodeBelow)
    (fun node nodeAbove =>
      valleyCupLegRootAboveFloor bottomCount bottomPositive capAtoms cupAtoms pureCap pureCup node nodeAbove)
    emb cover
    (fun index indexLt =>
      processSpine_openWires_below_ofAllCapArity_seed bottomCount bottomPositive capAtoms pureCap
        (natListGetAt (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms).openWires index)
        (getAt_mem_of_lt (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms).openWires
          index indexLt))

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

Also CLOSED here: the derived RANK read-off `survivorTopRank (matchingOf bc V) (bc + phi rankCap) = rankCap`
(`survivorTop_rankReadoff_ofStrictMono`) and its concrete whole-valley surjectivity instance
(`survivorTop_matchingValley_iff_cupImage`).  The top-side ↔ source-side COUNTING bridge — that the number of
survivor-tops (image positions) below `bc + phi rankCap` collapses to `rankCap` — is now the new
`countBelow_atStrictMonoImage_eq_rank` (SurvivorTopRank), a direct structural induction sliding a false window
across the cup-leg holes between consecutive images.

What this marker does NOT close (the standing wall): the F/G reconstruction (`capRestrict` / `cupRestrict` on
`DiagramType`, the `DiagramType.mk.injEq` field ext, the top-segment partner-list agreement threaded through
`phi`), `valleyAppend_split`, and valley normalization.  No gate flag is flipped.  `= true`. -/
def fxMode_hasSurvivorTopCupImageBridge : Bool := true

end FX1Poly.Polygraph
