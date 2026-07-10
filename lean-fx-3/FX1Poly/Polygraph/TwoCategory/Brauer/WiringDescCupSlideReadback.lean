import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupSlideExtract

/-! # WP-BRAUER-4 r4 — the CORRECTED readback statement + decide probes (B4, gated partial)

The r4 recon refuted the shipped `∀`-general readback `BrauerCrossingOnlyReadback` (`Brauer/WiringDescBrauerLedger.lean`)
AS PHRASED: for an OUT-OF-RANGE crossing (`position + 2 > bottomCount`) the crossing word's `topCount` (`2`) mismatches
the permutation diagram's (`1`), so the unconditional `∀` cannot hold.  The corrected target is the
BOUNDARY-WIDTH-AWARE form: gated on the firing discipline `∀ q ∈ positions, q + 2 ≤ bottomCount`, exactly the premise
the shipped T2 state invariant `stateIsPermGraph_ofInRange` (`Brauer/WiringDescBrauerReadback.lean`) already carries.

## What this file ships (ADDITIVE)

  * **`BrauerCrossingOnlyReadbackInRange`** — the CORRECTED readback Prop (re-aiming the refuted `∀`): the crossing
    word's diagram equals the permutation diagram *when every position fires in range*.  Non-vacuity: it holds at a
    concrete in-range instance (`decide`).
  * **`crossingWordInRange_ofMentionsOnlyBelow`** — the glue the completeness consumer needs: a `mentionsOnlyBelow
    generatorCount`-certified crossing word fires in range on `generatorCount + 1` strands, so the in-range premise
    is FREE from the census certificate the comb fold already carries.
  * **`stabilizerPair_conv` / `loopSeparation_notConv`** — the two decide probes on the shipped decidable
    connectivity-congruence `decidableBrauerConv`: the cup-slide straddle pair decides `isTrue` (same diagram), a
    loop-creating pair decides `isFalse` (different loop count).

## The banked residual — why the #2013 masters STAY `false`

The corrected readback `BrauerCrossingOnlyReadbackInRange` is NOT proven here.  Its discharge is the
`StateIsPermGraph ⇒ extractDiagram = permutationDiagram` bridge — the shipped invariant `stateIsPermGraph_ofInRange`
gives the boundary same-component view IS the permutation graph, but the read-off that the canonical `partnerIndexOf`
scan returns exactly the permutation-forced partner (a `findPartnerScan` uniqueness argument over the permutation
graph, plus propext-careful `List`-append/map extensionality for `permutationDiagram` injectivity) is the unbuilt
node — the SAME residual `fxBrauer_hasCrossingOnlyReadback` names.  Since the B3 extraction fold ASSEMBLY is banked
(`fxBrauer_hasBrauerV2ExtractionFold = false`) and this readback bridge is unbuilt, the #2013 masters
`fxBrauer_hasBrauerCompleteness` and `fxBrauer_hasCrossingOnlyReadback` STAY `false` — NO flip is fabricated.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The CORRECTED boundary-width-aware readback statement -/

/-- ★ **The corrected crossing-only readback** (boundary-width-aware).  For every strand count and every list of
adjacent-transposition positions FIRING IN RANGE (`∀ q ∈ positions, q + 2 ≤ bottomCount`), the crossing word's Brauer
diagram equals the permutation diagram of the through-strand permutation it realizes.  This is the r4-corrected form
of the refuted `∀`-general `BrauerCrossingOnlyReadback` — the in-range gate matches the shipped T2 invariant
`stateIsPermGraph_ofInRange`'s premise. -/
def BrauerCrossingOnlyReadbackInRange : Prop :=
  ∀ (bottomCount : Nat) (positions : List Nat),
    (∀ q ∈ positions, q + 2 ≤ bottomCount) →
    brauerDiagramOf bottomCount (crossingWord positions)
      = permutationDiagram bottomCount (permuteOfCrossingWord bottomCount positions)

/-- Non-vacuity — the corrected in-range readback holds at a concrete instance beyond the ∀-refutation: two commuting
crossings `s_0 s_2` on four strands (both positions in range, `0 + 2 ≤ 4`, `2 + 2 ≤ 4`) realize `[1, 0, 3, 2]`.  So
the corrected statement is inhabited exactly where the invariant certifies it. -/
theorem brauerCrossingOnlyReadbackInRange_instance :
    (∀ q ∈ [0, 2], q + 2 ≤ 4) →
    brauerDiagramOf 4 (crossingWord [0, 2]) = permutationDiagram 4 (permuteOfCrossingWord 4 [0, 2]) :=
  fun _ => by decide

/-! ## The census-to-in-range glue (the free in-range premise for the completeness consumer) -/

/-- ★ **A `mentionsOnlyBelow generatorCount`-certified crossing word fires in range on `generatorCount + 1`
strands.**  Every position `q < generatorCount` satisfies `q + 2 ≤ generatorCount + 1` — so the in-range premise the
corrected readback (and `stateIsPermGraph_ofInRange`) needs is FREE from the census certificate the comb fold already
threads.  Structural on the word; `Nat.blt`-to-`<` via `Nat.le_of_ble_eq_true` on the definitional `Nat.blt`. -/
theorem crossingWordInRange_ofMentionsOnlyBelow (generatorCount : Nat) :
    (word : List Nat) → mentionsOnlyBelow generatorCount word = true →
    ∀ q ∈ word, q + 2 ≤ generatorCount + 1
  | [], _, q, hmem => nomatch hmem
  | position :: rest, hmob, q, hmem => by
      have hsplit : mentionsOnlyBelow generatorCount (position :: rest)
          = (Nat.blt position generatorCount && mentionsOnlyBelow generatorCount rest) := rfl
      rw [hsplit] at hmob
      have hhead : Nat.blt position generatorCount = true := by
        cases hblt : Nat.blt position generatorCount with
        | true => rfl
        | false => rw [hblt, Bool.false_and] at hmob; exact Bool.noConfusion hmob
      have htail : mentionsOnlyBelow generatorCount rest = true := by
        rw [hhead, Bool.true_and] at hmob; exact hmob
      have hposLt : position + 1 ≤ generatorCount := Nat.le_of_ble_eq_true hhead
      cases hmem with
      | head => exact Nat.succ_le_succ hposLt
      | tail _ hrest => exact crossingWordInRange_ofMentionsOnlyBelow generatorCount rest htail q hrest

/-! ## The decide probes on the shipped decidable connectivity-congruence -/

/-- ★ **Stabilizer-pair probe — `isTrue`.**  The cup-slide straddle pair `[cupAt 0, crossingAt 1]` /
`[cupAt 1, crossingAt 0]` induces the SAME diagram over one bottom wire, so the shipped `decidableBrauerConv` decides
`BrauerConv` TRUE — a `decide` witness the V2 row's two sides are genuinely convertible (not just equal words). -/
theorem stabilizerPair_conv :
    BrauerConv 1 [cupAt 0, crossingAt 1] [cupAt 1, crossingAt 0] := by decide

/-- ★ **Loop-separation probe — `isFalse`.**  A cup then a cap on its own two legs closes ONE loop
(`[cupAt 0, capAt 0]` over `0` bottom wires reads `loops := 1`), whereas the empty word reads `loops := 0`.  Different
loop counts, so `decidableBrauerConv` decides `BrauerConv` FALSE — the decision genuinely SEPARATES on the loop
character, not only the boundary matching. -/
theorem loopSeparation_notConv :
    ¬ BrauerConv 0 [cupAt 0, capAt 0] [] := by decide

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the crossing-only readback is RE-AIMED at the corrected boundary-width-aware statement.**
The refuted `∀`-general `BrauerCrossingOnlyReadback` is corrected to `BrauerCrossingOnlyReadbackInRange` (gated on
`∀ q ∈ positions, q + 2 ≤ bottomCount`, the shipped `stateIsPermGraph_ofInRange` premise), non-vacuous at a concrete
in-range instance, and the census-to-in-range glue (`crossingWordInRange_ofMentionsOnlyBelow`) supplies that premise
FREE from the comb fold's `mentionsOnlyBelow` certificate.  The corrected statement is the RIGHT target; its proof is
the `StateIsPermGraph ⇒ extractDiagram = permutationDiagram` bridge (`partnerIndexOf` permutation-graph uniqueness +
`permutationDiagram` injectivity), the SAME residual `fxBrauer_hasCrossingOnlyReadback` names.  `= true`. -/
def fxBrauer_hasCorrectedCrossingReadbackStatement : Bool := true

/-- **Honesty marker — the #2013 completeness masters STAY `false` (NO flip fabricated).**  The V2 cup-slide row
(B1), its soundness (B2), and the cup-sink move set (B3) are shipped, but the extraction-fold ASSEMBLY
(`fxBrauer_hasBrauerV2ExtractionFold`) and the crossing-only readback bridge (this file's residual) are unbuilt, so
BOTH `fxBrauer_hasBrauerCompleteness` (`Brauer/WiringDesc.lean`) and `fxBrauer_hasCrossingOnlyReadback`
(`Brauer/WiringDescBrauerLedger.lean`) STAY honestly `false`.  The shipped decidable connectivity-congruence
`decidableBrauerConv` (diagram-gated) is exercised by the probes `stabilizerPair_conv` (isTrue) /
`loopSeparation_notConv` (isFalse) — but that is the diagram-gated decision, NOT the free-relation completeness #2013
names.  `= false`. -/
def fxBrauer_hasBrauerV2CompletenessFlip : Bool := false

end FX1Poly.Polygraph
