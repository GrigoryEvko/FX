import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardFoldInterior
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescConv

/-! # BRAUER-MIDDLE r5 B2 — R3-A-CROSSING-GLUE: the six-phase split assembly + the composed cap/cup phase-fold
connectivity (the `canonicalSpiderFold_connected` analog for the Brauer standard form)

The corrected extractor's realized word `standardFormWordExt5 form` is the six-phase concatenation

    crossingWord bottomPerm ++ capWord capBlock ++ crossingWord middle
      ++ cupWord cupBlock ++ crossingWord topPerm ++ circleWord loops.

The R3-A roundtrip PROOF reduces — exactly as FROB's spider realization reduced through
`canonicalSpiderFold_connected` — to a connectivity read of the union-find fold of this word.  The r4 phase folds
`capFold_consumes` / `cupFold_creates` (`Brauer/WiringDescStandardFoldPhases.lean`) and the r5 interior generalization
`cupFold_creates_atOffset` (`Brauer/WiringDescStandardFoldInterior.lean`) build the two genuinely NEW phase folds
(the `2 ⇒ 0` cap consumption and the `0 ⇒ 2` cup creation, at the interior offset the standard form uses).  This
file GLUES them: it splits the six-phase word at its five `++` seams via `processBrauer_append` (FROB's two-phase
split at `FrobeniusConnectivityInduction.lean:377`), and COMPOSES the cap-consumption phase directly into the
interior-cup-creation phase, threading each cap arc's and each cup arc's connectivity through the composed fold.

## What this file ships (each zero-axiom, structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`)

  * **`processBrauer_links_isUnionFindForest`** — the fold-level forest preservation (`processBrauer` never breaks
    the union-find forest invariant); the fold lift of `stepWiring_links_isUnionFindForest`, the analog of the
    shipped connectivity-monotone `processBrauer_isSameComponent_ofBase`.
  * **`standardFormFold_appendSplit`** — the six-phase `processBrauer_append` decomposition: the fold of
    `standardFormWordExt5 form` from the seed is the phase-by-phase composition through the six phase-boundary states
    (bottom-crossing, cap, middle-crossing, interior-cup, top-crossing, circle).  Fully general, structural.
  * ★ **`capThenCupFold_connects`** — the COMPOSED cap/cup phase fold: firing the cap-consumption block
    `capWord (natReplicate capFeet.length 0)` then the interior cup-creation block `cupWord (natReplicate cupCount
    cupOffset)` on a state whose open wires split as `flattenNatPairs capFeet ++ (cupFront ++ cupBack)` consumes every
    cap pair, prepends `cupCount` fresh cup pairs right after `cupFront`, and leaves EVERY cap pair AND every fresh
    cup pair same-component in the composed links.  The genuine T-CONNECT direction on the cap + interior-cup phases,
    composed via `processBrauer_append` (the crossing phases enter as connectivity-monotone words — see
    `capThenCupFold_connects_survivesTail`).
  * **`capThenCupFold_connects_survivesTail`** — the cap + cup connectivity survives ANY trailing word (the
    top-crossing + circle phases, which only ADD union-find connections by
    `processBrauer_isSameComponent_ofBase`).
  * non-vacuity on a MIXED cap+cup word (`capThenCupFold_connects_mixed`, `capThenCupFold_mixedWord_diagram`).

## Honest scope — this is the six-phase GLUE machinery, NOT the roundtrip

The cap / interior-cup phase composition and its survival past the crossing phases (as connectivity-monotone words)
are the R3-A-CROSSING-GLUE leg.  The crossing phases are threaded here ONLY as monotone words (they preserve the
cap/cup connectivity); the fact that they REALIZE their through-strand permutations — routing the cup legs to
straddle the through strands — is the standing TAG CORRESPONDENCE (R3-A-TAGCORR), NOT built here.  And above all,
that the read-offs enumerate `d`'s arcs in fold order and that NO over-connection occurs (the forest-cardinality
disjointness T-DISJOINT, the long pole) remain the standing R3-A residual.  So
`fxBrauer_hasExt5CorrectedRoundtripProof` / `fxBrauer_hasExt5TotalExtractorRoundtrip` STAY `false` (no flip is
fabricated); `fxBrauer_hasBrauerV2FullCompleteness` / `fxBrauer_hasBrauerCompleteness` stay `false`; #2013 does not
close.

Raw Lean 4 + Init.  Structural recursion + `List.Mem` constructor case analysis (propext-free).  Per-declaration
`#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Fold-level forest preservation -/

/-- ★ **`processBrauer` preserves the union-find forest invariant.**  Folding any Brauer word over a forest state
leaves a forest: each `stepBrauerAtom` step preserves the forest by `stepWiring_links_isUnionFindForest`.  The
fold lift of that single-step lemma, structural on the word (the forest analog of the connectivity-monotone
`processBrauer_isSameComponent_ofBase`). -/
theorem processBrauer_links_isUnionFindForest :
    (atoms : List BrauerAtom) → (state : WireState) → isUnionFindForest state.links →
    isUnionFindForest (processBrauer state atoms).links
  | [], _state, forest => forest
  | atom :: rest, state, forest =>
      processBrauer_links_isUnionFindForest rest (stepBrauerAtom state atom)
        (stepWiring_links_isUnionFindForest state atom.position atom.wiring forest)

/-! ## The six-phase split assembly -/

/-- ★ **The six-phase `processBrauer_append` decomposition of the standard-form fold.**  The union-find fold of the
corrected extractor's realized word `standardFormWordExt5 form` from the seed is the phase-by-phase composition
through the six phase-boundary states: bottom-crossing, then cap, then middle-crossing, then interior-cup, then
top-crossing, then circle.  Splits the word at its five `++` seams by `processBrauer_append` — the Brauer
`canonicalSpiderFold_connected`-analog skeleton (FROB's two-phase split at `FrobeniusConnectivityInduction.lean`).
Fully general, structural. -/
theorem standardFormFold_appendSplit (form : BrauerStandardFormExt5) :
    processBrauer (brauerSeed form.bottomCount) (standardFormWordExt5 form)
      = processBrauer (processBrauer (processBrauer (processBrauer (processBrauer
          (processBrauer (brauerSeed form.bottomCount) (crossingWord form.bottomPerm))
            (capWord form.capBlock)) (crossingWord form.middle)) (cupWord form.cupBlock))
          (crossingWord form.topPerm)) (circleWord form.loops) := by
  show processBrauer (brauerSeed form.bottomCount)
      (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle
        ++ cupWord form.cupBlock ++ crossingWord form.topPerm ++ circleWord form.loops) = _
  rw [processBrauer_append _ _ (circleWord form.loops),
    processBrauer_append _ _ (crossingWord form.topPerm),
    processBrauer_append _ _ (cupWord form.cupBlock),
    processBrauer_append _ _ (crossingWord form.middle),
    processBrauer_append _ _ (capWord form.capBlock)]

/-! ## The composed cap / interior-cup phase fold -/

/-- ★ **The composed cap-consumption + interior-cup-creation phase fold.**  On a state whose open wires split as
`flattenNatPairs capFeet ++ (cupFront ++ cupBack)` (the cap feet at the front, then the `cupFront` block the interior
cup offset counts past, then the `cupBack` tail), firing the cap block `capWord (natReplicate capFeet.length 0)`
followed by the interior cup block `cupWord (natReplicate cupCount cupOffset)` (with `cupOffset = cupFront.length`):

  * consumes every cap pair and leaves open wires `cupFront ++ (flattenNatPairs freshFeet ++ cupBack)` — the through
    block `cupFront` stays in place, the `cupCount` fresh cup pairs land right after it;
  * connects EVERY cap pair (via `capFold_consumes`, surviving the cup phase by
    `processBrauer_isSameComponent_ofBase`);
  * connects EVERY fresh cup pair (via `cupFold_creates_atOffset`).

Composed via `processBrauer_append` — the two genuinely NEW phase folds threaded into one composed fold state (the
Brauer `canonicalSpiderFold_connected` analog for the cap + interior-cup phases). -/
theorem capThenCupFold_connects
    (capFeet : List (Nat × Nat)) (cupCount cupOffset : Nat)
    (state : WireState) (cupFront cupBack : List Nat)
    (hopen : state.openWires = flattenNatPairs capFeet ++ (cupFront ++ cupBack))
    (hlen : cupFront.length = cupOffset)
    (forest : isUnionFindForest state.links) :
    ∃ freshFeet : List (Nat × Nat),
      freshFeet.length = cupCount
      ∧ (processBrauer state (capWord (natReplicate capFeet.length 0)
          ++ cupWord (natReplicate cupCount cupOffset))).openWires
          = cupFront ++ (flattenNatPairs freshFeet ++ cupBack)
      ∧ (∀ pair, pair ∈ capFeet →
          isSameComponent (processBrauer state (capWord (natReplicate capFeet.length 0)
            ++ cupWord (natReplicate cupCount cupOffset))).links pair.1 pair.2 = true)
      ∧ (∀ pair, pair ∈ freshFeet →
          isSameComponent (processBrauer state (capWord (natReplicate capFeet.length 0)
            ++ cupWord (natReplicate cupCount cupOffset))).links pair.1 pair.2 = true) := by
  obtain ⟨hCapOpen, hCapConn⟩ := capFold_consumes capFeet state (cupFront ++ cupBack) hopen forest
  have forestCap :
      isUnionFindForest (processBrauer state (capWord (natReplicate capFeet.length 0))).links :=
    processBrauer_links_isUnionFindForest (capWord (natReplicate capFeet.length 0)) state forest
  obtain ⟨freshFeet, hLen, hCupOpen, hCupConn⟩ :=
    cupFold_creates_atOffset cupOffset cupCount
      (processBrauer state (capWord (natReplicate capFeet.length 0))) cupFront cupBack hCapOpen hlen forestCap
  have hsplit : processBrauer state
        (capWord (natReplicate capFeet.length 0) ++ cupWord (natReplicate cupCount cupOffset))
      = processBrauer (processBrauer state (capWord (natReplicate capFeet.length 0)))
          (cupWord (natReplicate cupCount cupOffset)) :=
    processBrauer_append (capWord (natReplicate capFeet.length 0)) state
      (cupWord (natReplicate cupCount cupOffset))
  refine ⟨freshFeet, hLen, ?_, ?_, ?_⟩
  · rw [hsplit]; exact hCupOpen
  · intro pair hmem
    rw [hsplit]
    exact processBrauer_isSameComponent_ofBase (cupWord (natReplicate cupCount cupOffset))
      (processBrauer state (capWord (natReplicate capFeet.length 0))) forestCap pair.1 pair.2
      (hCapConn pair hmem)
  · intro pair hmem
    rw [hsplit]
    exact hCupConn pair hmem

/-- ★ **The composed cap / cup connectivity survives the later crossing + circle phases.**  Firing any trailing
word `tailWord` (the standard form's top-crossing staircase and its circle block) after the cap + interior-cup
phases preserves every cap pair's and every fresh cup pair's connectivity — the trailing word only ADDS union-find
connections (`processBrauer_isSameComponent_ofBase`).  This is how the six-phase glue threads the cap/cup arcs
through the crossing phases as connectivity-monotone words (their permutation-realizing content is the standing
R3-A-TAGCORR, not built here). -/
theorem capThenCupFold_connects_survivesTail
    (capFeet : List (Nat × Nat)) (cupCount cupOffset : Nat)
    (state : WireState) (cupFront cupBack : List Nat) (tailWord : List BrauerAtom)
    (hopen : state.openWires = flattenNatPairs capFeet ++ (cupFront ++ cupBack))
    (hlen : cupFront.length = cupOffset)
    (forest : isUnionFindForest state.links) :
    ∃ freshFeet : List (Nat × Nat),
      freshFeet.length = cupCount
      ∧ (∀ pair, pair ∈ capFeet →
          isSameComponent (processBrauer state (capWord (natReplicate capFeet.length 0)
            ++ cupWord (natReplicate cupCount cupOffset) ++ tailWord)).links pair.1 pair.2 = true)
      ∧ (∀ pair, pair ∈ freshFeet →
          isSameComponent (processBrauer state (capWord (natReplicate capFeet.length 0)
            ++ cupWord (natReplicate cupCount cupOffset) ++ tailWord)).links pair.1 pair.2 = true) := by
  obtain ⟨freshFeet, hLen, _hOpen, hCapConn, hCupConn⟩ :=
    capThenCupFold_connects capFeet cupCount cupOffset state cupFront cupBack hopen hlen forest
  have forestCapCup :
      isUnionFindForest (processBrauer state
        (capWord (natReplicate capFeet.length 0) ++ cupWord (natReplicate cupCount cupOffset))).links :=
    processBrauer_links_isUnionFindForest
      (capWord (natReplicate capFeet.length 0) ++ cupWord (natReplicate cupCount cupOffset)) state forest
  have hsplit : processBrauer state
        (capWord (natReplicate capFeet.length 0) ++ cupWord (natReplicate cupCount cupOffset) ++ tailWord)
      = processBrauer (processBrauer state
          (capWord (natReplicate capFeet.length 0) ++ cupWord (natReplicate cupCount cupOffset))) tailWord :=
    processBrauer_append
      (capWord (natReplicate capFeet.length 0) ++ cupWord (natReplicate cupCount cupOffset)) state tailWord
  refine ⟨freshFeet, hLen, ?_, ?_⟩
  · intro pair hmem
    rw [hsplit]
    exact processBrauer_isSameComponent_ofBase tailWord
      (processBrauer state (capWord (natReplicate capFeet.length 0) ++ cupWord (natReplicate cupCount cupOffset)))
      forestCapCup pair.1 pair.2 (hCapConn pair hmem)
  · intro pair hmem
    rw [hsplit]
    exact processBrauer_isSameComponent_ofBase tailWord
      (processBrauer state (capWord (natReplicate capFeet.length 0) ++ cupWord (natReplicate cupCount cupOffset)))
      forestCapCup pair.1 pair.2 (hCupConn pair hmem)

/-! ## Non-vacuity — the composed cap/cup fold FIRES on a mixed word -/

/-- ★ **The composed cap/cup fold fires on the mixed word `[capAt 0, cupAt 2]` over four bottom wires.**  The cap
pair `(0, 1)` at the front is consumed, then one interior cup at offset `2` (behind the two through wires `2, 3`)
creates a fresh connected pair, with the cap pair AND the fresh cup pair both same-component in the composed links —
the general `capThenCupFold_connects` on a genuine mixed word (a cap phase directly feeding an interior-cup phase). -/
theorem capThenCupFold_connects_mixed :
    ∃ freshFeet : List (Nat × Nat),
      freshFeet.length = 1
      ∧ (processBrauer (brauerSeed 4)
          (capWord (natReplicate 1 0) ++ cupWord (natReplicate 1 2))).openWires
          = [2, 3] ++ (flattenNatPairs freshFeet ++ [])
      ∧ (∀ pair, pair ∈ [(0, 1)] →
          isSameComponent (processBrauer (brauerSeed 4)
            (capWord (natReplicate 1 0) ++ cupWord (natReplicate 1 2))).links pair.1 pair.2 = true)
      ∧ (∀ pair, pair ∈ freshFeet →
          isSameComponent (processBrauer (brauerSeed 4)
            (capWord (natReplicate 1 0) ++ cupWord (natReplicate 1 2))).links pair.1 pair.2 = true) :=
  capThenCupFold_connects [(0, 1)] 1 2 (brauerSeed 4) [2, 3] [] (by decide) rfl isUnionFindForest_nil

/-- Cross-check: the mixed word `[capAt 0, cupAt 2]` over four bottom wires realizes the diagram whose bottom pair
`0 ↔ 1` is capped, whose two through strands `2, 3` surface at top ports `0, 1`, and whose interior cup produces a
fresh top pair at ports `2, 3` — decided directly, the concrete diagram the composed fold connects. -/
theorem capThenCupFold_mixedWord_diagram :
    brauerDiagramOf 4 (capWord (natReplicate 1 0) ++ cupWord (natReplicate 1 2))
      = { bottomCount := 4, topCount := 4, partner := [1, 0, 4, 5, 2, 3, 7, 6], loops := 0 } := by decide

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the SIX-PHASE GLUE machinery is SHIPPED (R3-A-CROSSING-GLUE).**  `standardFormFold_appendSplit`
decomposes the corrected extractor's six-phase word at its five `++` seams via `processBrauer_append` (the Brauer
`canonicalSpiderFold_connected`-analog skeleton), `processBrauer_links_isUnionFindForest` lifts forest preservation
to the whole fold, and `capThenCupFold_connects` COMPOSES the r4 cap-consumption phase fold with the r5 interior
cup-creation phase fold into one composed fold state — connecting every cap pair AND every fresh cup pair, with the
through block preserved in place.  `capThenCupFold_connects_survivesTail` threads that connectivity through any
trailing crossing + circle phases (as connectivity-monotone words).  Cross-checked FIRING on the mixed word
`[capAt 0, cupAt 2]` (`capThenCupFold_connects_mixed`, `capThenCupFold_mixedWord_diagram`).  `= true`. -/
def fxBrauer_hasSixPhaseGlue : Bool := true

/-- **Honesty WALL marker — the six-phase glue does NOT close the roundtrip (the standing residual).**  The glue
composes the cap + interior-cup phase folds and threads them past the crossing phases as connectivity-monotone
words (T-CONNECT on the cap/cup arcs).  But the crossing phases' permutation-REALIZING content — that the top
crossing staircase routes the cup legs to straddle the through strands — is the TAG CORRESPONDENCE (R3-A-TAGCORR:
T-ENUM ∧ T-DISJOINT ∧ T-CLOSE), of which the forest-cardinality DISJOINTNESS invariant T-DISJOINT (no
over-connection, no FROB analog) is the long pole, all unbuilt.  So `fxBrauer_hasExt5CorrectedRoundtripProof` /
`fxBrauer_hasExt5TotalExtractorRoundtrip` stay `false` (no flip fabricated); `fxBrauer_hasBrauerV2FullCompleteness`
/ `fxBrauer_hasBrauerCompleteness` stay `false`; #2013 does not close.  `= false`. -/
def fxBrauer_hasSixPhaseGlueRoundtrip : Bool := false

end FX1Poly.Polygraph
