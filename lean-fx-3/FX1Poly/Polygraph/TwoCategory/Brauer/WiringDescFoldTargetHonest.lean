import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingFoldAlignment
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescConnectivityMono

/-! # BRAUER r19 — the HONEST six-phase fold-alignment target: the r18 discipline applied to `foldRealizesTargetDiagram`

The r17/r18 file `WiringDescCrossingFoldAlignment` shipped `foldRealizesTargetDiagram` as the E3 / T-CLOSE(b)
fold-alignment TARGET invariant, proven only on the adversarial-B instance and named "TRUE, the residual is the
PROOF".  The r19 recon's headline self-attack found that claim to be OVERSTATED: `foldRealizesTargetDiagram` is
defined over the **UNCORRECTED** reconstruction `reconstructStandardFormExt5`, and that proposition is not merely
unproven in general — it is **FALSE** on a concrete well-formed involution.  This file surfaces the misstatement
(the r18 discipline: probe the truth by evaluation FIRST, never trust the narrative), REFUTES the target on the
witness, and RESTATES it honestly over the inversion-CORRECTED reconstruction `reconstructStandardFormExt5Corrected`
— on which the very same witness now holds.

## The refutation (the decisive r19 finding)

`foldRealizesTargetDiagram d` unfolds to `IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner →
extractDiagram d.bottomCount (processBrauer (brauerSeed d.bottomCount) (standardFormWordExt5
(reconstructStandardFormExt5 d))) = d`.  Because `brauerDiagramOf bc atoms` is definitionally `extractDiagram bc
(processBrauer (brauerSeed bc) atoms)` and `standardFormDiagramExt5 form = brauerDiagramOf form.bottomCount
(standardFormWordExt5 form)` with `(reconstructStandardFormExt5 d).bottomCount = d.bottomCount`, the CONCLUSION of
`foldRealizesTargetDiagram d` is exactly the GUARD of `standardFormOfDiagramExt d` — `standardFormDiagramExt5
(reconstructStandardFormExt5 d) = d`.  The shipped regression pin `standardFormOfDiagramExt_nestedCups_none` proves
that guard FAILS on `nestedCupsDiagram = {bottomCount := 0, topCount := 4, partner := [3,2,1,0], loops := 0}` (the
fully-nested crossing cups, where the uncorrected `topPerm` heuristic realizes the PARALLEL diagram).  And
`nestedCupsDiagram.partner = [3,2,1,0]` IS a boundary involution over its four top ports
(`isBoundaryInvolution_nestedCups`, each field `decide`-checked).  So the implication has a TRUE premise and a FALSE
conclusion: `¬ foldRealizesTargetDiagram nestedCupsDiagram` (`not_foldRealizesTargetDiagram_nestedCups`).  The
general target as written can NEVER be proven — `foldRealizesTargetDiagram_adversarialB` succeeded only because
adversarial-B happens to lie in the class the uncorrected extractor covers.

## The honest restatement + the same-witness contrast

`foldRealizesTargetDiagramCorrected` states the target over `reconstructStandardFormExt5Corrected` (the r3 cup-side
`permInverse` fix).  It holds on adversarial-B (`…_adversarialB`, no regression) AND on the very witness that
refutes the uncorrected target (`…_nestedCups`) — the corrected extractor routes the nested cup legs correctly
(`standardFormOfDiagramExtCorrected_nestedCups_some`).  This is the decisive contrast: the SAME diagram that
REFUTES the uncorrected fold target SATISFIES the corrected one.  The corrected target's GENERAL proof stays the
open R3-A totality / T-ENUM residual — this file does NOT flip `fxBrauer_hasFoldAlignmentE3`, and the masters stay
`false`.

## The monotonicity ingredient, exposed with an eval-first truth-probe (B1)

The six-phase assembly's "phase-k connectivity survives phases k+1..6" ingredient is the SHIPPED
`processBrauer_isSameComponent_ofBase` (`WiringDescConnectivityMono`) — a Brauer word only ever ADDS union-find
connections, never severs one.  `foldTargetConnectivity_monotone_probe` exercises it the r18 way, by evaluation
FIRST: a cap that connects bottom nodes `0`~`1` (phase 1) keeps them connected after a SECOND cap extends the link
list (a later phase).  `foldTargetConnectivity_monotone_viaLemma` then re-derives the extended-word connectivity
from the shipped monotonicity lemma over the phase-1 substate, confirming the lemma agrees with the eval.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin; independent `#print axioms` clean. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## B3a — the refutation: the uncorrected fold target is FALSE on the nested crossing cups -/

/-- ★ **The nested crossing cups form a boundary involution.**  `nestedCupsDiagram.partner = [3,2,1,0]` over the four
top ports has the right length, maps in range, is self-inverse (`0↔3`, `1↔2`), and is fixed-point-free — each field
`decide`-checked via `Nat.decidableBallLT`.  So the premise of `foldRealizesTargetDiagram nestedCupsDiagram` is
genuinely satisfiable — the refutation below is not vacuous. -/
theorem isBoundaryInvolution_nestedCups :
    IsBoundaryInvolution (nestedCupsDiagram.bottomCount + nestedCupsDiagram.topCount) nestedCupsDiagram.partner where
  hasBoundaryLength := rfl
  mapsInRange := by decide
  isSelfInverse := by decide
  isFixedPointFree := by decide

/-- ★★ **The r18-discipline headline — the UNCORRECTED six-phase fold target is FALSE.**  `foldRealizesTargetDiagram`
is defined over `reconstructStandardFormExt5`, whose conclusion on `nestedCupsDiagram` is definitionally the guard of
`standardFormOfDiagramExt` — the guard the shipped `standardFormOfDiagramExt_nestedCups_none` proves FAILS.  With the
premise `isBoundaryInvolution_nestedCups` satisfied, the implication is refuted: applying any purported proof to the
involution witness yields an equality the kernel evaluates to `false`.  Therefore the general
`foldRealizesTargetDiagram` can NEVER be a theorem — `_adversarialB` was inhabited only because adversarial-B lies in
the uncorrected extractor's covered class. -/
theorem not_foldRealizesTargetDiagram_nestedCups : ¬ foldRealizesTargetDiagram nestedCupsDiagram := by
  intro purportedProof
  exact absurd (purportedProof isBoundaryInvolution_nestedCups) (by decide)

/-! ## B3b — the honest restatement over the inversion-corrected reconstruction -/

/-- ★ **The HONEST fold-alignment target**, stated over the inversion-CORRECTED reconstruction
`reconstructStandardFormExt5Corrected` (the r3 cup-side `permInverse` fix).  For a well-formed boundary involution
`d`, running the CORRECTED standard-form word from the seed and reading the boundary matching back with
`extractDiagram` recovers `d`.  Unlike `foldRealizesTargetDiagram`, this is the truth-preserving statement: the
corrected extractor is empirically total on every perfect matching up to boundary size 8, so it is a TRUE-but-
unproven theorem (the general proof is the R3-A totality / T-ENUM residual).  Stated GATED on the involution
premise, honestly, not as an unconditional claim over the raw reconstruction. -/
def foldRealizesTargetDiagramCorrected (d : DiagramType) : Prop :=
  IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner →
    extractDiagram d.bottomCount
        (processBrauer (brauerSeed d.bottomCount) (standardFormWordExt5 (reconstructStandardFormExt5Corrected d)))
      = d

/-- ★★ **The corrected fold target holds on adversarial-B** (crossing cap + through + crossing cup + loop) — no
regression from the uncorrected target's adversarial-B inhabitant. -/
theorem foldRealizesTargetDiagramCorrected_adversarialB :
    foldRealizesTargetDiagramCorrected adversarialBDiagram :=
  fun _ => by decide

/-- ★★ **The DECISIVE contrast — the corrected fold target holds on the very witness that REFUTES the uncorrected
one.**  `nestedCupsDiagram` refutes `foldRealizesTargetDiagram` (`not_foldRealizesTargetDiagram_nestedCups`) yet
SATISFIES `foldRealizesTargetDiagramCorrected`: the `permInverse` fix routes the two nested cup legs into their
correct nesting (`{ cupBlock := [0,0], topPerm := [1,2] }`), so the corrected word reads back to `nestedCupsDiagram`
exactly.  The misstatement was in the extractor convention, not the target's spirit. -/
theorem foldRealizesTargetDiagramCorrected_nestedCups :
    foldRealizesTargetDiagramCorrected nestedCupsDiagram :=
  fun _ => by decide

/-! ## B1 — the monotonicity ingredient exposed with an eval-first truth-probe -/

/-- ★ **The monotonicity ingredient, probed by evaluation FIRST (the r18 discipline).**  A cap fired over four
bottom wires connects bottom nodes `0`~`1` in the union-find (phase 1); a SECOND cap extending the link list (a
later phase) leaves that connection intact.  Both facts evaluated by the kernel — the concrete instance of
"connectivity established in phase k survives every later phase", the ingredient the six-phase assembly rests on. -/
theorem foldTargetConnectivity_monotone_probe :
    isSameComponent (processBrauer (brauerSeed 4) [capAt 0]).links 0 1 = true
      ∧ isSameComponent (processBrauer (brauerSeed 4) [capAt 0, capAt 0]).links 0 1 = true :=
  ⟨by decide, by decide⟩

/-- ★★ **The extended-word connectivity re-derived from the SHIPPED monotonicity lemma.**  The connection `0`~`1`
established by the phase-1 cap survives the second cap by `processBrauer_isSameComponent_ofBase` (a Brauer word only
ADDS union-find connections; the forest carried across by `processBrauer_links_isUnionFindForest` from the empty seed
forest), matching `foldTargetConnectivity_monotone_probe`'s evaluated second conjunct.  This is how each per-phase
connectivity brick threads through the remaining phases in the assembly — no new induction, the shipped lemma. -/
theorem foldTargetConnectivity_monotone_viaLemma :
    isSameComponent (processBrauer (brauerSeed 4) [capAt 0, capAt 0]).links 0 1 = true :=
  processBrauer_isSameComponent_ofBase [capAt 0] (processBrauer (brauerSeed 4) [capAt 0])
    (processBrauer_links_isUnionFindForest [capAt 0] (brauerSeed 4) isUnionFindForest_nil)
    0 1 (by decide)

/-! ## B2 — per-phase corollaries: the CORRECTED extractor's crossing blocks decode to their read-off orders

Corollaries of the shipped conjugator roundtrip (`permuteOfCrossingWord_permutationToCrossingWord`) and the shipped
read-off range-permutations — phrased for the FIRST time at the `reconstructStandardFormExt5Corrected` field level,
which the six-phase assembly consumes.  The bottom side reuses the shipped raw roundtrip
`readOffBottomOrder_realizesRoundtrip` (cap side unchanged by r3); the top side is the genuinely NEW content — the
`permInverse`d top order (the r3 cup-side fix) is a range-permutation (`readOffTopOrderInverse_isPermutationOfRange`),
so its staircase decodes back to the INVERSE read-off order (only the NON-inverse top roundtrip was shipped). -/

/-- ★ **The corrected extractor's `bottomPerm` block decodes to the bottom read-off order.**  Decoding the corrected
extractor's bottom crossing staircase with `permuteOfCrossingWord` recovers `capArcFeet ++ throughStrandBottoms` — the
read-off order that routes the cap feet and through-bottoms into place.  A corollary of the shipped bottom roundtrip
`readOffBottomOrder_realizesRoundtrip`, re-phrased at the corrected-extractor field level (cap side unchanged by r3). -/
theorem correctedBottomPerm_decodesReadOff (d : DiagramType)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner) :
    permuteOfCrossingWord d.bottomCount (reconstructStandardFormExt5Corrected d).bottomPerm
      = capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner := by
  show permuteOfCrossingWord d.bottomCount
      (permutationToCrossingWord d.bottomCount
        (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner))
    = capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner
  exact readOffBottomOrder_realizesRoundtrip d.bottomCount d.topCount d.partner wf

/-- ★★ **The corrected extractor's `topPerm` block decodes to the INVERSE top read-off order — the r3 fix's content.**
Decoding the corrected extractor's top crossing staircase recovers `permInverse (throughStrandTops ++ cupArcTops)` — the
INVERTED routing the cup side (crossings applied AFTER the cups) requires, the exact defect the r3 `permInverse` fix
corrected.  The `permInverse`d order is a range-permutation (`readOffTopOrderInverse_isPermutationOfRange`), so the
shipped conjugator roundtrip `permuteOfCrossingWord_permutationToCrossingWord` decodes it — only the NON-inverse top
roundtrip `readOffTopOrder_realizesRoundtrip` was shipped, so this is genuinely new at the corrected-extractor level. -/
theorem correctedTopPerm_decodesInverseReadOff (d : DiagramType)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner) :
    permuteOfCrossingWord d.topCount (reconstructStandardFormExt5Corrected d).topPerm
      = permInverse (throughStrandTops d.bottomCount d.topCount d.partner
          ++ cupArcTops d.bottomCount d.topCount d.partner) := by
  show permuteOfCrossingWord d.topCount
      (permutationToCrossingWord d.topCount
        (permInverse (throughStrandTops d.bottomCount d.topCount d.partner
          ++ cupArcTops d.bottomCount d.topCount d.partner)))
    = permInverse (throughStrandTops d.bottomCount d.topCount d.partner
        ++ cupArcTops d.bottomCount d.topCount d.partner)
  exact permuteOfCrossingWord_permutationToCrossingWord d.topCount _
    (readOffTopOrderInverse_isPermutationOfRange d.bottomCount d.topCount d.partner wf)

/-- ★ **Non-vacuity — both corrected crossing blocks decode on adversarial-B.**  The corrected extractor's `bottomPerm`
decodes to `capArcFeet ++ throughStrandBottoms` and its `topPerm` to the `permInverse`d top order, evaluated on the
adversarial-B triple-axis instance (nontrivial crossing cap + crossing cup). -/
theorem correctedCrossingBlocks_decode_adversarialB :
    (permuteOfCrossingWord adversarialBDiagram.bottomCount
        (reconstructStandardFormExt5Corrected adversarialBDiagram).bottomPerm
      = capArcFeet adversarialBDiagram.bottomCount adversarialBDiagram.partner
          ++ throughStrandBottoms adversarialBDiagram.bottomCount adversarialBDiagram.partner)
    ∧ (permuteOfCrossingWord adversarialBDiagram.topCount
        (reconstructStandardFormExt5Corrected adversarialBDiagram).topPerm
      = permInverse (throughStrandTops adversarialBDiagram.bottomCount adversarialBDiagram.topCount
          adversarialBDiagram.partner
        ++ cupArcTops adversarialBDiagram.bottomCount adversarialBDiagram.topCount adversarialBDiagram.partner)) :=
  ⟨by decide, by decide⟩

/-! ## B4 / B5 — the honesty markers + the #2013 endgame ledger -/

/-- ★★ **Honesty marker — the UNCORRECTED six-phase fold target is machine-refuted (r19 headline).**
`not_foldRealizesTargetDiagram_nestedCups` proves `¬ foldRealizesTargetDiagram nestedCupsDiagram`: the r17/r18 target
is defined over the uncorrected reconstruction, whose conclusion is the failing guard of `standardFormOfDiagramExt`
on the nested crossing cups — with the boundary-involution premise genuinely satisfied
(`isBoundaryInvolution_nestedCups`).  The r18 discipline delivered: the "TRUE, residual is the proof" narrative on
`foldRealizesTargetDiagram` was OVERSTATED; the general statement is false, surfaced by evaluation.  `= true`. -/
def fxBrauer_hasFoldTargetRefutation : Bool := true

/-- ★★ **Honesty marker — the fold target RESTATED honestly over the corrected reconstruction (r19).**
`foldRealizesTargetDiagramCorrected` states the six-phase target over `reconstructStandardFormExt5Corrected`; it holds
on adversarial-B (`…_adversarialB`) and — decisively — on the very witness `nestedCupsDiagram` that refutes the
uncorrected target (`…_nestedCups`).  The corrected target is the truth-preserving statement (empirically total to
boundary size 8); its general proof is the open R3-A totality / T-ENUM residual.  `= true`. -/
def fxBrauer_hasFoldTargetCorrected : Bool := true

/-- ★ **Honesty marker — the monotonicity ingredient is exposed with an eval-first truth-probe (r19 B1).**  The
shipped `processBrauer_isSameComponent_ofBase` is the "phase-k connectivity survives later phases" ingredient;
`foldTargetConnectivity_monotone_probe` evaluates a concrete instance FIRST (cap-connected `0`~`1` survives a second
cap) and `foldTargetConnectivity_monotone_viaLemma` re-derives it from the lemma.  No new monotonicity lemma was
needed — the shipped one, exposed.  `= true`. -/
def fxBrauer_hasFoldTargetMonotoneProbe : Bool := true

/-- ★ **Honesty marker — the corrected extractor's crossing blocks decode to their read-off orders (r19 B2).**
`correctedBottomPerm_decodesReadOff` and `correctedTopPerm_decodesInverseReadOff` name, at the
`reconstructStandardFormExt5Corrected` field level the assembly consumes, that the bottom staircase decodes to
`capArcFeet ++ throughStrandBottoms` and the top staircase to the `permInverse`d top order (the r3 fix's semantic
content — only the NON-inverse top roundtrip was shipped).  Corollaries of the shipped conjugator roundtrip + read-off
range-permutations, firing on adversarial-B (`correctedCrossingBlocks_decode_adversarialB`).  `= true`. -/
def fxBrauer_hasCorrectedBlockDecoding : Bool := true

/-- **Honesty WALL marker — the #2013 endgame after r19: the six-phase assembly stays OPEN, now on an HONEST target.**
r19 corrected the r18 misstatement: the true target is `foldRealizesTargetDiagramCorrected` (over the CORRECTED
reconstruction), not `foldRealizesTargetDiagram` (refuted, `not_foldRealizesTargetDiagram_nestedCups`).  What stays
OPEN for `foldRealizesTargetDiagramCorrected` in general is the SIX-PHASE per-arc reassembly: **T-ENUM** (the
`capArcFeet ++ throughStrandBottoms` / cup-side read-offs are genuine permutations of their ranges — the crossing
conjugators are correct — UNBUILT, no Frobenius analog), the **through-strand cross-phase T-CONNECT** (a through
port's FINAL top node is a fresh id allocated across phases 1–5; composing the crossing-phase correspondence
`crossingWord_openWire_sameComponent_bottomPort` through the cap / `middle` / cup / `topPerm` phases via
`standardFormFold_appendSplit` needs a fresh-id bridge — UNBUILT), and a `WellFormedBrauerFold` proof for the
corrected word.  T-DISJOINT is SHIPPED (`boundedBoundaryComponents_reachable`, r12); the cap/cup per-pair T-CONNECT
is SHIPPED (`capThenCupFold_connects`); the monotonicity ingredient is SHIPPED
(`processBrauer_isSameComponent_ofBase`).  Until T-ENUM + the through-strand cross-phase bridge bind, the
tag-correspondence masters `fxBrauer_hasTagCorrDisjoint` / `fxBrauer_hasTagCorrExtraction` and
`fxBrauer_hasFoldAlignmentE3` stay honestly `false`; #2013 does NOT close.  `= false`. -/
def fxBrauer_hasFoldTargetHonestAssembly : Bool := false

end FX1Poly.Polygraph
