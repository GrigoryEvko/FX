import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerReadbackProof
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerCompleteness
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupSlideReadback

/-! # BRAUER-V2 r2 B3/B4 — UNCONDITIONAL crossing-only completeness + the pass-5-arc wall ledger

With the corrected crossing-only readback `brauerCrossingOnlyReadbackInRange` now PROVEN zero-axiom
(`WiringDescBrauerReadbackProof.brauerCrossingOnlyReadbackInRange_proof`), the crossing-only leg of Brauer
completeness ceases to be conditional: the shipped reduction `crossingCompleteness_of_readback` (which consumed the
∀-general — and REFUTED — `BrauerCrossingOnlyReadback` as a hypothesis) is re-founded here on the proven in-range
readback, discharging its premise FREE from the `mentionsOnlyBelow` census certificate the comb fold already carries.

## What this file ships (each zero-axiom, structural)

  * `crossingCompleteness_inRange` — ★ UNCONDITIONAL: equal `brauerDiagramOf` on crossing words (over generators in
    range) ⟹ `BrauerConvFree7`-convertibility.  No readback hypothesis.  (`crossingCompleteness_of_readback_r9`,
    the r9 jam pair `[2,0,1,2]`/`[0,1,2,1]`, is now dischargeable hypothesis-free — its concrete `decide` on the
    four-strand `brauerDiagramOf` fold is a kernel-cost, not a proof, residual, so the reduction is stated generically.)
  * the two decision verdicts re-surfaced (`stabilizerPair_conv` isTrue on a nontrivial chain, `loopSeparation_notConv`
    isFalse by loop-count separation) — the shipped diagram-gated `decidableBrauerConv` exercised both ways.
  * the honest ledger: crossing block CLOSES; the FULL V2 free word problem `fxBrauer_hasBrauerCompleteness`
    stays FALSE, WALLED on the cup/cap arc-selection driver-fold (pass-5-arc); #2013 does NOT close this round.

## The pass-5-arc WALL (why #2013 stays open after r2)

The full-completeness driver `brauerWords_equalMatching_conv` needs, per pass, (a) conv-to-standard-form and
(b) canonicity.  Passes 1 (untwist-NF), 4 (crossing straighten), and 5-crossing (this readback) all CLOSE.  It CAPS
on **pass-5-arc — the cup/cap arc-selection driver-fold** at exactly the configuration:

> a Brauer diagram whose cup and cap arcs are mutually INTERLEAVED — a cap arc `(i,j)` and a cup arc `(k,l)` with
> `i < k < j < l` in boundary order — which the non-crossing `partnerIndexOf` matching admits within one block but
> which forces a slide of a cup PAST a cap during the sort.  Every shipped move fires
> (`cupSlideStraddleFree8_inContext`, `distantCupCapSlideFree8`, foot-swap absorb) and the `ArcNonCrossing` invariant
> holds, yet no shipped `Nat`-fuel monovariant descends per arc-extraction step: the `WiringDescInsertion` windowPin
> SELECTS the next cup/cap to cut but the selection is length/inversion-FROZEN across a cup-past-cap commute, exactly
> as the `S_n` braid ascent freezes `ell = inversionCount`.  So pass-5-arc is a DRIVER wall of `pureCupSpine_sort`
> magnitude — a route/measure gap, not an obstruction to truth (Graham–Lehrer *Cellular algebras*, Invent. math. 123
> (1996), guarantees the standard-form triple exists and is unique modulo the foot-swap stabilizer).

The bequest for breaching it: a distinguished-arc lexicographic descent `(outermostUnsortedArc, arcSpan, legDistance)`
supplying the `Nat`-fuel recursion the fold lacks — the arc-level analog of the Matsumoto–Tits distinguished-active
-letter descent.  The arc gets NO r3 (2-round cap); this is the permanent wall statement. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **UNCONDITIONAL crossing-only Brauer completeness.**  Two crossing words over generators `< generatorCount`
inducing the SAME Brauer diagram on `generatorCount + 1` strands are `BrauerConvFree7`-convertible — with NO readback
hypothesis.  The proven in-range readback (`brauerCrossingOnlyReadbackInRange_proof`) turns diagram equality into
permutation-diagram equality (its in-range premise supplied FREE by `crossingWordInRange_ofMentionsOnlyBelow` from the
`mentionsOnlyBelow` certificate), `permutationDiagram_injective` extracts the permutation equality, and the shipped
comb straightening `crossingWords_equalPerm_conv` finishes.  Zero-axiom, structural. -/
theorem crossingCompleteness_inRange (generatorCount : Nat) (word1 word2 : List Nat)
    (hRange1 : mentionsOnlyBelow generatorCount word1 = true)
    (hRange2 : mentionsOnlyBelow generatorCount word2 = true)
    (diagramEq : brauerDiagramOf (generatorCount + 1) (crossingWord word1)
      = brauerDiagramOf (generatorCount + 1) (crossingWord word2)) :
    BrauerConvFree7 (crossingWord word1) (crossingWord word2) := by
  have read1 := brauerCrossingOnlyReadbackInRange_proof (generatorCount + 1) word1
    (crossingWordInRange_ofMentionsOnlyBelow generatorCount word1 hRange1)
  have read2 := brauerCrossingOnlyReadbackInRange_proof (generatorCount + 1) word2
    (crossingWordInRange_ofMentionsOnlyBelow generatorCount word2 hRange2)
  have permDiagEq :
      permutationDiagram (generatorCount + 1) (permuteOfCrossingWord (generatorCount + 1) word1)
        = permutationDiagram (generatorCount + 1) (permuteOfCrossingWord (generatorCount + 1) word2) := by
    rw [← read1, ← read2]; exact diagramEq
  have permEq : permuteOfCrossingWord (generatorCount + 1) word1
      = permuteOfCrossingWord (generatorCount + 1) word2 :=
    permutationDiagram_injective (generatorCount + 1) _ _
      (permuteOfCrossingWord_length (generatorCount + 1) word1)
      (permuteOfCrossingWord_length (generatorCount + 1) word2) permDiagEq
  exact crossingWords_equalPerm_conv generatorCount word1 word2 hRange1 hRange2 permEq

/-- The two decision verdicts on the shipped diagram-gated `decidableBrauerConv`, re-surfaced together: a REAL
`isTrue` pair (`stabilizerPair_conv`, related by a nontrivial foot-swap chain) and a REAL `isFalse` pair
(`loopSeparation_notConv`, separated by loop count).  Both directions of the decision fire. -/
theorem crossingCompleteness_bothVerdicts :
    (BrauerConv 1 [cupAt 0, crossingAt 1] [cupAt 1, crossingAt 0])
      ∧ ¬ BrauerConv 0 [cupAt 0, capAt 0] [] :=
  ⟨stabilizerPair_conv, loopSeparation_notConv⟩

/-! ## Honesty markers -/

/-- ★ **Honesty marker — crossing-only Brauer completeness is UNCONDITIONAL (T2 discharged).**
`crossingCompleteness_inRange` reduces equal-diagram crossing words to `BrauerConvFree7` with NO readback hypothesis,
because the readback `brauerCrossingOnlyReadbackInRange` is PROVEN zero-axiom.  This is the crossing block of the
standard-form driver (passes 1 / 4 / 5-crossing), all closed.  `= true`. -/
def fxBrauer_hasCrossingOnlyCompletenessUnconditional : Bool := true

/-- ★ **Honesty WALL marker — the FULL V2 free word problem stays OPEN after r2 (pass-5-arc).**
`crossingCompleteness_inRange` closes the crossing block, but `brauerWords_equalMatching_conv` (equal `brauerDiagramOf`
⟹ `BrauerConvFree8`) is NOT proven: it CAPS on pass-5-arc — the cup/cap arc-selection driver-fold — at the
interleaved-arc configuration `i < k < j < l` (a cup forced past a cap; the windowPin selection is inversion-FROZEN
across the commute).  A route/measure gap, not an obstruction to truth (Graham–Lehrer, Invent. math. 123 (1996)).
So `fxBrauer_hasBrauerCompleteness` stays `false` and #2013 does NOT close this round.  `= false`. -/
def fxBrauer_hasBrauerV2FullCompleteness : Bool := false

end FX1Poly.Polygraph
