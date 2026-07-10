import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescExtractorFold
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcExtractorRec
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStagedDescent

/-! # BRAUER-MIDDLE r3 B3 — R3-C: the whisker-free ASSEMBLY over the CORRECTED (total) extractor + the bounded driver

r2 B3 (`Brauer/WiringDescExtractorFold.lean`) shipped the whisker-free completeness reduction CONDITIONAL on the
fold, but over the r2 flat extractor `reconstructStandardFormExt5` — which returns `none` on nested cups, making the
fold's target UNSOUND on those diagrams (the recon's load-bearing caveat).  r3 B1 fixed the extractor: the
inversion-corrected `reconstructStandardFormExt5Corrected` is empirically total (every perfect matching up to
boundary size 8 reads back and REALIZES).  This file re-founds the whole assembly over the CORRECTED extractor, so
the fold's target is now SOUND on every diagram, and adds the bounded driver witness.

## What this file ships (each zero-axiom, structural)

  * **`BrauerExt5CorrectedFoldReaches`** — the FOLD over the CORRECTED extractor: every word `BrauerConvFree8`-reaches
    the extended standard form of its OWN diagram via `reconstructStandardFormExt5Corrected`.  Because the corrected
    extractor is (empirically) total AND correct, this target genuinely realizes the diagram — the r2 unsoundness
    caveat is removed.
  * ★★ **`brauerWords_equalMatching_conv_ofCorrectedFold`** — the whisker-free completeness reduction over the
    corrected extractor: GIVEN the corrected fold, two words with EQUAL diagram are `BrauerConvFree8`-convertible.
    The canonical extractor makes the forms LITERALLY equal (`congrArg`), so both words reach the SAME target and the
    shipped symm/trans glue `brauerConvFree8_common_target` closes it — threading ONLY the free constructors, never
    `BrauerConv.whisker` (the anti-circularity discipline).
  * ★ **`correctedFold_straddle_reaches`** — the BOUNDED driver witness: the straddle word `[cupAt 0, crossingAt 1]`
    (the exact move r1's `arcMeasure` resisted) `BrauerConvFree8`-reaches its OWN corrected extractor form via a
    SINGLE cup-slide move — the driver fires on the straddle class.
  * the machine-checked terminal state: the assembly is DONE over the corrected extractor; the masters stay `false`.

## The honest residual (B4)

`BrauerExt5CorrectedFoldReaches` is NOT discharged unconditionally.  Discharging it needs, jointly: R3-A's totality
roundtrip PROOF (the `stepWiring`-connectivity structural induction, the long pole — the TRUTH is now known, only
the proof walls), R3-B's INNER per-arc boundary-slot descent over `BrauerConvFree8` (the native chord-shift, the
OUTER arc-count fuel being already shipped), and the whisker-free driver threading the two-level fuel to carry an
ARBITRARY word to its corrected form.  Until then `fxBrauer_hasBrauerV2FullCompleteness` /
`fxBrauer_hasBrauerCompleteness` stay `false`; #2013 does not close.  Every residual is a route / measure / totality
gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The fold + the whisker-free reduction over the corrected extractor -/

/-- ★ **The FOLD over the CORRECTED extractor.**  Every word `BrauerConvFree8`-reaches the extended standard form of
its own diagram, via the inversion-corrected (total) extractor `reconstructStandardFormExt5Corrected`.  Because the
corrected extractor realizes the diagram on every class the flat one missed (the nested cups), this target is SOUND
where the r2 fold's was not. -/
def BrauerExt5CorrectedFoldReaches : Prop :=
  ∀ (bottomCount : Nat) (word : List BrauerAtom),
    BrauerConvFree8 word
      (standardFormWordExt5 (reconstructStandardFormExt5Corrected (brauerDiagramOf bottomCount word)))

/-- ★★ **The whisker-free completeness reduction over the corrected extractor, machine-checked CONDITIONALLY.**  GIVEN
the corrected fold, two words with EQUAL `brauerDiagramOf` diagram are `BrauerConvFree8`-convertible: the canonical
corrected extractor makes the extended forms LITERALLY equal (`congrArg` on the diagram equality), so both words
conv-reach the SAME target and the shipped symm/trans glue `brauerConvFree8_common_target` closes it.  Invokes ONLY
the free constructors + the fold — never `BrauerConv.whisker` (whisker-free).  Discharging
`BrauerExt5CorrectedFoldReaches` would flip `fxBrauer_hasBrauerV2FullCompleteness`. -/
theorem brauerWords_equalMatching_conv_ofCorrectedFold
    (foldReaches : BrauerExt5CorrectedFoldReaches)
    (bottomCount : Nat) (wordLeft wordRight : List BrauerAtom)
    (diagramEq : brauerDiagramOf bottomCount wordLeft = brauerDiagramOf bottomCount wordRight) :
    BrauerConvFree8 wordLeft wordRight := by
  have reachLeft := foldReaches bottomCount wordLeft
  have reachRight := foldReaches bottomCount wordRight
  have formEq :
      standardFormWordExt5 (reconstructStandardFormExt5Corrected (brauerDiagramOf bottomCount wordLeft))
      = standardFormWordExt5 (reconstructStandardFormExt5Corrected (brauerDiagramOf bottomCount wordRight)) :=
    congrArg (fun diagram => standardFormWordExt5 (reconstructStandardFormExt5Corrected diagram)) diagramEq
  rw [formEq] at reachLeft
  exact brauerConvFree8_common_target wordLeft wordRight
    (standardFormWordExt5 (reconstructStandardFormExt5Corrected (brauerDiagramOf bottomCount wordRight)))
    reachLeft reachRight

/-- Non-vacuity — the conditional reduction fires: fed ANY corrected-fold witness and the reflexive diagram
equality, it produces a genuine `BrauerConvFree8 word word`. -/
theorem brauerWords_equalMatching_conv_ofCorrectedFold_nonVacuity
    (foldReaches : BrauerExt5CorrectedFoldReaches) (bottomCount : Nat) (word : List BrauerAtom) :
    BrauerConvFree8 word word :=
  brauerWords_equalMatching_conv_ofCorrectedFold foldReaches bottomCount word word rfl

/-! ## The bounded driver witness — the straddle reaches its corrected form via one cup-slide -/

/-- ★ **The bounded driver fires on the straddle class.**  The straddle word `[cupAt 0, crossingAt 1]` — the exact
move r1's list-order `arcMeasure` provably RESISTED — `BrauerConvFree8`-reaches the extended standard form of its own
diagram (`{ cupBlock := [1], topPerm := [0] }`, realized word `[cupAt 1, crossingAt 0]`) via a SINGLE shipped
cup-slide move.  This is the fold `BrauerExt5CorrectedFoldReaches` instantiated and DISCHARGED on the straddle — the
driver's per-arc step, exhibited on the class that resisted the r1 measure. -/
theorem correctedFold_straddle_reaches :
    BrauerConvFree8 [cupAt 0, crossingAt 1]
      (standardFormWordExt5 (reconstructStandardFormExt5Corrected (brauerDiagramOf 1 [cupAt 0, crossingAt 1]))) := by
  have hword :
      standardFormWordExt5 (reconstructStandardFormExt5Corrected (brauerDiagramOf 1 [cupAt 0, crossingAt 1]))
      = [cupAt 1, crossingAt 0] := by decide
  rw [hword]
  exact brauerConvFree8_cupSlide_derivable

/-! ## The honest terminal state -/

/-- ★★ **The BRAUER-MIDDLE r3 B3 terminal state — MACHINE-CHECKED.**  The corrected extractor's nested readback ships
(`fxBrauer_hasExt5CorrectedNestedReadback = true`), the staged arc-count fuel ships
(`fxBrauer_hasStagedArcCountFuel = true`), and the corrected-extractor whisker-free reduction is assembled — while
the corrected roundtrip PROOF, the staged inner descent, the full V2 word problem, and master completeness stay
`false`.  No master flip is fabricated; #2013 does not close.  A `rfl`-conjunction the kernel checks. -/
theorem fxBrauer_correctedFoldTerminalState :
    fxBrauer_hasExt5CorrectedNestedReadback = true
      ∧ fxBrauer_hasStagedArcCountFuel = true
      ∧ fxBrauer_hasExt5FoldReduction = true
      ∧ fxBrauer_hasExt5CorrectedRoundtripProof = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the whisker-free ASSEMBLY is re-founded over the CORRECTED (total) extractor (B3).**  The
fold `BrauerExt5CorrectedFoldReaches` over the inversion-corrected extractor reduces (via the shipped symm/trans glue
`brauerConvFree8_common_target`, whisker-free) to full V2 completeness
`brauerWords_equalMatching_conv_ofCorrectedFold` — and because the corrected extractor is (empirically) total AND
realizes, the fold's target is SOUND on every diagram (the r2 unsoundness caveat on nested cups is removed).  The
bounded driver fires on the straddle class (`correctedFold_straddle_reaches`).  The assembly around the fold is DONE;
the ONLY missing ingredient is the unconditional fold.  `= true`. -/
def fxBrauer_hasCorrectedFoldReduction : Bool := true

/-- **Honesty WALL marker — the CORRECTED fold `BrauerExt5CorrectedFoldReaches` is NOT discharged (B3/B4).**  Carrying
an ARBITRARY word to its corrected extended standard form needs, jointly: R3-A's totality roundtrip PROOF (the
`stepWiring`-connectivity structural induction — the TRUTH is now known from the size-8 exhaustive check, only the
proof walls), R3-B's INNER per-arc boundary-slot descent over `BrauerConvFree8` (the OUTER arc-count fuel already
shipped), and the whisker-free driver threading the two-level fuel.  So
`brauerWords_equalMatching_conv` is NOT proven unconditionally, and `fxBrauer_hasBrauerV2FullCompleteness` /
`fxBrauer_hasBrauerCompleteness` STAY `false`; #2013 does not close.  `= false`. -/
def fxBrauer_hasCorrectedFoldDischarged : Bool := false

end FX1Poly.Polygraph
