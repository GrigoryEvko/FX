import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcExtractor
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStraddleDescent
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcMiddleLedger

/-! # BRAUER-MIDDLE r2 B3 — the FOLD + DECISION assembly, honestly scoped (the whisker-free reduction is
machine-checked CONDITIONALLY on the fold; the fold is the named jammed goal; masters STAY false)

B1 (`Brauer/WiringDescArcExtractor.lean`) ships the canonical general arc extractor
`reconstructStandardFormExt5 : DiagramType → BrauerStandardFormExt5` (reads back the crossing-cap / straddle /
loop classes; the adversarial-B instance reads back `some`).  B2 (`Brauer/WiringDescStraddleDescent.lean`) ships the
`straddleCount` primary coordinate that DESCENDS on the exact straddle move r1's `arcMeasure` ascended on.  This file
lands the honest B3: the ASSEMBLY that turns the extractor + descent into the `#2013` decision — and names the exact
piece that does not close.

## The recon's reduction, machine-checked as a CONDITIONAL

The `#2013` master target is `brauerWords_equalMatching_conv`: equal `brauerDiagramOf` diagram ⟹ `BrauerConvFree8`
convertible, for ALL words.  Because the extractor `reconstructStandardFormExt5` is ONE canonical function of the
diagram, equal diagrams give LITERALLY equal extended standard forms — so the decision needs only the FOLD

  `∀ bottomCount word, BrauerConvFree8 word (standardFormWordExt5 (reconstructStandardFormExt5
      (brauerDiagramOf bottomCount word)))`

(every word conv-reaches the extended standard form of its own diagram) plus the free symm/trans glue.  This file:

  * **`brauerConvFree8_common_target`** — the unconditional symm/trans GLUE: two words that both conv-reach a common
    target are convertible.  Non-vacuous via the shipped straddle move (`brauerConvFree8_common_target_nonVacuity`).
  * **`BrauerExt5FoldReaches`** — the FOLD as a named `Prop`: every word conv-reaches the extended standard form of
    its diagram.
  * ★ **`brauerWords_equalMatching_conv_ofFold`** — the whole reduction, machine-checked: GIVEN the fold, equal
    diagrams ⟹ `BrauerConvFree8`-convertible (the extracted forms are equal by `congrArg` on the canonical extractor,
    then the fold + glue closes it).  This threads ONLY the free `BrauerConvFree8` constructors — `symm`, `trans`,
    plus the fold's own moves — so it is WHISKER-FREE: it never invokes `BrauerConv.whisker` / `brauerConv_complete`
    (the recon's anti-circularity discipline).
  * **`fxBrauer_arcExtractorFoldTerminalState`** — the machine-checked master state: B1 / B2 markers `true`, the full
    V2 / connectivity completeness markers STAY `false`.  No master flip is fabricated; #2013 does NOT close.

## The exact jammed goal (B4 — the r3 residual)

`BrauerExt5FoldReaches` is NOT discharged.  Discharging it needs, jointly: (1) B1's extractor made TOTAL + its general
ROUNDTRIP `standardFormDiagramExt5 (reconstructStandardFormExt5 d) = d` (a `stepWiring`-connectivity structural
induction, the still-open `fxBrauer_hasCrossingOnlyReadback` long pole); (2) B2's per-move lex table composed into ONE
well-founded `Nat`-fuel over ARBITRARY interleavings (the global-fuel residual); (3) the sort DRIVER that applies the
shipped cup-sink / cap-sink move set directed by that fuel to carry any word to its extended standard form — kept
whisker-free.  Per the recon, the whisker derivation `fxBrauer_hasFreeBrauerStraighteningNF` is NOT a separate
prerequisite: it is a COROLLARY of this fold (the fold IS a proof that the free relations generate every
diagram-equality), so it must NOT be built standalone (that is the circularity trap).  `fxBrauer_hasBrauerV2FullCompleteness`
/ `fxBrauer_hasBrauerCompleteness` STAY `false`.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The symm/trans glue (unconditional) -/

/-- ★ **The common-target glue.**  Two words that each `BrauerConvFree8`-reach a common `target` are convertible to
each other, by `trans` with the `symm` of the second reach.  Threads only the free `symm` / `trans` constructors — no
`whisker`, no `brauerConv_complete`. -/
theorem brauerConvFree8_common_target (wordLeft wordRight target : List BrauerAtom)
    (leftReaches : BrauerConvFree8 wordLeft target) (rightReaches : BrauerConvFree8 wordRight target) :
    BrauerConvFree8 wordLeft wordRight :=
  BrauerConvFree8.trans leftReaches (BrauerConvFree8.symm rightReaches)

/-- Non-vacuity — the glue fires on the shipped straddle move: `[cupAt 0, crossingAt 1]` reaches `[cupAt 1,
crossingAt 0]` twice, gluing to a genuine (reflexive-shaped) convertibility built from two real presentation moves. -/
theorem brauerConvFree8_common_target_nonVacuity :
    BrauerConvFree8 [cupAt 0, crossingAt 1] [cupAt 0, crossingAt 1] :=
  brauerConvFree8_common_target [cupAt 0, crossingAt 1] [cupAt 0, crossingAt 1] [cupAt 1, crossingAt 0]
    straddle_isMove straddle_isMove

/-! ## The fold as a named Prop + the conditional completeness reduction -/

/-- ★ **The FOLD, named.**  Every word `BrauerConvFree8`-reaches the extended standard form of its own diagram — the
one hard ingredient the decision needs (the canonical extractor `reconstructStandardFormExt5` supplies the target;
this asserts the presentation moves reach it). -/
def BrauerExt5FoldReaches : Prop :=
  ∀ (bottomCount : Nat) (word : List BrauerAtom),
    BrauerConvFree8 word
      (standardFormWordExt5 (reconstructStandardFormExt5 (brauerDiagramOf bottomCount word)))

/-- ★★ **The whisker-free completeness reduction, machine-checked CONDITIONALLY on the fold.**  GIVEN the fold
`BrauerExt5FoldReaches`, two words with EQUAL `brauerDiagramOf` diagram are `BrauerConvFree8`-convertible: the
canonical extractor makes the extended standard forms LITERALLY equal (`congrArg` on `diagramEq`), so both words
conv-reach the SAME target and the free symm/trans glue closes it.  This is the recon's route, and it invokes ONLY
the free constructors + the fold — never `BrauerConv.whisker` / `brauerConv_complete` (whisker-free, per the
anti-circularity discipline).  Discharging `BrauerExt5FoldReaches` would flip
`fxBrauer_hasBrauerV2FullCompleteness`; it is the named r3 residual. -/
theorem brauerWords_equalMatching_conv_ofFold
    (foldReaches : BrauerExt5FoldReaches)
    (bottomCount : Nat) (wordLeft wordRight : List BrauerAtom)
    (diagramEq : brauerDiagramOf bottomCount wordLeft = brauerDiagramOf bottomCount wordRight) :
    BrauerConvFree8 wordLeft wordRight := by
  have reachLeft := foldReaches bottomCount wordLeft
  have reachRight := foldReaches bottomCount wordRight
  have formEq : standardFormWordExt5 (reconstructStandardFormExt5 (brauerDiagramOf bottomCount wordLeft))
      = standardFormWordExt5 (reconstructStandardFormExt5 (brauerDiagramOf bottomCount wordRight)) :=
    congrArg (fun diagram => standardFormWordExt5 (reconstructStandardFormExt5 diagram)) diagramEq
  rw [formEq] at reachLeft
  exact brauerConvFree8_common_target wordLeft wordRight
    (standardFormWordExt5 (reconstructStandardFormExt5 (brauerDiagramOf bottomCount wordRight)))
    reachLeft reachRight

/-- Non-vacuity — the conditional reduction fires: fed ANY fold witness and the reflexive diagram equality, it
produces a genuine `BrauerConvFree8 word word` (the degenerate but real instance, threading the fold + glue). -/
theorem brauerWords_equalMatching_conv_ofFold_nonVacuity
    (foldReaches : BrauerExt5FoldReaches) (bottomCount : Nat) (word : List BrauerAtom) :
    BrauerConvFree8 word word :=
  brauerWords_equalMatching_conv_ofFold foldReaches bottomCount word word rfl

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER-MIDDLE r2 terminal state — MACHINE-CHECKED.**  B1's general arc extractor ships
(`fxBrauer_hasExt5ArcExtractor = true`), B2's straddle-primary lex descent ships
(`fxBrauer_hasStraddleLexDescent = true`), and the crossing-only V2 word problem stays decided
(`fxBrauer_hasCrossingOnlyCompletenessUnconditional = true`) — while the extractor's totality, the global descent
fuel, the full V2 word problem, and master completeness stay `false`.  No master flip is fabricated; #2013 does not
close.  A `rfl`-conjunction the kernel checks over the shipped markers. -/
theorem fxBrauer_arcExtractorFoldTerminalState :
    fxBrauer_hasExt5ArcExtractor = true
      ∧ fxBrauer_hasStraddleLexDescent = true
      ∧ fxBrauer_hasCrossingOnlyCompletenessUnconditional = true
      ∧ fxBrauer_hasExt5TotalExtractor = false
      ∧ fxBrauer_hasStraddleGlobalFuel = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the whisker-free FOLD REDUCTION is SHIPPED (B3, conditional).**  The whole recon route is
machine-checked as a conditional: the unconditional symm/trans glue (`brauerConvFree8_common_target`, non-vacuous on
the straddle move) plus the canonical extractor turn the fold `BrauerExt5FoldReaches` into full V2 completeness
`brauerWords_equalMatching_conv_ofFold` — equal diagram ⟹ `BrauerConvFree8`, whisker-free (only `symm` / `trans` + the
fold's moves, never `BrauerConv.whisker`).  So the ONLY missing ingredient is the fold itself; the assembly around it
is DONE.  `= true`. -/
def fxBrauer_hasExt5FoldReduction : Bool := true

/-- **Honesty WALL marker — the FOLD `BrauerExt5FoldReaches` is NOT discharged, so #2013 does NOT close (B3/B4).**
Carrying an ARBITRARY word to the extended standard form of its diagram needs, jointly: (1) B1's extractor made TOTAL
+ its general roundtrip (`fxBrauer_hasExt5TotalExtractor = false`, the `fxBrauer_hasCrossingOnlyReadback` long pole);
(2) B2's per-move lex table composed into one well-founded fuel over arbitrary interleavings
(`fxBrauer_hasStraddleGlobalFuel = false`); (3) the whisker-free sort DRIVER applying the shipped move set directed by
that fuel.  The whisker derivation `fxBrauer_hasFreeBrauerStraighteningNF` is a COROLLARY of the fold, NOT a separate
prerequisite (do not build it standalone — the circularity trap).  Every residual is a ROUTE gap, not a truth gap
(Lehrer–Zhang arXiv:1207.5889 Thm 2.6 guarantees the presentation is complete).  Hence `brauerWords_equalMatching_conv`
is NOT proven unconditionally, and `fxBrauer_hasBrauerV2FullCompleteness` / `fxBrauer_hasBrauerCompleteness` STAY
`false`.  `= false`. -/
def fxBrauer_hasExt5FoldDischarged : Bool := false

end FX1Poly.Polygraph
