import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcMiddle
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingComplete
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupSlide

/-! # BRAUER-MIDDLE r1 B2/B3/B4 — the conv-to-standard-form partial fold + the honest terminal ledger (#2013)

B1 (`Brauer/WiringDescArcMiddle.lean`) shipped the FULL-MIDDLE readback: the `topPerm`-extended standard form
`BrauerStandardFormExt`, WALL-2 fixed (the pure-crossing diagram reads back with the correctly-inverted middle), and
WALL-1 breached at the datatype (the straddle's extended standard form provably EXISTS).  This file lands the honest
B2/B3/B4:

  * **B2 — the conv-to-standard-form partial fold (the two blocks that CLOSE, machine-checked).**  A crossing-only
    word `BrauerConvFree7`-conv-reaches its EXTENDED standard form with the canonical `recComb` middle
    (`pureCrossingWord_convReaches_standardFormExt`, re-homing the shipped `recCombConv` onto `standardFormWordExt`),
    and the straddle word `BrauerConvFree8`-conv-reaches its `topPerm`-extended standard form via a SINGLE shipped
    `cupSlide` (`straddleWord_convReaches_standardFormExt`) — exactly the recon's hand-checked straddle chain
    `[cupAt 0, crossingAt 1] ↝ [cupAt 1, crossingAt 0] = standardFormWordExt { cupBlock := [1], topPerm := [0] }`.
    So both the `S_n` middle block and the exhibited `topPerm` straddle reach their extended standard forms by the
    shipped presentation moves — the extended standard form is CONV-REACHABLE, not merely existent.

  * **B3 — the decision, honestly scoped.**  The CROSSING-only V2 word problem is DECIDED unconditionally
    (`crossingCompleteness_inRange`, `fxBrauer_hasCrossingOnlyCompletenessUnconditional = true`): equal diagram ⟹
    `BrauerConvFree7`-convertible.  The FULL V2 word problem `brauerWords_equalMatching_conv` (equal `brauerDiagramOf`
    ⟹ `BrauerConvFree8` for ALL words) is NOT decided — no master flip.

  * **B4 — the honest terminal wall.**  `fxBrauer_hasBrauerV2FullCompleteness` and `fxBrauer_hasBrauerCompleteness`
    STAY `false`.  #2013 does NOT close.  The exact resisting combinatorics is named below.

## The exact resisting combinatorics (B4 — the r2 arc cap)

The general four-phase fold (caps sink · middle straighten · cups sink · `cupSlide`-directed `topPerm` accumulation)
that would carry an ARBITRARY word to its full extended standard form is NOT built.  Three residuals, each a ROUTE
gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6 guarantees the presentation is complete, so the target is TRUE):

  1. **The general crossing-cup ARC EXTRACTOR** (`fxBrauer_hasCrossingCupArcExtractor = false`): reconstructing a
     non-empty `cupBlock` + `topPerm` AUTOMATICALLY from a matching with a CROSSING cup (the top TL+`S_m`
     decomposition).  The straddle's extended form is EXHIBITED and CONV-REACHED here, but its automatic
     reconstruction from the bare matching is unbuilt.
  2. **The `cupSlide`-directed accumulation MEASURE.**  The r1 list-order `arcMeasure` PROVABLY ASCENDS on the
     straddle `cupSlide` (`straddle_resists_arcMeasure`, a THEOREM), so the fold that DIRECTS `cupSlide` (accumulating
     into `topPerm`) needs its own top-crossing descent — the arc-level analog of the Matsumoto distinguished-active
     -letter descent — which no shipped `Nat`-fuel monovariant supplies.
  3. **The non-circular whisker derivation** (`fxBrauer_hasFreeBrauerStraighteningNF = false`): deriving the
     connectivity-view `whisker` congruence move (which makes `BrauerConv` already decidable, `decidableBrauerConv`)
     from the generating relations WITHOUT re-invoking `whisker` — the standing honesty trap the fold must avoid.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## B2 — the conv-to-standard-form partial fold -/

/-- `word ++ [] = word` — cons-only structural copy (Init's `List.append_nil` leaks `propext`). -/
private theorem appendNilArcMiddle : (word : List BrauerAtom) → word ++ [] = word
  | [] => rfl
  | head :: rest => congrArg (head :: ·) (appendNilArcMiddle rest)

/-- ★ **A crossing-only extended standard form realizes exactly its middle crossing word.**  The cap / cup / topPerm
blocks are empty, so `standardFormWordExt { middle := m, … } = crossingWord m` — the two trailing empty blocks
stripped by the cons-only append-nil. -/
theorem standardFormWordExt_crossingOnly (bottomCount : Nat) (middleWord : List Nat) :
    standardFormWordExt { bottomCount := bottomCount, capBlock := [], middle := middleWord, cupBlock := [], topPerm := [] }
      = crossingWord middleWord := by
  show crossingWord middleWord ++ [] ++ [] = crossingWord middleWord
  rw [appendNilArcMiddle (crossingWord middleWord ++ []), appendNilArcMiddle (crossingWord middleWord)]

/-- ★★ **B2 — the crossing block conv-reaches its EXTENDED standard form.**  A crossing-only word over generators
`< generatorCount` is `BrauerConvFree7`-convertible to the extended standard form carrying the canonical `recComb`
middle staircase (empty cap / cup / `topPerm`).  This re-homes the shipped `recCombConv` (the Coxeter–Moser staircase
convertibility) onto `standardFormWordExt` — the `S_n` middle block of the fold, machine-checked. -/
theorem pureCrossingWord_convReaches_standardFormExt (generatorCount : Nat) (word : List Nat)
    (inRange : mentionsOnlyBelow generatorCount word = true) :
    BrauerConvFree7 (crossingWord word)
      (standardFormWordExt { bottomCount := generatorCount + 1, capBlock := [], middle := recComb generatorCount word, cupBlock := [], topPerm := [] }) := by
  rw [standardFormWordExt_crossingOnly]
  exact recCombConv generatorCount word inRange

/-- ★★ **B2 — the straddle conv-reaches its `topPerm`-extended standard form (the recon's hand-checked chain).**  The
straddle word `[cupAt 0, crossingAt 1]` is `BrauerConvFree8`-convertible to its extended standard form
`{ cupBlock := [1], topPerm := [0] }` (realized word `[cupAt 1, crossingAt 0]`) by a SINGLE shipped `cupSlide` at
offset `0` (`brauerConvFree8_cupSlide_derivable`).  This is exactly the recon's straddle chain: the crossing-cup
diagram's `topPerm`-extended standard form is CONV-REACHABLE by the presentation, closing the datatype-existence
(`straddleExt_realizes`, B1) into a genuine convertibility. -/
theorem straddleWord_convReaches_standardFormExt :
    BrauerConvFree8 [cupAt 0, crossingAt 1]
      (standardFormWordExt { bottomCount := 1, capBlock := [], middle := [], cupBlock := [1], topPerm := [0] }) := by
  show BrauerConvFree8 [cupAt 0, crossingAt 1] [cupAt 1, crossingAt 0]
  exact brauerConvFree8_cupSlide_derivable

/-- Non-vacuity — the crossing-block conv-reach fires on the r9 jam word `[2, 0, 1, 2]`: it `BrauerConvFree7`-reaches
the extended standard form carrying its staircase `[0, 1, 2, 1]`. -/
theorem pureCrossingWord_convReaches_standardFormExt_r9 :
    BrauerConvFree7 (crossingWord [2, 0, 1, 2])
      (standardFormWordExt { bottomCount := 4, capBlock := [], middle := recComb 3 [2, 0, 1, 2], cupBlock := [], topPerm := [] }) :=
  pureCrossingWord_convReaches_standardFormExt 3 [2, 0, 1, 2] (by decide)

/-! ## B3 / B4 — the honest terminal state, machine-checked -/

/-- ★★ **The BRAUER-MIDDLE r1 terminal state — MACHINE-CHECKED.**  B1's full-middle readback ships
(`fxBrauer_hasFullMiddleReadback = true`), the crossing-only V2 word problem is decided
(`fxBrauer_hasCrossingOnlyCompletenessUnconditional = true`), and the conv-to-standard-form partial fold ships (this
file) — while the general crossing-cup arc extractor, the full V2 word problem, and master completeness stay `false`.
No master flip is fabricated; #2013 does not close.  A `rfl`-conjunction the kernel checks over the shipped markers. -/
theorem fxBrauer_arcMiddleTerminalState :
    fxBrauer_hasFullMiddleReadback = true
      ∧ fxBrauer_hasCrossingOnlyCompletenessUnconditional = true
      ∧ fxBrauer_hasCrossingCupArcExtractor = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the conv-to-standard-form PARTIAL FOLD is SHIPPED (B2).**  The two blocks that close reach
their EXTENDED standard forms by the shipped presentation moves: the `S_n` crossing block via `recCombConv`
(`pureCrossingWord_convReaches_standardFormExt`, non-vacuous on the r9 jam word) and the `topPerm` straddle via a
single `cupSlide` (`straddleWord_convReaches_standardFormExt`, the recon's hand-checked chain).  So the
`topPerm`-extended standard form is CONV-REACHABLE, upgrading B1's datatype-existence to convertibility.  This is NOT
the general four-phase fold over arbitrary words (that needs the crossing-cup arc extractor + the `cupSlide`-directed
descent measure).  `= true`. -/
def fxBrauer_hasStandardFormConvReach : Bool := true

/-- ★★ **Honesty WALL marker — the general four-phase FOLD + the full V2 DECISION are NOT built (B3/B4, the r2 arc
cap).**  Carrying an ARBITRARY word to its full extended standard form (caps sink · middle straighten · cups sink ·
`cupSlide`-directed `topPerm` accumulation) is unbuilt: it needs (1) the general crossing-cup arc extractor
(`fxBrauer_hasCrossingCupArcExtractor = false`), (2) a `cupSlide`-directed top-crossing descent measure (the r1
`arcMeasure` PROVABLY ascends on the straddle, `straddle_resists_arcMeasure`), and (3) the non-circular whisker
derivation (`fxBrauer_hasFreeBrauerStraighteningNF = false`).  Hence `brauerWords_equalMatching_conv` is NOT proven,
`fxBrauer_hasBrauerV2FullCompleteness` and `fxBrauer_hasBrauerCompleteness` STAY `false`, and #2013 does NOT close.
Every residual is a ROUTE gap, not a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6 guarantees completeness).
`= false`. -/
def fxBrauer_hasBrauerMiddleFullFold : Bool := false

end FX1Poly.Polygraph
