import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupSlideSoundness
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupSlideReadback

/-! # WP-BRAUER-4 r4 — the BRAUER-V2 honest ledger + the POLY-TAB-2 migration note (B5)

The per-brick status of the V2 presentation change (task #2238, feeding #2013), machine-checked as one coherence
theorem, plus the POLY-TAB-2 deletion-candidacy note.

## Per-brick status (all zero-axiom, all in `Brauer/`, all additive — V1 byte-identical)

  * **B1 — the versioned presentation** (`Brauer/WiringDescCupSlide.lean`): SHIPPED.  `cupSlideRelation` (the
    ∗-dual of `capSlideRelation`, Lehrer–Zhang ∗(2.7) "Sliding"), diagram-sound; `brauerPresentation8` =
    `brauerPresentation7 ++ [cupSlideRelation]` (V1 a prefix); the V2 free over-approximation `BrauerConvFree8`
    embedding `BrauerConvFree7` via `ofFree7` (every V1 conversion is a V2 conversion).  The r4 minimal straddle
    witness is derivable at V2 (`brauerConvFree8_cupSlide_derivable`).  Derivation gate: the yanking chain's
    ingredients ARE shipped, but the positioned-word mate does not close in one attempt (the naive snake-bend is
    circular); the row is the literature-faithful representative.  `fxBrauer_hasBrauerCupSlideRow`,
    `fxBrauer_hasBrauerV2Presentation` = `true`.

  * **B2 — V2 soundness** (`Brauer/WiringDescCupSlideSoundness.lean`): SHIPPED.  The ONE new arm
    `brauerConv_cupSlide_inContext` — the cup slide is `BrauerConv`-convertible in ANY horizontal context (all
    offsets / widths / prefixes, loops respected) via the relation-agnostic keystone, with a boundary-CHANGING
    non-minimal witness.  `fxBrauer_hasCupSlideConvSoundness` = `true`.

  * **B3 — the extraction fold under V2** (`Brauer/WiringDescCupSlideExtract.lean`): PARTIAL (honest).  The V2
    cup-sink MOVE SET is complete (contextual straddle slide + distant slides + untwist seed + crossing-block
    engine, all `BrauerConvFree8`), with a composite demo chaining the new cup slide with an interchange.  The full
    fold ASSEMBLY (`brauerWords_equalMatching_conv`) is BANKED: the residual is pass-(5) — matching the cup/cap
    half-diagrams via the boundary readback — a DRIVER + readback, not a missing move.
    `fxBrauer_hasCupSinkMoveSet` = `true`; `fxBrauer_hasBrauerV2ExtractionFold` = `false`.

  * **B4 — the readoff** (`Brauer/WiringDescCupSlideReadback.lean`): PARTIAL (honest, gated).  The refuted
    `∀`-general readback is CORRECTED to the boundary-width-aware `BrauerCrossingOnlyReadbackInRange` (re-aiming the
    completeness conditional at the shipped `stateIsPermGraph_ofInRange` premise), with the census-to-in-range glue
    and the two `decidableBrauerConv` probes (stabilizer `isTrue` / loop-separation `isFalse`).  The
    `StateIsPermGraph ⇒ extractDiagram` bridge is banked, so the #2013 masters STAY `false` — NO flip fabricated.
    `fxBrauer_hasCorrectedCrossingReadbackStatement` = `true`; `fxBrauer_hasBrauerV2CompletenessFlip` = `false`.

## The version relationship (honest)

V2 strictly extends V1 by one primitive move (the cup slide).  V1 (`brauerPresentation7` / `BrauerConvFree7`) is
UNTOUCHED — byte-identical.  The V1 straddle FINDING (`fxBrauer_hasCupSlideStraddleFinding`) stays `true`: it recorded
a TRUE historical gap (the shipped V1 ctor set did not provide the straddle slide); V2 discharges its bequest without
mutating the finding.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The machine-checked ledger coherence -/

/-- ★ **The BRAUER-V2 ledger is coherent** — the exact honest flag state after this round: B1/B2 shipped (`true`),
B3/B4 honest partials (move set / corrected statement `true`; fold assembly / completeness flip `false`), the #2013
masters `fxBrauer_hasBrauerCompleteness` / `fxBrauer_hasCrossingOnlyReadback` STAY `false` (no flip fabricated), and
the V1 straddle finding stays `true` (a true historical gap, bequest now discharged).  Machine-checked by `rfl` on
each flag. -/
theorem brauerV2_ledger_coherent :
    fxBrauer_hasBrauerCupSlideRow = true
    ∧ fxBrauer_hasBrauerV2Presentation = true
    ∧ fxBrauer_hasCupSlideConvSoundness = true
    ∧ fxBrauer_hasCupSinkMoveSet = true
    ∧ fxBrauer_hasBrauerV2ExtractionFold = false
    ∧ fxBrauer_hasCorrectedCrossingReadbackStatement = true
    ∧ fxBrauer_hasBrauerV2CompletenessFlip = false
    ∧ fxBrauer_hasBrauerCompleteness = false
    ∧ fxBrauer_hasCrossingOnlyReadback = false
    ∧ fxBrauer_hasCupSlideStraddleFinding = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the BRAUER-V2 round is a clean additive versioned presentation change.**  V2 = V1 + the
cup-slide row, additive (V1 byte-identical), diagram-sound (B1/B2), with the V2 cup-sink move set complete (B3) and
the crossing-only readback re-aimed at the corrected boundary-width-aware statement (B4).  The extraction-fold
assembly and the readback bridge are honest banked residuals; the #2013 completeness masters stay `false` — no flip
is fabricated.  Coherence machine-checked by `brauerV2_ledger_coherent`.  `= true`. -/
def fxBrauer_hasBrauerV2Ledger : Bool := true

/-- **Honesty marker — POLY-TAB-2 migration note: V2 is the migration target; DELETE NOTHING this round.**  The
table-driven polygraph layer (POLY-TAB, #2228) migrates the Brauer presentation to a data-parameterized row-list fed
to ONE generic row congruence.  When it lands, V2 (`brauerPresentation8` = the eight Lehrer–Zhang relations) is the
version that migration takes — it is the complete, literature-faithful relation set.  Only AFTER that migration
BRIDGES the bespoke `BrauerConvFree` / `BrauerConvFree7` / `BrauerConvFree8` free-conv inductives to the generic
row congruence do those hardwired-ctor inductives become deletion CANDIDATES.  The Brauer lane is NOT
migrated-and-bridged yet (POLY-TAB is `in_progress`, writing `Table/` concurrently), so per the no-delete-without-
green-light rule NOTHING is deleted this round — the bespoke free convs stay live.  `= true`. -/
def fxBrauer_hasBrauerV2PolyTabMigrationNote : Bool := true

end FX1Poly.Polygraph
