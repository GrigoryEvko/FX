import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescExtractorFold

/-! # BRAUER-MIDDLE r2 B4 — THE LEDGER: the machine-checked terminal state + the NAMED r3 residual nodes

This is the honest terminal ledger for the BRAUER-MIDDLE r2 round (#2013).  The round SHIPPED, zero-axiom:

  * **B1 — the general arc EXTRACTOR + the 5-block-plus-loops datatype** (`fxBrauer_hasExt5ArcExtractor = true`).
    `BrauerStandardFormExt5` carries the ∗-dual `bottomPerm` block and the `loops` field the r1 4-block loopless
    datatype lacked; `reconstructStandardFormExt5` reconstructs crossing caps, crossing cups (the STRADDLE now reads
    back `some`, where r1 returned `none`), and loops — the adversarial-B instance (a crossing cap + crossing cup +
    loop AT ONCE) reads back `some` and its form realizes it.  Guarded, hence SOUND unconditionally.
  * **B2 — the `straddleCount` PRIMARY lex descent** (`fxBrauer_hasStraddleLexDescent = true`).  The offset-reading
    straddle count strictly DESCENDS on the EXACT adjacent-straddle move r1's list-order `arcMeasure` provably
    ASCENDED on (`straddle_resists_arcMeasure`), and is held by the three distant cup-sink moves; the lex embedding
    descends on ALL FOUR shipped cup-sink moves — the per-move descent obstruction is CLOSED.
  * **B3 — the whisker-free FOLD reduction** (`fxBrauer_hasExt5FoldReduction = true`).  The canonical extractor makes
    equal diagrams give literally equal extended forms, so the fold `BrauerExt5FoldReaches` reduces (via the free
    symm/trans glue, whisker-free) to full V2 completeness `brauerWords_equalMatching_conv_ofFold` — the assembly
    around the fold is DONE.

The round did NOT close #2013: the fold `BrauerExt5FoldReaches` is not discharged, so
`fxBrauer_hasBrauerV2FullCompleteness` / `fxBrauer_hasBrauerCompleteness` STAY `false`.  Per the 110-percent directive
a wall gets a NAMED node for the next round (not a permanent statement) — every residual below is a ROUTE / measure /
totality gap, NEVER a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6 guarantees the presentation is complete).

## The three named r3 residual nodes (the next round's to-do list, machine-checked `false`)

  * **R3-A — the TOTAL extractor + its general roundtrip** (`fxBrauer_hasExt5TotalExtractorRoundtrip`): make
    `reconstructStandardFormExt5` total (it currently returns `none` on some nested multi-crossing cups) and prove
    `standardFormDiagramExt5 (reconstructStandardFormExt5 d) = d` for ALL well-formed `d` — a `stepWiring`-connectivity
    structural induction, the same long pole as the still-open `fxBrauer_hasCrossingOnlyReadback`.
  * **R3-B — the GLOBAL descent fuel** (`fxBrauer_hasStraddleGlobalFuelNode`): compose B2's per-move lex table
    `(straddleCount, arcMeasure)` into ONE well-founded `Nat`-fuel monovariant over ARBITRARY interleavings (the
    distant-slide-re-exposes-a-straddle case), the fuel the sort driver consumes.
  * **R3-C — the whisker-free sort DRIVER** (`fxBrauer_hasWhiskerFreeSortDriver`): assemble the shipped cup-sink /
    cap-sink move set, directed by the R3-B fuel and cutting cups from caps via the R3-A extractor, into the fold
    `BrauerExt5FoldReaches` — kept whisker-free (the whisker derivation `fxBrauer_hasFreeBrauerStraighteningNF` is a
    COROLLARY of this fold, NOT a separate prerequisite; building it standalone is the circularity trap).

Discharging R3-A + R3-B + R3-C jointly discharges `BrauerExt5FoldReaches`, which via
`brauerWords_equalMatching_conv_ofFold` flips `fxBrauer_hasBrauerV2FullCompleteness` and closes #2013.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The named r3 residual nodes -/

/-- **r3 node R3-A — the total extractor + its general roundtrip is NOT built.**  `reconstructStandardFormExt5` is
guard-sound and reads back the crossing-cap / straddle / single-crossing-cup / loop / planar / crossing-only classes,
but returns `none` on some nested multi-crossing cups; proving the general roundtrip
`standardFormDiagramExt5 (reconstructStandardFormExt5 d) = d` (the totality) is the `fxBrauer_hasCrossingOnlyReadback`
structural-induction long pole.  `= false`. -/
def fxBrauer_hasExt5TotalExtractorRoundtrip : Bool := false

/-- **r3 node R3-B — the global descent fuel is NOT built.**  B2's `(straddleCount, arcMeasure)` lex table descends
per shipped cup-sink move in isolation, but is not composed into ONE well-founded `Nat`-fuel over arbitrary
interleavings (a distant cup-past-crossing slide can re-expose a straddle window downstream).  `= false`. -/
def fxBrauer_hasStraddleGlobalFuelNode : Bool := false

/-- **r3 node R3-C — the whisker-free sort DRIVER is NOT built.**  The shipped cup-sink / cap-sink move set, directed
by the R3-B fuel and cutting cups from caps via the R3-A extractor, is not assembled into the fold
`BrauerExt5FoldReaches`; the whisker derivation `fxBrauer_hasFreeBrauerStraighteningNF` is a COROLLARY of this fold,
never a prerequisite (the circularity trap).  `= false`. -/
def fxBrauer_hasWhiskerFreeSortDriver : Bool := false

/-! ## The grand r2 ledger — one machine-checked terminal state -/

/-- ★★★ **The BRAUER-MIDDLE r2 GRAND LEDGER — MACHINE-CHECKED.**  Every B1 / B2 / B3 shipped marker is `true`, and
every wall — the r3 residual nodes R3-A / R3-B / R3-C, the fold-discharged flag, and the master V2 / connectivity /
free-straightening completeness flags — is `false`.  A `rfl`-conjunction the kernel checks over the shipped markers:
the round shipped the extractor + descent + whisker-free reduction, but the fold is not discharged, so #2013 does NOT
close and no master flip is fabricated. -/
theorem fxBrauer_r2GrandLedger :
    (fxBrauer_hasExt5ArcExtractor = true
      ∧ fxBrauer_hasStraddleLexDescent = true
      ∧ fxBrauer_hasExt5FoldReduction = true)
    ∧ (fxBrauer_hasExt5TotalExtractorRoundtrip = false
      ∧ fxBrauer_hasStraddleGlobalFuelNode = false
      ∧ fxBrauer_hasWhiskerFreeSortDriver = false)
    ∧ (fxBrauer_hasExt5FoldDischarged = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

/-! ## The terminal honesty marker -/

/-- ★★ **Honesty marker — BRAUER-MIDDLE r2 did NOT close #2013 (the honest wall, with named r3 nodes).**  The round
shipped the general arc extractor (B1), the `straddleCount` primary lex descent (B2), and the whisker-free fold
reduction (B3), each zero-axiom — a genuine advance over r1 (the straddle and the adversarial-B crossing-cap/cup/loop
instances now read back `some`; the exact move r1's measure ascended on now descends).  But the FOLD
`BrauerExt5FoldReaches` is not discharged, so the masters stay `false` and #2013 does not close.  The exact wall is
the conjunction R3-A (total extractor + roundtrip) ∧ R3-B (global fuel) ∧ R3-C (whisker-free driver), each a named r3
node above — every one a ROUTE / measure / totality gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).
`= false`. -/
def fxBrauer_hasBrauerMiddleR2Complete : Bool := false

end FX1Poly.Polygraph
