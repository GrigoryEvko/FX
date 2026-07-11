import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyDegenerateSplit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDescentStepOracleInhabited

/-! # WalkingString — THE ASSEMBLY: the adjoint-triple #2020 decision from the THREE colour-keyed sub-producers,
Piece I fully discharged

`StringValleyDegenerateSplit` SHARPENED the monolithic Piece-II residual `StringCellValleyTraceEquiv` into the three
named colour-keyed sub-producers `StringWidthZeroPureCupDeterminacyShared` (the FC-3 r12 shared-top strengthening),
`StringMidZeroValleyTraceEquiv`, `StringCellValleyTraceEquivPositive` (via
`stringCellValleyTraceEquiv_of_widthZero_of_midZero`, proving the colour-blind skeleton + the case-(a) reducer).
Piece I is ALREADY DONE — the per-step descent oracle is inhabited hypothesis-free (`stringDescentStepOracle`,
`StringDescentStepOracleInhabited`).

This file WIRES the two together into the final decision chain: given the three colour-keyed sub-producers, the
WHOLE adjoint-triple word-problem DECISION (#2020) fires, with everything else discharged.  The chain is

  `(three sub-producers) → StringCellValleyTraceEquiv → [Piece I oracle already fed]
    → StringMatchingReductsShareSpineTrace → decidableStringSaturatedConv`.

  * ★ `stringMatchingReductsShareSpineTrace_ofThreeSubProducers` — the monolithic residual from the three, threading
    the ported skeleton `stringCellValleyTraceEquiv_of_widthZero_of_midZero` into the Piece-I-discharged reduction
    `stringMatchingReductsShareSpineTrace_of_valleyTraceEquiv` (whose oracle argument is the inhabited
    `stringDescentStepOracle`).
  * ★ `stringConvOfMapEq_ofThreeSubProducers` — the BASE completeness `matchingOf cellA = matchingOf cellB →
    StringSaturatedTwoCellConv cellA cellB` from the three.
  * ★ `stringSaturatedMatchingCanonicalization_ofThreeSubProducers` — the two-field keystone (soundness r2 +
    completeness from the three).
  * ★★ `decidableStringSaturatedConv_ofThreeSubProducers` — the FULL adjoint-triple word-problem DECISION (#2020):
    `Decidable (StringSaturatedTwoCellConv cellA cellB)` on EVERY parallel pair, via the two-level `ColouredDiagramType`
    `DecidableEq`.  Its `isFalse` leg is residual-FREE (rides only the UNCONDITIONAL r2 soundness
    `stringSaturatedConv_colouredMatchingOf_eq_final`); its `isTrue` leg is gated on the three sub-producers.  So the
    decision genuinely runs BOTH verdicts on adjoint-triple 2-cells, gated modulo exactly the three colour-keyed
    bricks — Piece I and the colour-blind skeleton fully discharged.

## No flip (honest)

None of the three sub-producers is inhabited this round (each is the colour-keyed SORT + arc↔matching core the
length-rigidity failure forces).  So `StringCellValleyTraceEquiv` is NOT inhabited, and
`fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) STAYS `false`, honestly.  This file makes the
"three colour-keyed bricks ⟹ #2020 decides" chain machine-checked and explicit; it does NOT flip any completeness
gate.  The residual is now factored to exactly three named sub-producers, with Piece I, the block-split, the
case-(a) reducer, and the dispatching skeleton all discharged zero-axiom.

Raw Lean 4 + Init; each theorem is a one-composition of shipped lemmas.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The monolithic residual from the three sub-producers (Piece I already discharged) -/

/-- ★ **The monolithic completeness residual from the three colour-keyed sub-producers.**  Compose the ported
three-way split `stringCellValleyTraceEquiv_of_widthZero_of_midZero` (yielding `StringCellValleyTraceEquiv` from the
three) with the Piece-I-discharged reduction `stringMatchingReductsShareSpineTrace_of_valleyTraceEquiv` (whose oracle
argument is the inhabited `stringDescentStepOracle`).  So `StringMatchingReductsShareSpineTrace` follows from the
three sub-producers alone — every other input already discharged. -/
theorem stringMatchingReductsShareSpineTrace_ofThreeSubProducers
    (widthZero : StringWidthZeroPureCupDeterminacyShared) (midZero : StringMidZeroValleyTraceEquiv)
    (positive : StringCellValleyTraceEquivPositive) : StringMatchingReductsShareSpineTrace :=
  stringMatchingReductsShareSpineTrace_of_valleyTraceEquiv
    (stringCellValleyTraceEquiv_of_widthZero_of_midZero widthZero midZero positive)

/-! ## Completeness, keystone, and the #2020 decision from the three -/

/-- ★ **The BASE completeness from the three sub-producers** — `matchingOf cellA = matchingOf cellB → cellA ≈ cellB`,
routed through the shipped `stringConvOfMapEq_ofReductsShareSpineTrace`. -/
theorem stringConvOfMapEq_ofThreeSubProducers
    (widthZero : StringWidthZeroPureCupDeterminacyShared) (midZero : StringMidZeroValleyTraceEquiv)
    (positive : StringCellValleyTraceEquivPositive)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (matchingsEqual : matchingOf cellA = matchingOf cellB) :
    StringSaturatedTwoCellConv cellA cellB :=
  stringConvOfMapEq_ofReductsShareSpineTrace
    (stringMatchingReductsShareSpineTrace_ofThreeSubProducers widthZero midZero positive)
    cellA cellB matchingsEqual

/-- ★ **The whole keystone from the three sub-producers** — soundness (r2, unconditional) + completeness (from the
three), the two-field `StringSaturatedMatchingCanonicalization`. -/
def stringSaturatedMatchingCanonicalization_ofThreeSubProducers
    (widthZero : StringWidthZeroPureCupDeterminacyShared) (midZero : StringMidZeroValleyTraceEquiv)
    (positive : StringCellValleyTraceEquivPositive) : StringSaturatedMatchingCanonicalization :=
  stringSaturatedMatchingCanonicalization_ofReducts
    (stringMatchingReductsShareSpineTrace_ofThreeSubProducers widthZero midZero positive)

/-- ★★ **The FULL adjoint-triple word-problem DECISION (#2020) from the three sub-producers.**  Compare the two
cells' `ColouredDiagramType` by the derived `DecidableEq` (structural over `Nat` / `List Nat` / `WireLabel` — it
COMPUTES, no `propext`): equal ⟹ `isTrue` via the two-level completeness from the three; unequal ⟹ `isFalse`, since
the UNCONDITIONAL r2 soundness `stringSaturatedConv_colouredMatchingOf_eq_final` forces the coloured matchings equal.
The decision runs BOTH verdicts on adjoint-triple 2-cells; the `isFalse` leg is residual-FREE, the `isTrue` leg gated
on the three colour-keyed sub-producers — Piece I, the block-split, the case-(a) reducer, and the dispatching
skeleton all discharged.  Routed through the shipped `decidableStringSaturatedConv_ofReducts`. -/
def decidableStringSaturatedConv_ofThreeSubProducers
    (widthZero : StringWidthZeroPureCupDeterminacyShared) (midZero : StringMidZeroValleyTraceEquiv)
    (positive : StringCellValleyTraceEquivPositive)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    Decidable (StringSaturatedTwoCellConv cellA cellB) :=
  decidableStringSaturatedConv_ofReducts
    (stringMatchingReductsShareSpineTrace_ofThreeSubProducers widthZero midZero positive)
    cellA cellB

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the #2020 decision is wired to fire from exactly THREE colour-keyed sub-producers; Piece I and
the colour-blind skeleton are fully discharged.**  `stringMatchingReductsShareSpineTrace_ofThreeSubProducers`,
`stringConvOfMapEq_ofThreeSubProducers`, the keystone, and the full DECISION
`decidableStringSaturatedConv_ofThreeSubProducers` all follow — zero-axiom, one composition each — from the three
named sub-producers `StringWidthZeroPureCupDeterminacyShared` (the r12 shared-top strengthening),
`StringMidZeroValleyTraceEquiv`, `StringCellValleyTraceEquivPositive`.  Everything below Piece II is shipped: Piece I
(`stringDescentStepOracle`,
hypothesis-free), the block extractor + empty-source cap collapse + case-(a) reducer + dispatching skeleton
(`StringValleyDegenerateSplit`), and the completeness reduction + gated decision (`StringMatchingCompleteness`).
The decision genuinely runs both verdicts on adjoint-triple 2-cells (`isFalse` residual-free via r2 soundness,
`isTrue` gated on the three).

  What this marker does NOT close (no gate flag flips): the three sub-producers are the colour-keyed SORT +
  arc↔matching core (the adjunction discharges its analogs through length-rigid atom determination, FALSE at the
  string), un-inhabited this round.  So `StringCellValleyTraceEquiv` is not inhabited and
  `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) STAYS `false`, honestly — the residual now
  factored to exactly three named colour-keyed bricks with the entire scaffolding around them discharged.  `= true`. -/
def fxString_hasThreeSubProducerDecisionAssembly : Bool := true

end FX1Poly.Polygraph
