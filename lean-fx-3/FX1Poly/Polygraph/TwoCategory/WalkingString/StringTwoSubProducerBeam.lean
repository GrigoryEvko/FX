import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyDecisionAssembly
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMidZeroValleyCellReducer

/-! # WalkingString/StringTwoSubProducerBeam — the beam re-wired from THREE colour-keyed sub-producers to TWO
(FC-3 r38, the residual-drop made machine-checked)

`StringValleyDecisionAssembly` wired the whole adjoint-triple #2020 decision to fire from the THREE colour-keyed
sub-producers `StringWidthZeroPureCupDeterminacyShared`, `StringMidZeroValleyTraceEquiv`,
`StringCellValleyTraceEquivPositive`.  The r38 cell reducer (`StringMidZeroValleyCellReducer`) now INHABITS the
middle one hypothesis-free (`stringMidZeroValleyTraceEquiv_holds`).  This file threads that discharge into the
decision chain, re-wiring the beam `StringMatchingReductsShareSpineTrace` and the #2020 decision to fire from only
the TWO remaining colour-keyed sub-producers — the residual-drop from three bricks to two, made a machine-checked
theorem rather than a marker claim.

  * ★ `stringMatchingReductsShareSpineTrace_ofTwoSubProducers` — the beam (the completeness reduct-existence
    residual) from the two remaining sub-producers, threading the discharged `stringMidZeroValleyTraceEquiv_holds`
    into the shipped three-sub-producer assembly `stringMatchingReductsShareSpineTrace_ofThreeSubProducers`.
  * ★★ `decidableStringSaturatedConv_ofTwoSubProducers` — the FULL adjoint-triple word-problem DECISION gated on
    only the two remaining sub-producers (the `isFalse` leg still residual-free via r2 soundness; the `isTrue` leg
    gated on the two colour-keyed SORT bricks).

## No flip (honest)

The two remaining sub-producers `StringWidthZeroPureCupDeterminacyShared` (the width-`0` colour-aware SORT) and
`StringCellValleyTraceEquivPositive` (the doubly-positive colour-aware SORT) are the un-ported length-rigidity walls,
NOT inhabited this round.  So the beam is still gated (on TWO instead of three), `StringCellValleyTraceEquiv` is not
inhabited, and the masters `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) and
`fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) STAY `false`.  This file only records — as a theorem —
that the standing residual is now exactly TWO colour-keyed bricks.

Raw Lean 4 + Init; each theorem is a one-composition of the shipped three-sub-producer assembly with the discharged
mid-zero producer.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The beam from the two remaining sub-producers (mid-zero discharged) -/

/-- ★ **The completeness beam from the TWO remaining colour-keyed sub-producers.**  Thread the discharged
`stringMidZeroValleyTraceEquiv_holds` into the shipped three-sub-producer assembly
`stringMatchingReductsShareSpineTrace_ofThreeSubProducers`, so `StringMatchingReductsShareSpineTrace` — the
reduct-existence completeness residual — follows from only `StringWidthZeroPureCupDeterminacyShared` and
`StringCellValleyTraceEquivPositive`.  The residual-drop from three bricks to two, made a theorem. -/
theorem stringMatchingReductsShareSpineTrace_ofTwoSubProducers
    (widthZero : StringWidthZeroPureCupDeterminacyShared)
    (positive : StringCellValleyTraceEquivPositive) : StringMatchingReductsShareSpineTrace :=
  stringMatchingReductsShareSpineTrace_ofThreeSubProducers widthZero
    stringMidZeroValleyTraceEquiv_holds positive

/-- ★ **The BASE completeness from the two remaining sub-producers** — `matchingOf cellA = matchingOf cellB →
cellA ≈ cellB`, routed through the two-sub-producer beam. -/
theorem stringConvOfMapEq_ofTwoSubProducers
    (widthZero : StringWidthZeroPureCupDeterminacyShared)
    (positive : StringCellValleyTraceEquivPositive)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (matchingsEqual : matchingOf cellA = matchingOf cellB) :
    StringSaturatedTwoCellConv cellA cellB :=
  stringConvOfMapEq_ofReductsShareSpineTrace
    (stringMatchingReductsShareSpineTrace_ofTwoSubProducers widthZero positive)
    cellA cellB matchingsEqual

/-- ★★ **The FULL adjoint-triple word-problem DECISION from the TWO remaining sub-producers.**  The #2020 decision
`Decidable (StringSaturatedTwoCellConv cellA cellB)` on EVERY parallel pair, gated on only the two colour-keyed SORT
bricks (the mid-zero producer discharged).  The `isFalse` leg is residual-free (rides only the UNCONDITIONAL r2
soundness); the `isTrue` leg is gated on the two.  Routed through the shipped `decidableStringSaturatedConv_ofReducts`
via the two-sub-producer beam. -/
def decidableStringSaturatedConv_ofTwoSubProducers
    (widthZero : StringWidthZeroPureCupDeterminacyShared)
    (positive : StringCellValleyTraceEquivPositive)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    Decidable (StringSaturatedTwoCellConv cellA cellB) :=
  decidableStringSaturatedConv_ofReducts
    (stringMatchingReductsShareSpineTrace_ofTwoSubProducers widthZero positive)
    cellA cellB

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the beam and the #2020 decision are re-wired to fire from exactly TWO colour-keyed
sub-producers (FC-3 r38).**  With `StringMidZeroValleyTraceEquiv` discharged hypothesis-free by the r38 cell reducer
(`stringMidZeroValleyTraceEquiv_holds`, `StringMidZeroValleyCellReducer`), the beam
`stringMatchingReductsShareSpineTrace_ofTwoSubProducers`, the base completeness
`stringConvOfMapEq_ofTwoSubProducers`, and the full decision `decidableStringSaturatedConv_ofTwoSubProducers` all
follow — zero-axiom, one composition each — from only `StringWidthZeroPureCupDeterminacyShared` and
`StringCellValleyTraceEquivPositive`.  The standing residual is now exactly TWO named colour-keyed bricks (down from
three), machine-checked.

  What this does NOT close (no gate flag flips): the two remaining sub-producers are the width-`0` and
  doubly-positive colour-aware SORT cores (the length-rigidity walls, un-ported), so `StringCellValleyTraceEquiv` is
  not inhabited and `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) /
  `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) STAY `false`.  This round flips ONLY this NEW marker.
  `= true`. -/
def fxString_hasTwoSubProducerBeam : Bool := true

end FX1Poly.Polygraph
