import FX1Poly.Polygraph.TwoCategory.WalkingString.StringTwoSubProducerBeam
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWidthZeroPureCupSort

/-! # WalkingString/StringOneSubProducerBeam — the beam re-wired from TWO colour-keyed sub-producers to ONE
(FC-3 r39, the width-`0` wall discharged by wiring the shipped r17 proof)

`StringTwoSubProducerBeam` (r38) wired the whole adjoint-triple #2020 decision to fire from the TWO remaining
colour-keyed sub-producers `StringWidthZeroPureCupDeterminacyShared` and `StringCellValleyTraceEquivPositive` (the
mid-zero sub-producer having been discharged hypothesis-free).  But the FIRST of those two is NOT open: it was
INHABITED at r17 by `stringWidthZeroPureCupDeterminacyShared_proof` (`StringWidthZeroPureCupSort`, zero-axiom, via the
fueled partner-locate + word-threaded sort).  The r38 beam carried it only as a hypothesis because no beam file
imported `StringWidthZeroPureCupSort`.  This file closes that gap: it imports the r17 proof and threads it into the
two-sub-producer beam, collapsing the beam and the #2020 decision to fire from a SINGLE remaining colour-keyed
sub-producer — `StringCellValleyTraceEquivPositive`, the doubly-positive colour-aware SORT.

  * ★ `stringMatchingReductsShareSpineTrace_ofOneSubProducer` — the completeness reduct-existence residual from the
    single remaining sub-producer, feeding the shipped r17 proof `stringWidthZeroPureCupDeterminacyShared_proof` into
    the r38 two-sub-producer beam `stringMatchingReductsShareSpineTrace_ofTwoSubProducers`.
  * ★ `stringConvOfMapEq_ofOneSubProducer` — the base completeness `matchingOf cellA = matchingOf cellB →
    cellA ≈ cellB` from the single remaining sub-producer.
  * ★★ `decidableStringSaturatedConv_ofOneSubProducer` — the FULL adjoint-triple word-problem DECISION on every
    parallel pair, gated on only the single remaining colour-keyed SORT brick (the `isFalse` leg still residual-free
    via r2 soundness).

## No flip (honest)

The single remaining sub-producer `StringCellValleyTraceEquivPositive` (the doubly-positive colour-aware SORT — its
`pureCupSpine_sort` / `pureCapSpine_sort` core reads atom species off the boundary labels, not lengths) is the
un-ported length-rigidity wall, NOT inhabited this round.  So the beam is still gated (on ONE instead of two),
`StringCellValleyTraceEquiv` is not inhabited, and the masters `fxString_hasAdjointTripleCompleteness`
(`StringMatchingCompleteness`) and `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) STAY `false`.  This file
records — as a theorem — that the standing residual is now exactly ONE colour-keyed brick (down from two): the
width-`0` wall was never open math, only unwired.

Raw Lean 4 + Init; each theorem is a one-composition of the shipped r38 two-sub-producer assembly with the r17
width-`0` proof.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The beam from the single remaining sub-producer (width-`0` wired from the r17 proof) -/

/-- ★ **The completeness beam from the ONE remaining colour-keyed sub-producer.**  Feed the shipped r17 proof
`stringWidthZeroPureCupDeterminacyShared_proof` into the r38 two-sub-producer beam, so
`StringMatchingReductsShareSpineTrace` — the reduct-existence completeness residual — follows from only
`StringCellValleyTraceEquivPositive`.  The residual-drop from two bricks to one, made a theorem. -/
theorem stringMatchingReductsShareSpineTrace_ofOneSubProducer
    (positive : StringCellValleyTraceEquivPositive) : StringMatchingReductsShareSpineTrace :=
  stringMatchingReductsShareSpineTrace_ofTwoSubProducers
    stringWidthZeroPureCupDeterminacyShared_proof positive

/-- ★ **The BASE completeness from the one remaining sub-producer** — `matchingOf cellA = matchingOf cellB →
cellA ≈ cellB`, routed through the one-sub-producer beam. -/
theorem stringConvOfMapEq_ofOneSubProducer
    (positive : StringCellValleyTraceEquivPositive)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (matchingsEqual : matchingOf cellA = matchingOf cellB) :
    StringSaturatedTwoCellConv cellA cellB :=
  stringConvOfMapEq_ofTwoSubProducers
    stringWidthZeroPureCupDeterminacyShared_proof positive cellA cellB matchingsEqual

/-- ★★ **The FULL adjoint-triple word-problem DECISION from the ONE remaining sub-producer.**  The #2020 decision
`Decidable (StringSaturatedTwoCellConv cellA cellB)` on EVERY parallel pair, gated on only the single colour-keyed
SORT brick `StringCellValleyTraceEquivPositive` (the mid-zero producer discharged, the width-`0` sort wired from the
r17 proof).  The `isFalse` leg is residual-free (rides only the UNCONDITIONAL r2 soundness); the `isTrue` leg is gated
on the one.  Routed through the shipped `decidableStringSaturatedConv_ofReducts` via the one-sub-producer beam. -/
def decidableStringSaturatedConv_ofOneSubProducer
    (positive : StringCellValleyTraceEquivPositive)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    Decidable (StringSaturatedTwoCellConv cellA cellB) :=
  decidableStringSaturatedConv_ofTwoSubProducers
    stringWidthZeroPureCupDeterminacyShared_proof positive cellA cellB

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the beam and the #2020 decision are re-wired to fire from exactly ONE colour-keyed
sub-producer (FC-3 r39).**  The width-`0` sub-producer `StringWidthZeroPureCupDeterminacyShared` was never open math:
`stringWidthZeroPureCupDeterminacyShared_proof` (`StringWidthZeroPureCupSort`) inhabited it at r17, zero-axiom.  Wiring
that proof into the r38 two-sub-producer beam gives the one-sub-producer beam
`stringMatchingReductsShareSpineTrace_ofOneSubProducer`, the base completeness `stringConvOfMapEq_ofOneSubProducer`,
and the full decision `decidableStringSaturatedConv_ofOneSubProducer` — zero-axiom, one composition each — from only
`StringCellValleyTraceEquivPositive`.  The standing residual is now exactly ONE named colour-keyed brick (down from
two), machine-checked.

  What this does NOT close (no gate flag flips): the single remaining sub-producer is the doubly-positive colour-aware
  SORT core (the length-rigidity wall, un-ported), so `StringCellValleyTraceEquiv` is not inhabited and
  `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) / `fxString_hasConvOfMapEqPortFlip`
  (`StringConvOfMapEqPort`) STAY `false`.  This round flips ONLY this NEW marker.  `= true`. -/
def fxString_hasOneSubProducerBeam : Bool := true

end FX1Poly.Polygraph
