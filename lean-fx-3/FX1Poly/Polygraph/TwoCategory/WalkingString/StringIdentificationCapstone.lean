import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingCompleteness
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidPureCupSort
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWidthZeroPureCupSort
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMidZeroValleyCellReducer
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidValleyCellReducer
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyDegenerateSplit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyDecisionAssembly

/-! # WalkingString — THE IDENTIFICATION CAPSTONE: the post-flip harvest, and the packaged #2209 identification

Post-flip (FC-3 r45), the two masters are TRUE per their LITERAL texts:
`fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`, `:= true`) and
`fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`, `:= true`).  The single named residual
`StringMatchingReductsShareSpineTrace` was DISCHARGED unconditionally by the inhabited valley brick
(`stringMatchingReductsShareSpineTrace_holds`), so completeness is unconditional and the adjoint-triple
word-problem decision is total.  This file is ADDITIVE: it CONSUMES the now-true masters and packages their
consequences.  It does NOT relabel the masters as more than their literal texts.

Every producer that was previously shipped only in gated `_of…` form is now a closed term, because all three
Piece-II valley sub-producers are inhabited unconditionally (`stringWidthZeroPureCupDeterminacyShared_proof`,
`stringMidZeroValleyTraceEquiv_holds`, `stringPositiveMidValleyTraceEquiv_holds` fed by the brick
`stringPositiveMidPureCupDeterminacy_proof`) and the per-step descent oracle is inhabited hypothesis-free
(`stringDescentStepOracle`).

## The harvest (each a one-composition of shipped terms)

  * ★ `stringConvOfColouredMapEq_holds` — the TWO-LEVEL / coloured base completeness, UNCONDITIONAL: equal
    `ColouredDiagramType` of a parallel pair forces saturated convertibility.  Colours are colour-blind — they
    project on the nose to base `matchingOf` and add nothing.
  * ★ `stringCellValleyTraceEquiv_holds` — the FULL Piece-II valley trace-equivalence `StringCellValleyTraceEquiv`,
    UNCONDITIONAL, assembled from the three colour-keyed sub-producers via the ported three-way split.
  * ★ `decidableStringSaturatedConv_viaThreeSubProducers` — a SECOND assembled derivation of the #2020 decision,
    routed through the valley three-sub-producer assembly (`decidableStringSaturatedConv_ofThreeSubProducers`)
    rather than the r45 brick short-route (`decidableStringSaturatedConv_holds`).  Honest scope: both derivations
    SHARE the valley brick `stringPositiveMidPureCupDeterminacy_proof` at their core — this is a second ASSEMBLY of
    the SAME decidable, not a proof-independent route.  No agreement equation is claimed here (an equation between
    two `Decidable` instances would need `Subsingleton (Decidable _)`, a separate theorem to be axiom-audited).

## The identification (the #2209 statement, named per the honest scope)

  * ★★ `stringSaturatedConv_iff_matchingOf_eq` — for every parallel pair of adjoint-triple 2-cells,
    `StringSaturatedTwoCellConv cellA cellB ↔ matchingOf cellA = matchingOf cellB`: saturated convertibility of
    2-cells of the walking adjoint triple `F ⊣ G ⊣ H` is IDENTIFIED with the boundary-matching combinatorial
    invariant, both directions machine-checked.  This is the packaged form of the shipped, inhabited keystone
    `StringSaturatedMatchingCanonicalization` (`stringSaturatedMatchingCanonicalization_holds`): the `⇒` direction
    is r2 SOUNDNESS (unconditional), the `⇐` direction is the now-unconditional COMPLETENESS.

  HONEST SCOPE — what the identification IS, and what it is NOT:
  - The shipped identification is the CANONICALIZATION BICONDITIONAL, reached via the brick / fueled-sort route.
    It is NOT the normalizer-route identification `matchingInjectiveOnNormalForms`
    (`fxString_hasReconstructionInhabited = false`, NOT inhabited); do not conflate the two.
  - This is the combinatorial-invariant identification (convertibility ↔ boundary matching).  The SEPARATE
    Fuss–Catalan COUNTING identification (`StringFussCatalan`, the `k = 2` two-colour discipline) is a distinct
    statement and is not restated here.
  - No squiggle↔string two-route identification is asserted: the squiggle side is off-lane and no in-lane term
    equates the two, so it is NOT part of this identification.

  PARITY NUANCE (documented wherever the determinacy is cited).  The valley determinacy brick
  `stringPositiveMidPureCupDeterminacy_proof` is width-generic (covers all `0 < midWidth`), but its anti-vacuity
  witness `stringPositiveMidBrick_firesOnDistinctDoubleCup` fires only at EVEN `midWidth = 2` (the distinct
  double-cup fixture).  At ODD midWidths the distinct-pair pure-cup fixture space is trivially empty, so
  non-vacuity is witnessed at even widths only, while the determinacy theorem itself covers every `0 < midWidth`.

Raw Lean 4 + Init; each term is a one-composition of shipped lemmas.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` in the
audit twin, plus an INDEPENDENT `#print axioms` witness. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## H1 — the two-level (coloured) base completeness, unconditional -/

/-- ★ **The TWO-LEVEL completeness, UNCONDITIONAL.**  Instantiates the gate
`stringConvOfColouredMapEq_ofReductsShareSpineTrace` at the now-discharged residual
`stringMatchingReductsShareSpineTrace_holds`: equal `ColouredDiagramType` of a parallel pair forces saturated
convertibility, colours projecting on the nose to base `matchingOf`. -/
theorem stringConvOfColouredMapEq_holds
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (colouredMatchingsEqual :
      colouredMatchingOf sourcePath targetPath cellA = colouredMatchingOf sourcePath targetPath cellB) :
    StringSaturatedTwoCellConv cellA cellB :=
  stringConvOfColouredMapEq_ofReductsShareSpineTrace stringMatchingReductsShareSpineTrace_holds
    cellA cellB colouredMatchingsEqual

/-! ## H2 — the full Piece-II valley trace-equivalence, unconditional -/

/-- ★ **The FULL Piece-II valley trace-equivalence, UNCONDITIONAL.**  Fires the ported three-way split
`stringCellValleyTraceEquiv_of_widthZero_of_midZero` on the three now-inhabited colour-keyed sub-producers: the
case-(a) width-zero determinacy, the mid-zero valley reducer, and the positive-mid valley reducer (fed by the brick
`stringPositiveMidPureCupDeterminacy_proof`).  See the header PARITY NUANCE for the brick's even-width anti-vacuity
witness. -/
theorem stringCellValleyTraceEquiv_holds : StringCellValleyTraceEquiv :=
  stringCellValleyTraceEquiv_of_widthZero_of_midZero
    stringWidthZeroPureCupDeterminacyShared_proof
    stringMidZeroValleyTraceEquiv_holds
    (stringPositiveMidValleyTraceEquiv_holds stringPositiveMidPureCupDeterminacy_proof)

/-! ## H3 — a second assembled derivation of the #2020 decision (shares the brick core) -/

/-- ★ **A SECOND assembled derivation of the #2020 decision.**  Routes the decision through the valley
three-sub-producer assembly `decidableStringSaturatedConv_ofThreeSubProducers` (the three inhabited sub-producers)
rather than the r45 brick short-route `decidableStringSaturatedConv_holds`.  Honest: both SHARE the valley brick
`stringPositiveMidPureCupDeterminacy_proof` — a second ASSEMBLY of the same decidable, no agreement equation
claimed (see header). -/
def decidableStringSaturatedConv_viaThreeSubProducers
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    Decidable (StringSaturatedTwoCellConv cellA cellB) :=
  decidableStringSaturatedConv_ofThreeSubProducers
    stringWidthZeroPureCupDeterminacyShared_proof
    stringMidZeroValleyTraceEquiv_holds
    (stringPositiveMidValleyTraceEquiv_holds stringPositiveMidPureCupDeterminacy_proof)
    cellA cellB

/-! ## H4 — the packaged identification biconditional (the #2209 statement) -/

/-- ★★ **THE IDENTIFICATION.**  Saturated convertibility of adjoint-triple 2-cells is IDENTIFIED with the
boundary-matching invariant: `StringSaturatedTwoCellConv cellA cellB ↔ matchingOf cellA = matchingOf cellB`.  The
packaged form of the shipped, inhabited keystone `stringSaturatedMatchingCanonicalization_holds` — `⇒` is r2
SOUNDNESS (unconditional), `⇐` is the now-unconditional COMPLETENESS.  Named per the CANONICALIZATION route (the
inhabited identification), NOT the normalizer route `matchingInjectiveOnNormalForms` (not inhabited).  See the
header HONEST SCOPE + PARITY NUANCE. -/
theorem stringSaturatedConv_iff_matchingOf_eq
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    StringSaturatedTwoCellConv cellA cellB ↔ matchingOf cellA = matchingOf cellB :=
  Iff.intro
    (fun conv => stringSaturatedMatchingCanonicalization_holds.mapEqOfConv conv)
    (fun matchingsEqual => stringSaturatedMatchingCanonicalization_holds.convOfMapEq matchingsEqual)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the post-flip harvest is packaged and the #2209 identification is stated.**  With the masters
TRUE per their literal texts and all Piece-II valley sub-producers inhabited, the coloured completeness, the full
valley trace-equivalence, and the identification biconditional
`stringSaturatedConv_iff_matchingOf_eq` (`StringSaturatedTwoCellConv ↔ matchingOf-equality`) are all closed terms; a
second valley-assembly derivation of the #2020 decision is also shipped.  Honest scope: the identification is the
CANONICALIZATION biconditional (NOT the non-inhabited normalizer route `matchingInjectiveOnNormalForms`, NOT the
separate Fuss–Catalan counting identification, NOT a squiggle↔string claim); the valley brick is width-generic with
even-width anti-vacuity only (PARITY NUANCE).  Zero-axiom. -/
def fxString_hasIdentificationCapstone : Bool := true

end FX1Poly.Polygraph
