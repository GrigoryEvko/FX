import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCupReconstruct
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCupTopTopSeed

/-! # WalkingString/StringValleyCupReconstructUngated — the UNCONDITIONAL cup-side `DiagramType.ext`, over the
walking ADJOINT-TRIPLE (`F ⊣ G ⊣ H`) signature (FC-3 r34, Piece-II cup assembly closed)

`stringCupRestrict_reconstructs` (`StringValleyCupReconstruct`) ships the cup-side reconstruction GATED on a single
case-3 hypothesis `stringCupTopTopPartner` (the top-top cup-arc partner agreement).  As of FC-3 r34 that gate is
DISCHARGED: `stringCupTopTopPartner` (`StringValleyCupTopTopSeed`) is the string port of the walking-adjunction
`cupTopTopPartner`, proved zero-axiom.  This file supplies the gate and lands the UNCONDITIONAL reconstruct:

  * ★ `stringCupRestrict_reconstructs_unconditional` — `matchingOf midWidth cupBlock =
    cupRestrict (matchingOf bc (capBlock ++ cupBlock))`, with the case-3 binder discharged by
    `stringCupTopTopPartner`, modulo only the genuine valley-shape inputs (`cupChained` / `wholeChained` /
    `midPositive`).

Unlike the gated reconstruct — whose ∀-`topOffset` case-3 hypothesis over a symbolic matching is not
`decide`-dischargeable — the unconditional reconstruct FIRES concretely on the genuine non-degenerate WIDE valley
`[ε] ++ [η']` at `bottomCount = 4` (mid-width `2`).  That firing
(`stringCupRestrict_reconstructs_unconditional_firesOnWideValley`) is the honest non-degenerate inhabitation the
gated theorem could never produce.

Raw Lean 4 + Init; no `omega` / `simp`-AC / `WellFounded.fix`.  Per-declaration `#assert_no_axioms` gated in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The unconditional cup-side reconstruction (case-3 gate discharged) -/

/-- ★ **The cup-side reconstruction (G-assembly) — UNCONDITIONAL.**  The cup block's OWN diagram is `cupRestrict`
of the whole valley's diagram: `matchingOf midWidth cupBlock = cupRestrict (matchingOf bc (capBlock ++ cupBlock))`,
where `midWidth = capState.openWires.length`.  Feeds the shipped gated `stringCupRestrict_reconstructs` the case-3
hypothesis it keeps as a binder — the top-top cup-arc partner agreement `stringCupTopTopPartner`
(`StringValleyCupTopTopSeed`), now proved — leaving only the genuine valley-shape inputs (`cupChained` /
`wholeChained` / `midPositive`) as honest hypotheses the eventual valley caller supplies. -/
theorem stringCupRestrict_reconstructs_unconditional
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock)
    (wholeChained : SpineBoundaryChained bottomCount (capBlock ++ cupBlock))
    (midPositive : 0 <
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length) :
    matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock
      = cupRestrict (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) :=
  stringCupRestrict_reconstructs bottomCount bottomPositive capBlock cupBlock capPure cupPure
    cupChained wholeChained midPositive
    (fun {topOffset} topLt wpAbove =>
      stringCupTopTopPartner bottomCount bottomPositive capBlock cupBlock capPure cupPure
        cupChained wholeChained midPositive topLt wpAbove)

/-! ## Concrete truth-probe — the UNCONDITIONAL reconstruct FIRES on the non-degenerate wide valley -/

/-- ★ **The unconditional cup-side reconstruction FIRES on the genuine non-degenerate wide valley.**  On the
concrete valley `[ε] ++ [η']` at `bottomCount = 4` (mid-width `2`, `stringWideProbe_midWidth_isTwo`), the cup
block's OWN diagram equals `cupRestrict` of the whole valley's diagram — a real inhabitation over a valley with
non-zero mid content, the honest non-degenerate firing that the gated reconstruct (whose case-3 hypothesis is not
`decide`-dischargeable) could never produce. -/
theorem stringCupRestrict_reconstructs_unconditional_firesOnWideValley :
    matchingOfSpineList
        (processSpine ⟨List.range 4, [], 4, 0⟩ [stringWideProbeCapAtom]).openWires.length
        [stringWideProbeCupAtom]
      = cupRestrict (matchingOfSpineList 4 ([stringWideProbeCapAtom] ++ [stringWideProbeCupAtom])) :=
  stringCupRestrict_reconstructs_unconditional 4 (by decide) [stringWideProbeCapAtom] [stringWideProbeCupAtom]
    stringWideProbeCapBlock_pureCap stringWideProbeCupBlock_pureCup
    stringWideProbeCupBlock_chained stringWideProbeValley_chained (by decide)

/-! ## Marker -/

/-- **★ ESTABLISHED — the string cup-side `DiagramType.ext` is UNCONDITIONAL (FC-3 r34): the case-3 gate of
`stringCupRestrict_reconstructs` is discharged by the ported `stringCupTopTopPartner`.**

Landed here, all zero-axiom:

  * `stringCupRestrict_reconstructs_unconditional` — the cup-side reconstruction, feeding the shipped gated
    `stringCupRestrict_reconstructs` its case-3 binder via `stringCupTopTopPartner` (`StringValleyCupTopTopSeed`),
    leaving only the genuine valley-shape inputs (`cupChained` / `wholeChained` / `midPositive`).
  * `stringCupRestrict_reconstructs_unconditional_firesOnWideValley` — the honest non-degenerate firing on the
    wide (mid-width `2`) valley `[ε] ++ [η']`, the inhabitation the gated theorem could not produce.

With this closed, `stringSameWholeMatching_cupBlockMatchingEq`'s cup reconstruction inputs are now supplyable and
`stringValleyAppend_split`'s cup splitter is unblocked.  Still separately gated downstream:
`stringValleysWithEqualMatching_spineTraceEquiv` (also needs the un-ported `valleysWithBlockMatchingEq_spineTraceEquiv`
interface) — so the producer flips `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) /
`fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) stay `false` this round (they need BOTH the full cup
assembly and the independent Piece-I beam `MatchingReductsShareSpineTrace`, #1996).  This round flips ONLY this NEW
un-gating marker.  `= true`. -/
def fxString_hasCupRestrictReconstructsUnconditional : Bool := true

end FX1Poly.Polygraph
