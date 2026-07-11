import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingWidthZeroInvolution
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWidthZeroMixedSpeciesWitness

/-! # WalkingString — the width-0 partner INVOLUTION FIRES at the string signature (FC-3 r14, B1 truth-probe)

The make-or-break of the r14 round: the width-0 pure-cup partner involution
`matchingOfSpineListZero_partner_isInvolution` (`MatchingWidthZeroInvolution`), which the r13 markers named as
"hardcoded to `adjunctionModeSignature`, so it must first be genericised", has been widened over
`{signature : ModeSignature}` (the proof is colour-BLIND — pure signature-free union-find over `WireState`).
This file is the CONCRETE truth-probe that the widen actually unblocks the STRING lane: the widened involution
is instantiated at `adjointTripleModeSignature` — first for an ARBITRARY width-0 pure-cup string spine (the exact
brick the string LOCATE snake exclusion consumes), then FIRED on the r13 concrete mixed-species witness
`stringMixedWidthZeroSpine`.

  * ★ `stringWidthZeroPureCup_partnerInvolution` — for ANY width-0 pure-cup string spine over
    `adjointTripleModeSignature`, a non-fixed boundary port's partner-of-partner is the port again.  The widened
    involution, specialised to the three-generator seed: the width-0 partner involution the string LOCATE
    (`matchingForwardChordsNotAdjacent` twin) will ride, now AVAILABLE at the string signature.

  * ★ `stringMixedWidthZero_matchingPartner` — the concrete matching of the r13 mixed witness
    `[baseCup, tipCup]` is the nested (rainbow) matching `partner = [3, 2, 1, 0]` (base cup pairs the outer
    ports 0/3, the nested tip cup pairs the inner ports 1/2), machine-computed by `rfl`.

  * ★ `stringMixedWidthZero_partnerInvolution` — the widened involution FIRED on the concrete mixed witness:
    at any non-fixed index its partner-of-partner returns the index.  The involution holds on a REAL width-0
    string matching (the mixed-species one the r13 witness refuted single-species with), not just abstractly.

  * ★ `stringMixedWidthZero_involutionAtZero` — the fully concrete firing at port 0: `partner (partner 0) = 0`
    (`= partner 3 = 0`), by `rfl` on the computed matching — the involution, end-to-end, on concrete data.

## What this does NOT do (the gate flag stays `false`, honestly)

This probe confirms the involution FIRES at the string signature; it is not the sort.  The width-0 SORT
inhabiting `StringWidthZeroPureCupDeterminacyShared` (`StringValleyDegenerateSplit`) still needs the fueled
partner-LOCATE recursion (which consumes this involution through the snake exclusion) plus the
matching-injective drop — the r15+ content.  So `fxString_hasAdjointTripleCompleteness`
(`StringMatchingCompleteness`) stays `false`.

Raw Lean 4 + Init; the general probe is a one-line instantiation of the widened involution, the concrete facts
are `rfl` on a 4-wire matching.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The involution, available at the string signature -/

/-- ★ **The width-0 partner involution, at the string signature.**  For an arbitrary width-0 pure-cup string
spine over `adjointTripleModeSignature`, a non-fixed boundary port's partner-of-partner is the port again.
The widened `matchingOfSpineListZero_partner_isInvolution` specialised to the three-generator seed — the exact
brick the string LOCATE snake exclusion will consume, now AVAILABLE at the string signature (the r14
make-or-break unblock). -/
theorem stringWidthZeroPureCup_partnerInvolution
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (spine : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCup : AllCupArity spine)
    (index : Nat)
    (inRange : index < 0 + (matchingOfSpineList 0 spine).topCount)
    (notFixed : natListGetAt (matchingOfSpineList 0 spine).partner index ≠ index) :
    natListGetAt (matchingOfSpineList 0 spine).partner
        (natListGetAt (matchingOfSpineList 0 spine).partner index)
      = index :=
  matchingOfSpineListZero_partner_isInvolution spine pureCup index inRange notFixed

/-! ## The concrete firing on the r13 mixed-species witness -/

/-- ★ **The r13 mixed witness's concrete matching is the nested (rainbow) matching `[3, 2, 1, 0]`.**  The base
cup `η` (`id_base ⇒ F·G`) pairs the outer ports 0/3; the nested tip cup `η'` (`id_tip ⇒ G·H`, fired at the
interior `tip` junction, window 1) pairs the inner ports 1/2.  Machine-computed by `rfl`. -/
theorem stringMixedWidthZero_matchingPartner :
    (matchingOfSpineList 0 stringMixedWidthZeroSpine).partner = [3, 2, 1, 0] := rfl

/-- ★ The r13 mixed witness has boundary width 4 (top word `F·G·H·G`, four ports). -/
theorem stringMixedWidthZero_topCount :
    (matchingOfSpineList 0 stringMixedWidthZeroSpine).topCount = 4 := rfl

/-- ★ **The widened involution, FIRED on the r13 concrete mixed-species witness.**  For the concrete width-0
mixed-species spine `[baseCup, tipCup]`, any non-fixed port's partner-of-partner returns the port — the
involution holds on a REAL width-0 string matching (the mixed-species one), instantiating the widened involution
at `adjointTripleModeSignature` on `stringMixedWidthZeroSpine`. -/
theorem stringMixedWidthZero_partnerInvolution
    (index : Nat)
    (inRange : index < 0 + (matchingOfSpineList 0 stringMixedWidthZeroSpine).topCount)
    (notFixed :
      natListGetAt (matchingOfSpineList 0 stringMixedWidthZeroSpine).partner index ≠ index) :
    natListGetAt (matchingOfSpineList 0 stringMixedWidthZeroSpine).partner
        (natListGetAt (matchingOfSpineList 0 stringMixedWidthZeroSpine).partner index)
      = index :=
  stringWidthZeroPureCup_partnerInvolution stringMixedWidthZeroSpine
    stringMixedWidthZeroSpine_allCup index inRange notFixed

/-- ★ **The fully concrete involution firing at port 0.**  `partner (partner 0) = partner 3 = 0` on the r13
mixed witness's matching, by `rfl` — the width-0 partner involution, end-to-end, on concrete string data. -/
theorem stringMixedWidthZero_involutionAtZero :
    natListGetAt (matchingOfSpineList 0 stringMixedWidthZeroSpine).partner
        (natListGetAt (matchingOfSpineList 0 stringMixedWidthZeroSpine).partner 0)
      = 0 := rfl

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the width-0 partner INVOLUTION fires at the string signature (FC-3 r14, B1).**  The
make-or-break the r13 markers named ("hardcoded to `adjunctionModeSignature`, so it must first be genericised")
is discharged: `matchingOfSpineListZero_partner_isInvolution` was widened over `{signature : ModeSignature}`
(colour-blind proof) and is now AVAILABLE at `adjointTripleModeSignature` for arbitrary width-0 pure-cup string
spines (`stringWidthZeroPureCup_partnerInvolution`), FIRED on the r13 concrete mixed-species witness whose
matching is the nested rainbow `[3, 2, 1, 0]` (`stringMixedWidthZero_matchingPartner`,
`stringMixedWidthZero_partnerInvolution`, `stringMixedWidthZero_involutionAtZero`).

  What this marker does NOT close (no gate flag flips): the width-0 SORT
  (`StringWidthZeroPureCupDeterminacyShared`) — the fueled partner-LOCATE recursion (which consumes this
  involution through the snake exclusion) + the matching-injective drop — is the r15+ content.  So
  `fxString_hasAdjointTripleCompleteness` stays `false`, honestly.  `= true`. -/
def fxString_hasWidthZeroInvolutionProbe : Bool := true

end FX1Poly.Polygraph
