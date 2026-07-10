import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCommuteWordFactorData
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringLabelPinning

/-! # WalkingString — the WORD-LEVEL SPINE-ATOM PIN: the length-rigid atom determination, re-founded on boundary
words (FC-3 r10, B1 keystone)

The walking-adjunction sort determines a spine atom from its domain boundary + three arc read-off LENGTHS
(`adjunctionSpineAtom_eq_of_readOffs`, `WalkingAdjunction/AdjunctionAtomRigidity`), whose proof calls
`adjunctionPath_eq_of_length_eq` FIVE times — "parallel 1-cells of equal LENGTH are EQUAL".  At the walking adjoint
triple that rigidity is FALSE (`fxString_hasStringLengthRigidityFailure`: `F = left`, `H = coLeft` both length-1,
distinct), so the length-rigid atom pin does NOT port.  This is the SINGLE load-bearing node BOTH width-0 pure-cup
determinacy (`StringWidthZeroPureCupDeterminacy`) and the positive-core sort consume — the "one new brick" the recon
named.

This file re-founds that atom pin on boundary WORDS instead of lengths — colour-AWARE, so it runs at the string:

  * ★ `stringTwoCell_unique_of_wordBoundaries` — two PARALLEL string generators (same dom AND cod word) are equal.
    A `cases`-`cases` subsingleton: the four `StringTwoCell` constructors sit at pairwise-incompatible (dom, cod)
    boundaries, so the off-diagonal cases are discarded by index unification (`nil` vs `cons` clash on the dom /
    cod word, or a `base`/`tip` mode clash) — no wrong-shape case survives.  The string analog of the adjunction's
    `adjunctionTwoCell_unique`.
  * ★ `stringTwoCell_codPack_uniqueOfDom` — the DOM word ALONE determines a generator's (cod, cell) pack.  At each
    mode pair the two candidate generators carry DIFFERENT dom words (a cup's dom is `nil`, length 0; the parallel
    cap's dom has length 2), so the dom index discards the cross case by the same `nil`-vs-`cons` clash.  This is the
    colour-aware replacement for the adjunction's length-driven cod determination: the generator's cod is READ OFF
    its dom, not reconstructed from a cod length.
  * ★★ `stringSpineAtom_eq_of_wordReadOffs` — **the keystone.**  Two string spine atoms firing at the SAME domain
    boundary WORD with equal left-context and generator-dom read-off LENGTHS are EQUAL.  The word equality plus the
    two prefix lengths pin the left context, the mid modes, the generator dom, and the right context by the shipped
    `composePath_splitPackEqOfPrefixLengthEq` (peel the left context off the shared word, then the generator dom off
    the residual) — COLOUR-AWARE, no `adjunctionPath_eq_of_length_eq`.  The generator (hence its cod) is then pinned
    by `stringTwoCell_codPack_uniqueOfDom`.  This is the drop-in the width-0 sort port needs where the adjunction
    used `adjunctionSpineAtom_eq_of_readOffs`.

## What the pin STRENGTHENS over the adjunction (an honest finding)

`adjunctionSpineAtom_eq_of_readOffs` needs the generator-COD read-off length (`codLengthsEqual`) — its fifth
`adjunctionPath_eq_of_length_eq` call pins the cod from that length.  The string pin needs NO cod length: the
generator's cod is DOM-determined (`stringTwoCell_codPack_uniqueOfDom`).  So the word pin is a genuine strengthening
— two prefix lengths + the domain boundary word, versus three lengths + the domain boundary — the colour data (which
the string carries in its four distinct generators) subsumes the third length constraint the length-rigid engine
needed.  This is the r6 thesis ("length-rigidity was a CONVENIENCE, not a necessity", `StringLabelPinning`) made a
full atom-level theorem, not just the cup-vs-cap word separation `stringCupCod_ne_capDom`.

## What this file does NOT do (the flag stays `false` — honestly)

Shipping the word pin does NOT flip `fxString_hasAdjointTripleCompleteness`.  The pin is the atom-determination CORE
of the width-0 pure-cup sort (`matchingPureCupSpineSortFueled` in the adjunction lane), but that sort still needs the
partner-locate-by-chord port (`matchingLocateAux` analog, colour-blind ~180 lines) and the matching-injective drop
(`dropLastCup_matching_injective` port) assembled ON TOP of the pin before `StringWidthZeroPureCupDeterminacy` is
inhabited — the multi-round content the r10 budget defers.  This file lands the ONE node the whole sort's determinacy
rests on: the colour-aware atom pin, machine-checked, riding shipped tools
(`composePath_splitPackEqOfPrefixLengthEq`, the four-constructor `StringTwoCell` index structure).

Raw Lean 4 + Init; the two-cell uniqueness is `cases`-`cases` with automatic index-clash discharge, the atom pin is
the two-split-pack derivation of `StringCommuteWordFactorData` re-run to a full atom equality.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The two-cell subsingleton and the dom-determined cod pack -/

/-- ★ **Parallel string generators are equal.**  Two `StringTwoCell` at the SAME domain and codomain word are equal:
the four constructors (`unitLower`/`counitLower`/`unitUpper`/`counitUpper`) live at pairwise-incompatible (dom, cod)
boundaries, so after casing the first every off-diagonal second constructor is discarded by index unification (a
`nil`-vs-`cons` clash on the dom or cod word, or a `base`/`tip` mode clash).  The string analog of the adjunction's
`adjunctionTwoCell_unique`. -/
theorem stringTwoCell_unique_of_wordBoundaries
    {midSource midTarget : AdjointTripleMode}
    {generatorDom generatorCod : ModalityPath adjointTripleGraph midSource midTarget}
    (cellFirst cellSecond : StringTwoCell generatorDom generatorCod) :
    cellFirst = cellSecond := by
  cases cellFirst <;> cases cellSecond <;> rfl

/-- ★ **The dom word determines the generator's (cod, cell) pack.**  At each mode pair the two candidate string
generators carry DIFFERENT dom words — a cup's dom is `nil` (length 0), the parallel cap's dom has length 2 — so
casing the first generator fixes the shared dom to a constructor-headed word and the cross second constructor is
discarded by the `nil`-vs-`cons` index clash.  Packaged as a `PSigma` equality so a consumer pins BOTH the cod word
and the cell at once by `congrArg`.  This is the colour-aware replacement for the adjunction's length-driven cod
determination: the generator's cod is READ OFF its dom, not reconstructed from a cod length. -/
theorem stringTwoCell_codPack_uniqueOfDom
    {midSource midTarget : AdjointTripleMode}
    {generatorDom generatorCodFirst generatorCodSecond :
      ModalityPath adjointTripleGraph midSource midTarget}
    (cellFirst : StringTwoCell generatorDom generatorCodFirst)
    (cellSecond : StringTwoCell generatorDom generatorCodSecond) :
    (⟨generatorCodFirst, cellFirst⟩ :
        PSigma fun generatorCod => StringTwoCell generatorDom generatorCod)
      = ⟨generatorCodSecond, cellSecond⟩ := by
  cases cellFirst <;> cases cellSecond <;> rfl

/-! ## The keystone — the word-level spine-atom pin -/

/-- ★★ **The word-level spine-atom pin.**  Two string spine atoms firing at the SAME domain boundary WORD
(`leftContext · generatorDom · rightContext`) with equal left-context and generator-dom read-off LENGTHS are EQUAL.

The proof is the two-split-pack derivation of `StringCommuteWordFactorData` run to a full atom equality: peel the
left context off the shared word by `composePath_splitPackEqOfPrefixLengthEq` (pins the left mid mode, the left
context, and the residual `generatorDom · rightContext`), then peel the generator dom off that residual (pins the
right mid mode, the generator dom, and the right context) — COLOUR-AWARE, no `adjunctionPath_eq_of_length_eq`.  The
generator and its cod are then pinned by `stringTwoCell_codPack_uniqueOfDom` (the dom word determines them), so NO
cod read-off length is needed — a strengthening over the length-rigid `adjunctionSpineAtom_eq_of_readOffs`.  This is
the drop-in replacement the string width-0 pure-cup sort needs at each atom-determination step. -/
theorem stringSpineAtom_eq_of_wordReadOffs
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (atomFirst atomSecond : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (domBoundaryWordsEqual :
      composePath atomFirst.leftContext (composePath atomFirst.generatorDom atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorDom atomSecond.rightContext))
    (leftLengthsEqual : atomFirst.leftContext.length = atomSecond.leftContext.length)
    (domLengthsEqual : atomFirst.generatorDom.length = atomSecond.generatorDom.length) :
    atomFirst = atomSecond := by
  obtain ⟨leftMidFirst, rightMidFirst, leftContextFirst, generatorDomFirst, generatorCodFirst,
    generatorFirst, rightContextFirst⟩ := atomFirst
  obtain ⟨leftMidSecond, rightMidSecond, leftContextSecond, generatorDomSecond, generatorCodSecond,
    generatorSecond, rightContextSecond⟩ := atomSecond
  dsimp only at domBoundaryWordsEqual leftLengthsEqual domLengthsEqual
  have leftPack := composePath_splitPackEqOfPrefixLengthEq
    leftContextFirst (composePath generatorDomFirst rightContextFirst)
    leftContextSecond (composePath generatorDomSecond rightContextSecond)
    domBoundaryWordsEqual leftLengthsEqual
  have leftMidEqual : leftMidFirst = leftMidSecond := congrArg (fun pack => pack.fst) leftPack
  subst leftMidEqual
  injection leftPack with _leftFstEqual innerLeftPack
  injection innerLeftPack with leftContextEqual suffixesEqual
  subst leftContextEqual
  have rightPack := composePath_splitPackEqOfPrefixLengthEq
    generatorDomFirst rightContextFirst generatorDomSecond rightContextSecond
    suffixesEqual domLengthsEqual
  have rightMidEqual : rightMidFirst = rightMidSecond := congrArg (fun pack => pack.fst) rightPack
  subst rightMidEqual
  injection rightPack with _rightFstEqual innerRightPack
  injection innerRightPack with generatorDomEqual rightContextEqual
  subst generatorDomEqual
  subst rightContextEqual
  exact congrArg
    (fun pack =>
      (⟨leftMidFirst, rightMidFirst, leftContextFirst, generatorDomFirst, pack.fst, pack.snd,
          rightContextFirst⟩ :
        SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (stringTwoCell_codPack_uniqueOfDom generatorFirst generatorSecond)

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the word-level spine-atom pin is machine-checked (FC-3 r10, B1 keystone).**
`stringSpineAtom_eq_of_wordReadOffs`: two string spine atoms at the same domain boundary WORD with equal
left-context and generator-dom read-off lengths are EQUAL, colour-AWARE, via the shipped
`composePath_splitPackEqOfPrefixLengthEq` (two peels) plus the dom-determined generator pin
`stringTwoCell_codPack_uniqueOfDom` (and the parallel subsingleton `stringTwoCell_unique_of_wordBoundaries`).  This
re-founds the adjunction's length-rigid atom determination (`adjunctionSpineAtom_eq_of_readOffs`, five
`adjunctionPath_eq_of_length_eq` calls, FALSE at the string) on boundary words — the SINGLE load-bearing node both
`StringWidthZeroPureCupDeterminacy` and the positive-core sort consume, and a genuine STRENGTHENING (two prefix
lengths, no cod length — the colour data subsumes the third length constraint).  The r6 thesis, made a full
atom-level theorem.  `= true`. -/
def fxString_hasSpineAtomWordPin : Bool := true

/-- **OPEN (honest) — the word pin does NOT flip completeness; the width-0 sort assembly is a later round.**  The
pin is the atom-determination CORE of the width-0 pure-cup sort, but that sort still needs the partner-locate-by-chord
port (`matchingLocateAux` analog) and the matching-injective drop (`dropLastCup_matching_injective` port) assembled
on top before `StringWidthZeroPureCupDeterminacy` (`StringValleyDegenerateSplit`) is inhabited — the multi-round
content the r10 budget defers.  So `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) stays
`false` and `decidableStringSaturatedConv` stays gated on the three sub-producers, honestly, with the pin now shipped
and the exact remaining sort bricks named.  `= false`. -/
def fxString_hasSpineAtomWordPinCompletenessFlip : Bool := false

end FX1Poly.Polygraph
