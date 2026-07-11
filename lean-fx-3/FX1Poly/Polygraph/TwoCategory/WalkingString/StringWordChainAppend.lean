import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineTopWordAppend

/-! # WalkingString/StringWordChainAppend — the boundary-WORD-chain append / peel / snoc substrate
(FC-3 r16, B3 word-chain substrate W1-W3)

The width-0 pure-cup SORT inhabiting `StringWidthZeroPureCupDeterminacyShared`
(`StringValleyDegenerateSplit`) threads TWO parallel chains through its fueled partner-LOCATE: the length
chain `SpineBoundaryChained 0` (feeding the drop / chord-shift ports) and a WORD chain
`SpineBoundaryWordChained bottomWord` (feeding the shared-top pin).  The locate reassembles its atom list
constructively — peel a prefix, transpose the located pair, re-append — so it needs the word-chain
analogues of the length version's append / peel / snoc bookkeeping.  The recon named three, grep confirmed
none exists; this file ships all three, signature-GENERIC, UNCONDITIONAL:

  * ★ W3 `spineBoundaryWordChained_prefix_ofAppend` — peel: a word-chained `xs ++ ys` gives a word-chained
    `xs` (at the same running bottom word).  Structural on `xs`, each cons inverting the chain
    (`spineBoundaryWordChained_tail`).  The word analogue of `spineBoundaryChained_prefix_ofAppend'`.
  * ★ W2 `spineBoundaryWordChained_append` — concatenate: a word-chained `xs` (from `bottomWord`) and a
    word-chained `ys` (from `spineListTopWord bottomWord xs`, the prefix's top word) give a word-chained
    `xs ++ ys` (from `bottomWord`).  Structural on `xs`; the suffix premise's boundary word is exactly the
    running word `spineListTopWord` advances to (definitional at each cons).
  * ★ W1 `spineBoundaryWordChained_snoc` — extend by one atom: a word-chained `xs` and a `lastAtom` firing
    at the prefix's top word `spineListTopWord bottomWord xs` give a word-chained `xs ++ [lastAtom]`.  The
    `ys = [lastAtom]` special case of W2.

Raw Lean 4 + Init; structural recursion on the prefix list threading the running boundary word.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## W3 — the peel: a word-chained append's prefix is word-chained -/

/-- ★ **W3 — a word-chained append's prefix is word-chained.**  If `prefixAtoms ++ suffixAtoms` is
boundary-word-chained from `bottomWord`, so is `prefixAtoms`.  Structural on the prefix: nil is chained at
any word, each cons peels the head (its firing word survives) and recurses on the shorter append.  The word
analogue of the length-only `spineBoundaryChained_prefix_ofAppend'`. -/
theorem spineBoundaryWordChained_prefix_ofAppend {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (bottomWord : ModalityPath signature.graph sourceMode targetMode) →
    (prefixAtoms suffixAtoms : List (SpineAtom signature sourceMode targetMode)) →
    SpineBoundaryWordChained bottomWord (prefixAtoms ++ suffixAtoms) →
    SpineBoundaryWordChained bottomWord prefixAtoms
  | bottomWord, [], _, _ => SpineBoundaryWordChained.nil bottomWord
  | _, atom :: restPrefix, suffixAtoms, chained => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryWordChained_tail chained
      exact SpineBoundaryWordChained.cons atom headFires
        (spineBoundaryWordChained_prefix_ofAppend
          (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext))
          restPrefix suffixAtoms tailChained)

/-! ## W2 — the concatenation: two word-chained blocks join at the prefix's top word -/

/-- ★ **W2 — concatenate two word-chained blocks.**  If `prefixAtoms` is word-chained from `bottomWord` and
`suffixAtoms` is word-chained from the prefix's top word `spineListTopWord bottomWord prefixAtoms`, then
`prefixAtoms ++ suffixAtoms` is word-chained from `bottomWord`.  Structural on the prefix: at nil the top
word IS the bottom word (`spineListTopWord bottomWord [] = bottomWord`), so the suffix premise is exactly
the goal; each cons peels the head and recurses, the running word advancing to the head's cod word — which
is precisely the word `spineListTopWord` threads to at the cons. -/
theorem spineBoundaryWordChained_append {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (bottomWord : ModalityPath signature.graph sourceMode targetMode) →
    (prefixAtoms suffixAtoms : List (SpineAtom signature sourceMode targetMode)) →
    SpineBoundaryWordChained bottomWord prefixAtoms →
    SpineBoundaryWordChained (spineListTopWord bottomWord prefixAtoms) suffixAtoms →
    SpineBoundaryWordChained bottomWord (prefixAtoms ++ suffixAtoms)
  | _, [], _, _, suffixChained => suffixChained
  | _, atom :: restPrefix, suffixAtoms, prefixChained, suffixChained => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryWordChained_tail prefixChained
      exact SpineBoundaryWordChained.cons atom headFires
        (spineBoundaryWordChained_append
          (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext))
          restPrefix suffixAtoms tailChained suffixChained)

/-! ## W1 — the snoc: extend a word-chained list by one atom at the top word -/

/-- ★ **W1 — extend a word-chained list by one atom at the top word.**  If `prefixAtoms` is word-chained
from `bottomWord` and `lastAtom` fires at the prefix's top word `spineListTopWord bottomWord prefixAtoms`
(its dom boundary word equals the running word there), then `prefixAtoms ++ [lastAtom]` is word-chained
from `bottomWord`.  The `suffixAtoms = [lastAtom]` special case of W2 (the singleton suffix chain is one
`cons` onto `nil`). -/
theorem spineBoundaryWordChained_snoc {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomWord : ModalityPath signature.graph sourceMode targetMode)
    (prefixAtoms : List (SpineAtom signature sourceMode targetMode))
    (lastAtom : SpineAtom signature sourceMode targetMode)
    (prefixChained : SpineBoundaryWordChained bottomWord prefixAtoms)
    (lastFires : spineListTopWord bottomWord prefixAtoms
      = composePath lastAtom.leftContext (composePath lastAtom.generatorDom lastAtom.rightContext)) :
    SpineBoundaryWordChained bottomWord (prefixAtoms ++ [lastAtom]) :=
  spineBoundaryWordChained_append bottomWord prefixAtoms [lastAtom] prefixChained
    (SpineBoundaryWordChained.cons lastAtom lastFires (SpineBoundaryWordChained.nil _))

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the boundary-WORD-chain append / peel / snoc substrate is shipped (FC-3 r16, B3
word-chain substrate W1-W3).**  `spineBoundaryWordChained_prefix_ofAppend` (W3, peel),
`spineBoundaryWordChained_append` (W2, concatenate two blocks at the prefix's top word), and
`spineBoundaryWordChained_snoc` (W1, extend by one atom at the top word).  All signature-GENERIC,
UNCONDITIONAL, structural on the prefix, zero-axiom.  These are the word-chain bookkeeping bricks the
width-0 sort's fueled LOCATE consumes to thread its parallel WORD chain through the constructive
peel / transpose / re-append.

  What this marker does NOT close (no gate flag flips): the fourth word-chain brick W4
  `spineBoundaryWordChained_swappedPairLeft` (the LEFT/case-iii chain preservation), the fueled
  `stringMatchingLocateAux` threading the two parallel chains, the `stringMatchingPureCupSpineSortFueled`
  assembly, and the inhabitation of `StringWidthZeroPureCupDeterminacyShared`.  So
  `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) stays `false`, honestly.
  `= true`. -/
def fxString_hasWordChainAppend : Bool := true

end FX1Poly.Polygraph
