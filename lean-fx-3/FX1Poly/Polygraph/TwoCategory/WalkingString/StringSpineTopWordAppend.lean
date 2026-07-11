import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineTopWord

/-! # WalkingString — the spine TOP-WORD append + prefix-drop bricks for the width-0 sort recursion
(FC-3 r14, B3 down-payment)

The full width-0 pure-cup sort inhabiting `StringWidthZeroPureCupDeterminacyShared`
(`StringValleyDegenerateSplit`) is the fueled partner-LOCATE recursion whose DROP step hands the SHORTER shared
top word (the located cup's dom word) to the recursive call — the shared top drops by one cup at each descent.
The recon named the two `spineListTopWord` bookkeeping bricks that step needs (the word analogs of the length
lemmas the adjunction sort threads); grep confirmed neither exists.  This file ships both, UNCONDITIONALLY.

  * ★ `spineListTopWord_append` — threading the top word through a concatenation is threading through the prefix,
    then through the suffix from the prefix's top word: `spineListTopWord bw (xs ++ ys) =
    spineListTopWord (spineListTopWord bw xs) ys`.  Structural recursion on the prefix (the running bottom word
    generalised).  The word analog of a fold-append law.

  * ★ `spineListTopWord_prefix_eq_lastDomWord` — for a word-chained spine `prefixAtoms ++ [lastAtom]`, the
    prefix's top word IS the appended atom's DOM word: `spineListTopWord bw prefixAtoms =
    lastAtom.leftContext · lastAtom.generatorDom · lastAtom.rightContext`.  Structural recursion on the prefix,
    each step inverting the word-chain cons (`spineBoundaryWordChained_tail`).  The word analog of the length
    lemma `processSpine_prefix_openWires_eq_lastDomBoundary` the adjunction sort's drop step uses at the width-0
    seed — this is what lets the sort recursion hand the shorter shared top word (the last cup's dom word) to the
    recursive call.

## What this does NOT do (the gate flag stays `false`, honestly)

These are two bookkeeping bricks the width-0 sort recursion consumes, not the recursion.  The full
`StringWidthZeroPureCupDeterminacyShared` inhabitation still needs the fueled partner-LOCATE (blocked on the
peel `extractDiagram_eq_of_atomicPureCupTraceEquiv` being string-ready — the r15+ classifier-elimination) plus
the matching-injective drop.  So `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) stays
`false`.

Raw Lean 4 + Init; both bricks are structural recursion on the prefix list threading the running boundary word.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **Top-word append law.**  Threading `spineListTopWord` through a concatenation `prefixAtoms ++ suffixAtoms`
equals threading through the prefix, then through the suffix starting from the prefix's top word.  Structural
recursion on the prefix; the nil case collapses `[] ++ ys` and `spineListTopWord bw []`, the cons case hands the
head atom's cod word to the recursive call. -/
theorem spineListTopWord_append {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (bottomWord : ModalityPath signature.graph sourceMode targetMode) →
    (prefixAtoms suffixAtoms : List (SpineAtom signature sourceMode targetMode)) →
    spineListTopWord bottomWord (prefixAtoms ++ suffixAtoms)
      = spineListTopWord (spineListTopWord bottomWord prefixAtoms) suffixAtoms
  | _, [], _ => rfl
  | bottomWord, atom :: rest, suffixAtoms =>
      spineListTopWord_append
        (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)) rest suffixAtoms

/-- ★ **The word-chained prefix's top word is the appended atom's dom word.**  For a spine
`prefixAtoms ++ [lastAtom]` that is boundary-word-chained from `bottomWord`, threading the top word through the
prefix lands exactly on `lastAtom`'s domain boundary word — the running word the last atom fires at.  Structural
recursion on the prefix, each cons inverting the word-chain (`spineBoundaryWordChained_tail`) to advance the
running word to the head atom's cod word.  The word analog of
`processSpine_prefix_openWires_eq_lastDomBoundary`; lets the width-0 sort recursion drop the shared top word by
one cup. -/
theorem spineListTopWord_prefix_eq_lastDomWord {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (bottomWord : ModalityPath signature.graph sourceMode targetMode) →
    (prefixAtoms : List (SpineAtom signature sourceMode targetMode)) →
    (lastAtom : SpineAtom signature sourceMode targetMode) →
    SpineBoundaryWordChained bottomWord (prefixAtoms ++ [lastAtom]) →
    spineListTopWord bottomWord prefixAtoms
      = composePath lastAtom.leftContext (composePath lastAtom.generatorDom lastAtom.rightContext)
  | bottomWord, [], lastAtom, chained => (spineBoundaryWordChained_tail chained).1
  | bottomWord, atom :: rest, lastAtom, chained => by
      obtain ⟨_headFires, tailChained⟩ := spineBoundaryWordChained_tail chained
      exact spineListTopWord_prefix_eq_lastDomWord
        (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)) rest lastAtom
        tailChained

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the spine top-word append + prefix-drop bricks are shipped (FC-3 r14, B3 down-payment).**
`spineListTopWord_append` (threading through a concatenation factors through the prefix's top word) and
`spineListTopWord_prefix_eq_lastDomWord` (a word-chained prefix's top word is the appended atom's dom word) —
the two `spineListTopWord` bookkeeping bricks the recon named as needed by the width-0 sort's DROP step, which
hands the shorter shared top word (the located cup's dom word) to the recursive call.  Both UNCONDITIONAL,
structural, zero-axiom.

  What this marker does NOT close (no gate flag flips): the full `StringWidthZeroPureCupDeterminacyShared`
  inhabitation — the fueled partner-LOCATE recursion (blocked on the peel
  `extractDiagram_eq_of_atomicPureCupTraceEquiv` being string-ready, the r15+ classifier-elimination) + the
  matching-injective drop.  So `fxString_hasAdjointTripleCompleteness` stays `false`, honestly.  `= true`. -/
def fxString_hasSpineTopWordAppend : Bool := true

end FX1Poly.Polygraph
