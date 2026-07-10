import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineAtomWordPin

/-! # WalkingString — the SHARED-TOP last-cup pin: the LENGTH→WORD bridge the width-0 sort site needs
(FC-3 r11, B1/B2 keystone-feeder)

The walking-adjunction width-0 pure-cup sort (`MatchingWidthZeroSort.widthZeroPureCupDeterminacy_proof`) pins its
located partner cup to the head cup by `adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths`
(`WalkingAdjunction/ArcPeelFoundations`).  That wrapper upgrades a domain-boundary **LENGTH** equality
(`backCup.domBoundaryLength = C1.domBoundaryLength`, all the sort site delivers) to the domain-boundary **WORD**
equality the atom pin consumes — via `adjunctionPath_eq_of_length_eq` (length-rigidity: "parallel 1-cells of equal
length are equal").  At the walking adjoint triple that rigidity is FALSE (`string_left_ne_coLeft`: `F`, `H` both
length-1, distinct), so the LENGTH→WORD upgrade the sort needs has NO length-rigid route at the string.

The recon located the string's replacement: the WORD equality comes NOT from length rigidity but from the SHARED
TOP boundary word.  In a width-0 pure-cup valley both cup lists build the SAME top 1-cell (the fixed cod boundary
word); at the last-cup peel the head cup `C1` and the located partner `backCup` therefore carry the SAME cod
boundary word and fire at the SAME window.  Splitting that shared cod word by the common window pins their left
and right contexts (hence their dom boundary word) — COLOUR-AWARE, no length rigidity.  This file ships that
bridge:

  * ★ `stringLastCupDomWord_eq_of_sharedCod_sameWindow` — **the adapter.**  Two width-0 CUP spine atoms
    (generator dom length `0`) with EQUAL cod boundary WORD, equal window (left-context length), and equal cod
    read-off length have EQUAL dom boundary WORD.  Two `composePath_splitPackEqOfPrefixLengthEq` peels off the
    shared cod word (left context, then generator cod) pin both contexts; the generator doms coincide because
    both have length `0` (`modalityPathEqOfLengthZero`).  This is the LENGTH→WORD upgrade the string sort site
    lacks — the node the recon flagged as "the bridge exists but is NOT shipped".
  * ★★ `stringSpineAtom_eq_of_sharedCod_sameWindow` — **the drop-in.**  The full string replacement for
    `adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths`, WORD-driven: the adapter feeds its dom boundary
    word into the shipped keystone `stringSpineAtom_eq_of_wordReadOffs` (`StringSpineAtomWordPin`), which pins the
    generator (hence its cod) from the dom, concluding the two cup atoms are EQUAL — from a shared cod word plus a
    common window, with no cod-length read and no length rigidity.

## What this file does NOT do (the flag stays `false` — honestly)

The adapter is the ONE atom-pin bridge the width-0 pure-cup sort's last-cup peel rests on, but it is NOT the sort.
Inhabiting `StringWidthZeroPureCupDeterminacy` (`StringValleyDegenerateSplit`) additionally needs (1) the
colour-blind matching-brick ports (`matchingLastCup_isShortChord`, `matchingOpenWiresCupEndSplit`,
`dropLastCup_matching_injective`, the chord-shift/snake descents) re-typed at the three-generator seed; (2) the
partner-locate-by-chord recursion (`matchingLocateAux`) re-plumbed onto the WORD-swap kit
(`spineAtomSwap_of_disjointWordWindows`, already shipped) threading a `SpineBoundaryWordChained`; AND (3) the
`StringWidthZeroPureCupDeterminacy` signature STRENGTHENED with the shared top word this adapter consumes (its bare
form throws the top word away, so the adapter cannot even be called from it).  Those are the multi-round content
the recon budgets to r12+.  So `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) stays
`false`; this file lands the keystone-feeding bridge, machine-checked, riding the shipped
`composePath_splitPackEqOfPrefixLengthEq` and the shipped keystone pin.

Raw Lean 4 + Init; the adapter is the two-split-pack derivation off the shared COD word (dual to the keystone's DOM
split), the drop-in is one keystone application.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/
`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Length-0 paths are the identity 1-cell -/

/-- Two modality paths of length `0` between the same modes are EQUAL — both are `nil` (a `cons` has length
`≥ 1`), so the only length-0 path is the identity 1-cell.  Hand-rolled `cases` (core has no length-zero-path
lemma); propext-free (`Nat.noConfusion` on the successor length). -/
private theorem modalityPathEqOfLengthZero {graph : ModeGraph} {sourceMode targetMode : graph.Mode}
    (pathFirst pathSecond : ModalityPath graph sourceMode targetMode)
    (firstZero : pathFirst.length = 0) (secondZero : pathSecond.length = 0) :
    pathFirst = pathSecond := by
  cases pathFirst with
  | nil _ =>
      cases pathSecond with
      | nil _ => rfl
      | cons _ _ =>
          dsimp only [ModalityPath.length] at secondZero
          exact Nat.noConfusion secondZero
  | cons _ _ =>
      dsimp only [ModalityPath.length] at firstZero
      exact Nat.noConfusion firstZero

/-! ## The adapter — the LENGTH→WORD bridge off the shared cod word -/

/-- ★ **The shared-top dom-word bridge.**  Two width-0 CUP spine atoms (generator dom length `0`) whose COD
boundary words agree, that fire at the same window (equal left-context length) with equal cod read-off length, have
EQUAL DOM boundary words.  Peel the left context off the shared cod word by
`composePath_splitPackEqOfPrefixLengthEq` (pins the left mid mode + the left context + the residual
`generatorCod · rightContext`), then peel the generator cod off that residual (pins the right mid mode + the
generator cod + the right context); the two generator doms coincide because both have length `0`
(`modalityPathEqOfLengthZero`), so the dom boundary words `leftContext · generatorDom · rightContext` agree by
congruence.  COLOUR-AWARE, no `adjunctionPath_eq_of_length_eq` — the string's replacement for the length-rigid
`adjunctionAtoms_domBoundaryPathsEqual_of_lengthsEqual`.  This is the LENGTH→WORD upgrade the width-0 sort site
lacks: at the last-cup peel the head cup and the located partner share the fixed top word, and this delivers the
dom word the keystone pin needs. -/
theorem stringLastCupDomWord_eq_of_sharedCod_sameWindow
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (atomFirst atomSecond : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (codBoundaryWordsEqual :
      composePath atomFirst.leftContext (composePath atomFirst.generatorCod atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorCod atomSecond.rightContext))
    (leftLengthsEqual : atomFirst.leftContext.length = atomSecond.leftContext.length)
    (codLengthsEqual : atomFirst.generatorCod.length = atomSecond.generatorCod.length)
    (domZeroFirst : atomFirst.generatorDom.length = 0)
    (domZeroSecond : atomSecond.generatorDom.length = 0) :
    composePath atomFirst.leftContext (composePath atomFirst.generatorDom atomFirst.rightContext)
      = composePath atomSecond.leftContext
          (composePath atomSecond.generatorDom atomSecond.rightContext) := by
  obtain ⟨leftMidFirst, rightMidFirst, leftContextFirst, generatorDomFirst, generatorCodFirst,
    generatorFirst, rightContextFirst⟩ := atomFirst
  obtain ⟨leftMidSecond, rightMidSecond, leftContextSecond, generatorDomSecond, generatorCodSecond,
    generatorSecond, rightContextSecond⟩ := atomSecond
  dsimp only at codBoundaryWordsEqual leftLengthsEqual codLengthsEqual domZeroFirst domZeroSecond ⊢
  have leftPack := composePath_splitPackEqOfPrefixLengthEq
    leftContextFirst (composePath generatorCodFirst rightContextFirst)
    leftContextSecond (composePath generatorCodSecond rightContextSecond)
    codBoundaryWordsEqual leftLengthsEqual
  have leftMidEqual : leftMidFirst = leftMidSecond := congrArg (fun pack => pack.fst) leftPack
  subst leftMidEqual
  injection leftPack with _leftFstEqual innerLeftPack
  injection innerLeftPack with leftContextEqual codSuffixesEqual
  subst leftContextEqual
  have rightPack := composePath_splitPackEqOfPrefixLengthEq
    generatorCodFirst rightContextFirst generatorCodSecond rightContextSecond
    codSuffixesEqual codLengthsEqual
  have rightMidEqual : rightMidFirst = rightMidSecond := congrArg (fun pack => pack.fst) rightPack
  subst rightMidEqual
  injection rightPack with _rightFstEqual innerRightPack
  injection innerRightPack with _generatorCodEqual rightContextEqual
  subst rightContextEqual
  have domEqual : generatorDomFirst = generatorDomSecond :=
    modalityPathEqOfLengthZero generatorDomFirst generatorDomSecond domZeroFirst domZeroSecond
  rw [domEqual]

/-! ## The drop-in — the WORD-driven last-cup atom pin -/

/-- ★★ **The shared-top last-cup pin (the drop-in).**  Two width-0 CUP spine atoms sharing a COD boundary word,
firing at the same window with equal cod read-off length, are EQUAL.  The adapter
`stringLastCupDomWord_eq_of_sharedCod_sameWindow` delivers their DOM boundary word; the shipped keystone
`stringSpineAtom_eq_of_wordReadOffs` (`StringSpineAtomWordPin`) then pins the two atoms from that dom word plus the
common window and the common dom length (both `0`) — the generator and its cod are DOM-determined, so NO cod-length
read is needed.  This is the string replacement, WORD-driven, for the length-rigid
`adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths` the walking-adjunction sort's last-cup peel calls. -/
theorem stringSpineAtom_eq_of_sharedCod_sameWindow
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (atomFirst atomSecond : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (codBoundaryWordsEqual :
      composePath atomFirst.leftContext (composePath atomFirst.generatorCod atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorCod atomSecond.rightContext))
    (leftLengthsEqual : atomFirst.leftContext.length = atomSecond.leftContext.length)
    (codLengthsEqual : atomFirst.generatorCod.length = atomSecond.generatorCod.length)
    (domZeroFirst : atomFirst.generatorDom.length = 0)
    (domZeroSecond : atomSecond.generatorDom.length = 0) :
    atomFirst = atomSecond :=
  stringSpineAtom_eq_of_wordReadOffs atomFirst atomSecond
    (stringLastCupDomWord_eq_of_sharedCod_sameWindow atomFirst atomSecond
      codBoundaryWordsEqual leftLengthsEqual codLengthsEqual domZeroFirst domZeroSecond)
    leftLengthsEqual (domZeroFirst.trans domZeroSecond.symm)

/-! ## Non-vacuity — the pin fires on a concrete lower cup -/

/-- The pin fires on a concrete width-0 lower cup `η : id_base ⇒ F·G`: its hypotheses (shared cod word, equal
window, equal cod length, dom length `0`) all hold reflexively, and the drop-in discharges the atom equality.  A
determinacy pin has no distinct-atom witness (any pair satisfying the hypotheses is equal — that is its content),
so non-vacuity is exactly "the hypotheses are inhabited by a real cup", confirmed here. -/
theorem stringSharedCodCupPin_firesOnConcreteCup :
    (⟨AdjointTripleMode.base, AdjointTripleMode.base,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base, stringFG,
        StringTwoCell.unitLower,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base⟩ :
      SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base)
    = ⟨AdjointTripleMode.base, AdjointTripleMode.base,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base, stringFG,
        StringTwoCell.unitLower,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base⟩ :=
  stringSpineAtom_eq_of_sharedCod_sameWindow _ _ rfl rfl rfl rfl rfl

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the SHARED-TOP last-cup pin is machine-checked; the LENGTH→WORD bridge the width-0 sort
needs is shipped (FC-3 r11, B1/B2).**  `stringLastCupDomWord_eq_of_sharedCod_sameWindow` (the adapter) upgrades a
shared COD boundary word + common window + `0` dom length into the DOM boundary word equality, via two
`composePath_splitPackEqOfPrefixLengthEq` peels off the shared cod word plus `modalityPathEqOfLengthZero`;
`stringSpineAtom_eq_of_sharedCod_sameWindow` (the drop-in) feeds that dom word into the shipped keystone
`stringSpineAtom_eq_of_wordReadOffs` to conclude two width-0 cup atoms EQUAL.  This is the string replacement,
COLOUR-AWARE and WORD-driven, for the walking-adjunction sort's length-rigid last-cup pin
`adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths` (whose `adjunctionPath_eq_of_length_eq` upgrade is
FALSE at the string) — the node the recon named "the bridge exists but is NOT shipped".

  What this marker does NOT close (no gate flag flips): the width-0 sort itself.
  `StringWidthZeroPureCupDeterminacy` (`StringValleyDegenerateSplit`) still needs the colour-blind matching-brick
  ports, the `matchingLocateAux` recursion re-plumbed onto the shipped WORD-swap kit, AND its own signature
  STRENGTHENED with the shared top word this adapter consumes (the bare form discards it) — the multi-round content
  the recon budgets to r12+.  So `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) stays
  `false`, honestly, with the keystone-feeding bridge now shipped and the exact remaining sort bricks named.
  `= true`. -/
def fxString_hasLastCupSharedTopPin : Bool := true

end FX1Poly.Polygraph
