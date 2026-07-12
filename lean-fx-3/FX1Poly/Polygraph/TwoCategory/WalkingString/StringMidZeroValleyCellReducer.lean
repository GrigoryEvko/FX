import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMidZeroValleyProducer
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSharedMidWord
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyDegenerateSplit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWordChainAppend
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineTopWordAppend
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingModel

/-! # WalkingString/StringMidZeroValleyCellReducer — the cell-level reducer that INHABITS
`StringMidZeroValleyTraceEquiv` UNCONDITIONALLY (FC-3 r38)

`StringValleyDegenerateSplit` sharpened the monolithic Piece-II residual into three colour-keyed sub-producers, one
of which is the Tier-D case-(b) residual `StringMidZeroValleyTraceEquiv` (two whole VALLEY cells with equal boundary
`matchingOf`, POSITIVE source width, and mid-width `0` are `SpineTraceEquiv`).  The r36 block-level producer
`stringMidZeroValleysWithEqualMatching_spineTraceEquiv` (`StringMidZeroValleyProducer`) discharges that content — but
it takes the two cup blocks' shared boundary WORDS as SEVEN hypotheses (`capWord`, `midWord`, four
`SpineBoundaryWordChained` chains, the shared `spineListTopWord`).  The r37 shared-`midWord` brick
`stringSharedMidWord_ofMidZero` (`StringSharedMidWord`) supplies the shared mid word for the two parallel cap blocks
at mid-width `0`.  This file threads those together into the CELL-level reducer: block-split the two `RawTwoCellExpr`
valleys, DERIVE the seven word arguments from the cell structure, and fire the producer.  The result inhabits
`StringMidZeroValleyTraceEquiv` with NO open hypothesis — the string port of the walking-adjunction
`midZeroValleyTraceEquiv_ofCupReconstruct` (`SpineValleyCellDegenerate`), word-threaded (the adjunction reassembly
is un-word-threaded, so it sidesteps the derivation this file lands).

Two new sub-bricks close the two word arguments the shipped substrate does not already supply:

  * ★ **Brick A** `stringSpineBoundaryChained_cupSuffix_ofCapPrefix` — the NUMERIC cup-suffix chain restriction at
    the walking ADJOINT-TRIPLE signature.  The only shipped one (`spineBoundaryChained_cupSuffix_ofCapPrefix`,
    `SpineValleyChainRestrict`) is hardcoded to `adjunctionModeSignature`; its proof is signature-blind (reads only
    the per-atom boundary tracker `stepAtom_openWires_tracksBoundary`), so this is a per-file re-copy under a
    distinct name (umbrella duplicate-global-safe), `adjunctionModeSignature → adjointTripleModeSignature`.

  * ★ **Brick B** `spineBoundaryWordChained_cupSuffix_ofCapPrefix` — the WORD-chain DROP, the W4-suffix companion to
    the shipped W1-W3 (`StringWordChainAppend`): a word-chained `capBlock ++ cupBlock` restricts to the cup suffix
    word-chained from the prefix's top word `spineListTopWord bottomWord capBlock`.  `{signature}`-GENERIC,
    structural on the cap prefix, no arity needed (the running word advances by each atom's cod word regardless of
    species) — the exact mirror of W3 `spineBoundaryWordChained_prefix_ofAppend` for the suffix.

The reducer supplies `bottomCount := sourcePath.length`, `capWord := sourcePath`, `midWord := spineListTopWord
sourcePath capA`.  Every producer hypothesis is derived: the cap prefix chain by the shipped prefix restriction; the
cup suffix chain by Brick A; the cap word chain by W3; the cup word chain by Brick B; the shared cap top word by the
r37 brick (transporting the second cup word chain across); the shared cup top word by the top-word append law
(`spineListTopWord_append`) folded against both valleys' `RawTwoCellExpr.spineListTopWord_spine`.

  What this does NOT flip (honestly): the completeness masters `fxString_hasAdjointTripleCompleteness`
  (`StringMatchingCompleteness`) and `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) stay `false`.  This
  reducer discharges ONE of the THREE colour-keyed sub-producers (`StringMidZeroValleyTraceEquiv`), reducing the
  standing residual from three bricks to two — the un-ported colour-aware SORT core
  `StringWidthZeroPureCupDeterminacyShared` and `StringCellValleyTraceEquivPositive` remain the walls.  The beam
  `StringMatchingReductsShareSpineTrace` still consumes those two as hypotheses; no master flips.

Raw Lean 4 + Init; the two bricks are structural recursion over the cap prefix, the reducer is pure block-split +
word-derivation assembly over the shipped r36 producer and r37 shared-`midWord` brick, no `omega` / `simp`-AC /
`WellFounded.fix`.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local propext-free `List.range` length (per-file copy; the core `List.length_range` leaks propext) -/

/-- The `List.range` accumulator length, structural and propext-free.  Per-file copy with a distinct name from the
walking-adjunction / shared-`midWord` twins so the umbrella build's global table stays duplicate-free. -/
private theorem stringMidZeroReducerRangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := stringMidZeroReducerRangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

/-- `(List.range count).length = count`, propext-free (per-file copy; the core lemma leaks). -/
private theorem stringMidZeroReducerRangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [stringMidZeroReducerRangeLoopLength count []]
  exact Nat.add_zero count

/-! ## Brick A — the numeric cup-suffix chain restriction at the adjoint-triple signature -/

/-- ★ **Brick A — the numeric cup-suffix chain restriction (adjoint-triple port).**  A whole valley chained from
`state.openWires.length` restricts, over its pure-cap prefix, to the cup suffix chained from the mid-width
`(processSpine state capBlock).openWires.length`.  Each cap fires at the running boundary (chain inversion) and
`stepAtom_openWires_tracksBoundary` shows the stepped open-wire count equals the head's cod boundary, at which the
tail chain continues — so the induction threads the mid-width to the cup block.  Per-file re-copy of the shipped
`spineBoundaryChained_cupSuffix_ofCapPrefix` (`SpineValleyChainRestrict`, hardcoded to `adjunctionModeSignature`) at
`adjointTripleModeSignature`; the proof is signature-blind. -/
theorem stringSpineBoundaryChained_cupSuffix_ofCapPrefix
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (capBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    AllCapArity capBlock →
    (cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    (state : WireState) →
    SpineBoundaryChained state.openWires.length (capBlock ++ cupBlock) →
    SpineBoundaryChained (processSpine state capBlock).openWires.length cupBlock
  | [], _, _, _, chained => chained
  | atom :: rest, capPure, cupBlock, state, chained => by
      cases capPure with
      | cons capDom capCod restCap =>
          obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
          have arity : AtomHasCupOrCapArity atom := Or.inr ⟨capDom, capCod⟩
          have stepTracks : (stepAtom state atom).openWires.length = atom.codBoundaryLength :=
            stepAtom_openWires_tracksBoundary state atom arity headFires.symm
          have tailChainedAtStep :
              SpineBoundaryChained (stepAtom state atom).openWires.length (rest ++ cupBlock) := by
            rw [stepTracks]; exact tailChained
          show SpineBoundaryChained (processSpine (stepAtom state atom) rest).openWires.length cupBlock
          exact stringSpineBoundaryChained_cupSuffix_ofCapPrefix rest restCap cupBlock
            (stepAtom state atom) tailChainedAtStep

/-! ## Brick B — the word-chain drop (W4, the suffix companion to the shipped W1-W3) -/

/-- ★ **Brick B — the word-chain drop.**  A word-chained `capBlock ++ cupBlock` (from `bottomWord`) restricts to
the cup suffix word-chained from the prefix's top word `spineListTopWord bottomWord capBlock`.  Structural on the
cap prefix, each cons inverting the word chain (`spineBoundaryWordChained_tail`): the running word advances to the
head's cod word — precisely the word `spineListTopWord` threads to at the cons — and the tail chain continues from
there.  No arity is read (the word chain advances by each atom's cod word regardless of species), so this is the
exact mirror of the shipped W3 `spineBoundaryWordChained_prefix_ofAppend` for the SUFFIX, `{signature}`-GENERIC. -/
theorem spineBoundaryWordChained_cupSuffix_ofCapPrefix {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (bottomWord : ModalityPath signature.graph sourceMode targetMode) →
    (capBlock cupBlock : List (SpineAtom signature sourceMode targetMode)) →
    SpineBoundaryWordChained bottomWord (capBlock ++ cupBlock) →
    SpineBoundaryWordChained (spineListTopWord bottomWord capBlock) cupBlock
  | _, [], _, chained => chained
  | bottomWord, atom :: rest, cupBlock, chained => by
      obtain ⟨_headFires, tailChained⟩ := spineBoundaryWordChained_tail chained
      show SpineBoundaryWordChained
        (spineListTopWord
          (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)) rest) cupBlock
      exact spineBoundaryWordChained_cupSuffix_ofCapPrefix
        (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)) rest cupBlock tailChained

/-! ## The cell-level reducer — `StringMidZeroValleyTraceEquiv` inhabited UNCONDITIONALLY -/

/-- ★★ **The mid-width-`0` valley determinacy sub-producer, DISCHARGED.**  `StringMidZeroValleyTraceEquiv` holds
with no open hypothesis: two whole VALLEY string cells with equal boundary `matchingOf`, POSITIVE source width, and
mid-width `0` are `SpineTraceEquiv`.  Block-split both valleys (`stringSpineValley_blockSplit`); derive the length
chains (whole chain from `RawTwoCellExpr.spineBoundaryChained_spine`, cap prefix by the shipped prefix restriction,
cup suffix at the mid-width by Brick A); derive the word chains (`capWord := sourcePath` via W3, `midWord :=
spineListTopWord sourcePath capA` via Brick B); derive the shared cap top word by the r37 brick
`stringSharedMidWord_ofMidZero` (transporting the second cup's word chain across); derive the shared cup top word by
the top-word append law folded against both `RawTwoCellExpr.spineListTopWord_spine`; then fire the r36 producer
`stringMidZeroValleysWithEqualMatching_spineTraceEquiv`.  The string port of the adjunction's
`midZeroValleyTraceEquiv_ofCupReconstruct`, word-threaded. -/
theorem stringMidZeroValleyTraceEquiv_holds : StringMidZeroValleyTraceEquiv := by
  intro sourceMode targetMode sourcePath targetPath valleyA valleyB isValleyA isValleyB
    matchingEq sourcePos midZeroA
  -- Block-split both valley spines into cap-prefix ++ cup-suffix.
  obtain ⟨capA, cupA, splitA, capPureA, cupPureA⟩ := stringSpineValley_blockSplit valleyA.spine isValleyA
  obtain ⟨capB, cupB, splitB, capPureB, cupPureB⟩ := stringSpineValley_blockSplit valleyB.spine isValleyB
  -- The two whole valleys are boundary-chained at the source width.
  have wholeChainedA : SpineBoundaryChained sourcePath.length (capA ++ cupA) := by
    rw [← splitA]; exact valleyA.spineBoundaryChained_spine
  have wholeChainedB : SpineBoundaryChained sourcePath.length (capB ++ cupB) := by
    rw [← splitB]; exact valleyB.spineBoundaryChained_spine
  -- The cup suffixes are boundary-chained at the mid-width (restrict the whole chain over the cap prefix, Brick A).
  have seedWholeA : SpineBoundaryChained
      (⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ : WireState).openWires.length (capA ++ cupA) := by
    show SpineBoundaryChained (List.range sourcePath.length).length (capA ++ cupA)
    rw [stringMidZeroReducerRangeLength]; exact wholeChainedA
  have seedWholeB : SpineBoundaryChained
      (⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ : WireState).openWires.length (capB ++ cupB) := by
    show SpineBoundaryChained (List.range sourcePath.length).length (capB ++ cupB)
    rw [stringMidZeroReducerRangeLength]; exact wholeChainedB
  have cupChainedA : SpineBoundaryChained
      (processSpine ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ capA).openWires.length cupA :=
    stringSpineBoundaryChained_cupSuffix_ofCapPrefix capA capPureA cupA
      ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ seedWholeA
  have cupChainedB : SpineBoundaryChained
      (processSpine ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ capB).openWires.length cupB :=
    stringSpineBoundaryChained_cupSuffix_ofCapPrefix capB capPureB cupB
      ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ seedWholeB
  -- The cap prefixes are boundary-chained at the source width (prefix restriction).
  have capChainedA : SpineBoundaryChained sourcePath.length capA :=
    spineBoundaryChained_prefix_ofAppend capA cupA sourcePath.length wholeChainedA
  have capChainedB : SpineBoundaryChained sourcePath.length capB :=
    spineBoundaryChained_prefix_ofAppend capB cupB sourcePath.length wholeChainedB
  -- The whole valleys are boundary-WORD-chained from the source word.
  have wholeWordA : SpineBoundaryWordChained sourcePath (capA ++ cupA) := by
    rw [← splitA]; exact valleyA.spineBoundaryWordChained_spine
  have wholeWordB : SpineBoundaryWordChained sourcePath (capB ++ cupB) := by
    rw [← splitB]; exact valleyB.spineBoundaryWordChained_spine
  -- The cap word chains (W3 peel) and cup word chains (Brick B drop).
  have capWordA : SpineBoundaryWordChained sourcePath capA :=
    spineBoundaryWordChained_prefix_ofAppend sourcePath capA cupA wholeWordA
  have capWordB : SpineBoundaryWordChained sourcePath capB :=
    spineBoundaryWordChained_prefix_ofAppend sourcePath capB cupB wholeWordB
  have cupWordA : SpineBoundaryWordChained (spineListTopWord sourcePath capA) cupA :=
    spineBoundaryWordChained_cupSuffix_ofCapPrefix sourcePath capA cupA wholeWordA
  have cupWordBraw : SpineBoundaryWordChained (spineListTopWord sourcePath capB) cupB :=
    spineBoundaryWordChained_cupSuffix_ofCapPrefix sourcePath capB cupB wholeWordB
  -- Re-read the matching hypothesis at the spine level.
  have wholeEqA : matchingOf valleyA = matchingOfSpineList sourcePath.length (capA ++ cupA) := by
    show matchingOfSpineList sourcePath.length valleyA.spine
      = matchingOfSpineList sourcePath.length (capA ++ cupA)
    rw [splitA]
  have wholeEqB : matchingOf valleyB = matchingOfSpineList sourcePath.length (capB ++ cupB) := by
    show matchingOfSpineList sourcePath.length valleyB.spine
      = matchingOfSpineList sourcePath.length (capB ++ cupB)
    rw [splitB]
  have wholeEq : matchingOfSpineList sourcePath.length (capA ++ cupA)
      = matchingOfSpineList sourcePath.length (capB ++ cupB) :=
    wholeEqA.symm.trans (matchingEq.trans wholeEqB)
  -- The mid-`0` witness at the spine level.
  have midZeroFirst : survivorTopTotal (matchingOfSpineList sourcePath.length (capA ++ cupA)) = 0 := by
    rw [← wholeEqA]; exact midZeroA
  -- The shared mid word (the r37 brick): both cap blocks reach the same length-`0` top word at mid-width `0`.
  have sharedMid : spineListTopWord sourcePath capA = spineListTopWord sourcePath capB :=
    stringSharedMidWord_ofMidZero sourcePath.length sourcePos sourcePath rfl capA capB cupA cupB
      capPureA capPureB cupPureA cupPureB capChainedA capChainedB cupChainedA cupChainedB midZeroFirst wholeEq
  -- Transport the second cup's word chain to the shared mid word.
  have cupWordB : SpineBoundaryWordChained (spineListTopWord sourcePath capA) cupB := sharedMid ▸ cupWordBraw
  -- The shared cup top word: both cup blocks thread to the common `targetPath`.
  have topA : spineListTopWord (spineListTopWord sourcePath capA) cupA = targetPath := by
    rw [← spineListTopWord_append sourcePath capA cupA, ← splitA]
    exact valleyA.spineListTopWord_spine
  have topB : spineListTopWord (spineListTopWord sourcePath capA) cupB = targetPath := by
    rw [sharedMid, ← spineListTopWord_append sourcePath capB cupB, ← splitB]
    exact valleyB.spineListTopWord_spine
  have cupTopWordEq :
      spineListTopWord (spineListTopWord sourcePath capA) cupA
        = spineListTopWord (spineListTopWord sourcePath capA) cupB :=
    topA.trans topB.symm
  -- Fire the r36 producer with the seven derived word arguments, transporting back through the block splits.
  rw [splitA, splitB]
  exact stringMidZeroValleysWithEqualMatching_spineTraceEquiv sourcePath.length sourcePos
    sourcePath (spineListTopWord sourcePath capA) capA capB cupA cupB
    capPureA capPureB cupPureA cupPureB cupChainedA cupChainedB wholeChainedA wholeChainedB
    capWordA capWordB cupWordA cupWordB cupTopWordEq midZeroFirst wholeEq

/-! ## Concrete truth-probe (anti-vacuity) — the cross-level valley `ε` then `η'` at the cell level -/

/-- ★ **The cell-level reducer FIRES on the genuine cross-level valley.**  Instantiating the discharged
`StringMidZeroValleyTraceEquiv` on `stringCrossLevelCell : G·F ⇒ G·H` (the lower counit `ε` vertically composed with
the upper unit `η'`) as BOTH valleys runs the WHOLE reducer end-to-end: block-split extracts `capBlock = [ε]`,
`cupBlock = [η']`; the derivation supplies all seven word arguments; the producer closes.  The concrete hypotheses
are machine-checked (`decide`): the spine is a cap-then-cup valley, `stringGF` has positive length `2`, and the
cap `ε` consumes both bottom wires so the mid-width is `0` — a genuine positive-source mid-width-`0` valley.  This
probe is DIAGONAL, though: it feeds the SAME cell `stringCrossLevelCell` as both valleys, so its conclusion is
`SpineTraceEquiv X X` with `X := stringCrossLevelCell.spine`, which `SpineTraceEquiv.refl X` proves outright — the
probe exercises the whole reducer machinery but establishes nothing `refl` could not.  The genuine NON-diagonal
witness (two SYNTACTICALLY DISTINCT spines with equal `matchingOf`, on which `SpineTraceEquiv.refl` FAILS with a type
mismatch) is `stringMidZeroValleyTraceEquiv_firesOnDistinctDoubleCap` (`StringMidZeroValleyDistinctFire`): the two
firing orders of the disjoint double-cap `ε ▷ (G·F)` / `(G·F) ◁ ε` then `ε` on `G·F·G·F ⇒ id_tip` (bottomCount `4`,
mid-width `0`, equal `matchingOf`, leftContext-length spine projections `[0, 0]` vs `[2, 0]`). -/
theorem stringMidZeroValleyTraceEquiv_firesOnCrossLevelValley :
    SpineTraceEquiv adjointTripleModeSignature stringCrossLevelCell.spine stringCrossLevelCell.spine :=
  stringMidZeroValleyTraceEquiv_holds stringCrossLevelCell stringCrossLevelCell
    (by decide) (by decide) rfl (by decide) (by decide)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the mid-width-`0` valley determinacy sub-producer is INHABITED UNCONDITIONALLY, zero-axiom
(FC-3 r38).**  `stringMidZeroValleyTraceEquiv_holds : StringMidZeroValleyTraceEquiv` — one of the THREE colour-keyed
sub-producers `StringValleyDegenerateSplit` named — now holds with no open hypothesis.  The cell-level reducer
block-splits the two `RawTwoCellExpr` valleys and DERIVES the seven boundary-word arguments the r36 producer
`stringMidZeroValleysWithEqualMatching_spineTraceEquiv` takes as hypotheses:

  * ★ **Brick A** `stringSpineBoundaryChained_cupSuffix_ofCapPrefix` — the numeric cup-suffix chain restriction at
    `adjointTripleModeSignature` (per-file re-copy of the `adjunctionModeSignature`-hardcoded shipped lemma; the
    proof is signature-blind, riding `stepAtom_openWires_tracksBoundary`);
  * ★ **Brick B** `spineBoundaryWordChained_cupSuffix_ofCapPrefix` — the `{signature}`-generic WORD-chain drop (the
    W4-suffix companion to the shipped W1-W3), structural on the cap prefix, no arity read;
  * the cap word chain by the shipped W3 `spineBoundaryWordChained_prefix_ofAppend`; the shared cap top word by the
    r37 brick `stringSharedMidWord_ofMidZero` (transporting the second cup's word chain across `sharedMid`); the
    shared cup top word by the top-word append law `spineListTopWord_append` folded against both
    `RawTwoCellExpr.spineListTopWord_spine`.

The truth-probe `stringMidZeroValleyTraceEquiv_firesOnCrossLevelValley` fires the whole reducer on the genuine
cross-level valley `ε` then `η'` (`stringCrossLevelCell : G·F ⇒ G·H`, source length `2`, mid-width `0`), with the
concrete valley / positivity / mid-`0` hypotheses machine-checked — but as BOTH valleys, so it is DIAGONAL
(conclusion `SpineTraceEquiv X X`, `refl`-provable); the genuine non-diagonal distinct-pair witness is
`stringMidZeroValleyTraceEquiv_firesOnDistinctDoubleCap` (`StringMidZeroValleyDistinctFire`).

  What this does NOT flip (honestly): the completeness masters `fxString_hasAdjointTripleCompleteness`
  (`StringMatchingCompleteness`) and `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) stay `false`.  This
  reducer discharges ONE of the three colour-keyed sub-producers, reducing the standing residual from three bricks to
  TWO: `StringWidthZeroPureCupDeterminacyShared` (the width-`0` colour-aware SORT) and
  `StringCellValleyTraceEquivPositive` (the doubly-positive colour-aware SORT) remain the un-ported walls.  The beam
  `StringMatchingReductsShareSpineTrace` still consumes those two as hypotheses; no master flips.  This round flips
  ONLY this NEW marker.  `= true`. -/
def fxString_hasMidZeroValleyCellReducer : Bool := true

end FX1Poly.Polygraph
