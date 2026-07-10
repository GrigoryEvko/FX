import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineAtomWordPin
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringInterleavedWindowSort
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryWordChain

/-! # WalkingString — the POSITIVE-CORE OPENING: the cap-block Godement-step chain + the word-pin base case
(FC-3 r10, B3)

The doubly-positive sub-producer `StringCellValleyTraceEquivPositive` (source width positive, mid width positive)
is the LAST of the three colour-keyed residuals; its full discharge is the inversion-decreasing fueled two-block
sort (r11+).  This file lands the OPENING the recon scoped — the scaffolding the r11 block-equality induction runs
on, riding ONLY shipped atoms (the transposition atom and the keystone word pin), with no new hard node:

  * ★ `StringCapBlockGodementChain` — the reflexive-transitive closure of the one-Godement-step relation on a cap
    block: two cap blocks are chained when one is reached from the other by a sequence of adjacent horizontally-
    independent transpositions (`SpineAtomSwap`).  This is the relation the sort's REORDERINGS live in.
  * ★ `stringCapBlockGodementChain_spineTraceEquiv` — a chain lifts to `SpineTraceEquiv` (each step by the shipped
    transposition atom `stringSpineAtomSwap_spineTraceEquiv`, glued by `SpineTraceEquiv.trans`; the base case is
    `refl`).  So "reachable by Godement steps ⟹ trace-equivalent" — the trace-equivalence the r11 sort delivers,
    scaffolded.
  * ★ `stringWordChainedSingletonBlock_eq_of_readOffs` — **the base case**, discharged by the keystone.  Two
    singleton blocks word-chained at the SAME running boundary word with equal left-context and generator-dom
    read-off lengths are EQUAL (the two `headFires` decompositions supply the keystone's `wordEq`, and
    `stringSpineAtom_eq_of_wordReadOffs` pins the atom colour-aware).  This is the recon's "0 inversions ⟹ the two
    blocks are identical — word pin at each position", at the length-1 block; the r11 induction peels one atom and
    recurses, applying this pin at each position.

## The measure (the r11 induction scaffold, named)

The r11 induction is STRUCTURAL on the cap block (peel-and-pin): the head atoms are pinned equal by the keystone
(the base-case lemma here, generalized to the head of a `cons`), then the tails recurse — so the measure is the
block LENGTH.  The cup/cap disorder `spineDisorder` (`SpineValleyDisorder`) is NOT the intra-block measure: a PURE
cap block has all-cap tags, hence `spineDisorder = 0` (it is already a cup/cap valley), so it is blind to the colour
order WITHIN the block — the r11 induction sorts the block by its boundary-word colour order, decreasing the
block-length / transposition-count measure, with the base case shipped here.

## What this file does NOT do (the flag stays `false` — honestly)

The chain scaffold and the singleton base case are the OPENING; `StringCellValleyTraceEquivPositive`
(`StringValleyDegenerateSplit`) is NOT inhabited — the full two-block sort (the partner-locate-by-chord port, the
matching-injective drop, the width-telescope / chain-restrict ports) is the r11+ content.  So
`fxString_hasAdjointTripleCompleteness` stays `false`; this file scopes the positive core and discharges its base
case, honestly.

Raw Lean 4 + Init; the chain lift is induction on the chain, the base case is the keystone pin fed by the word-chain
cons inversion.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The cap-block Godement-step chain -/

/-- ★ **The cap-block Godement-step chain.**  The reflexive-transitive closure of the one-step relation "reached by
one adjacent horizontally-independent transposition (`SpineAtomSwap`)".  The relation the pure-block sort's
reorderings live in — two cap blocks are chained exactly when a sequence of adjacent Godement transpositions carries
one to the other. -/
inductive StringCapBlockGodementChain {overallSource overallTarget : adjointTripleGraph.Mode} :
    List (SpineAtom adjointTripleModeSignature overallSource overallTarget) →
    List (SpineAtom adjointTripleModeSignature overallSource overallTarget) → Prop where
  /-- The empty chain: a block is chained to itself. -/
  | refl (block : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
      StringCapBlockGodementChain block block
  /-- One more adjacent transposition in front of a chain. -/
  | step {blockBefore blockMid blockAfter :
        List (SpineAtom adjointTripleModeSignature overallSource overallTarget)}
      (swapStep : SpineAtomSwap adjointTripleModeSignature blockBefore blockMid)
      (restChain : StringCapBlockGodementChain blockMid blockAfter) :
      StringCapBlockGodementChain blockBefore blockAfter

/-- ★ **A cap-block Godement chain lifts to a spine trace equivalence.**  Each transposition step is a
`SpineTraceEquiv` (the shipped transposition atom `stringSpineAtomSwap_spineTraceEquiv`); the chain glues them by
`SpineTraceEquiv.trans`, with the base case `refl`.  So "reachable by Godement steps ⟹ trace-equivalent" — the
trace-equivalence the r11 positive-core sort delivers, scaffolded on shipped atoms. -/
theorem stringCapBlockGodementChain_spineTraceEquiv
    {overallSource overallTarget : adjointTripleGraph.Mode}
    {blockBefore blockAfter :
      List (SpineAtom adjointTripleModeSignature overallSource overallTarget)}
    (chain : StringCapBlockGodementChain blockBefore blockAfter) :
    SpineTraceEquiv adjointTripleModeSignature blockBefore blockAfter := by
  induction chain with
  | refl block => exact SpineTraceEquiv.refl block
  | step swapStep _restChain restEquiv =>
      exact SpineTraceEquiv.trans (stringSpineAtomSwap_spineTraceEquiv swapStep) restEquiv

/-! ## The base case — the word pin at a single position -/

/-- ★ **The positive-core induction base case, discharged by the keystone.**  Two singleton blocks
`[atomFirst]` / `[atomSecond]` word-chained at the SAME running boundary word, with equal left-context and
generator-dom read-off lengths, are EQUAL: the two `headFires` decompositions of the shared boundary word supply the
keystone's `wordEq`, and `stringSpineAtom_eq_of_wordReadOffs` pins the atom colour-aware (its cod / generator read
off the dom word, no length rigidity).  This is the recon's "0 inversions ⟹ the two blocks are identical — word pin
at each position", at the length-1 block; the r11 sort peels one atom and applies this pin per position. -/
theorem stringWordChainedSingletonBlock_eq_of_readOffs
    {overallSource overallTarget : adjointTripleGraph.Mode}
    {boundaryWord : ModalityPath adjointTripleGraph overallSource overallTarget}
    {atomFirst atomSecond : SpineAtom adjointTripleModeSignature overallSource overallTarget}
    (chainedFirst : SpineBoundaryWordChained boundaryWord [atomFirst])
    (chainedSecond : SpineBoundaryWordChained boundaryWord [atomSecond])
    (leftLengthsEqual : atomFirst.leftContext.length = atomSecond.leftContext.length)
    (domLengthsEqual : atomFirst.generatorDom.length = atomSecond.generatorDom.length) :
    [atomFirst] = [atomSecond] := by
  obtain ⟨headFiresFirst, _tailFirst⟩ := spineBoundaryWordChained_tail chainedFirst
  obtain ⟨headFiresSecond, _tailSecond⟩ := spineBoundaryWordChained_tail chainedSecond
  have wordEq :
      composePath atomFirst.leftContext
          (composePath atomFirst.generatorDom atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorDom atomSecond.rightContext) :=
    headFiresFirst.symm.trans headFiresSecond
  rw [stringSpineAtom_eq_of_wordReadOffs atomFirst atomSecond wordEq leftLengthsEqual
    domLengthsEqual]

/-! ## Non-vacuity — a concrete cap-block Godement step -/

/-- ★ **A cap-block Godement step, non-vacuously.**  Two upper counits `ε' = StringTwoCell.counitUpper`
(`H·G ⇒ id_base`), fired disjointly, transpose as a one-step `StringCapBlockGodementChain` whose lift is a genuine
`SpineTraceEquiv` — the composable cap-block reorder the positive-core sort iterates, at the minimal cap width. -/
theorem stringCapBlockGodementStep_nonvacuity :
    ∃ blockFirst blockSecond :
        List (SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base),
      StringCapBlockGodementChain blockFirst blockSecond
        ∧ SpineTraceEquiv adjointTripleModeSignature blockFirst blockSecond := by
  have windowSwap :=
    SpineAtomSwap.swap (signature := adjointTripleModeSignature)
      StringTwoCell.counitUpper StringTwoCell.counitUpper
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      []
  refine ⟨_, _, StringCapBlockGodementChain.step windowSwap (StringCapBlockGodementChain.refl _), ?_⟩
  exact stringCapBlockGodementChain_spineTraceEquiv
    (StringCapBlockGodementChain.step windowSwap (StringCapBlockGodementChain.refl _))

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the positive-core OPENING is shipped (FC-3 r10, B3).**  The cap-block Godement-step chain
(`StringCapBlockGodementChain`) and its lift to `SpineTraceEquiv` (`stringCapBlockGodementChain_spineTraceEquiv`,
each step the shipped transposition atom, base case `refl`) scaffold the r11 positive-core sort's reorderings; the
base case (`stringWordChainedSingletonBlock_eq_of_readOffs`) discharges the length-1 "0 inversions ⟹ identical" via
the keystone word pin `stringSpineAtom_eq_of_wordReadOffs`; non-vacuity `stringCapBlockGodementStep_nonvacuity`
exhibits a concrete two-cap transposition.  The r11 measure is the block LENGTH (structural peel-and-pin) — the cup/
cap `spineDisorder` is 0 on a pure cap block and blind to the intra-block colour order, so it is the wrong measure.

  What this marker does NOT close: `StringCellValleyTraceEquivPositive` (`StringValleyDegenerateSplit`) is NOT
  inhabited — the full two-block sort (partner-locate-by-chord port, matching-injective drop, width-telescope /
  chain-restrict ports) is the r11+ content.  So `fxString_hasAdjointTripleCompleteness` stays `false`, honestly,
  with the positive core scoped and its base case discharged.  `= true`. -/
def fxString_hasCapBlockGodementStepOpening : Bool := true

end FX1Poly.Polygraph
