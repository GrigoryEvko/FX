import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TaggedSwap
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SwapInversion

/-! # TaggedSwapChain — tagged chains, tagged determinacy, and the projection zip (FREE-7)

The determination rung (equal tag orders ⇒ equal reachable traces) is a zigzag induction,
and inducting over the raw `TaggedTraceEquiv` closure strands at the `symm`/`trans` arms —
the same obstruction `SwapChain.lean` solved for the untagged closure.  This file ships
the tagged mirror plus the determinacy layer the induction consumes:

  * `taggedListEqOfProjectionsEq` — ★ the projection zip: a tagged trace is determined by
    its atom list and its tag list together (the final reassembly step of every
    determination argument);
  * `TaggedSpineAtomSwap.tagListShape` — a tagged swap transposes the two head tags and
    fixes the rest;
  * `TaggedSpineAtomSwap.rhsDetermined` / `lhsDetermined` — ★ tagged swap determinacy in
    both directions: the untagged determinacy (`SwapInversion.lean`) pins the atoms, the
    tag-list shapes pin the tags, and the zip reassembles;
  * `OneTaggedAdjacentSwap` / `OneTaggedAdjacentSwapChain` — one tagged transposition at
    any depth in either direction, and its reflexive-transitive chain, with `symm` /
    `trans` / `consCongr` admissible (mirroring `SwapChain.lean` arm for arm);
  * `oneTaggedAdjacentSwapChain_iff_taggedTraceEquiv` — ★ the closure identification:
    tagged chains ARE the tagged trace equivalence, so determination may induct over
    chains of single positioned moves.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The projection zip -/

/-- ★ **The projection zip**: equal atom lists and equal tag lists reassemble to equal
tagged traces — a tagged trace is exactly the pair of its projections. -/
theorem taggedListEqOfProjectionsEq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (firstList secondList : List (TaggedSpineAtom signature sourceMode targetMode)) →
    untagSpineAtoms firstList = untagSpineAtoms secondList →
    spineTagList firstList = spineTagList secondList →
    firstList = secondList
  | [], [], _untagsEq, _tagsEq => rfl
  | [], _otherHead :: _otherRest, untagsEq, _tagsEq => nomatch untagsEq
  | _taggedHead :: _taggedRest, [], untagsEq, _tagsEq => nomatch untagsEq
  | taggedHead :: taggedRest, otherHead :: otherRest, untagsEq, tagsEq => by
      have untagsShaped : taggedHead.atom :: untagSpineAtoms taggedRest
          = otherHead.atom :: untagSpineAtoms otherRest := untagsEq
      have tagsShaped : taggedHead.occurrenceTag :: spineTagList taggedRest
          = otherHead.occurrenceTag :: spineTagList otherRest := tagsEq
      injection untagsShaped with atomsEq restUntagsEq
      injection tagsShaped with headTagsEq restTagsEq
      have headsEq : taggedHead = otherHead := by
        cases taggedHead with
        | mk firstTag firstAtom =>
            cases otherHead with
            | mk secondTag secondAtom =>
                have tagsReduced : firstTag = secondTag := headTagsEq
                have atomsReduced : firstAtom = secondAtom := atomsEq
                rw [tagsReduced, atomsReduced]
      rw [headsEq,
        taggedListEqOfProjectionsEq taggedRest otherRest restUntagsEq restTagsEq]

/-! ## Tagged swap determinacy -/

/-- A tagged swap transposes exactly its two head tags. -/
theorem TaggedSpineAtomSwap.tagListShape {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (TaggedSpineAtom signature overallSource overallTarget)}
    (swapStep : TaggedSpineAtomSwap signature firstList secondList) :
    ∃ (leftTag rightTag : Nat) (restTags : List Nat),
      spineTagList firstList = leftTag :: rightTag :: restTags ∧
      spineTagList secondList = rightTag :: leftTag :: restTags := by
  cases swapStep with
  | @swap _swapSourceMode _swapMiddleLeft _swapMiddleRight _swapTargetMode _oneCellFMid
      _oneCellFHigh _oneCellGLow _oneCellGMid _generatorLeft _generatorRight leftTag
      rightTag _leftAcc _inertPath _rightAcc rest =>
      exact ⟨leftTag, rightTag, spineTagList rest, rfl, rfl⟩

/-- ★ **Tagged determinacy, forward**: two tagged swaps out of the same list land in the
same list — untagged determinacy pins the atoms, the tag-list shapes pin the tags, the
zip reassembles. -/
theorem TaggedSpineAtomSwap.rhsDetermined {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sharedLhs rhsOne rhsTwo :
      List (TaggedSpineAtom signature overallSource overallTarget)}
    (swapOne : TaggedSpineAtomSwap signature sharedLhs rhsOne)
    (swapTwo : TaggedSpineAtomSwap signature sharedLhs rhsTwo) :
    rhsOne = rhsTwo := by
  have untagsEq : untagSpineAtoms rhsOne = untagSpineAtoms rhsTwo :=
    SpineAtomSwap.rhsDetermined swapOne.untagged swapTwo.untagged
  obtain ⟨leftTagOne, rightTagOne, restTagsOne, lhsShapeOne, rhsShapeOne⟩ :=
    swapOne.tagListShape
  obtain ⟨leftTagTwo, rightTagTwo, restTagsTwo, lhsShapeTwo, rhsShapeTwo⟩ :=
    swapTwo.tagListShape
  have lhsTagsAgree : leftTagOne :: rightTagOne :: restTagsOne
      = leftTagTwo :: rightTagTwo :: restTagsTwo := lhsShapeOne.symm.trans lhsShapeTwo
  injection lhsTagsAgree with leftTagsEq tailTagsAgree
  injection tailTagsAgree with rightTagsEq restTagsAgree
  have tagsEq : spineTagList rhsOne = spineTagList rhsTwo := by
    rw [rhsShapeOne, rhsShapeTwo, leftTagsEq, rightTagsEq, restTagsAgree]
  exact taggedListEqOfProjectionsEq rhsOne rhsTwo untagsEq tagsEq

/-- ★ **Tagged determinacy, backward**: two tagged swaps into the same list start from
the same list — the mirror through the untagged backward determinacy. -/
theorem TaggedSpineAtomSwap.lhsDetermined {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {lhsOne lhsTwo sharedRhs :
      List (TaggedSpineAtom signature overallSource overallTarget)}
    (swapOne : TaggedSpineAtomSwap signature lhsOne sharedRhs)
    (swapTwo : TaggedSpineAtomSwap signature lhsTwo sharedRhs) :
    lhsOne = lhsTwo := by
  have untagsEq : untagSpineAtoms lhsOne = untagSpineAtoms lhsTwo :=
    SpineAtomSwap.lhsDetermined swapOne.untagged swapTwo.untagged
  obtain ⟨leftTagOne, rightTagOne, restTagsOne, lhsShapeOne, rhsShapeOne⟩ :=
    swapOne.tagListShape
  obtain ⟨leftTagTwo, rightTagTwo, restTagsTwo, lhsShapeTwo, rhsShapeTwo⟩ :=
    swapTwo.tagListShape
  have rhsTagsAgree : rightTagOne :: leftTagOne :: restTagsOne
      = rightTagTwo :: leftTagTwo :: restTagsTwo := rhsShapeOne.symm.trans rhsShapeTwo
  injection rhsTagsAgree with rightTagsEq tailTagsAgree
  injection tailTagsAgree with leftTagsEq restTagsAgree
  have tagsEq : spineTagList lhsOne = spineTagList lhsTwo := by
    rw [lhsShapeOne, lhsShapeTwo, leftTagsEq, rightTagsEq, restTagsAgree]
  exact taggedListEqOfProjectionsEq lhsOne lhsTwo untagsEq tagsEq

/-! ## One tagged swap, anywhere, either direction -/

/-- One tagged adjacent transposition, in either direction, at any depth. -/
inductive OneTaggedAdjacentSwap (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} :
    List (TaggedSpineAtom signature overallSource overallTarget) →
    List (TaggedSpineAtom signature overallSource overallTarget) → Prop where
  /-- The swap at the head, along the constructor direction. -/
  | here {firstList secondList :
      List (TaggedSpineAtom signature overallSource overallTarget)} :
      TaggedSpineAtomSwap signature firstList secondList →
      OneTaggedAdjacentSwap signature firstList secondList
  /-- The swap at the head, against the constructor direction. -/
  | hereReversed {firstList secondList :
      List (TaggedSpineAtom signature overallSource overallTarget)} :
      TaggedSpineAtomSwap signature secondList firstList →
      OneTaggedAdjacentSwap signature firstList secondList
  /-- The swap sits deeper (an untouched head atom passes through). -/
  | deeper (taggedAtom : TaggedSpineAtom signature overallSource overallTarget)
      {firstList secondList :
        List (TaggedSpineAtom signature overallSource overallTarget)} :
      OneTaggedAdjacentSwap signature firstList secondList →
      OneTaggedAdjacentSwap signature (taggedAtom :: firstList)
        (taggedAtom :: secondList)

/-- One tagged adjacent swap is symmetric by construction. -/
theorem OneTaggedAdjacentSwap.symm {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (TaggedSpineAtom signature overallSource overallTarget)}
    (oneSwap : OneTaggedAdjacentSwap signature firstList secondList) :
    OneTaggedAdjacentSwap signature secondList firstList := by
  induction oneSwap with
  | here swapStep => exact OneTaggedAdjacentSwap.hereReversed swapStep
  | hereReversed swapStep => exact OneTaggedAdjacentSwap.here swapStep
  | deeper taggedAtom _ innerHypothesis =>
      exact OneTaggedAdjacentSwap.deeper taggedAtom innerHypothesis

/-- One tagged adjacent swap includes into the tagged closure. -/
theorem OneTaggedAdjacentSwap.toTaggedTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (TaggedSpineAtom signature overallSource overallTarget)}
    (oneSwap : OneTaggedAdjacentSwap signature firstList secondList) :
    TaggedTraceEquiv signature firstList secondList := by
  induction oneSwap with
  | here swapStep => exact TaggedTraceEquiv.ofSwap swapStep
  | hereReversed swapStep =>
      exact TaggedTraceEquiv.symm (TaggedTraceEquiv.ofSwap swapStep)
  | deeper taggedAtom _ innerHypothesis =>
      exact TaggedTraceEquiv.consCongr taggedAtom innerHypothesis

/-! ## The tagged chain -/

/-- The reflexive-transitive chain of single tagged adjacent swaps. -/
inductive OneTaggedAdjacentSwapChain (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} :
    List (TaggedSpineAtom signature overallSource overallTarget) →
    List (TaggedSpineAtom signature overallSource overallTarget) → Prop where
  /-- The empty chain. -/
  | refl (taggedList : List (TaggedSpineAtom signature overallSource overallTarget)) :
      OneTaggedAdjacentSwapChain signature taggedList taggedList
  /-- Advance by one tagged swap, then continue. -/
  | advance {firstList midList secondList :
      List (TaggedSpineAtom signature overallSource overallTarget)} :
      OneTaggedAdjacentSwap signature firstList midList →
      OneTaggedAdjacentSwapChain signature midList secondList →
      OneTaggedAdjacentSwapChain signature firstList secondList

/-- A one-step tagged chain. -/
theorem OneTaggedAdjacentSwapChain.single {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (TaggedSpineAtom signature overallSource overallTarget)}
    (oneSwap : OneTaggedAdjacentSwap signature firstList secondList) :
    OneTaggedAdjacentSwapChain signature firstList secondList :=
  OneTaggedAdjacentSwapChain.advance oneSwap
    (OneTaggedAdjacentSwapChain.refl secondList)

/-- Tagged chains append. -/
theorem OneTaggedAdjacentSwapChain.trans {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList thirdList :
      List (TaggedSpineAtom signature overallSource overallTarget)}
    (firstChain : OneTaggedAdjacentSwapChain signature firstList secondList)
    (secondChain : OneTaggedAdjacentSwapChain signature secondList thirdList) :
    OneTaggedAdjacentSwapChain signature firstList thirdList := by
  induction firstChain with
  | refl _ => exact secondChain
  | advance headSwap _ innerHypothesis =>
      exact OneTaggedAdjacentSwapChain.advance headSwap (innerHypothesis secondChain)

/-- Tagged chains reverse (each step is symmetric, appended in reverse order). -/
theorem OneTaggedAdjacentSwapChain.symm {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (TaggedSpineAtom signature overallSource overallTarget)}
    (chain : OneTaggedAdjacentSwapChain signature firstList secondList) :
    OneTaggedAdjacentSwapChain signature secondList firstList := by
  induction chain with
  | refl taggedList => exact OneTaggedAdjacentSwapChain.refl taggedList
  | advance headSwap _ innerHypothesis =>
      exact innerHypothesis.trans (OneTaggedAdjacentSwapChain.single headSwap.symm)

/-- Tagged chains map under a head cons (every step moves deeper). -/
theorem OneTaggedAdjacentSwapChain.consCongr {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (taggedAtom : TaggedSpineAtom signature overallSource overallTarget)
    {firstList secondList : List (TaggedSpineAtom signature overallSource overallTarget)}
    (chain : OneTaggedAdjacentSwapChain signature firstList secondList) :
    OneTaggedAdjacentSwapChain signature (taggedAtom :: firstList)
      (taggedAtom :: secondList) := by
  induction chain with
  | refl taggedList => exact OneTaggedAdjacentSwapChain.refl (taggedAtom :: taggedList)
  | advance headSwap _ innerHypothesis =>
      exact OneTaggedAdjacentSwapChain.advance
        (OneTaggedAdjacentSwap.deeper taggedAtom headSwap) innerHypothesis

/-! ## The closure identification -/

/-- Tagged chains include into the tagged closure. -/
theorem OneTaggedAdjacentSwapChain.toTaggedTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (TaggedSpineAtom signature overallSource overallTarget)}
    (chain : OneTaggedAdjacentSwapChain signature firstList secondList) :
    TaggedTraceEquiv signature firstList secondList := by
  induction chain with
  | refl taggedList => exact TaggedTraceEquiv.refl taggedList
  | advance headSwap _ innerHypothesis =>
      exact TaggedTraceEquiv.trans headSwap.toTaggedTraceEquiv innerHypothesis

/-- The tagged closure flattens into a chain — every closure operator is admissible for
chains, so the induction goes arm by arm. -/
theorem TaggedTraceEquiv.toOneTaggedAdjacentSwapChain {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (TaggedSpineAtom signature overallSource overallTarget)}
    (traceEquiv : TaggedTraceEquiv signature firstList secondList) :
    OneTaggedAdjacentSwapChain signature firstList secondList := by
  induction traceEquiv with
  | ofSwap swapStep =>
      exact OneTaggedAdjacentSwapChain.single (OneTaggedAdjacentSwap.here swapStep)
  | refl taggedList => exact OneTaggedAdjacentSwapChain.refl taggedList
  | symm _ innerHypothesis => exact innerHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis
  | consCongr taggedAtom _ innerHypothesis =>
      exact OneTaggedAdjacentSwapChain.consCongr taggedAtom innerHypothesis

/-- ★ **The tagged closure identification**: single-tagged-swap chains ARE the tagged
trace equivalence — the determination zigzag may induct over chains of single positioned
moves instead of the raw closure. -/
theorem oneTaggedAdjacentSwapChain_iff_taggedTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (firstList secondList : List (TaggedSpineAtom signature overallSource overallTarget)) :
    OneTaggedAdjacentSwapChain signature firstList secondList
      ↔ TaggedTraceEquiv signature firstList secondList :=
  ⟨OneTaggedAdjacentSwapChain.toTaggedTraceEquiv,
    TaggedTraceEquiv.toOneTaggedAdjacentSwapChain⟩

end FX1Poly.Polygraph
