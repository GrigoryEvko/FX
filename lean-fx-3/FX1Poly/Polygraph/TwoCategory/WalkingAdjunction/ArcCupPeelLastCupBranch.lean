import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupPeelLastAssembly
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupBubbleToBack

/-! # ArcCupPeelLastCupBranch — the CUP branch of the peel-last obligation, MECHANIZED modulo two named pins

`ArcCupPeelLastAssembly` reduced the whole walking-adjunction cell reconstruction to the peel-LAST per-atom
obligation `SpineArcLastExtractionChained`, and shipped the CUP-branch anchor `lastCup_sharedShortChord_ofArcEqual`
(the second spine's own arc carries the peeled cup's TOP short chord at the arc-determined port — the honest
replacement for the refuted head windowPin) plus the block-level back carrier `ArcCupBubbleToBack`
(`BubblesToBack` + `atomicTraceEquiv_of_bubblesToBack` + `spineBoundaryChained_of_bubblesToBack`).  What was
missing was the ASSEMBLY that consumes a LOCATED owner cup and its back-bubble and lands the obligation's
existential.  This file ships that assembly — the peel-last analog of the head route's
`arcCupCase_locateAndBubble` feeding `cupHeadExtractionConclusion_ofLocatedBubbleWindowAndCancel`.

The obligation's conclusion is a threefold existential over `matchedInit`:

  1. `SpineTraceEquiv secondList (matchedInit ++ [lastAtom])` — the realized back-bubble;
  2. `SpineBoundaryChained bottomCount matchedInit` — the remainder stays chained;
  3. `arcStructureOfSpineList bottomCount initList = arcStructureOfSpineList bottomCount matchedInit` — the
     peeled remainder matches the reference tail's arc structure.

With `matchedInit := prefixAtoms ++ movedSuffixAtoms` (the owner cup bubbled to the back and the trailing image
peeled off), parts (1) and (2) are DISCHARGED here, MECHANICALLY, from the located split + the `BubblesToBack`
witness + the moved-image pin:

  * ★ `arcLastCupCase_backBubbleTraceEquiv` — part (1): the prefix-lifted back-bubble
    (`spineTraceEquiv_of_bubblesToBack_withPrefix`) carries `secondList = prefixAtoms ++ ownerCup :: suffixAtoms`
    to `prefixAtoms ++ (movedSuffixAtoms ++ [movedTarget])`; a STRUCTURAL append-reassociation (`listAppendAssoc`,
    zero-axiom — the Init `List.append_assoc` leaks `propext`) rebrackets it to `(prefixAtoms ++ movedSuffixAtoms)
    ++ [movedTarget]`, and the pin `movedTarget = lastAtom` closes it.
  * ★ `arcLastCupCase_matchedInitChained` — part (2): the running boundary is preserved through the bubble
    (`spineBoundaryChained_of_bubblesToBack` threaded past the fixed prefix by `spineBoundaryChained_replaceTail`),
    then the trailing image is dropped by the shipped `spineBoundaryChained_prefix_ofAppend`.
  * ★ `arcLastCupCase_extractionConclusion_ofLocatedBackBubbleAndCancel` — the full CUP-branch conclusion of
    `SpineArcLastExtractionChained`, consuming the located split, the back-bubble witness, the moved-image pin,
    the second spine's chain, and the arc-cancellation (part (3)) as a hypothesis.

## The exact residual this ISOLATES (does NOT discharge)

The cup branch of `SpineArcLastExtractionChained` now reduces to exactly THREE named inputs, none of which this
file invents:

  * the OWNER-LOCATE split `secondList = prefixAtoms ++ ownerCup :: suffixAtoms` at the arc-determined port
    (`lastCup_sharedShortChord_ofArcEqual` anchors the target chord `[p, p+1]` at `p = bottomCount +
    lastCup.leftContext.length`, but pinning `ownerCup` to that port — and the right-disjointness that lets it
    bubble to the back at all — is unbuilt), TOGETHER with the `BubblesToBack` witness (the geometric fact that a
    boundary cup's legs are unobstructed by its suffix, so the back-bubble EXISTS — NOT unconditional, unlike the
    front bubble, since `adjunctionCupPastAtomWindowDichotomy` gives `w <= wP` or `wP + P.cod <= w`, neither the
    right-of `w + cup.cod <= wP` the back step needs);
  * the moved-image pin `movedTarget = lastAtom` (the peel-last analog of the still-open head `windowPin`);
  * the arc-cancellation part (3) — the mixed `dropLastCup_arc_injective` on the interior (the shipped
    `ArcCupStepDrop` version needs `AllCupArity`, pure-cup only).

So this brick converts "cup branch" from an opaque obligation into "TWO mechanical parts (shipped) + THREE named
geometric residuals", exactly parallel to how the head route isolated `windowPin` + `tailsCancel`.  No gate flip;
`fxMode_hasArcStructureReconstruction` stays `false`.

Raw Lean 4 + Init; structural list/chain recursion, only `List.cons_append` (`rfl`) reductions — the append
reassociation is a hand-rolled structural induction (the Init `List.append_assoc` leaks `propext`).  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

universe u

namespace FX1Poly.Polygraph

/-! ## Structural append reassociation (the Init `List.append_assoc` leaks `propext`) -/

/-- **Append associativity, hand-rolled structurally.**  `(firstList ++ secondList) ++ thirdList
= firstList ++ (secondList ++ thirdList)` by structural recursion on `firstList`: the nil case is `rfl`
(`[] ++ x` reduces), the cons case re-cons-es the head over the recursive equality (`List.cons_append` is `rfl`
on both sides).  The Init `List.append_assoc` depends on `propext` in this toolchain; this copy does not. -/
private theorem listAppendAssoc {Elem : Type u} :
    (firstList secondList thirdList : List Elem) →
      (firstList ++ secondList) ++ thirdList = firstList ++ (secondList ++ thirdList)
  | [], _, _ => rfl
  | headElem :: restFirst, secondList, thirdList =>
      congrArg (fun tailList => headElem :: tailList) (listAppendAssoc restFirst secondList thirdList)

/-! ## Replacing a boundary-chained tail past a fixed prefix -/

/-- **Replace a chained tail past a fixed prefix.**  If some boundary transfer carries any chain of `origSuffix`
to a chain of `bubbledSuffix` at the SAME running boundary, then a chain of `prefixAtoms ++ origSuffix` becomes a
chain of `prefixAtoms ++ bubbledSuffix`: structural recursion on the prefix, peeling the head with cons inversion
(`spineBoundaryChained_tail`) and re-consing it (`(head :: rest) ++ x` reduces by `List.cons_append`) over the
recursive replacement, the base being the transfer itself.  This threads
`spineBoundaryChained_of_bubblesToBack` (universally quantified over the boundary) past the located prefix. -/
private theorem spineBoundaryChained_replaceTail {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (prefixAtoms : List (SpineAtom signature sourceMode targetMode))
    {origSuffix bubbledSuffix : List (SpineAtom signature sourceMode targetMode)}
    (transfer : ∀ {boundaryLength : Nat},
        SpineBoundaryChained boundaryLength origSuffix →
        SpineBoundaryChained boundaryLength bubbledSuffix) :
    ∀ {boundaryLength : Nat},
      SpineBoundaryChained boundaryLength (prefixAtoms ++ origSuffix) →
      SpineBoundaryChained boundaryLength (prefixAtoms ++ bubbledSuffix) := by
  induction prefixAtoms with
  | nil => intro _boundaryLength chained; exact transfer chained
  | cons headAtom restPrefix inductionHypothesis =>
      intro _boundaryLength chained
      obtain ⟨headFiresAtBoundary, tailChained⟩ := spineBoundaryChained_tail chained
      exact SpineBoundaryChained.cons headAtom headFiresAtBoundary (inductionHypothesis tailChained)

/-! ## Part (1) — the realized back-bubble trace equivalence -/

/-- ★ **Part (1) of the cup-branch conclusion — the realized back-bubble.**  Given the located split
`secondList = prefixAtoms ++ ownerCup :: suffixAtoms`, a `BubblesToBack` witness carrying `ownerCup` rightward to
the back as `movedTarget`, and the moved-image pin `movedTarget = lastAtom`, the second spine is `SpineTraceEquiv`
to `(prefixAtoms ++ movedSuffixAtoms) ++ [lastAtom]` — the peeled remainder with the last cup at the back.  The
prefix-lifted back-bubble (`spineTraceEquiv_of_bubblesToBack_withPrefix`) lands `prefixAtoms ++ (movedSuffixAtoms
++ [movedTarget])`; the structural `listAppendAssoc` rebrackets and the pin closes. -/
theorem arcLastCupCase_backBubbleTraceEquiv
    {overallSource overallTarget : adjunctionGraph.Mode}
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (ownerCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (suffixAtoms movedSuffixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (movedTarget lastAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (witness : BubblesToBack ownerCup suffixAtoms movedTarget movedSuffixAtoms)
    (movedIsLast : movedTarget = lastAtom) :
    SpineTraceEquiv adjunctionModeSignature (prefixAtoms ++ ownerCup :: suffixAtoms)
      ((prefixAtoms ++ movedSuffixAtoms) ++ [lastAtom]) := by
  have withPrefix := spineTraceEquiv_of_bubblesToBack_withPrefix prefixAtoms witness
  rw [movedIsLast] at withPrefix
  rw [listAppendAssoc prefixAtoms movedSuffixAtoms [lastAtom]]
  exact withPrefix

/-! ## Part (2) — the matched remainder stays boundary-chained -/

/-- ★ **Part (2) of the cup-branch conclusion — the matched remainder is boundary-chained.**  Given the located
split's chain (`secondList = prefixAtoms ++ ownerCup :: suffixAtoms` chained at `bottomCount`) and the
`BubblesToBack` witness, the remainder `prefixAtoms ++ movedSuffixAtoms` is chained at `bottomCount`.  The bubble
preserves the running boundary (`spineBoundaryChained_of_bubblesToBack`, universally over the boundary), threaded
past the fixed prefix by `spineBoundaryChained_replaceTail` to chain `prefixAtoms ++ (movedSuffixAtoms ++
[movedTarget])`; the structural `listAppendAssoc` rebrackets and the shipped `spineBoundaryChained_prefix_ofAppend`
drops the trailing image. -/
theorem arcLastCupCase_matchedInitChained
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (ownerCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (suffixAtoms movedSuffixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (witness : BubblesToBack ownerCup suffixAtoms movedTarget movedSuffixAtoms)
    (chained : SpineBoundaryChained bottomCount (prefixAtoms ++ ownerCup :: suffixAtoms)) :
    SpineBoundaryChained bottomCount (prefixAtoms ++ movedSuffixAtoms) := by
  have chainedBubbled :
      SpineBoundaryChained bottomCount (prefixAtoms ++ (movedSuffixAtoms ++ [movedTarget])) :=
    spineBoundaryChained_replaceTail prefixAtoms
      (spineBoundaryChained_of_bubblesToBack witness) chained
  rw [← listAppendAssoc prefixAtoms movedSuffixAtoms [movedTarget]] at chainedBubbled
  exact spineBoundaryChained_prefix_ofAppend (prefixAtoms ++ movedSuffixAtoms) [movedTarget]
    bottomCount chainedBubbled

/-! ## The CUP-branch conclusion of the peel-last obligation -/

/-- ★ **The CUP branch of `SpineArcLastExtractionChained`, assembled.**  Given the located owner split
`secondList = prefixAtoms ++ ownerCup :: suffixAtoms`, a `BubblesToBack` witness carrying `ownerCup` to the back,
the moved-image pin `movedTarget = lastAtom`, the second spine's chain, and the arc-cancellation
`arcStructureOfSpineList bottomCount initList = arcStructureOfSpineList bottomCount (prefixAtoms ++
movedSuffixAtoms)`, the peel-last obligation's threefold existential holds with `matchedInit := prefixAtoms ++
movedSuffixAtoms`: part (1) is `arcLastCupCase_backBubbleTraceEquiv`, part (2) is `arcLastCupCase_matchedInitChained`,
and part (3) is the arc-cancellation hypothesis.

This is the peel-last analog of the head route's
`cupHeadExtractionConclusion_ofLocatedBubbleWindowAndCancel`: parts (1)/(2) are mechanical trace/chain algebra,
and the residual is exactly the located split + back-bubble EXISTENCE, the moved-image pin, and the mixed
arc-cancellation. -/
theorem arcLastCupCase_extractionConclusion_ofLocatedBackBubbleAndCancel
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (initList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (ownerCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (suffixAtoms movedSuffixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (locatedSplit : secondList = prefixAtoms ++ ownerCup :: suffixAtoms)
    (witness : BubblesToBack ownerCup suffixAtoms movedTarget movedSuffixAtoms)
    (movedIsLast : movedTarget = lastAtom)
    (secondChained : SpineBoundaryChained bottomCount secondList)
    (arcCancel : arcStructureOfSpineList bottomCount initList
        = arcStructureOfSpineList bottomCount (prefixAtoms ++ movedSuffixAtoms)) :
    ∃ matchedInit,
      SpineTraceEquiv adjunctionModeSignature secondList (matchedInit ++ [lastAtom])
        ∧ SpineBoundaryChained bottomCount matchedInit
        ∧ arcStructureOfSpineList bottomCount initList
            = arcStructureOfSpineList bottomCount matchedInit := by
  subst locatedSplit
  exact ⟨prefixAtoms ++ movedSuffixAtoms,
    arcLastCupCase_backBubbleTraceEquiv prefixAtoms ownerCup suffixAtoms movedSuffixAtoms
      movedTarget lastAtom witness movedIsLast,
    arcLastCupCase_matchedInitChained bottomCount prefixAtoms ownerCup suffixAtoms
      movedSuffixAtoms movedTarget witness secondChained,
    arcCancel⟩

/-! ## Honesty marker -/

/-- **Honesty marker — the CUP branch of the peel-last obligation is MECHANIZED modulo two named pins.**
`arcLastCupCase_extractionConclusion_ofLocatedBackBubbleAndCancel` lands the full CUP-branch existential of
`SpineArcLastExtractionChained` from a located owner split, a `BubblesToBack` witness, the moved-image pin, the
second spine's chain, and the arc-cancellation.  The two block-algebra parts are discharged here:
`arcLastCupCase_backBubbleTraceEquiv` (the prefix-lifted back-bubble, rebracketed by the structural
`listAppendAssoc` and closed by the pin) and `arcLastCupCase_matchedInitChained` (the boundary chain threaded past
the prefix by `spineBoundaryChained_replaceTail` and trimmed by `spineBoundaryChained_prefix_ofAppend`).

What this marker does NOT claim: (i) the OWNER-LOCATE split at the arc-determined port
(`lastCup_sharedShortChord_ofArcEqual` anchors the target chord but does not pin the owner atom), (ii) the
`BubblesToBack` witness EXISTENCE (the back-bubble is NOT unconditional — a boundary cup's legs must be
unobstructed by its suffix, `adjunctionCupPastAtomWindowDichotomy` giving neither the right-of gap the back step
needs), (iii) the moved-image pin `movedTarget = lastAtom` (the peel-last analog of the still-open head
`windowPin`), (iv) the mixed arc-cancellation (the interior `dropLastCup_arc_injective`, shipped only under
`AllCupArity`).  So the cup branch is isolated onto (i)-(iv), the mechanical shell removed.  No gate flip;
`fxMode_hasArcStructureReconstruction` stays `false`.  `= true`. -/
def fxMode_hasArcPeelLastCupBranch : Bool := true

end FX1Poly.Polygraph
