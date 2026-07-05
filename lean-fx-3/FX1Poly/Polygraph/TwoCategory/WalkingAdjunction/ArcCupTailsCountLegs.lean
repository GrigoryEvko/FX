import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBubbleToFront
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcReconstruction
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking

/-! # ArcCupTailsCountLegs — the cup cancel's TOTAL-count legs are orbit-free (peel campaign H)

`tailsCancel` (the cup case's residual arc-structure equality
`arcStructureOfSpineList w tailList = arcStructureOfSpineList w (movedPrefix ++ suffix)`) decomposes
by `arcCupTailsCancel_ofDiagramAndCounts` into FIVE field-agreements: the boundary DIAGRAM, the two
TOTAL counts (`cupCount`, `capCount`), and the two PER-PORT internal counts (`internalCupCounts`,
`internalCapCounts`).  The prior ledger routed ALL four count legs through the through-the-head trace
orbit (the refuted unconditional cancel, `not_arcCupHeadCancellationUnconditional`).

This brick shows the TWO TOTAL-count legs are NOT orbit content — they follow unconditionally from
global count conservation.  The arc `cupCount` reads back the spine's cup-atom count
(`arcStructureOfSpineList_cupCount`, boundary-independent), and the bubble preserves every atom's
generator (each `BubblesToFront` step rewrites only the left/right whiskering contexts, so the
cup/cap indicator — a function of the generator arities alone — is invariant).  Together with the
whole-list arc equality, the peeled cup's `1` is accounted on both sides and the tails' total cup and
cap counts agree.

  * `cupAtomCount_append` / `capAtomCount_append` — the counts are additive over `++`;
  * `bubblesToFront_cupAtomCount` / `bubblesToFront_capAtomCount` — the bubble preserves the count of
    the moved bundle (generator-arity invariance, one transposition per step);
  * ★ `arcCupCase_cupCountAgree` / `arcCupCase_capCountAgree` — the two total-count legs of
    `tailsCancel`, discharged from the cup-case dispatch hypotheses alone (NO orbit).

So the genuine orbit residual for the cup cancel shrinks from five legs to THREE: the diagram and the
two per-port internal counts.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Count additivity over concatenation -/

/-- **The cup-atom count is additive over `++`.**  Structural on the first list; each head contributes
its indicator, the tail recurses. -/
theorem cupAtomCount_append {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (firstAtoms secondAtoms : List (SpineAtom signature sourceMode targetMode)) →
    cupAtomCount (firstAtoms ++ secondAtoms)
      = cupAtomCount firstAtoms + cupAtomCount secondAtoms
  | [], secondAtoms => (Nat.zero_add _).symm
  | headAtom :: restAtoms, secondAtoms => by
      show (if headAtom.generatorDom.length == 0 && headAtom.generatorCod.length == 2
              then (1 : Nat) else 0)
            + cupAtomCount (restAtoms ++ secondAtoms)
          = ((if headAtom.generatorDom.length == 0 && headAtom.generatorCod.length == 2
              then (1 : Nat) else 0)
            + cupAtomCount restAtoms) + cupAtomCount secondAtoms
      rw [cupAtomCount_append restAtoms secondAtoms, Nat.add_assoc]

/-- **The cap-atom count is additive over `++`** — the dual of `cupAtomCount_append`. -/
theorem capAtomCount_append {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (firstAtoms secondAtoms : List (SpineAtom signature sourceMode targetMode)) →
    capAtomCount (firstAtoms ++ secondAtoms)
      = capAtomCount firstAtoms + capAtomCount secondAtoms
  | [], secondAtoms => (Nat.zero_add _).symm
  | headAtom :: restAtoms, secondAtoms => by
      show (if headAtom.generatorDom.length == 2 && headAtom.generatorCod.length == 0
              then (1 : Nat) else 0)
            + capAtomCount (restAtoms ++ secondAtoms)
          = ((if headAtom.generatorDom.length == 2 && headAtom.generatorCod.length == 0
              then (1 : Nat) else 0)
            + capAtomCount restAtoms) + capAtomCount secondAtoms
      rw [capAtomCount_append restAtoms secondAtoms, Nat.add_assoc]

/-! ## The bubble preserves the moved bundle's count -/

/-- The transposition rearrangement `a + (p + m) = t + (p + r)` from `a + m = t + r`: the passed
atom's contribution `p` factors out over the inductive count agreement. -/
private theorem countRearrange (leftHead passedContrib movedTail rightHead restTail : Nat)
    (inner : leftHead + movedTail = rightHead + restTail) :
    leftHead + (passedContrib + movedTail) = rightHead + (passedContrib + restTail) := by
  rw [Nat.add_comm passedContrib movedTail, ← Nat.add_assoc leftHead movedTail passedContrib,
    inner, Nat.add_assoc rightHead restTail passedContrib,
    Nat.add_comm restTail passedContrib]

/-- **The bubble preserves the moved bundle's cup count.**  Each `BubblesToFront` step rewrites only
the whiskering contexts (record updates on `leftContext` / `rightContext`), so the cup indicator of
the moved target and of the passed atom equal their originals; the count is the inductive rearrangement
of a single transposition. -/
theorem bubblesToFront_cupAtomCount
    {overallSource overallTarget : adjunctionGraph.Mode}
    {target movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {prefixAtoms movedPrefixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (witness : BubblesToFront target prefixAtoms movedTarget movedPrefixAtoms) :
    cupAtomCount (movedTarget :: movedPrefixAtoms) = cupAtomCount (target :: prefixAtoms) := by
  induction witness with
  | nil => rfl
  | @stepRightOf passedAtom restPrefix movedTargetOfRest movedRestPrefix _ _ _ _
      inductionHypothesis =>
      show (if movedTargetOfRest.generatorDom.length == 0
              && movedTargetOfRest.generatorCod.length == 2 then (1 : Nat) else 0)
            + ((if passedAtom.generatorDom.length == 0
                  && passedAtom.generatorCod.length == 2 then (1 : Nat) else 0)
              + cupAtomCount movedRestPrefix)
          = (if target.generatorDom.length == 0
              && target.generatorCod.length == 2 then (1 : Nat) else 0)
            + ((if passedAtom.generatorDom.length == 0
                  && passedAtom.generatorCod.length == 2 then (1 : Nat) else 0)
              + cupAtomCount restPrefix)
      exact countRearrange _ _ _ _ _ inductionHypothesis
  | @stepLeftOf passedAtom restPrefix movedTargetOfRest movedRestPrefix _ _ _ _
      inductionHypothesis =>
      show (if movedTargetOfRest.generatorDom.length == 0
              && movedTargetOfRest.generatorCod.length == 2 then (1 : Nat) else 0)
            + ((if passedAtom.generatorDom.length == 0
                  && passedAtom.generatorCod.length == 2 then (1 : Nat) else 0)
              + cupAtomCount movedRestPrefix)
          = (if target.generatorDom.length == 0
              && target.generatorCod.length == 2 then (1 : Nat) else 0)
            + ((if passedAtom.generatorDom.length == 0
                  && passedAtom.generatorCod.length == 2 then (1 : Nat) else 0)
              + cupAtomCount restPrefix)
      exact countRearrange _ _ _ _ _ inductionHypothesis

/-- **The bubble preserves the moved bundle's cap count** — the dual of `bubblesToFront_cupAtomCount`. -/
theorem bubblesToFront_capAtomCount
    {overallSource overallTarget : adjunctionGraph.Mode}
    {target movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {prefixAtoms movedPrefixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (witness : BubblesToFront target prefixAtoms movedTarget movedPrefixAtoms) :
    capAtomCount (movedTarget :: movedPrefixAtoms) = capAtomCount (target :: prefixAtoms) := by
  induction witness with
  | nil => rfl
  | @stepRightOf passedAtom restPrefix movedTargetOfRest movedRestPrefix _ _ _ _
      inductionHypothesis =>
      show (if movedTargetOfRest.generatorDom.length == 2
              && movedTargetOfRest.generatorCod.length == 0 then (1 : Nat) else 0)
            + ((if passedAtom.generatorDom.length == 2
                  && passedAtom.generatorCod.length == 0 then (1 : Nat) else 0)
              + capAtomCount movedRestPrefix)
          = (if target.generatorDom.length == 2
              && target.generatorCod.length == 0 then (1 : Nat) else 0)
            + ((if passedAtom.generatorDom.length == 2
                  && passedAtom.generatorCod.length == 0 then (1 : Nat) else 0)
              + capAtomCount restPrefix)
      exact countRearrange _ _ _ _ _ inductionHypothesis
  | @stepLeftOf passedAtom restPrefix movedTargetOfRest movedRestPrefix _ _ _ _
      inductionHypothesis =>
      show (if movedTargetOfRest.generatorDom.length == 2
              && movedTargetOfRest.generatorCod.length == 0 then (1 : Nat) else 0)
            + ((if passedAtom.generatorDom.length == 2
                  && passedAtom.generatorCod.length == 0 then (1 : Nat) else 0)
              + capAtomCount movedRestPrefix)
          = (if target.generatorDom.length == 2
              && target.generatorCod.length == 0 then (1 : Nat) else 0)
            + ((if passedAtom.generatorDom.length == 2
                  && passedAtom.generatorCod.length == 0 then (1 : Nat) else 0)
              + capAtomCount restPrefix)
      exact countRearrange _ _ _ _ _ inductionHypothesis

/-! ## Cup-atom indicators at a cup head -/

/-- A cup atom's cup indicator is `1`. -/
private theorem cupIndicator_ofCup {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode)
    (dom0 : atom.generatorDom.length = 0) (cod2 : atom.generatorCod.length = 2) :
    (if atom.generatorDom.length == 0 && atom.generatorCod.length == 2 then (1 : Nat) else 0) = 1 := by
  rw [dom0, cod2]
  rfl

/-- A cup atom's cap indicator is `0`. -/
private theorem capIndicator_ofCup {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode)
    (dom0 : atom.generatorDom.length = 0) (cod2 : atom.generatorCod.length = 2) :
    (if atom.generatorDom.length == 2 && atom.generatorCod.length == 0 then (1 : Nat) else 0) = 0 := by
  rw [dom0, cod2]
  rfl

/-! ## The two total-count legs -/

/-- The lex arithmetic of the cup total-count leg: with the peeled cup contributing `1` on both the
whole-list and moved-bundle sides, the tail cup count equals the moved-bundle-plus-suffix count. -/
private theorem cupLegArith (tailCount movedPrefixCount suffixCount prefixCount toucherContrib : Nat)
    (wholeEq : 1 + tailCount = prefixCount + (toucherContrib + suffixCount))
    (bubble : 1 + movedPrefixCount = toucherContrib + prefixCount) :
    tailCount = movedPrefixCount + suffixCount := by
  have step : (1 : Nat) + tailCount = 1 + (movedPrefixCount + suffixCount) := by
    rw [wholeEq, ← Nat.add_assoc prefixCount toucherContrib suffixCount,
      Nat.add_comm prefixCount toucherContrib, ← bubble,
      Nat.add_assoc 1 movedPrefixCount suffixCount]
  have stepRight : tailCount + 1 = (movedPrefixCount + suffixCount) + 1 := by
    rw [Nat.add_comm tailCount 1, Nat.add_comm (movedPrefixCount + suffixCount) 1]
    exact step
  exact Nat.succ.inj stepRight

/-- The arithmetic of the cap total-count leg: the peeled cup contributes `0` to the cap count on both
sides. -/
private theorem capLegArith (tailCount movedPrefixCount suffixCount prefixCount toucherContrib : Nat)
    (wholeEq : 0 + tailCount = prefixCount + (toucherContrib + suffixCount))
    (bubble : 0 + movedPrefixCount = toucherContrib + prefixCount) :
    tailCount = movedPrefixCount + suffixCount := by
  rw [Nat.zero_add] at wholeEq bubble
  rw [wholeEq, bubble, ← Nat.add_assoc prefixCount toucherContrib suffixCount,
    Nat.add_comm prefixCount toucherContrib]

/-- ★ **The cup cancel's TOTAL cup-count leg, orbit-free.**  Given the cup-case dispatch data — a cup
head, a second spine split at a bubbled cup, and whole-list arc equality — the tail's total cup count
equals the moved-remainder's, discharging the `cupCountAgree` hypothesis of
`arcCupTailsCancel_ofDiagramAndCounts` with NO recourse to the orbit. -/
theorem arcCupCase_cupCountAgree
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList secondList prefixAtoms suffixAtoms movedPrefixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (toucherAtom movedTarget :
      SpineAtom adjunctionModeSignature overallSource overallTarget)
    (movedDomPin : movedTarget.generatorDom.length = 0)
    (doesSplitSpine : secondList = prefixAtoms ++ toucherAtom :: suffixAtoms)
    (witness : BubblesToFront toucherAtom prefixAtoms movedTarget movedPrefixAtoms)
    (arcEqual : arcStructureOfSpineList bottomCount (headAtom :: tailList)
        = arcStructureOfSpineList bottomCount secondList) :
    (arcStructureOfSpineList headAtom.codBoundaryLength tailList).cupCount
      = (arcStructureOfSpineList headAtom.codBoundaryLength (movedPrefixAtoms ++ suffixAtoms)).cupCount
    := by
  have movedCod : movedTarget.generatorCod.length = 2 := by
    cases adjunctionSpineAtom_hasCupOrCapArity movedTarget with
    | inl cupArity => exact cupArity.2
    | inr capArity => exact Nat.noConfusion (capArity.1.symm.trans movedDomPin)
  rw [arcStructureOfSpineList_cupCount, arcStructureOfSpineList_cupCount, cupAtomCount_append]
  have wholeCup : cupAtomCount (headAtom :: tailList) = cupAtomCount secondList := by
    have base := congrArg FullArcStructure.cupCount arcEqual
    rw [arcStructureOfSpineList_cupCount, arcStructureOfSpineList_cupCount] at base
    exact base
  have headInd : cupAtomCount (headAtom :: tailList) = 1 + cupAtomCount tailList := by
    show (if headAtom.generatorDom.length == 0 && headAtom.generatorCod.length == 2
            then (1 : Nat) else 0) + cupAtomCount tailList = 1 + cupAtomCount tailList
    rw [cupIndicator_ofCup headAtom hasCupDomArity hasCupCodArity]
  have movedInd : cupAtomCount (movedTarget :: movedPrefixAtoms)
      = 1 + cupAtomCount movedPrefixAtoms := by
    show (if movedTarget.generatorDom.length == 0 && movedTarget.generatorCod.length == 2
            then (1 : Nat) else 0) + cupAtomCount movedPrefixAtoms
        = 1 + cupAtomCount movedPrefixAtoms
    rw [cupIndicator_ofCup movedTarget movedDomPin movedCod]
  have wholeEq : 1 + cupAtomCount tailList
      = cupAtomCount prefixAtoms
        + ((if toucherAtom.generatorDom.length == 0 && toucherAtom.generatorCod.length == 2
            then (1 : Nat) else 0) + cupAtomCount suffixAtoms) := by
    rw [← headInd, wholeCup, doesSplitSpine, cupAtomCount_append]
    rfl
  have bubble : 1 + cupAtomCount movedPrefixAtoms
      = (if toucherAtom.generatorDom.length == 0 && toucherAtom.generatorCod.length == 2
          then (1 : Nat) else 0) + cupAtomCount prefixAtoms := by
    have raw := bubblesToFront_cupAtomCount witness
    rw [movedInd] at raw
    exact raw
  exact cupLegArith (cupAtomCount tailList) (cupAtomCount movedPrefixAtoms)
    (cupAtomCount suffixAtoms) (cupAtomCount prefixAtoms) _ wholeEq bubble

/-- ★ **The cup cancel's TOTAL cap-count leg, orbit-free.**  The dual of `arcCupCase_cupCountAgree`:
the tail's total cap count equals the moved-remainder's, discharging `capCountAgree` with NO orbit.
The cup head and moved cup contribute `0` to the cap count. -/
theorem arcCupCase_capCountAgree
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList secondList prefixAtoms suffixAtoms movedPrefixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (toucherAtom movedTarget :
      SpineAtom adjunctionModeSignature overallSource overallTarget)
    (movedDomPin : movedTarget.generatorDom.length = 0)
    (doesSplitSpine : secondList = prefixAtoms ++ toucherAtom :: suffixAtoms)
    (witness : BubblesToFront toucherAtom prefixAtoms movedTarget movedPrefixAtoms)
    (arcEqual : arcStructureOfSpineList bottomCount (headAtom :: tailList)
        = arcStructureOfSpineList bottomCount secondList) :
    (arcStructureOfSpineList headAtom.codBoundaryLength tailList).capCount
      = (arcStructureOfSpineList headAtom.codBoundaryLength (movedPrefixAtoms ++ suffixAtoms)).capCount
    := by
  have movedCod : movedTarget.generatorCod.length = 2 := by
    cases adjunctionSpineAtom_hasCupOrCapArity movedTarget with
    | inl cupArity => exact cupArity.2
    | inr capArity => exact Nat.noConfusion (capArity.1.symm.trans movedDomPin)
  rw [arcStructureOfSpineList_capCount, arcStructureOfSpineList_capCount, capAtomCount_append]
  have wholeCap : capAtomCount (headAtom :: tailList) = capAtomCount secondList := by
    have base := congrArg FullArcStructure.capCount arcEqual
    rw [arcStructureOfSpineList_capCount, arcStructureOfSpineList_capCount] at base
    exact base
  have headInd : capAtomCount (headAtom :: tailList) = 0 + capAtomCount tailList := by
    show (if headAtom.generatorDom.length == 2 && headAtom.generatorCod.length == 0
            then (1 : Nat) else 0) + capAtomCount tailList = 0 + capAtomCount tailList
    rw [capIndicator_ofCup headAtom hasCupDomArity hasCupCodArity]
  have movedInd : capAtomCount (movedTarget :: movedPrefixAtoms)
      = 0 + capAtomCount movedPrefixAtoms := by
    show (if movedTarget.generatorDom.length == 2 && movedTarget.generatorCod.length == 0
            then (1 : Nat) else 0) + capAtomCount movedPrefixAtoms
        = 0 + capAtomCount movedPrefixAtoms
    rw [capIndicator_ofCup movedTarget movedDomPin movedCod]
  have wholeEq : 0 + capAtomCount tailList
      = capAtomCount prefixAtoms
        + ((if toucherAtom.generatorDom.length == 2 && toucherAtom.generatorCod.length == 0
            then (1 : Nat) else 0) + capAtomCount suffixAtoms) := by
    rw [← headInd, wholeCap, doesSplitSpine, capAtomCount_append]
    rfl
  have bubble : 0 + capAtomCount movedPrefixAtoms
      = (if toucherAtom.generatorDom.length == 2 && toucherAtom.generatorCod.length == 0
          then (1 : Nat) else 0) + capAtomCount prefixAtoms := by
    have raw := bubblesToFront_capAtomCount witness
    rw [movedInd] at raw
    exact raw
  exact capLegArith (capAtomCount tailList) (capAtomCount movedPrefixAtoms)
    (capAtomCount suffixAtoms) (capAtomCount prefixAtoms) _ wholeEq bubble

/-! ## Honesty marker -/

/-- **Honesty marker — the cup cancel's TWO total-count legs are orbit-free (peel campaign H).**
`arcCupCase_cupCountAgree` / `arcCupCase_capCountAgree` discharge the `cupCountAgree` / `capCountAgree`
hypotheses of `arcCupTailsCancel_ofDiagramAndCounts` from the cup-case dispatch data alone — global
count conservation (`arcStructureOfSpineList_{cup,cap}Count`, boundary-independent) plus the bubble's
generator-arity invariance (`bubblesToFront_{cup,cap}AtomCount`).  So the genuine orbit residual for
the cup cancel is now the DIAGRAM leg and the two PER-PORT internal-count legs — NOT the totals.  What
this marker does NOT claim: the diagram agreement (the parity campaign's MIXED cell) nor the per-port
internal-count agreement (the through-the-head re-selection) — those remain the orbit.  `= true`. -/
def fxMode_hasArcCupTailsCountLegs : Bool := true

end FX1Poly.Polygraph
