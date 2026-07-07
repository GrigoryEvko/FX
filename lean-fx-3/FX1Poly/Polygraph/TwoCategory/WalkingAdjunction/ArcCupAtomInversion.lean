import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupExists
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadCountPositive

/-! # ArcCupAtomInversion — the boundary → cup-atom occurrence identification

The cup-head discharge (`#2152`) opens by identifying WHICH occurrence in the second spine realizes
the head cup.  The refuted universal window read-off
(`ArcCupHeadWindowUniversalRefuted`, R1c) means the head cup's window is NOT a function of the arc
structure alone — so we cannot read the realizing occurrence's window straight off the fold.  What
the arc structure DOES pin, unconditionally, is the *presence* of a cup occurrence: the head cup
fires one cup event (`arcCupHead_cupCount_pos`), arc-structure equality transports that cup total to
the second spine, and a positive cup total LOCATES a genuine cup atom in the list
(`arcSpine_hasCup_of_cupCount_pos`) — an occurrence `secondList = prefixAtoms ++ toucherAtom ::
suffixAtoms` whose toucher carries the cup arities (dom `0`, cod `2`).

This is the first, tractable brick of the located-cup certificate `ArcCupOrbitWitness`: it inverts
the arc-fold's cup count to a concrete list occurrence.  It is deliberately WEAKER than the shipped
`arcCupCase_locateAndBubble`: that brick additionally bubbles the located cup to the front and reports
the *moved* image's dom arity; this one reports the *located occurrence's own* dom AND cod arities —
the raw cup-atom occurrence, before any bubbling.  What it does NOT supply is the window pin (which
cup, at which window — the orbit-dependent content the refuted universal read-off leaves open) nor the
event-node identity of the realizing strand; those remain the genuine planar residual downstream
(`arcCupReselection_exists`).

Raw Lean 4 + Init; cup-count positivity transported by arc-equality into the shipped cup locator;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The boundary → cup-atom occurrence identification.**  For a cup-arity head and a second spine
arc-equal to it, the second spine splits at a genuine cup occurrence `prefixAtoms ++ toucherAtom ::
suffixAtoms` — `toucherAtom` a walking-adjunction cup (dom `0`, cod `2`).  The head cup forces
`0 < cupCount (headAtom :: tailList)` (`arcCupHead_cupCount_pos`); arc-structure equality transports
it to `0 < cupCount secondList`; a positive cup total locates a cup atom
(`arcSpine_hasCup_of_cupCount_pos`), whose arity dichotomy delivers both cup arities on the located
occurrence.  This inverts the arc fold's cup count back to a concrete list occurrence — the first
brick of `ArcCupOrbitWitness`.  It does NOT pin which occurrence sits at the head's window (the
refuted universal read-off leaves that to the trace orbit). -/
theorem arcCupAtomInversion {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList secondList :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (arcEqual : arcStructureOfSpineList bottomCount (headAtom :: tailList)
        = arcStructureOfSpineList bottomCount secondList) :
    ∃ (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
      (toucherAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
      (suffixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
      secondList = prefixAtoms ++ toucherAtom :: suffixAtoms
        ∧ toucherAtom.generatorDom.length = 0
        ∧ toucherAtom.generatorCod.length = 2 := by
  have headPos : 0 < (arcStructureOfSpineList bottomCount (headAtom :: tailList)).cupCount :=
    arcCupHead_cupCount_pos bottomCount headAtom hasCupDomArity hasCupCodArity tailList
  have cupCountEq : (arcStructureOfSpineList bottomCount (headAtom :: tailList)).cupCount
      = (arcStructureOfSpineList bottomCount secondList).cupCount :=
    congrArg FullArcStructure.cupCount arcEqual
  have secondPos : 0 < (arcStructureOfSpineList bottomCount secondList).cupCount :=
    cupCountEq ▸ headPos
  exact arcSpine_hasCup_of_cupCount_pos bottomCount secondList secondPos

/-! ## Honesty marker -/

/-- **Honesty marker — the boundary → cup-atom occurrence inversion is SHIPPED.**
`arcCupAtomInversion`: from a cup-arity head arc-equal to the second spine, the second spine splits at
a genuine cup occurrence (`toucherAtom` dom `0`, cod `2`), by transporting the head cup's positivity
(`arcCupHead_cupCount_pos`) across arc-structure equality into the shipped cup locator
(`arcSpine_hasCup_of_cupCount_pos`).  This is the raw cup-atom occurrence, pre-bubble — the first
brick of `ArcCupOrbitWitness`.  What this marker does NOT claim: the window pin (WHICH cup, at WHICH
window — the R1c-refuted orbit-dependent content), the event-node identity of the realizing strand,
nor the leg-aligned re-selection (`arcCupReselection_exists`, the genuine planar residual).
`= true`. -/
def fxMode_hasArcCupAtomInversion : Bool := true

end FX1Poly.Polygraph
