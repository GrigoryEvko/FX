import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHalfTouchKill
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLegAttachment
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute

/-! # ArcPairCapWindow — the located consuming cap, from the final pins

The head-location campaign's read-off theorem: over a walking-adjunction spine run from the
canonical seed, a FINAL partner pin (the partner read-off at one bottom port names the
other) together with a FINAL strand count pin (exactly one cap event on that port's
component) locates a cap in the spine whose two window reads consume EXACTLY the two pinned
bottom ports, adjacently, in one of the two orders.

The chain: the seed invariants (`arcStateFresh_initial`, `isUnionFindForest_initialLinks`,
`arcPairUntouched_initial`) feed the head-location scan
(`arcPairTouchSplit_ofPartnerPin`); the split refolds the final state through
`processArcSpine_append` and the cap-arity rewrite; the boundary reads below the seed width
convert the raw pins into the connection/count forms; and the half-touch kill
(`arcTouchWindowReadsArePair`) upgrades the touch to full consumption.

* `ArcPairCapWindow` — the located-window certificate (split + cap arity + untouched prefix
  + the exact ordered reads);
* ★ `arcPairCapWindow_ofFinalPins` — the read-off: final pins locate the consuming cap.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **The located-window certificate**: the spine splits at a cap whose window reads consume
EXACTLY the two tracked bottom ports (in one of the two orders), with the pair untouched
through the prefix — everything the bubble-to-front witness construction needs.  A
single-constructor `Prop` inductive (data witnesses inside a proposition); consume with
`obtain ⟨prefixAtoms, toucherAtom, suffixAtoms, doesSplitSpine, isUntouchedBeforeToucher,
hasCapDomArity, hasCapCodArity, doesConsumePair⟩`. -/
inductive ArcPairCapWindow (bottomCount leftIndex rightIndex : Nat)
    {sourceMode targetMode : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature sourceMode targetMode)) : Prop where
  | intro
      (prefixAtoms : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
      (toucherAtom : SpineAtom adjunctionModeSignature sourceMode targetMode)
      (suffixAtoms : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
      (doesSplitSpine : atoms = prefixAtoms ++ toucherAtom :: suffixAtoms)
      (isUntouchedBeforeToucher : ArcPairUntouched leftIndex rightIndex
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms))
      (hasCapDomArity : toucherAtom.generatorDom.length = 2)
      (hasCapCodArity : toucherAtom.generatorCod.length = 0)
      (doesConsumePair :
        (natListGetAt (processArcSpine
              (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              prefixAtoms).openWires toucherAtom.leftContext.length = leftIndex
          ∧ natListGetAt (processArcSpine
              (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              prefixAtoms).openWires (toucherAtom.leftContext.length + 1) = rightIndex)
        ∨ (natListGetAt (processArcSpine
              (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              prefixAtoms).openWires toucherAtom.leftContext.length = rightIndex
          ∧ natListGetAt (processArcSpine
              (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              prefixAtoms).openWires (toucherAtom.leftContext.length + 1) = leftIndex))

/-- ★ **The read-off**: over a spine run from the canonical seed, the final partner pin and
the final strand count pin at two distinct bottom ports locate a cap consuming exactly
those two ports. -/
theorem arcPairCapWindow_ofFinalPins (bottomCount : Nat)
    {sourceMode targetMode : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
    {leftIndex rightIndex : Nat}
    (leftBelow : leftIndex < bottomCount) (rightBelow : rightIndex < bottomCount)
    (indexesNe : leftIndex ≠ rightIndex)
    (partnerPin : partnerIndexOf
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          atoms).links
        (List.range bottomCount ++ (processArcSpine
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          atoms).openWires)
        (bottomCount + (processArcSpine
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          atoms).openWires.length)
        leftIndex
      = rightIndex)
    (capCountPin : internalEventCountAt
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          atoms).links
        (List.range bottomCount ++ (processArcSpine
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          atoms).openWires)
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          atoms).capEventNodes
        leftIndex
      = 1) :
    ArcPairCapWindow bottomCount leftIndex rightIndex atoms := by
  obtain ⟨prefixAtoms, toucherAtom, suffixAtoms, doesSplitSpine, untouchedBefore,
    capDomArity, capCodArity, doesTouchPair⟩ :=
    arcPairTouchSplit_ofPartnerPin bottomCount atoms
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      leftBelow rightBelow indexesNe (arcStateFresh_initial bottomCount)
      (arcPairUntouched_initial bottomCount leftIndex rightIndex leftBelow rightBelow)
      partnerPin
  have freshSplit : ArcStateFresh (processArcSpine
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms) :=
    arcStateFresh_processArcSpine prefixAtoms
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      (arcStateFresh_initial bottomCount)
  have forestSplit : isUnionFindForest (processArcSpine
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      prefixAtoms).links :=
    isUnionFindForest_processArcSpine prefixAtoms
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      (isUnionFindForest_initialLinks bottomCount)
  have chainEq : processArcSpine
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms
      = processArcSpine
          (stepCapArc
            (processArcSpine
              (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              prefixAtoms)
            toucherAtom.leftContext.length)
          suffixAtoms := by
    rw [doesSplitSpine, processArcSpine_append prefixAtoms (toucherAtom :: suffixAtoms)
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])]
    show processArcSpine
        (stepArcAtom
          (processArcSpine
            (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms)
          toucherAtom)
        suffixAtoms = _
    rw [stepArcAtom_eq_stepCapArc _ toucherAtom capDomArity capCodArity]
  have leftRead : natListGetAt (List.range bottomCount ++ (processArcSpine
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      atoms).openWires) leftIndex = leftIndex :=
    natListGetAt_rangeAppend_below bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        atoms).openWires leftIndex leftBelow
  have rightRead : natListGetAt (List.range bottomCount ++ (processArcSpine
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      atoms).openWires) rightIndex = rightIndex :=
    natListGetAt_rangeAppend_below bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        atoms).openWires rightIndex rightBelow
  have pinConnectedAtFinal : isSameComponent (processArcSpine
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).links
      leftIndex rightIndex = true := by
    have connectedReads := isSameComponent_ofPartnerIndexOfHit
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        atoms).links
      (List.range bottomCount ++ (processArcSpine
        (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).openWires)
      (bottomCount + (processArcSpine
        (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        atoms).openWires.length)
      leftIndex rightIndex (Ne.symm indexesNe) partnerPin
    rw [leftRead, rightRead] at connectedReads
    exact connectedReads
  have pinCountAtFinal : countEventsInRoot (processArcSpine
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).links
      (unionFindRootOf (processArcSpine
        (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).links
        leftIndex)
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        atoms).capEventNodes = 1 := by
    have countRead : countEventsInRoot (processArcSpine
        (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).links
        (unionFindRootOf (processArcSpine
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).links
          (natListGetAt (List.range bottomCount ++ (processArcSpine
            (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            atoms).openWires) leftIndex))
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          atoms).capEventNodes = 1 := capCountPin
    rw [leftRead] at countRead
    exact countRead
  have pinConnectedRefolded := chainEq ▸ pinConnectedAtFinal
  have pinCountRefolded := chainEq ▸ pinCountAtFinal
  exact ⟨prefixAtoms, toucherAtom, suffixAtoms, doesSplitSpine, untouchedBefore,
    capDomArity, capCodArity,
    arcTouchWindowReadsArePair prefixAtoms suffixAtoms toucherAtom
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) indexesNe
      freshSplit forestSplit untouchedBefore capDomArity capCodArity doesTouchPair
      pinConnectedRefolded pinCountRefolded⟩

/-! ## Honesty marker -/

/-- **Honesty marker — the located consuming cap is SHIPPED.**  Over a walking-adjunction
spine from the canonical seed, a final partner pin plus a final strand count pin of one at
two distinct bottom ports locate a cap consuming exactly those two ports adjacently — the
`ArcPairCapWindow` certificate.  NOT yet shipped: producing the two pins from
`FullArcStructure` EQUALITY with a cap-headed reference spine (the extract-field read-off)
and the bubble-to-front witness construction over the located window.  `= true`. -/
def fxMode_hasArcPairCapWindow : Bool := true

end FX1Poly.Polygraph
