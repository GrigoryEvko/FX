import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPairCapWindow
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcHalfTouchKill

/-! # WalkingString/StringArcPairCapWindow — the located consuming cap, ported
(FC-3 r19, THE CAP-HEAD DISCHARGE PORT — LOCATE certificate)

Colour-blind two-token clone of the walking-adjunction `ArcPairCapWindow`, re-plumbed onto the FOUR-generator seed.
Over a string spine from the canonical seed, a FINAL partner pin plus a FINAL strand count pin at two distinct
bottom ports locate a cap consuming EXACTLY those two ports adjacently.  The only non-generic dependencies are the
ported split-under-pin (`stringArcPairTouchSplit_ofPartnerPin`, Brick 1) and the ported half-touch upgrade
(`stringArcTouchWindowReadsArePair`, Brick 2b); the seed-invariant / union-find kit is `{signature}`-generic and
REUSED by import.

  * `StringArcPairCapWindow` — the located-window certificate (split + cap arity + untouched prefix + exact ordered
    reads), a genuinely new inductive (`SpineAtom adjointTripleModeSignature` fields);
  * ★ `stringArcPairCapWindow_ofFinalPins` — the read-off.

Raw Lean 4 + Init; structural recursion only; no `omega` / `simp`-AC / `WellFounded.fix`.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **The located-window certificate** (four-generator port): the spine splits at a cap whose window reads consume
EXACTLY the two tracked bottom ports (in one of the two orders), with the pair untouched through the prefix.  A
single-constructor `Prop` inductive; consume with `obtain ⟨prefixAtoms, toucherAtom, suffixAtoms, doesSplitSpine,
isUntouchedBeforeToucher, hasCapDomArity, hasCapCodArity, doesConsumePair⟩`.  The three-generator analog of
`ArcPairCapWindow`. -/
inductive StringArcPairCapWindow (bottomCount leftIndex rightIndex : Nat)
    {sourceMode targetMode : adjointTripleGraph.Mode}
    (atoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode)) : Prop where
  | intro
      (prefixAtoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
      (toucherAtom : SpineAtom adjointTripleModeSignature sourceMode targetMode)
      (suffixAtoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
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

/-- ★ **The read-off** (four-generator port): over a string spine run from the canonical seed, the final partner pin
and the final strand count pin at two distinct bottom ports locate a cap consuming exactly those two ports.  The
three-generator analog of `arcPairCapWindow_ofFinalPins`. -/
theorem stringArcPairCapWindow_ofFinalPins (bottomCount : Nat)
    {sourceMode targetMode : adjointTripleGraph.Mode}
    (atoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
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
    StringArcPairCapWindow bottomCount leftIndex rightIndex atoms := by
  obtain ⟨prefixAtoms, toucherAtom, suffixAtoms, doesSplitSpine, untouchedBefore,
    capDomArity, capCodArity, doesTouchPair⟩ :=
    stringArcPairTouchSplit_ofPartnerPin bottomCount atoms
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
    stringArcTouchWindowReadsArePair prefixAtoms suffixAtoms toucherAtom
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) indexesNe
      freshSplit forestSplit untouchedBefore capDomArity capCodArity doesTouchPair
      pinConnectedRefolded pinCountRefolded⟩

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the located consuming cap ported to the adjoint-triple seed (FC-3 r19).**  Over a string spine
from the canonical seed, a final partner pin plus a final strand count pin of one at two distinct bottom ports locate
a cap consuming exactly those two ports adjacently — the `StringArcPairCapWindow` certificate, via the ported
split-under-pin and half-touch upgrade.  NOT yet shipped: producing the two pins from `FullArcStructure` EQUALITY
with a cap-headed reference (the transport) — the next LOCATE brick.  `= true`. -/
def fxString_hasArcPairCapWindow : Bool := true

end FX1Poly.Polygraph
