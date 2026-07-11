import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPairLocateTouch
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcArity

/-! # WalkingString/StringArcPairLocateTouch — the head-location scan, ported to the adjoint-triple seed
(FC-3 r19, THE CAP-HEAD DISCHARGE PORT — LOCATE substrate, Phase B floor)

Colour-blind two-token clone of the walking-adjunction `ArcPairLocateTouch` (the scan induction over a spine from a
fresh untouched state), re-plumbed onto the FOUR-generator seed.  The only non-generic dependency is the seed
classification `adjointTripleSpineAtom_isCupOrCap` (`StringArcArity`) — the arc engine (`processArcSpine`,
`stepArcAtom`, `ArcPairUntouched`, `ArcReadsTouchPair`, the freshness/step kit) is `{signature}`-generic and REUSED
by import, never cloned.  The touch predicate `ArcReadsTouchPair` (pure `ArcWireState`/`Nat`) is reused directly.

  * `StringArcPairTouchSplit` — the split certificate (`SpineAtom adjointTripleModeSignature` fields, so a genuinely
    new inductive), one constructor carrying prefix/toucher/suffix + untouched-before + cap arity + touch witness;
  * `stringArcPairTouchSplit_ofSteppedTail` — a tail split lifts over the leading atom;
  * ★ `stringArcPairUntouched_locateTouch` — the scan: from a fresh untouched state, either the pair survives or the
    spine splits at a pair-touching cap (cups preserve, a cap dispatches on its four decidable read-vs-node equalities);
  * ★ `stringArcPairTouchSplit_ofPartnerPin` — under the final partner pin the split is unconditional.

Raw Lean 4 + Init; structural recursion only; no `omega` / `simp`-AC / `WellFounded.fix`.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The split certificate -/

/-- **The scan's split certificate** (four-generator port): a decomposition of the spine at a pair-touching cap —
the spine equals prefix + toucher + suffix, the prefix keeps the pair untouched, the toucher has cap arity, and its
window reads hit the pair at the split state.  A single-constructor `Prop` inductive; consume with
`obtain ⟨prefixAtoms, toucherAtom, suffixAtoms, doesSplitSpine, isUntouchedBeforeToucher, hasCapDomArity,
hasCapCodArity, doesTouchPair⟩`.  The three-generator analog of `ArcPairTouchSplit`. -/
inductive StringArcPairTouchSplit (leftNode rightNode : Nat)
    {sourceMode targetMode : adjointTripleGraph.Mode}
    (state : ArcWireState)
    (atoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode)) : Prop where
  | intro
      (prefixAtoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
      (toucherAtom : SpineAtom adjointTripleModeSignature sourceMode targetMode)
      (suffixAtoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
      (doesSplitSpine : atoms = prefixAtoms ++ toucherAtom :: suffixAtoms)
      (isUntouchedBeforeToucher :
        ArcPairUntouched leftNode rightNode (processArcSpine state prefixAtoms))
      (hasCapDomArity : toucherAtom.generatorDom.length = 2)
      (hasCapCodArity : toucherAtom.generatorCod.length = 0)
      (doesTouchPair : ArcReadsTouchPair (processArcSpine state prefixAtoms)
        toucherAtom.leftContext.length leftNode rightNode)

/-- A split of the stepped tail lifts over the leading atom — the prefix grows by one, and the split state is
unchanged (the fold's cons step is definitional).  The three-generator analog of `arcPairTouchSplit_ofSteppedTail`. -/
theorem stringArcPairTouchSplit_ofSteppedTail {leftNode rightNode : Nat}
    {sourceMode targetMode : adjointTripleGraph.Mode} {state : ArcWireState}
    (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode)
    {rest : List (SpineAtom adjointTripleModeSignature sourceMode targetMode)}
    (split : StringArcPairTouchSplit leftNode rightNode (stepArcAtom state atom) rest) :
    StringArcPairTouchSplit leftNode rightNode state (atom :: rest) := by
  obtain ⟨prefixAtoms, toucherAtom, suffixAtoms, doesSplit, untouchedBefore,
    capDomArity, capCodArity, touches⟩ := split
  exact ⟨atom :: prefixAtoms, toucherAtom, suffixAtoms,
    congrArg (atom :: ·) doesSplit, untouchedBefore, capDomArity, capCodArity, touches⟩

/-! ## The scan induction -/

/-- ★ **The head-location scan** (four-generator port): from a fresh state with the pair untouched, either the pair
survives the whole spine untouched, or the spine splits at a pair-touching cap.  Cups preserve the invariant
unconditionally; a cap dispatches on its four decidable read-vs-node equalities — all misses preserve, any hit stops
with the certificate.  The three-generator analog of `arcPairUntouched_locateTouch`. -/
theorem stringArcPairUntouched_locateTouch {leftNode rightNode : Nat}
    {sourceMode targetMode : adjointTripleGraph.Mode} :
    (atoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode)) →
    (state : ArcWireState) → ArcStateFresh state →
    ArcPairUntouched leftNode rightNode state →
    ArcPairUntouched leftNode rightNode (processArcSpine state atoms)
      ∨ StringArcPairTouchSplit leftNode rightNode state atoms
  | [], _, _, untouched => Or.inl untouched
  | atom :: rest, state, fresh, untouched => by
      cases adjointTripleSpineAtom_isCupOrCap atom with
      | inl cupArity =>
          have steppedUntouched :
              ArcPairUntouched leftNode rightNode (stepArcAtom state atom) := by
            rw [stepArcAtom_eq_stepCupArc state atom cupArity.1 cupArity.2]
            exact arcPairUntouched_stepCupArc state atom.leftContext.length fresh untouched
          cases stringArcPairUntouched_locateTouch rest (stepArcAtom state atom)
              (arcStateFresh_stepArcAtom state atom fresh) steppedUntouched with
          | inl untouchedAtEnd => exact Or.inl untouchedAtEnd
          | inr splitOfTail => exact Or.inr (stringArcPairTouchSplit_ofSteppedTail atom splitOfTail)
      | inr capArity =>
          cases Nat.decEq (natListGetAt state.openWires atom.leftContext.length) leftNode with
          | isTrue firstHitsLeft =>
              exact Or.inr ⟨[], atom, rest, rfl, untouched, capArity.1, capArity.2,
                Or.inl firstHitsLeft⟩
          | isFalse firstMissesLeft =>
          cases Nat.decEq (natListGetAt state.openWires atom.leftContext.length)
              rightNode with
          | isTrue firstHitsRight =>
              exact Or.inr ⟨[], atom, rest, rfl, untouched, capArity.1, capArity.2,
                Or.inr (Or.inl firstHitsRight)⟩
          | isFalse firstMissesRight =>
          cases Nat.decEq (natListGetAt state.openWires (atom.leftContext.length + 1))
              leftNode with
          | isTrue secondHitsLeft =>
              exact Or.inr ⟨[], atom, rest, rfl, untouched, capArity.1, capArity.2,
                Or.inr (Or.inr (Or.inl secondHitsLeft))⟩
          | isFalse secondMissesLeft =>
          cases Nat.decEq (natListGetAt state.openWires (atom.leftContext.length + 1))
              rightNode with
          | isTrue secondHitsRight =>
              exact Or.inr ⟨[], atom, rest, rfl, untouched, capArity.1, capArity.2,
                Or.inr (Or.inr (Or.inr secondHitsRight))⟩
          | isFalse secondMissesRight =>
              have steppedUntouched :
                  ArcPairUntouched leftNode rightNode (stepArcAtom state atom) := by
                rw [stepArcAtom_eq_stepCapArc state atom capArity.1 capArity.2]
                exact arcPairUntouched_stepCapArc_ofDisjointReads state
                  atom.leftContext.length fresh firstMissesLeft secondMissesLeft
                  firstMissesRight secondMissesRight untouched
              cases stringArcPairUntouched_locateTouch rest (stepArcAtom state atom)
                  (arcStateFresh_stepArcAtom state atom fresh) steppedUntouched with
              | inl untouchedAtEnd => exact Or.inl untouchedAtEnd
              | inr splitOfTail =>
                  exact Or.inr (stringArcPairTouchSplit_ofSteppedTail atom splitOfTail)

/-! ## The unconditional split under the partner pin -/

/-- ★ **Under the partner pin the split is unconditional** (four-generator port): when the FINAL partner read-off
pairs the two tracked bottom ports, the survival branch dies on the end-state kill, so the spine splits at a
pair-touching cap.  The three-generator analog of `arcPairTouchSplit_ofPartnerPin`. -/
theorem stringArcPairTouchSplit_ofPartnerPin {sourceMode targetMode : adjointTripleGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
    (state : ArcWireState) {leftIndex rightIndex : Nat}
    (leftBelow : leftIndex < bottomCount) (rightBelow : rightIndex < bottomCount)
    (indexesNe : leftIndex ≠ rightIndex)
    (fresh : ArcStateFresh state)
    (untouched : ArcPairUntouched leftIndex rightIndex state)
    (partnerPin : partnerIndexOf (processArcSpine state atoms).links
        (List.range bottomCount ++ (processArcSpine state atoms).openWires)
        (bottomCount + (processArcSpine state atoms).openWires.length) leftIndex
      = rightIndex) :
    StringArcPairTouchSplit leftIndex rightIndex state atoms :=
  (stringArcPairUntouched_locateTouch atoms state fresh untouched).resolve_left
    (fun untouchedAtEnd =>
      arcPairUntouched_partnerIndexOf_ne bottomCount (processArcSpine state atoms)
        leftBelow rightBelow indexesNe untouchedAtEnd partnerPin)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the head-location scan is ported to the adjoint-triple seed (FC-3 r19, LOCATE floor).**
`StringArcPairTouchSplit` / `stringArcPairTouchSplit_ofSteppedTail` / `stringArcPairUntouched_locateTouch` /
`stringArcPairTouchSplit_ofPartnerPin` — the colour-blind two-token clone of `ArcPairLocateTouch`, riding the seed
classification `adjointTripleSpineAtom_isCupOrCap` and the `{signature}`-generic arc engine (reused, never cloned).
Over any string spine from a fresh untouched state the pair either survives untouched or the spine splits at a
pair-touching cap; under the final partner pin the split is unconditional.  NOT yet shipped: the half-touch
refinement (a one-node touch contradicts the final internal-count pins, so the toucher consumes BOTH nodes) —
the next LOCATE brick.  `= true`. -/
def fxString_hasArcPairTouchLocation : Bool := true

end FX1Poly.Polygraph
