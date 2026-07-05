import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPairSeparation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPeelFoundations
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold

/-! # ArcPairLocateTouch — the head-location scan over a walking-adjunction spine

The scan induction: walking a walking-adjunction spine from a fresh state where the tracked
pair is untouched, EITHER the pair survives untouched to the end, OR the spine splits at a
cap whose window reads hit the pair, with the pair still untouched at that split point.
Every atom is a cup or a cap (`adjunctionSpineAtom_isCupOrCap`); cups never touch the pair;
a cap dispatches on the four decidable read-vs-node equalities — all misses preserve the
invariant, any hit stops the scan with the witness decomposition.

Combined with the end-state kill (`arcPairUntouched_partnerIndexOf_ne`): a final partner
read-off pinning the pair as partners refutes the survival branch, so the split is
UNCONDITIONAL under the pin (`arcPairTouchSplit_ofPartnerPin`) — the head-location scan
terminates with a touching cap.

NOT yet shipped: the touch REFINEMENT — a cap consuming exactly one pair node pollutes that
node's component with an event, contradicting the final internal-count pins, so the toucher
under the full pin set must consume BOTH nodes at adjacent positions.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The touch predicate and the split certificate -/

/-- A cap window's two reads at a state HIT the tracked pair when at least one read equals
one of the two tracked nodes. -/
def ArcReadsTouchPair (state : ArcWireState) (position leftNode rightNode : Nat) : Prop :=
  natListGetAt state.openWires position = leftNode
    ∨ natListGetAt state.openWires position = rightNode
    ∨ natListGetAt state.openWires (position + 1) = leftNode
    ∨ natListGetAt state.openWires (position + 1) = rightNode

/-- **The scan's split certificate**: a decomposition of the spine at a pair-touching cap —
the spine equals prefix + toucher + suffix, the prefix keeps the pair untouched, the toucher
has cap arity, and its window reads hit the pair at the split state.  A single-constructor
`Prop` inductive (data witnesses inside a proposition, like `Exists`); consume with
`obtain ⟨prefixAtoms, toucherAtom, suffixAtoms, doesSplitSpine, isUntouchedBeforeToucher,
hasCapDomArity, hasCapCodArity, doesTouchPair⟩`. -/
inductive ArcPairTouchSplit (leftNode rightNode : Nat)
    {sourceMode targetMode : adjunctionGraph.Mode}
    (state : ArcWireState)
    (atoms : List (SpineAtom adjunctionModeSignature sourceMode targetMode)) : Prop where
  | intro
      (prefixAtoms : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
      (toucherAtom : SpineAtom adjunctionModeSignature sourceMode targetMode)
      (suffixAtoms : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
      (doesSplitSpine : atoms = prefixAtoms ++ toucherAtom :: suffixAtoms)
      (isUntouchedBeforeToucher :
        ArcPairUntouched leftNode rightNode (processArcSpine state prefixAtoms))
      (hasCapDomArity : toucherAtom.generatorDom.length = 2)
      (hasCapCodArity : toucherAtom.generatorCod.length = 0)
      (doesTouchPair : ArcReadsTouchPair (processArcSpine state prefixAtoms)
        toucherAtom.leftContext.length leftNode rightNode)

/-- A split of the stepped tail lifts over the leading atom — the prefix grows by one, and
the split state is unchanged (the fold's cons step is definitional). -/
theorem arcPairTouchSplit_ofSteppedTail {leftNode rightNode : Nat}
    {sourceMode targetMode : adjunctionGraph.Mode} {state : ArcWireState}
    (atom : SpineAtom adjunctionModeSignature sourceMode targetMode)
    {rest : List (SpineAtom adjunctionModeSignature sourceMode targetMode)}
    (split : ArcPairTouchSplit leftNode rightNode (stepArcAtom state atom) rest) :
    ArcPairTouchSplit leftNode rightNode state (atom :: rest) := by
  obtain ⟨prefixAtoms, toucherAtom, suffixAtoms, doesSplit, untouchedBefore,
    capDomArity, capCodArity, touches⟩ := split
  exact ⟨atom :: prefixAtoms, toucherAtom, suffixAtoms,
    congrArg (atom :: ·) doesSplit, untouchedBefore, capDomArity, capCodArity, touches⟩

/-! ## The scan induction -/

/-- ★ **The head-location scan**: from a fresh state with the pair untouched, either the
pair survives the whole spine untouched, or the spine splits at a pair-touching cap.  Cups
preserve the invariant unconditionally; a cap dispatches on its four decidable read-vs-node
equalities — all misses preserve, any hit stops with the certificate. -/
theorem arcPairUntouched_locateTouch {leftNode rightNode : Nat}
    {sourceMode targetMode : adjunctionGraph.Mode} :
    (atoms : List (SpineAtom adjunctionModeSignature sourceMode targetMode)) →
    (state : ArcWireState) → ArcStateFresh state →
    ArcPairUntouched leftNode rightNode state →
    ArcPairUntouched leftNode rightNode (processArcSpine state atoms)
      ∨ ArcPairTouchSplit leftNode rightNode state atoms
  | [], _, _, untouched => Or.inl untouched
  | atom :: rest, state, fresh, untouched => by
      cases adjunctionSpineAtom_isCupOrCap atom with
      | inl cupArity =>
          have steppedUntouched :
              ArcPairUntouched leftNode rightNode (stepArcAtom state atom) := by
            rw [stepArcAtom_eq_stepCupArc state atom cupArity.1 cupArity.2]
            exact arcPairUntouched_stepCupArc state atom.leftContext.length fresh untouched
          cases arcPairUntouched_locateTouch rest (stepArcAtom state atom)
              (arcStateFresh_stepArcAtom state atom fresh) steppedUntouched with
          | inl untouchedAtEnd => exact Or.inl untouchedAtEnd
          | inr splitOfTail => exact Or.inr (arcPairTouchSplit_ofSteppedTail atom splitOfTail)
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
              cases arcPairUntouched_locateTouch rest (stepArcAtom state atom)
                  (arcStateFresh_stepArcAtom state atom fresh) steppedUntouched with
              | inl untouchedAtEnd => exact Or.inl untouchedAtEnd
              | inr splitOfTail =>
                  exact Or.inr (arcPairTouchSplit_ofSteppedTail atom splitOfTail)

/-! ## The unconditional split under the partner pin -/

/-- ★ **Under the partner pin the split is unconditional**: when the FINAL partner read-off
pairs the two tracked bottom ports, the survival branch dies on the end-state kill, so the
spine splits at a pair-touching cap — the head-location scan's termination theorem. -/
theorem arcPairTouchSplit_ofPartnerPin {sourceMode targetMode : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
    (state : ArcWireState) {leftIndex rightIndex : Nat}
    (leftBelow : leftIndex < bottomCount) (rightBelow : rightIndex < bottomCount)
    (indexesNe : leftIndex ≠ rightIndex)
    (fresh : ArcStateFresh state)
    (untouched : ArcPairUntouched leftIndex rightIndex state)
    (partnerPin : partnerIndexOf (processArcSpine state atoms).links
        (List.range bottomCount ++ (processArcSpine state atoms).openWires)
        (bottomCount + (processArcSpine state atoms).openWires.length) leftIndex
      = rightIndex) :
    ArcPairTouchSplit leftIndex rightIndex state atoms :=
  (arcPairUntouched_locateTouch atoms state fresh untouched).resolve_left
    (fun untouchedAtEnd =>
      arcPairUntouched_partnerIndexOf_ne bottomCount (processArcSpine state atoms)
        leftBelow rightBelow indexesNe untouchedAtEnd partnerPin)

/-! ## Honesty marker -/

/-- **Honesty marker — the head-location scan is SHIPPED.**  Over any walking-adjunction
spine from a fresh untouched state, the pair either survives untouched or the spine splits
at a pair-touching cap with the pair untouched at the split point; under the final partner
pin the split is unconditional.  NOT yet shipped: the touch refinement (a one-node touch
contradicts the final internal-count pins, so the toucher consumes BOTH nodes) and the
bubbling of the located toucher to the spine's front.  `= true`. -/
def fxMode_hasArcPairTouchLocation : Bool := true

end FX1Poly.Polygraph
