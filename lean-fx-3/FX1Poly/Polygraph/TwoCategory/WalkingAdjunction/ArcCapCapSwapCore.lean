import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPartitionSimStep
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcWindowCommutation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcFreshBlockTransposition

/-! # WalkingAdjunction/ArcCapCapSwapCore — the CAP x CAP two-step partition-simulation core

The FOURTH two-step swap combo, in the corrected vehicle.  Both cap-cap obstructions
(`ArcCapCapSwapObstruction`, `ArcCapCapAgreeObstruction`) showed the renaming and plain-agreement
vehicles fail here; the target is `ArcPartitionSim` under the EVENT TRANSPOSITION
`arcFreshBlockTransposition state.nextFresh 1 1` (the swap `nf <-> nf + 1` of the two cap event
nodes, fixing everything else).

This file opens the core with the WIRE leg: the two run orders produce the SAME open-wire list
(`natListRemoveTwoAt_removeAbove_commute` — removing the high pair first and then the low pair
equals removing low-first and then at the down-shifted position), and the transposition fixes
every remaining wire (wires are OLD nodes, strictly below `nextFresh`), so the `openMap` field
holds with the map degenerating to the identity. -/

namespace FX1Poly.Polygraph

/-- ★ **The cap-cap `openMap` leg.**  HIGH-first wires (`removeTwoAt` at `gap + 2 + positionLow`
then at `positionLow`) equal the `sigma`-image of LOW-first wires (`removeTwoAt` at
`positionLow` then at `gap + positionLow`): the raw lists agree by the unconditional
remove-remove commutation, and the event transposition fixes every surviving wire
(`arcFreshBlockTransposition_ofBelow` on the freshness bound, through two `removeTwoAt`
membership projections). -/
theorem capCapSwap_openMap (state : ArcWireState) (positionLow gap : Nat)
    (wiresFresh : ∀ wire ∈ state.openWires, wire < state.nextFresh) :
    (stepCapArc (stepCapArc state (gap + 2 + positionLow)) positionLow).openWires
      = ((stepCapArc (stepCapArc state positionLow) (gap + positionLow)).openWires).map
          (arcFreshBlockTransposition state.nextFresh 1 1) := by
  show natListRemoveTwoAt (natListRemoveTwoAt state.openWires (gap + 2 + positionLow))
        positionLow
     = (natListRemoveTwoAt (natListRemoveTwoAt state.openWires positionLow)
         (gap + positionLow)).map (arcFreshBlockTransposition state.nextFresh 1 1)
  rw [natListRemoveTwoAt_removeAbove_commute state.openWires positionLow gap,
    mapFixedOn (arcFreshBlockTransposition state.nextFresh 1 1)
      (natListRemoveTwoAt (natListRemoveTwoAt state.openWires positionLow) (gap + positionLow))
      (fun wire wireMember =>
        arcFreshBlockTransposition_ofBelow state.nextFresh 1 1 wire
          (wiresFresh wire
            (mem_natListRemoveTwoAt state.openWires positionLow wire
              (mem_natListRemoveTwoAt
                (natListRemoveTwoAt state.openWires positionLow)
                (gap + positionLow) wire wireMember))))]

/-- `Nat` boolean equality is reflexive (`==` is `decide (· = ·)`). -/
theorem natBeq_self (value : Nat) : (value == value) = true :=
  decide_eq_true rfl

/-- `Nat` boolean equality is symmetric as a `Bool`-valued equation. -/
theorem natBeq_comm (firstValue secondValue : Nat) :
    (firstValue == secondValue) = (secondValue == firstValue) := by
  cases forwardWitness : (firstValue == secondValue) with
  | true =>
      have valuesEqual : firstValue = secondValue := of_decide_eq_true forwardWitness
      rw [valuesEqual, natBeq_self]
  | false =>
      cases backwardWitness : (secondValue == firstValue) with
      | true =>
          have valuesEqual : secondValue = firstValue := of_decide_eq_true backwardWitness
          rw [valuesEqual, natBeq_self] at forwardWitness
          exact Bool.noConfusion forwardWitness
      | false => rfl

/-- `false && bit = false` as a rewritable equation (definitional, but `rw` needs the lemma). -/
theorem boolFalseAnd (bit : Bool) : (false && bit) = false := rfl

/-- `bit || false = bit` — `||` matches on its FIRST argument, so this needs a case split. -/
theorem boolOrFalse (bit : Bool) : (bit || false) = bit := by
  cases bit with
  | true => rfl
  | false => rfl

/-- `true || bit = true` as a rewritable equation. -/
theorem boolTrueOr (bit : Bool) : (true || bit) = true := rfl

/-- `false || bit = bit` as a rewritable equation. -/
theorem boolFalseOr (bit : Bool) : (false || bit) = bit := rfl

/-- `true && bit = bit` as a rewritable equation. -/
theorem boolTrueAnd (bit : Bool) : (true && bit) = bit := rfl

/-- ★ **The boolean JOIN SPLIT — one merge, characterized at the partition level.**  After
joining `firstNode` and `secondNode`, two queries share a component iff they already did, or
they sit crosswise in the two merged components.  This is the elementwise characterization the
cap-cap `componentsCorr` and `loopsEq` legs case over: it expresses the after-join partition
purely in PRE-join same-component booleans, with no representative mentioned.  Four cases over
the two after-join root-formula guards; each leaf reduces by `Nat`-beq reflexivity/symmetry and
`Bool` absorption. -/
theorem isSameComponent_unionFindJoin_split (links : List (Nat × Nat))
    (hforest : isUnionFindForest links)
    (firstNode secondNode queryLeft queryRight : Nat) :
    isSameComponent (unionFindJoin links firstNode secondNode) queryLeft queryRight
      = (isSameComponent links queryLeft queryRight
          || (isSameComponent links firstNode queryLeft
               && isSameComponent links secondNode queryRight)
          || (isSameComponent links firstNode queryRight
               && isSameComponent links secondNode queryLeft)) := by
  show (unionFindRootOf (unionFindJoin links firstNode secondNode) queryLeft
          == unionFindRootOf (unionFindJoin links firstNode secondNode) queryRight)
     = ((unionFindRootOf links queryLeft == unionFindRootOf links queryRight)
         || ((unionFindRootOf links firstNode == unionFindRootOf links queryLeft)
              && (unionFindRootOf links secondNode == unionFindRootOf links queryRight))
         || ((unionFindRootOf links firstNode == unionFindRootOf links queryRight)
              && (unionFindRootOf links secondNode == unionFindRootOf links queryLeft)))
  rw [unionFindRootOf_unionFindJoin links firstNode secondNode queryLeft hforest,
    unionFindRootOf_unionFindJoin links firstNode secondNode queryRight hforest]
  cases guardLeft : (unionFindRootOf links firstNode == unionFindRootOf links queryLeft) with
  | true =>
      have rootLeftEq : unionFindRootOf links firstNode = unionFindRootOf links queryLeft :=
        of_decide_eq_true guardLeft
      cases guardRight : (unionFindRootOf links firstNode
          == unionFindRootOf links queryRight) with
      | true =>
          have rootRightEq : unionFindRootOf links firstNode
              = unionFindRootOf links queryRight := of_decide_eq_true guardRight
          show (unionFindRootOf links secondNode == unionFindRootOf links secondNode)
             = ((unionFindRootOf links queryLeft == unionFindRootOf links queryRight)
                 || (true && (unionFindRootOf links secondNode
                       == unionFindRootOf links queryRight))
                 || (true && (unionFindRootOf links secondNode
                       == unionFindRootOf links queryLeft)))
          rw [natBeq_self (unionFindRootOf links secondNode), ← rootLeftEq, ← rootRightEq,
            natBeq_self (unionFindRootOf links firstNode), boolTrueOr, boolTrueOr]
      | false =>
          show (unionFindRootOf links secondNode == unionFindRootOf links queryRight)
             = ((unionFindRootOf links queryLeft == unionFindRootOf links queryRight)
                 || (true && (unionFindRootOf links secondNode
                       == unionFindRootOf links queryRight))
                 || (false && (unionFindRootOf links secondNode
                       == unionFindRootOf links queryLeft)))
          rw [← rootLeftEq, guardRight,
            boolFalseAnd (unionFindRootOf links secondNode == unionFindRootOf links firstNode),
            boolOrFalse, boolFalseOr, boolTrueAnd]
  | false =>
      cases guardRight : (unionFindRootOf links firstNode
          == unionFindRootOf links queryRight) with
      | true =>
          have rootRightEq : unionFindRootOf links firstNode
              = unionFindRootOf links queryRight := of_decide_eq_true guardRight
          show (unionFindRootOf links queryLeft == unionFindRootOf links secondNode)
             = ((unionFindRootOf links queryLeft == unionFindRootOf links queryRight)
                 || (false && (unionFindRootOf links secondNode
                       == unionFindRootOf links queryRight))
                 || (true && (unionFindRootOf links secondNode
                       == unionFindRootOf links queryLeft)))
          rw [← rootRightEq,
            natBeq_comm (unionFindRootOf links queryLeft) (unionFindRootOf links firstNode),
            guardLeft,
            natBeq_comm (unionFindRootOf links secondNode) (unionFindRootOf links queryLeft),
            boolFalseAnd (unionFindRootOf links secondNode == unionFindRootOf links firstNode),
            boolFalseOr, boolFalseOr, boolTrueAnd]
      | false =>
          show (unionFindRootOf links queryLeft == unionFindRootOf links queryRight)
             = ((unionFindRootOf links queryLeft == unionFindRootOf links queryRight)
                 || (false && (unionFindRootOf links secondNode
                       == unionFindRootOf links queryRight))
                 || (false && (unionFindRootOf links secondNode
                       == unionFindRootOf links queryLeft)))
          rw [boolFalseAnd (unionFindRootOf links secondNode
              == unionFindRootOf links queryRight),
            boolFalseAnd (unionFindRootOf links secondNode
              == unionFindRootOf links queryLeft),
            boolOrFalse, boolOrFalse]

/-- **Honesty marker — the cap-cap core's WIRE leg and JOIN-SPLIT substrate are BUILT.**
`capCapSwap_openMap` discharges the `openMap` field of the target `ArcPartitionSim
(arcFreshBlockTransposition state.nextFresh 1 1)` instance between the two cap-cap run orders
(`nfEq` and the event-LIST equalities are definitional: both orders allocate `nf` then `nf + 1`
and cons them in the same order), and `isSameComponent_unionFindJoin_split` characterizes one
merge purely in pre-join same-component booleans — the case-analysis substrate for the
remaining legs.  What this marker does NOT claim: the `componentsCorr` leg (old-merge
commutation via the split + the event swap), the `loopsEq` leg (the rank argument over the
four wire reads), the two count legs, and the assembled core instance.  `= true` records the
wire leg + the split. -/
def fxMode_hasCapCapSwapWireLeg : Bool := true

end FX1Poly.Polygraph
