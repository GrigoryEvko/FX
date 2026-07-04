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

/-- `Bool` equality from the two `= true` implications — the zero-axiom `Bool`-of-iff shuttle. -/
theorem boolEqOfIff (leftBit rightBit : Bool)
    (forward : leftBit = true → rightBit = true)
    (backward : rightBit = true → leftBit = true) : leftBit = rightBit := by
  cases leftBit with
  | true =>
      cases rightBit with
      | true => rfl
      | false => exact Bool.noConfusion (forward rfl)
  | false =>
      cases rightBit with
      | true => exact Bool.noConfusion (backward rfl)
      | false => rfl

/-- Destructor: a true disjunction has a true disjunct. -/
theorem orElimBit (left right : Bool) (h : (left || right) = true) :
    left = true ∨ right = true := by
  cases left with
  | true => exact Or.inl rfl
  | false =>
      rw [boolFalseOr] at h
      exact Or.inr h

/-- Constructor: a true LEFT disjunct makes the disjunction true. -/
theorem orIntroLeftBit (left right : Bool) (h : left = true) : (left || right) = true := by
  rw [h, boolTrueOr]

/-- Constructor: a true RIGHT disjunct makes the disjunction true. -/
theorem orIntroRightBit (left right : Bool) (h : right = true) : (left || right) = true := by
  rw [h]
  cases left with
  | true => exact boolTrueOr true
  | false => exact boolFalseOr true

/-- Destructor: a true conjunction has two true conjuncts. -/
theorem andElimBit (left right : Bool) (h : (left && right) = true) :
    left = true ∧ right = true := by
  cases left with
  | true =>
      rw [boolTrueAnd] at h
      exact And.intro rfl h
  | false =>
      rw [boolFalseAnd] at h
      exact Bool.noConfusion h

/-- Constructor: two true conjuncts make the conjunction true. -/
theorem andIntroBit (left right : Bool) (leftTrue : left = true) (rightTrue : right = true) :
    (left && right) = true := by
  rw [leftTrue, rightTrue, boolTrueAnd]

/-- The `Prop` reading of `isSameComponent`: the boolean is true exactly when the two roots are
EQUAL as naturals — the shuttle that makes same-component facts compose by `Eq.trans`/`Eq.symm`. -/
theorem isSameComponent_true_iff_rootsEqual (links : List (Nat × Nat))
    (firstNode secondNode : Nat) :
    isSameComponent links firstNode secondNode = true
      ↔ unionFindRootOf links firstNode = unionFindRootOf links secondNode :=
  Iff.intro
    (fun sameTrue => of_decide_eq_true
      (show (unionFindRootOf links firstNode == unionFindRootOf links secondNode) = true
        from sameTrue))
    (fun rootsEqual =>
      show (unionFindRootOf links firstNode == unionFindRootOf links secondNode) = true
        from decide_eq_true rootsEqual)

/-- Same-component truth is symmetric (through the root reading). -/
theorem isSameComponent_true_symm (links : List (Nat × Nat)) (firstNode secondNode : Nat)
    (h : isSameComponent links firstNode secondNode = true) :
    isSameComponent links secondNode firstNode = true :=
  (isSameComponent_true_iff_rootsEqual links secondNode firstNode).mpr
    ((isSameComponent_true_iff_rootsEqual links firstNode secondNode).mp h).symm

/-- The `Prop`-level reading of the boolean join split: after-join same-component truth is the
three-way disjunction over pre-join same-component truths. -/
theorem isSameComponent_unionFindJoin_true_iff (links : List (Nat × Nat))
    (hforest : isUnionFindForest links) (firstNode secondNode queryLeft queryRight : Nat) :
    isSameComponent (unionFindJoin links firstNode secondNode) queryLeft queryRight = true
      ↔ (isSameComponent links queryLeft queryRight = true
          ∨ (isSameComponent links firstNode queryLeft = true
               ∧ isSameComponent links secondNode queryRight = true)
          ∨ (isSameComponent links firstNode queryRight = true
               ∧ isSameComponent links secondNode queryLeft = true)) := by
  rw [isSameComponent_unionFindJoin_split links hforest firstNode secondNode
    queryLeft queryRight]
  constructor
  · intro combinedTrue
    cases orElimBit _ _ combinedTrue with
    | inl frontTrue =>
        cases orElimBit _ _ frontTrue with
        | inl directTrue => exact Or.inl directTrue
        | inr crossTrue => exact Or.inr (Or.inl (andElimBit _ _ crossTrue))
    | inr mirrorTrue => exact Or.inr (Or.inr (andElimBit _ _ mirrorTrue))
  · intro disjunction
    cases disjunction with
    | inl directTrue => exact orIntroLeftBit _ _ (orIntroLeftBit _ _ directTrue)
    | inr crossOrMirror =>
        cases crossOrMirror with
        | inl crossPair =>
            exact orIntroLeftBit _ _
              (orIntroRightBit _ _ (andIntroBit _ _ crossPair.1 crossPair.2))
        | inr mirrorPair =>
            exact orIntroRightBit _ _ (andIntroBit _ _ mirrorPair.1 mirrorPair.2)

/-- ★ **The cross-connection swap core.**  If the two later-join nodes reach the two queries
THROUGH the first join (`laterFirst ~ queryLeft` and `laterSecond ~ queryRight` over
`join links firstNode secondNode`), then the queries are connected in the SWAPPED double join
(`firstNode`/`secondNode` joined over `join links laterFirst laterSecond`).  Nine leaves: each
cross hypothesis splits three ways at the base level, and every combination reassembles on the
swapped side by root symmetry/transitivity. -/
theorem isSameComponent_join_cross_swap (links : List (Nat × Nat))
    (hforest : isUnionFindForest links)
    (firstNode secondNode laterFirst laterSecond queryLeft queryRight : Nat)
    (crossLeft : isSameComponent (unionFindJoin links firstNode secondNode)
        laterFirst queryLeft = true)
    (crossRight : isSameComponent (unionFindJoin links firstNode secondNode)
        laterSecond queryRight = true) :
    isSameComponent (unionFindJoin (unionFindJoin links laterFirst laterSecond)
        firstNode secondNode) queryLeft queryRight = true := by
  have forestLater : isUnionFindForest (unionFindJoin links laterFirst laterSecond) :=
    isUnionFindForest_unionFindJoin links laterFirst laterSecond hforest
  refine (isSameComponent_unionFindJoin_true_iff (unionFindJoin links laterFirst laterSecond)
    forestLater firstNode secondNode queryLeft queryRight).mpr ?_
  cases (isSameComponent_unionFindJoin_true_iff links hforest firstNode secondNode
      laterFirst queryLeft).mp crossLeft with
  | inl sameLaterFirstLeft =>
      cases (isSameComponent_unionFindJoin_true_iff links hforest firstNode secondNode
          laterSecond queryRight).mp crossRight with
      | inl sameLaterSecondRight =>
          exact Or.inl ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst
            laterSecond queryLeft queryRight).mpr
            (Or.inr (Or.inl (And.intro sameLaterFirstLeft sameLaterSecondRight))))
      | inr rightCrossOrMirror =>
          cases rightCrossOrMirror with
          | inl rightCross =>
              exact Or.inr (Or.inl (And.intro
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  firstNode queryLeft).mpr (Or.inr (Or.inr (And.intro sameLaterFirstLeft
                    (isSameComponent_true_symm links firstNode laterSecond rightCross.1)))))
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  secondNode queryRight).mpr (Or.inl rightCross.2))))
          | inr rightMirror =>
              exact Or.inr (Or.inr (And.intro
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  firstNode queryRight).mpr (Or.inl rightMirror.1))
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  secondNode queryLeft).mpr (Or.inr (Or.inr (And.intro sameLaterFirstLeft
                    (isSameComponent_true_symm links secondNode laterSecond
                      rightMirror.2)))))))
  | inr leftCrossOrMirror =>
      cases leftCrossOrMirror with
      | inl leftCross =>
          cases (isSameComponent_unionFindJoin_true_iff links hforest firstNode secondNode
              laterSecond queryRight).mp crossRight with
          | inl sameLaterSecondRight =>
              exact Or.inr (Or.inr (And.intro
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  firstNode queryRight).mpr (Or.inr (Or.inl (And.intro
                    (isSameComponent_true_symm links firstNode laterFirst leftCross.1)
                    sameLaterSecondRight))))
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  secondNode queryLeft).mpr (Or.inl leftCross.2))))
          | inr rightCrossOrMirror =>
              cases rightCrossOrMirror with
              | inl rightCross =>
                  have rootsLeftRight : unionFindRootOf links queryLeft
                      = unionFindRootOf links queryRight :=
                    ((isSameComponent_true_iff_rootsEqual links secondNode
                      queryLeft).mp leftCross.2).symm.trans
                      ((isSameComponent_true_iff_rootsEqual links secondNode
                        queryRight).mp rightCross.2)
                  exact Or.inl ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst
                    laterSecond queryLeft queryRight).mpr (Or.inl
                    ((isSameComponent_true_iff_rootsEqual links queryLeft
                      queryRight).mpr rootsLeftRight)))
              | inr rightMirror =>
                  exact Or.inr (Or.inr (And.intro
                    ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst
                      laterSecond firstNode queryRight).mpr (Or.inl rightMirror.1))
                    ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst
                      laterSecond secondNode queryLeft).mpr (Or.inl leftCross.2))))
      | inr leftMirror =>
          cases (isSameComponent_unionFindJoin_true_iff links hforest firstNode secondNode
              laterSecond queryRight).mp crossRight with
          | inl sameLaterSecondRight =>
              exact Or.inr (Or.inl (And.intro
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  firstNode queryLeft).mpr (Or.inl leftMirror.1))
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  secondNode queryRight).mpr (Or.inr (Or.inl (And.intro
                    (isSameComponent_true_symm links secondNode laterFirst leftMirror.2)
                    sameLaterSecondRight))))))
          | inr rightCrossOrMirror =>
              cases rightCrossOrMirror with
              | inl rightCross =>
                  exact Or.inr (Or.inl (And.intro
                    ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst
                      laterSecond firstNode queryLeft).mpr (Or.inl leftMirror.1))
                    ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst
                      laterSecond secondNode queryRight).mpr (Or.inl rightCross.2))))
              | inr rightMirror =>
                  have rootsLeftRight : unionFindRootOf links queryLeft
                      = unionFindRootOf links queryRight :=
                    ((isSameComponent_true_iff_rootsEqual links firstNode
                      queryLeft).mp leftMirror.1).symm.trans
                      ((isSameComponent_true_iff_rootsEqual links firstNode
                        queryRight).mp rightMirror.1)
                  exact Or.inl ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst
                    laterSecond queryLeft queryRight).mpr (Or.inl
                    ((isSameComponent_true_iff_rootsEqual links queryLeft
                      queryRight).mpr rootsLeftRight)))

/-- One direction of the two-join commutation: connectivity in `join (join links a b) c d`
transfers to `join (join links c d) a b`.  Three top cases: a through-first-join connection
re-expands and lifts disjunct-by-disjunct; the two cross connections are the cross-swap core
(the mirror one after swapping the queries and symmetrizing). -/
theorem isSameComponent_two_joins_swap (links : List (Nat × Nat))
    (hforest : isUnionFindForest links)
    (firstNode secondNode laterFirst laterSecond queryLeft queryRight : Nat)
    (h : isSameComponent (unionFindJoin (unionFindJoin links firstNode secondNode)
        laterFirst laterSecond) queryLeft queryRight = true) :
    isSameComponent (unionFindJoin (unionFindJoin links laterFirst laterSecond)
        firstNode secondNode) queryLeft queryRight = true := by
  have forestFirst : isUnionFindForest (unionFindJoin links firstNode secondNode) :=
    isUnionFindForest_unionFindJoin links firstNode secondNode hforest
  have forestLater : isUnionFindForest (unionFindJoin links laterFirst laterSecond) :=
    isUnionFindForest_unionFindJoin links laterFirst laterSecond hforest
  cases (isSameComponent_unionFindJoin_true_iff (unionFindJoin links firstNode secondNode)
      forestFirst laterFirst laterSecond queryLeft queryRight).mp h with
  | inl throughFirst =>
      refine (isSameComponent_unionFindJoin_true_iff (unionFindJoin links laterFirst laterSecond)
        forestLater firstNode secondNode queryLeft queryRight).mpr ?_
      cases (isSameComponent_unionFindJoin_true_iff links hforest firstNode secondNode
          queryLeft queryRight).mp throughFirst with
      | inl direct =>
          exact Or.inl ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst
            laterSecond queryLeft queryRight).mpr (Or.inl direct))
      | inr crossOrMirror =>
          cases crossOrMirror with
          | inl crossPair =>
              exact Or.inr (Or.inl (And.intro
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  firstNode queryLeft).mpr (Or.inl crossPair.1))
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  secondNode queryRight).mpr (Or.inl crossPair.2))))
          | inr mirrorPair =>
              exact Or.inr (Or.inr (And.intro
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  firstNode queryRight).mpr (Or.inl mirrorPair.1))
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  secondNode queryLeft).mpr (Or.inl mirrorPair.2))))
  | inr crossOrMirror =>
      cases crossOrMirror with
      | inl crossPair =>
          exact isSameComponent_join_cross_swap links hforest firstNode secondNode laterFirst
            laterSecond queryLeft queryRight crossPair.1 crossPair.2
      | inr mirrorPair =>
          exact isSameComponent_true_symm _ queryRight queryLeft
            (isSameComponent_join_cross_swap links hforest firstNode secondNode laterFirst
              laterSecond queryRight queryLeft mirrorPair.1 mirrorPair.2)

/-- ★ **Two adjacent union-find joins COMMUTE at the partition level.**  The boolean
same-component relation of `join (join links a b) c d` equals that of
`join (join links c d) a b` on every query pair — the reorder engine for the cap-cap
`componentsCorr` leg (the two run orders perform the same four merges in different orders).
NOTE: this is NOT a free boolean identity in the pre-join atoms (transitivity-violating
assignments separate the two expansions); it genuinely needs the root reading. -/
theorem isSameComponent_two_joins_comm (links : List (Nat × Nat))
    (hforest : isUnionFindForest links)
    (firstNode secondNode laterFirst laterSecond queryLeft queryRight : Nat) :
    isSameComponent (unionFindJoin (unionFindJoin links firstNode secondNode)
        laterFirst laterSecond) queryLeft queryRight
      = isSameComponent (unionFindJoin (unionFindJoin links laterFirst laterSecond)
          firstNode secondNode) queryLeft queryRight :=
  boolEqOfIff _ _
    (isSameComponent_two_joins_swap links hforest firstNode secondNode laterFirst laterSecond
      queryLeft queryRight)
    (isSameComponent_two_joins_swap links hforest laterFirst laterSecond firstNode secondNode
      queryLeft queryRight)

/-- **Honesty marker — the cap-cap core's WIRE leg, JOIN-SPLIT, and JOIN-COMMUTATION substrate
are BUILT.**  `capCapSwap_openMap` discharges the `openMap` field of the target
`ArcPartitionSim (arcFreshBlockTransposition state.nextFresh 1 1)` instance between the two
cap-cap run orders (`nfEq` and the event-LIST equalities are definitional: both orders allocate
`nf` then `nf + 1` and cons them in the same order); `isSameComponent_unionFindJoin_split`
characterizes one merge purely in pre-join same-component booleans; and
`isSameComponent_two_joins_comm` commutes two adjacent joins at the partition level — the
reorder engine that aligns the two four-join link towers.  What this marker does NOT claim:
the `componentsCorr` leg (tower reorder + the fresh-attach sigma dispatch), the `loopsEq` leg,
the two count legs, and the assembled core instance.  `= true` records the wire leg + the
split + the commutation. -/
def fxMode_hasCapCapSwapWireLeg : Bool := true

end FX1Poly.Polygraph
